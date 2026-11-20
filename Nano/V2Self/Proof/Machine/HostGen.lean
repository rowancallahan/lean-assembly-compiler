/- The generic host lift, part 2 (over any `JTarget`): the code bytes of a J program (`tbytes`), and the start
(`enter`): a `StartCorrect` state with code `tbytes T C` satisfies the target's layout condition and is related to
its J view at pc 0, for every layout `K` inside the call's blocks. -/
import Nano.V2Self.Proof.Machine.HostOn
namespace JT
open Proven.Top SimW CallProbe

variable {T : JTarget}

/-- the code bytes of a J program on `T`: its words, 4 bytes each, little-endian -/
def tbytes (T : JTarget) (C : List J) : List UInt8 :=
  (C.flatMap T.enc).flatMap fun w => [wbyte w 0, wbyte w 1, wbyte w 2, wbyte w 3]

theorem flat_len {α β : Type} (f : α → List β) (n : Nat) (hf : ∀ a, (f a).length = n) :
    ∀ L : List α, (L.flatMap f).length = n * L.length
  | [] => by simp
  | a :: L => by simp only [List.flatMap_cons, List.length_append, hf, flat_len f n hf L, List.length_cons, Nat.mul_succ]; omega

theorem flat_get {α β : Type} (f : α → List β) (n : Nat) (hf : ∀ a, (f a).length = n) :
    ∀ (L : List α) (i r : Nat) (hi : i < L.length), r < n → (L.flatMap f)[n * i + r]? = (f L[i])[r]?
  | [], _, _, hi, _ => absurd hi (by simp)
  | a :: L, 0, r, _, hr => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add]
    rw [List.getElem?_append_left (by rw [hf]; exact hr)]; rfl
  | a :: L, i + 1, r, hi, hr => by
    simp only [List.flatMap_cons]
    rw [List.getElem?_append_right (by rw [hf, Nat.mul_succ]; omega), hf,
      show n * (i + 1) + r - n = n * i + r by rw [Nat.mul_succ]; omega]
    exact flat_get f n hf L i r (by simp at hi; omega) hr

theorem tbytes_len (L : T.Laws) (C : List J) : (tbytes T C).length = 4 * T.blockLen * C.length := by
  unfold tbytes
  rw [flat_len _ 4 (fun _ => rfl), flat_len _ _ L.enc_len, Nat.mul_assoc]

theorem tbytes_get (L : T.Laws) (C : List J) (i : Nat) (hi : i < C.length) (k : Nat) (hk : k < T.blockLen)
    (b : Nat) (hb : b < 4) :
    (tbytes T C)[4 * T.blockLen * i + 4 * k + b]? = (T.enc C[i])[k]?.map (wbyte · b) := by
  unfold tbytes
  have hl : T.blockLen * i + k < (C.flatMap T.enc).length := by
    rw [flat_len _ _ L.enc_len]
    have := Nat.mul_le_mul_left T.blockLen (show i + 1 ≤ C.length by omega)
    rw [Nat.mul_succ] at this; omega
  rw [show 4 * T.blockLen * i + 4 * k + b = 4 * (T.blockLen * i + k) + b by rw [Nat.mul_assoc, Nat.mul_add],
    flat_get _ 4 (fun _ => rfl) _ _ _ hl hb, ← flat_get T.enc _ L.enc_len C i k hi hk,
    List.getElem?_eq_getElem hl]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem add_ofNat (a : UInt64) (o : Nat) : a + o.toUInt64 = UInt64.ofNat (a.toNat + o) := by
  apply UInt64.toNat_inj.1; simp [UInt64.toNat_add]

theorem mapM_get (g : Nat → Option UInt8) : ∀ (l : List Nat) (bs : List UInt8), l.mapM g = some bs →
    bs.length = l.length ∧ ∀ i (hi : i < l.length), g l[i] = bs[i]?
  | [], bs, h => by simp at h; subst h; simp
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h
    cases ha : g a with
    | none => simp [ha] at h
    | some v =>
      cases hl : l.mapM g with
      | none => simp [ha, hl] at h
      | some r =>
        simp [ha, hl] at h; subst h
        obtain ⟨h1, h2⟩ := mapM_get g l r hl
        refine ⟨by simp [h1], fun i hi => ?_⟩
        cases i with
        | zero => simpa using ha
        | succ i => simpa using h2 i (by simp at hi; omega)

/-- a successful `readMemory`, bytewise -/
theorem read_some {st : MachineState} {a : UInt64} {n : Nat} {bs : List UInt8} (h : readMemory st a n = some bs) :
    bs.length = n ∧ ∀ i, i < n → st.memory (UInt64.ofNat (a.toNat + i)) = bs[i]? := by
  obtain ⟨h1, h2⟩ := mapM_get _ _ _ h
  refine ⟨by simpa using h1, fun i hi => ?_⟩
  have := h2 i (by simpa using hi)
  simp only [List.getElem_range] at this
  rw [← add_ofNat]; exact this

/-- the call's blocks in Nat form (RAM window, pairwise apart) -/
theorem blocks_of (L : T.Laws) {s : T.M.State} {call : Call} {code x : List UInt8}
    (sc : StartCorrect T.M s call code x) :
    let pc := (T.M.observe s).programCounter.toNat
    T.M.ramStart ≤ call.inputAddress.toNat ∧ call.inputAddress.toNat + call.inputLength ≤ T.M.ramEnd ∧
    T.M.ramStart ≤ call.outputAddress.toNat ∧ call.outputAddress.toNat + call.outputLength ≤ T.M.ramEnd ∧
    T.M.ramStart ≤ call.workAddress.toNat ∧ call.workAddress.toNat + call.workLength ≤ T.M.ramEnd ∧
    T.M.ramStart ≤ pc ∧ pc + code.length ≤ T.M.ramEnd ∧
    (call.inputAddress.toNat + call.inputLength ≤ call.outputAddress.toNat ∨
      call.outputAddress.toNat + call.outputLength ≤ call.inputAddress.toNat) ∧
    (call.inputAddress.toNat + call.inputLength ≤ call.workAddress.toNat ∨
      call.workAddress.toNat + call.workLength ≤ call.inputAddress.toNat) ∧
    (call.inputAddress.toNat + call.inputLength ≤ pc ∨ pc + code.length ≤ call.inputAddress.toNat) ∧
    (call.outputAddress.toNat + call.outputLength ≤ call.workAddress.toNat ∨
      call.workAddress.toNat + call.workLength ≤ call.outputAddress.toNat) ∧
    (call.outputAddress.toNat + call.outputLength ≤ pc ∨ pc + code.length ≤ call.outputAddress.toNat) ∧
    (call.workAddress.toNat + call.workLength ≤ pc ∨ pc + code.length ≤ call.workAddress.toNat) ∧
    T.M.ramEnd ≤ 2 ^ 32 := by
  have hr := sc.inRam
  have hd := sc.disjoint
  simp only [Call.blocks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  simp only [Call.blocks, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true, Apart] at hd
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩⟩ := hr
  obtain ⟨⟨e1, e2, e3⟩, ⟨f1, f2⟩, g1⟩ := hd
  exact ⟨a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, e3, f1, f2, g1.1, L.ram.2⟩

/-- **the start**: a `StartCorrect` state whose code is `tbytes T C` meets the target's layout condition and is related to
its J view at pc 0, for a layout inside the call's blocks (work cells in the work block, output bytes in the output
block) -/
theorem enter (L : T.Laws) {s : T.M.State} {call : Call} {C : List J} {x : List UInt8}
    (sc : StartCorrect T.M s call (tbytes T C) x) (hld : T.loader s call (tbytes T C) x) (K : LayW)
    (hb : K.base = (T.M.observe s).programCounter.toNat) (hW : K.W = T.words C) (hm0 : K.m0 = T.m0 s)
    (hlo : K.lo = call.workAddress.toNat) (hhi : K.hi ≤ call.workAddress.toNat + call.workLength)
    (hib : K.ib = call.inputAddress.toNat) (hil : K.il = x.length)
    (hob : K.ob = call.outputAddress.toNat) (hol : K.ol ≤ call.outputLength) (hv : T.valid C) :
    T.lay K C ∧ T.Rel K C s (0, jOfT T s K.base) s := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, e3, f1, f2, g1, r32⟩ := blocks_of L sc
  have hn := tbytes_len L C
  have ilen := sc.inputLength
  have b4 := sc.codeAligned
  rw [hn] at d2 e3 f2 g1
  refine ⟨L.lay_init K C ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hW hv, rel_entry L sc.configured ?_ ?_ ?_ ?_ hm0
    (L.inv_init K C s call _ x sc hld (tbytes_len L C) hb hW hm0 hlo hhi hib hil hob hol)⟩
  all_goals try (rw [hb] <;> omega)
  all_goals try omega
  · rw [hb]; simp
  · intro i hi k hk b hb4
    rw [L.enc_len] at hk
    obtain ⟨-, hr⟩ := read_some sc.codeLoaded
    have hlt : 4 * T.blockLen * i + 4 * k + b < (tbytes T C).length := by
      rw [hn]
      have := Nat.mul_le_mul_left (4 * T.blockLen) (show i + 1 ≤ C.length by omega)
      rw [Nat.mul_succ] at this; omega
    have := hr _ hlt
    rw [tbytes_get L C i hi k hk b hb4, List.getElem?_eq_getElem (by rw [L.enc_len]; exact hk)] at this
    rw [JTarget.addr, hb, show (T.M.observe s).programCounter.toNat + 4 * T.blockLen * i + 4 * k + b =
      (T.M.observe s).programCounter.toNat + (4 * T.blockLen * i + 4 * k + b) by omega]
    exact this
  · intro a ha k hk
    unfold wok at ha
    have := sc.workPresent (a + k - call.workAddress.toNat) (by omega)
    rwa [add_ofNat, show call.workAddress.toNat + (a + k - call.workAddress.toNat) = a + k by omega] at this
  · intro a ha
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨-, hr⟩ := read_some sc.inputLoaded
      have := hr (a - call.inputAddress.toNat) (by omega)
      rw [show call.inputAddress.toNat + (a - call.inputAddress.toNat) = a by omega] at this
      rw [this, List.getElem?_eq_getElem (by obtain ⟨e, -⟩ := read_some sc.inputLoaded; omega)]; rfl
    · have := sc.outputPresent (a - call.outputAddress.toNat) (by omega)
      rwa [add_ofNat, show call.outputAddress.toNat + (a - call.outputAddress.toNat) = a by omega] at this

/-- the J view's registers at the start (through `reg_map`) -/
theorem jregs (L : T.Laws) {s : T.M.State} {call : Call} {code x : List UInt8}
    (sc : StartCorrect T.M s call code x) (b : Nat) :
    (jOfT T s b).x 1 = call.returnAddress ∧ (jOfT T s b).x 2 = call.workAddress + call.workLength.toUInt64 ∧
    (jOfT T s b).x 10 = call.inputAddress ∧ (jOfT T s b).x 11 = x.length.toUInt64 ∧
    (jOfT T s b).x 12 = call.workAddress ∧ (jOfT T s b).x 13 = call.outputAddress ∧ (jOfT T s b).x 0 = 0 ∧
    (jOfT T s b).b = b := by
  obtain ⟨r1, r2, r10, r11, r12, r13, -, -⟩ := L.reg_map
  simp only [jOfT, show (0 : Nat) < 1 ∧ 1 < 32 from by omega, show (0 : Nat) < 2 ∧ 2 < 32 from by omega,
    show (0 : Nat) < 10 ∧ 10 < 32 from by omega, show (0 : Nat) < 11 ∧ 11 < 32 from by omega,
    show (0 : Nat) < 12 ∧ 12 < 32 from by omega, show (0 : Nat) < 13 ∧ 13 < 32 from by omega,
    r1, r2, r10, r11, r12, r13]
  exact ⟨sc.returnRegister, sc.workTopRegister, sc.inputRegister, sc.lengthRegister, sc.workRegister,
    sc.outputRegister, by simp, trivial⟩

end JT
