/- The generic host lift, part 2 (over any general target `GTarget`): the start (`enter`): a `StartCorrect` state
whose code is a valid image's bytes satisfies the target's layout condition and is related to its J view at pc 0, for
every layout `K` inside the call's blocks. -/
import Nano.Run.HostOn
namespace JT
open Proven.Top SimW CallProbe

variable {T : GTarget}

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

/-- **the start**: a `StartCorrect` state whose code is the image `I` of `C` meets the target's layout condition and
is related to its J view at pc 0, for a layout inside the call's blocks (work cells in the work block, output bytes in
the output block) -/
theorem enter (L : T.Laws) {s : T.M.State} {call : Call} {C : List J} {I : Img} {x : List UInt8}
    (sc : StartCorrect T.M s call I.code x) (hld : T.loader s call I.code x) (K : LayW)
    (hb : K.base = (T.M.observe s).programCounter.toNat) (hm0 : K.m0 = T.m0 s)
    (hlo : K.lo = call.workAddress.toNat) (hhi : K.hi ≤ call.workAddress.toNat + call.workLength)
    (hib : K.ib = call.inputAddress.toNat) (hil : K.il = x.length)
    (hob : K.ob = call.outputAddress.toNat) (hol : K.ol ≤ call.outputLength) (hv : T.valid C I) :
    T.lay K C I ∧ T.Rel K C I s (0, jOfG T s K.base I.ly) s := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, e3, f1, f2, g1, r32⟩ := blocks_of L sc
  have ilen := sc.inputLength
  have b4 := sc.codeAligned
  refine ⟨L.lay_init K C I ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hv, rel_entry L sc.configured ?_ hv ?_ ?_ ?_ hm0
    (L.inv_init K C I s call x sc hld hv hb hm0 hlo hhi hib hil hob hol)⟩
  all_goals try (rw [hb] <;> omega)
  all_goals try omega
  · rw [hb]; simp
  · intro a ha
    obtain ⟨-, hr⟩ := read_some sc.codeLoaded
    have := hr a ha
    rw [List.getElem?_eq_getElem ha] at this
    rw [hb]; exact this
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
    (sc : StartCorrect T.M s call code x) (b : Nat) (ly : CallProbe.LinkLay) :
    (jOfG T s b ly).x 1 = call.returnAddress ∧ (jOfG T s b ly).x 2 = call.workAddress + call.workLength.toUInt64 ∧
    (jOfG T s b ly).x 10 = call.inputAddress ∧ (jOfG T s b ly).x 11 = x.length.toUInt64 ∧
    (jOfG T s b ly).x 12 = call.workAddress ∧ (jOfG T s b ly).x 13 = call.outputAddress ∧ (jOfG T s b ly).x 0 = 0 ∧
    (jOfG T s b ly).b = b := by
  obtain ⟨r1, r2, r10, r11, r12, r13, -, -⟩ := L.reg_map
  simp only [jOfG, show (0 : Nat) < 1 ∧ 1 < 32 from by omega, show (0 : Nat) < 2 ∧ 2 < 32 from by omega,
    show (0 : Nat) < 10 ∧ 10 < 32 from by omega, show (0 : Nat) < 11 ∧ 11 < 32 from by omega,
    show (0 : Nat) < 12 ∧ 12 < 32 from by omega, show (0 : Nat) < 13 ∧ 13 < 32 from by omega,
    r1, r2, r10, r11, r12, r13]
  exact ⟨sc.returnRegister, sc.workTopRegister, sc.inputRegister, sc.lengthRegister, sc.workRegister,
    sc.outputRegister, by simp, trivial⟩

end JT
