/- Calls in the emitted code: the callee's prologue (open the frame below the caller's, all slots zero, the
arguments into the parameter slots), the call site (the arguments into `r0 ..`, the check that the frame fits,
the jump-and-link), the return (the results into `r0 ..`, close the frame, back to the return address in the
frame's cell 0) and the code after the call (the frame limit back up, the results into their slots). -/
import Compiler.Ir.EmitInstOk

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Ctx
variable {T : Target} {C : Ctx T}

theorem _root_.Proven.Ir.Target.len_append (T : Target) (a b : List EOp) : T.len (a ++ b) = T.len a + T.len b := by
  simp only [Target.len, T.words_append, List.length_append]
theorem _root_.Proven.Ir.Target.len_cons (T : Target) (o : EOp) (os : List EOp) :
    T.len (o :: os) = (T.encO o).length + T.len os := by
  simp only [Target.len, T.words_cons, List.length_append]
theorem _root_.Proven.Ir.Target.len_nil (T : Target) : T.len [] = 0 := rfl

theorem fa_AtQ {s : T.S} {q n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).AtQ s q ↔ C.AtQ s q := Iff.rfl

/-- memory unchanged from address `a` to the top of the work block -/
def Above (C : Ctx T) (a : Nat) (s s' : T.S) : Prop := ∀ x, a ≤ x → x < C.T0 → T.mem s' x = T.mem s x

theorem Above.trans {a : Nat} {s₁ s₂ s₃ : T.S} (h₁ : C.Above a s₁ s₂) (h₂ : C.Above a s₂ s₃) : C.Above a s₁ s₃ :=
  fun x h1 h2 => by rw [h₂ x h1 h2, h₁ x h1 h2]

theorem Above.mono {a b : Nat} {s s' : T.S} (h : C.Above a s s') (hab : a ≤ b) : C.Above b s s' :=
  fun x h1 h2 => h x (by omega) h2

theorem Above.refl (a : Nat) (s : T.S) : C.Above a s s := fun _ _ _ => rfl

theorem Above.bytes {a b n : Nat} {s s' : T.S} (h : C.Above a s s') (h1 : a ≤ b) (h2 : b + n ≤ C.T0) :
    Proven.Mach.bytes (T.mem s') b n = Proven.Mach.bytes (T.mem s) b n :=
  bytes_congr fun j hj => h _ (by omega) (by omega)

/-- the machine right before a frame of `n` slots at `fb` is opened (below the caller's frame at `fb + 8 (n + 1)`) -/
structure Pre (m : Mem) (fb n : Nat) (s : T.S) : Prop where
  ok : T.ok s
  keep : T.keepC C.s0 s
  fr : T.fr s = BitVec.ofNat 64 (fb + 8 * (n + 1))
  rlim : T.get s RLim = BitVec.ofNat 64 fb
  rin : T.get s RIn = BitVec.ofNat 64 C.inA
  rhp : T.get s RHp = BitVec.ofNat 64 (C.wb + 8 * m.cells.length)
  cap : C.wb + 8 * m.cells.length ≤ fb
  fit : fb + 8 * (n + 1) + 16 ≤ C.T0
  fal : fb % 8 = 0
  nsl : n ≤ T.maxSlots
  stub : bytes (T.mem s) (C.T0 - 16) 8 = (le8 (T.ra C.s0)).map some
  cells : ∀ g v, m.cells[g]? = some (some v) →
    bytes (T.mem s) (C.wb + 8 * g) 8 = (le8 (C.repr m.blks v)).map some
  out : ∀ i b, m.out[i]? = some (some b) → T.mem s (C.outA + i) = some b.toBitVec
  outL : m.out.length ≤ C.outL
  unch : C.Unch s
  mok : C.MemOK m


theorem Pre.fa {m : Mem} {a k n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} {s : T.S}
    (h : C.Pre m a k s) : (C.fa n fb v M).Pre m a k s :=
  ⟨h.ok, h.keep, h.fr, h.rlim, h.rin, h.rhp, h.cap, h.fit, h.fal, h.nsl, h.stub, h.cells, h.out, h.outL, h.unch, ⟨h.mok.inp, h.mok.blks, h.mok.cv⟩⟩

theorem Pre.unfa {m : Mem} {a k n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} {s : T.S}
    (h : (C.fa n fb v M).Pre m a k s) : C.Pre m a k s :=
  ⟨h.ok, h.keep, h.fr, h.rlim, h.rin, h.rhp, h.cap, h.fit, h.fal, h.nsl, h.stub, h.cells, h.out, h.outL, h.unch, ⟨h.mok.inp, h.mok.blks, h.mok.cv⟩⟩

theorem zeros_len (n : Nat) : (Target.zeros n).length = n := by simp [Target.zeros]

/-- the zero stores of the prologue: the frame grows slot by slot -/
theorem zeros_ok {m : Mem} {fb n : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} :
    ∀ (k j : Nat) {s : T.S} {q : Nat} {rest : List (BitVec 32)}, j + k = n →
      (C.fa j fb v M).AtQ s q → (C.fa j fb v M).MR m (fun _ => .w 0) s → T.get s R7 = 0 →
      fb + 8 * (n + 1) + 16 ≤ C.T0 → n ≤ T.maxSlots →
      InW C.W q (T.words (((List.range k).map fun i => EOp.w (.stS (j + i) R7))) ++ rest) →
      T.runsTo s fun s' => C.AtQ s' (q + T.len ((List.range k).map fun i => EOp.w (.stS (j + i) R7))) ∧
        (C.fa n fb v M).MR m (fun _ => .w 0) s' ∧ (∀ r : Reg, T.get s' r = T.get s r) ∧
        C.Above (fb + 8 * (n + 1)) s s'
  | 0, j, s, q, rest, hjk, hA, hR, h7, hfit, hn, _ => by
    subst hjk
    exact T.runsTo_of ⟨by simp only [Target.len, Target.words, List.range_zero, List.map_nil, List.flatMap_nil, List.length_nil, Nat.add_zero]; exact hA, by simpa using hR, fun _ => rfl, Above.refl _ _⟩
  | k + 1, j, s, q, rest, hjk, hA, hR, h7, hfit, hn, hin => by
    have hin' : InW C.W q (T.encO (.w (.stS j R7)) ++
        (T.words ((List.range k).map fun i => EOp.w (.stS (j + 1 + i) R7)) ++ rest)) := by
      have e : (List.range (k + 1)).map (fun i => EOp.w (.stS (j + i) R7)) =
          EOp.w (.stS j R7) :: (List.range k).map fun i => EOp.w (.stS (j + 1 + i) R7) := by
        rw [List.range_succ_eq_map]; simp only [List.map_cons, List.map_map, Nat.add_zero]
        congr 1; apply List.map_congr_left; intro i _; simp only [Function.comp]; congr 2; omega
      rw [e, Target.words_cons, List.append_assoc] at hin; exact hin
    have hF : (T.fr s).toNat + 8 * (j + 1) = fb + 8 * (j + 1) := by
      have e := hR.fr; change T.fr s = BitVec.ofNat 64 fb at e
      have := C.T0_le; have := C.w_lt; have := T.ramHi_lt; have := hR.fit; change fb + 8 * (j + 1) + 16 ≤ C.T0 at this
      rw [e, ofNat_toNat' (by omega)]
    have hT := C.T0_le; obtain ⟨hw1, hw2⟩ := C.wR; have hcap := hR.cap; change C.wb + 8 * m.cells.length ≤ fb at hcap
    have hal := hR.fal; change fb % 8 = 0 at hal
    refine T.toCore.runsTo_trans (C.opW (fa_AtQ.1 hA) hin' (fun h => T.w_stS (j := j) (v := R7) (by omega) h
        (by rw [hF]; exact ⟨by omega, by omega⟩) (by rw [hF]; omega)
        (fun i hi => C.wr _ _ (.inr ⟨by rw [hF]; omega, by rw [hF]; omega⟩)))
      (fun s' ⟨_, hm⟩ => unch_work hA.2.2 hm (by rw [hF]; omega) (by rw [hF, length_le8]; omega)))
      fun s1 ⟨hA1, hk1, hs1, hm1⟩ => ?_
    have hR1 : (C.fa (j + 1) fb v M).MR m (fun _ => .w 0) s1 :=
      MR.grow (C := C.fa j fb v M) hR rfl (by change fb + 8 * (j + 2) + 16 ≤ C.T0; omega)
        (show j + 1 ≤ T.maxSlots by omega) hA1.1 hk1 hs1 (by rw [hm1, hF, h7]; rfl)
    refine T.toCore.runsTo_mono (zeros_ok k (j + 1) (by omega) hA1 hR1 (by rw [hs1]; exact h7) hfit hn hin'.right)
      fun s' ⟨hA', hR', hs', hab⟩ => ⟨?_, hR', fun r => by rw [hs', hs1], ?_⟩
    · refine hA'.congr ?_
      have e : (List.range (k + 1)).map (fun i => EOp.w (.stS (j + i) R7)) =
          EOp.w (.stS j R7) :: (List.range k).map fun i => EOp.w (.stS (j + 1 + i) R7) := by
        rw [List.range_succ_eq_map]; simp only [List.map_cons, List.map_map, Nat.add_zero]
        congr 1; apply List.map_congr_left; intro i _; simp only [Function.comp]; congr 2; omega
      rw [e]; simp only [Target.len, Target.words_cons, List.length_append]; omega
    · refine Above.trans (fun x h1 h2 => ?_) hab
      rw [hm1, hF]; exact Proven.Mach.Mem.wr_out (by rw [length_le8]; omega)


set_option maxHeartbeats 1000000 in
/-- **the prologue** of a function with `n` slots: from the state before its frame is opened (the arguments in
`r0 ..`) to its first block, with the relation for the new frame (cell 0: the return address; above it: the
memory as it was) -/
theorem pro_ok {m : Mem} {fb n : Nat} {F : Func Nat} {args : List Val} {s : T.S} {q t : Nat} {j : List EOp}
    {rest : List (BitVec 32)} (hA : C.AtQ s q) (hP : C.Pre m fb n s)
    (hj : T.jTo (q + T.len (Target.proF n F)) t = some j) (hin : InW C.W q (T.words (Target.proF n F ++ j) ++ rest))
    (hpl : F.params.length = args.length) (hp7 : F.params.length ≤ 7) (hps : ∀ p ∈ F.params, p < n)
    (hargs : ∀ i (h : i < args.length), T.get s (rk i) = C.repr m.blks args[i]) (hval : ∀ v ∈ args, Valid m.blks v) :
    T.runsTo s fun s' => C.AtQ s' t ∧
      (C.fa n fb (T.ra s) (T.mem s)).MR m (setMany (fun _ => .w 0) F.params args) s' := by
  have hin1 : InW C.W q (T.encO (.enterC n) ++ (T.encO (.w (.li R7 0)) ++ (T.words (Target.zeros n) ++
      (T.words (storeAll 0 F.params) ++ (T.words j ++ rest))))) := by
    simpa only [Target.proF, T.words_append, Target.words_cons, Target.words_nil, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append] using hin
  have hT := C.T0_le; obtain ⟨hw1, hw2⟩ := C.wR; have hlt := T.ramHi_lt
  have hcap := hP.cap; have hfit := hP.fit; have hal := hP.fal
  have hfr : (T.fr s).toNat = fb + 8 * (n + 1) := by rw [hP.fr, ofNat_toNat' (by omega)]
  have hO := C.dOW; unfold disjoint at hO; dsimp only at hO
  refine T.toCore.runsTo_trans (T.c_enterC hP.nsl (C.at_of hA hin1.left) (by omega) (by rw [hfr]; exact ⟨by omega, by omega⟩)
    (by rw [hfr]; omega) (fun i hi => C.wr _ _ (.inr ⟨by rw [hfr]; omega, by rw [hfr]; omega⟩)))
    fun s1 ⟨hok1, hk1, hpc1, hfr1, hs1, hm1⟩ => ?_
  rw [hfr, show fb + 8 * (n + 1) - 8 * (n + 1) = fb by omega] at hfr1 hm1
  have hl8 : ∀ x : BitVec 64, (le8 x).length = 8 := length_le8
  have hA1 : C.AtQ s1 (q + (T.encO (.enterC n)).length) :=
    ⟨hok1, by rw [← next_add]; exact hpc1, unch_work hP.unch hm1 (by omega) (by rw [hl8]; omega)⟩
  have hR1 : (C.fa 0 fb (T.ra s) (T.mem s)).MR m (fun _ => .w 0) s1 := {
    ok := hok1
    keep := T.keepC_trans hP.keep hk1
    fr := hfr1
    rlim := by rw [hs1]; exact hP.rlim
    rin := by rw [hs1]; exact hP.rin
    rhp := by rw [hs1]; exact hP.rhp
    cap := hcap
    fit := by change fb + 8 * (0 + 1) + 16 ≤ C.T0; omega
    fal := hal
    nsl := Nat.zero_le _
    saved := by
      change bytes (T.mem s1) fb 8 = _
      have e := @bytes_wr_self (T.mem s) fb (le8 (T.ra s)); rw [hl8] at e; rw [hm1, e]; rfl
    stub := by change bytes (T.mem s1) (C.T0 - 16) 8 = _; rw [hm1, bytes_wr_out (.inr (by rw [hl8]; omega))]; exact hP.stub
    above := fun x h1 h2 => by
      change fb + 8 * (0 + 1) ≤ x at h1; rw [hm1]; exact Proven.Mach.Mem.wr_out (by rw [hl8]; omega)
    slots := fun j hj => absurd hj (Nat.not_lt_zero _)
    cells := fun g v hg => by
      have : g < m.cells.length := (List.getElem?_eq_some_iff.1 hg).1
      change bytes (T.mem s1) (C.wb + 8 * g) 8 = _
      rw [hm1, bytes_wr_out (.inl (by omega))]; exact hP.cells g v hg
    out := fun i b hi => by
      have : i < m.out.length := (List.getElem?_eq_some_iff.1 hi).1
      have := hP.outL
      change T.mem s1 (C.outA + i) = _
      rw [hm1, Proven.Mach.Mem.wr_out (by rw [hl8]; omega)]; exact hP.out i b hi
    outL := hP.outL
    unch := hA1.2.2
    valid := fun _ => trivial
    mok := ⟨hP.mok.inp, hP.mok.blks, hP.mok.cv⟩ }
  refine T.toCore.runsTo_trans (Ctx.reg_ok (C := C.fa 0 fb (T.ra s) (T.mem s)) (o := .w (.li R7 0)) (d := R7) hA1 hR1 hin1.right (by decide)
    fun h => T.w_li h) fun s2 ⟨hA2, hR2, st2⟩ => ?_
  have hz := zeros_ok (C := C) (M := T.mem s) (v := T.ra s) (fb := fb) (n := n) n 0 (by omega) hA2 hR2
    (by rw [Core.Set1.same T.toCore st2]) (by omega) hP.nsl
    (rest := T.words (storeAll 0 F.params) ++ (T.words j ++ rest))
    (by simpa only [Target.zeros, Nat.zero_add] using hin1.right.right)
  refine T.toCore.runsTo_trans hz fun s3 ⟨hA3, hR3, hs3, _⟩ => ?_
  have hin3 : InW C.W (q + (T.encO (.enterC n)).length + (T.encO (.w (.li R7 0))).length +
      T.len ((List.range n).map fun i => EOp.w (.stS (0 + i) R7))) (T.words (storeAll 0 F.params) ++ (T.words j ++ rest)) := by
    have := hin1.right.right.right
    simpa only [Target.zeros, Nat.zero_add, Target.len] using this
  refine T.toCore.runsTo_trans (Ctx.storeAll_ok (C := C.fa n fb (T.ra s) (T.mem s)) F.params args 0 hA3 hR3 hpl (by omega) hps hval
    (fun i h h' => by
      have hne : rk (0 + i) ≠ R7 := by
        intro e; have := congrArg Fin.val e; rw [Nat.zero_add, rk_lt (by omega)] at this
        simp [R7] at this; omega
      rw [hs3, Core.Set1.other T.toCore st2 hne, hs1, Nat.zero_add]
      exact hargs i h') hin3) fun s4 ⟨hA4, hR4⟩ => ?_
  have hq4 : q + (T.encO (.enterC n)).length + (T.encO (.w (.li R7 0))).length +
      T.len ((List.range n).map fun i => EOp.w (.stS (0 + i) R7)) + T.len (storeAll 0 F.params) = q + T.len (Target.proF n F) := by
    simp only [Target.proF, Target.len_append, Target.len_cons, Target.len_nil, Target.zeros, Nat.zero_add]; omega
  rw [hq4] at hA4
  have hin4 := hin3.right
  rw [← Target.len, hq4] at hin4
  exact T.toCore.runsTo_mono (Ctx.jTo_ok (C := C.fa n fb (T.ra s) (T.mem s)) hA4 hR4 hj hin4) fun s5 ⟨hA5, hR5⟩ => ⟨hA5, hR5⟩


theorem next_call (pc : BitVec 64) (q t : Nat) : next pc q + BitVec.ofInt 64 (4 * ((t : Int) - q)) = next pc t := by
  rcases Nat.le_total q t with h | h
  · have e : (4 * ((t : Int) - q)) = ((4 * (t - q) : Nat) : Int) := by omega
    rw [e, BitVec.ofInt_natCast, show next pc q + BitVec.ofNat 64 (4 * (t - q)) = next (next pc q) (t - q) from rfl,
      next_add]; congr 1; omega
  · have e : (4 * ((t : Int) - q)) = -((4 * (q - t) : Nat) : Int) := by omega
    rw [e, BitVec.ofInt_neg, BitVec.ofInt_natCast, ← BitVec.sub_eq_add_neg]
    exact next_back pc h

theorem rk_ne_big {i : Nat} (hi : i < 7) {r : Reg} (hr : 7 ≤ r.val) : rk i ≠ r := by
  intro e; have := congrArg Fin.val e; rw [rk_lt (by omega)] at this; omega

/-- what the memory `M` holds for the current frame: its slots, its cell 0, and above it what the frame expects -/
structure Snap (C : Ctx T) (m : Mem) (regs : Nat → Val) (M : Nat → Option (BitVec 8)) : Prop where
  slots : ∀ j, j < C.nS → bytes M (C.F0 + 8 * (j + 1)) 8 = (le8 (C.repr m.blks (regs j))).map some
  saved : bytes M C.F0 8 = (le8 C.sv).map some
  above : ∀ x, C.F0 + 8 * (C.nS + 1) ≤ x → x < C.T0 → M x = C.hm x

theorem MR.snap {m : Mem} {regs : Nat → Val} {s : T.S} (h : C.MR m regs s) : C.Snap m regs (T.mem s) :=
  ⟨h.slots, h.saved, h.above⟩

/-- **a call site**: the arguments, the check that the callee's frame fits below this one (else the exit), the
call, the callee's prologue; the callee's frame has the return address in cell 0 and the memory above it as it
was at the call -/
theorem call_ok {E : Env} {m : Mem} {regs : Nat → Val} {s : T.S} {q ex t : Nat} {ds : List Nat} {g : FId}
    {as : List (Arg Nat)} {cc jg : List EOp} {rest rest' rest'' : List (BitVec 32)} {G : Func Nat}
    (hA : C.AtQ s q) (hR : C.MR m regs s)
    (hc : T.emitCall E C.nS ex q ds g as = some cc) (hin : InW C.W q (T.words cc ++ rest))
    (hex : InW C.W ex (T.encO .exit ++ rest')) (hfs : E.fs g = G.slots)
    (hjg : T.jTo (E.fq g + T.len (Target.proF G.slots G)) t = some jg)
    (hpro : InW C.W (E.fq g) (T.words (Target.proF G.slots G ++ jg) ++ rest''))
    (hpl : G.params.length = as.length) (hps : ∀ p ∈ G.params, p < G.slots) :
    T.runsTo s fun s' =>
      (∃ c1 M, cc = c1 ++ Target.callPost G.slots ds ∧ C.Snap m regs M ∧ C.AtQ s' t ∧
        8 * (G.slots + 1) ≤ C.F0 - (C.wb + 8 * m.cells.length) ∧
        (C.fa G.slots (C.F0 - 8 * (G.slots + 1)) (next C.pc0 (q + T.len c1)) M).MR m
          (setMany (fun _ => .w 0) G.params (as.map (Arg.eval regs))) s') ∨
      (C.F0 - (C.wb + 8 * m.cells.length) < 8 * (G.slots + 1) ∧ C.Exited s') := by
  unfold Target.emitCall at hc
  split at hc
  · next hcond =>
    obtain ⟨ha7, hd7, hok, hdok, hfp, hns, h64, hbr⟩ := hcond
    rw [hfs] at hns h64 hc
    cases hct : T.callTo ex G.slots (q + T.len (loadAll 0 as)) (E.fq g) with
    | none => rw [hct] at hc; exact nomatch hc
    | some c2 =>
    rw [hct] at hc; cases hc
    unfold Target.callTo at hct
    cases hj : T.jW (q + T.len (loadAll 0 as) + T.len (T.chkPre G.slots)) ex with
    | none => rw [hj] at hct; exact nomatch hct
    | some j =>
    rw [hj] at hct; simp only at hct
    split at hct
    case isFalse => exact nomatch hct
    rename_i hcall
    cases hct
    generalize hd : ((E.fq g : Nat) : Int) - ((q + T.len (loadAll 0 as) + T.len (T.chkPre G.slots ++
      [j, .w (.bin .sub RLim RLim R8)]) : Nat) : Int) = d at hin hcall
    generalize hq1 : q + T.len (loadAll 0 as) = q1 at hj hd
    have hin0 : InW C.W q (T.words (loadAll 0 as) ++ (T.encO (.w (.bin .sub R7 RLim RHp)) ++
        (T.encO (.w (.li R8 (BitVec.ofNat 64 (8 * (G.slots + 1))))) ++
        (T.encO (.w (.br .geu R7 (some R8) false (T.lenBr + T.lenJ))) ++ (T.encO j ++
        (T.encO (.w (.bin .sub RLim RLim R8)) ++ (T.encO (.call d) ++
        (T.words (Target.callPost G.slots ds) ++ rest)))))))) := by
      simpa only [Target.chkPre, T.words_append, Target.words_cons, Target.words_nil, List.append_nil,
        List.append_assoc, List.cons_append, List.nil_append] using hin
    -- the arguments
    refine T.toCore.runsTo_trans (C.loadAll_ok as 0 hA hR (by omega) hok hin0) fun s1 ⟨hA1, hR1, hv1, _⟩ => ?_
    rw [hq1] at hA1
    have hin1 := hin0.right
    rw [show q + (T.words (loadAll 0 as)).length = q1 from hq1] at hin1
    have hcap := hR.cap; have hfit := hR.fit; have hal := hR.fal; have hT := C.T0_le
    obtain ⟨hw1, hw2⟩ := C.wR; have hlt := T.ramHi_lt
    -- r7 := free bytes, r8 := frame bytes
    refine T.toCore.runsTo_trans (C.reg_ok hA1 hR1 hin1 (by decide) fun h => T.w_bin h) fun s2 ⟨hA2, hR2, st2⟩ => ?_
    refine T.toCore.runsTo_trans (C.reg_ok hA2 hR2 hin1.right (by decide) fun h => T.w_li h) fun s3 ⟨hA3, hR3, st3⟩ => ?_
    have e7 : T.get s3 R7 = BitVec.ofNat 64 (C.F0 - (C.wb + 8 * m.cells.length)) := by
      rw [Core.Set1.other T.toCore st3 (by decide), Core.Set1.same T.toCore st2, hR1.rlim, hR1.rhp,
        bv_sub _ _ hcap (by omega)]
    have e8 : T.get s3 R8 = BitVec.ofNat 64 (8 * (G.slots + 1)) := Core.Set1.same T.toCore st3
    have hin3 := hin1.right.right
    refine T.toCore.runsTo_trans (C.br_ok hA3 hR3 hin3 hbr (fun h => nomatch h)) fun s4 ⟨hR4, hs4, ht4, hf4⟩ => ?_
    simp only [Bool.false_eq_true, if_false] at ht4
    rw [e7, e8] at ht4 hf4
    have hfree : C.F0 - (C.wb + 8 * m.cells.length) < 2 ^ 64 := by omega
    have hlj := jW_len hj
    by_cases hfits : 8 * (G.slots + 1) ≤ C.F0 - (C.wb + 8 * m.cells.length)
    · -- fits: over the jump, the frame limit down, the call
      have hA4 := ht4 (by
        simp only [Cond.eval, Bool.not_eq_true']; apply decide_eq_false; intro hlt'
        rw [BitVec.lt_def, ofNat_toNat' hfree, ofNat_toNat' h64] at hlt'; omega)
      have hin4 := hin3.right.right
      rw [T.len_brO, hlj] at hin4
      rw [show q1 + (T.encO (.w (.bin .sub R7 RLim RHp))).length +
          (T.encO (.w (.li R8 (BitVec.ofNat 64 (8 * (G.slots + 1)))))).length + (T.lenBr + T.lenJ) =
        q1 + (T.encO (.w (.bin .sub R7 RLim RHp))).length +
          (T.encO (.w (.li R8 (BitVec.ofNat 64 (8 * (G.slots + 1)))))).length + T.lenBr + T.lenJ by omega] at hA4
      refine T.toCore.runsTo_trans (C.op hA4 hin4 fun h => T.toCore.runsTo_mono (T.w_bin h)
        fun s' ⟨d', st, hm⟩ => ⟨d', hm, st⟩) fun s5 ⟨hA5, hk5, hm5, st5⟩ => ?_
      have hin5 := hin4.right
      have hAt := C.at_of hA5 hin5.left
      refine T.toCore.runsTo_trans (T.c_call hcall hAt) fun s6 ⟨hok6, hk6, hpc6, hra6, hfr6, hs6, hm6⟩ => ?_
      have hqc : q1 + (T.encO (.w (.bin .sub R7 RLim RHp))).length +
          (T.encO (.w (.li R8 (BitVec.ofNat 64 (8 * (G.slots + 1)))))).length + T.lenBr + T.lenJ +
          (T.encO (.w (.bin .sub RLim RLim R8))).length =
          q1 + T.len (T.chkPre G.slots ++ [j, .w (.bin .sub RLim RLim R8)]) := by
        simp only [Target.chkPre, Target.len_append, Target.len_cons, Target.len_nil, T.len_brO, hlj]; omega
      rw [hqc, ← hd, next_call] at hpc6
      rw [hqc] at hra6
      have hm64 : T.mem s6 = T.mem s4 := by rw [hm6, hm5]
      have hreg : ∀ r : Reg, r ≠ RLim → T.get s6 r = T.get s4 r := fun r hr => by
        rw [hs6, Core.Set1.other T.toCore st5 hr]
      have hU6 : C.Unch s6 := fun a h1 h2 => by rw [hm64]; exact hR4.unch a h1 h2
      have hP : C.Pre m (C.F0 - 8 * (G.slots + 1)) G.slots s6 := {
        ok := hok6
        keep := T.keepC_trans (T.keepC_trans hR4.keep (T.keepC_of_keepF (T.keepF_of_keep hk5))) hk6
        fr := by rw [hfr6, T.keep_fr hk5, hR4.fr]; congr 1; omega
        rlim := by
          rw [hs6, Core.Set1.same T.toCore st5, hR4.rlim, hs4, e8]
          exact bv_sub _ _ (by omega) (by omega)
        rin := by rw [hreg _ (by decide)]; exact hR4.rin
        rhp := by rw [hreg _ (by decide)]; exact hR4.rhp
        cap := by omega
        fit := by omega
        fal := by have := hR.fal; omega
        nsl := hns
        stub := by rw [hm64]; exact hR4.stub
        cells := fun g' v hg => by rw [hm64]; exact hR4.cells g' v hg
        out := fun i b hi => by rw [hm64]; exact hR4.out i b hi
        outL := hR4.outL
        unch := hU6
        mok := hR4.mok }
      have hA6 : C.AtQ s6 (E.fq g) := ⟨hok6, hpc6, hU6⟩
      have hargs : ∀ i (h : i < (as.map (Arg.eval regs)).length), T.get s6 (rk i) = C.repr m.blks (as.map (Arg.eval regs))[i] := by
        intro i h
        simp only [List.length_map] at h
        rw [hreg _ (rk_ne_big (by omega) (by decide)), hs4, Core.Set1.other T.toCore st3 (rk_ne_big (by omega) (by decide)),
          Core.Set1.other T.toCore st2 (rk_ne_big (by omega) (by decide)), List.getElem_map]
        have := hv1 i h; rwa [Nat.zero_add] at this
      refine T.toCore.runsTo_mono (C.pro_ok hA6 hP hjg hpro (by simp [hpl]) (by omega) hps hargs
        (fun v hv => by
          obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv; exact valid_eval hR.valid a)) fun s7 ⟨hA7, hR7⟩ => ?_
      refine .inl ⟨loadAll 0 as ++ (T.chkPre G.slots ++ [j, .w (.bin .sub RLim RLim R8), .call d]), T.mem s4,
        by simp only [List.append_assoc], hR4.snap, hA7, hfits, ?_⟩
      rw [hra6, hm64] at hR7
      have hq7 : q1 + T.len (T.chkPre G.slots ++ [j, .w (.bin .sub RLim RLim R8)]) + T.lenCall =
          q + T.len (loadAll 0 as ++ (T.chkPre G.slots ++ [j, .w (.bin .sub RLim RLim R8), .call d])) := by
        rw [← hq1]; simp only [Target.len_append, Target.len_cons, Target.len_nil]
        have : (T.encO (EOp.call d)).length = T.lenCall := T.len_call d
        omega
      rw [next_add, hq7] at hR7
      exact hR7
    · -- does not fit: to the exit
      have hA4 := hf4 (by
        simp only [Cond.eval, Bool.not_eq_false']; apply decide_eq_true
        rw [BitVec.lt_def, ofNat_toNat' hfree, ofNat_toNat' h64]; omega)
      have hin4 := hin3.right
      rw [T.len_brO] at hin4
      have hpq : q1 + (T.encO (.w (.bin .sub R7 RLim RHp))).length +
          (T.encO (.w (.li R8 (BitVec.ofNat 64 (8 * (G.slots + 1)))))).length + T.lenBr = q1 + T.len (T.chkPre G.slots) := by
        simp only [Target.chkPre, Target.len_cons, Target.len_nil, T.len_brO]; omega
      rw [hpq] at hA4 hin4
      exact T.toCore.runsTo_trans (C.jW_ok hA4 hR4 hj hin4) fun s5 ⟨hA5, hR5, _⟩ =>
        T.toCore.runsTo_mono (C.exit_ok hA5 hR5 hex) fun s6 h6 => .inr ⟨by omega, h6⟩
  · exact nomatch hc


theorem storeRegs_ok {m : Mem} : ∀ (ps : List Nat) (rs : List Reg) (vs : List Val) {regs : Nat → Val} {s : T.S}
    {q : Nat} {rest : List (BitVec 32)}, C.AtQ s q → C.MR m regs s → rs.length = vs.length →
    (∀ p ∈ ps, p < C.nS) → (∀ v ∈ vs, Valid m.blks v) →
    (∀ i (h : i < rs.length) (h' : i < vs.length), T.get s rs[i] = C.repr m.blks vs[i]) →
    InW C.W q (T.words (storeRegs ps rs) ++ rest) →
    T.runsTo s fun s' => C.AtQ s' (q + T.len (storeRegs ps rs)) ∧ C.MR m (setMany regs ps vs) s'
  | [], _, _, regs, s, q, rest, hA, hR, _, _, _, _, _ =>
    T.runsTo_of ⟨hA.congr (by simp [Target.len, storeRegs, Target.words]), by simpa [setMany] using hR⟩
  | _ :: _, [], [], regs, s, q, rest, hA, hR, _, _, _, _, _ =>
    T.runsTo_of ⟨hA.congr (by simp [Target.len, storeRegs, Target.words]), by simpa [setMany] using hR⟩
  | _ :: _, [], _ :: _, _, _, _, _, _, _, hl, _, _, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, _, _, _, _, hl, _, _, _, _ => nomatch hl
  | p :: ps, r :: rs, v :: vs, regs, s, q, rest, hA, hR, hl, hp, hv, hg, hin => by
    simp only [List.length_cons] at hl
    have hin' : InW C.W q (T.words (.w (.stS p r) :: storeRegs ps rs) ++ rest) := hin
    refine T.toCore.runsTo_trans (C.stS_ok hA hR hin'.cons (hp p (List.mem_cons_self ..))
      (hg 0 (by simp) (by simp)) (hv v (List.mem_cons_self ..))) fun s1 ⟨hA1, hR1, hs1⟩ => ?_
    refine T.toCore.runsTo_mono (storeRegs_ok ps rs vs hA1 hR1 (by omega)
      (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (fun x hx => hv x (List.mem_cons_of_mem _ hx))
      (fun i h h' => by rw [hs1]; exact hg (i + 1) (by simp; omega) (by simp; omega)) hin'.next)
      fun s' ⟨hA', hR'⟩ => ⟨hA'.congr (by simp only [Target.len, storeRegs, Target.words, List.length_append]; omega), hR'⟩

theorem storeRegs_take : ∀ (ps : List Nat) (rs : List Reg), storeRegs ps rs = storeRegs ps (rs.take ps.length)
  | [], _ => by simp [storeRegs]
  | _ :: _, [] => rfl
  | p :: ps, r :: rs => by simp only [storeRegs, List.length_cons, List.take_succ_cons]; rw [storeRegs_take ps rs]

theorem argRegs_get {i : Nat} (h : i < argRegs.length) : argRegs[i] = rk i := by
  simp [argRegs]

theorem argRegs_len : argRegs.length = 7 := by simp [argRegs]

/-- **the return** of a frame: the results into `r0 ..`, the frame closed, to the return address in cell 0 -/
theorem ret_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {vs : List (Arg Nat)} {rest : List (BitVec 32)}
    (hA : C.AtQ s q) (hR : C.MR m regs s) (hv7 : vs.length ≤ 7) (hok : vs.all (okA C.nS) = true)
    (hin : InW C.W q (T.words (loadAll 0 vs ++ [.leaveC C.nS, .w .ret]) ++ rest)) (hret : T.retOK C.sv) :
    T.runsTo s fun s' => T.pcIs s' C.sv ∧ C.Pre m C.F0 C.nS s' ∧
      (∀ x, C.F0 + 8 * (C.nS + 1) ≤ x → x < C.T0 → T.mem s' x = C.hm x) ∧
      ∀ i (h : i < vs.length), T.get s' (rk i) = C.repr m.blks (vs[i].eval regs) := by
  have hin0 : InW C.W q (T.words (loadAll 0 vs) ++ (T.encO (.leaveC C.nS) ++ (T.encO (.w .ret) ++ rest))) := by
    simpa only [T.words_append, Target.words_cons, Target.words_nil, List.append_nil, List.append_assoc] using hin
  refine T.toCore.runsTo_trans (C.loadAll_ok vs 0 hA hR (by omega) hok hin0) fun s1 ⟨hA1, hR1, hv1, _⟩ => ?_
  have hin1 := hin0.right
  have hF := hR1.F0_lt; have hal := hR1.F0_al; have hcap := hR1.cap; have hfit := hR1.fit; have hT := C.T0_le
  obtain ⟨hw1, hw2⟩ := C.wR; have hlt := T.ramHi_lt
  have hfr : (T.fr s1).toNat = C.F0 := by rw [hR1.fr, ofNat_toNat' (by omega)]
  refine T.toCore.runsTo_trans (T.c_leaveC (w := C.sv) hR1.nsl (C.at_of hA1 hin1.left) (by rw [hfr]; exact ⟨by omega, by omega⟩)
    (by rw [hfr]; exact hal) (by rw [hfr]; exact hR1.saved)) fun s2 ⟨hok2, hk2, hpc2, hra2, hfr2, hs2, hm2⟩ => ?_
  have hAt2 : T.At s2 (next (next C.pc0 (q + (T.words (loadAll 0 vs)).length)) (T.encO (.leaveC C.nS)).length)
      (T.encO (.w .ret)) := by
    have := C.at_of (s := s2) (q := q + (T.words (loadAll 0 vs)).length + (T.encO (.leaveC C.nS)).length)
      ⟨hok2, by rw [← next_add]; exact hpc2, fun a h1 h2 => by rw [hm2]; exact hA1.2.2 a h1 h2⟩ hin1.right.left
    rw [next_add]; exact this
  refine T.toCore.runsTo_mono (T.w_ret (by rw [hra2]; exact hret) hAt2) fun s3 ⟨d3, hs3, hm3⟩ => ?_
  have hreg : ∀ r, T.get s3 r = T.get s1 r := fun r => by rw [hs3, hs2]
  have hm31 : T.mem s3 = T.mem s1 := by rw [hm3, hm2]
  refine ⟨by rw [← hra2]; exact d3.hpc, ?_, ?_, fun i h => by rw [hreg]; have := hv1 i h; rwa [Nat.zero_add] at this⟩
  · exact {
      ok := d3.ok
      keep := T.keepC_trans (T.keepC_trans hR1.keep hk2) (T.keepC_of_keepF (T.keepF_of_keep d3.keep))
      fr := by rw [T.keep_fr d3.keep, hfr2, hfr]
      rlim := by rw [hreg]; exact hR1.rlim
      rin := by rw [hreg]; exact hR1.rin
      rhp := by rw [hreg]; exact hR1.rhp
      cap := hcap
      fit := hfit
      fal := hal
      nsl := hR1.nsl
      stub := by rw [hm31]; exact hR1.stub
      cells := fun g v hg => by rw [hm31]; exact hR1.cells g v hg
      out := fun i b hi => by rw [hm31]; exact hR1.out i b hi
      outL := hR1.outL
      unch := fun a h1 h2 => by rw [hm31]; exact hR1.unch a h1 h2
      mok := hR1.mok }
  · intro x h1 h2; rw [hm31]; exact hR1.above x h1 h2

/-- **after the return** (at the return address): the frame limit back up (the callee had `n` slots), the
results from `r0 ..` into their slots -/
theorem resume_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q n : Nat} {ds : List Nat} {vals : List Val}
    {rest : List (BitVec 32)} (hA : C.AtQ s q) (hP : C.Pre m (C.F0 - 8 * (n + 1)) n s) (hn8 : 8 * (n + 1) ≤ C.F0)
    (hsnap : C.Snap m regs (T.mem s)) (hvalid : ∀ j, Valid m.blks (regs j)) (hnsl : C.nS ≤ T.maxSlots)
    (hfitc : C.F0 + 8 * (C.nS + 1) + 16 ≤ C.T0) (hfal : C.F0 % 8 = 0) (h64 : 8 * (n + 1) < 2 ^ 64)
    (hin : InW C.W q (T.words (Target.callPost n ds) ++ rest)) (hds : ∀ d ∈ ds, d < C.nS)
    (hdl : ds.length = vals.length) (hd7 : ds.length ≤ 7)
    (hvals : ∀ i (h : i < vals.length), T.get s (rk i) = C.repr m.blks vals[i]) (hvv : ∀ v ∈ vals, Valid m.blks v) :
    T.runsTo s fun s' => C.AtQ s' (q + T.len (Target.callPost n ds)) ∧ C.MR m (setMany regs ds vals) s' := by
  have hin0 : InW C.W q (T.encO (.w (.li R9 (BitVec.ofNat 64 (8 * (n + 1))))) ++
      (T.encO (.w (.bin .add RLim RLim R9)) ++ (T.words (storeRegs ds argRegs) ++ rest))) := by
    simpa only [Target.callPost, T.words_append, Target.words_cons, Target.words_nil, List.append_nil,
      List.append_assoc, List.cons_append, List.nil_append] using hin
  refine T.toCore.runsTo_trans (C.op hA hin0 fun h => T.toCore.runsTo_mono (T.w_li h)
    fun s' ⟨d', st, hm⟩ => ⟨d', hm, st⟩) fun s1 ⟨hA1, hk1, hm1, st1⟩ => ?_
  refine T.toCore.runsTo_trans (C.op hA1 hin0.right fun h => T.toCore.runsTo_mono (T.w_bin h)
    fun s' ⟨d', st, hm⟩ => ⟨d', hm, st⟩) fun s2 ⟨hA2, hk2, hm2, st2⟩ => ?_
  have hm20 : T.mem s2 = T.mem s := by rw [hm2, hm1]
  have hT := C.T0_le; obtain ⟨hw1, hw2⟩ := C.wR; have hlt := T.ramHi_lt; have hcap := hP.cap
  have hreg : ∀ r : Reg, r ≠ RLim → r ≠ R9 → T.get s2 r = T.get s r := fun r h1 h2 => by
    rw [Core.Set1.other T.toCore st2 h1, Core.Set1.other T.toCore st1 h2]
  have hR2 : C.MR m regs s2 := {
    ok := hA2.1
    keep := T.keepC_trans hP.keep (T.keepC_of_keepF (T.keepF_of_keep (T.keep_trans hk1 hk2)))
    fr := by rw [T.keep_fr hk2, T.keep_fr hk1, hP.fr]; congr 1; omega
    rlim := by
      rw [Core.Set1.same T.toCore st2, Core.Set1.other T.toCore st1 (by decide), Core.Set1.same T.toCore st1, hP.rlim]
      show BitVec.ofNat 64 _ + BitVec.ofNat 64 _ = _
      rw [bv_ofNat_add]; congr 1; omega
    rin := by rw [hreg _ (by decide) (by decide)]; exact hP.rin
    rhp := by rw [hreg _ (by decide) (by decide)]; exact hP.rhp
    cap := by omega
    fit := hfitc
    fal := hfal
    nsl := hnsl
    saved := by rw [hm20]; exact hsnap.saved
    stub := by rw [hm20]; exact hP.stub
    above := fun x h1 h2 => by rw [hm20]; exact hsnap.above x h1 h2
    slots := fun j hj => by rw [hm20]; exact hsnap.slots j hj
    cells := fun g v hg => by rw [hm20]; exact hP.cells g v hg
    out := fun i b hi => by rw [hm20]; exact hP.out i b hi
    outL := hP.outL
    unch := hA2.2.2
    valid := hvalid
    mok := hP.mok }
  have hin2 := hin0.right.right
  rw [storeRegs_take] at hin2
  refine T.toCore.runsTo_mono (storeRegs_ok ds (argRegs.take ds.length) vals hA2 hR2
    (by simp [argRegs_len]; omega) hds hvv (fun i h h' => ?_) hin2) fun s' ⟨hA', hR'⟩ => ⟨hA'.congr ?_, hR'⟩
  · simp only [List.getElem_take]
    rw [argRegs_get (by rw [argRegs_len]; simp at h; omega), hreg _ (rk_ne_big (by omega) (by decide))
      (rk_ne_big (by omega) (by decide))]
    exact hvals i h'
  · simp only [Target.callPost, Target.len_append, Target.len_cons, Target.len_nil]; rw [← storeRegs_take]; omega

end Ctx
end Proven.Ir
