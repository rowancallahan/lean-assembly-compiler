/- `Implements1` (`Spec/Implements1.lean`) for programs of the middle layer: any `Mach.BStmt` program run
as `compBF N [0, 3] [2]` (byte blocks: input = block 0, base in variable 0; output = block 1, base in
variable 3; word block 0 = the first `8 · wn n` bytes of the work block, base in variable 2; variable 1 =
the input length; `N` slots in a frame at the top of the work block, below `sp`) implements `f` with
`space n ≥ 8 · wn n + 8 (N + 1) + 7`, as soon as its source-level run computes `f` (`implements1_of_exec`).
Also the conversion of the older statements' proofs. -/
import Riscv.Back.BStmt
import Riscv.Back.Keep
import Riscv.Direct.SortMergeMachine
import Spec.Implements1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

theorem extract_cat8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (k : Nat) (hk : k < 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64).extractLsb' (8 * k) 8 =
      [b0, b1, b2, b3, b4, b5, b6, b7][k] := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  all_goals
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
      List.getElem_cons_zero, List.getElem_cons_succ]
    repeat' split
    all_goals first | omega | (congr 1; omega)

theorem le8_cat8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    Mach.le8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  apply List.ext_getElem (by rw [length_le8]; rfl)
  intro k h1 h2
  rw [length_le8] at h1
  simp only [Mach.le8, List.getElem_map, List.getElem_range]
  exact extract_cat8 b0 b1 b2 b3 b4 b5 b6 b7 k h1

/-- every byte list of length `8 k` is the bytes of `k` words -/
theorem exists_wbytes : ∀ (k : Nat) (l : List (BitVec 8)), l.length = 8 * k →
    ∃ ws : List (BitVec 64), ws.length = k ∧ wbytes ws = l
  | 0, [], _ => ⟨[], rfl, rfl⟩
  | 0, _ :: _, h => by simp at h
  | k + 1, l, h => by
    match l, h with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h =>
      have hr : rest.length = 8 * k := by simp only [List.length_cons] at h; omega
      obtain ⟨ws, hl, hw⟩ := exists_wbytes k rest hr
      exact ⟨(b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64) :: ws, by rw [List.length_cons, hl],
        by show Mach.le8 _ ++ wbytes ws = _; rw [le8_cat8, hw]; rfl⟩
    | [], h => simp at h
    | [_], h => simp at h; omega
    | [_, _], h => simp at h; omega
    | [_, _, _], h => simp at h; omega
    | [_, _, _, _], h => simp at h; omega
    | [_, _, _, _, _], h => simp at h; omega
    | [_, _, _, _, _, _], h => simp at h; omega
    | [_, _, _, _, _, _, _], h => simp at h; omega

theorem bytesAt_take' (s : St) (a : Nat) {k n : Nat} (h : k ≤ n) : (bytesAt s a n).take k = bytesAt s a k := by
  simp [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- from a source-level run of a `BStmt` program to `Implements1` -/
theorem implements1_of_exec {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (N : Nat) (hN : N ≤ 16) (prog : Mach.BStmt) (hwf : rvF.wfB N [0, 3] [2] prog) (wn : Nat → Nat)
    (space : Nat → Nat) (hsp : ∀ n, 8 * wn n + 8 * (N + 1) + 7 ≤ space n) (maxLen : Nat) (retLen : Bool)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (tbl : List (BitVec 64)) (env : Mach.BEnv),
      env 1 = BitVec.ofNat 64 (encA a).length → (∀ j, 8 ≤ j → env j = 0) → (encA a).length ≤ maxLen →
      (encA a).length < 2 ^ 32 → (encB (f a)).length ≤ out.length → out.length < 2 ^ 32 →
      tbl.length = wn (encA a).length →
      ∃ σ' out', Mach.BExec prog ⟨env, [(encA a).map (·.toBitVec), out], [tbl]⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) :
    Implements1With encA encB (rvF.codeF (rvF.compBF N [0, 3] [2] prog)) f space maxLen retLen := by
  intro a s entry ra input output work x y codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hws hwal hram hdis hmapO hmapW
  have hin : ∀ r ∈ [input, output, work, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rw' rc
  unfold Proven.disjoint at d12 d13 d14 d23 d24 d34
  simp only [codeR] at d14 d24 d34 rc
  have hil' : input.len = x.length := hil
  have hol' : y.length ≤ output.len := hol
  have hws' := hsp x.length
  have hws'' : space x.length ≤ work.len := hws
  have hxl : (x.map (·.toBitVec)).length = x.length := by simp
  -- the frame
  have hsp2 : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = work.base + work.len := by rw [hsp2]; exact toNat_ofNat' (by omega)
  have hfb : frameBase N (getX s 2) = (work.base + work.len) / 8 * 8 - 8 * (N + 1) := by
    unfold frameBase; rw [hspn]
  have hfb1 : work.base + 8 * wn x.length ≤ frameBase N (getX s 2) := by rw [hfb]; omega
  have hfb2 : frameBase N (getX s 2) + 8 * (N + 1) ≤ work.base + work.len := by rw [hfb]; omega
  have hf : FrOK N (frameBase N (getX s 2)) :=
    ⟨by rw [hfb]; omega, by omega, by omega, by unfold NS; omega⟩
  -- the initial heap
  obtain ⟨out0, hout0l, ho⟩ : ∃ out0 : List (BitVec 8), out0.length = output.len ∧
      bytesAt s output.base output.len = out0.map some :=
    ⟨_, by simp [bytesAt], bytesAt_hosted fun i hi => hmapO i hi⟩
  obtain ⟨tbl0, htl, htb⟩ : ∃ tbl0 : List (BitVec 64), tbl0.length = wn x.length ∧
      bytesAt s work.base (8 * wn x.length) = (wbytes tbl0).map some := by
    obtain ⟨ws, hl, hw⟩ := exists_wbytes (wn x.length) ((bytesAt s work.base (8 * wn x.length)).map (·.getD 0))
      (by simp [bytesAt])
    exact ⟨ws, hl, by rw [hw]; exact bytesAt_hosted fun i hi => hmapW i (by omega)⟩
  obtain ⟨σ', out', hexec, hh, htk, hdr, hrl⟩ := hex a out0 tbl0 (envOf s)
    (by simpa [envOf] using getX_of (h.x11.symm.trans h11) rfl) (fun j hj => by simp [envOf]; omega)
    hmax (by show x.length < 2 ^ 32; omega) (by show y.length ≤ out0.length; omega) (by omega) htl
  -- the layout
  let R : List Region := [⟨input.base, x.length⟩, ⟨output.base, output.len⟩]
  let W : List Region := [⟨work.base, 8 * wn x.length⟩]
  have hL : rvF.Lay N (rvF.frameAt s N) R W := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, List.pairwise_singleton _ _, fun r hr w hw => ?_, fun r hr => ?_,
      fun w hw => ?_, fun w hw => ?_⟩
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (show _ ∧ _; dsimp only; show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; omega)
    · simp only [W, List.mem_singleton] at hr; subst hr
      show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; dsimp only; omega
    · simp only [R, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold Mach.disjoint; dsimp only; omega
    · simp only [W, List.mem_singleton] at hw; subst hw
      simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Mach.disjoint; dsimp only; omega)
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      show Mach.disjoint ⟨frameBase N (getX s 2), _⟩ r
      rcases hr with rfl | rfl <;> (unfold Mach.disjoint; dsimp only; omega)
    · simp only [W, List.mem_singleton] at hw; subst hw
      show Mach.disjoint ⟨frameBase N (getX s 2), _⟩ _
      unfold Mach.disjoint; dsimp only; omega
    · simp only [W, List.mem_singleton] at hw; subst hw; exact hwal
  have hok : codeOK entry (rvF.codeF (rvF.compBF N [0, 3] [2] prog)).length := ⟨hal, rc.1, rc.2⟩
  have hcd : ∀ r ∈ R ++ W ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩],
      Mach.disjoint ⟨entry.toNat, 4 * (rvF.codeF (rvF.compBF N [0, 3] [2] prog)).length⟩ r := by
    intro r hr
    simp only [R, W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [show rvF.frameAt s N = frameBase N (getX s 2) from rfl] at hr
    show Mach.disjoint _ r
    rcases hr with rfl | rfl | rfl | rfl <;> (unfold Mach.disjoint; dsimp only)
    · omega
    · omega
    · omega
    · show _ ∨ frameBase N (getX s 2) + _ ≤ _; omega
  have hheap : rvF.HeapB [0, 3] [2] R W ⟨envOf s, [x.map (·.toBitVec), out0], [tbl0]⟩ s := by
    refine ⟨rfl, rfl, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, rfl, rfl, fun b hb => ?_, fun b hb => ?_,
      fun b hb => ?_⟩
    · obtain _ | _ | b := b
      · simpa [envOf] using getX_of (h.x10.symm.trans h10) rfl
      · simpa [envOf] using getX_of (h.x13.symm.trans h13) rfl
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | _ | b := b
      · simp [R]
      · simpa [R] using hout0l
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | _ | b := b
      · show bytes (rvF.mem s) input.base x.length = _
        exact (bytes_eq s _ _).trans (by simpa [List.map_map, Function.comp_def] using hx)
      · show bytes (rvF.mem s) output.base output.len = _
        exact (bytes_eq s _ _).trans (by simpa using ho)
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | b := b
      · simpa [envOf] using getX_of (h.x12.symm.trans h12) rfl
      · exact absurd hb (by show ¬(b + 1 < 1); omega)
    · obtain _ | b := b
      · show 8 * tbl0.length = 8 * wn x.length; rw [htl]
      · exact absurd hb (by show ¬(b + 1 < 1); omega)
    · obtain _ | b := b
      · show bytes (rvF.mem s) work.base (8 * wn x.length) = _
        exact (bytes_eq s _ _).trans htb
      · exact absurd hb (by show ¬(b + 1 < 1); omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (rvF.compBF_ok N [0, 3] [2] (by intro x hx; simp at hx; omega)
    (by intro x hx; simp at hx; omega) hwf hexec ⟨h, hpc, codeAt_of_codeBytes hok hcode, hok⟩ hf hL hcd
    (fun i => by show getX s (phys (avar i)) = _; rw [phys_avar]; simp [envOf])
    (fun j hj => by simp only [envOf]; rw [dite_neg' (by omega)]) hheap (by show (getX s 1).toNat % 2 = 0; rw [hra']; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  have e0 := p3.rbytes 0 (by simp [R]); have e1 := p3.rbytes 1 (by simp [R])
  simp only [hh] at e0 e1
  have e0' : bytesAt s' input.base x.length = (x.map (·.toBitVec)).map some := by
    have := (bytes_eq s' _ _).symm.trans e0; simpa using this
  have e1' : bytesAt s' output.base output.len = out'.map some := by
    have := (bytes_eq s' _ _).symm.trans e1; simpa using this
  refine ⟨by rw [← hra']; exact p1, ?_, ?_, abi_of_keep h p5 p6, p5, fun hr => ?_⟩
  · rw [← bytesAt_take' s' output.base hol', e1', ← List.map_take, htk]; simp [List.map_map, y]
  · intro q hq
    have a2 := hq ⟨output.base, y.length⟩ (by simp); have a3 := hq work (by simp)
    dsimp only at a2
    by_cases hqi : input.base ≤ q ∧ q < input.base + input.len
    · have e0x : bytesAt s' input.base x.length = bytesAt s input.base x.length := by
        rw [e0', hx, List.map_map]; rfl
      have := congrArg (·[q - input.base]?) e0x
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - input.base < x.length by omega),
        Option.map_some, Option.some.injEq] at this
      rwa [Nat.add_sub_cancel' hqi.1] at this
    by_cases hqo : output.base ≤ q ∧ q < output.base + output.len
    · have e1x : (bytesAt s' output.base output.len)[q - output.base]? =
          (bytesAt s output.base output.len)[q - output.base]? := by
        rw [e1', ho, List.getElem?_map, List.getElem?_map]
        have := congrArg (·[q - output.base - y.length]?) hdr
        simp only [List.getElem?_drop] at this
        rw [show y.length + (q - output.base - y.length) = q - output.base by omega] at this
        rw [this]
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - output.base < output.len by omega),
        Option.map_some, Option.some.injEq] at e1x
      rwa [Nat.add_sub_cancel' hqo.1] at e1x
    · apply p4 q
      intro r hr
      simp only [R, W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only
      · omega
      · omega
      · omega
      · show q < frameBase N (getX s 2) ∨ frameBase N (getX s 2) + _ ≤ q; omega

end Proven.Mach.Riscv
