/- Edges: the arguments of a jump into `r0 ..`, then into the target block's parameter slots (a parallel
assignment), then to the target block; branch tests on IR values. -/
import Compiler.Ir.EmitAlloc

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

theorem rk_lt {k : Nat} (h : k < 15) : (rk k).val = k := rk_val h

theorem rk_ne {j k : Nat} (hj : j < 15) (hk : k < 15) (h : j ≠ k) : rk j ≠ rk k := fun e =>
  h (by have := congrArg Fin.val e; rwa [rk_lt hj, rk_lt hk] at this)

namespace Ctx
variable {T : Target} {C : Ctx T}

theorem loadAll_ok {m : Mem} {regs : Nat → Val} : ∀ (as : List (Arg Nat)) (k : Nat) {s : T.S} {q : Nat}
    {rest : List (BitVec 32)}, C.AtQ s q → C.MR m regs s → k + as.length ≤ 7 → as.all (okA C.nS) = true →
    InW C.W q (T.words (loadAll k as) ++ rest) →
    T.runsTo s fun s' => C.AtQ s' (q + T.len (loadAll k as)) ∧ C.MR m regs s' ∧
      (∀ i (h : i < as.length), T.get s' (rk (k + i)) = C.repr m.blks (as[i].eval regs)) ∧
      (∀ j, j < k → T.get s' (rk j) = T.get s (rk j))
  | [], k, s, q, rest, hA, hR, _, _, _ =>
    T.runsTo_of ⟨hA.congr (by simp [Target.len, loadAll, Target.words]), hR, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ => rfl⟩
  | a :: as, k, s, q, rest, hA, hR, hk, hok, hin => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [List.length_cons] at hk
    have hin' : InW C.W q (T.words (ldArg (rk k) a :: loadAll (k + 1) as) ++ rest) := hin
    refine T.toCore.runsTo_trans (C.ldArg_ok hA hR hin'.cons (by rw [rk_lt (by omega)]; omega) hok.1)
      fun s1 ⟨hA1, hR1, st1⟩ => ?_
    refine T.toCore.runsTo_mono (loadAll_ok as (k + 1) hA1 hR1 (by omega) hok.2 hin'.next) fun s' ⟨hA', hR', hv, hj⟩ =>
      ⟨hA'.congr (by simp only [Target.len, loadAll, Target.words, List.length_append]; omega), hR', fun i hi => ?_,
        fun j hj' => ?_⟩
    · cases i with
      | zero => rw [Nat.add_zero, hj k (by omega)]; exact Core.Set1.same T.toCore st1
      | succ i =>
        have := hv i (by simp only [List.length_cons] at hi; omega)
        rw [show k + (i + 1) = k + 1 + i by omega]; exact this
    · rw [hj j (by omega), Core.Set1.other T.toCore st1 (rk_ne (by omega) (by omega) (by omega))]

theorem storeAll_ok {m : Mem} : ∀ (ps : List Nat) (vs : List Val) (k : Nat) {regs : Nat → Val} {s : T.S} {q : Nat}
    {rest : List (BitVec 32)}, C.AtQ s q → C.MR m regs s → ps.length = vs.length → k + ps.length ≤ 7 →
    (∀ p ∈ ps, p < C.nS) → (∀ v ∈ vs, Valid m.blks v) →
    (∀ i (h : i < ps.length) (h' : i < vs.length), T.get s (rk (k + i)) = C.repr m.blks vs[i]) →
    InW C.W q (T.words (storeAll k ps) ++ rest) →
    T.runsTo s fun s' => C.AtQ s' (q + T.len (storeAll k ps)) ∧ C.MR m (setMany regs ps vs) s'
  | [], _, k, regs, s, q, rest, hA, hR, _, _, _, _, _, _ =>
    T.runsTo_of ⟨hA.congr (by simp [Target.len, storeAll, Target.words]), by simpa [setMany] using hR⟩
  | p :: ps, [], _, _, _, _, _, _, _, hl, _, _, _, _, _ => nomatch hl
  | p :: ps, v :: vs, k, regs, s, q, rest, hA, hR, hl, hk, hp, hv, hg, hin => by
    simp only [List.length_cons] at hl hk
    have hin' : InW C.W q (T.words (.w (.stS p (rk k)) :: storeAll (k + 1) ps) ++ rest) := hin
    refine T.toCore.runsTo_trans (C.stS_ok hA hR hin'.cons (hp p (List.mem_cons_self ..))
      (by have := hg 0 (by simp) (by simp); rwa [Nat.add_zero] at this) (hv v (List.mem_cons_self ..)))
      fun s1 ⟨hA1, hR1, hs1⟩ => ?_
    refine T.toCore.runsTo_mono (storeAll_ok ps vs (k + 1) hA1 hR1 (by omega) (by omega)
      (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (fun x hx => hv x (List.mem_cons_of_mem _ hx))
      (fun i h h' => by
        rw [hs1, show k + 1 + i = k + (i + 1) by omega]
        exact hg (i + 1) (by simp; omega) (by simp; omega)) hin'.next) fun s' ⟨hA', hR'⟩ =>
      ⟨hA'.congr (by simp only [Target.len, storeAll, Target.words, List.length_append]; omega), hR'⟩

/-- **an edge**: the arguments into the parameters of `l`, then to `l` -/
theorem edge_ok {F : Func Nat} {pos : Lbl → Nat} {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {l : Lbl}
    {as : List (Arg Nat)} {os : List EOp} {rest : List (BitVec 32)} {B : Block Nat}
    (hA : C.AtQ s q) (hR : C.MR m regs s) (he : T.edge F C.nS pos q l as = some os)
    (hin : InW C.W q (T.words os ++ rest)) (hB : F.blocks.lookup l = some B) :
    T.runsTo s fun s' => C.AtQ s' (pos l) ∧ C.MR m (setMany regs B.params (as.map (Arg.eval regs))) s' := by
  unfold Target.edge at he
  rw [hB] at he
  simp only at he
  split at he
  · next hc =>
    obtain ⟨hl, h7, hok, hps⟩ := hc
    cases hj : T.jTo (q + T.len (loadAll 0 as ++ storeAll 0 B.params)) (pos l) with
    | none => rw [hj] at he; exact nomatch he
    | some j =>
      rw [hj] at he; cases he
      have hin2 : InW C.W q (T.words (loadAll 0 as) ++ (T.words (storeAll 0 B.params) ++ (T.words j ++ rest))) := by
        simpa only [T.words_append, List.append_assoc] using hin
      have hvs : ∀ v ∈ as.map (Arg.eval regs), Valid m.blks v := by
        intro v hv
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
        exact valid_eval hR.valid a
      refine T.toCore.runsTo_trans (C.loadAll_ok as 0 hA hR (by omega) hok hin2) fun s1 ⟨hA1, hR1, hv1, _⟩ => ?_
      refine T.toCore.runsTo_trans (C.storeAll_ok B.params (as.map (Arg.eval regs)) 0 hA1 hR1
        (by simp only [List.length_map]; omega) (by omega)
        (fun p hp => by simpa using List.all_eq_true.1 hps p hp) hvs
        (fun i h h' => by rw [List.getElem_map]; exact hv1 i (by omega)) hin2.right) fun s2 ⟨hA2, hR2⟩ => ?_
      have epos : q + (T.words (loadAll 0 as)).length + (T.words (storeAll 0 B.params)).length =
          q + T.len (loadAll 0 as ++ storeAll 0 B.params) := by
        simp only [Target.len, T.words_append, List.length_append]; omega
      have hin3 := hin2.right.right; rw [epos] at hin3
      refine C.jTo_ok (hA2.congr ?_) hR2 hj hin3
      simp only [Target.len, T.words_append, List.length_append]; omega
  · exact nomatch he

end Ctx
end Proven.Ir
