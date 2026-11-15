/- Run-time memory at the source level (machine-independent): the memory events of a program's run.

The compiled code (`Compiler/MemCode.lean`) keeps word block 0 (the heap) at the bottom of the work block and
the stack of frames at the top.  The heap GROWS: an access of word `j` at or above its current length first
extends it with zero words to `j + 1` words (in memory the new words are zeroed); it never shrinks (the
program frees nothing).  A call opens a frame of `nlocals + 1` 8-byte cells and closes it on return.  The
memory events (`MemEvent`, `Compiler/AllocSpec.lean`, newest first) of a run are exactly these: `alloc d`
when the heap grows by `d` words, `alloc (n + 1)` on entering a function with `n` locals, `free (n + 1)`
on leaving it.  Cells are 8 bytes.  Global 7 holds the heap length (the run-time check reads it).

* `TExecB` / `TExec`: the run with events (heap unbounded); defined like `BExec` / `CExec`.
* `texec_of_cexec`: a `CExec` run on a zero heap of any length is a `TExec` run (from the empty heap)
  with heap length at most the old one and peak at most the start + growth + stack need: the old
  space bounds bound the new memory need.
* `texec_det`: two runs from states that differ only in unread data (the base addresses, the output
  block's contents) have the same events.

Pure Lean (core only). -/
import Compiler.CLang
import Compiler.AllocSpec

namespace Proven.Mach
open Proven.Top.Alloc

/-! ## events -/

theorem inUse_append_alloc : ∀ (X L : List MemEvent), inUse (X ++ L) = inUse (X ++ [.alloc (inUse L)])
  | [], L => by simp [inUse]
  | .alloc n :: X, L => by simp only [List.cons_append, inUse]; rw [inUse_append_alloc X L]
  | .free n :: X, L => by simp only [List.cons_append, inUse]; rw [inUse_append_alloc X L]

theorem inUse_le_peak : ∀ (L : List MemEvent), inUse L ≤ peak L
  | [] => Nat.le_refl _
  | e :: L => Nat.le_max_left _ _

theorem peak_append : ∀ (X L : List MemEvent), peak (X ++ L) = max (peak (X ++ [.alloc (inUse L)])) (peak L)
  | [], L => by
    simp only [List.nil_append, peak, inUse]
    have := inUse_le_peak L
    simp only [Nat.zero_add]; omega
  | e :: X, L => by
    have h := inUse_append_alloc (e :: X) L
    simp only [List.cons_append] at h
    simp only [List.cons_append, peak]
    rw [peak_append X L, h]; omega

theorem inUse_seq (E₁ E₂ : List MemEvent) (c : Nat) :
    inUse (E₂ ++ E₁ ++ [.alloc c]) = inUse (E₂ ++ [.alloc (inUse (E₁ ++ [.alloc c]))]) := by
  rw [List.append_assoc, inUse_append_alloc]

theorem peak_seq (E₁ E₂ : List MemEvent) (c : Nat) :
    peak (E₂ ++ E₁ ++ [.alloc c]) =
      max (peak (E₂ ++ [.alloc (inUse (E₁ ++ [.alloc c]))])) (peak (E₁ ++ [.alloc c])) := by
  rw [List.append_assoc, peak_append]

theorem peak_one (c : Nat) : peak [.alloc c] = c := by simp [peak, inUse]

theorem inUse_one (c : Nat) : inUse [.alloc c] = c := by simp [inUse]

/-- a call's events from `c` cells: frame, body, frame freed -/
theorem inUse_two (E : List MemEvent) (n c : Nat) :
    inUse (E ++ [.alloc n, .alloc c]) = inUse (E ++ [.alloc (c + n)]) := by
  rw [inUse_append_alloc]; simp [inUse]

theorem peak_two (E : List MemEvent) (n c : Nat) :
    peak (E ++ [.alloc n, .alloc c]) = peak (E ++ [.alloc (c + n)]) := by
  rw [peak_append, peak_append E [.alloc (c + n)]]; simp [peak, inUse]

theorem inUse_call (E : List MemEvent) (n c : Nat) :
    inUse ([.free n] ++ E ++ [.alloc n] ++ [.alloc c]) = inUse (E ++ [.alloc (c + n)]) - n := by
  simp only [List.cons_append, List.append_assoc, List.nil_append, inUse]
  rw [inUse_two]

theorem peak_ge (E : List MemEvent) (c : Nat) : c ≤ peak (E ++ [.alloc c]) := by
  rw [peak_append, peak_one]; exact Nat.le_max_right _ _

theorem peak_call (E : List MemEvent) (n c : Nat) :
    peak ([.free n] ++ E ++ [.alloc n] ++ [.alloc c]) =
      max (inUse (E ++ [.alloc (c + n)]) - n) (max (peak (E ++ [.alloc (c + n)])) c) := by
  have e1 := inUse_two E n c
  have e2 := peak_two E n c
  have e3 := peak_ge E (c + n)
  simp only [List.cons_append, List.append_assoc, List.nil_append, peak, inUse]
  rw [e1, e2]; omega

/-! ## the heap -/

/-- word block `W` grown with zero words to at least `n` words -/
def grow (W : List (BitVec 64)) (n : Nat) : List (BitVec 64) := W ++ List.replicate (n - W.length) 0

/-- the event of growing `W` to `n` words -/
def growE (W : List (BitVec 64)) (n : Nat) : List MemEvent := if W.length < n then [.alloc (n - W.length)] else []

theorem grow_length (W : List (BitVec 64)) (n : Nat) : (grow W n).length = max W.length n := by
  simp only [grow, List.length_append, List.length_replicate]; omega

theorem inUse_growE (W : List (BitVec 64)) (n c : Nat) :
    inUse (growE W n ++ [.alloc c]) = c + ((grow W n).length - W.length) := by
  rw [grow_length]; unfold growE; split <;> simp [inUse] <;> omega

theorem peak_growE (W : List (BitVec 64)) (n c : Nat) :
    peak (growE W n ++ [.alloc c]) = c + ((grow W n).length - W.length) := by
  rw [grow_length]; unfold growE; split <;> simp [peak, inUse] <;> omega

/-- the heap length lives in global 7 -/
def hvar : Nat := 7

/-- variables the compiled program never reads or writes: the byte block bases `0`, `3`, the heap base
`2` and the heap length `7` -/
def unread : List Nat := [0, 2, 3, 7]

def BExp.vars : BExp → List Nat
  | .var i => [i]
  | .const _ => []
  | .bin _ a b => a.vars ++ b.vars
  | .ite c a b => c.vars ++ a.vars ++ b.vars

/-- the expression reads no variable of `unread` -/
def BExp.clean (e : BExp) : Bool := e.vars.all fun x => !unread.contains x

/-- the statement reads and writes no variable of `unread`, loads bytes only from block 0 (the input),
accesses only word block 0, and has no multiply / divide (the plain back end has none) -/
def BStmt.clean : BStmt → Bool
  | .assign v e => !unread.contains v && e.clean
  | .load v b i => !unread.contains v && b == 0 && i.clean
  | .store _ i e => i.clean && e.clean
  | .seq p q => p.clean && q.clean
  | .loop c b => c.clean && b.clean
  | .load64 v b i => !unread.contains v && b == 0 && i.clean
  | .store64 b i e => b == 0 && i.clean && e.clean
  | .mop _ _ _ _ => false

def CStmt.clean : CStmt → Bool
  | .base p => p.clean
  | .seq p q => p.clean && q.clean
  | .ite c p q => c.clean && p.clean && q.clean
  | .loop c b => c.clean && b.clean
  | .call res _ args => !unread.contains res && args.all BExp.clean

def Fn.clean (F : Fn) : Bool := F.body.clean && F.ret.clean

def progClean (P : Prog) : Bool := P.all Fn.clean

theorem BExp.denote_clean {e : BExp} (h : e.clean = true) {env env' : BEnv}
    (he : ∀ x, x ∉ unread → env x = env' x) : e.denote env = e.denote env' := by
  induction e with
  | var i =>
    simp [BExp.clean, BExp.vars] at h
    exact he i (by simpa using h)
  | const c => rfl
  | bin op a b iha ihb =>
    simp only [BExp.clean, BExp.vars, List.all_append, Bool.and_eq_true] at h
    simp only [BExp.denote]; rw [iha h.1, ihb h.2]
  | ite c a b ihc iha ihb =>
    simp only [BExp.clean, BExp.vars, List.all_append, Bool.and_eq_true] at h
    simp only [BExp.denote]; rw [ihc h.1.1, iha h.1.2, ihb h.2]

theorem not_unread {v : Nat} (h : (!unread.contains v) = true) : v ∉ unread := by
  simpa using h

/-! ## the run with events -/

/-- a call-free statement with a growing word block 0 -/
inductive TExecB : BStmt → BState → List MemEvent → BState → Prop
  | assign {v e σ} : TExecB (.assign v e) σ [] ⟨σ.env.set v (e.denote σ.env), σ.heap, σ.wheap⟩
  | load {v b i σ} (hb : b < σ.heap.length) (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
      TExecB (.load v b i) σ [] ⟨σ.env.set v (σ.heap[b][(i.denote σ.env).toNat].setWidth 64), σ.heap, σ.wheap⟩
  | store {b i e σ} (hb : b < σ.heap.length) (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
      TExecB (.store b i e) σ []
        ⟨σ.env, σ.heap.set b (σ.heap[b].set (i.denote σ.env).toNat ((e.denote σ.env).setWidth 8)), σ.wheap⟩
  | seq {p q σ σ₁ σ₂ E₁ E₂} : TExecB p σ E₁ σ₁ → TExecB q σ₁ E₂ σ₂ → TExecB (.seq p q) σ (E₂ ++ E₁) σ₂
  | loopF {c b σ} : c.denote σ.env = 0 → TExecB (.loop c b) σ [] σ
  | loopT {c b σ σ₁ σ₂ E₁ E₂} : c.denote σ.env ≠ 0 → TExecB b σ E₁ σ₁ → TExecB (.loop c b) σ₁ E₂ σ₂ →
      TExecB (.loop c b) σ (E₂ ++ E₁) σ₂
  | load64 {v i env H W} :
      TExecB (.load64 v 0 i) ⟨env, H, [W]⟩ (growE W ((i.denote env).toNat + 1))
        ⟨(env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length)).set v
          ((grow W ((i.denote env).toNat + 1)).getD (i.denote env).toNat 0), H, [grow W ((i.denote env).toNat + 1)]⟩
  | store64 {i e env H W} :
      TExecB (.store64 0 i e) ⟨env, H, [W]⟩ (growE W ((i.denote env).toNat + 1))
        ⟨env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length), H,
          [(grow W ((i.denote env).toNat + 1)).set (i.denote env).toNat (e.denote env)]⟩

/-- a statement with calls: `CExec` with the growing heap and the frame events -/
inductive TExec (P : Prog) : CStmt → BState → List MemEvent → BState → Prop
  | base {p σ E σ'} : TExecB p σ E σ' → TExec P (.base p) σ E σ'
  | seq {p q σ σ₁ σ₂ E₁ E₂} : TExec P p σ E₁ σ₁ → TExec P q σ₁ E₂ σ₂ → TExec P (.seq p q) σ (E₂ ++ E₁) σ₂
  | iteT {c p q σ E σ'} : c.denote σ.env ≠ 0 → TExec P p σ E σ' → TExec P (.ite c p q) σ E σ'
  | iteF {c p q σ E σ'} : c.denote σ.env = 0 → TExec P q σ E σ' → TExec P (.ite c p q) σ E σ'
  | loopF {c b σ} : c.denote σ.env = 0 → TExec P (.loop c b) σ [] σ
  | loopT {c b σ σ₁ σ₂ E₁ E₂} : c.denote σ.env ≠ 0 → TExec P b σ E₁ σ₁ → TExec P (.loop c b) σ₁ E₂ σ₂ →
      TExec P (.loop c b) σ (E₂ ++ E₁) σ₂
  | call {res f args σ E σ₁} (hf : f < P.length) (ha : args.length = P[f].nparams)
      (hb : TExec P P[f].body ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩ E σ₁) :
      TExec P (.call res f args) σ ([.free (P[f].nlocals + 1)] ++ E ++ [.alloc (P[f].nlocals + 1)])
        ⟨(retEnv σ.env σ₁.env).set res (P[f].ret.denote σ₁.env), σ₁.heap, σ₁.wheap⟩

end Proven.Mach

namespace Proven.Mach
open Proven.Top.Alloc

/-! ## from `CExec` on a zero heap to `TExec` -/

theorem grow_getD (W : List (BitVec 64)) (n j : Nat) : (grow W n).getD j 0 = W.getD j 0 := by
  simp only [grow, List.getD_eq_getElem?_getD]
  by_cases h : j < W.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := W) (by omega), List.getElem?_replicate]
    split <;> rfl

theorem getD_set_eq' (W : List (BitVec 64)) (j k : Nat) (v : BitVec 64) (hj : j < W.length) :
    (W.set j v).getD k 0 = if k = j then v else W.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = k
  · subst h; simp [hj]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- the big run's heap `Wb` (zero beyond the small heap) and the small run's growing heap `Ws` -/
structure Tr (σb σs : BState) (Wb Ws : List (BitVec 64)) : Prop where
  wb : σb.wheap = [Wb]
  ws : σs.wheap = [Ws]
  heap : σs.heap = σb.heap
  env : ∀ x, x ≠ hvar → σs.env x = σb.env x
  len : σs.env hvar = BitVec.ofNat 64 Ws.length
  le : Ws.length ≤ Wb.length
  agree : ∀ j, j < Wb.length → Wb[j]? = some (Ws.getD j 0)

theorem Tr.envU {σb σs : BState} {Wb Ws : List (BitVec 64)} (t : Tr σb σs Wb Ws) :
    ∀ x, x ∉ unread → σs.env x = σb.env x := fun x hx => t.env x (by intro h; subst h; exact hx (by decide))

theorem hvar_unread : hvar ∈ unread := by decide

theorem ne_hvar {v : Nat} (h : v ∉ unread) : v ≠ hvar := by intro e; subst e; exact h hvar_unread

theorem texecB_of_bexec : ∀ {p : BStmt} {σb σb' : BState}, BExec p σb σb' → p.clean = true →
    ∀ {σs : BState} {Wb Ws : List (BitVec 64)}, Tr σb σs Wb Ws →
    ∃ E σs' Wb' Ws', TExecB p σs E σs' ∧ Tr σb' σs' Wb' Ws' ∧ Ws.length ≤ Ws'.length ∧
      ∀ c, inUse (E ++ [.alloc c]) = c + (Ws'.length - Ws.length) ∧
        peak (E ++ [.alloc c]) = c + (Ws'.length - Ws.length) := by
  intro p σb σb' h
  induction h with
  | @assign v e σ =>
    intro hc σs Wb Ws t
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    have hv := not_unread hc.1
    have he : e.denote σs.env = e.denote σ.env := BExp.denote_clean hc.2 t.envU
    refine ⟨[], _, Wb, Ws, .assign, ⟨t.wb, t.ws, t.heap, fun x hx => ?_, ?_, t.le, t.agree⟩, Nat.le_refl _,
      fun c => by simp [inUse, peak]⟩
    · simp only [BEnv.set]; split
      · exact he
      · exact t.env x hx
    · simp only [BEnv.set]; rw [if_neg (Ne.symm (ne_hvar hv))]; exact t.len
  | @load v b i σ hb hi =>
    intro hc σs Wb Ws t
    simp only [BStmt.clean, Bool.and_eq_true, beq_iff_eq] at hc
    have hv := not_unread hc.1.1
    have he : i.denote σs.env = i.denote σ.env := BExp.denote_clean hc.2 t.envU
    have hb' : b < σs.heap.length := by rw [t.heap]; exact hb
    have hi' : (i.denote σs.env).toNat < (σs.heap[b]'hb').length := by simp only [t.heap, he]; exact hi
    have hx : (σs.heap[b]'hb')[(i.denote σs.env).toNat]'hi' = σ.heap[b][(i.denote σ.env).toNat] := by
      simp only [t.heap, he]
    refine ⟨[], _, Wb, Ws, .load hb' hi', ⟨t.wb, t.ws, t.heap, fun x hx' => ?_, ?_, t.le, t.agree⟩, Nat.le_refl _,
      fun c => by simp [inUse, peak]⟩
    · simp only [BEnv.set]; split
      · rw [hx]
      · exact t.env x hx'
    · simp only [BEnv.set]; rw [if_neg (Ne.symm (ne_hvar hv))]; exact t.len
  | @store b i e σ hb hi =>
    intro hc σs Wb Ws t
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    have hi' : i.denote σs.env = i.denote σ.env := BExp.denote_clean hc.1 t.envU
    have he : e.denote σs.env = e.denote σ.env := BExp.denote_clean hc.2 t.envU
    have hb' : b < σs.heap.length := by rw [t.heap]; exact hb
    have hi'' : (i.denote σs.env).toNat < (σs.heap[b]'hb').length := by simp only [t.heap, hi']; exact hi
    refine ⟨[], _, Wb, Ws, .store hb' hi'', ⟨t.wb, t.ws, ?_, t.env, t.len, t.le, t.agree⟩, Nat.le_refl _,
      fun c => by simp [inUse, peak]⟩
    simp only [t.heap, hi', he]
  | @seq p q σ σ₁ σ₂ _ _ ih₁ ih₂ =>
    intro hc σs Wb Ws t
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    obtain ⟨E₁, σs₁, Wb₁, Ws₁, x₁, t₁, l₁, b₁⟩ := ih₁ hc.1 t
    obtain ⟨E₂, σs₂, Wb₂, Ws₂, x₂, t₂, l₂, b₂⟩ := ih₂ hc.2 t₁
    refine ⟨E₂ ++ E₁, σs₂, Wb₂, Ws₂, .seq x₁ x₂, t₂, Nat.le_trans l₁ l₂, fun c => ?_⟩
    rw [inUse_seq, peak_seq, (b₁ c).1, (b₂ _).1, (b₂ _).2, (b₁ c).2]; omega
  | @loopF c b σ hc0 =>
    intro hc σs Wb Ws t
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    refine ⟨[], σs, Wb, Ws, .loopF (by rw [BExp.denote_clean hc.1 t.envU]; exact hc0), t, Nat.le_refl _,
      fun c => by simp [inUse, peak]⟩
  | @loopT c b σ σ₁ σ₂ hc0 _ _ ih₁ ih₂ =>
    intro hc σs Wb Ws t
    have hc' := hc
    simp only [BStmt.clean, Bool.and_eq_true] at hc'
    obtain ⟨E₁, σs₁, Wb₁, Ws₁, x₁, t₁, l₁, b₁⟩ := ih₁ hc'.2 t
    obtain ⟨E₂, σs₂, Wb₂, Ws₂, x₂, t₂, l₂, b₂⟩ := ih₂ hc t₁
    refine ⟨E₂ ++ E₁, σs₂, Wb₂, Ws₂, .loopT (by rw [BExp.denote_clean hc'.1 t.envU]; exact hc0) x₁ x₂, t₂,
      Nat.le_trans l₁ l₂, fun c => ?_⟩
    rw [inUse_seq, peak_seq, (b₁ c).1, (b₂ _).1, (b₂ _).2, (b₁ c).2]; omega
  | @load64 v b i σ hb hi =>
    intro hc σs Wb Ws t
    simp only [BStmt.clean, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨hv0, rfl⟩, hic⟩ := hc
    have hv := not_unread hv0
    have he : i.denote σs.env = i.denote σ.env := BExp.denote_clean hic t.envU
    obtain ⟨envs, Hs, Wss⟩ := σs
    have hws : Wss = [Ws] := t.ws
    subst hws
    have hj : (i.denote σ.env).toNat < Wb.length := by
      have := hi; simp only [t.wb] at this; simpa using this
    have hgl := grow_length Ws ((i.denote envs).toNat + 1)
    refine ⟨_, _, Wb, _, .load64, ⟨t.wb, rfl, t.heap, fun x hx => ?_, ?_, ?_, fun j hj' => ?_⟩, ?_, fun c => ?_⟩
    · simp only [BEnv.set]
      by_cases hxv : x = v
      · rw [if_pos hxv, if_pos hxv]
        have := t.agree _ hj
        simp only [t.wb, List.getElem_singleton]
        rw [grow_getD, he]
        rw [List.getElem?_eq_getElem hj] at this
        exact (Option.some.inj this).symm
      · rw [if_neg hxv, if_neg hxv, if_neg hx]; exact t.env x hx
    · simp only [BEnv.set]; rw [if_neg (Ne.symm (ne_hvar hv))]; simp
    · rw [hgl, he]; have := t.le; omega
    · rw [grow_getD]; exact t.agree j hj'
    · rw [hgl]; omega
    · rw [inUse_growE, peak_growE]; exact ⟨rfl, rfl⟩
  | @store64 b i e σ hb hi =>
    intro hc σs Wb Ws t
    simp only [BStmt.clean, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨rfl, hic⟩, hec⟩ := hc
    have hi' : i.denote σs.env = i.denote σ.env := BExp.denote_clean hic t.envU
    have he : e.denote σs.env = e.denote σ.env := BExp.denote_clean hec t.envU
    obtain ⟨envs, Hs, Wss⟩ := σs
    have hws : Wss = [Ws] := t.ws
    subst hws
    have hj : (i.denote σ.env).toNat < Wb.length := by
      have := hi; simp only [t.wb] at this; simpa using this
    have hgl := grow_length Ws ((i.denote envs).toNat + 1)
    dsimp only at hi' he
    refine ⟨_, _, Wb.set (i.denote σ.env).toNat (e.denote σ.env), _, .store64,
      ⟨by simp only [t.wb, List.getElem_singleton, List.set_cons_zero], rfl, t.heap, fun x hx => ?_, ?_, ?_,
        fun j hj' => ?_⟩, ?_, fun c => ?_⟩
    · simp only [BEnv.set]; rw [if_neg hx]; exact t.env x hx
    · simp only [BEnv.set]; rw [List.length_set]; simp
    · rw [List.length_set, List.length_set, hgl, hi']; have := t.le; omega
    · rw [List.length_set] at hj'
      rw [getD_set_eq' _ _ _ _ (by rw [hgl]; omega), List.getElem?_set, hi', he]
      by_cases h : (i.denote σ.env).toNat = j
      · rw [if_pos h, if_pos h.symm, if_pos hj]
      · rw [if_neg h, if_neg (Ne.symm h), grow_getD]; exact t.agree j hj'
    · rw [List.length_set, hgl]; omega
    · rw [List.length_set, inUse_growE, peak_growE]; exact ⟨rfl, rfl⟩
  | mop =>
    intro hc; simp [BStmt.clean] at hc

end Proven.Mach

namespace Proven.Mach
open Proven.Top.Alloc

theorem fn_clean {P : Prog} (hP : progClean P = true) {f : Nat} (hf : f < P.length) :
    P[f].body.clean = true ∧ P[f].ret.clean = true := by
  have := List.all_eq_true.1 hP P[f] (List.getElem_mem hf)
  simpa [Fn.clean] using this

/-- **`CExec` on a zero heap is a `TExec` run**: same result, the heap a prefix, at most the stack need more
cells in use than at the end. -/
theorem texec_of_cexec {P : Prog} (hP : progClean P = true) :
    ∀ {k : Nat} {p : CStmt} {σb σb' : BState}, CExec P k p σb σb' → p.clean = true →
    ∀ {σs : BState} {Wb Ws : List (BitVec 64)}, Tr σb σs Wb Ws →
    ∃ E σs' Wb' Ws', TExec P p σs E σs' ∧ Tr σb' σs' Wb' Ws' ∧ Ws.length ≤ Ws'.length ∧
      ∀ c, inUse (E ++ [.alloc c]) = c + (Ws'.length - Ws.length) ∧
        peak (E ++ [.alloc c]) ≤ c + (Ws'.length - Ws.length) + k / 8 := by
  intro k p σb σb' h
  induction h with
  | base hx =>
    intro hc σs Wb Ws t
    obtain ⟨E, σs', Wb', Ws', x, t', l, b⟩ := texecB_of_bexec hx hc t
    exact ⟨E, σs', Wb', Ws', .base x, t', l, fun c => ⟨(b c).1, by rw [(b c).2]; omega⟩⟩
  | @seq k p q σ σ₁ σ₂ _ _ ih₁ ih₂ =>
    intro hc σs Wb Ws t
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    obtain ⟨E₁, σs₁, Wb₁, Ws₁, x₁, t₁, l₁, b₁⟩ := ih₁ hc.1 t
    obtain ⟨E₂, σs₂, Wb₂, Ws₂, x₂, t₂, l₂, b₂⟩ := ih₂ hc.2 t₁
    refine ⟨E₂ ++ E₁, σs₂, Wb₂, Ws₂, .seq x₁ x₂, t₂, Nat.le_trans l₁ l₂, fun c => ?_⟩
    rw [inUse_seq, peak_seq, (b₁ c).1, (b₂ _).1]
    have := (b₂ (c + (Ws₁.length - Ws.length))).2; have := (b₁ c).2
    constructor
    · omega
    · omega
  | @iteT k c p q σ σ' hc0 _ ih =>
    intro hc σs Wb Ws t
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    obtain ⟨E, σs', Wb', Ws', x, t', l, b⟩ := ih hc.1.2 t
    exact ⟨E, σs', Wb', Ws', .iteT (by rw [BExp.denote_clean hc.1.1 t.envU]; exact hc0) x, t', l, b⟩
  | @iteF k c p q σ σ' hc0 _ ih =>
    intro hc σs Wb Ws t
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    obtain ⟨E, σs', Wb', Ws', x, t', l, b⟩ := ih hc.2 t
    exact ⟨E, σs', Wb', Ws', .iteF (by rw [BExp.denote_clean hc.1.1 t.envU]; exact hc0) x, t', l, b⟩
  | @loopF k c b σ hc0 =>
    intro hc σs Wb Ws t
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    exact ⟨[], σs, Wb, Ws, .loopF (by rw [BExp.denote_clean hc.1 t.envU]; exact hc0), t, Nat.le_refl _,
      fun c => by simp [inUse, peak]⟩
  | @loopT k c b σ σ₁ σ₂ hc0 _ _ ih₁ ih₂ =>
    intro hc σs Wb Ws t
    have hc' := hc
    simp only [CStmt.clean, Bool.and_eq_true] at hc'
    obtain ⟨E₁, σs₁, Wb₁, Ws₁, x₁, t₁, l₁, b₁⟩ := ih₁ hc'.2 t
    obtain ⟨E₂, σs₂, Wb₂, Ws₂, x₂, t₂, l₂, b₂⟩ := ih₂ hc t₁
    refine ⟨E₂ ++ E₁, σs₂, Wb₂, Ws₂, .loopT (by rw [BExp.denote_clean hc'.1 t.envU]; exact hc0) x₁ x₂, t₂,
      Nat.le_trans l₁ l₂, fun c => ?_⟩
    rw [inUse_seq, peak_seq, (b₁ c).1, (b₂ _).1]
    have := (b₂ (c + (Ws₁.length - Ws.length))).2; have := (b₁ c).2
    constructor
    · omega
    · omega
  | @call k k' res f args σ σ₁ hf ha hk _ ih =>
    intro hc σs Wb Ws t
    simp only [CStmt.clean, Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨hres, hargs⟩ := hc
    have hres' := not_unread hres
    obtain ⟨hbody, hret⟩ := fn_clean hP hf
    have hav : args.map (·.denote σs.env) = args.map (·.denote σ.env) :=
      List.map_congr_left fun e he => BExp.denote_clean (hargs e he) t.envU
    have t₀ : Tr ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩
        ⟨callEnv σs.env (args.map (·.denote σs.env)), σs.heap, σs.wheap⟩ Wb Ws :=
      ⟨t.wb, t.ws, t.heap, fun x hx => by
          simp only [callEnv, hav]; split
          · exact t.env x hx
          · rfl,
        by simp only [callEnv, show hvar < 8 by decide, if_true]; exact t.len, t.le, t.agree⟩
    obtain ⟨E, σs₁, Wb₁, Ws₁, x, t₁, l, b⟩ := ih hbody t₀
    refine ⟨_, _, Wb₁, Ws₁, .call hf ha x, ⟨t₁.wb, t₁.ws, t₁.heap, fun y hy => ?_, ?_, t₁.le, t₁.agree⟩, l,
      fun c => ?_⟩
    · simp only [BEnv.set, retEnv]
      have hr : P[f].ret.denote σs₁.env = P[f].ret.denote σ₁.env := BExp.denote_clean hret t₁.envU
      split
      · exact hr
      · split
        · exact t₁.env y hy
        · exact t.env y hy
    · simp only [BEnv.set, retEnv, show hvar < 8 by decide, if_true]
      rw [if_neg (Ne.symm (ne_hvar hres'))]; exact t₁.len
    · have hk8 : P[f].nlocals + 1 + k' / 8 ≤ k / 8 := by
        have : P[f].frame = 8 * (P[f].nlocals + 1) := rfl
        omega
      rw [inUse_call, peak_call, (b _).1]
      have := (b (c + (P[f].nlocals + 1))).2
      constructor
      · omega
      · omega

end Proven.Mach

namespace Proven.Mach
open Proven.Top.Alloc

/-! ## the events do not depend on unread data -/

/-- two states that differ only in what a clean program does not read -/
structure Eqv (σ₁ σ₂ : BState) : Prop where
  env : ∀ x, x ∉ unread → σ₁.env x = σ₂.env x
  hv : σ₁.env hvar = σ₂.env hvar
  heap0 : σ₁.heap[0]? = σ₂.heap[0]?
  wheap : σ₁.wheap = σ₂.wheap

theorem Eqv.set {σ₁ σ₂ : BState} (q : Eqv σ₁ σ₂) {v : Nat} (hv : v ∉ unread) {x₁ x₂ : BitVec 64} (hx : x₁ = x₂)
    {H₁ H₂ : Heap} (hH : H₁[0]? = H₂[0]?) {W₁ W₂ : WHeap} (hW : W₁ = W₂) :
    Eqv ⟨σ₁.env.set v x₁, H₁, W₁⟩ ⟨σ₂.env.set v x₂, H₂, W₂⟩ :=
  ⟨fun y hy => by simp only [BEnv.set]; split
                  · exact hx
                  · exact q.env y hy,
    by simp only [BEnv.set]; rw [if_neg (Ne.symm (ne_hvar hv)), if_neg (Ne.symm (ne_hvar hv))]; exact q.hv,
    hH, hW⟩

theorem heap0_set {H₁ H₂ : Heap} (h : H₁[0]? = H₂[0]?) {b₁ b₂ : Nat} (hb : b₁ = b₂) (hb₁ : b₁ < H₁.length)
    (hb₂ : b₂ < H₂.length) {j : Nat} {v : BitVec 8} :
    (H₁.set b₁ (H₁[b₁].set j v))[0]? = (H₂.set b₂ (H₂[b₂].set j v))[0]? := by
  subst hb
  simp only [List.getElem?_set]
  split
  · next h0 =>
    subst h0
    rw [List.getElem?_eq_getElem hb₁, List.getElem?_eq_getElem hb₂] at h
    simp only [Option.some.inj h]
  · exact h

theorem texecB_det : ∀ {p : BStmt} {σ₁ σ₁' : BState} {E₁ : List MemEvent}, TExecB p σ₁ E₁ σ₁' → p.clean = true →
    ∀ {σ₂ σ₂' : BState} {E₂ : List MemEvent}, TExecB p σ₂ E₂ σ₂' → Eqv σ₁ σ₂ → E₁ = E₂ ∧ Eqv σ₁' σ₂' := by
  intro p σ₁ σ₁' E₁ h
  induction h with
  | @assign v e σ =>
    intro hc σ₂ σ₂' E₂ h2 q
    cases h2
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    exact ⟨rfl, q.set (not_unread hc.1) (BExp.denote_clean hc.2 q.env) q.heap0 q.wheap⟩
  | @load v b i σ hb hi =>
    intro hc σ₂ σ₂' E₂ h2 q
    cases h2 with
    | load hb₂ hi₂ =>
      simp only [BStmt.clean, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hv, rfl⟩, hic⟩ := hc
      have he := BExp.denote_clean hic q.env
      refine ⟨rfl, q.set (not_unread hv) ?_ q.heap0 q.wheap⟩
      have h0 := q.heap0
      rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hb₂] at h0
      simp only [Option.some.injEq] at h0
      simp only [h0, he]
  | @store b i e σ hb hi =>
    intro hc σ₂ σ₂' E₂ h2 q
    cases h2 with
    | store hb₂ hi₂ =>
      simp only [BStmt.clean, Bool.and_eq_true] at hc
      have hi' := BExp.denote_clean hc.1 q.env
      have he := BExp.denote_clean hc.2 q.env
      refine ⟨rfl, ⟨q.env, q.hv, ?_, q.wheap⟩⟩
      dsimp only
      rw [hi', he]; exact heap0_set q.heap0 rfl hb hb₂
  | @seq p₁ p₂ σ σ₁ σ₂ E₁ E₂ _ _ ih₁ ih₂ =>
    intro hc τ τ' F h2 q
    cases h2 with
    | seq x₁ x₂ =>
      simp only [BStmt.clean, Bool.and_eq_true] at hc
      obtain ⟨e₁, q₁⟩ := ih₁ hc.1 x₁ q
      obtain ⟨e₂, q₂⟩ := ih₂ hc.2 x₂ q₁
      exact ⟨by rw [e₁, e₂], q₂⟩
  | @loopF c b σ hc0 =>
    intro hc σ₂ σ₂' E₂ h2 q
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    cases h2 with
    | loopF _ => exact ⟨rfl, q⟩
    | loopT hc1 _ _ => exact absurd (by rw [← BExp.denote_clean hc.1 q.env]; exact hc0) hc1
  | @loopT c b σ σ₁ σ₂ E₁ E₂ hc0 _ _ ih₁ ih₂ =>
    intro hc τ τ' F h2 q
    have hc' := hc
    simp only [BStmt.clean, Bool.and_eq_true] at hc'
    cases h2 with
    | loopF hc1 => exact absurd (by rw [BExp.denote_clean hc'.1 q.env]; exact hc1) hc0
    | loopT _ x₁ x₂ =>
      obtain ⟨e₁, q₁⟩ := ih₁ hc'.2 x₁ q
      obtain ⟨e₂, q₂⟩ := ih₂ hc x₂ q₁
      exact ⟨by rw [e₁, e₂], q₂⟩
  | @load64 v i env H W =>
    intro hc σ₂ σ₂' E₂ h2 q
    cases h2 with
    | load64 =>
      simp only [BStmt.clean, Bool.and_eq_true, beq_iff_eq] at hc
      have he := BExp.denote_clean hc.2 q.env
      have hw : W = _ := List.head_eq_of_cons_eq q.wheap
      dsimp only at he hw
      subst hw
      rw [he]
      refine ⟨rfl, ⟨fun y hy => ?_, ?_, q.heap0, rfl⟩⟩
      · simp only [BEnv.set]; split
        · rfl
        · rw [if_neg (by intro e; subst e; exact hy hvar_unread), if_neg (by intro e; subst e; exact hy hvar_unread)]
          exact q.env y hy
      · simp only [BEnv.set]; rw [if_neg (Ne.symm (ne_hvar (not_unread hc.1.1))), if_neg (Ne.symm (ne_hvar (not_unread hc.1.1)))]
        simp
  | @store64 i e env H W =>
    intro hc σ₂ σ₂' E₂ h2 q
    cases h2 with
    | store64 =>
      simp only [BStmt.clean, Bool.and_eq_true, beq_iff_eq] at hc
      have hi := BExp.denote_clean hc.1.2 q.env
      have he := BExp.denote_clean hc.2 q.env
      have hw : W = _ := List.head_eq_of_cons_eq q.wheap
      dsimp only at hi he hw
      subst hw
      rw [hi, he]
      refine ⟨rfl, ⟨fun y hy => ?_, by simp [BEnv.set], q.heap0, rfl⟩⟩
      simp only [BEnv.set]
      rw [if_neg (by intro e; subst e; exact hy hvar_unread), if_neg (by intro e; subst e; exact hy hvar_unread)]
      exact q.env y hy

theorem texec_det {P : Prog} (hP : progClean P = true) :
    ∀ {p : CStmt} {σ₁ σ₁' : BState} {E₁ : List MemEvent}, TExec P p σ₁ E₁ σ₁' → p.clean = true →
    ∀ {σ₂ σ₂' : BState} {E₂ : List MemEvent}, TExec P p σ₂ E₂ σ₂' → Eqv σ₁ σ₂ → E₁ = E₂ ∧ Eqv σ₁' σ₂' := by
  intro p σ₁ σ₁' E₁ h
  induction h with
  | base x =>
    intro hc σ₂ σ₂' E₂ h2 q
    cases h2 with
    | base x₂ => exact texecB_det x hc x₂ q
  | @seq p₁ p₂ σ σ₁ σ₂ E₁ E₂ _ _ ih₁ ih₂ =>
    intro hc τ τ' F h2 q
    cases h2 with
    | seq x₁ x₂ =>
      simp only [CStmt.clean, Bool.and_eq_true] at hc
      obtain ⟨e₁, q₁⟩ := ih₁ hc.1 x₁ q
      obtain ⟨e₂, q₂⟩ := ih₂ hc.2 x₂ q₁
      exact ⟨by rw [e₁, e₂], q₂⟩
  | @iteT c p₁ p₂ σ E σ' hc0 _ ih =>
    intro hc τ τ' F h2 q
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    cases h2 with
    | iteT _ x => exact ih hc.1.2 x q
    | iteF hc1 _ => exact absurd (by rw [BExp.denote_clean hc.1.1 q.env]; exact hc1) hc0
  | @iteF c p₁ p₂ σ E σ' hc0 _ ih =>
    intro hc τ τ' F h2 q
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    cases h2 with
    | iteT hc1 _ => exact absurd (by rw [← BExp.denote_clean hc.1.1 q.env]; exact hc0) hc1
    | iteF _ x => exact ih hc.2 x q
  | @loopF c b σ hc0 =>
    intro hc σ₂ σ₂' E₂ h2 q
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    cases h2 with
    | loopF _ => exact ⟨rfl, q⟩
    | loopT hc1 _ _ => exact absurd (by rw [← BExp.denote_clean hc.1 q.env]; exact hc0) hc1
  | @loopT c b σ σ₁ σ₂ E₁ E₂ hc0 _ _ ih₁ ih₂ =>
    intro hc τ τ' F h2 q
    have hc' := hc
    simp only [CStmt.clean, Bool.and_eq_true] at hc'
    cases h2 with
    | loopF hc1 => exact absurd (by rw [BExp.denote_clean hc'.1 q.env]; exact hc1) hc0
    | loopT _ x₁ x₂ =>
      obtain ⟨e₁, q₁⟩ := ih₁ hc'.2 x₁ q
      obtain ⟨e₂, q₂⟩ := ih₂ hc x₂ q₁
      exact ⟨by rw [e₁, e₂], q₂⟩
  | @call res f args σ E σ₁ hf ha _ ih =>
    intro hc τ τ' F h2 q
    simp only [CStmt.clean, Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨hbody, hret⟩ := fn_clean hP hf
    cases h2 with
    | call _ _ x =>
      have hav : args.map (·.denote σ.env) = args.map (·.denote τ.env) :=
        List.map_congr_left fun e he => BExp.denote_clean (hc.2 e he) q.env
      have q₀ : Eqv ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩
          ⟨callEnv τ.env (args.map (·.denote τ.env)), τ.heap, τ.wheap⟩ :=
        ⟨fun y hy => by simp only [callEnv, hav]; split
                        · exact q.env y hy
                        · rfl,
          by simp only [callEnv, show hvar < 8 by decide, if_true]; exact q.hv, q.heap0, q.wheap⟩
      obtain ⟨e, q₁⟩ := ih hbody x q₀
      refine ⟨by rw [e], ⟨fun y hy => ?_, ?_, q₁.heap0, q₁.wheap⟩⟩
      · simp only [BEnv.set, retEnv]
        split
        · exact BExp.denote_clean hret q₁.env
        · split
          · exact q₁.env y hy
          · exact q.env y hy
      · simp only [BEnv.set, retEnv, show hvar < 8 by decide, if_true]
        rw [if_neg (Ne.symm (ne_hvar (not_unread hc.1))), if_neg (Ne.symm (ne_hvar (not_unread hc.1)))]
        exact q₁.hv

end Proven.Mach
