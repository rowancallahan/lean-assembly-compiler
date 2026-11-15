/- Fast loops for the compiled tree (`Tree.lean`), and the function's program `prog` with `prog_ok`.

The plain program runs one tree step per iteration of `while fl { comp t }`; every conditional of the step is
two at-most-once loops and every test a 0/1 value.  Before the plain step, each iteration now runs
**fast loops**, one per path of `ite`s from the root of the tree to a subtree `S`:
* `S` has only `call` leaves: `while Gv { S }` (the path's conditions `Gv` as the loop test);
* `S` is `X; if c then A else B` with `X` straight-line code (loads, lets) and one of `A`, `B` all `call`s:
  `k := 1; while Gv ∧ k { X; k := c'; if k { the call branch } }; if Gv ∧ ¬c' { the other branch }`.
Conditions whose variables the loop never writes are tested once, outside (`Gi`); a call argument that is a
constant the variable already has (checked in `Gi`) is not assigned.  Each fast iteration is one step of the
tree, so the result is unchanged (`fast_ok`); the plain step afterwards handles everything else.

`prog L t out` and `prog_ok` (and `prog_ok_ro`, `prog_okQ`) keep the statements they had. -/
import Riscv.Frontx.Tree

namespace Proven.Frontx
open Proven

deriving instance DecidableEq for Proven.BExp

/-! ## Syntactic facts about trees -/

/-- the variables one step may write -/
def Tree.wv : Tree → List Nat
  | .ret _ => []
  | .call as => as.map (·.1)
  | .ite _ a b => a.wv ++ b.wv
  | .let_ v _ k | .load v _ _ k | .cload v _ _ _ _ k => v :: k.wv
  | .store _ _ _ k => k.wv
  | .sub _ k => k.wv

/-- every leaf is a `call`, no sub-programs -/
def Tree.calls : Tree → Bool
  | .ret _ => false
  | .call _ => true
  | .ite _ a b => a.calls && b.calls
  | .let_ _ _ k | .load _ _ _ k | .cload _ _ _ _ _ k | .store _ _ _ k => k.calls
  | .sub _ _ => false

/-- the targets of `let`/`load`/`cload` -/
def Tree.lets : Tree → List Nat
  | .ite _ a b => a.lets ++ b.lets
  | .let_ v _ k | .load v _ _ k | .cload v _ _ _ _ k => v :: k.lets
  | .store _ _ _ k => k.lets
  | _ => []

/-- the pairs of all `call` leaves -/
def Tree.pairs : Tree → List (Nat × BExp)
  | .call as => as
  | .ite _ a b => a.pairs ++ b.pairs
  | .let_ _ _ k | .load _ _ _ k | .cload _ _ _ _ _ k | .store _ _ _ k | .sub _ k => k.pairs
  | .ret _ => []

/-- `(v, c)` for the constant pairs `v := c` -/
def cpairs : List (Nat × BExp) → List (Nat × BitVec 64)
  | [] => []
  | (v, .const c) :: as => (v, c) :: cpairs as
  | _ :: as => cpairs as

/-- the pair assigns `v` the constant `c` -/
def isK (v : Nat) (c : BitVec 64) : Nat × BExp → Bool
  | (w, .const d) => decide (w = v) && decide (d = c)
  | _ => false

/-- `v` gets only the constant `c` in `S`, and is no `let` target -/
def kOK (S : Tree) (p : Nat × BitVec 64) : Bool :=
  S.pairs.all (fun q => !decide (q.1 = p.1) || isK p.1 p.2 q) && !S.lets.contains p.1

/-- the `call` pairs with targets in `K` removed -/
def Tree.strip (K : List Nat) : Tree → Tree
  | .call as => .call (as.filter fun p => !K.contains p.1)
  | .ite c a b => .ite c (a.strip K) (b.strip K)
  | .let_ v e k => .let_ v e (k.strip K)
  | .load v b i k => .load v b i (k.strip K)
  | .cload v b i c d k => .cload v b i c d (k.strip K)
  | .store b i e k => .store b i e (k.strip K)
  | t => t

/-- the target lists of the `call` leaves -/
def Tree.leaves : Tree → List (List (Nat × BExp))
  | .call as => [as]
  | .ite _ a b => a.leaves ++ b.leaves
  | .let_ _ _ k | .load _ _ _ k | .cload _ _ _ _ _ k | .store _ _ _ k | .sub _ k => k.leaves
  | .ret _ => []

/-- the pairs of every `call` leaf that can be assigned after the step instead (`hoist`) -/
def common (S : Tree) : List (Nat × BExp) :=
  match S.leaves with
  | [] => []
  | as :: ls =>
    let H := as.filter fun p => ls.all fun l => l.contains p
    let S'' := S.strip (H.map (·.1))
    if (S.leaves.all fun l => (l.map (·.1)).Nodup) &&
      H.all (fun p => !S''.wv.contains p.1 && p.2.vs.all fun x => !S''.wv.contains x) then H else []

/-! ## Fast loops -/

def eqz (c : BExp) : BExp := .bin .eq c (.const 0)

/-- a path condition: `c ≠ 0` or `c = 0` -/
def condE : BExp × Bool → BExp
  | (c, true) => c
  | (c, false) => eqz c

/-- short-circuit conjunction -/
def conj : List BExp → BExp
  | [] => .const 1
  | [c] => c
  | c :: cs => .ite c (conj cs) (.const 0)

/-- the paths of `ite`s from the root: their conditions and the subtree reached (not an `ite`) -/
def peel : Tree → List (List (BExp × Bool) × Tree)
  | .ite c a b => ((peel a).map fun r => ((c, true) :: r.1, r.2)) ++ ((peel b).map fun r => ((c, false) :: r.1, r.2))
  | t => [([], t)]

/-- straight-line nodes before a conditional -/
inductive Pre where
  | let_ (v : Nat) (e : BExp)
  | load (v b : Nat) (i : BExp)
  | cload (v b : Nat) (i c d : BExp)

def Pre.app : List Pre → Tree → Tree
  | [], k => k
  | .let_ v e :: xs, k => .let_ v e (Pre.app xs k)
  | .load v b i :: xs, k => .load v b i (Pre.app xs k)
  | .cload v b i c d :: xs, k => .cload v b i c d (Pre.app xs k)

def Pre.tgt : Pre → Nat
  | .let_ v _ | .load v _ _ | .cload v _ _ _ _ => v

/-- `S` as `X; if c then A else B` -/
def splitPre : Tree → Option (List Pre × BExp × Tree × Tree)
  | .ite c a b => some ([], c, a, b)
  | .let_ v e k => (splitPre k).map fun r => (.let_ v e :: r.1, r.2)
  | .load v b i k => (splitPre k).map fun r => (.load v b i :: r.1, r.2)
  | .cload v b i c d k => (splitPre k).map fun r => (.cload v b i c d :: r.1, r.2)
  | _ => none

/-- `while g { c; g := 0 }` after `g := e`: run `c` if `e ≠ 0` (`g` a control variable) -/
def whenS (g : Nat) (e : BExp) (c : BStmt) : BStmt :=
  .seq (.assign g e) (.loop (.var g) (.seq c (.assign g (.const 0))))

/-- the invariant conditions (`Gi`, with the constant checks) and the others (`Gv`) -/
def splitG (W : List Nat) (K : List (Nat × BitVec 64)) (cs : List (BExp × Bool)) : List BExp × List BExp :=
  (K.map (fun p => .bin .eq (.var p.1) (.const p.2)) ++
      (cs.filter fun c => (condE c).vs.all fun x => !W.contains x).map condE,
    (cs.filter fun c => !(condE c).vs.all fun x => !W.contains x).map condE)

/-- the constants of the loop's calls that need no assignment -/
def kOf (S : Tree) (W : List Nat) : List (Nat × BitVec 64) :=
  ((cpairs S.pairs).eraseDups).filter fun p => kOK S p && !W.contains p.1

/-- a fast loop for one path (`none` if the path does not qualify) -/
def fastOf (L : Lay) (cs : List (BExp × Bool)) (S : Tree) : Option BStmt :=
  if S.calls then
    let K := kOf S []
    let S' := S.strip (K.map (·.1))
    let H := common S'
    let S'' := S'.strip (H.map (·.1))
    let G := splitG S'.wv K cs
    if G.2.isEmpty then none else
    let lp := BStmt.loop (conj G.2) (if H.isEmpty then comp L S' 1 else .seq (comp L S'' 1) (comp L (.call H) 1))
    some (whenS (L.cv 0) (conj (.var L.fl :: G.1)) lp)
  else match splitPre S with
  | some (xs@(_ :: _), c, a, b) =>
    let r := if a.calls then some (a, b, c) else if b.calls then some (b, a, eqz c) else none
    match r with
    | none => none
    | some (S2, R, c') =>
      let W0 := xs.map Pre.tgt
      let K := kOf S2 W0
      let S2' := S2.strip (K.map (·.1))
      let G := splitG (W0 ++ S2'.wv) K cs
      if G.2.isEmpty || !(conj G.2).vs.all (fun x => !W0.contains x) then none else
      let k := L.cv 0 + 1
      let w := L.cv 1
      let body := BStmt.seq (comp L (Pre.app xs (.call [])) 1)
        (.seq (.assign k c') (whenS w (.var k) (comp L S2' 2)))
      let fl := BStmt.seq (.seq (.assign k (.const 1)) (.loop (.ite (conj G.2) (.var k) (.const 0)) body))
        (whenS w (.ite (conj G.2) (eqz c') (.const 0)) (comp L R 2))
      some (whenS (L.cv 0) (conj (.var L.fl :: G.1)) fl)
  | _ => none

/-- expression depths the back ends accept -/
def _root_.Proven.BStmt.dOK : BStmt → Bool
  | .assign _ e => decide (e.depth < 6)
  | .load _ _ i => decide (i.depth < 5)
  | .store _ i e => decide (i.depth < 5) && decide (e.depth < 5)
  | .seq p q => p.dOK && q.dOK
  | .loop c b => decide (c.depth < 6) && b.dOK

def seqs : List BStmt → BStmt
  | [] => .loop (.const 0) (.loop (.const 0) (.assign 1 (.var 1)))
  | [p] => p
  | p :: ps => .seq p (seqs ps)

/-- the fast loops of a tree -/
def fasts (L : Lay) (t : Tree) : List BStmt :=
  ((peel t).filterMap fun r => fastOf L r.1 r.2).filter Proven.BStmt.dOK

/-- one iteration: the fast loops, then (if the function has not returned) one plain step -/
def iter (L : Lay) (t : Tree) : BStmt :=
  match fasts L t with
  | [] => comp L t 0
  | fs =>
    -- the old back end bounds the code of a loop body (`BStmt.wf`)
    if (compileB [0, 3] (.seq (seqs fs) (whenS (L.cv 0) (.var L.fl) (comp L t 0)))).length < 1000 then
      .seq (seqs fs) (whenS (L.cv 0) (.var L.fl) (comp L t 0))
    else comp L t 0

/-! ## Facts about the pieces -/

/-- `Runs` with the number of `call` steps -/
inductive Tree.RunsN (t : Tree) : Nat → BState → BitVec 64 → BState → Prop
  | ret {σ r σ'} : t.step σ = some (.ret r σ') → RunsN t 0 σ r σ'
  | call {n σ σ₁ r σ'} : t.step σ = some (.call σ₁) → RunsN t n σ₁ r σ' → RunsN t (n + 1) σ r σ'

theorem Tree.Runs.toN {t : Tree} {σ σ' : BState} {r : BitVec 64} (h : t.Runs σ r σ') : ∃ n, t.RunsN n σ r σ' := by
  induction h with
  | ret hs => exact ⟨0, .ret hs⟩
  | call hs _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .call hs h⟩

theorem conj_ne (env : BEnv) : ∀ cs : List BExp, (conj cs).denote env ≠ 0 ↔ ∀ c ∈ cs, c.denote env ≠ 0
  | [] => by simp [conj, BExp.denote]
  | [c] => by simp [conj]
  | c :: c' :: cs => by
    have ih := conj_ne env (c' :: cs)
    show (if c.denote env = 0 then (BExp.const 0).denote env else (conj (c' :: cs)).denote env) ≠ 0 ↔ _
    rw [List.forall_mem_cons, ← ih]
    by_cases h : c.denote env = 0
    · rw [if_pos h]; exact ⟨fun h' => absurd rfl h', fun h' => absurd h h'.1⟩
    · rw [if_neg h]; exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩

theorem condE_ne (env : BEnv) : ∀ p : BExp × Bool, (condE p).denote env ≠ 0 ↔ ((p.1.denote env ≠ 0) ↔ p.2 = true)
  | (c, true) => by simp [condE]
  | (c, false) => by
    simp only [condE, eqz, BExp.denote, Op.eval]
    by_cases h : c.denote env = 0 <;> simp [h]

theorem condE_vlt {m : Nat} {p : BExp × Bool} (h : p.1.vlt m) : (condE p).vlt m := by
  obtain ⟨c, b⟩ := p
  cases b
  · exact ⟨h, trivial⟩
  · exact h

theorem conj_vlt {m : Nat} : ∀ {cs : List BExp}, (∀ c ∈ cs, c.vlt m) → (conj cs).vlt m
  | [], _ => trivial
  | [c], h => h c (List.mem_singleton_self _)
  | c :: c' :: cs, h => ⟨h c List.mem_cons_self, conj_vlt fun x hx => h x (List.mem_cons_of_mem _ hx), trivial⟩

/-- the subtree at the end of a path is the step when the path's conditions hold -/
theorem peel_step : ∀ (t : Tree) {cs : List (BExp × Bool)} {S : Tree}, (cs, S) ∈ peel t → ∀ σ : BState,
    (∀ p ∈ cs, (condE p).denote σ.env ≠ 0) → t.step σ = S.step σ
  | .ite c a b, cs, S, hm, σ, hc => by
    simp only [peel, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨⟨cs', S'⟩, hm, e⟩ | ⟨⟨cs', S'⟩, hm, e⟩ <;> simp only [Prod.mk.injEq] at e <;>
      obtain ⟨rfl, rfl⟩ := e
    · have h := (condE_ne σ.env _).1 (hc _ List.mem_cons_self)
      simp only [iff_true] at h
      simp only [Tree.step, if_neg h]
      exact peel_step a hm σ fun p hp => hc p (List.mem_cons_of_mem _ hp)
    · have h : c.denote σ.env = 0 := by simpa using (condE_ne σ.env _).1 (hc _ List.mem_cons_self)
      simp only [Tree.step, if_pos h]
      exact peel_step b hm σ fun p hp => hc p (List.mem_cons_of_mem _ hp)
  | .ret _, _, _, hm, _, _ | .call _, _, _, hm, _, _ | .let_ _ _ _, _, _, hm, _, _ | .load _ _ _ _, _, _, hm, _, _
  | .cload _ _ _ _ _ _, _, _, hm, _, _ | .store _ _ _ _, _, _, hm, _, _ | .sub _ _, _, _, hm, _, _ => by
    simp only [peel, List.mem_singleton, Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm; rfl

theorem peel_wf (L : Lay) : ∀ (t : Tree) {cs : List (BExp × Bool)} {S : Tree}, (cs, S) ∈ peel t → t.wf L →
    S.wf L ∧ ∀ p ∈ cs, p.1.vlt L.M
  | .ite c a b, cs, S, hm, hw => by
    simp only [peel, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨⟨cs', S'⟩, hm, e⟩ | ⟨⟨cs', S'⟩, hm, e⟩ <;> simp only [Prod.mk.injEq] at e <;>
      obtain ⟨rfl, rfl⟩ := e
    · obtain ⟨h1, h2⟩ := peel_wf L a hm hw.2.1
      exact ⟨h1, fun p hp => (List.mem_cons.1 hp).elim (fun e => e ▸ hw.1) (h2 p)⟩
    · obtain ⟨h1, h2⟩ := peel_wf L b hm hw.2.2
      exact ⟨h1, fun p hp => (List.mem_cons.1 hp).elim (fun e => e ▸ hw.1) (h2 p)⟩
  | .ret _, _, _, hm, hw | .call _, _, _, hm, hw | .let_ _ _ _, _, _, hm, hw | .load _ _ _ _, _, _, hm, hw
  | .cload _ _ _ _ _ _, _, _, hm, hw | .store _ _ _ _, _, _, hm, hw | .sub _ _, _, _, hm, hw => by
    simp only [peel, List.mem_singleton, Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm
    exact ⟨hw, fun _ h => nomatch h⟩

/-- a tree whose leaves are `call`s steps to a `call`, changing only the variables it writes -/
theorem calls_step : ∀ (S : Tree), S.calls = true → ∀ (σ : BState) (o : Out), S.step σ = some o →
    ∃ σ₁, o = .call σ₁ ∧ ∀ x, x ∉ S.wv → σ₁.env x = σ.env x
  | .call as, _, σ, o, hs => by
    simp only [Tree.step, Option.some.injEq] at hs; subst hs
    exact ⟨_, rfl, fun x hx => parSet_out _ _ as _ fun p hp e => hx (by
      simp only [Tree.wv, List.mem_map]; exact ⟨p, hp, e⟩)⟩
  | .ite c a b, hc, σ, o, hs => by
    simp only [Tree.calls, Bool.and_eq_true] at hc
    simp only [Tree.step] at hs
    split at hs
    · obtain ⟨σ₁, e, h⟩ := calls_step b hc.2 σ o hs
      exact ⟨σ₁, e, fun x hx => h x fun h' => hx (by simp [Tree.wv, h'])⟩
    · obtain ⟨σ₁, e, h⟩ := calls_step a hc.1 σ o hs
      exact ⟨σ₁, e, fun x hx => h x fun h' => hx (by simp [Tree.wv, h'])⟩
  | .let_ v e k, hc, σ, o, hs => by
    obtain ⟨σ₁, e', h⟩ := calls_step k hc _ o hs
    refine ⟨σ₁, e', fun x hx => ?_⟩
    simp only [Tree.wv, List.mem_cons, not_or] at hx
    rw [h x hx.2]; exact set_ne _ _ hx.1
  | .load v b i k, hc, σ, o, hs => by
    simp only [Tree.step] at hs
    cases hr : rd σ.heap b (i.denote σ.env).toNat with
    | none => rw [hr] at hs; cases hs
    | some y =>
      rw [hr] at hs
      obtain ⟨σ₁, e', h⟩ := calls_step k hc _ o hs
      refine ⟨σ₁, e', fun x hx => ?_⟩
      simp only [Tree.wv, List.mem_cons, not_or] at hx
      rw [h x hx.2]; exact set_ne _ _ hx.1
  | .cload v b i c d k, hc, σ, o, hs => by
    simp only [Tree.step] at hs
    split at hs
    · obtain ⟨σ₁, e', h⟩ := calls_step k hc _ o hs
      refine ⟨σ₁, e', fun x hx => ?_⟩
      simp only [Tree.wv, List.mem_cons, not_or] at hx
      rw [h x hx.2]; exact set_ne _ _ hx.1
    · cases hr : rd σ.heap b (i.denote σ.env).toNat with
      | none => rw [hr] at hs; cases hs
      | some y =>
        rw [hr] at hs
        obtain ⟨σ₁, e', h⟩ := calls_step k hc _ o hs
        refine ⟨σ₁, e', fun x hx => ?_⟩
        simp only [Tree.wv, List.mem_cons, not_or] at hx
        rw [h x hx.2]; exact set_ne _ _ hx.1
  | .store b i e k, hc, σ, o, hs => by
    simp only [Tree.step] at hs
    cases hr : wr σ.heap b (i.denote σ.env).toNat ((e.denote σ.env).setWidth 8) with
    | none => rw [hr] at hs; cases hs
    | some H =>
      rw [hr] at hs
      obtain ⟨σ₁, e', h⟩ := calls_step k hc _ o hs
      exact ⟨σ₁, e', fun x hx => h x hx⟩
  | .ret _, hc, _, _, _ | .sub _ _, hc, _, _, _ => nomatch hc

theorem strip_calls (K : List Nat) : ∀ S : Tree, S.calls = true → (S.strip K).calls = true
  | .call _, _ => rfl
  | .ite _ a b, h => by
    simp only [Tree.calls, Tree.strip, Bool.and_eq_true] at h ⊢; exact ⟨strip_calls K a h.1, strip_calls K b h.2⟩
  | .let_ _ _ k, h | .load _ _ _ k, h | .cload _ _ _ _ _ k, h | .store _ _ _ k, h => strip_calls K k h
  | .ret _, h | .sub _ _, h => nomatch h

theorem strip_wf (L : Lay) (K : List Nat) : ∀ S : Tree, S.wf L → (S.strip K).wf L
  | .call as, h => ⟨Nat.le_trans (List.length_filter_le _ _) h.1, fun p hp => h.2 p (List.mem_filter.1 hp).1⟩
  | .ite _ a b, h => ⟨h.1, strip_wf L K a h.2.1, strip_wf L K b h.2.2⟩
  | .let_ _ _ k, h => ⟨h.1, h.2.1, strip_wf L K k h.2.2⟩
  | .load _ _ _ k, h => ⟨h.1, h.2.1, strip_wf L K k h.2.2⟩
  | .cload _ _ _ _ _ k, h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, strip_wf L K k h.2.2.2.2⟩
  | .store _ _ _ k, h => ⟨h.1, h.2.1, strip_wf L K k h.2.2⟩
  | .ret _, h | .sub _ _, h => h

theorem strip_wv (K : List Nat) {x : Nat} : ∀ S : Tree, S.calls = true → (x ∉ S.wv ∨ (x ∈ K ∧ x ∉ S.lets)) →
    x ∉ (S.strip K).wv
  | .call as, _, h => by
    intro hx
    simp only [Tree.strip, Tree.wv, List.mem_map, List.mem_filter] at hx
    obtain ⟨p, ⟨hp, hk⟩, rfl⟩ := hx
    rcases h with h | ⟨h, _⟩
    · exact h (List.mem_map.2 ⟨p, hp, rfl⟩)
    · simp at hk; exact hk h
  | .ite _ a b, hc, h => by
    simp only [Tree.calls, Bool.and_eq_true] at hc
    simp only [Tree.strip, Tree.wv, List.mem_append, not_or]
    simp only [Tree.wv, Tree.lets, List.mem_append, not_or] at h
    rcases h with ⟨ha, hb⟩ | ⟨h, ha, hb⟩
    · exact ⟨strip_wv K a hc.1 (.inl ha), strip_wv K b hc.2 (.inl hb)⟩
    · exact ⟨strip_wv K a hc.1 (.inr ⟨h, ha⟩), strip_wv K b hc.2 (.inr ⟨h, hb⟩)⟩
  | .let_ v _ k, hc, h | .load v _ _ k, hc, h | .cload v _ _ _ _ k, hc, h => by
    simp only [Tree.strip, Tree.wv, Tree.lets, List.mem_cons, not_or] at h ⊢
    rcases h with ⟨h1, h2⟩ | ⟨h, h1, h2⟩
    · exact ⟨h1, strip_wv K k hc (.inl h2)⟩
    · exact ⟨h1, strip_wv K k hc (.inr ⟨h, h2⟩)⟩
  | .store _ _ _ k, hc, h => by
    simp only [Tree.strip, Tree.wv, Tree.lets] at h ⊢
    exact strip_wv K k hc h
  | .ret _, hc, _ | .sub _ _, hc, _ => nomatch hc

theorem parSet_strip (KP : List (Nat × BitVec 64)) (ρ : BEnv) :
    ∀ (as : List (Nat × BExp)) (env : BEnv), (∀ p ∈ KP, ∀ q ∈ as, q.1 = p.1 → q.2 = .const p.2) →
    (∀ p ∈ KP, env p.1 = p.2) →
    parSet ρ env (as.filter fun q => !(KP.map (·.1)).contains q.1) = parSet ρ env as
  | [], _, _, _ => rfl
  | (v, e) :: as, env, hq, he => by
    have hq' : ∀ p ∈ KP, ∀ q ∈ as, q.1 = p.1 → q.2 = .const p.2 := fun p hp q hq'' =>
      hq p hp q (List.mem_cons_of_mem _ hq'')
    rw [List.filter_cons]
    by_cases hv : ∃ p ∈ KP, p.1 = v
    · obtain ⟨p, hp, rfl⟩ := hv
      have e' : e = .const p.2 := hq p hp _ List.mem_cons_self rfl
      subst e'
      have hc : (KP.map (·.1)).contains p.1 = true := List.contains_iff_mem.2 (List.mem_map.2 ⟨p, hp, rfl⟩)
      rw [if_neg (by rw [hc]; decide), parSet]
      have : env.set p.1 ((BExp.const p.2).denote ρ) = env := by
        funext x; by_cases hx : x = p.1
        · subst hx; rw [set_eq]; exact (he p hp).symm
        · exact set_ne _ _ hx
      rw [this]; exact parSet_strip KP ρ as env hq' he
    · have hc : (KP.map (·.1)).contains v = false := by
        cases h : (KP.map (·.1)).contains v
        · rfl
        · obtain ⟨q, hq2, e⟩ := List.mem_map.1 (List.contains_iff_mem.1 h); exact absurd ⟨q, hq2, e⟩ hv
      rw [if_pos (by rw [hc]; decide), parSet, parSet]
      exact parSet_strip KP ρ as _ hq' fun p hp => by rw [set_ne _ _ fun e => hv ⟨p, hp, e⟩]; exact he p hp

theorem pairs_sub : ∀ (S : Tree) {q : Nat × BExp}, (∀ as ∈ S.leaves, q ∈ as → q ∈ S.pairs) := by
  intro S
  induction S with
  | call as => intro q l hl hq; simp only [Tree.leaves, List.mem_singleton] at hl; subst hl; exact hq
  | ite _ a b iha ihb =>
    intro q l hl hq
    simp only [Tree.leaves, List.mem_append] at hl
    simp only [Tree.pairs, List.mem_append]
    exact hl.elim (fun h => .inl (iha l h hq)) (fun h => .inr (ihb l h hq))
  | let_ _ _ k ih | load _ _ _ k ih | cload _ _ _ _ _ k ih | store _ _ _ k ih | sub _ k ih =>
    intro q l hl hq; exact ih l hl hq
  | ret _ => intro q l hl; nomatch hl

/-- constants the variables already have need no assignment -/
theorem strip_step (KP : List (Nat × BitVec 64)) : ∀ (S : Tree), (∀ p ∈ KP, kOK S p = true) → ∀ σ : BState,
    (∀ p ∈ KP, σ.env p.1 = p.2) → (S.strip (KP.map (·.1))).step σ = S.step σ
  | .call as, hk, σ, he => by
    simp only [Tree.strip, Tree.step]
    rw [parSet_strip KP σ.env as σ.env (fun p hp q hq e => ?_) he]
    have := hk p hp
    simp only [kOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at this
    rcases this.1 q (by simpa [Tree.pairs] using hq) with h | h
    · exact absurd e h
    · obtain ⟨w, d⟩ := q
      cases d <;> simp_all [isK]
  | .ite c a b, hk, σ, he => by
    have ha : ∀ p ∈ KP, kOK a p = true := fun p hp => by
      have := hk p hp; simp only [kOK, Tree.pairs, Tree.lets, List.all_append, List.contains_append,
        Bool.and_eq_true, Bool.or_eq_false_iff, Bool.not_eq_true'] at this ⊢; exact ⟨this.1.1, this.2.1⟩
    have hb : ∀ p ∈ KP, kOK b p = true := fun p hp => by
      have := hk p hp; simp only [kOK, Tree.pairs, Tree.lets, List.all_append, List.contains_append,
        Bool.and_eq_true, Bool.or_eq_false_iff, Bool.not_eq_true'] at this ⊢; exact ⟨this.1.2, this.2.2⟩
    simp only [Tree.strip, Tree.step, strip_step KP a ha σ he, strip_step KP b hb σ he]
  | .let_ v e k, hk, σ, he => by
    have hk' : ∀ p ∈ KP, kOK k p = true := fun p hp => by
      have := hk p hp; simp only [kOK, Tree.pairs, Tree.lets, List.contains_cons, Bool.and_eq_true,
        Bool.or_eq_false_iff, Bool.not_eq_true'] at this ⊢; exact ⟨this.1, this.2.2⟩
    have hv : ∀ p ∈ KP, v ≠ p.1 := fun p hp e => by
      have := hk p hp; simp [kOK, Tree.lets, e] at this
    simp only [Tree.strip, Tree.step]
    exact strip_step KP k hk' _ fun p hp => by show BEnv.set _ _ _ _ = _; rw [set_ne _ _ (hv p hp).symm]; exact he p hp
  | .load v b i k, hk, σ, he => by
    have hk' : ∀ p ∈ KP, kOK k p = true := fun p hp => by
      have := hk p hp; simp only [kOK, Tree.pairs, Tree.lets, List.contains_cons, Bool.and_eq_true,
        Bool.or_eq_false_iff, Bool.not_eq_true'] at this ⊢; exact ⟨this.1, this.2.2⟩
    have hv : ∀ p ∈ KP, v ≠ p.1 := fun p hp e => by
      have := hk p hp; simp [kOK, Tree.lets, e] at this
    simp only [Tree.strip, Tree.step]
    cases rd σ.heap b (i.denote σ.env).toNat with
    | none => rfl
    | some y =>
      simp only [Option.bind_some]
      exact strip_step KP k hk' _ fun p hp => by show BEnv.set _ _ _ _ = _; rw [set_ne _ _ (hv p hp).symm]; exact he p hp
  | .cload v b i c d k, hk, σ, he => by
    have hk' : ∀ p ∈ KP, kOK k p = true := fun p hp => by
      have := hk p hp; simp only [kOK, Tree.pairs, Tree.lets, List.contains_cons, Bool.and_eq_true,
        Bool.or_eq_false_iff, Bool.not_eq_true'] at this ⊢; exact ⟨this.1, this.2.2⟩
    have hv : ∀ p ∈ KP, v ≠ p.1 := fun p hp e => by
      have := hk p hp; simp [kOK, Tree.lets, e] at this
    have hset : ∀ x, ∀ p ∈ KP, (σ.env.set v x) p.1 = p.2 := fun x p hp => by
      rw [set_ne _ _ (hv p hp).symm]; exact he p hp
    simp only [Tree.strip, Tree.step]
    split
    · exact strip_step KP k hk' _ (hset _)
    · cases rd σ.heap b (i.denote σ.env).toNat with
      | none => rfl
      | some y => simp only [Option.bind_some]; exact strip_step KP k hk' _ (hset _)
  | .store b i e k, hk, σ, he => by
    have hk' : ∀ p ∈ KP, kOK k p = true := fun p hp => by
      have := hk p hp; simpa [kOK, Tree.pairs, Tree.lets] using this
    simp only [Tree.strip, Tree.step]
    cases wr σ.heap b (i.denote σ.env).toNat ((e.denote σ.env).setWidth 8) with
    | none => rfl
    | some H => simp only [Option.bind_some]; exact strip_step KP k hk' _ he
  | .ret _, _, _, _ => rfl
  | .sub _ _, _, _, _ => rfl

/-- `S` is the prefix `xs`, then `k` -/
theorem pre_step : ∀ (xs : List Pre) (k : Tree) (σ : BState),
    (Pre.app xs k).step σ = ((Pre.app xs (.call [])).step σ).bind fun o => match o with
      | .call σX => k.step σX
      | .ret _ _ => none
  | [], k, σ => by simp [Pre.app, Tree.step, parSet]
  | .let_ v e :: xs, k, σ => pre_step xs k _
  | .load v b i :: xs, k, σ => by
    simp only [Pre.app, Tree.step]
    cases rd σ.heap b (i.denote σ.env).toNat with
    | none => rfl
    | some y => exact pre_step xs k _
  | .cload v b i c d :: xs, k, σ => by
    simp only [Pre.app, Tree.step]
    split
    · exact pre_step xs k _
    · cases rd σ.heap b (i.denote σ.env).toNat with
      | none => rfl
      | some y => exact pre_step xs k _

theorem splitPre_eq : ∀ {S : Tree} {xs : List Pre} {c : BExp} {a b : Tree}, splitPre S = some (xs, c, a, b) →
    S = Pre.app xs (.ite c a b)
  | .ite c' a' b', xs, c, a, b, h => by
    simp only [splitPre, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  | .let_ v e k, xs, c, a, b, h => by
    simp only [splitPre] at h
    cases hk : splitPre k with
    | none => rw [hk] at h; exact nomatch h
    | some r =>
      obtain ⟨xs', c', a', b'⟩ := r
      rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rw [splitPre_eq hk]; rfl
  | .load v b' i k, xs, c, a, b, h => by
    simp only [splitPre] at h
    cases hk : splitPre k with
    | none => rw [hk] at h; exact nomatch h
    | some r =>
      obtain ⟨xs', c', a', b'⟩ := r
      rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rw [splitPre_eq hk]; rfl
  | .cload v b' i c' d k, xs, c, a, b, h => by
    simp only [splitPre] at h
    cases hk : splitPre k with
    | none => rw [hk] at h; exact nomatch h
    | some r =>
      obtain ⟨xs', c', a', b'⟩ := r
      rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rw [splitPre_eq hk]; rfl
  | .ret _, _, _, _, _, h | .call _, _, _, _, _, h | .store _ _ _ _, _, _, _, _, h | .sub _ _, _, _, _, _, h =>
    nomatch h

/-! ## Hoisting the pairs common to all `call` leaves -/

theorem parSet_val (ρ : BEnv) (x : Nat) (e : BExp) : ∀ (l : List (Nat × BExp)) (env : BEnv),
    (∀ q ∈ l, q.1 = x → q.2 = e) → (∃ q ∈ l, q.1 = x) → parSet ρ env l x = e.denote ρ
  | [], _, _, h => by obtain ⟨_, h, _⟩ := h; exact nomatch h
  | (v, e') :: l, env, hq, hx => by
    rw [parSet]
    by_cases h : ∃ q ∈ l, q.1 = x
    · exact parSet_val ρ x e l _ (fun q hq' => hq q (List.mem_cons_of_mem _ hq')) h
    · have hv : v = x := by
        obtain ⟨q, hq', e''⟩ := hx
        rcases List.mem_cons.1 hq' with rfl | hq'
        · exact e''
        · exact absurd ⟨q, hq', e''⟩ h
      have he := hq _ List.mem_cons_self hv
      simp only at he
      rw [parSet_out ρ x l _ fun q hq' e'' => h ⟨q, hq', e''⟩, hv, set_eq, he]

theorem parSet_filter (ρ : BEnv) (T : List Nat) {x : Nat} (hx : x ∉ T) : ∀ (l : List (Nat × BExp)) (env env' : BEnv),
    (∀ y, y ∉ T → env y = env' y) → parSet ρ env l x = parSet ρ env' (l.filter fun q => !T.contains q.1) x
  | [], _, _, h => h x hx
  | (v, e) :: l, env, env', h => by
    rw [List.filter_cons]
    by_cases hv : v ∈ T
    · rw [if_neg (by rw [List.contains_iff_mem.2 hv]; decide), parSet]
      exact parSet_filter ρ T hx l _ _ fun y hy => by
        rw [set_ne _ _ fun e => hy (by rw [e]; exact hv)]; exact h y hy
    · have : T.contains v = false := by cases h' : T.contains v; rfl; exact absurd (List.contains_iff_mem.1 h') hv
      rw [if_pos (by rw [this]; decide), parSet, parSet]
      exact parSet_filter ρ T hx l _ _ fun y hy => by
        by_cases e' : y = v
        · subst e'; rw [set_eq, set_eq]
        · rw [set_ne _ _ e', set_ne _ _ e']; exact h y hy

/-- the conditions under which the pairs `H` can be assigned after the step -/
def HoistOK (S : Tree) (H : List (Nat × BExp)) : Prop :=
  (∀ l ∈ S.leaves, (∀ p ∈ H, p ∈ l) ∧ (l.map (·.1)).Nodup) ∧
  ∀ p ∈ H, p.1 ∉ (S.strip (H.map (·.1))).wv ∧ ∀ x ∈ p.2.vs, x ∉ (S.strip (H.map (·.1))).wv

theorem nodup_val {l : List (Nat × BExp)} (hn : (l.map (·.1)).Nodup) {p q : Nat × BExp} (hp : p ∈ l) (hq : q ∈ l)
    (e : q.1 = p.1) : q.2 = p.2 := by
  induction l with
  | nil => exact nomatch hp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.1 hp with rfl | hp' <;> rcases List.mem_cons.1 hq with rfl | hq'
    · rfl
    · exact absurd e (hn.1 q hq')
    · exact absurd e.symm (hn.1 p hp')
    · exact ih hn.2 hp' hq'

theorem hoist_call (H as : List (Nat × BExp)) (env : BEnv) (hH : ∀ p ∈ H, p ∈ as) (hn : (as.map (·.1)).Nodup)
    (hv : ∀ p ∈ H, ∀ x ∈ p.2.vs, x ∉ (as.filter fun q => !(H.map (·.1)).contains q.1).map (·.1)) :
    parSet env env as = parSet (parSet env env (as.filter fun q => !(H.map (·.1)).contains q.1))
      (parSet env env (as.filter fun q => !(H.map (·.1)).contains q.1)) H := by
  funext x
  by_cases hx : x ∈ H.map (·.1)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    have hpa := hH p hp
    rw [parSet_val env p.1 p.2 as env (fun q hq e => nodup_val hn hpa hq e) ⟨p, hpa, rfl⟩,
      parSet_val _ p.1 p.2 H _ (fun q hq e => nodup_val hn hpa (hH q hq) e) ⟨p, hp, rfl⟩]
    exact (denote_vs p.2 fun y hy => parSet_out _ _ _ _ fun q hq e => hv p hp y hy
      (List.mem_map.2 ⟨q, hq, e⟩)).symm
  · rw [parSet_out _ _ H _ fun q hq e => hx (List.mem_map.2 ⟨q, hq, e⟩)]
    exact parSet_filter env _ hx as env env fun _ _ => rfl

theorem hoist_step (H : List (Nat × BExp)) : ∀ (S : Tree), S.calls = true →
    (∀ l ∈ S.leaves, (∀ p ∈ H, p ∈ l) ∧ (l.map (·.1)).Nodup) →
    (∀ p ∈ H, ∀ x ∈ p.2.vs, x ∉ (S.strip (H.map (·.1))).wv) →
    ∀ (σ σ₁ : BState), S.step σ = some (.call σ₁) →
    ∃ σ₂, (S.strip (H.map (·.1))).step σ = some (.call σ₂) ∧ (Tree.call H).step σ₂ = some (.call σ₁)
  | .call as, _, hl, hv, σ, σ₁, hs => by
    simp only [Tree.step, Option.some.injEq, Out.call.injEq] at hs; subst hs
    obtain ⟨hH, hn⟩ := hl as (List.mem_singleton_self _)
    refine ⟨_, rfl, ?_⟩
    simp only [Tree.step, Option.some.injEq, Out.call.injEq, BState.mk.injEq, and_true]
    exact (hoist_call H as σ.env hH hn hv).symm
  | .ite c a b, hc, hl, hv, σ, σ₁, hs => by
    simp only [Tree.calls, Bool.and_eq_true] at hc
    simp only [Tree.strip, Tree.step]
    simp only [Tree.step] at hs
    split
    · rw [if_pos (by assumption)] at hs
      exact hoist_step H b hc.2 (fun l h => hl l (by simp [Tree.leaves, h]))
        (fun p hp x hx h => hv p hp x hx (by simp [Tree.strip, Tree.wv, h])) σ σ₁ hs
    · rw [if_neg (by assumption)] at hs
      exact hoist_step H a hc.1 (fun l h => hl l (by simp [Tree.leaves, h]))
        (fun p hp x hx h => hv p hp x hx (by simp [Tree.strip, Tree.wv, h])) σ σ₁ hs
  | .let_ v e k, hc, hl, hv, σ, σ₁, hs => by
    simp only [Tree.strip, Tree.step]
    exact hoist_step H k hc hl (fun p hp x hx h => hv p hp x hx (by simp [Tree.strip, Tree.wv, h])) _ σ₁ hs
  | .load v b i k, hc, hl, hv, σ, σ₁, hs => by
    simp only [Tree.strip, Tree.step]
    simp only [Tree.step] at hs
    cases hr : rd σ.heap b (i.denote σ.env).toNat with
    | none => rw [hr] at hs; cases hs
    | some y =>
      rw [hr] at hs
      exact hoist_step H k hc hl (fun p hp x hx h => hv p hp x hx (by simp [Tree.strip, Tree.wv, h])) _ σ₁ hs
  | .cload v b i c d k, hc, hl, hv, σ, σ₁, hs => by
    simp only [Tree.strip, Tree.step]
    simp only [Tree.step] at hs
    split
    · rw [if_pos (by assumption)] at hs
      exact hoist_step H k hc hl (fun p hp x hx h => hv p hp x hx (by simp [Tree.strip, Tree.wv, h])) _ σ₁ hs
    · rw [if_neg (by assumption)] at hs
      cases hr : rd σ.heap b (i.denote σ.env).toNat with
      | none => rw [hr] at hs; cases hs
      | some y =>
        rw [hr] at hs
        exact hoist_step H k hc hl (fun p hp x hx h => hv p hp x hx (by simp [Tree.strip, Tree.wv, h])) _ σ₁ hs
  | .store b i e k, hc, hl, hv, σ, σ₁, hs => by
    simp only [Tree.strip, Tree.step]
    simp only [Tree.step] at hs
    cases hr : wr σ.heap b (i.denote σ.env).toNat ((e.denote σ.env).setWidth 8) with
    | none => rw [hr] at hs; cases hs
    | some y =>
      rw [hr] at hs
      exact hoist_step H k hc hl (fun p hp x hx h => hv p hp x hx (by simp [Tree.strip, Tree.wv, h])) _ σ₁ hs
  | .ret _, hc, _, _, _, _, _ | .sub _ _, hc, _, _, _, _, _ => nomatch hc

theorem leaves_wv : ∀ (S : Tree) {l : List (Nat × BExp)}, l ∈ S.leaves → ∀ q ∈ l, q.1 ∈ S.wv
  | .call as, l, hl, q, hq => by
    simp only [Tree.leaves, List.mem_singleton] at hl; subst hl
    exact List.mem_map.2 ⟨q, hq, rfl⟩
  | .ite _ a b, l, hl, q, hq => by
    simp only [Tree.leaves, List.mem_append] at hl
    simp only [Tree.wv, List.mem_append]
    exact hl.elim (fun h => .inl (leaves_wv a h q hq)) (fun h => .inr (leaves_wv b h q hq))
  | .let_ _ _ k, l, hl, q, hq | .load _ _ _ k, l, hl, q, hq | .cload _ _ _ _ _ k, l, hl, q, hq =>
    List.mem_cons_of_mem _ (leaves_wv k hl q hq)
  | .store _ _ _ k, l, hl, q, hq | .sub _ k, l, hl, q, hq => leaves_wv k hl q hq
  | .ret _, _, hl, _, _ => nomatch hl

/-- what `common` returns satisfies the conditions of `hoist_step` -/
theorem common_ok (S : Tree) :
    (∀ l ∈ S.leaves, (∀ p ∈ common S, p ∈ l) ∧ (l.map (·.1)).Nodup) ∧
    (∀ p ∈ common S, ∀ x ∈ p.2.vs, x ∉ (S.strip ((common S).map (·.1))).wv) ∨ common S = [] := by
  unfold common
  split
  · exact .inr rfl
  · rename_i as ls hls
    dsimp only
    split
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      refine .inl ⟨fun l hl => ⟨fun p hp => ?_, hc.1 l hl⟩, fun p hp x hx h => ?_⟩
      · rw [hls] at hl
        obtain ⟨hp, hq⟩ := List.mem_filter.1 hp
        rcases List.mem_cons.1 hl with rfl | hl
        · exact hp
        · exact List.contains_iff_mem.1 (List.all_eq_true.1 hq l hl)
      · have := (hc.2 p hp).2 x hx
        rw [List.contains_iff_mem.2 h] at this; exact nomatch this
    · exact .inr rfl

/-! ## Fast loops keep the iteration invariant -/

/-- between iterations: `m` more `call` steps to the result `r` (final state `σf`), or returned -/
def Inv (L : Lay) (t : Tree) (r : BitVec 64) (σf : BState) (m : Nat) (τ : BState) : Prop :=
  (τ.env L.fl ≠ 0 ∧ ∃ σ, t.RunsN m σ r σf ∧ Agree L.M σ τ) ∨ (τ.env L.fl = 0 ∧ τ.env L.res = r ∧ Agree L.M σf τ)

/-- a program that keeps the invariant (and does not increase the number of steps left) -/
def FastOK (L : Lay) (t : Tree) (F : BStmt) : Prop :=
  ∀ r σf m τ, Inv L t r σf m τ → ∃ m' τ', m' ≤ m ∧ BExec F τ τ' ∧ Inv L t r σf m' τ'

theorem Agree.set {M : Nat} {σ τ : BState} (h : Agree M σ τ) {g : Nat} (hg : M ≤ g) (x : BitVec 64) :
    Agree M σ ⟨τ.env.set g x, τ.heap⟩ := ⟨fun v hv => (set_ne _ _ (by omega)).trans (h.1 v hv), h.2⟩

theorem Inv.set {L : Lay} {t : Tree} {r : BitVec 64} {σf : BState} {m : Nat} {τ : BState} (h : Inv L t r σf m τ)
    {g : Nat} (hg : L.M + 2 ≤ g) (x : BitVec 64) : Inv L t r σf m ⟨τ.env.set g x, τ.heap⟩ := by
  have hfl : (τ.env.set g x) L.fl = τ.env L.fl := set_ne _ _ (by simp only [Lay.fl]; omega)
  have hres : (τ.env.set g x) L.res = τ.env L.res := set_ne _ _ (by simp only [Lay.res]; omega)
  rcases h with ⟨h1, σ, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact .inl ⟨by simp only [hfl]; exact h1, σ, h2, h3.set (by omega) x⟩
  · exact .inr ⟨by simp only [hfl]; exact h1, by simp only [hres]; exact h2, h3.set (by omega) x⟩

theorem whenS_ok (g : Nat) (e : BExp) (c : BStmt) (τ : BState) (P : BState → Prop)
    (h0 : e.denote τ.env = 0 → P ⟨τ.env.set g 0, τ.heap⟩)
    (h1 : e.denote τ.env ≠ 0 → ∃ τ', BExec c ⟨τ.env.set g (e.denote τ.env), τ.heap⟩ τ' ∧
      P ⟨τ'.env.set g 0, τ'.heap⟩) :
    ∃ τ', BExec (whenS g e c) τ τ' ∧ P τ' := by
  by_cases he : e.denote τ.env = 0
  · refine ⟨_, .seq .assign (.loopF ?_), ?_⟩
    · show BEnv.set _ _ _ _ = 0; rw [set_eq, he]
    · rw [he]; exact h0 he
  · obtain ⟨τ', hc, hp⟩ := h1 he
    exact ⟨_, .seq .assign (.loopT (by show BEnv.set _ _ _ _ ≠ 0; rw [set_eq]; exact he) (.seq hc .assign)
      (.loopF (by show BEnv.set _ _ _ _ = 0; rw [set_eq]; rfl))), hp⟩

theorem conj_cons_ne (env : BEnv) (c : BExp) (cs : List BExp) :
    (conj (c :: cs)).denote env ≠ 0 ↔ c.denote env ≠ 0 ∧ ∀ x ∈ cs, x.denote env ≠ 0 := by
  rw [conj_ne]; simp

theorem conj_agree {M : Nat} {σ τ : BState} (h : Agree M σ τ) {cs : List BExp} (hv : ∀ c ∈ cs, c.vlt M) :
    (∀ c ∈ cs, c.denote τ.env ≠ 0) ↔ (∀ c ∈ cs, c.denote σ.env ≠ 0) :=
  ⟨fun h' c hc => by rw [← denote_agree h.1 c (hv c hc)]; exact h' c hc,
   fun h' c hc => by rw [denote_agree h.1 c (hv c hc)]; exact h' c hc⟩

theorem RunsN.some {t : Tree} {n : Nat} {σ σ' : BState} {r : BitVec 64} (h : t.RunsN n σ r σ') :
    ∃ o, t.step σ = some o := by
  cases h with
  | ret hs => exact ⟨_, hs⟩
  | call hs _ => exact ⟨_, hs⟩

/-- **a loop of `call` steps** (`S` the subtree, `body` its compiled step) keeps the invariant -/
theorem fastLoop_ok (L : Lay) (t : Tree) (Gi Gv : List BExp) (body : BStmt) (S : Tree)
    (hvi : ∀ c ∈ Gi, c.vlt L.M) (hvv : ∀ c ∈ Gv, c.vlt L.M)
    (hpath : ∀ σ : BState, (∀ c ∈ Gi, c.denote σ.env ≠ 0) → (∀ c ∈ Gv, c.denote σ.env ≠ 0) → t.step σ = S.step σ)
    (hstep : ∀ σ o, (∀ c ∈ Gi, c.denote σ.env ≠ 0) → S.step σ = some o →
      ∃ σ₁, o = .call σ₁ ∧ ∀ c ∈ Gi, c.denote σ₁.env ≠ 0)
    (hbody : ∀ σ σ₁ τ, (∀ c ∈ Gi, c.denote σ.env ≠ 0) → S.step σ = some (.call σ₁) → Agree L.M σ τ →
      ∃ τ₁, BExec body τ τ₁ ∧ Agree L.M σ₁ τ₁ ∧ τ₁.env L.fl = τ.env L.fl)
    (g : Nat) (hg : L.M + 2 ≤ g) :
    FastOK L t (whenS g (conj (.var L.fl :: Gi)) (.loop (conj Gv) body)) := by
  intro r σf
  have key : ∀ m σ τ, t.RunsN m σ r σf → Agree L.M σ τ → τ.env L.fl ≠ 0 → (∀ c ∈ Gi, c.denote σ.env ≠ 0) →
      ∃ m' τ', m' ≤ m ∧ BExec (.loop (conj Gv) body) τ τ' ∧ Inv L t r σf m' τ' := by
    intro m σ τ h
    induction h generalizing τ with
    | @ret σ r' σ' hs =>
      intro hA hf hgi
      by_cases hv : (conj Gv).denote τ.env = 0
      · exact ⟨0, τ, Nat.le_refl _, .loopF hv, .inl ⟨hf, σ, .ret hs, hA⟩⟩
      · have hv' := (conj_agree hA hvv).1 ((conj_ne _ _).1 hv)
        obtain ⟨σ₁, e, _⟩ := hstep σ _ hgi ((hpath σ hgi hv').symm.trans hs)
        cases e
    | @call n σ σ₁ r' σ' hs hn ih =>
      intro hA hf hgi
      by_cases hv : (conj Gv).denote τ.env = 0
      · exact ⟨n + 1, τ, Nat.le_refl _, .loopF hv, .inl ⟨hf, σ, .call hs hn, hA⟩⟩
      · have hv' := (conj_agree hA hvv).1 ((conj_ne _ _).1 hv)
        have hs' := (hpath σ hgi hv').symm.trans hs
        obtain ⟨σ₂, e, hgi'⟩ := hstep σ _ hgi hs'
        have e' := Out.call.inj e
        subst e'
        obtain ⟨τ₁, hb, hA₁, hf₁⟩ := hbody σ σ₁ τ hgi hs' hA
        obtain ⟨m', τ', hm, hl, hI'⟩ := ih τ₁ hA₁ (by rw [hf₁]; exact hf) hgi'
        exact ⟨m', τ', by omega, .loopT hv hb hl, hI'⟩
  intro m τ hI
  refine (whenS_ok g _ _ τ (fun τ' => ∃ m', m' ≤ m ∧ Inv L t r σf m' τ') (fun _ => ⟨m, Nat.le_refl _, hI.set hg 0⟩)
    fun hc => ?_).elim fun τ' ⟨hx, m', hm, hI'⟩ => ⟨m', τ', hm, hx, hI'⟩
  obtain ⟨hf, hgi⟩ := (conj_cons_ne _ _ _).1 hc
  rcases hI with ⟨_, σ, hR, hA⟩ | ⟨hf0, _⟩
  · obtain ⟨m', τ', hm, hl, hI'⟩ := key m σ _ hR (hA.set (g := g) (by omega) ((conj (.var L.fl :: Gi)).denote τ.env))
      (by show BEnv.set _ _ _ _ ≠ 0; rw [set_ne _ _ (by simp only [Lay.fl]; omega)]; exact hf)
      ((conj_agree hA hvi).1 hgi)
    exact ⟨τ', hl, m', hm, hI'.set hg 0⟩
  · exact absurd hf0 hf

theorem ite_ne (env : BEnv) (c a : BExp) : (BExp.ite c a (.const 0)).denote env ≠ 0 ↔ c.denote env ≠ 0 ∧ a.denote env ≠ 0 := by
  simp only [BExp.denote]
  by_cases h : c.denote env = 0
  · simp [h]
  · simp [h]

theorem eqz_ne (env : BEnv) (c : BExp) : (eqz c).denote env ≠ 0 ↔ c.denote env = 0 := by
  simp only [eqz, BExp.denote, Op.eval]
  by_cases h : c.denote env = 0 <;> simp [h]

/-- **a search loop** (`X`, then the test `c'`: continue with the `call` branch `S2` or leave and run `R`) keeps
the invariant -/
theorem fastExit_ok (L : Lay) (t : Tree) (Gi Gv : List BExp) (X : Tree) (c' : BExp) (S2 R : Tree) (body2 : BStmt)
    (hvi : ∀ c ∈ Gi, c.vlt L.M) (hvv : ∀ c ∈ Gv, c.vlt L.M) (hvc : c'.vlt L.M)
    (hXc : X.calls = true) (hXw : X.wf L) (hRw : R.wf L)
    (hpath : ∀ σ : BState, (∀ c ∈ Gi, c.denote σ.env ≠ 0) → (∀ c ∈ Gv, c.denote σ.env ≠ 0) →
      t.step σ = (X.step σ).bind fun o => match o with
        | .call σX => if c'.denote σX.env = 0 then R.step σX else S2.step σX
        | .ret _ _ => none)
    (hGvX : ∀ σ σX, X.step σ = some (.call σX) → ∀ c ∈ Gv, c.denote σX.env = c.denote σ.env)
    (hstep2 : ∀ σ σX o, (∀ c ∈ Gi, c.denote σ.env ≠ 0) → X.step σ = some (.call σX) → S2.step σX = some o →
      ∃ σ₁, o = .call σ₁ ∧ ∀ c ∈ Gi, c.denote σ₁.env ≠ 0)
    (hbody2 : ∀ σ σX σ₁ τ, (∀ c ∈ Gi, c.denote σ.env ≠ 0) → X.step σ = some (.call σX) →
      S2.step σX = some (.call σ₁) → Agree L.M σX τ →
      ∃ τ₁, BExec body2 τ τ₁ ∧ Agree L.M σ₁ τ₁ ∧ τ₁.env L.fl = τ.env L.fl ∧ τ₁.env (L.cv 0 + 1) = τ.env (L.cv 0 + 1)) :
    FastOK L t (whenS (L.cv 0) (conj (.var L.fl :: Gi))
      (.seq (.seq (.assign (L.cv 0 + 1) (.const 1)) (.loop (.ite (conj Gv) (.var (L.cv 0 + 1)) (.const 0))
          (.seq (comp L X 1) (.seq (.assign (L.cv 0 + 1) c') (whenS (L.cv 1) (.var (L.cv 0 + 1)) body2)))))
        (whenS (L.cv 1) (.ite (conj Gv) (eqz c') (.const 0)) (comp L R 2)))) := by
  intro r σf
  have hk : L.M + 2 ≤ L.cv 0 + 1 := by simp only [Lay.cv]; omega
  have hw : L.M + 2 ≤ L.cv 1 := by simp only [Lay.cv]; omega
  have hkw : L.cv 0 + 1 ≠ L.cv 1 := by simp only [Lay.cv]; omega
  have hfl : ∀ (τ : BState) g x, L.M + 2 ≤ g → (τ.env.set g x) L.fl = τ.env L.fl := fun τ g x hg =>
    set_ne _ _ (by simp only [Lay.fl]; omega)
  have hfl : ∀ (e : BEnv) g x, L.M + 2 ≤ g → e.set g x L.fl = e L.fl := fun e g x hg =>
    set_ne _ _ (by simp only [Lay.fl]; omega)
  -- one more round of the inner loop from a state that leaves it after `X` (`c'` false)
  have leave : ∀ σ τ σX τX, Agree L.M σX τX → c'.denote σX.env = 0 → (conj Gv).denote τ.env ≠ 0 →
      τ.env (L.cv 0 + 1) ≠ 0 → BExec (comp L X 1) τ τX → (∀ c ∈ Gv, c.denote σ.env ≠ 0) →
      X.step σ = some (.call σX) →
      BExec (.loop (.ite (conj Gv) (.var (L.cv 0 + 1)) (.const 0))
          (.seq (comp L X 1) (.seq (.assign (L.cv 0 + 1) c') (whenS (L.cv 1) (.var (L.cv 0 + 1)) body2)))) τ
        ⟨(τX.env.set (L.cv 0 + 1) (c'.denote τX.env)).set (L.cv 1) 0, τX.heap⟩ := by
    intro σ τ σX τX hAX hc0 hv hk0 xX hv' hX
    have hck : c'.denote τX.env = 0 := by rw [denote_agree hAX.1 c' hvc]; exact hc0
    obtain ⟨τW, xW, eW⟩ := whenS_ok (L.cv 1) (.var (L.cv 0 + 1)) body2 ⟨τX.env.set (L.cv 0 + 1)
        (c'.denote τX.env), τX.heap⟩ (fun τ' => τ' = ⟨(τX.env.set (L.cv 0 + 1) (c'.denote τX.env)).set (L.cv 1) 0,
          τX.heap⟩) (fun _ => rfl) (fun h => absurd (by show BEnv.set _ _ _ _ = 0; rw [set_eq]; exact hck) h)
    subst eW
    refine .loopT ((ite_ne _ _ _).2 ⟨hv, hk0⟩) (.seq xX (.seq .assign xW)) (.loopF ?_)
    show (BExp.ite (conj Gv) (.var (L.cv 0 + 1)) (.const 0)).denote _ = 0
    simp only [BExp.denote]
    rw [show (BEnv.set (BEnv.set τX.env (L.cv 0 + 1) (c'.denote τX.env)) (L.cv 1) 0) (L.cv 0 + 1) = 0 by
      rw [set_ne _ _ hkw, set_eq, hck]]
    split <;> rfl
  -- the inner loop ends with the path's conditions false, or after `X` with `c'` false
  have key : ∀ m σ τ, t.RunsN m σ r σf → Agree L.M σ τ → τ.env L.fl ≠ 0 → (∀ c ∈ Gi, c.denote σ.env ≠ 0) →
      τ.env (L.cv 0 + 1) ≠ 0 →
      ∃ τ', BExec (.loop (.ite (conj Gv) (.var (L.cv 0 + 1)) (.const 0))
          (.seq (comp L X 1) (.seq (.assign (L.cv 0 + 1) c') (whenS (L.cv 1) (.var (L.cv 0 + 1)) body2)))) τ τ' ∧
        ∃ m', m' ≤ m ∧ ∃ σ', t.RunsN m' σ' r σf ∧ τ'.env L.fl ≠ 0 ∧
          ((Agree L.M σ' τ' ∧ (conj Gv).denote τ'.env = 0) ∨
           (∃ σX, X.step σ' = some (.call σX) ∧ Agree L.M σX τ' ∧ c'.denote σX.env = 0 ∧
             (∀ c ∈ Gi, c.denote σ'.env ≠ 0) ∧ ∀ c ∈ Gv, c.denote σ'.env ≠ 0)) := by
    intro m σ τ h
    induction h generalizing τ with
    | @ret σ r' σ' hs =>
      intro hA hf hgi hk0
      by_cases hv : (conj Gv).denote τ.env = 0
      · exact ⟨τ, .loopF (by simp only [BExp.denote, hv]; rfl), 0, Nat.le_refl _, σ, .ret hs, hf, .inl ⟨hA, hv⟩⟩
      · have hv' := (conj_agree hA hvv).1 ((conj_ne _ _).1 hv)
        have hp := (hpath σ hgi hv').symm.trans hs
        cases hX : X.step σ with
        | none => rw [hX] at hp; cases hp
        | some oX =>
          obtain ⟨σX, rfl, _⟩ := calls_step X hXc σ oX hX
          rw [hX] at hp
          simp only [Option.bind_some] at hp
          obtain ⟨τX, xX, fX, pX⟩ := comp_ok L X 1 σ τ _ hXw hA hX
          by_cases hc0 : c'.denote σX.env = 0
          · refine ⟨_, leave σ τ σX τX pX.1 hc0 hv hk0 xX hv' hX, 0, Nat.le_refl _, σ, .ret hs, ?_,
              .inr ⟨σX, hX, (pX.1.set (g := L.cv 0 + 1) (by omega) _).set (g := L.cv 1) (by omega) _, hc0, hgi, hv'⟩⟩
            show BEnv.set (BEnv.set τX.env _ _) _ _ L.fl ≠ 0
            rw [hfl _ _ _ hw, hfl _ _ _ hk, pX.2]; exact hf
          · rw [if_neg hc0] at hp
            obtain ⟨σ₁, e, _⟩ := hstep2 σ σX _ hgi hX hp
            cases e
    | @call n σ σ₁ r' σ' hs hn ih =>
      intro hA hf hgi hk0
      by_cases hv : (conj Gv).denote τ.env = 0
      · exact ⟨τ, .loopF (by simp only [BExp.denote, hv]; rfl), n + 1, Nat.le_refl _, σ, .call hs hn, hf,
          .inl ⟨hA, hv⟩⟩
      · have hv' := (conj_agree hA hvv).1 ((conj_ne _ _).1 hv)
        have hp := (hpath σ hgi hv').symm.trans hs
        cases hX : X.step σ with
        | none => rw [hX] at hp; cases hp
        | some oX =>
          obtain ⟨σX, rfl, _⟩ := calls_step X hXc σ oX hX
          rw [hX] at hp
          simp only [Option.bind_some] at hp
          obtain ⟨τX, xX, fX, pX⟩ := comp_ok L X 1 σ τ _ hXw hA hX
          have hcv : c'.denote τX.env = c'.denote σX.env := denote_agree pX.1.1 c' hvc
          by_cases hc0 : c'.denote σX.env = 0
          · refine ⟨_, leave σ τ σX τX pX.1 hc0 hv hk0 xX hv' hX, n + 1, Nat.le_refl _, σ, .call hs hn, ?_,
              .inr ⟨σX, hX, (pX.1.set (g := L.cv 0 + 1) (by omega) _).set (g := L.cv 1) (by omega) _, hc0, hgi, hv'⟩⟩
            show BEnv.set (BEnv.set τX.env _ _) _ _ L.fl ≠ 0
            rw [hfl _ _ _ hw, hfl _ _ _ hk, pX.2]; exact hf
          · rw [if_neg hc0] at hp
            obtain ⟨σ₂, e, hgi₁⟩ := hstep2 σ σX _ hgi hX hp
            have e' := Out.call.inj e
            subst e'
            have hτK : τX.env L.fl ≠ 0 := by rw [pX.2]; exact hf
            obtain ⟨τW, xW, hAW, hfW, hkW⟩ := whenS_ok (L.cv 1) (.var (L.cv 0 + 1)) body2
              ⟨τX.env.set (L.cv 0 + 1) (c'.denote τX.env), τX.heap⟩
              (fun τ' => Agree L.M σ₁ τ' ∧ τ'.env L.fl ≠ 0 ∧ τ'.env (L.cv 0 + 1) ≠ 0)
              (fun h => absurd h (by show BEnv.set _ _ _ _ ≠ 0; rw [set_eq, hcv]; exact hc0)) fun _ => by
                obtain ⟨τ₁, xb, hA₁, hf₁, hk₁⟩ := hbody2 σ σX σ₁ _ hgi hX hp
                  (((pX.1.set (g := L.cv 0 + 1) (by omega) (c'.denote τX.env)).set (g := L.cv 1) (by omega) _))
                refine ⟨τ₁, xb, hA₁.set (by omega) 0, ?_, ?_⟩
                · show BEnv.set _ _ _ _ ≠ 0
                  rw [hfl _ _ _ hw, hf₁]
                  show BEnv.set (BEnv.set τX.env _ _) _ _ L.fl ≠ 0
                  rw [hfl _ _ _ hw, hfl _ _ _ hk]; exact hτK
                · show BEnv.set _ _ _ _ ≠ 0
                  rw [set_ne _ _ hkw, hk₁]
                  show BEnv.set (BEnv.set τX.env _ _) _ _ (L.cv 0 + 1) ≠ 0
                  rw [set_ne _ _ hkw, set_eq, hcv]; exact hc0
            obtain ⟨τ', xl, m', hm, σ'', hR, hf'', hQ⟩ := ih τW hAW hfW hgi₁ hkW
            exact ⟨τ', .loopT ((ite_ne _ _ _).2 ⟨hv, hk0⟩) (.seq xX (.seq .assign xW)) xl, m', by omega, σ'', hR,
              hf'', hQ⟩
  intro m τ hI
  refine (whenS_ok (L.cv 0) _ _ τ (fun τ' => ∃ m', m' ≤ m ∧ Inv L t r σf m' τ')
    (fun _ => ⟨m, Nat.le_refl _, hI.set (by simp only [Lay.cv]; omega) 0⟩) fun hc => ?_).elim
    fun τ' ⟨hx, m', hm, hI'⟩ => ⟨m', τ', hm, hx, hI'⟩
  obtain ⟨hf, hgi⟩ := (conj_cons_ne _ _ _).1 hc
  obtain ⟨_, σ, hR, hA⟩ := hI.resolve_right fun h => hf h.1
  have hg0 : L.M + 2 ≤ L.cv 0 := by simp only [Lay.cv]; omega
  -- `k := 1`, the inner loop
  obtain ⟨τ₃, xl, m', hm, σ', hR', hf₃, hQ⟩ := key m σ
    ⟨(τ.env.set (L.cv 0) ((conj (.var L.fl :: Gi)).denote τ.env)).set (L.cv 0 + 1) 1, τ.heap⟩ hR
    ((hA.set (g := L.cv 0) (by omega) _).set (g := L.cv 0 + 1) (by omega) _)
    (by show BEnv.set _ _ _ _ ≠ 0; rw [hfl _ _ _ hk, hfl _ _ _ hg0]; exact hf)
    ((conj_agree hA hvi).1 hgi) (by show BEnv.set _ _ _ _ ≠ 0; rw [set_eq]; decide)
  -- the other branch, when the loop ended after `X` with `c'` false
  obtain ⟨τ₄, x₄, m'', hm'', hI₄⟩ : ∃ τ₄, BExec (whenS (L.cv 1) (.ite (conj Gv) (eqz c') (.const 0)) (comp L R 2)) τ₃ τ₄ ∧
      ∃ m'', m'' ≤ m' ∧ Inv L t r σf m'' τ₄ := by
    -- in the second case the guard holds
    have hgd : ∀ σX, Agree L.M σX τ₃ → X.step σ' = some (.call σX) → c'.denote σX.env = 0 →
        (∀ c ∈ Gv, c.denote σ'.env ≠ 0) → (BExp.ite (conj Gv) (eqz c') (.const 0)).denote τ₃.env ≠ 0 := by
      intro σX hA₃ hX hc0 hv
      refine (ite_ne _ _ _).2 ⟨(conj_ne _ _).2 fun c hc => ?_, (eqz_ne _ _).2 ?_⟩
      · rw [denote_agree hA₃.1 c (hvv c hc), hGvX σ' σX hX c hc]; exact hv c hc
      · rw [denote_agree hA₃.1 c' hvc]; exact hc0
    refine whenS_ok _ _ _ τ₃ _ ?_ ?_
    · intro h0
      rcases hQ with ⟨hA₃, _⟩ | ⟨σX, hX, hA₃, hc0, _, hv⟩
      · exact ⟨m', Nat.le_refl _, (Inv.set (.inl ⟨hf₃, σ', hR', hA₃⟩) hw 0)⟩
      · exact absurd h0 (hgd σX hA₃ hX hc0 hv)
    · intro h1
      rcases hQ with ⟨hA₃, hv0⟩ | ⟨σX, hX, hA₃, hc0, hgi', hv⟩
      · exact absurd ((ite_ne _ _ _).1 h1).1 (by rw [hv0]; exact fun h => h rfl)
      · have hRs : t.step σ' = R.step σX := by
          rw [hpath σ' hgi' hv, hX]; simp only [Option.bind_some, if_pos hc0]
        cases hR' with
        | ret hs =>
          obtain ⟨τR, xR, _, pR⟩ := comp_ok L R 2 σX _ _ hRw (hA₃.set (g := L.cv 1) (by omega) _) (hRs ▸ hs)
          exact ⟨τR, xR, 0, Nat.le_refl _, Inv.set (.inr ⟨pR.2.2, pR.2.1, pR.1⟩) hw 0⟩
        | @call n _ σ₁ _ _ hs hn =>
          obtain ⟨τR, xR, _, pR⟩ := comp_ok L R 2 σX _ _ hRw (hA₃.set (g := L.cv 1) (by omega) _) (hRs ▸ hs)
          refine ⟨τR, xR, n, by omega, Inv.set (.inl ⟨?_, σ₁, hn, pR.1⟩) hw 0⟩
          rw [pR.2]; show BEnv.set _ _ _ _ ≠ 0; rw [hfl _ _ _ hw]; exact hf₃
  exact ⟨τ₄, .seq (.seq .assign xl) x₄, m'', by omega, hI₄.set hg0 0⟩

/-! ## The fast loops of `fastOf` keep the invariant -/

theorem leaves_wf (L : Lay) : ∀ (S : Tree), S.wf L → ∀ l ∈ S.leaves, l.length ≤ L.K ∧ ∀ p ∈ l, p.1 < L.M ∧ p.2.vlt L.M
  | .call as, hw, l, hl => by simp only [Tree.leaves, List.mem_singleton] at hl; subst hl; exact hw
  | .ite _ a b, hw, l, hl => by
    simp only [Tree.leaves, List.mem_append] at hl
    exact hl.elim (leaves_wf L a hw.2.1 l) (leaves_wf L b hw.2.2 l)
  | .let_ _ _ k, hw, l, hl => leaves_wf L k hw.2.2 l hl
  | .load _ _ _ k, hw, l, hl => leaves_wf L k hw.2.2 l hl
  | .cload _ _ _ _ _ k, hw, l, hl => leaves_wf L k hw.2.2.2.2 l hl
  | .store _ _ _ k, hw, l, hl => leaves_wf L k hw.2.2 l hl
  | .sub _ k, hw, l, hl => leaves_wf L k hw.2 l hl
  | .ret _, _, l, hl => nomatch hl

theorem pairs_wf (L : Lay) : ∀ (S : Tree), S.wf L → ∀ p ∈ S.pairs, p.1 < L.M
  | .call as, hw, p, hp => (hw.2 p hp).1
  | .ite _ a b, hw, p, hp => by
    simp only [Tree.pairs, List.mem_append] at hp
    exact hp.elim (pairs_wf L a hw.2.1 p) (pairs_wf L b hw.2.2 p)
  | .let_ _ _ k, hw, p, hp => pairs_wf L k hw.2.2 p hp
  | .load _ _ _ k, hw, p, hp => pairs_wf L k hw.2.2 p hp
  | .cload _ _ _ _ _ k, hw, p, hp => pairs_wf L k hw.2.2.2.2 p hp
  | .store _ _ _ k, hw, p, hp => pairs_wf L k hw.2.2 p hp
  | .sub _ k, hw, p, hp => pairs_wf L k hw.2 p hp
  | .ret _, _, p, hp => nomatch hp

theorem cpairs_mem : ∀ {as : List (Nat × BExp)} {p : Nat × BitVec 64}, p ∈ cpairs as → (p.1, .const p.2) ∈ as
  | (v, .const c) :: as, p, h => by
    simp only [cpairs, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (cpairs_mem h)
  | (v, .var _) :: as, p, h | (v, .bin _ _ _) :: as, p, h | (v, .ite _ _ _) :: as, p, h =>
    List.mem_cons_of_mem _ (cpairs_mem h)

theorem kOf_mem {S : Tree} {W : List Nat} {p : Nat × BitVec 64} (h : p ∈ kOf S W) :
    kOK S p = true ∧ p.1 ∉ W ∧ (p.1, .const p.2) ∈ S.pairs := by
  simp only [kOf, List.mem_filter, List.mem_eraseDups, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.2.1, (fun e => by rw [List.contains_iff_mem.2 e] at h; exact nomatch h.2.2), cpairs_mem h.1⟩

theorem kOK_lets {S : Tree} {p : Nat × BitVec 64} (h : kOK S p = true) : p.1 ∉ S.lets := fun e => by
  simp only [kOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [List.contains_iff_mem.2 e] at h; exact nomatch h.2

theorem conj_vs : ∀ {cs : List BExp} {c : BExp}, c ∈ cs → ∀ x ∈ c.vs, x ∈ (conj cs).vs
  | [c'], c, hc, x, hx => by simp only [List.mem_singleton] at hc; subst hc; exact hx
  | c' :: c'' :: cs, c, hc, x, hx => by
    simp only [conj, BExp.vs, List.mem_append]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact .inl (.inl hx)
    · exact .inl (.inr (conj_vs hc x hx))

theorem condE_vs (p : BExp × Bool) : (condE p).vs = p.1.vs := by
  obtain ⟨c, b⟩ := p; cases b <;> simp [condE, eqz, BExp.vs]

theorem pre_calls : ∀ xs : List Pre, (Pre.app xs (.call [])).calls = true
  | [] => rfl
  | .let_ _ _ :: xs | .load _ _ _ :: xs | .cload _ _ _ _ _ :: xs => pre_calls xs

theorem pre_wv : ∀ xs : List Pre, (Pre.app xs (.call [])).wv = xs.map Pre.tgt
  | [] => rfl
  | .let_ v _ :: xs | .load v _ _ :: xs | .cload v _ _ _ _ :: xs => by
    simp only [Pre.app, Tree.wv, List.map_cons, Pre.tgt, pre_wv xs]

theorem pre_wf (L : Lay) (k : Tree) : ∀ xs : List Pre, (Pre.app xs k).wf L → (Pre.app xs (.call [])).wf L ∧ k.wf L
  | [], h => ⟨⟨Nat.zero_le _, fun _ h => nomatch h⟩, h⟩
  | .let_ _ _ :: xs, h => ⟨⟨h.1, h.2.1, (pre_wf L k xs h.2.2).1⟩, (pre_wf L k xs h.2.2).2⟩
  | .load _ _ _ :: xs, h => ⟨⟨h.1, h.2.1, (pre_wf L k xs h.2.2).1⟩, (pre_wf L k xs h.2.2).2⟩
  | .cload _ _ _ _ _ :: xs, h =>
    ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, (pre_wf L k xs h.2.2.2.2).1⟩, (pre_wf L k xs h.2.2.2.2).2⟩

theorem common_wf (L : Lay) (S : Tree) (hw : S.wf L) : (Tree.call (common S)).wf L := by
  unfold common
  split
  · exact ⟨Nat.zero_le _, fun _ h => nomatch h⟩
  · rename_i as ls hls
    dsimp only
    split
    · have := leaves_wf L S hw as (by rw [hls]; exact List.mem_cons_self)
      exact ⟨Nat.le_trans (List.length_filter_le _ _) this.1, fun p hp => this.2 p (List.mem_filter.1 hp).1⟩
    · exact ⟨Nat.zero_le _, fun _ h => nomatch h⟩

/-- the conditions of `splitG` -/
theorem splitG_K (W : List Nat) (K : List (Nat × BitVec 64)) (cs : List (BExp × Bool)) (env : BEnv)
    (h1 : ∀ c ∈ (splitG W K cs).1, c.denote env ≠ 0) : ∀ p ∈ K, env p.1 = p.2 := fun p hp => by
  have := h1 _ (List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩))
  simpa [BExp.denote, Op.eval] using this

theorem splitG_ok (W : List Nat) (K : List (Nat × BitVec 64)) (cs : List (BExp × Bool)) (env : BEnv)
    (h1 : ∀ c ∈ (splitG W K cs).1, c.denote env ≠ 0) (h2 : ∀ c ∈ (splitG W K cs).2, c.denote env ≠ 0) :
    ∀ p ∈ cs, (condE p).denote env ≠ 0 := fun p hp => by
  by_cases hi : ((condE p).vs.all fun x => !W.contains x) = true
  · exact h1 _ (List.mem_append_right _ (List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, hi⟩, rfl⟩))
  · exact h2 _ (List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simpa using hi⟩, rfl⟩)

/-- the invariant part survives a step that writes only `W` -/
theorem splitG_keep (W : List Nat) (K : List (Nat × BitVec 64)) (cs : List (BExp × Bool)) (env env' : BEnv)
    (hK : ∀ p ∈ K, env' p.1 = env p.1) (hW : ∀ x, x ∉ W → env' x = env x) :
    (∀ c ∈ (splitG W K cs).1, c.denote env ≠ 0) → ∀ c ∈ (splitG W K cs).1, c.denote env' ≠ 0 := by
  intro h c hc
  rcases List.mem_append.1 hc with hc' | hc'
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc'
    have := h _ hc
    simp only [BExp.denote] at this ⊢; rw [hK p hp]; exact this
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc'
    have hi := (List.mem_filter.1 hp).2
    rw [denote_vs (condE p) fun x hx => hW x fun e => by
      have := List.all_eq_true.1 hi x hx; rw [List.contains_iff_mem.2 e] at this; exact nomatch this]
    exact h _ hc

theorem splitG_vlt {M : Nat} (W : List Nat) (K : List (Nat × BitVec 64)) (cs : List (BExp × Bool))
    (hK : ∀ p ∈ K, p.1 < M) (hc : ∀ p ∈ cs, p.1.vlt M) :
    (∀ c ∈ (splitG W K cs).1, c.vlt M) ∧ ∀ c ∈ (splitG W K cs).2, c.vlt M := by
  refine ⟨fun c h => ?_, fun c h => ?_⟩
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h; exact ⟨hK p hp, trivial⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h; exact condE_vlt (hc p (List.mem_filter.1 hp).1)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h; exact condE_vlt (hc p (List.mem_filter.1 hp).1)

theorem comp_call (L : Lay) (S : Tree) (d : Nat) (hw : S.wf L) (σ σ₁ τ : BState) (hA : Agree L.M σ τ)
    (hs : S.step σ = some (.call σ₁)) :
    ∃ τ₁, BExec (comp L S d) τ τ₁ ∧ Agree L.M σ₁ τ₁ ∧ τ₁.env L.fl = τ.env L.fl ∧
      ∀ x, L.M + 2 + L.K ≤ x → x < L.cv d → τ₁.env x = τ.env x := by
  obtain ⟨τ₁, x, f, p⟩ := comp_ok L S d σ τ _ hw hA hs
  exact ⟨τ₁, x, p.1, p.2, f⟩

theorem fastExitOf_ok (L : Lay) (t : Tree) (hw : t.wf L) {cs : List (BExp × Bool)} {xs : List Pre} {c : BExp}
    {a b : Tree} (hp : (cs, Pre.app xs (.ite c a b)) ∈ peel t) (S2 R : Tree) (c' : BExp)
    (hsel : ∀ σX : BState, (Tree.ite c a b).step σX = if c'.denote σX.env = 0 then R.step σX else S2.step σX)
    (hS2c : S2.calls = true) (hS2w : S2.wf L) (hRw : R.wf L) (hvc : c'.vlt L.M)
    (hG : ((splitG (xs.map Pre.tgt ++ (S2.strip ((kOf S2 (xs.map Pre.tgt)).map (·.1))).wv) (kOf S2 (xs.map Pre.tgt))
      cs).2.isEmpty || !(conj (splitG (xs.map Pre.tgt ++ (S2.strip ((kOf S2 (xs.map Pre.tgt)).map (·.1))).wv)
        (kOf S2 (xs.map Pre.tgt)) cs).2).vs.all (fun x => !(xs.map Pre.tgt).contains x)) = false) :
    FastOK L t (whenS (L.cv 0) (conj (.var L.fl :: (splitG (xs.map Pre.tgt ++
        (S2.strip ((kOf S2 (xs.map Pre.tgt)).map (·.1))).wv) (kOf S2 (xs.map Pre.tgt)) cs).1))
      (.seq (.seq (.assign (L.cv 0 + 1) (.const 1)) (.loop (.ite (conj (splitG (xs.map Pre.tgt ++
          (S2.strip ((kOf S2 (xs.map Pre.tgt)).map (·.1))).wv) (kOf S2 (xs.map Pre.tgt)) cs).2) (.var (L.cv 0 + 1))
          (.const 0))
          (.seq (comp L (Pre.app xs (.call [])) 1) (.seq (.assign (L.cv 0 + 1) c') (whenS (L.cv 1) (.var (L.cv 0 + 1))
            (comp L (S2.strip ((kOf S2 (xs.map Pre.tgt)).map (·.1))) 2))))))
        (whenS (L.cv 1) (.ite (conj (splitG (xs.map Pre.tgt ++ (S2.strip ((kOf S2 (xs.map Pre.tgt)).map (·.1))).wv)
          (kOf S2 (xs.map Pre.tgt)) cs).2) (eqz c') (.const 0)) (comp L R 2)))) := by
  obtain ⟨hSw, hcs⟩ := peel_wf L t hp hw
  generalize hW0 : xs.map Pre.tgt = W0 at hG ⊢
  generalize hK : kOf S2 W0 = K at hG ⊢
  generalize hS' : S2.strip (K.map (·.1)) = S2' at hG ⊢
  have hKm : ∀ p ∈ K, kOK S2 p = true ∧ p.1 ∉ W0 ∧ (p.1, .const p.2) ∈ S2.pairs := fun p h => by
    rw [← hK] at h; exact kOf_mem h
  have hS'c : S2'.calls = true := hS' ▸ strip_calls _ S2 hS2c
  have hS'w : S2'.wf L := hS' ▸ strip_wf L _ S2 hS2w
  have hstrip : ∀ σ : BState, (∀ p ∈ K, σ.env p.1 = p.2) → S2'.step σ = S2.step σ := fun σ h =>
    hS' ▸ strip_step K S2 (fun p hp => (hKm p hp).1) σ h
  have hKw : ∀ p ∈ K, p.1 ∉ S2'.wv := fun p hp => hS' ▸ strip_wv _ S2 hS2c
    (.inr ⟨List.mem_map.2 ⟨p, hp, rfl⟩, kOK_lets (hKm p hp).1⟩)
  have hXw := (pre_wf L _ xs hSw).1
  have hXwv : (Pre.app xs (.call [])).wv = W0 := by rw [pre_wv, hW0]
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.all_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨-, hGv⟩ := hG
  obtain ⟨hvi, hvv⟩ := splitG_vlt (M := L.M) (W0 ++ S2'.wv) K cs
    (fun p hp => pairs_wf L S2 hS2w _ (hKm p hp).2.2) hcs
  have hX0 : ∀ σ σX, (Pre.app xs (.call [])).step σ = some (.call σX) → ∀ x, x ∉ W0 → σX.env x = σ.env x :=
    fun σ σX hX x hx => by
      obtain ⟨σ', e, hk⟩ := calls_step _ (pre_calls xs) σ _ hX
      cases e; exact hk x (hXwv ▸ hx)
  refine fastExit_ok L t _ _ (Pre.app xs (.call [])) c' S2 R _ hvi hvv hvc (pre_calls xs) hXw hRw
    (fun σ h1 h2 => ?_) (fun σ σX hX c hc => ?_) (fun σ σX o h1 hX hs => ?_) (fun σ σX σ₁ τ h1 hX hs hA => ?_)
  · rw [peel_step t hp σ (splitG_ok _ _ _ _ h1 h2), pre_step]
    congr 1; funext o
    cases o with
    | call σX => exact hsel σX
    | ret _ _ => rfl
  · exact denote_vs c fun x hx => hX0 σ σX hX x fun e => by
      have := hGv x (conj_vs hc x hx); rw [List.contains_iff_mem.2 e] at this; exact nomatch this
  · have hKX : ∀ p ∈ K, σX.env p.1 = p.2 := fun p hp => by
      rw [hX0 σ σX hX _ (hKm p hp).2.1]; exact splitG_K _ _ _ _ h1 p hp
    obtain ⟨σ₁, rfl, hkeep⟩ := calls_step S2' hS'c σX o ((hstrip σX hKX).trans hs)
    refine ⟨σ₁, rfl, splitG_keep _ K cs σ.env σ₁.env (fun p hp => ?_) (fun x hx => ?_) h1⟩
    · rw [hkeep _ (hKw p hp), hX0 σ σX hX _ (hKm p hp).2.1]
    · simp only [List.mem_append, not_or] at hx
      rw [hkeep x hx.2, hX0 σ σX hX x hx.1]
  · have hKX : ∀ p ∈ K, σX.env p.1 = p.2 := fun p hp => by
      rw [hX0 σ σX hX _ (hKm p hp).2.1]; exact splitG_K _ _ _ _ h1 p hp
    obtain ⟨τ₁, x, a', f, fr⟩ := comp_call L S2' 2 hS'w σX σ₁ τ hA ((hstrip σX hKX).trans hs)
    exact ⟨τ₁, x, a', f, fr _ (by simp only [Lay.cv]; omega) (by simp only [Lay.cv]; omega)⟩

theorem fastOf_ok (L : Lay) (t : Tree) (hw : t.wf L) {cs : List (BExp × Bool)} {S : Tree} (hp : (cs, S) ∈ peel t)
    {F : BStmt} (hF : fastOf L cs S = some F) : FastOK L t F := by
  obtain ⟨hSw, hcs⟩ := peel_wf L t hp hw
  unfold fastOf at hF
  split at hF
  · rename_i hc
    dsimp only at hF
    split at hF
    · exact nomatch hF
    · cases hF
      generalize hK : kOf S [] = K
      generalize hS' : S.strip (K.map (·.1)) = S'
      have hKm : ∀ p ∈ K, kOK S p = true ∧ (p.1, .const p.2) ∈ S.pairs := fun p h => by
        rw [← hK] at h; exact ⟨(kOf_mem h).1, (kOf_mem h).2.2⟩
      have hS'c : S'.calls = true := hS' ▸ strip_calls _ S hc
      have hS'w : S'.wf L := hS' ▸ strip_wf L _ S hSw
      have hstrip : ∀ σ : BState, (∀ p ∈ K, σ.env p.1 = p.2) → S'.step σ = S.step σ := fun σ h =>
        hS' ▸ strip_step K S (fun p hp => (hKm p hp).1) σ h
      have hKw : ∀ p ∈ K, p.1 ∉ S'.wv := fun p hp => hS' ▸ strip_wv _ S hc
        (.inr ⟨List.mem_map.2 ⟨p, hp, rfl⟩, kOK_lets (hKm p hp).1⟩)
      obtain ⟨hvi, hvv⟩ := splitG_vlt (M := L.M) S'.wv K cs (fun p hp => pairs_wf L S hSw _ (hKm p hp).2) hcs
      refine fastLoop_ok L t _ _ _ S hvi hvv (fun σ h1 h2 => peel_step t hp σ (splitG_ok _ _ _ _ h1 h2))
        (fun σ o h1 hs => ?_) (fun σ σ₁ τ h1 hs hA => ?_) (L.cv 0) (by simp only [Lay.cv]; omega)
      · have hs' : S'.step σ = some o := (hstrip σ (splitG_K _ _ _ _ h1)).trans hs
        obtain ⟨σ₁, rfl, hkeep⟩ := calls_step S' hS'c σ o hs'
        exact ⟨σ₁, rfl, splitG_keep S'.wv K cs σ.env σ₁.env (fun p hp => hkeep _ (hKw p hp)) hkeep h1⟩
      · have hs' : S'.step σ = some (.call σ₁) := (hstrip σ (splitG_K _ _ _ _ h1)).trans hs
        split
        · obtain ⟨τ₁, x, a, f, _⟩ := comp_call L S' 1 hS'w σ σ₁ τ hA hs'
          exact ⟨τ₁, x, a, f⟩
        · rename_i hne
          rcases common_ok S' with ⟨hl, hv⟩ | he
          · obtain ⟨σ₂, h2, h3⟩ := hoist_step (common S') S' hS'c hl hv σ σ₁ hs'
            obtain ⟨τ₂, x₂, a₂, f₂, _⟩ := comp_call L _ 1 (strip_wf L _ S' hS'w) σ σ₂ τ hA h2
            obtain ⟨τ₃, x₃, a₃, f₃, _⟩ := comp_call L _ 1 (common_wf L S' hS'w) σ₂ σ₁ τ₂ a₂ h3
            exact ⟨τ₃, .seq x₂ x₃, a₃, f₃.trans f₂⟩
          · rw [he] at hne; exact absurd rfl hne
  · cases hsp : splitPre S with
    | none => rw [hsp] at hF; exact nomatch hF
    | some q =>
      obtain ⟨xs, c, a, b⟩ := q
      rw [hsp] at hF
      have hSe := splitPre_eq hsp
      subst hSe
      have hiw : (Tree.ite c a b).wf L := (pre_wf L _ xs hSw).2
      cases xs with
      | nil => exact nomatch hF
      | cons x xs' =>
        dsimp only at hF
        by_cases ha : a.calls = true
        · simp only [if_pos ha] at hF
          split at hF
          · exact nomatch hF
          · cases hF
            exact fastExitOf_ok L t hw hp a b c (fun σX => by simp only [Tree.step]) ha hiw.2.1 hiw.2.2
              hiw.1 (Bool.eq_false_iff.2 (by assumption))
        · by_cases hb : b.calls = true
          · simp only [if_neg ha, if_pos hb] at hF
            split at hF
            · exact nomatch hF
            · cases hF
              refine fastExitOf_ok L t hw hp b a (eqz c) (fun σX => ?_) hb hiw.2.2 hiw.2.1 ⟨hiw.1, trivial⟩
                (Bool.eq_false_iff.2 (by assumption))
              simp only [Tree.step]
              by_cases h0 : c.denote σX.env = 0
              · rw [if_pos h0, if_neg ((eqz_ne _ _).2 h0)]
              · have : (eqz c).denote σX.env = 0 := Classical.byContradiction fun h => h0 ((eqz_ne _ _).1 h)
                rw [if_neg h0, if_pos this]
          · simp only [if_neg ha, if_neg hb] at hF; exact nomatch hF

/-! ## The program -/

theorem fasts_ok (L : Lay) (t : Tree) (hw : t.wf L) : ∀ F ∈ fasts L t, FastOK L t F := by
  intro F hF
  simp only [fasts, List.mem_filter, List.mem_filterMap] at hF
  obtain ⟨⟨⟨cs, S⟩, hp, hF⟩, -⟩ := hF
  exact fastOf_ok L t hw hp hF

theorem seqs_ok (L : Lay) (t : Tree) : ∀ (fs : List BStmt), fs ≠ [] → (∀ F ∈ fs, FastOK L t F) → FastOK L t (seqs fs)
  | [p], _, h => h p (List.mem_singleton_self _)
  | p :: q :: ps, _, h => by
    intro r σf m τ hI
    obtain ⟨m₁, τ₁, h1, x₁, hI₁⟩ := h p List.mem_cons_self r σf m τ hI
    obtain ⟨m₂, τ₂, h2, x₂, hI₂⟩ := seqs_ok L t (q :: ps) (List.cons_ne_nil _ _)
      (fun F hF => h F (List.mem_cons_of_mem _ hF)) r σf m₁ τ₁ hI₁
    exact ⟨m₂, τ₂, by omega, .seq x₁ x₂, hI₂⟩

/-- one plain step, from a state that has not returned -/
theorem plain_ok (L : Lay) (t : Tree) (hw : t.wf L) {r : BitVec 64} {σf : BState} {m : Nat} {τ : BState}
    (hI : Inv L t r σf m τ) (hf : τ.env L.fl ≠ 0) :
    ∃ m' τ', BExec (comp L t 0) τ τ' ∧ Inv L t r σf m' τ' ∧ (τ'.env L.fl ≠ 0 → m' < m) := by
  obtain ⟨_, σ, hR, hA⟩ := hI.resolve_right fun h => hf h.1
  cases hR with
  | ret hs =>
    obtain ⟨τ', x, _, p⟩ := comp_ok L t 0 σ τ _ hw hA hs
    exact ⟨0, τ', x, .inr ⟨p.2.2, p.2.1, p.1⟩, fun h => absurd p.2.2 h⟩
  | @call n _ σ₁ _ _ hs hn =>
    obtain ⟨τ', x, _, p⟩ := comp_ok L t 0 σ τ _ hw hA hs
    exact ⟨n, τ', x, .inl ⟨by rw [p.2]; exact hf, σ₁, hn, p.1⟩, fun _ => by omega⟩

theorem iter_ok (L : Lay) (t : Tree) (hw : t.wf L) {r : BitVec 64} {σf : BState} {m : Nat} {τ : BState}
    (hI : Inv L t r σf m τ) (hf : τ.env L.fl ≠ 0) :
    ∃ m' τ', BExec (iter L t) τ τ' ∧ Inv L t r σf m' τ' ∧ (τ'.env L.fl ≠ 0 → m' < m) := by
  unfold iter
  cases hfs : fasts L t with
  | nil => exact plain_ok L t hw hI hf
  | cons F fs' =>
    dsimp only
    split
    case isFalse => exact plain_ok L t hw hI hf
    obtain ⟨m₁, τ₁, h1, x₁, hI₁⟩ := seqs_ok L t (F :: fs') (List.cons_ne_nil _ _)
      (fun G hG => fasts_ok L t hw G (by rw [hfs]; exact hG)) r σf m τ hI
    have hg : L.M + 2 ≤ L.cv 0 := by simp only [Lay.cv]; omega
    have hgf : L.fl ≠ L.cv 0 := by simp only [Lay.fl, Lay.cv]; omega
    obtain ⟨τ', x', m', hI', hlt⟩ := whenS_ok (L.cv 0) (.var L.fl) (comp L t 0) τ₁
      (fun τ' => ∃ m', Inv L t r σf m' τ' ∧ (τ'.env L.fl ≠ 0 → m' < m))
      (fun h0 => by
        have e : (τ₁.env.set (L.cv 0) 0) L.fl = 0 := by rw [set_ne _ _ hgf]; exact h0
        exact ⟨m₁, hI₁.set hg 0, fun h => absurd e h⟩)
      (fun h1 => by
        have e : (τ₁.env.set (L.cv 0) ((BExp.var L.fl).denote τ₁.env)) L.fl ≠ 0 := by
          rw [set_ne _ _ hgf]; exact h1
        obtain ⟨m', τ', x, hI', hlt⟩ := plain_ok L t hw (hI₁.set hg ((BExp.var L.fl).denote τ₁.env)) e
        refine ⟨τ', x, m', hI'.set hg 0, fun h => ?_⟩
        have e' : τ'.env L.fl ≠ 0 := fun h' => h (by show BEnv.set _ _ _ _ = 0; rw [set_ne _ _ hgf]; exact h')
        have := hlt e'
        omega)
    exact ⟨m', τ', .seq x₁ x', hI', hlt⟩

/-- the whole function: result in variable `out` -/
def prog (L : Lay) (t : Tree) (out : Nat) : BStmt :=
  .seq (.assign L.fl (.const 1)) (.seq (.loop (.var L.fl) (iter L t)) (.assign out (.var L.res)))

theorem loop_ok (L : Lay) {t : Tree} (hw : t.wf L) {σ σ' : BState} {r : BitVec 64} (h : t.Runs σ r σ') :
    ∀ τ, Agree L.M σ τ → τ.env L.fl ≠ 0 →
    ∃ τ', BExec (.loop (.var L.fl) (iter L t)) τ τ' ∧ Agree L.M σ' τ' ∧ τ'.env L.res = r := by
  obtain ⟨n, hn⟩ := h.toN
  have key : ∀ m τ, Inv L t r σ' m τ →
      ∃ τ', BExec (.loop (.var L.fl) (iter L t)) τ τ' ∧ Agree L.M σ' τ' ∧ τ'.env L.res = r := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro τ hI
      by_cases hf : τ.env L.fl = 0
      · obtain ⟨_, h2, h3⟩ := hI.resolve_left fun h => h.1 hf
        exact ⟨τ, .loopF hf, h3, h2⟩
      · obtain ⟨m', τ', x, hI', hlt⟩ := iter_ok L t hw hI hf
        by_cases hf' : τ'.env L.fl = 0
        · obtain ⟨_, h2, h3⟩ := hI'.resolve_left fun h => h.1 hf'
          exact ⟨τ', .loopT hf x (.loopF hf'), h3, h2⟩
        · obtain ⟨τ'', x', h3⟩ := ih m' (hlt hf') τ' hI'
          exact ⟨τ'', .loopT hf x x', h3⟩
  exact fun τ hA hf => key n τ (.inl ⟨hf, σ, hn, hA⟩)

/-- **Once and for all**: if the tree iterates from `σ` to the result `r`, the compiled program run from any
state with the same user variables and heap ends with `r` in `out`, the same heap, and the other user
variables as the tree left them. -/
theorem prog_ok (L : Lay) {t : Tree} (hw : t.wf L) {σ σ' : BState} {r : BitVec 64} (h : t.Runs σ r σ')
    (out : Nat) (τ : BState) (hA : Agree L.M σ τ) :
    ∃ τ', BExec (prog L t out) τ τ' ∧ τ'.env out = r ∧ τ'.heap = σ'.heap ∧
      ∀ v, v < L.M → v ≠ out → τ'.env v = σ'.env v := by
  obtain ⟨τ₁, hl, hA', hr⟩ := loop_ok L hw h ⟨τ.env.set L.fl 1, τ.heap⟩
    ⟨fun v hv => (set_ne _ _ (by simp only [Lay.fl]; omega)).trans (hA.1 v hv), hA.2⟩
    (by show BEnv.set _ _ _ _ ≠ 0; rw [set_eq]; decide)
  exact ⟨_, .seq .assign (.seq hl .assign), by simp [BEnv.set, BExp.denote, hr], hA'.2, fun v hv hne => by
    show BEnv.set _ _ _ v = _
    rw [set_ne _ _ hne]; exact hA'.1 v hv⟩

/-- `prog_ok` for a read-only tree started in the very state `σ` -/
theorem prog_ok_ro (L : Lay) {t : Tree} (hw : t.wf L) (hr : t.ro = true) {σ : BState} {r : BitVec 64}
    (h : ∃ σ', t.Runs σ r σ') (out : Nat) :
    ∃ τ', BExec (prog L t out) σ τ' ∧ τ'.env out = r ∧ τ'.heap = σ.heap := by
  obtain ⟨σ', h⟩ := h
  obtain ⟨τ', h1, h2, h3, _⟩ := prog_ok L hw h out σ ⟨fun _ _ => rfl, rfl⟩
  exact ⟨τ', h1, h2, h3.trans (h.heap_ro hr)⟩

/-- `prog_ok` with extra result variables (read-only tree, started in the very state `σ`) -/
theorem prog_okQ (L : Lay) {t : Tree} (hw : t.wf L) (hr : t.ro = true) {σ : BState} {r : BitVec 64}
    {rs : List (Nat × BitVec 64)} (h : ∃ σ', t.Runs σ r σ' ∧ ∀ p ∈ rs, σ'.env p.1 = p.2) (out : Nat)
    (hlt : ∀ p ∈ rs, p.1 < L.M ∧ p.1 ≠ out) :
    ∃ τ', BExec (prog L t out) σ τ' ∧ τ'.env out = r ∧ τ'.heap = σ.heap ∧ ∀ p ∈ rs, τ'.env p.1 = p.2 := by
  obtain ⟨σ', h, hq⟩ := h
  obtain ⟨τ', h1, h2, h3, h4⟩ := prog_ok L hw h out σ ⟨fun _ _ => rfl, rfl⟩
  exact ⟨τ', h1, h2, h3.trans (h.heap_ro hr), fun p hp => (h4 p.1 (hlt p hp).1 (hlt p hp).2).trans (hq p hp)⟩

end Proven.Frontx
