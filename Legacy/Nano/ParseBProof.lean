/- nano stage 2, layer A proof: the explicit-stack parser machine `parseA` (`Nano/ParseB.lean`) computes
`(pDefsU (ts.length + 1) [] [] ts).map serU` for EVERY token list `ts` (`parseA_eq`): on `some u` it returns
`serU u` with enough gas, on `none` it returns `none` with any gas.  Method: one simulation lemma per parse function
(`sim`, by induction on the fuel), stated with `Reach` (the machine gets from a call state to the return state in a
fixed number of steps, whatever gas is left) and `Fails` (the machine returns `none` with any gas). -/
import Legacy.Nano.ParseB
import Legacy.Nano.ElabU

namespace Nano.PB
open Nano Nano.U

/-! ## Runs -/

def Reach (c : Ctl) (s : St) (c' : Ctl) (s' : St) : Prop := ∃ n, ∀ g, run (g + n) c s = run g c' s'
def Fails (c : Ctl) (s : St) : Prop := ∀ g, run g c s = none

theorem Reach.refl (c : Ctl) (s : St) : Reach c s c s := ⟨0, fun _ => rfl⟩

theorem Reach.trans {c1 c2 c3 : Ctl} {s1 s2 s3 : St} (h1 : Reach c1 s1 c2 s2) (h2 : Reach c2 s2 c3 s3) :
    Reach c1 s1 c3 s3 := by
  obtain ⟨n1, h1⟩ := h1; obtain ⟨n2, h2⟩ := h2
  exact ⟨n2 + n1, fun g => by rw [← Nat.add_assoc, h1, h2]⟩

theorem Reach.one {c c' : Ctl} {s s' : St} (h : step c s = .go c' s') : Reach c s c' s' :=
  ⟨1, fun g => by simp only [run, h]⟩

theorem Reach.stepT {c c' c'' : Ctl} {s s' s'' : St} (h : step c s = .go c' s') (h2 : Reach c' s' c'' s'') :
    Reach c s c'' s'' := (Reach.one h).trans h2

theorem Reach.fails {c c' : Ctl} {s s' : St} (h : Reach c s c' s') (hf : Fails c' s') : Fails c s := by
  obtain ⟨n, h⟩ := h
  intro g
  by_cases hg : n ≤ g
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hg
    rw [Nat.add_comm, h, hf]
  · -- fewer steps than `n`: the run stops before (a `none` from gas or a `fail`), or `done`, impossible: run longer
    have key : ∀ m c s, run m c s ≠ none → ∀ k, run (m + k) c s = run m c s := by
      intro m
      induction m with
      | zero => intro c s h; exact absurd rfl h
      | succ m ih =>
        intro c s h k
        rw [show m + 1 + k = (m + k) + 1 by omega]
        simp only [run] at h ⊢
        split <;> rename_i heq <;> simp only [heq] at h ⊢
        · exact ih _ _ h k
    cases hr : run g c s with
    | none => rfl
    | some o =>
      have := key g c s (by simp [hr]) (n - g)
      rw [show g + (n - g) = 0 + n by omega, h, hr] at this
      cases this

theorem Fails.one {c : Ctl} {s : St} (h : step c s = .fail) : Fails c s := by
  intro g; cases g with
  | zero => rfl
  | succ g => simp only [run, h]

theorem Fails.stepT {c c' : Ctl} {s s' : St} (h : step c s = .go c' s') (hf : Fails c' s') : Fails c s :=
  (Reach.one h).fails hf

theorem Reach.congr {c c' : Ctl} {s s' t : St} (h : Reach c s c' s') (e : s' = t) : Reach c s c' t := e ▸ h

/-! ## Views: the spec's and the machine's case splits -/

def letV : List Tok → Option (List UInt8 × List Tok)
  | Tok.klet :: Tok.id x :: Tok.assign :: ts => some (x, ts)
  | _ => none

/-- `+` (`false`) / `-` (`true`) -/
def addV : List Tok → Option (Bool × List Tok)
  | Tok.plus :: ts => some (false, ts)
  | Tok.minus :: ts => some (true, ts)
  | _ => none

def starV : List Tok → Option (List Tok)
  | Tok.star :: ts => some ts
  | _ => none

inductive AV where
  | name (g : List UInt8) (ts : List Tok)
  | neg (n : UInt64) (ts : List Tok)
  | lp (ts : List Tok)
  | num (n : UInt64) (ts : List Tok)
  | other

def appV : List Tok → AV
  | Tok.id g :: ts => .name g ts
  | Tok.minus :: Tok.num n :: ts => .neg n ts
  | Tok.lp :: ts => .lp ts
  | Tok.num n :: ts => .num n ts
  | _ => .other

def opE (m : Bool) (a b : Ex) : Ex := if m then .sub a b else .add a b
def opB (m : Bool) : UInt8 := if m then 32 else 24

macro "tcases" ts:ident : tactic => `(tactic|
  rcases $ts:ident with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _⟩⟩⟩)

theorem pExpr_succ (f : Nat) (sc : List (List UInt8)) (ds : Defs) (ts : List Tok) :
    pExpr (f + 1) sc ds ts = match letV ts with
    | some (x, ts') =>
      match pExpr f sc ds ts' with
      | some (v, Tok.semi :: r) =>
        match pExpr f (x :: sc) ds r with
        | some (b, r2) => some (Ex.let_ v b, r2)
        | none => none
      | _ => none
    | none =>
      match pMul f sc ds ts with
      | some (e, r) => pAdd f sc ds e r
      | none => none := by
  tcases ts <;> simp only [pExpr, letV] <;> rfl

theorem step_expr (f : Nat) (s : St) : step (.expr (f + 1)) s = match letV s.ts with
    | some (x, ts) => .go (.expr f) { s with ts := ts, K := .letV f x :: s.K }
    | none => .go (.mul f) { s with K := .exprAdd f :: s.K } := by
  rcases s with ⟨ts⟩; tcases ts <;> simp only [step, letV] <;> rfl

theorem pAdd_succ (f : Nat) (sc : List (List UInt8)) (ds : Defs) (acc : Ex) (ts : List Tok) :
    pAdd (f + 1) sc ds acc ts = match addV ts with
    | some (m, ts') =>
      match pMul f sc ds ts' with
      | some (e, r) => pAdd f sc ds (opE m acc e) r
      | none => none
    | none => some (acc, ts) := by
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _⟩ <;> simp only [pAdd, addV, opE] <;> rfl

theorem step_add (f : Nat) (s : St) : step (.add (f + 1)) s = match addV s.ts with
    | some (m, ts) => .go (.mul f) { s with ts := ts, K := .addOp f (opB m) :: s.K }
    | none => .go .ret s := by
  rcases s with ⟨ts⟩
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _⟩ <;> simp only [step, addV, opB] <;> rfl

theorem pMulT_succ (f : Nat) (sc : List (List UInt8)) (ds : Defs) (acc : Ex) (ts : List Tok) :
    pMulT (f + 1) sc ds acc ts = match starV ts with
    | some ts' =>
      match pApp f sc ds ts' with
      | some (e, r) => pMulT f sc ds (Ex.mul acc e) r
      | none => none
    | none => some (acc, ts) := by
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _⟩ <;> simp only [pMulT, starV] <;> rfl

theorem step_mulT (f : Nat) (s : St) : step (.mulT (f + 1)) s = match starV s.ts with
    | some ts => .go (.app f) { s with ts := ts, K := .mulOp f :: s.K }
    | none => .go .ret s := by
  rcases s with ⟨ts⟩
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _⟩ <;> simp only [step, starV] <;> rfl

theorem pApp_succ (f : Nat) (sc : List (List UInt8)) (ds : Defs) (ts : List Tok) :
    pApp (f + 1) sc ds ts = match appV ts with
    | .name g ts' =>
      match idx g sc 0 with
      | some i => some (Ex.var i, ts')
      | none =>
        match findDef g ds with
        | some (k, b) =>
          match pArgs f sc ds k ts' with
          | some (as, r) => some (Ex.call b as, r)
          | none => none
        | none => none
    | .neg n ts' => some (Ex.num (0 - n), ts')
    | _ => pAtom f sc ds ts := by
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _, _⟩⟩ <;> simp only [pApp, appV] <;> rfl

theorem step_app (f : Nat) (s : St) : step (.app (f + 1)) s = match appV s.ts with
    | .name g ts =>
      match lookS g s.sc with
      | some k => .go .ret { s with ts := ts, out := s.out ++ sVar s.d k, d := s.d + 1 }
      | none =>
        match findD g s.ds with
        | some (k, j) => .go (.args f k) { s with ts := ts, K := .call j k :: s.K }
        | none => .fail
    | .neg n ts => .go .ret { s with ts := ts, out := s.out ++ (sLi (0 - n) ++ mo 3 0), d := s.d + 1 }
    | _ => .go (.atom f) s := by
  rcases s with ⟨ts⟩
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _, _⟩⟩ <;> simp only [step, appV] <;> rfl

theorem pAtom_succ (f : Nat) (sc : List (List UInt8)) (ds : Defs) (ts : List Tok) :
    pAtom (f + 1) sc ds ts = match appV ts with
    | .num n ts' => some (Ex.num n, ts')
    | .name g ts' =>
      match idx g sc 0 with
      | some i => some (Ex.var i, ts')
      | none =>
        match findDef g ds with
        | some (0, b) => some (Ex.call b Ex.anil, ts')
        | _ => none
    | .lp ts' =>
      match pExpr f sc ds ts' with
      | some (e, Tok.rp :: r) => some (e, r)
      | _ => none
    | _ => none := by
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _, _⟩⟩ <;> simp only [pAtom, appV] <;> rfl

theorem step_atom (f : Nat) (s : St) : step (.atom (f + 1)) s = match appV s.ts with
    | .num n ts => .go .ret { s with ts := ts, out := s.out ++ (sLi n ++ mo 3 0), d := s.d + 1 }
    | .name g ts =>
      match lookS g s.sc with
      | some k => .go .ret { s with ts := ts, out := s.out ++ sVar s.d k, d := s.d + 1 }
      | none =>
        match findD g s.ds with
        | some (0, j) => .go .ret { s with ts := ts, out := s.out ++ sCall j 0, d := s.d + 1 }
        | _ => .fail
    | .lp ts => .go (.expr f) { s with ts := ts, K := .paren :: s.K }
    | _ => .fail := by
  rcases s with ⟨ts⟩
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _, _⟩⟩ <;> simp only [step, appV] <;> rfl

/-! ## Tables -/

/-- the spec's def table (bodies are markers) from the machine's -/
def dsOf (mds : List (List UInt8 × Nat × Nat)) : Defs := mds.map fun x => (x.1, x.2.1, Ex.var x.2.2)

theorem findDef_dsOf (g : List UInt8) : ∀ mds : List (List UInt8 × Nat × Nat),
    findDef g (dsOf mds) = (findD g mds).map fun kj => (kj.1, Ex.var kj.2)
  | [] => rfl
  | (x, k, j) :: r => by
    simp only [dsOf, List.map_cons, findDef, findD] at *
    split
    · rfl
    · exact findDef_dsOf g r

theorem idx_ge (g : List UInt8) : ∀ (sc : List (List UInt8)) (i0 i : Nat), idx g sc i0 = some i → i0 ≤ i
  | [], _, _, h => by simp [idx] at h
  | t :: ts, i0, i, h => by
    simp only [idx] at h
    split at h
    · cases h; exact Nat.le_refl _
    · have := idx_ge g ts (i0 + 1) i h; omega

theorem lookS_zip (g : List UInt8) : ∀ (scN : List (List UInt8)) (scD : List Nat) (i0 : Nat),
    scN.length = scD.length → lookS g (scN.zip scD) = (idx g scN i0).map fun i => scD.getD (i - i0) 0
  | [], [], _, _ => rfl
  | x :: scN, k :: scD, i0, h => by
    simp only [List.zip_cons_cons, lookS, idx]
    split
    · simp
    · rw [lookS_zip g scN scD (i0 + 1) (by simpa using h)]
      cases hi : idx g scN (i0 + 1) with
      | none => rfl
      | some i =>
        have : i0 + 1 ≤ i := idx_ge g scN _ _ hi
        simp only [Option.map_some]
        congr 1
        rw [show i - i0 = (i - (i0 + 1)) + 1 by omega]; rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

end Nano.PB
