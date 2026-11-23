/- Bridge.Typed: the nano half of the typing lemma (task 3).

`Wf Sig Γ e s`: `e` is an EMITTED Expr (the type and instance arguments of every constant are exactly the ones
`emit` writes: `lit`, `binX`, `iteX`, `Prod.mk`, `Prod.casesOn`, `Nat.casesOn`, `List.nil`, prims, calls) of shape
`s` under binder shapes `Γ` (head = bvar 0).  `ev_shape` (subject reduction): an Ev value of a well-formed term
has the term's shape.  This is what makes the `Facts` of EvSkeleton satisfiable: Ev's own rules accept ANY type
and instance arguments (e.g. `litU` any instance `i`), for which no model fact can hold; under `Wf` the arguments
are the canonical ones, and every value has a known shape, so `enc v ∈ ⟦shTy s⟧` (the con-leche half) can be
stated.  Still open: `emit … = some (x, some s) → Wf …` (the emitter produces well-formed terms).

STATUS: proved, no sorry. -/
import Nano.Expr.Correct
import Lean

namespace Bridge.Typed
open ExprSpec ParSpec

/-- the `.bin` op table of `binX`: head and instance -/
def binHead (op : Nat) : String × X :=
  let (f, i, j) := match op with
    | 1 => ("HAdd.hAdd", "instHAdd", "instAddUInt64") | 2 => ("HSub.hSub", "instHSub", "instSubUInt64")
    | 3 => ("HMul.hMul", "instHMul", "instMulUInt64") | 4 => ("HAnd.hAnd", "instHAndOfAndOp", "instAndOpUInt64")
    | 5 => ("HOr.hOr", "instHOrOfOrOp", "instOrOpUInt64")
    | 6 => ("HShiftLeft.hShiftLeft", "instHShiftLeftOfShiftLeft", "instShiftLeftUInt64")
    | _ => ("HShiftRight.hShiftRight", "instHShiftRightOfShiftRight", "instShiftRightUInt64")
  (f, apps (.c i [0]) [U, .c j []])

theorem binX_eq (op : Nat) (a b : X) :
    binX op a b = apps (.c (binHead op).1 [0, 0, 0]) [U, U, U, (binHead op).2, a, b] := by
  unfold binX binHead
  rcases op with _ | _ | _ | _ | _ | _ | _ | op <;> rfl

/-- value shapes -/
inductive VSh : Sh → ExprSpec.V → Prop
  | uw (x : UInt64) : VSh .uw (.w x)
  | nt (k : Nat) : VSh .nt (.n k)
  | ls (l : List UInt8) : VSh .ls (.l l)
  | bf (b : List UInt64) : VSh .bf (.b b)
  | p {A B x y} : VSh A x → VSh B y → VSh (.p A B) (.p x y)

inductive Fa2 {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | nil : Fa2 r [] []
  | cons {a b as bs} : r a b → Fa2 r as bs → Fa2 r (a :: as) (b :: bs)

/-- names that are not program defs -/
def reserved : List String :=
  ["OfNat.ofNat", "ite", "Prod.mk", "Prod.casesOn", "Nat.casesOn", "List.nil", "HAdd.hAdd", "HSub.hSub", "HMul.hMul",
   "HAnd.hAnd", "HOr.hOr", "HShiftLeft.hShiftLeft", "HShiftRight.hShiftRight",
   "rd", "len", "len'", "put", "bnew", "bsize", "bget", "bset", "bpush"]

def binList : List String := ["HAdd.hAdd", "HSub.hSub", "HMul.hMul", "HAnd.hAnd", "HOr.hOr",
    "HShiftLeft.hShiftLeft", "HShiftRight.hShiftRight"]
def primList : List String := ["rd", "len", "len'", "put", "bnew", "bsize", "bget", "bset", "bpush"]

/-- the program's signatures: parameter shapes (input = `.ls`, fuel = `.nt`) and result -/
abbrev Sig := String → Option (List Sh × Sh)

/-- the `ite` condition and decidability instance `iteX` emits (cmp = 1: `==`, else `<`) -/
def condX (n : Bool) (cmp : Nat) (a b : X) : X × X :=
  let T := if n then X.c "Nat" [] else U
  if cmp = 1 then
    let q := apps (.c "BEq.beq" [0]) [T, apps (.c "instBEqOfDecidableEq" [0])
      [T, .c (if n then "instDecidableEqNat" else "instDecidableEqUInt64") []], a, b]
    (apps (.c "Eq" [1]) [.c "Bool" [], q, .c "Bool.true" []], apps (.c "instDecidableEqBool" []) [q, .c "Bool.true" []])
  else
    (apps (.c "LT.lt" [0]) [T, .c (if n then "instLTNat" else "instLTUInt64") [], a, b],
      apps (.c (if n then "Nat.decLt" else "UInt64.decLt") []) [a.dropHead, b.dropHead])

theorem iteX_eq (r : Sh) (n : Bool) (cmp : Nat) (a b t e : X) :
    iteX r n cmp a b t e = apps (.c "ite" [1]) [shTy r, (condX n cmp a b).1, (condX n cmp a b).2, t, e] := by
  unfold iteX condX; by_cases h : cmp = 1 <;> simp [h]

/- Every constructor has a VARIABLE term index and an equation for it (`cases` cannot decide string
literals, so inversion goes through the equation and `apps_inj`). -/
mutual
inductive Wf (sig : Sig) : List Sh → X → Sh → Prop
  | bv {Γ e i s} : e = .bv i → Γ[i]? = some s → Wf sig Γ e s
  | lt {Γ e v b s r} : e = .lt true (shTy s) v b → Wf sig Γ v s → Wf sig (s :: Γ) b r → Wf sig Γ e r
  | litU {Γ e k} : e = apps (.c "OfNat.ofNat" [0]) [U, .nat k, .app (.c "UInt64.instOfNat" []) (.nat k)] →
      Wf sig Γ e .uw
  | litN {Γ e k} : e = apps (.c "OfNat.ofNat" [0]) [.c "Nat" [], .nat k, .app (.c "instOfNatNat" []) (.nat k)] →
      Wf sig Γ e .nt
  | bin {Γ e op n i a b} : e = apps (.c n [0, 0, 0]) [U, U, U, i, a, b] → binHead op = (n, i) →
      n ∈ binList → 1 ≤ op → op ≤ 7 → Wf sig Γ a .uw → Wf sig Γ b .uw → Wf sig Γ e .uw
  | ite {Γ e r n cmp a b c d t el} : e = apps (.c "ite" [1]) [shTy r, c, d, t, el] → condX n cmp a b = (c, d) →
      (cmp = 1 ∨ cmp = 2) →
      Wf sig Γ a (if n then .nt else .uw) → Wf sig Γ b (if n then .nt else .uw) →
      Wf sig Γ t r → Wf sig Γ el r → Wf sig Γ e r
  | mk {Γ e a b A B} : e = apps (.c "Prod.mk" [0, 0]) [shTy A, shTy B, a, b] → Wf sig Γ a A → Wf sig Γ b B →
      Wf sig Γ e (.p A B)
  | cases {Γ e l r R v body} : e = apps (.c "Prod.casesOn" [1, 0, 0])
        [shTy l, shTy r, .lam (shTy (.p l r)) (shTy R), v, .lam (shTy l) (.lam (shTy r) body)] →
      Wf sig Γ v (.p l r) → Wf sig (r :: l :: Γ) body R → Wf sig Γ e R
  | natCases {Γ e R d z s} : e = apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy R), d, z, .lam (.c "Nat" []) s] →
      Wf sig Γ d .nt → Wf sig Γ z R → Wf sig (.nt :: Γ) s R → Wf sig Γ e R
  | nil {Γ e} : e = apps (.c "List.nil" [0]) [.c "UInt8" []] → Wf sig Γ e .ls
  | prim {Γ e p n ps r as} : e = apps (.c n []) as → primInfo p = (n, ps, r) → n ∈ primList → p ≠ 5 → p ≠ 0 →
      p ≤ 9 → WfL sig Γ as (ps.map psSh) → Wf sig Γ e r
  | bnew {Γ e} : e = apps (.c "bnew" []) [] → Wf sig Γ e .bf
  | call {Γ e n as ps r} : e = apps (.c n []) as → n ∉ reserved → sig n = some (ps, r) → WfL sig Γ as ps → Wf sig Γ e r
inductive WfL (sig : Sig) : List Sh → List X → List Sh → Prop
  | nil {Γ} : WfL sig Γ [] []
  | cons {Γ a as s ss} : Wf sig Γ a s → WfL sig Γ as ss → WfL sig Γ (a :: as) (s :: ss)
end

/-! ## apps is injective on constant heads -/

theorem spine_foldl : ∀ (as : List X) (f : X), spine (as.foldl X.app f) = ((spine f).1, (spine f).2 ++ as)
  | [], f => by simp
  | a :: as, f => by rw [List.foldl, spine_foldl as (.app f a)]; simp [spine]

theorem spine_apps (n : String) (ls : List Nat) (as : List X) : spine (apps (.c n ls) as) = (.c n ls, as) := by
  simp [apps, spine_foldl, spine]

theorem apps_inj {n n' : String} {ls ls' : List Nat} {as as' : List X}
    (h : apps (.c n ls) as = apps (.c n' ls') as') : n = n' ∧ ls = ls' ∧ as = as' := by
  have := congrArg spine h
  simp only [spine_apps, Prod.mk.injEq, X.c.injEq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

@[simp] theorem apps_eq_apps {n n' : String} {ls ls' : List Nat} {as as' : List X} :
    apps (.c n ls) as = apps (.c n' ls') as' ↔ n = n' ∧ ls = ls' ∧ as = as' :=
  ⟨apps_inj, fun ⟨h1, h2, h3⟩ => h1 ▸ h2 ▸ h3 ▸ rfl⟩

@[simp] theorem apps_ne_bv (n : String) (ls : List Nat) (as : List X) (i : Nat) : apps (.c n ls) as ≠ .bv i := by
  intro h; have := congrArg spine h; simp [spine_apps, spine] at this

@[simp] theorem apps_ne_lt (n : String) (ls : List Nat) (as : List X) (nd t v b) : apps (.c n ls) as ≠ .lt nd t v b := by
  intro h; have := congrArg spine h; simp [spine_apps, spine] at this

/-! ## program well-formedness -/

/-- the program's defs: each has a signature, its name is not reserved, its body after the parameter λs is
well formed under the reversed parameter shapes (Ev's `call` evaluates it in `vs.reverse`) -/
structure PWf (sig : Sig) (P : Prog) : Prop where
  defs : ∀ {n body}, P.lookup n = some body → ∃ ps r b, sig n = some (ps, r) ∧ strip ps.length body = some b ∧
    Wf sig ps.reverse b r
  sig_res : ∀ {n ps r}, sig n = some (ps, r) → n ∉ reserved
  sig_fun : ∀ {n ps r ps' r'}, sig n = some (ps, r) → sig n = some (ps', r') → ps = ps' ∧ r = r'

theorem primInfo_res {p : Nat} : (primInfo p).1 ∈ reserved := by
  unfold primInfo; split <;> simp [reserved]

theorem prim_res {n vs r} (h : ExprSpec.prim n vs = some r) : n ∈ reserved := by
  unfold ExprSpec.prim at h; split at h <;> cases h <;> simp [reserved]

theorem binHead_res (op : Nat) : (binHead op).1 ∈ reserved := by
  unfold binHead; rcases op with _ | _ | _ | _ | _ | _ | _ | op <;> simp [reserved]

theorem binV_res {n x y z} (h : binV n x y = some z) : n ∈ reserved := by
  unfold binV at h; split at h <;> cases h <;> simp [reserved]

/-! ## subject reduction -/

theorem fa2_get {Γ : List Sh} {env : List ExprSpec.V} (h : Fa2 VSh Γ env) :
    ∀ {i : Nat} {s v}, Γ[i]? = some s → env[i]? = some v → VSh s v := by
  induction h with
  | nil => intro i s v h; simp at h
  | cons ha _ ih =>
    intro i s v h1 h2
    cases i with
    | zero => simp at h1 h2; subst h1 h2; exact ha
    | succ i => exact ih (by simpa using h1) (by simpa using h2)

theorem fa2_len {α β} {r : α → β → Prop} {as bs} (h : Fa2 r as bs) : as.length = bs.length := by
  induction h <;> simp [*]

theorem fa2_append {α β} {r : α → β → Prop} {as bs cs ds} (h1 : Fa2 r as bs) (h2 : Fa2 r cs ds) :
    Fa2 r (as ++ cs) (bs ++ ds) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem fa2_reverse {α β} {r : α → β → Prop} {as bs} (h : Fa2 r as bs) : Fa2 r as.reverse bs.reverse := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => simpa using fa2_append ih (.cons h .nil)

theorem psSh_primInfo_res {p} : (primInfo p).2.2 = (primInfo p).2.2 := rfl

/-- the shape of a prim's result (the Lean meaning `prim` agrees with `primInfo`) -/
theorem prim_shape {p vs r} (hp0 : p ≠ 5) (hp1 : p ≠ 0) (hp2 : p ≤ 9)
    (hvs : Fa2 VSh ((primInfo p).2.1.map psSh) vs) (h : ExprSpec.prim (primInfo p).1 vs = some r) :
    VSh (primInfo p).2.2 r := by
  have : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · match hvs with | .cons (.ls _) .nil => simp [primInfo, ExprSpec.prim] at h ⊢; subst h; exact .nt _
  · match hvs with | .cons (.ls _) (.cons (.uw _) .nil) => simp [primInfo, ExprSpec.prim] at h ⊢; subst h; exact .uw _
  · match hvs with | .cons (.ls _) .nil => simp [primInfo, ExprSpec.prim] at h ⊢; subst h; exact .uw _
  · match hvs with | .cons (.ls _) (.cons (.uw _) .nil) => simp [primInfo, ExprSpec.prim] at h ⊢; subst h; exact .ls _
  · match hvs with | .cons (.bf _) .nil => simp [primInfo, ExprSpec.prim] at h ⊢; subst h; exact .uw _
  · match hvs with | .cons (.bf _) (.cons (.uw _) .nil) => simp [primInfo, ExprSpec.prim] at h ⊢; subst h; exact .uw _
  · match hvs with | .cons (.bf _) (.cons (.uw _) (.cons (.uw _) .nil)) => simp [primInfo, ExprSpec.prim] at h ⊢; subst h; exact .bf _
  · match hvs with | .cons (.bf _) (.cons (.uw _) .nil) => simp [primInfo, ExprSpec.prim] at h ⊢; subst h; exact .bf _

@[simp] theorem bv_ne_apps (n : String) (ls : List Nat) (as : List X) (i : Nat) : X.bv i ≠ apps (.c n ls) as :=
  fun h => apps_ne_bv n ls as i h.symm
@[simp] theorem lt_ne_apps (n : String) (ls : List Nat) (as : List X) (nd t v b) : X.lt nd t v b ≠ apps (.c n ls) as :=
  fun h => apps_ne_lt n ls as nd t v b h.symm

theorem nil_apps (ls : List Nat) (T : X) : X.app (.c "List.nil" ls) T = apps (.c "List.nil" ls) [T] := rfl

theorem binNames {op : Nat} : (binHead op).1 ∈ ["HAdd.hAdd", "HSub.hSub", "HMul.hMul", "HAnd.hAnd", "HOr.hOr",
    "HShiftLeft.hShiftLeft", "HShiftRight.hShiftRight"] := by
  unfold binHead; rcases op with _ | _ | _ | _ | _ | _ | _ | op <;> simp

theorem binV_names {n x y z} (h : binV n x y = some z) : n ∈ binList := by
  unfold binV at h; split at h <;> cases h <;> simp [binList]

theorem binList_primList {n : String} (h1 : n ∈ binList) (h2 : n ∈ primList) : False := by
  simp only [binList, List.mem_cons, List.not_mem_nil] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all [primList]

theorem binList_res {n : String} (h : n ∈ binList) : n ∈ reserved := by
  simp only [binList, List.mem_cons, List.not_mem_nil] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all [reserved]

theorem primList_res {n : String} (h : n ∈ primList) : n ∈ reserved := by
  simp only [primList, List.mem_cons, List.not_mem_nil] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all [reserved]

theorem primNames {p : Nat} : (primInfo p).1 ∈ ["len'", "rd", "len", "put", "bsize", "bget", "bset", "bpush"] := by
  unfold primInfo; split <;> simp

theorem prim_names {n vs r} (h : ExprSpec.prim n vs = some r) : n ∈ primList := by
  unfold ExprSpec.prim at h; split at h <;> cases h <;> simp [primList]

theorem wfL_len {sig Γ} : ∀ {as ss}, WfL sig Γ as ss → as.length = ss.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [wfL_len t]

theorem evL_len {P env} : ∀ {as vs}, EvL P env as vs → as.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [evL_len t]

open Lean Elab Tactic in
/-- split every `∧` hypothesis (core `MVarId.casesAnd`) -/
elab "cases_and" : tactic => liftMetaTactic1 fun g => g.casesAnd

/-- unify an `apps` equation: split, substitute -/
macro "unif" : tactic => `(tactic| ((try simp only [apps_eq_apps, List.cons.injEq, X.c.injEq, X.lt.injEq, X.bv.injEq,
  X.lam.injEq, and_true, true_and] at *); cases_and; (try subst_vars)))

/-- discharge a mismatched `Wf` rule -/
macro "kill" : tactic => `(tactic| (unif; first
  | exact (binList_primList (by assumption) (by assumption)).elim
  | exact ((by assumption : _ ∉ reserved) (binList_res (by assumption))).elim
  | exact ((by assumption : _ ∉ reserved) (primList_res (by assumption))).elim
  | simp_all [U, reserved, binList, primList]))

/-- **Subject reduction.**  An Ev value of a well-formed term has the term's shape (with the program's defs
well formed, `PWf`).  Proof: the recursor of the mutual `Ev`/`EvB`/`EvL` (the `EvB` motive is trivial). -/
theorem ev_shape {sig : Sig} {P : Prog} (hP : PWf sig P) {env e v} (h : Ev P env e v) :
    ∀ {Γ s}, Wf sig Γ e s → Fa2 VSh Γ env → VSh s v := by
  refine Ev.rec (motive_1 := fun env e v _ => ∀ {Γ s}, Wf sig Γ e s → Fa2 VSh Γ env → VSh s v)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun env as vs _ => ∀ {Γ ss}, WfL sig Γ as ss → Fa2 VSh Γ env → Fa2 VSh ss vs)
    ?bv ?lt ?litU ?litN ?bin ?iteT ?iteF ?mk ?cases ?natZ ?natS ?nil ?prim ?call
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    ?lnil ?lcons h
  case bv =>
    intro env i v hi Γ s hw he
    cases hw with
    | bv h1 h2 => cases h1; exact fa2_get he h2 hi
    | _ => kill
  case lt =>
    intro env nd t v b a r _ _ ihv ihb Γ s hw he
    cases hw with
    | lt h1 h2 h3 => unif; exact ihb h3 (.cons (ihv h2 he) he)
    | _ => kill
  case litU =>
    intro env ls k i Γ s hw he
    cases hw with
    | litU => exact .uw _
    | _ => kill
  case litN =>
    intro env ls k i Γ s hw he
    cases hw with
    | litN => exact .nt _
    | _ => kill
  case bin =>
    intro env n ls t1 t2 t3 i a b x y z hz _ _ _ _ Γ s hw he
    have hn := binV_names hz
    cases hw with
    | bin => exact .uw _
    | _ => kill
  case iteT =>
    intro env ls T c d t e r _ _ _ iht Γ s hw he
    cases hw with
    | ite h1 _ _ _ _ h5 _ => unif; exact iht h5 he
    | _ => kill
  case iteF =>
    intro env ls T c d t e r _ _ _ ihe Γ s hw he
    cases hw with
    | ite h1 _ _ _ _ _ h6 => unif; exact ihe h6 he
    | _ => kill
  case mk =>
    intro env ls A B a b x y _ _ iha ihb Γ s hw he
    cases hw with
    | mk h1 h2 h3 => unif; exact .p (iha h2 he) (ihb h3 he)
    | _ => kill
  case cases =>
    intro env ls A B M v T1 T2 body x y r _ _ ihv ihb Γ s hw he
    cases hw with
    | cases h1 h2 h3 =>
      unif
      have hp := ihv h2 he
      cases hp with
      | p hx hy => exact ihb h3 (.cons hy (.cons hx he))
    | _ => kill
  case natZ =>
    intro env ls M d z T s r _ _ _ ihz Γ s' hw he
    cases hw with
    | natCases h1 h2 h3 h4 => unif; exact ihz h3 he
    | _ => kill
  case natS =>
    intro env ls M d z T s k r _ _ _ ihs Γ s' hw he
    cases hw with
    | natCases h1 h2 h3 h4 => unif; exact ihs h4 (.cons (.nt _) he)
    | _ => kill
  case nil =>
    intro env ls T Γ s hw he
    rw [nil_apps] at hw
    cases hw with
    | nil => exact .ls _
    | _ => kill
  case prim =>
    intro env n as vs r hl hp ihl Γ s hw he
    have hn := prim_names hp
    cases hw with
    | prim h1 h2 _ h3 h4 h5 h6 =>
      unif
      have := prim_shape (p := _) h3 h4 h5 (by rw [h2]; exact ihl h6 he) (by rw [h2]; exact hp)
      rwa [h2] at this
    | bnew h1 => unif; cases hl; simp [ExprSpec.prim] at hp; subst hp; exact .bf _
    | _ => kill
  case call =>
    intro env n as vs body b r hl hlook hstrip _ ihl ihb Γ s hw he
    obtain ⟨ps, r', b', hs, hst, hwb⟩ := hP.defs hlook
    have hres := hP.sig_res hs
    cases hw with
    | call h1 _ h2 h3 =>
      unif
      obtain ⟨rfl, rfl⟩ := hP.sig_fun hs h2
      have hvs := ihl h3 he
      rw [← fa2_len hvs] at hstrip; rw [hstrip] at hst; cases hst
      exact ihb hwb (fa2_reverse hvs)
    | _ => kill
  case lnil =>
    intro env Γ ss hw he
    cases hw; exact .nil
  case lcons =>
    intro env a as v vs _ _ iha ihl Γ ss hw he
    cases hw with
    | cons h1 h2 => exact .cons (iha h1 he) (ihl h2 he)

end Bridge.Typed
