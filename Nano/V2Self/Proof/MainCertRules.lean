/- Nano/V2Self/Proof/MainCertRules: syntax-directed rules for per-def certificates in the cap-free world (certificate lead).
`Ev inp ms n env vs`: node `n` evaluates (value mode) to `vs`.  The rules build the Lean term of the source expression
(`if x == y then …`, `x + y`, `bpush l v`, …), so a def's body is checked against its Lean definition by unification.
`ev_auto` applies them along the node. -/
import Nano.V2Self.Proof.MainPure
namespace NanoMain
open ParSpec

def Ev (inp : List UInt8) (ms : List Fn) (n : Nd) (env vs : List W) : Prop := val (pev inp ms n env) = .ok vs
def EvL (inp : List UInt8) (ms : List Fn) (ns : List Nd) (env vs : List W) : Prop := pevL inp ms ns env = .ok vs

section
variable {inp : List UInt8} {ms : List Fn} {env : List W}

theorem ev_const (v : UInt64) : Ev inp ms (.const v) env [.w v] := rfl

theorem ev_loc {s w : Nat} {vs : List W} (h : s + w ≤ env.length) (e : (env.drop s).take w = vs) : Ev inp ms (.loc s w) env vs := by
  simp [Ev, pev, h, val, e]

theorem ev_bin {op : Nat} {a b : Nd} {x y z : UInt64} (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y])
    (ho : binop op x y = .ok z) : Ev inp ms (.bin op a b) env [.w z] := by
  unfold Ev at *; simp only [pev, ha, hb, bind, Except.bind, ho]; rfl

theorem ev_add {a b : Nd} {x y : UInt64} (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y]) :
    Ev inp ms (.bin 1 a b) env [.w (x + y)] := ev_bin ha hb rfl
theorem ev_sub {a b : Nd} {x y : UInt64} (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y]) :
    Ev inp ms (.bin 2 a b) env [.w (x - y)] := ev_bin ha hb rfl
theorem ev_mul {a b : Nd} {x y : UInt64} (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y]) :
    Ev inp ms (.bin 3 a b) env [.w (x * y)] := ev_bin ha hb rfl
theorem ev_and {a b : Nd} {x y : UInt64} (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y]) :
    Ev inp ms (.bin 4 a b) env [.w (x &&& y)] := ev_bin ha hb rfl
theorem ev_or {a b : Nd} {x y : UInt64} (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y]) :
    Ev inp ms (.bin 5 a b) env [.w (x ||| y)] := ev_bin ha hb rfl
theorem ev_shl {a b : Nd} {x y : UInt64} (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y]) :
    Ev inp ms (.bin 6 a b) env [.w (x <<< y)] := ev_bin ha hb rfl
theorem ev_shr {a b : Nd} {x y : UInt64} (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y]) :
    Ev inp ms (.bin 7 a b) env [.w (x >>> y)] := ev_bin ha hb rfl
theorem ev_xor {a b : Nd} {x y : UInt64} (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y]) :
    Ev inp ms (.bin 8 a b) env [.w (x ^^^ y)] := ev_bin ha hb rfl

/-- value-mode `if a == b` at any result type `α` encoded by `enc` -/
theorem ev_ite1 {α : Type} (enc : α → List W) {a b t e : Nd} {x y : UInt64} {p q : α}
    (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y])
    (ht : Ev inp ms t env (enc p)) (he : Ev inp ms e env (enc q)) :
    Ev inp ms (.ite 1 a b t e) env (enc (if x == y then p else q)) := by
  unfold Ev at *
  simp only [pev, bind, Except.bind]
  rw [ha, hb]; dsimp only
  by_cases h : x = y
  · simp only [h, if_true, BEq.rfl]; subst h; exact ht
  · have h' : (x == y) = false := by simpa using h
    simp only [h, h', if_false, Bool.false_eq_true]; exact he

theorem ev_ite2 {α : Type} (enc : α → List W) {a b t e : Nd} {x y : UInt64} {p q : α}
    (ha : Ev inp ms a env [.w x]) (hb : Ev inp ms b env [.w y])
    (ht : Ev inp ms t env (enc p)) (he : Ev inp ms e env (enc q)) :
    Ev inp ms (.ite 2 a b t e) env (enc (if x < y then p else q)) := by
  unfold Ev at *
  simp only [pev, bind, Except.bind]
  rw [ha, hb]; dsimp only
  by_cases h : x < y
  · simp only [h, if_true]; exact ht
  · simp only [h, if_false]; exact he

theorem ev_let {s w : Nat} {v b : Nd} {x env' r : List W} (hv : Ev inp ms v env x) (hw : x.length = w)
    (he : setSlots env s x = .ok env') (hb : Ev inp ms b env' r) : Ev inp ms (.letE s w v b) env r := by
  unfold Ev at *
  simp only [pev, bind, Except.bind]
  rw [hv]; simp only [hw, if_true, he]; exact hb

/-- `let x := v; body` with a word value: the body is evaluated with `x` abstract, and the result is a real `let` -/
theorem ev_letW {s : Nat} {v b : Nd} {x0 : UInt64} {E : UInt64 → List W} {R : UInt64 → List W}
    (hv : Ev inp ms v env [.w x0]) (he : ∀ x, setSlots env s [.w x] = .ok (E x)) (hb : ∀ x, Ev inp ms b (E x) (R x)) :
    Ev inp ms (.letE s 1 v b) env (let x := x0; R x) := ev_let hv rfl (he x0) (hb x0)
theorem ev_letB {s : Nat} {v b : Nd} {x0 : List UInt64} {E : List UInt64 → List W} {R : List UInt64 → List W}
    (hv : Ev inp ms v env [.b x0]) (he : ∀ x, setSlots env s [.b x] = .ok (E x)) (hb : ∀ x, Ev inp ms b (E x) (R x)) :
    Ev inp ms (.letE s 1 v b) env (let x := x0; R x) := ev_let hv rfl (he x0) (hb x0)

theorem evL_nil : EvL inp ms [] env [] := rfl
theorem evL_cons {n : Nd} {r : List Nd} {v vs : List W} (h1 : Ev inp ms n env v) (h2 : EvL inp ms r env vs) :
    EvL inp ms (n :: r) env (v ++ vs) := by
  unfold Ev EvL at *; simp only [pevL, bind, Except.bind, h1, h2]; rfl

theorem ev_pair {cs : List Nd} {vs : List W} (h : EvL inp ms cs env vs) : Ev inp ms (.pair cs) env vs := by
  unfold Ev EvL at *; simp only [pev, bind, Except.bind, h]; rfl

theorem ev_call {i : Nat} {as : List Nd} {xs r : List W} {F : Fn} (ha : EvL inp ms as env xs) (hF : ms[i]? = some F)
    (hr : F xs = .ok r) : Ev inp ms (.call i as) env r := by
  unfold Ev EvL at *; simp only [pev, bind, Except.bind, ha, hF, hr]; rfl

/-- marker for the `len' x`-fuel form of a loop def's equation -/
def LenC (p : Prop) : Prop := p

/-- a call whose fuel argument is `len' x` -/
theorem ev_callL {i : Nat} {as : List Nd} {xs r : List W} {F : Fn} (ha : EvL inp ms as env xs) (hF : ms[i]? = some F)
    (hr : LenC (F (.w inp.length.toUInt64 :: xs) = .ok r)) : Ev inp ms (.call i (.prim 1 [] :: as)) env r := by
  unfold Ev EvL LenC at *
  simp only [pev, pevL, pprim, val, bind, Except.bind, ha, hF]
  simp only [pure, Except.pure, List.cons_append, List.nil_append, hr]

theorem ev_prim {p : Nat} {as : List Nd} {xs r : List W} (ha : EvL inp ms as env xs) (hr : pprim inp p xs = .ok r) :
    Ev inp ms (.prim p as) env r := by
  unfold Ev EvL at *; simp only [pev, bind, Except.bind, ha, hr]; rfl

theorem ev_rd {i : Nd} {x : UInt64} (h : Ev inp ms i env [.w x]) : Ev inp ms (.prim 2 [i]) env [.w (rd inp x)] :=
  ev_prim (evL_cons h evL_nil) rfl
theorem ev_len : Ev inp ms (.prim 3 []) env [.w (len inp)] := ev_prim evL_nil rfl
theorem ev_bnew : Ev inp ms (.prim 5 []) env [.b bnew] := ev_prim evL_nil rfl
theorem ev_bsize {b : Nd} {l : List UInt64} (h : Ev inp ms b env [.b l]) : Ev inp ms (.prim 6 [b]) env [.w (bsize l)] :=
  ev_prim (evL_cons h evL_nil) rfl
theorem ev_bget {b i : Nd} {l : List UInt64} {x : UInt64} (h : Ev inp ms b env [.b l]) (hi : Ev inp ms i env [.w x]) :
    Ev inp ms (.prim 7 [b, i]) env [.w (bget l x)] := ev_prim (evL_cons h (evL_cons hi evL_nil)) rfl
theorem ev_bset {b i v : Nd} {l : List UInt64} {x y : UInt64} (h : Ev inp ms b env [.b l]) (hi : Ev inp ms i env [.w x])
    (hv : Ev inp ms v env [.w y]) : Ev inp ms (.prim 8 [b, i, v]) env [.b (bset l x y)] :=
  ev_prim (evL_cons h (evL_cons hi (evL_cons hv evL_nil))) rfl
theorem ev_bpush {b v : Nd} {l : List UInt64} {y : UInt64} (h : Ev inp ms b env [.b l]) (hv : Ev inp ms v env [.w y]) :
    Ev inp ms (.prim 9 [b, v]) env [.b (bpush l y)] := ev_prim (evL_cons h (evL_cons hv evL_nil)) rfl

/-- a plain def's certificate from its body's evaluation -/
theorem pdef_of {d : DefA} {ps r : List W} (h1 : ps.length = d.npw) (h2 : d.npw ≤ d.nslots)
    (hb : Ev inp ms d.body (ps ++ List.replicate (d.nslots - d.npw) (.w 0)) r) (hr : r.length = d.nres) :
    pdefMean inp ms d ps = .ok r := by
  unfold Ev at hb
  simp only [pdefMean, h1, h2, and_self, if_true, bind, Except.bind, hb, hr]; rfl

/-- synthesis form with the initial environment given explicitly -/
theorem pdef_env {d : DefA} {ps r r' : List W} (env0 : List W) (h1 : ps.length = d.npw) (h2 : d.npw ≤ d.nslots)
    (he : ps ++ List.replicate (d.nslots - d.npw) (.w 0) = env0) (hb : Ev inp ms d.body env0 r) (hr : r'.length = d.nres)
    (hf : r = r') : pdefMean inp ms d ps = .ok r' := by
  subst he hf; exact pdef_of h1 h2 hb hr

/-- synthesis form: evaluate the body to some `r`, then compare `r` with the Lean value once -/
theorem pdef_of' {d : DefA} {ps r r' : List W} (h1 : ps.length = d.npw) (h2 : d.npw ≤ d.nslots)
    (hb : Ev inp ms d.body (ps ++ List.replicate (d.nslots - d.npw) (.w 0)) r) (hr : r.length = d.nres) (hf : r = r') :
    pdefMean inp ms d ps = .ok r' := hf ▸ pdef_of h1 h2 hb hr
end

attribute [irreducible] Ev EvL LenC

def encW (x : UInt64) : List W := [.w x]
def encB (l : List UInt64) : List W := [.b l]

syntax "evl_auto" : tactic
/-- syntax-directed evaluation of a node against the expected Lean value -/
syntax "ev_auto" : tactic
macro_rules
  | `(tactic| ev_auto) => `(tactic| first
    | exact ev_const _
    | exact ev_loc (Nat.le_of_ble_eq_true rfl) rfl
    | (apply ev_add; (case ha => ev_auto); (case hb => ev_auto))
    | (apply ev_sub; (case ha => ev_auto); (case hb => ev_auto))
    | (apply ev_mul; (case ha => ev_auto); (case hb => ev_auto))
    | (apply ev_and; (case ha => ev_auto); (case hb => ev_auto))
    | (apply ev_or; (case ha => ev_auto); (case hb => ev_auto))
    | (apply ev_shl; (case ha => ev_auto); (case hb => ev_auto))
    | (apply ev_shr; (case ha => ev_auto); (case hb => ev_auto))
    | (apply ev_xor; (case ha => ev_auto); (case hb => ev_auto))
    | (apply ev_ite1 (fun x => [W.w x]); (case ha => ev_auto); (case hb => ev_auto); (case ht => ev_auto); (case he => ev_auto))
    | (apply ev_ite2 (fun x => [W.w x]); (case ha => ev_auto); (case hb => ev_auto); (case ht => ev_auto); (case he => ev_auto))
    | (apply ev_ite1 (fun x => [W.b x]); (case ha => ev_auto); (case hb => ev_auto); (case ht => ev_auto); (case he => ev_auto))
    | (apply ev_ite2 (fun x => [W.b x]); (case ha => ev_auto); (case hb => ev_auto); (case ht => ev_auto); (case he => ev_auto))
    | (apply ev_rd; (case h => ev_auto))
    | exact ev_len
    | exact ev_bnew
    | (apply ev_bsize; (case h => ev_auto))
    | (apply ev_bget; (case h => ev_auto); (case hi => ev_auto))
    | (apply ev_bset; (case h => ev_auto); (case hi => ev_auto); (case hv => ev_auto))
    | (apply ev_bpush; (case h => ev_auto); (case hv => ev_auto))
    | (apply ev_letW
       case hv => ev_auto
       case he => (intro x; simp [setSlots]; first | rfl | done)
       case hb => (intro x; ev_auto))
    | (apply ev_letB
       case hv => ev_auto
       case he => (intro x; simp [setSlots]; first | rfl | done)
       case hb => (intro x; ev_auto))
    | (apply ev_let
       case hv => ev_auto
       case hw => rfl
       case he => rfl
       case hb => ev_auto)
    | (apply ev_callL
       case ha => evl_auto
       case hF => assumption
       case hr => apply_assumption)
    | (apply ev_call
       case ha => evl_auto
       case hF => assumption
       case hr => apply_assumption))
macro_rules
  | `(tactic| evl_auto) => `(tactic| first
    | exact evL_nil
    | (apply evL_cons
       case h1 => ev_auto
       case h2 => evl_auto))

end NanoMain
