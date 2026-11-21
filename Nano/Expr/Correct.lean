/- Nano/Expr/Correct: eval_emit (EXPR.md §6 step 2). `Ev` is the big-step meaning of the Expr fragment (the
constants' Lean meaning); the theorem: for a program whose Exprs `emitAll` produces, every result `Sem` computes is
the meaning of the emitted Expr of `m` applied to the input. -/
import Nano.Expr.Eval
import Nano.Main.Sem
namespace ExprSpec
open NanoMain ParSpec

/-! ## the big-step meaning of the fragment -/
mutual
inductive Ev (P : Prog) : List V → X → V → Prop
  | bv {env i v} : env[i]? = some v → Ev P env (.bv i) v
  | lt {env nd t v b a r} : Ev P env v a → Ev P (a :: env) b r → Ev P env (.lt nd t v b) r
  | litU {env ls k i} : Ev P env (apps (.c "OfNat.ofNat" ls) [.c "UInt64" [], .nat k, i]) (.w (UInt64.ofNat k))
  | litN {env ls k i} : Ev P env (apps (.c "OfNat.ofNat" ls) [.c "Nat" [], .nat k, i]) (.n k)
  | bin {env n ls t1 t2 t3 i a b x y z} : binV n x y = some z → Ev P env a (.w x) → Ev P env b (.w y) →
      Ev P env (apps (.c n ls) [t1, t2, t3, i, a, b]) (.w z)
  | iteT {env ls T c d t e r} : EvB P env c true → Ev P env t r → Ev P env (apps (.c "ite" ls) [T, c, d, t, e]) r
  | iteF {env ls T c d t e r} : EvB P env c false → Ev P env e r → Ev P env (apps (.c "ite" ls) [T, c, d, t, e]) r
  | mk {env ls A B a b x y} : Ev P env a x → Ev P env b y → Ev P env (apps (.c "Prod.mk" ls) [A, B, a, b]) (.p x y)
  | cases {env ls A B M v T1 T2 body x y r} : Ev P env v (.p x y) → Ev P (y :: x :: env) body r →
      Ev P env (apps (.c "Prod.casesOn" ls) [A, B, M, v, .lam T1 (.lam T2 body)]) r
  | natZ {env ls M d z T s r} : Ev P env d (.n 0) → Ev P env z r →
      Ev P env (apps (.c "Nat.casesOn" ls) [M, d, z, .lam T s]) r
  | natS {env ls M d z T s k r} : Ev P env d (.n (k + 1)) → Ev P (.n k :: env) s r →
      Ev P env (apps (.c "Nat.casesOn" ls) [M, d, z, .lam T s]) r
  | nil {env ls T} : Ev P env (.app (.c "List.nil" ls) T) (.l [])
  | prim {env n as vs r} : EvL P env as vs → prim n vs = some r → Ev P env (apps (.c n []) as) r
  | call {env n as vs body b r} : EvL P env as vs → P.lookup n = some body → strip vs.length body = some b →
      Ev P vs.reverse b r → Ev P env (apps (.c n []) as) r
inductive EvB (P : Prog) : List V → X → Bool → Prop
  | eq {env ls ls' B T I a b tr x y} : Ev P env a (.w x) → Ev P env b (.w y) →
      EvB P env (apps (.c "Eq" ls) [B, apps (.c "BEq.beq" ls') [T, I, a, b], tr]) (x == y)
  | lt {env ls T I a b x y} : Ev P env a (.w x) → Ev P env b (.w y) →
      EvB P env (apps (.c "LT.lt" ls) [T, I, a, b]) (decide (x < y))
inductive EvL (P : Prog) : List V → List X → List V → Prop
  | nil {env} : EvL P env [] []
  | cons {env a as v vs} : Ev P env a v → EvL P env as vs → EvL P env (a :: as) (v :: vs)
end

/-! ## values ↔ Sem's flat words -/
/-- `R sh v ws`: the value `v` of shape `sh` is Sem's words `ws` -/
inductive R : Sh → V → List W → Prop
  | uw (v : UInt64) : R .uw (.w v) [.w v]
  | bf (l : List UInt64) : R .bf (.b l) [.b l]
  | ls {o : List UInt8} {ws : List UInt64} : ws.map UInt64.toUInt8 = o → R .ls (.l o) [.b ws]
  | nt {k : Nat} {u : UInt64} : u.toNat = k → R .nt (.n k) [.w u]
  | p {a b : Sh} {x y : V} {xs ys : List W} : R a x xs → R b y ys → R (.p a b) (.p x y) (xs ++ ys)

theorem R.len : ∀ {sh v ws}, R sh v ws → ws.length = sh.width
  | _, _, _, .uw _ => rfl | _, _, _, .bf _ => rfl | _, _, _, .ls _ => rfl | _, _, _, .nt _ => rfl
  | _, _, _, .p ha hb => by simp [Sh.width, ha.len, hb.len]

/-- arguments: values for parameter kinds `ps` (the input as `.l inp`) and Sem's flat argument words -/
inductive ArgsR (inp : List UInt8) : List Ps → List V → List W → Prop
  | nil : ArgsR inp [] [] []
  | inp {ps vs ws} : ArgsR inp ps vs ws → ArgsR inp (.inp :: ps) (.l inp :: vs) ws
  | sh {p ps v vs xs ws} : p ≠ .inp → R (psSh p) v xs → ArgsR inp ps vs ws → ArgsR inp (p :: ps) (v :: vs) (xs ++ ws)

/-- binders ↔ Sem's slot environment: a value binder's value is its slot range; the input is `.l inp`; a fuel
binder's value is unconstrained (its slot is rewritten by the loop) -/
inductive EnvR (inp : List UInt8) (env : List W) : Bs → List V → Prop
  | nil : EnvR inp env [] []
  | inp {s bs venv} : EnvR inp env bs venv → EnvR inp env ((s, .inp) :: bs) (.l inp :: venv)
  | fuel {s bs venv k} : EnvR inp env bs venv → EnvR inp env ((s, .fuel) :: bs) (.n k :: venv)
  | sh {s sh bs v venv} : R sh v ((env.drop s).take sh.width) → EnvR inp env bs venv →
      EnvR inp env ((s, .sh sh) :: bs) (v :: venv)

theorem findSlot_R {inp env} : ∀ {bs venv s i sh}, EnvR inp env bs venv → findSlot s bs = some (i, sh) →
    ∃ v, venv[i]? = some v ∧ R sh v ((env.drop s).take sh.width)
  | _, _, _, _, _, .nil, h => by simp [findSlot] at h
  | _, _, _, i, sh, .inp (s := s') hr, h => by
    simp only [findSlot, Option.map_eq_some_iff] at h
    obtain ⟨⟨j, sh'⟩, hj, he⟩ := h; simp at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨v, hv, hR⟩ := findSlot_R hr hj; exact ⟨v, by simpa using hv, hR⟩
  | _, _, _, i, sh, .fuel (s := s') hr, h => by
    simp only [findSlot, Option.map_eq_some_iff] at h
    obtain ⟨⟨j, sh'⟩, hj, he⟩ := h; simp at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨v, hv, hR⟩ := findSlot_R hr hj; exact ⟨v, by simpa using hv, hR⟩
  | _, _, s, i, sh, .sh (s := s') (v := v0) h0 hr, h => by
    simp only [findSlot] at h
    split at h
    · rename_i hs; simp at h; obtain ⟨rfl, rfl⟩ := h; subst hs; exact ⟨v0, rfl, h0⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨j, sh'⟩, hj, he⟩ := h; simp at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨v, hv, hR⟩ := findSlot_R hr hj; exact ⟨v, by simpa using hv, hR⟩

/-! ## Sem inversion -/
theorem val_ok {r : Out} {ws : List W} : val r = .ok ws ↔ r = .ok (.inl ws) := by
  unfold val; split <;> simp_all

/-- the monad-unfolding simp set for `ev` -/
macro "evsimp" l:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, val] $[$l]?)

theorem ev_bin {cx op a b env r} (h : ev cx (.bin op a b) env = .ok r) :
    ∃ x y z, ev cx a env = .ok (.inl [.w x]) ∧ ev cx b env = .ok (.inl [.w y]) ∧ binop op x y = .ok z ∧
      r = .inl [.w z] := by
  simp only [ev] at h
  rcases ha : ev cx a env with _ | (xs | xs) <;> rw [ha] at h <;> (try evsimp at h) <;> try cases h
  rcases hb : ev cx b env with _ | (ys | ys) <;> rw [hb] at h <;> (try evsimp at h) <;> try cases h
  match xs, ys, h with
  | [.w x], [.w y], h =>
    dsimp only at h
    rcases hz : binop op x y with _ | z <;> rw [hz] at h <;> (try evsimp at h) <;> try cases h
    exact ⟨x, y, z, rfl, rfl, hz, rfl⟩

theorem ev_ite {cx c a b t e env r} (h : ev cx (.ite c a b t e) env = .ok r) :
    ∃ x y, ev cx a env = .ok (.inl [.w x]) ∧ ev cx b env = .ok (.inl [.w y]) ∧
      ((c = 1 ∧ ev cx (if x = y then t else e) env = .ok r) ∨ (c = 2 ∧ ev cx (if x < y then t else e) env = .ok r)) := by
  simp only [ev] at h
  rcases ha : ev cx a env with _ | (xs | xs) <;> rw [ha] at h <;> (try evsimp at h) <;> try cases h
  rcases hb : ev cx b env with _ | (ys | ys) <;> rw [hb] at h <;> (try evsimp at h) <;> try cases h
  match xs, ys, h with
  | [.w x], [.w y], h =>
    refine ⟨x, y, rfl, rfl, ?_⟩
    by_cases h1 : c = 1
    · subst h1; left; refine ⟨rfl, ?_⟩; simp at h; split <;> simp_all
    · by_cases h2 : c = 2
      · subst h2; right; refine ⟨rfl, ?_⟩; simp at h; split <;> simp_all
      · simp [h1, h2] at h

theorem ev_let {cx s w v b env r} (h : ev cx (.letE s w v b) env = .ok r) :
    ∃ x env', ev cx v env = .ok (.inl x) ∧ x.length = w ∧ setSlots env s x = .ok env' ∧ ev cx b env' = .ok r := by
  simp only [ev] at h
  rcases hv : ev cx v env with _ | (x | x) <;> rw [hv] at h <;> (try evsimp at h) <;> try cases h
  by_cases hw : x.length = w
  · simp only [hw, ite_true] at h
    rcases hs : setSlots env s x with _ | env' <;> rw [hs] at h <;> (try evsimp at h) <;> try cases h
    exact ⟨x, env', rfl, hw, hs, h⟩
  · simp [hw] at h

theorem ev_cont {cx e env r} (h : ev cx (.cont e) env = .ok r) : ∃ x, ev cx e env = .ok (.inl x) ∧ r = .inr x := by
  simp only [ev] at h
  rcases hv : ev cx e env with _ | (x | x) <;> rw [hv] at h <;> (try evsimp at h) <;> try cases h
  exact ⟨x, rfl, rfl⟩

theorem ev_pair {cx cs env r} (h : ev cx (.pair cs) env = .ok r) : ∃ xs, evL cx cs env = .ok xs ∧ r = .inl xs := by
  simp only [ev] at h
  rcases hv : evL cx cs env with _ | xs <;> rw [hv] at h <;> (try evsimp at h) <;> try cases h
  exact ⟨xs, rfl, rfl⟩

theorem ev_call {cx i as env r} (h : ev cx (.call i as) env = .ok r) :
    ∃ xs f ys, evL cx as env = .ok xs ∧ cx.defs[i]? = some f ∧ f xs = .ok ys ∧ r = .inl ys := by
  simp only [ev] at h
  rcases hv : evL cx as env with _ | xs <;> rw [hv] at h <;> (try evsimp at h) <;> try cases h
  rcases hf : cx.defs[i]? with _ | f <;> rw [hf] at h <;> (try evsimp at h) <;> try cases h
  rcases hy : f xs with _ | ys <;> rw [hy] at h <;> (try evsimp at h) <;> try cases h
  exact ⟨xs, f, ys, rfl, rfl, hy, rfl⟩

theorem ev_prim {cx p as env r} (h : ev cx (.prim p as) env = .ok r) :
    ∃ xs ys, evL cx as env = .ok xs ∧ NanoMain.prim cx p xs = .ok ys ∧ r = .inl ys := by
  simp only [ev] at h
  rcases hv : evL cx as env with _ | xs <;> rw [hv] at h <;> (try evsimp at h) <;> try cases h
  rcases hy : NanoMain.prim cx p xs with _ | ys <;> rw [hy] at h <;> (try evsimp at h) <;> try cases h
  exact ⟨xs, ys, rfl, hy, rfl⟩

theorem evL_cons {cx a as env r} (h : evL cx (a :: as) env = .ok r) :
    ∃ x xs, ev cx a env = .ok (.inl x) ∧ evL cx as env = .ok xs ∧ r = x ++ xs := by
  simp only [evL] at h
  rcases ha : ev cx a env with _ | (x | x) <;> rw [ha] at h <;> (try evsimp at h) <;> try cases h
  rcases hv : evL cx as env with _ | xs <;> rw [hv] at h <;> (try evsimp at h) <;> try cases h
  exact ⟨x, xs, rfl, rfl, rfl⟩

theorem ev_loc {cx s w env r} (h : ev cx (.loc s w) env = .ok r) : s + w ≤ env.length ∧ r = .inl ((env.drop s).take w) := by
  simp only [ev] at h; split at h
  · simp at h; exact ⟨by assumption, h.symm⟩
  · cases h

/-! ## setSlots -/
theorem setSlots_frame {env env' : List W} {s : Nat} {x : List W} (h : setSlots env s x = .ok env')
    {s' w : Nat} (hle : s' + w ≤ s) : (env'.drop s').take w = (env.drop s').take w := by
  unfold setSlots at h
  split at h
  · rename_i hk; simp at h; subst h
    rw [List.take_drop, List.take_drop]
    have : s' + w ≤ (env.take s).length := by simp; omega
    rw [List.take_append_of_le_length this, List.take_take]
    congr 1; congr 1; omega
  · cases h

theorem setSlots_at {env env' : List W} {s : Nat} {x : List W} (h : setSlots env s x = .ok env') :
    (env'.drop s).take x.length = x := by
  unfold setSlots at h
  split at h
  · rename_i hk; simp at h; subst h
    have : (env.take s).length = s := by simp; omega
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega)]
    simp [this]
  · cases h

theorem setSlots_len {env env' : List W} {s : Nat} {x : List W} (h : setSlots env s x = .ok env') :
    env'.length = env.length := by
  unfold setSlots at h
  split at h
  · rename_i hk; simp at h; subst h; simp; omega
  · cases h

/-! ## environments -/
theorem EnvR.frame {inp env env' s x} (hs : setSlots env s x = .ok env') :
    ∀ {bs venv}, fresh s bs = true → EnvR inp env bs venv → EnvR inp env' bs venv
  | _, _, _, .nil => .nil
  | _, _, hf, .inp h => .inp (h.frame hs (by simp_all [fresh]))
  | _, _, hf, .fuel h => .fuel (h.frame hs (by simp_all [fresh]))
  | (s', .sh sh0) :: bs', v' :: venv', hf, .sh h0 h => by
    simp only [fresh, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hf
    refine .sh ?_ (h.frame hs (by simpa [fresh] using hf.2))
    rw [setSlots_frame hs (by simpa [Ps.width] using hf.1)]; exact h0

theorem inpX_R {inp env} : ∀ {bs venv x}, EnvR inp env bs venv → inpX bs = some x →
    ∃ i, x = .bv i ∧ venv[i]? = some (.l inp)
  | _, _, _, .nil, h => by simp [inpX, findB] at h
  | _, _, x, .inp (s := s) hr, h => by
    simp [inpX, findB] at h; subst h; exact ⟨0, rfl, rfl⟩
  | _, _, x, .fuel (s := s) hr, h => by
    simp only [inpX, findB, Option.map_eq_some_iff] at h
    obtain ⟨j, hj, rfl⟩ := h
    simp at hj; obtain ⟨j', hj', rfl⟩ := hj
    obtain ⟨i, hi, hv⟩ := inpX_R hr (show inpX _ = some (.bv j') by simp [inpX, hj'])
    cases hi; exact ⟨j' + 1, rfl, by simpa using hv⟩
  | _, _, x, .sh (s := s) _ hr, h => by
    simp only [inpX, findB, Option.map_eq_some_iff] at h
    obtain ⟨j, hj, rfl⟩ := h
    simp at hj; obtain ⟨j', hj', rfl⟩ := hj
    obtain ⟨i, hi, hv⟩ := inpX_R hr (show inpX _ = some (.bv j') by simp [inpX, hj'])
    cases hi; exact ⟨j' + 1, rfl, by simpa using hv⟩

/-- the innermost fuel binder holds `.n k` -/
def FuelAt (bs : Bs) (venv : List V) (k : Nat) : Prop :=
  ∀ fi, findB (fun b => b.2 == .fuel) bs = some fi → venv[fi]? = some (.n k)

theorem FuelAt.push {bs venv k s sh v} (h : FuelAt bs venv k) : FuelAt ((s, .sh sh) :: bs) (v :: venv) k := by
  intro fi hf
  simp only [findB, Option.map_eq_some_iff] at hf
  simp at hf; obtain ⟨j, hj, rfl⟩ := hf
  simpa using h j hj

/-! ## the node lemma -/
/-- a def call's meaning: the def's value, its λs stripped by the arguments, evaluated in them -/
def EvCall (P : Prog) (n : String) (vs : List V) (v : V) : Prop :=
  ∃ body b, P.lookup n = some body ∧ strip vs.length body = some b ∧ Ev P vs.reverse b v

/-- what a node needs: callee meanings (`defs`), and for a loop's step arm the meaning of a CONTINUE (`kont`:
Sem's continuation from payload `st` is the self call at fuel `k`) -/
structure Hyp (P : Prog) (cx : Ctx) (cxe : Cx) (res : Sh) (k : Nat) (Kont : List W → Except Stop (List W)) : Prop where
  inp : cx.inp.length < 2 ^ 64
  defs : ∀ (i : Nat) (f : List W → Except Stop (List W)) (d : DefI), cx.defs[i]? = some f → cxe.defs[i]? = some d → ∀ ws r vs, f ws = .ok r →
    ArgsR cx.inp d.params vs ws → ∃ v, EvCall P (nameS d.name) vs v ∧ R d.res v r
  kont : ∀ st r vs, Kont st = .ok r → ArgsR cx.inp cxe.self.2 vs st →
    ∃ v, EvCall P cxe.self.1 (.n k :: vs) v ∧ R res v r

def NodeOK (P : Prog) (cx : Ctx) (cxe : Cx) (res : Sh) (k : Nat) (Kont : List W → Except Stop (List W)) (e : Na) : Prop :=
  ∀ bs exp x sh env venv, emit cxe bs exp e = some (x, sh) → EnvR cx.inp env bs venv → FuelAt bs venv k →
    (∀ ws, ev cx e.erase env = .ok (.inl ws) → ∃ v s', sh = some s' ∧ Ev P venv x v ∧ R s' v ws) ∧
    (∀ st r, ev cx e.erase env = .ok (.inr st) → Kont st = .ok r → ∃ v, Ev P venv x v ∧ R res v r)

def ArgsOK (P : Prog) (cx : Ctx) (cxe : Cx) (as : List Na) : Prop :=
  ∀ bs ps xs env venv, args cxe bs ps as = some xs → EnvR cx.inp env bs venv →
    ∀ ws, evL cx (Na.eraseL as) env = .ok ws → ∃ vs, EvL P venv xs vs ∧ ArgsR cx.inp ps vs ws

theorem const_ok {P cx cxe res k Kont} (v : UInt64) : NodeOK P cx cxe res k Kont (.const v) := by
  intro bs exp x sh env venv he _ _
  unfold emit at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨fun ws hw => ?_, fun st r hw => by simp [Na.erase, ev] at hw⟩
  simp [Na.erase, ev] at hw; subst hw
  split
  · exact ⟨_, _, rfl, Ev.litN, .nt rfl⟩
  · refine ⟨_, _, rfl, ?_, .uw v⟩
    have h := Ev.litU (P := P) (env := venv) (ls := [0]) (k := v.toNat) (i := .app (.c "UInt64.instOfNat" []) (.nat v.toNat))
    have e : UInt64.ofNat v.toNat = v := by simp
    rw [e] at h; exact h

theorem loc_ok {P cx cxe res k Kont} (s w : Nat) : NodeOK P cx cxe res k Kont (.loc s w) := by
  intro bs exp x sh env venv he hr _
  unfold emit at he
  rcases hf : findSlot s bs with _ | ⟨i, sh0⟩ <;> rw [hf] at he <;> simp only [bind, Option.bind] at he
  · cases he
  split at he
  · rename_i hw; simp at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨v, hv, hR⟩ := findSlot_R hr hf
    refine ⟨fun ws hws => ?_, fun st r hws => by simp [Na.erase] at hws; have := (ev_loc hws).2; cases this⟩
    simp only [Na.erase] at hws
    obtain ⟨-, hws⟩ := ev_loc hws; simp at hws; subst hws
    exact ⟨v, sh0, rfl, .bv hv, by rw [hw.1]; exact hR⟩
  · cases he

theorem bin_ok {P cx cxe res k Kont op a b} (ha : NodeOK P cx cxe res k Kont a) (hb : NodeOK P cx cxe res k Kont b) :
    NodeOK P cx cxe res k Kont (.bin op a b) := by
  intro bs exp x sh env venv he hr hfu
  unfold emit at he
  rcases hea : emit cxe bs (some .uw) a with _ | ⟨xa, sa⟩ <;> rw [hea] at he <;> simp only [bind, Option.bind] at he
  · cases he
  rcases heb : emit cxe bs (some .uw) b with _ | ⟨xb, sb⟩ <;> rw [heb] at he <;> simp only [bind, Option.bind] at he
  · cases he
  split at he
  · rename_i hc; simp at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨rfl, rfl, h1, h7⟩ := hc
    have key : ∀ r, ev cx (Na.erase (.bin op a b)) env = .ok r →
        ∃ x y z, Ev P venv xa (.w x) ∧ Ev P venv xb (.w y) ∧ binop op x y = .ok z ∧ r = .inl [.w z] := by
      intro r hr'
      obtain ⟨x, y, z, h1', h2', h3', rfl⟩ := ev_bin hr'
      obtain ⟨va, _, hsa, hva, hRa⟩ := (ha bs _ _ _ env venv hea hr hfu).1 _ h1'
      obtain ⟨vb, _, hsb, hvb, hRb⟩ := (hb bs _ _ _ env venv heb hr hfu).1 _ h2'
      cases hsa; cases hsb; cases hRa; cases hRb
      exact ⟨x, y, z, hva, hvb, h3', rfl⟩
    refine ⟨fun ws hws => ?_, fun st r hws _ => ?_⟩
    · obtain ⟨x, y, z, hx, hy, hz, he⟩ := key _ hws; cases he
      refine ⟨.w z, .uw, rfl, ?_, .uw z⟩
      have : op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [binop, Except.ok.injEq] at hz; subst hz; exact Ev.bin rfl hx hy)
    · obtain ⟨x, y, z, -, -, -, he⟩ := key _ hws; cases he
  · cases he

theorem agree_eq {r : Sh} {t : Option Sh} {s : Sh} (h : agree r t = true) (ht : t = some s) : s = r := by
  subst ht; simpa [agree] using h

theorem ite_ok {P cx cxe res k Kont c a b t e} (ha : NodeOK P cx cxe res k Kont a) (hb : NodeOK P cx cxe res k Kont b)
    (ht : NodeOK P cx cxe res k Kont t) (hel : NodeOK P cx cxe res k Kont e) :
    NodeOK P cx cxe res k Kont (.ite c a b t e) := by
  intro bs exp x sh env venv he hr hfu
  unfold emit at he
  rcases hea : emit cxe bs (some .uw) a with _ | ⟨xa, sa⟩ <;> rw [hea] at he <;> simp only [bind, Option.bind] at he
  · cases he
  rcases heb : emit cxe bs (some .uw) b with _ | ⟨xb, sb⟩ <;> rw [heb] at he <;> simp only [bind, Option.bind] at he
  · cases he
  rcases het : emit cxe bs exp t with _ | ⟨xt, st⟩ <;> rw [het] at he <;> simp only [bind, Option.bind] at he
  · cases he
  rcases hee : emit cxe bs exp e with _ | ⟨xe, se⟩ <;> rw [hee] at he <;> simp only [bind, Option.bind] at he
  · cases he
  rcases hr0 : exp <|> st <|> se with _ | r0 <;> rw [hr0] at he <;> simp only at he
  · cases he
  split at he
  · rename_i hc; simp at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨rfl, rfl, hcmp, hagt, hage⟩ := hc
    -- the operands and the condition
    have key : ∀ q, ev cx (Na.erase (.ite c a b t e)) env = .ok q →
        ∃ x y, Ev P venv xa (.w x) ∧ Ev P venv xb (.w y) ∧
          ((c = 1 ∧ ev cx (if x = y then t.erase else e.erase) env = .ok q) ∨
           (c = 2 ∧ ev cx (if x < y then t.erase else e.erase) env = .ok q)) := by
      intro q hq
      obtain ⟨x, y, h1, h2, h3⟩ := ev_ite hq
      obtain ⟨va, _, hsa, hva, hRa⟩ := (ha bs _ _ _ env venv hea hr hfu).1 _ h1
      obtain ⟨vb, _, hsb, hvb, hRb⟩ := (hb bs _ _ _ env venv heb hr hfu).1 _ h2
      cases hsa; cases hsb; cases hRa; cases hRb
      exact ⟨x, y, hva, hvb, h3⟩
    -- the chosen branch
    have pick : ∀ (x y : UInt64) (bc : Bool), (∀ q, ev cx (if bc then t.erase else e.erase) env = .ok q → True) →
        EvB P venv (if c = 1 then apps (.c "Eq" [1]) [.c "Bool" [], apps (.c "BEq.beq" [0]) [U,
          apps (.c "instBEqOfDecidableEq" [0]) [U, .c "instDecidableEqUInt64" []], xa, xb], .c "Bool.true" []]
          else apps (.c "LT.lt" [0]) [U, .c "instLTUInt64" [], xa, xb]) bc →
        ∀ v, Ev P venv (if bc then xt else xe) v → Ev P venv (iteX r0 c xa xb xt xe) v := by
      intro x y bc _ hB v hv
      unfold iteX
      split
      · rename_i h1; simp only [h1, ite_true] at hB
        cases bc
        · exact Ev.iteF hB hv
        · exact Ev.iteT hB hv
      · rename_i h1; simp only [h1, ite_false] at hB
        cases bc
        · exact Ev.iteF hB hv
        · exact Ev.iteT hB hv
    have branch : ∀ q, ev cx (Na.erase (.ite c a b t e)) env = .ok q →
        ∃ bc, EvB P venv (if c = 1 then apps (.c "Eq" [1]) [.c "Bool" [], apps (.c "BEq.beq" [0]) [U,
          apps (.c "instBEqOfDecidableEq" [0]) [U, .c "instDecidableEqUInt64" []], xa, xb], .c "Bool.true" []]
          else apps (.c "LT.lt" [0]) [U, .c "instLTUInt64" [], xa, xb]) bc ∧
          ev cx (if bc then t.erase else e.erase) env = .ok q := by
      intro q hq
      obtain ⟨x, y, hx, hy, h3⟩ := key q hq
      rcases h3 with ⟨rfl, h3⟩ | ⟨rfl, h3⟩
      · refine ⟨x == y, ?_, ?_⟩
        · rw [if_pos rfl]; exact EvB.eq hx hy
        · by_cases hxy : x = y
          · rw [if_pos hxy] at h3; rw [if_pos (by simp [hxy])]; exact h3
          · rw [if_neg hxy] at h3; rw [if_neg (by simp [hxy])]; exact h3
      · refine ⟨decide (x < y), ?_, ?_⟩
        · rw [if_neg (by decide)]; exact EvB.lt hx hy
        · by_cases hxy : x < y
          · rw [if_pos hxy] at h3; rw [if_pos (by simp [hxy])]; exact h3
          · rw [if_neg hxy] at h3; rw [if_neg (by simp [hxy])]; exact h3
    refine ⟨fun ws hws => ?_, fun st0 r hws hk => ?_⟩
    · obtain ⟨bc, hB, hbr⟩ := branch _ hws
      cases bc
      · rw [if_neg (by decide)] at hbr
        obtain ⟨v, s', hs', hv, hR⟩ := (hel bs _ _ _ env venv hee hr hfu).1 _ hbr
        exact ⟨v, r0, rfl, pick 0 0 false (fun _ _ => trivial) hB v (by simpa using hv), (agree_eq hage hs') ▸ hR⟩
      · rw [if_pos rfl] at hbr
        obtain ⟨v, s', hs', hv, hR⟩ := (ht bs _ _ _ env venv het hr hfu).1 _ hbr
        exact ⟨v, r0, rfl, pick 0 0 true (fun _ _ => trivial) hB v (by simpa using hv), (agree_eq hagt hs') ▸ hR⟩
    · obtain ⟨bc, hB, hbr⟩ := branch _ hws
      cases bc
      · rw [if_neg (by decide)] at hbr
        obtain ⟨v, hv, hR⟩ := (hel bs _ _ _ env venv hee hr hfu).2 _ _ hbr hk
        exact ⟨v, pick 0 0 false (fun _ _ => trivial) hB v (by simpa using hv), hR⟩
      · rw [if_pos rfl] at hbr
        obtain ⟨v, hv, hR⟩ := (ht bs _ _ _ env venv het hr hfu).2 _ _ hbr hk
        exact ⟨v, pick 0 0 true (fun _ _ => trivial) hB v (by simpa using hv), hR⟩
  · cases he

end ExprSpec
