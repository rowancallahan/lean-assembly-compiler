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

theorem take_split {L xs ys : List W} (h : L.take (xs ++ ys).length = xs ++ ys) :
    L.take xs.length = xs ∧ (L.drop xs.length).take ys.length = ys := by
  rw [List.length_append] at h
  constructor
  · rw [show xs.length = min xs.length (xs.length + ys.length) by omega, ← List.take_take, h]; simp
  · rw [show ys.length = xs.length + ys.length - xs.length by omega, ← List.drop_take, h]; simp

theorem let_ok {P cx cxe res k Kont pr s w v b} (hv : NodeOK P cx cxe res k Kont v)
    (hb : NodeOK P cx cxe res k Kont b) : NodeOK P cx cxe res k Kont (.letE pr s w v b) := by
  intro bs exp x sh env venv he hr hfu
  unfold emit at he
  rcases hev : emit cxe bs none v with _ | ⟨xv, sv⟩ <;> rw [hev] at he <;> simp only [bind, Option.bind] at he
  · cases he
  rcases sv with _ | vsh <;> simp only at he
  · cases he
  split at he
  · cases he
  rename_i hck; obtain ⟨hw, hfr⟩ := Decidable.not_not.mp hck
  -- Sem's value, written at slot s
  have val : ∀ q, ev cx (Na.erase (.letE pr s w v b)) env = .ok q →
      ∃ a xs env', Ev P venv xv a ∧ R vsh a xs ∧ setSlots env s xs = .ok env' ∧ ev cx b.erase env' = .ok q := by
    intro q hq
    obtain ⟨xs, env', h1, h2, h3, h4⟩ := ev_let hq
    obtain ⟨a, _, hs, ha, hRa⟩ := (hv bs _ _ _ env venv hev hr hfu).1 _ h1
    cases hs
    exact ⟨a, xs, env', ha, hRa, h3, h4⟩
  cases pr with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at he
    rcases heb : emit cxe ((s, .sh vsh) :: bs) exp b with _ | ⟨xb, sb⟩ <;> rw [heb] at he <;> simp only [bind, Option.bind] at he
    · cases he
    simp at he; obtain ⟨rfl, rfl⟩ := he
    have env_ok : ∀ a xs env', R vsh a xs → setSlots env s xs = .ok env' →
        EnvR cx.inp env' ((s, .sh vsh) :: bs) (a :: venv) := by
      intro a xs env' hRa hs
      refine .sh ?_ (hr.frame hs hfr)
      rw [← hRa.len]; rw [setSlots_at hs]; exact hRa
    refine ⟨fun ws hws => ?_, fun st r hws hk => ?_⟩
    · obtain ⟨a, xs, env', ha, hRa, hs, hbody⟩ := val _ hws
      obtain ⟨vb, s', hs', hvb, hRb⟩ := (hb _ _ _ _ env' _ heb (env_ok a xs env' hRa hs) hfu.push).1 _ hbody
      exact ⟨vb, s', hs', Ev.lt ha hvb, hRb⟩
    · obtain ⟨a, xs, env', ha, hRa, hs, hbody⟩ := val _ hws
      obtain ⟨vb, hvb, hRb⟩ := (hb _ _ _ _ env' _ heb (env_ok a xs env' hRa hs) hfu.push).2 _ _ hbody hk
      exact ⟨vb, Ev.lt ha hvb, hRb⟩
  | true =>
    simp only [ite_true] at he
    rcases vsh with _ | _ | _ | _ | ⟨l, r⟩ <;> simp only at he
    all_goals try cases he
    rcases heb : emit cxe ((s + l.width, .sh r) :: (s, .sh l) :: bs) exp b with _ | ⟨xb, sb⟩ <;>
      rw [heb] at he <;> simp only [bind, Option.bind] at he
    · cases he
    rcases hR0 : exp <|> sb with _ | R0 <;> rw [hR0] at he <;> simp only at he
    · cases he
    split at he
    · rename_i hag; simp at he; obtain ⟨rfl, rfl⟩ := he
      have env_ok : ∀ a xs env', R (.p l r) a xs → setSlots env s xs = .ok env' →
          ∃ a1 a2, a = .p a1 a2 ∧ EnvR cx.inp env' ((s + l.width, .sh r) :: (s, .sh l) :: bs) (a2 :: a1 :: venv) := by
        intro a xs env' hRa hs
        cases hRa with
        | p h1 h2 =>
          rename_i a1 a2 xs1 ys1
          have hat := setSlots_at hs
          obtain ⟨hx1, hy1⟩ := take_split hat
          refine ⟨a1, a2, rfl, .sh ?_ (.sh ?_ (hr.frame hs hfr))⟩
          · rw [← List.drop_drop, ← h1.len, ← h2.len, hy1]; exact h2
          · rw [← h1.len, hx1]; exact h1
      refine ⟨fun ws hws => ?_, fun st r1 hws hk => ?_⟩
      · obtain ⟨a, xs, env', ha, hRa, hs, hbody⟩ := val _ hws
        obtain ⟨a1, a2, rfl, henv⟩ := env_ok a xs env' hRa hs
        obtain ⟨vb, s', hs', hvb, hRb⟩ := (hb _ _ _ _ env' _ heb henv hfu.push.push).1 _ hbody
        exact ⟨vb, R0, rfl, Ev.cases ha hvb, (agree_eq hag hs') ▸ hRb⟩
      · obtain ⟨a, xs, env', ha, hRa, hs, hbody⟩ := val _ hws
        obtain ⟨a1, a2, rfl, henv⟩ := env_ok a xs env' hRa hs
        obtain ⟨vb, hvb, hRb⟩ := (hb _ _ _ _ env' _ heb henv hfu.push.push).2 _ _ hbody hk
        exact ⟨vb, Ev.cases ha hvb, hRb⟩
    · cases he

theorem evL_nil {cx env r} (h : evL cx [] env = .ok r) : r = [] := by simp [evL] at h; exact h

theorem leadInp_spec : ∀ (ps : List Ps) n p ps', leadInp ps = (n, p :: ps') →
    ps = List.replicate n .inp ++ p :: ps' ∧ p ≠ .inp
  | .inp :: ps, n, p, ps', h => by
    simp only [leadInp] at h
    rcases h' : leadInp ps with ⟨m, r⟩
    rw [h'] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := leadInp_spec ps m p ps' h'
    exact ⟨by rw [h1]; simp [List.replicate_succ], h2⟩
  | [], n, p, ps', h => by simp [leadInp] at h
  | .fuel :: ps, n, p, ps', h => by simp [leadInp] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, by simp⟩
  | .sh sh :: ps, n, p, ps', h => by simp [leadInp] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, by simp⟩

theorem ArgsR.inps {inp} : ∀ (n : Nat) {ps vs ws}, ArgsR inp ps vs ws →
    ArgsR inp (List.replicate n .inp ++ ps) (List.replicate n (.l inp) ++ vs) ws
  | 0, _, _, _, h => by simpa using h
  | n + 1, _, _, _, h => by simpa [List.replicate_succ] using ArgsR.inp (ArgsR.inps n h)

theorem EvL.app {P env} : ∀ {as bs vs ws}, EvL P env as vs → EvL P env bs ws → EvL P env (as ++ bs) (vs ++ ws)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha h1, h2 => .cons ha (EvL.app h1 h2)

theorem EvL.rep {P env x v} (h : Ev P env x v) : ∀ (n : Nat), EvL P env (List.replicate n x) (List.replicate n v)
  | 0 => .nil
  | n + 1 => by simpa [List.replicate_succ] using EvL.cons h (EvL.rep h n)

theorem inps_ok {P inp env venv bs} (hr : EnvR inp env bs venv) :
    ∀ (ps : List Ps) xs, inps bs ps = some xs → ∃ vs, EvL P venv xs vs ∧ ArgsR inp ps vs []
  | [], xs, h => by simp [inps] at h; subst h; exact ⟨[], .nil, .nil⟩
  | .inp :: ps, xs, h => by
    simp only [inps, bind, Option.bind] at h
    rcases h1 : inpX bs with _ | y <;> rw [h1] at h <;> simp only at h
    · cases h
    rcases h2 : inps bs ps with _ | ys <;> rw [h2] at h <;> simp at h
    subst h
    obtain ⟨i, rfl, hv⟩ := inpX_R hr h1
    obtain ⟨vs, hvs, hA⟩ := inps_ok hr ps ys h2
    exact ⟨_, .cons (.bv hv) hvs, .inp hA⟩
  | .fuel :: ps, xs, h => by simp [inps] at h
  | .sh _ :: ps, xs, h => by simp [inps] at h

theorem args_ok {P cx cxe res k Kont} : ∀ (ps : List Ps) (as : List Na), (∀ a ∈ as, NodeOK P cx cxe res k Kont a) →
    ∀ bs xs env venv, args cxe bs ps as = some xs → EnvR cx.inp env bs venv → FuelAt bs venv k →
    ∀ ws, evL cx (Na.eraseL as) env = .ok ws → ∃ vs, EvL P venv xs vs ∧ ArgsR cx.inp ps vs ws
  | ps, [], _, bs, xs, env, venv, he, hr, _, ws, hw => by
    unfold args at he
    simp [Na.eraseL] at hw; rw [evL_nil hw]; exact inps_ok hr ps xs he
  | ps, a :: as, hall, bs, xs, env, venv, he, hr, hfu, ws, hw => by
    unfold args at he
    rcases hl : leadInp ps with ⟨n, _ | ⟨p, ps'⟩⟩ <;> rw [hl] at he <;> simp only at he
    · cases he
    obtain ⟨hps, hp⟩ := leadInp_spec ps n p ps' hl
    obtain ⟨ix, hix, he⟩ : ∃ ix, (n ≠ 0 → inpX bs = some ix) ∧ (do
        let (x, sx) ← emit cxe bs (some (psSh p)) a
        if sx ≠ some (psSh p) then none else
        some (List.replicate n ix ++ x :: (← args cxe bs ps' as))) = some xs := by
      by_cases hn : n = 0
      · subst hn; exact ⟨.bv 0, fun h => absurd rfl h, by simpa using he⟩
      · rw [if_neg hn] at he
        rcases hi : inpX bs with _ | ix <;> rw [hi] at he <;> simp only [bind, Option.bind] at he
        · cases he
        exact ⟨ix, fun _ => rfl, he⟩
    rcases hea : emit cxe bs (some (psSh p)) a with _ | ⟨x, sx⟩ <;> rw [hea] at he <;> simp only [bind, Option.bind] at he
    · cases he
    split at he
    · cases he
    rename_i hsx; have hsx := Decidable.not_not.mp hsx; subst hsx
    rcases hrest : args cxe bs ps' as with _ | xs' <;> rw [hrest] at he <;> simp at he
    subst he
    obtain ⟨wa, wr, h1, h2, rfl⟩ := evL_cons (by simpa [Na.eraseL] using hw)
    obtain ⟨va, s', hs', hva, hRa⟩ := (hall a (by simp) bs _ _ _ env venv hea hr hfu).1 _ h1
    cases hs'
    obtain ⟨vs, hvs, hA⟩ := args_ok ps' as (fun a' h' => hall a' (by simp [h'])) bs xs' env venv hrest hr hfu wr h2
    have hix' : n ≠ 0 → Ev P venv ix (.l cx.inp) := fun hn => by
      obtain ⟨i, rfl, hv⟩ := inpX_R hr (hix hn); exact .bv hv
    refine ⟨List.replicate n (.l cx.inp) ++ va :: vs, ?_, by rw [hps]; exact ArgsR.inps n (.sh hp hRa hA)⟩
    refine EvL.app ?_ (.cons hva hvs)
    by_cases hn : n = 0
    · subst hn; exact .nil
    · exact EvL.rep (hix' hn) n

theorem pair_ok {P cx cxe res k Kont a b} (ha : NodeOK P cx cxe res k Kont a) (hb : NodeOK P cx cxe res k Kont b) :
    NodeOK P cx cxe res k Kont (.pair [a, b]) := by
  intro bs exp x sh env venv he hr hfu
  unfold emit at he
  generalize expSplit exp = pe at he
  obtain ⟨ea, eb⟩ := pe
  simp only at he
  rcases hea : emit cxe bs ea a with _ | ⟨xa, sa⟩ <;> simp only [hea, bind, Option.bind] at he
  · cases he
  rcases heb : emit cxe bs eb b with _ | ⟨xb, sb⟩ <;> simp only [heb, bind, Option.bind] at he
  · cases he
  rcases sa with _ | A <;> simp only at he
  · cases he
  rcases sb with _ | B <;> simp only at he
  · cases he
  split at he
  · simp at he; obtain ⟨rfl, rfl⟩ := he
    have key : ∀ q, ev cx (Na.erase (.pair [a, b])) env = .ok q →
        ∃ va vb xs ys, Ev P venv xa va ∧ Ev P venv xb vb ∧ R A va xs ∧ R B vb ys ∧ q = .inl (xs ++ ys) := by
      intro q hq
      obtain ⟨ws, hws, rfl⟩ := ev_pair hq
      obtain ⟨xs, r1, h1, h2, rfl⟩ := evL_cons (by simpa [Na.erase, Na.eraseL] using hws)
      obtain ⟨ys, r2, h3, h4, rfl⟩ := evL_cons h2
      rw [evL_nil h4]
      obtain ⟨va, _, hs1, hva, hR1⟩ := (ha bs _ _ _ env venv hea hr hfu).1 _ h1
      obtain ⟨vb, _, hs2, hvb, hR2⟩ := (hb bs _ _ _ env venv heb hr hfu).1 _ h3
      cases hs1; cases hs2
      exact ⟨va, vb, xs, ys, hva, hvb, hR1, hR2, by simp⟩
    refine ⟨fun ws hws => ?_, fun st r hws _ => ?_⟩
    · obtain ⟨va, vb, xs, ys, hva, hvb, h1, h2, he⟩ := key _ hws; cases he
      exact ⟨.p va vb, _, rfl, Ev.mk hva hvb, .p h1 h2⟩
    · obtain ⟨_, _, _, _, _, _, _, _, he⟩ := key _ hws; cases he
  · cases he

theorem nil_ok {P cx cxe res k Kont} (lst : Bool) : NodeOK P cx cxe res k Kont (.nil lst) := by
  intro bs exp x sh env venv he _ _
  unfold emit at he; simp only [Option.some.injEq] at he
  have key : ∀ q, ev cx (Na.erase (.nil lst)) env = .ok q → q = .inl [.b []] := by
    intro q hq
    obtain ⟨xs, ys, h1, h2, rfl⟩ := ev_prim (by simpa [Na.erase] using hq)
    rw [evL_nil h1] at h2; simp [NanoMain.prim] at h2; rw [h2]
  refine ⟨fun ws hws => ?_, fun st r hws _ => by cases key _ hws⟩
  cases key _ hws
  cases lst
  · simp at he; obtain ⟨rfl, rfl⟩ := he
    exact ⟨.b [], .bf, rfl, Ev.prim (as := []) .nil rfl, .bf []⟩
  · simp at he; obtain ⟨rfl, rfl⟩ := he
    exact ⟨.l [], .ls, rfl, Ev.nil, .ls rfl⟩

theorem push_ok {κ : Nat} {l : List UInt64} {v : UInt64} {ys : List W} (h : NanoMain.push κ l v = .ok ys) :
    ys = [.b (l ++ [v])] := by
  unfold NanoMain.push at h; split at h
  · simp at h; exact h.symm
  · cases h

/-- the prims: Sem's prim and the fragment's constant agree on related arguments -/
theorem prim_rel {cx : Ctx} (hin : cx.inp.length < 2 ^ 64) {p : Nat} (hp : ¬ (p = 5 ∨ p = 0 ∨ 9 < p)) {vs ws ys}
    (hA : ArgsR cx.inp (primInfo p).2.1 vs ws) (hs : NanoMain.prim cx p ws = .ok ys) :
    ∃ r, ExprSpec.prim (primInfo p).1 vs = some r ∧ R (primInfo p).2.2 r ys := by
  have : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [primInfo] at hA ⊢
  · rcases hA with _ | ⟨h⟩ | ⟨hp, _, _⟩
    · cases h; simp [NanoMain.prim] at hs; subst hs; exact ⟨_, rfl, .nt (by simp; omega)⟩
    · exact absurd rfl hp
  · rcases hA with _ | ⟨h⟩ | ⟨hp, _, _⟩
    · rcases h with _ | _ | ⟨_, h1, h2⟩
      cases h1; cases h2; simp [NanoMain.prim] at hs; subst hs; exact ⟨_, rfl, .uw _⟩
    · exact absurd rfl hp
  · rcases hA with _ | ⟨h⟩ | ⟨hp, _, _⟩
    · cases h; simp [NanoMain.prim] at hs; subst hs; exact ⟨_, rfl, .uw _⟩
    · exact absurd rfl hp
  · rcases hA with _ | _ | ⟨_, h1, h⟩
    rcases h with _ | _ | ⟨_, h2, h3⟩
    cases h3; cases h2
    rcases h1 with _ | _ | ⟨ho⟩
    simp only [List.append_nil, List.singleton_append, NanoMain.prim] at hs
    rw [push_ok hs]; exact ⟨_, rfl, .ls (by simp [← ho])⟩
  · rcases hA with _ | _ | ⟨_, h1, h⟩
    cases h; cases h1; simp [NanoMain.prim] at hs; subst hs; exact ⟨_, rfl, .uw _⟩
  · rcases hA with _ | _ | ⟨_, h1, h⟩
    rcases h with _ | _ | ⟨_, h2, h3⟩
    cases h3; cases h2; cases h1; simp [NanoMain.prim] at hs; subst hs; exact ⟨_, rfl, .uw _⟩
  · rcases hA with _ | _ | ⟨_, h1, h⟩
    rcases h with _ | _ | ⟨_, h2, h⟩
    rcases h with _ | _ | ⟨_, h3, h4⟩
    cases h4; cases h3; cases h2; cases h1; simp [NanoMain.prim] at hs; subst hs; exact ⟨_, rfl, .bf _⟩
  · rcases hA with _ | _ | ⟨_, h1, h⟩
    rcases h with _ | _ | ⟨_, h2, h3⟩
    cases h3; cases h2; cases h1
    simp only [List.append_nil, List.singleton_append, NanoMain.prim] at hs
    rw [push_ok hs]; exact ⟨_, rfl, .bf _⟩

theorem prim_ok {P cx cxe res k Kont p as} (hin : cx.inp.length < 2 ^ 64)
    (hall : ∀ a ∈ as, NodeOK P cx cxe res k Kont a) : NodeOK P cx cxe res k Kont (.prim p as) := by
  intro bs exp x sh env venv he hr hfu
  unfold emit at he
  split at he
  · cases he
  rename_i hp
  rcases hpi : primInfo p with ⟨n, ps, r⟩
  rw [hpi] at he; simp only at he
  rcases hxs : args cxe bs ps as with _ | xs <;> rw [hxs] at he <;> simp only [bind, Option.bind] at he
  · cases he
  simp at he; obtain ⟨rfl, rfl⟩ := he
  have key : ∀ q, ev cx (Na.erase (.prim p as)) env = .ok q →
      ∃ v ys, Ev P venv (apps (.c n []) xs) v ∧ R r v ys ∧ q = .inl ys := by
    intro q hq
    obtain ⟨ws, ys, h1, h2, rfl⟩ := ev_prim (by simpa [Na.erase] using hq)
    obtain ⟨vs, hvs, hA⟩ := args_ok ps as hall bs xs env venv hxs hr hfu ws h1
    rw [show ps = (primInfo p).2.1 by rw [hpi]] at hA
    obtain ⟨v, hv, hR⟩ := prim_rel hin hp hA h2
    rw [hpi] at hv hR
    exact ⟨v, ys, Ev.prim hvs hv, hR, rfl⟩
  refine ⟨fun ws hws => ?_, fun st r1 hws _ => ?_⟩
  · obtain ⟨v, ys, hv, hR, he⟩ := key _ hws; cases he; exact ⟨v, r, rfl, hv, hR⟩
  · obtain ⟨_, _, _, _, he⟩ := key _ hws; cases he

theorem call_ok {P cx cxe res k Kont i as} (H : Hyp P cx cxe res k Kont)
    (hall : ∀ a ∈ as, NodeOK P cx cxe res k Kont a) : NodeOK P cx cxe res k Kont (.call i as) := by
  intro bs exp x sh env venv he hr hfu
  unfold emit at he
  rcases hd : cxe.defs[i]? with _ | d <;> rw [hd] at he <;> simp only [bind, Option.bind] at he
  · cases he
  rcases hxs : args cxe bs d.params as with _ | xs <;> rw [hxs] at he <;> simp only [bind, Option.bind] at he
  · cases he
  simp at he; obtain ⟨rfl, rfl⟩ := he
  have key : ∀ q, ev cx (Na.erase (.call i as)) env = .ok q →
      ∃ v ys, Ev P venv (apps (.c (nameS d.name) []) xs) v ∧ R d.res v ys ∧ q = .inl ys := by
    intro q hq
    obtain ⟨ws, f, ys, h1, hf, h2, rfl⟩ := ev_call (by simpa [Na.erase] using hq)
    obtain ⟨vs, hvs, hA⟩ := args_ok d.params as hall bs xs env venv hxs hr hfu ws h1
    obtain ⟨v, ⟨body, b, hl, hs, hb⟩, hR⟩ := H.defs i f d hf hd ws ys vs h2 hA
    exact ⟨v, ys, Ev.call hvs hl hs hb, hR, rfl⟩
  refine ⟨fun ws hws => ?_, fun st r1 hws _ => ?_⟩
  · obtain ⟨v, ys, hv, hR, he⟩ := key _ hws; cases he; exact ⟨v, d.res, rfl, hv, hR⟩
  · obtain ⟨_, _, _, _, he⟩ := key _ hws; cases he

theorem loop_ok {P cx cxe res k Kont z s} : NodeOK P cx cxe res k Kont (.loop z s) := by
  intro bs exp x sh env venv he; unfold emit at he; cases he

/-- states that are all the input: their argument Exprs evaluate to `.l inp`, no words -/
theorem allInp_args {P inp venv bs x} (hi : ∀ y, inpX bs = some y → Ev P venv y (.l inp)) :
    ∀ (sps : List Ps) xs, sps.filter (· != .inp) = [] →
      sps.mapM (fun q => if q == .inp then inpX bs else some x) = some xs → ∃ vs, EvL P venv xs vs ∧ ArgsR inp sps vs []
  | [], xs, _, h => by simp at h; subst h; exact ⟨[], .nil, .nil⟩
  | q :: sps, xs, hf, h => by
    by_cases hq : q = .inp
    · subst hq
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false] at hf
      simp only [List.mapM_cons, beq_self_eq_true, ite_true, bind, Option.bind] at h
      rcases h2 : sps.mapM (fun q => if q == .inp then inpX bs else some x) with _ | ys <;> rw [h2] at h
      · rcases h1 : inpX bs with _ | y <;> rw [h1] at h <;> simp at h
      rcases h1 : inpX bs with _ | y <;> rw [h1] at h <;> simp at h
      subst h
      obtain ⟨vs, hvs, hA⟩ := allInp_args hi sps ys hf h2
      exact ⟨_, .cons (hi y h1) hvs, .inp hA⟩
    · simp [List.filter_cons, hq] at hf

theorem single_args {P inp venv bs x v ws p} (hi : ∀ y, inpX bs = some y → Ev P venv y (.l inp))
    (hx : Ev P venv x v) (hR : R (psSh p) v ws) :
    ∀ (sps : List Ps) xs, (sps.filter (· != .inp)).length = 1 → sps.find? (· != .inp) = some p →
      sps.mapM (fun q => if q == .inp then inpX bs else some x) = some xs → ∃ vs, EvL P venv xs vs ∧ ArgsR inp sps vs ws
  | [], xs, h, _, _ => by simp at h
  | q :: sps, xs, hl, hf, h => by
    by_cases hq : q = .inp
    · subst hq
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false] at hl
      simp only [List.find?_cons, bne_self_eq_false] at hf
      simp only [List.mapM_cons, beq_self_eq_true, ite_true, bind, Option.bind] at h
      rcases h2 : sps.mapM (fun q => if q == .inp then inpX bs else some x) with _ | ys <;> rw [h2] at h
      · rcases h1 : inpX bs with _ | y <;> rw [h1] at h <;> simp at h
      rcases h1 : inpX bs with _ | y <;> rw [h1] at h <;> simp at h
      subst h
      obtain ⟨vs, hvs, hA⟩ := single_args hi hx hR sps ys hl hf h2
      exact ⟨_, .cons (hi y h1) hvs, .inp hA⟩
    · have hq' : (q != .inp) = true := by simpa using hq
      simp only [List.find?_cons, hq', Option.some.injEq] at hf; subst hf
      simp only [List.filter_cons, hq', ite_true, List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff] at hl
      have hqi : (q == .inp) = false := by simpa using hq
      simp only [List.mapM_cons, hqi, Bool.false_eq_true, ite_false, bind, Option.bind] at h
      rcases h2 : sps.mapM (fun q => if q == .inp then inpX bs else some x) with _ | ys <;> rw [h2] at h <;> simp at h
      subst h
      obtain ⟨vs, hvs, hA⟩ := allInp_args hi sps ys hl h2
      exact ⟨v :: vs, .cons hx hvs, by simpa using ArgsR.sh hq hR hA⟩

theorem cont_ok {P cx cxe res k Kont e} (H : Hyp P cx cxe res k Kont) (he0 : NodeOK P cx cxe res k Kont e)
    (hcs : ∀ cs, e = .pair cs → ∀ a ∈ cs, NodeOK P cx cxe res k Kont a) : NodeOK P cx cxe res k Kont (.cont e) := by
  intro bs exp x sh env venv he hr hfu
  have hi : ∀ y, inpX bs = some y → Ev P venv y (.l cx.inp) := fun y hy => by
    obtain ⟨i, rfl, hv⟩ := inpX_R hr hy; exact .bv hv
  refine ⟨fun ws hws => ?_, fun st r hws hk => ?_⟩
  · obtain ⟨_, _, h⟩ := ev_cont (by simpa [Na.erase] using hws); cases h
  obtain ⟨x0, hx0, hst⟩ := ev_cont (by simpa [Na.erase] using hws)
  have hst : st = x0 := by simpa using hst
  subst hst
  unfold emit at he
  rcases hself : cxe.self with ⟨n, sps⟩
  rw [hself] at he; simp only at he
  rcases hfi : findB (fun b => b.2 == .fuel) bs with _ | fi <;> rw [hfi] at he <;> simp only [bind, Option.bind] at he
  · cases he
  have hfv := hfu fi hfi
  split at he
  · rename_i hlen
    rcases hp : sps.find? (· != .inp) with _ | p <;> rw [hp] at he <;> simp only [bind, Option.bind] at he
    · cases he
    rcases hee : emit cxe bs (some (psSh p)) e with _ | ⟨xe, sx⟩ <;> rw [hee] at he <;> simp only [bind, Option.bind] at he
    · cases he
    split at he
    · cases he
    rename_i hsx; have hsx := Decidable.not_not.mp hsx; subst hsx
    rcases hm : sps.mapM (fun q => if q == .inp then inpX bs else some xe) with _ | xs <;> rw [hm] at he <;> simp at he
    obtain ⟨rfl, -⟩ := he
    obtain ⟨v, s', hs', hv, hR⟩ := (he0 bs _ _ _ env venv hee hr hfu).1 _ hx0
    cases hs'
    obtain ⟨vs, hvs, hA⟩ := single_args hi hv hR sps xs hlen hp hm
    obtain ⟨v', ⟨body, b, hl, hs, hb⟩, hR'⟩ := H.kont st r vs hk (by rw [hself]; exact hA)
    rw [hself] at hl
    exact ⟨v', Ev.call (.cons (.bv hfv) hvs) hl hs hb, hR'⟩
  · cases e with
    | pair cs =>
      simp only at he
      rcases hxs : args cxe bs sps cs with _ | xs <;> rw [hxs] at he <;> simp at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨ws, hws', hq⟩ := ev_pair (by simpa [Na.erase] using hx0)
      have hq : st = ws := by simpa using hq
      subst hq
      obtain ⟨vs, hvs, hA⟩ := args_ok sps cs (hcs cs rfl) bs xs env venv hxs hr hfu st hws'
      obtain ⟨v', ⟨body, b, hl, hs, hb⟩, hR'⟩ := H.kont st r vs hk (by rw [hself]; exact hA)
      rw [hself] at hl
      exact ⟨v', Ev.call (.cons (.bv hfv) hvs) hl hs hb, hR'⟩
    | _ => simp at he

/-! ## all nodes -/
mutual
theorem node_ok {P cx cxe res k Kont} (H : Hyp P cx cxe res k Kont) : ∀ e, NodeOK P cx cxe res k Kont e
  | .const v => const_ok v
  | .loc s w => loc_ok s w
  | .bin _ a b => bin_ok (node_ok H a) (node_ok H b)
  | .ite _ a b t e => ite_ok (node_ok H a) (node_ok H b) (node_ok H t) (node_ok H e)
  | .letE _ _ _ v b => let_ok (node_ok H v) (node_ok H b)
  | .pair [] => fun _ _ _ _ _ _ he => by unfold emit at he; cases he
  | .pair [a] => fun _ _ _ _ _ _ he => by unfold emit at he; cases he
  | .pair [a, b] => pair_ok (node_ok H a) (node_ok H b)
  | .pair (_ :: _ :: _ :: _) => fun _ _ _ _ _ _ he => by unfold emit at he; cases he
  | .call _ as => call_ok H (nodeL_ok H as)
  | .prim _ as => prim_ok H.inp (nodeL_ok H as)
  | .nil l => nil_ok l
  | .loop _ _ => loop_ok
  | .cont (.pair cs) => cont_ok H (node_ok H (.pair cs)) (fun cs' h => by cases h; exact nodeL_ok H cs)
  | .cont (.const v) => cont_ok H (node_ok H _) (fun _ h => by cases h)
  | .cont (.loc s w) => cont_ok H (node_ok H _) (fun _ h => by cases h)
  | .cont (.bin o a b) => cont_ok H (node_ok H _) (fun _ h => by cases h)
  | .cont (.ite c a b t e) => cont_ok H (node_ok H _) (fun _ h => by cases h)
  | .cont (.letE pr s w v b) => cont_ok H (node_ok H _) (fun _ h => by cases h)
  | .cont (.call i as) => cont_ok H (node_ok H _) (fun _ h => by cases h)
  | .cont (.prim p as) => cont_ok H (node_ok H _) (fun _ h => by cases h)
  | .cont (.nil l) => cont_ok H (node_ok H _) (fun _ h => by cases h)
  | .cont (.loop z s) => cont_ok H (node_ok H _) (fun _ h => by cases h)
  | .cont (.cont e) => cont_ok H (node_ok H _) (fun _ h => by cases h)
theorem nodeL_ok {P cx cxe res k Kont} (H : Hyp P cx cxe res k Kont) : ∀ (as : List Na), ∀ a ∈ as, NodeOK P cx cxe res k Kont a
  | [] => fun _ h => by cases h
  | a :: as => List.forall_mem_cons.2 ⟨node_ok H a, nodeL_ok H as⟩
end

/-! ## annotation keeps the IR -/
mutual
theorem annot_erase : ∀ (e : Nd) st b st', annot e st = some (b, st') → b.erase = e
  | .const v, st, b, st', h => by simp [annot] at h; obtain ⟨rfl, -⟩ := h; rfl
  | .loc s w, st, b, st', h => by simp [annot] at h; obtain ⟨rfl, -⟩ := h; rfl
  | .bin op a c, st, b, st', h => by
    simp only [annot, bind, Option.bind] at h
    rcases h1 : annot a st with _ | ⟨a', s1⟩ <;> rw [h1] at h <;> simp only at h
    · cases h
    rcases h2 : annot c s1 with _ | ⟨c', s2⟩ <;> rw [h2] at h <;> simp at h
    obtain ⟨rfl, -⟩ := h; simp [Na.erase, annot_erase a _ _ _ h1, annot_erase c _ _ _ h2]
  | .ite cm a c t e, st, b, st', h => by
    simp only [annot, bind, Option.bind] at h
    rcases h1 : annot a st with _ | ⟨a', s1⟩ <;> rw [h1] at h <;> simp only at h
    · cases h
    rcases h2 : annot c s1 with _ | ⟨c', s2⟩ <;> rw [h2] at h <;> simp only at h
    · cases h
    rcases h3 : annot t s2 with _ | ⟨t', s3⟩ <;> rw [h3] at h <;> simp only at h
    · cases h
    rcases h4 : annot e s3 with _ | ⟨e', s4⟩ <;> rw [h4] at h <;> simp at h
    obtain ⟨rfl, -⟩ := h
    simp [Na.erase, annot_erase a _ _ _ h1, annot_erase c _ _ _ h2, annot_erase t _ _ _ h3, annot_erase e _ _ _ h4]
  | .letE s w v c, ([], ns), b, st', h => by simp [annot] at h
  | .letE s w v c, (pr :: ls, ns), b, st', h => by
    simp only [annot, bind, Option.bind] at h
    rcases h1 : annot v (ls, ns) with _ | ⟨v', s1⟩ <;> rw [h1] at h <;> simp only at h
    · cases h
    rcases h2 : annot c s1 with _ | ⟨c', s2⟩ <;> rw [h2] at h <;> simp at h
    obtain ⟨rfl, -⟩ := h; simp [Na.erase, annot_erase v _ _ _ h1, annot_erase c _ _ _ h2]
  | .pair cs, st, b, st', h => by
    simp only [annot, bind, Option.bind] at h
    rcases h1 : annotL cs st with _ | ⟨cs', s1⟩ <;> rw [h1] at h <;> simp at h
    obtain ⟨rfl, -⟩ := h; simp [Na.erase, annotL_erase cs _ _ _ h1]
  | .call i as, st, b, st', h => by
    simp only [annot, bind, Option.bind] at h
    rcases h1 : annotL as st with _ | ⟨as', s1⟩ <;> rw [h1] at h <;> simp at h
    obtain ⟨rfl, -⟩ := h; simp [Na.erase, annotL_erase as _ _ _ h1]
  | .prim p as, st, b, st', h => by
    by_cases hp : p = 5 ∧ as = []
    · obtain ⟨rfl, rfl⟩ := hp
      rcases st with ⟨ls, _ | ⟨n, ns⟩⟩ <;> simp [annot] at h
      obtain ⟨rfl, -⟩ := h; rfl
    · have : annot (.prim p as) st = (do let (as', st) ← annotL as st; pure (.prim p as', st)) := by
        rcases as with _ | ⟨a, as⟩
        · have hp5 : p ≠ 5 := fun e => hp ⟨e, rfl⟩
          rcases st with ⟨ls, _ | ⟨n, ns⟩⟩ <;> simp [annot, hp5]
        · simp only [annot]
      rw [this] at h
      simp only [bind, Option.bind] at h
      rcases h1 : annotL as st with _ | ⟨as', s1⟩ <;> rw [h1] at h <;> simp at h
      obtain ⟨rfl, -⟩ := h; simp [Na.erase, annotL_erase as _ _ _ h1]
  | .loop z s, st, b, st', h => by
    simp only [annot, bind, Option.bind] at h
    rcases h1 : annot z st with _ | ⟨z', s1⟩ <;> rw [h1] at h <;> simp only at h
    · cases h
    rcases h2 : annot s s1 with _ | ⟨s', s2⟩ <;> rw [h2] at h <;> simp at h
    obtain ⟨rfl, -⟩ := h; simp [Na.erase, annot_erase z _ _ _ h1, annot_erase s _ _ _ h2]
  | .cont e, st, b, st', h => by
    simp only [annot, bind, Option.bind] at h
    rcases h1 : annot e st with _ | ⟨e', s1⟩ <;> rw [h1] at h <;> simp at h
    obtain ⟨rfl, -⟩ := h; simp [Na.erase, annot_erase e _ _ _ h1]
theorem annotL_erase : ∀ (as : List Nd) st bs st', annotL as st = some (bs, st') → Na.eraseL bs = as
  | [], st, bs, st', h => by simp [annotL] at h; obtain ⟨rfl, -⟩ := h; rfl
  | a :: as, st, bs, st', h => by
    simp only [annotL, bind, Option.bind] at h
    rcases h1 : annot a st with _ | ⟨a', s1⟩ <;> rw [h1] at h <;> simp only at h
    · cases h
    rcases h2 : annotL as s1 with _ | ⟨as', s2⟩ <;> rw [h2] at h <;> simp at h
    obtain ⟨rfl, -⟩ := h; simp [Na.eraseL, annot_erase a _ _ _ h1, annotL_erase as _ _ _ h2]
end

/-! ## parameters -/
theorem ArgsR.len {inp} : ∀ {ps vs ws}, ArgsR inp ps vs ws → vs.length = ps.length
  | _, _, _, .nil => rfl
  | _, _, _, .inp h => by simp [h.len]
  | _, _, _, .sh _ _ h => by simp [h.len]

theorem strip_lamX : ∀ (ps : List Ps) (b : X), strip ps.length (lamX ps b) = some b
  | [], b => rfl
  | p :: ps, b => by simp [lamX, strip] at *; exact strip_lamX ps b

theorem binders_len : ∀ (s : Nat) (ps : List Ps) (bs : Bs), (binders s ps bs).length = ps.length + bs.length
  | _, [], _ => by simp [binders]
  | s, p :: ps, bs => by simp [binders, binders_len _ ps]; omega

theorem binders_slot : ∀ (s0 : Nat) (ps : List Ps) (bs0 : Bs), ∀ b ∈ binders s0 ps bs0, b ∈ bs0 ∨ s0 ≤ b.1
  | _, [], _, b, h => .inl (by simpa [binders] using h)
  | s0, p :: ps, bs0, b, h => by
    simp only [binders] at h
    rcases binders_slot _ ps _ b h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr (Nat.le_refl _)
      · exact .inl h
    · exact .inr (by omega)

theorem psSh_width : ∀ {p : Ps}, p ≠ .inp → (psSh p).width = p.width
  | .inp, h => absurd rfl h
  | .fuel, _ => rfl
  | .sh _, _ => rfl

theorem params_env {inp} : ∀ {ps vs ws}, ArgsR inp ps vs ws → ∀ (s0 : Nat) (bs0 : Bs) (venv0 : List V) (env : List W),
    (env.drop s0).take ws.length = ws → EnvR inp env bs0 venv0 → EnvR inp env (binders s0 ps bs0) (vs.reverse ++ venv0)
  | _, _, _, .nil, s0, bs0, venv0, env, _, h => by simpa [binders] using h
  | _, _, ws, .inp (ps := ps) (vs := vs) hA, s0, bs0, venv0, env, hw, h => by
    simp only [binders, List.reverse_cons, List.append_assoc, List.singleton_append]
    have := params_env hA (s0 + Ps.width .inp) ((s0, .inp) :: bs0) (.l inp :: venv0) env (by simpa [Ps.width] using hw) (.inp h)
    exact this
  | _, _, _, .sh (p := p) (ps := ps) (v := v) (vs := vs) (xs := xs) (ws := ws) hp hR hA, s0, bs0, venv0, env, hw, h => by
    simp only [binders, List.reverse_cons, List.append_assoc, List.singleton_append]
    obtain ⟨h1, h2⟩ := take_split hw
    have hlen : xs.length = p.width := by rw [hR.len, psSh_width hp]
    have hhead : EnvR inp env ((s0, p) :: bs0) (v :: venv0) := by
      cases p with
      | inp => exact absurd rfl hp
      | fuel => cases hR; exact .fuel h
      | sh sh => simp only [psSh] at hR; exact .sh (by rw [← hR.len, h1]; exact hR) h
    refine params_env hA (s0 + p.width) _ _ env ?_ hhead
    rw [← List.drop_drop, ← hlen]; exact h2

theorem fuel_exists {inp env} : ∀ {bs venv}, EnvR inp env bs venv → ∃ k, FuelAt bs venv k
  | _, _, .nil => ⟨0, fun fi h => by simp [findB] at h⟩
  | _, _, .inp h => by
    obtain ⟨k, hk⟩ := fuel_exists h
    refine ⟨k, fun fi hf => ?_⟩
    simp [findB] at hf; obtain ⟨j, hj, rfl⟩ := hf; simpa using hk j hj
  | _, _, .fuel (k := k) h => ⟨k, fun fi hf => by simp [findB] at hf; subst hf; rfl⟩
  | _, _, .sh _ h => by
    obtain ⟨k, hk⟩ := fuel_exists h
    exact ⟨k, hk.push⟩

theorem setSlots_frame_above {env env' : List W} {s : Nat} {x : List W} (h : setSlots env s x = .ok env')
    {s' w : Nat} (hle : s + x.length ≤ s') : (env'.drop s').take w = (env.drop s').take w := by
  unfold setSlots at h
  split at h
  · rename_i hk; simp at h; subst h
    have hl : (env.take s ++ x).length = s + x.length := by simp; omega
    rw [← List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by rw [hl]; omega),
      List.nil_append, hl, List.drop_drop, show s + x.length + (s' - (s + x.length)) = s' by omega]
  · cases h

/-- writes at slots below every value binder keep the binders' values (input / fuel binders have none) -/
theorem EnvR.frame_above {inp env env' s x} (hs : setSlots env s x = .ok env') :
    ∀ {bs venv}, (∀ b ∈ bs, (∃ sh, b.2 = .sh sh) → s + x.length ≤ b.1) → EnvR inp env bs venv → EnvR inp env' bs venv
  | _, _, _, .nil => .nil
  | _, _, hf, .inp h => .inp (h.frame_above hs (fun b hb => hf b (by simp [hb])))
  | _, _, hf, .fuel h => .fuel (h.frame_above hs (fun b hb => hf b (by simp [hb])))
  | (s', .sh sh0) :: bs', v' :: venv', hf, .sh h0 h => by
    refine .sh ?_ (h.frame_above hs (fun b hb => hf b (by simp [hb])))
    have hle : s + x.length ≤ s' := hf (s', .sh sh0) (by simp) ⟨sh0, rfl⟩
    rw [setSlots_frame_above hs hle]; exact h0

/-! ## defs -/
theorem loopRun_zero {fz fs : List W → Out} {env r} (h : loopRun fz fs 0 env = .ok r) : fz env = .ok (.inl r) := by
  simp only [loopRun] at h; exact val_ok.1 h

theorem loopRun_succ {fz fs : List W → Out} {m env r} (h : loopRun fz fs (m + 1) env = .ok r) :
    ∃ env1, setSlots env 0 [.w (UInt64.ofNat m)] = .ok env1 ∧
      (fs env1 = .ok (.inl r) ∨ ∃ st env2, fs env1 = .ok (.inr st) ∧ setSlots env1 1 st = .ok env2 ∧ loopRun fz fs m env2 = .ok r) := by
  simp only [loopRun] at h
  rcases h1 : setSlots env 0 [.w (UInt64.ofNat m)] with _ | env1 <;> rw [h1] at h <;> (try evsimp at h) <;> try cases h
  refine ⟨env1, rfl, ?_⟩
  rcases h2 : fs env1 with _ | (v | st) <;> rw [h2] at h <;> (try evsimp at h) <;> try cases h
  · exact .inl rfl
  · rcases h3 : setSlots env1 1 st with _ | env2 <;> rw [h3] at h <;> (try evsimp at h) <;> try cases h
    exact .inr ⟨st, env2, rfl, h3, h⟩

theorem ev_loop {cx z s env r} (h : ev cx (.loop z s) env = .ok r) :
    ∃ n rest r', env = .w n :: rest ∧ loopRun (fun e => ev cx z e) (fun e => ev cx s e) n.toNat env = .ok r' ∧ r = .inl r' := by
  simp only [ev] at h
  split at h
  · rename_i n rest
    rcases h1 : loopRun (fun e => ev cx z e) (fun e => ev cx s e) n.toNat (.w n :: rest) with _ | r' <;>
      rw [h1] at h <;> (try evsimp at h) <;> try cases h
    exact ⟨n, rest, r', rfl, h1, rfl⟩
  · cases h

/-- callee meanings for a def list -/
def DefsHyp (P : Prog) (cx : Ctx) (ds : List DefI) : Prop :=
  ∀ (i : Nat) (f : List W → Except Stop (List W)) (d : DefI), cx.defs[i]? = some f → ds[i]? = some d →
    ∀ ws r vs, f ws = .ok r → ArgsR cx.inp d.params vs ws → ∃ v, EvCall P (nameS d.name) vs v ∧ R d.res v r

/-- a fuel loop: at fuel m, from any slot environment whose parameter slots hold the states -/
theorem fuelLoop_ok {P : Prog} {cx : Ctx} {ds : List DefI} {di : DefI} {sps : List Ps} {z s : Na} {zx sx : X} {zs ss : Option Sh}
    (hin : cx.inp.length < 2 ^ 64) (hdefs : DefsHyp P cx ds) (hps : di.params = .fuel :: sps)
    (hz : emit ⟨ds, (nameS di.name, di.params.drop 1)⟩ (binders 0 di.params []) (some di.res) z = some (zx, zs))
    (hs : emit ⟨ds, (nameS di.name, di.params.drop 1)⟩ ((0, .fuel) :: binders 0 di.params []) (some di.res) s = some (sx, ss))
    (hzs : agree di.res zs = true) (hss : agree di.res ss = true)
    (hl : P.lookup (nameS di.name) = some (lamX di.params (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy di.res),
      .bv ((binders 0 di.params []).length - 1), zx, .lam (.c "Nat" []) sx]))) :
    ∀ (m : Nat) (env : List W) (svs : List V) (r : List W), EnvR cx.inp env (binders 0 di.params []) (svs.reverse ++ [.n m]) → svs.length = sps.length →
      loopRun (fun e => ev cx z.erase e) (fun e => ev cx s.erase e) m env = .ok r →
      ∃ v, Ev P (svs.reverse ++ [.n m]) (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy di.res),
        .bv ((binders 0 di.params []).length - 1), zx, .lam (.c "Nat" []) sx]) v ∧ R di.res v r := by
  have hidx : ∀ (svs : List V) (m : Nat), svs.length = sps.length →
      (svs.reverse ++ [V.n m])[(binders 0 di.params []).length - 1]? = some (.n m) := by
    intro svs m h; rw [binders_len, hps]; simp [List.getElem?_append_right, h]
  have hdefs' : ∀ k Kont, (∀ st r vs, Kont st = .ok r → ArgsR cx.inp (di.params.drop 1) vs st →
      ∃ v, EvCall P (nameS di.name) (.n k :: vs) v ∧ R di.res v r) →
      Hyp P cx ⟨ds, (nameS di.name, di.params.drop 1)⟩ di.res k Kont :=
    fun k Kont hk => ⟨hin, hdefs, hk⟩
  intro m
  induction m with
  | zero =>
    intro env svs r hr hsv hrun
    have h0 := loopRun_zero hrun
    obtain ⟨k, hk⟩ := fuel_exists hr
    obtain ⟨v, s', hs', hv, hR⟩ := (node_ok (hdefs' k (fun _ => .error .stuck) (fun _ _ _ h => by cases h)) z
      _ _ _ _ env _ hz hr hk).1 _ h0
    exact ⟨v, Ev.natZ (.bv (hidx svs 0 hsv)) hv, (agree_eq hzs hs') ▸ hR⟩
  | succ m ih =>
    intro env svs r hr hsv hrun
    obtain ⟨env1, h1, hcase⟩ := loopRun_succ hrun
    have hbig : ∀ b ∈ binders 0 di.params [], (∃ sh, b.2 = .sh sh) → 0 + [W.w (UInt64.ofNat m)].length ≤ b.1 := by
      intro b hb ⟨sh, hsh⟩
      rw [hps] at hb; simp only [binders] at hb
      rcases binders_slot 1 sps [(0, .fuel)] b hb with h | h
      · simp at h; rw [h] at hsh; cases hsh
      · simpa using h
    have hr1 : EnvR cx.inp env1 ((0, .fuel) :: binders 0 di.params []) (.n m :: (svs.reverse ++ [.n (m + 1)])) :=
      .fuel (hr.frame_above h1 hbig)
    have hfu : FuelAt ((0, .fuel) :: binders 0 di.params []) (.n m :: (svs.reverse ++ [.n (m + 1)])) m :=
      fun fi hf => by simp [findB] at hf; subst hf; rfl
    let Kont : List W → Except Stop (List W) := fun st => (setSlots env1 1 st).bind
      (loopRun (fun e => ev cx z.erase e) (fun e => ev cx s.erase e) m)
    have hK : ∀ st r vs, Kont st = .ok r → ArgsR cx.inp (di.params.drop 1) vs st →
        ∃ v, EvCall P (nameS di.name) (.n m :: vs) v ∧ R di.res v r := by
      intro st r vs hk hA
      simp only [Kont] at hk
      rcases h2 : setSlots env1 1 st with _ | env2 <;> rw [h2] at hk <;> simp only [Except.bind] at hk
      · cases hk
      rw [hps] at hA; simp only [List.drop_succ_cons, List.drop_zero] at hA
      have henv2 : EnvR cx.inp env2 (binders 0 di.params []) (vs.reverse ++ [.n m]) := by
        rw [hps]; simp only [binders]
        exact params_env hA 1 [(0, .fuel)] [.n m] env2 (by simpa using setSlots_at h2) (.fuel .nil)
      obtain ⟨v, hv, hR⟩ := ih env2 vs r henv2 hA.len hk
      refine ⟨v, ⟨_, _, hl, ?_, by simpa using hv⟩, hR⟩
      have : (V.n m :: vs).length = di.params.length := by rw [hps]; simp [hA.len]
      rw [this]; exact strip_lamX _ _
    have H := hdefs' m Kont hK
    rcases hcase with hv | ⟨st, env2, hv, h2, hrest⟩
    · obtain ⟨v, s', hs', hev, hR⟩ := (node_ok H s _ _ _ _ env1 _ hs hr1 hfu).1 _ hv
      exact ⟨v, Ev.natS (.bv (hidx svs (m + 1) hsv)) hev, (agree_eq hss hs') ▸ hR⟩
    · obtain ⟨v, hev, hR⟩ := (node_ok H s _ _ _ _ env1 _ hs hr1 hfu).2 st r hv (by simp [Kont, h2, Except.bind, hrest])
      exact ⟨v, Ev.natS (.bv (hidx svs (m + 1) hsv)) hev, hR⟩

theorem defMean_ok {inp κ ms d ws r} (h : defMean inp κ ms d ws = .ok r) :
    ev ⟨inp, κ, ms⟩ d.body (ws ++ List.replicate (d.nslots - d.npw) (.w 0)) = .ok (.inl r) := by
  simp only [defMean] at h
  split at h
  · rcases h1 : ev ⟨inp, κ, ms⟩ d.body (ws ++ List.replicate (d.nslots - d.npw) (.w 0)) with _ | (v | v) <;>
      rw [h1] at h <;> (try evsimp at h) <;> try cases h
    split at h
    · simp at h; subst h; exact h1
    · cases h
  · cases h

/-- **a def's meaning**: Sem's meaning of a def = the meaning of its emitted Expr, called on related arguments -/
theorem def_ok {P : Prog} {inp : List UInt8} {κ : Nat} {ms : List (List W → Except Stop (List W))} {ds : List DefI}
    {di : DefI} {da : DefA} {b : Na} {t val : X} (hin : inp.length < 2 ^ 64) (hdefs : DefsHyp P ⟨inp, κ, ms⟩ ds)
    (hb : b.erase = da.body) (he : emitDef ds di b = some (t, val)) (hl : P.lookup (nameS di.name) = some val) :
    ∀ ws r vs, defMean inp κ ms da ws = .ok r → ArgsR inp di.params vs ws →
      ∃ v, EvCall P (nameS di.name) vs v ∧ R di.res v r := by
  intro ws r vs hm hA
  have hev := defMean_ok hm
  rw [← hb] at hev
  have henv : EnvR inp (ws ++ List.replicate (da.nslots - da.npw) (.w 0)) (binders 0 di.params []) vs.reverse := by
    simpa using params_env hA 0 [] [] _ (by simp) .nil
  have hstrip : ∀ x, strip vs.length (lamX di.params x) = some x := fun x => by rw [hA.len]; exact strip_lamX _ x
  by_cases hlp : ∃ z s, b = .loop z s
  · obtain ⟨z, s, rfl⟩ := hlp
    unfold emitDef at he
    simp only at he
    split at he
    · cases he
    rename_i hhd
    rcases hz : emit ⟨ds, (nameS di.name, di.params.drop 1)⟩ (binders 0 di.params []) (some di.res) z with _ | ⟨zx, zs⟩ <;>
      rw [hz] at he <;> simp only [bind, Option.bind] at he
    · cases he
    rcases hs : emit ⟨ds, (nameS di.name, di.params.drop 1)⟩ ((0, .fuel) :: binders 0 di.params []) (some di.res) s with _ | ⟨sx, ss⟩ <;>
      rw [hs] at he <;> simp only [bind, Option.bind] at he
    · cases he
    split at he
    · rename_i hc; simp at he; obtain ⟨-, rfl⟩ := he
      obtain ⟨hzs, hss, -⟩ := hc
      obtain ⟨sps, hps⟩ : ∃ sps, di.params = .fuel :: sps := by
        rcases h : di.params with _ | ⟨p, sps⟩
        · rw [h] at hhd; simp at hhd
        · rw [h] at hhd; simp at hhd; subst hhd; exact ⟨sps, rfl⟩
      rw [hps] at hA
      rcases hA with _ | _ | @⟨p, ps, v0, svs, xs, ws', hp0, h0, hA'⟩
      rcases h0 with _ | _ | _ | @⟨k, u, hu⟩
      obtain ⟨n, rest, r', henv0, hrun, hr⟩ := ev_loop (by simpa [Na.erase] using hev)
      simp only [List.cons_append, List.nil_append, List.cons.injEq, W.w.injEq] at henv0
      obtain ⟨hun, hrest⟩ := henv0
      subst hun; cases hr
      have henv' : EnvR inp (W.w u :: (ws' ++ List.replicate (da.nslots - da.npw) (.w 0))) (binders 0 di.params [])
          (svs.reverse ++ [.n u.toNat]) := by
        rw [hu]; simpa using henv
      obtain ⟨v, hv, hR⟩ := fuelLoop_ok hin hdefs hps hz hs hzs hss hl u.toNat _ svs r henv' hA'.len
        (by subst hrest; simpa using hrun)
      have hstr := strip_lamX di.params (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy di.res),
        .bv ((binders 0 di.params []).length - 1), zx, .lam (.c "Nat" []) sx])
      have hlen : (V.n k :: svs).length = di.params.length := by rw [hps]; simp [hA'.len]
      rw [← hlen] at hstr
      exact ⟨v, ⟨_, _, hl, hstr, by rw [← hu]; simpa using hv⟩, hR⟩
    · cases he
  · have he' : (do
        let (bx, bsh) ← emit ⟨ds, (nameS di.name, di.params.drop 1)⟩ (binders 0 di.params []) (some di.res) b
        if bsh = some di.res then some (piX di.params (shTy di.res), lamX di.params bx) else none) = some (t, val) := by
      cases b with
      | loop z s => exact absurd ⟨z, s, rfl⟩ hlp
      | _ => unfold emitDef at he; exact he
    rcases heb : emit ⟨ds, (nameS di.name, di.params.drop 1)⟩ (binders 0 di.params []) (some di.res) b with _ | ⟨bx, bsh⟩ <;>
      rw [heb] at he' <;> simp only [bind, Option.bind] at he'
    · cases he'
    split at he'
    · rename_i hbs; simp at he'; obtain ⟨-, rfl⟩ := he'
      obtain ⟨k, hk⟩ := fuel_exists henv
      have H : Hyp P ⟨inp, κ, ms⟩ ⟨ds, (nameS di.name, di.params.drop 1)⟩ di.res k (fun _ => .error .stuck) :=
        ⟨hin, hdefs, fun _ _ _ h => by cases h⟩
      obtain ⟨v, s', hs', hv, hR⟩ := (node_ok H b _ _ _ _ _ _ heb henv hk).1 _ hev
      rw [hbs] at hs'; cases hs'
      exact ⟨v, ⟨_, _, hl, hstrip bx, hv⟩, hR⟩
    · cases he'

/-! ## programs -/
/-- the program table of emitted defs -/
def progOf (o : List (String × X × X)) : Prog := o.map fun e => (e.1, e.2.2)

theorem lookup_of_mem {o : List (String × X × X)} (hnd : (o.map (·.1)).Nodup) :
    ∀ {n t v}, (n, t, v) ∈ o → (progOf o).lookup n = some v := by
  induction o with
  | nil => intro _ _ _ h; cases h
  | cons e o ih =>
    intro n t v h
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [progOf, List.map_cons, List.lookup_cons]
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have hne : (n == e.1) = false := by
        simp only [beq_eq_false_iff_ne]; intro he; apply hnd.1; rw [← he]; exact List.mem_map.2 ⟨_, h, rfl⟩
      rw [hne]; exact ih hnd.2 h

theorem prog_inv {P : Prog} {inp : List UInt8} {κ : Nat} {ds : List DefI} (hin : inp.length < 2 ^ 64) :
    ∀ (as : List DefA) (j : Nat) (ms : List (List W → Except Stop (List W))) (st : Sd) (o' : List (String × X × X)),
      emitAll ds j as st = some o' → (∀ n t v, (n, t, v) ∈ o' → P.lookup n = some v) → ms.length = j →
      DefsHyp P ⟨inp, κ, ms⟩ ds →
      (means inp κ ms as).length = j + as.length ∧ DefsHyp P ⟨inp, κ, means inp κ ms as⟩ ds
  | [], j, ms, st, o', _, _, hl, hd => by simpa [means] using ⟨hl, hd⟩
  | da :: as, j, ms, st, o', he, hlk, hl, hd => by
    unfold emitAll at he
    split at he
    · cases he
    rename_i hid
    rcases ha : annot da.body st with _ | ⟨b, st1⟩ <;> rw [ha] at he <;> simp only [bind, Option.bind] at he
    · cases he
    rcases hdi : ds[j]? with _ | di <;> rw [hdi] at he <;> simp only at he
    · cases he
    rcases hed : emitDef ds di b with _ | ⟨t, v⟩ <;> rw [hed] at he <;> simp only at he
    · cases he
    rcases hrest : emitAll ds (j + 1) as st1 with _ | o2 <;> rw [hrest] at he <;> simp only at he
    · cases he
    simp at he; subst he
    have hthis := def_ok (P := P) (κ := κ) (ms := ms) hin hd (annot_erase _ _ _ _ ha) hed (hlk _ t _ (by simp))
    have hd' : DefsHyp P ⟨inp, κ, ms ++ [defMean inp κ ms da]⟩ ds := by
      intro i f d hf hdd ws r vs hfr hA
      simp only at hf
      by_cases hij : i < ms.length
      · rw [List.getElem?_append_left hij] at hf; exact hd i f d hf hdd ws r vs hfr hA
      · have hi : i = ms.length := by
          have := (List.getElem?_eq_some_iff.1 hf).1; simp at this; omega
        subst hi
        rw [List.getElem?_append_right (by omega)] at hf; simp at hf; subst hf
        rw [hl, hdi] at hdd; cases hdd
        exact hthis ws r vs hfr hA
    obtain ⟨h1, h2⟩ := prog_inv hin as (j + 1) _ st1 o2 hrest (fun n t v h => hlk n t v (by simp [h])) (by simp [hl]) hd'
    simp only [means]
    exact ⟨by rw [h1]; simp; omega, h2⟩

/-- **eval_emit**: for a program whose Exprs `emitAll` produces (distinct names; the last def is `m (x : List UInt8)
: List UInt8`), every output Sem computes on an input is the meaning `Ev` of the emitted Expr of `m` applied to the
input -/
theorem eval_emit {ds : List DefI} {p : List DefA} {st : Sd} {o : List (String × X × X)} {inp : List UInt8} {κ : Nat}
    {out : List UInt8} {dm : DefI}
    (he : emitAll ds 0 p st = some o) (hnd : (o.map (·.1)).Nodup) (hin : inp.length < 2 ^ 64)
    (hm : ds[p.length - 1]? = some dm) (hmn : dm.name = [109]) (hmp : dm.params = [.inp]) (hmr : dm.res = .ls)
    (hs : Sem κ p inp = .ok out) : Ev (progOf o) [.l inp] (.app (.c "m" []) (.bv 0)) (.l out) := by
  have hP : ∀ n t v, (n, t, v) ∈ o → (progOf o).lookup n = some v := fun n t v h => lookup_of_mem hnd h
  obtain ⟨hlen, hdefs⟩ := prog_inv (P := progOf o) (κ := κ) hin p 0 [] st o he hP rfl
    (fun i f d h => by simp at h)
  simp only [Sem] at hs
  rcases hlast : (means inp κ [] p).getLast? with _ | f <;> rw [hlast] at hs <;> simp only at hs
  · cases hs
  rcases hf : f [] with _ | r <;> rw [hf] at hs
  · cases hs
  rcases r with _ | ⟨_ | l, _ | _⟩ <;> simp at hs
  have hfi : (means inp κ [] p)[p.length - 1]? = some f := by
    rw [List.getLast?_eq_getElem?] at hlast; simpa [hlen] using hlast
  obtain ⟨v, ⟨body, b, hl, hst, hev⟩, hR⟩ := hdefs (p.length - 1) f dm hfi hm [] [.b l] [.l inp] hf
    (by rw [hmp]; exact .inp .nil)
  rw [hmr] at hR
  rcases hR with _ | _ | ⟨ho⟩
  rw [hmn] at hl
  have : nameS [109] = "m" := by decide
  rw [this] at hl
  rw [← hs, ho]
  exact Ev.call (as := [.bv 0]) (.cons (.bv rfl) .nil) hl hst hev

end ExprSpec
