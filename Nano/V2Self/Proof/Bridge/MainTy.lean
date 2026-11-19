/- Nano/V2Self/Proof/Bridge/MainTy: a kind discipline for resolved ASTs (`ParSpec.Nd`) and PROGRESS for `NanoMain.Sem`:
a well-kinded program never evaluates to `.error .stuck` (only to a value or the capacity stop).
Kinds: `w` (word) / `b` (buffer).  `Γ : List (Option Kd)` = what each slot is known to hold (`none`: not readable,
e.g. a let slot before its let, or after a loop iteration).  `S` = the CONTINUE payload kinds allowed here
(`some sk` in a loop's step arm, else `none`).  Second half (to do): ParSpec's parser only produces well-kinded programs. -/
import Nano.V2Self.Proof.Main.Sem

namespace NanoMain
open ParSpec

inductive Kd | w | b deriving DecidableEq, Repr

def W.k : W → Kd | .w _ => .w | .b _ => .b
def kOf (l : List W) : List Kd := l.map W.k

/-- prim signatures on kinds (input dropped) -/
def primK : Nat → List Kd → Option (List Kd)
  | 1, [] => some [.w] | 2, [.w] => some [.w] | 3, [] => some [.w] | 4, [.b, .w] => some [.b]
  | 5, [] => some [.b] | 6, [.b] => some [.w] | 7, [.b, .w] => some [.w] | 8, [.b, .w, .w] => some [.b]
  | 9, [.b, .w] => some [.b] | _, _ => none

def setK (Γ : List (Option Kd)) (s : Nat) (ks : List Kd) : List (Option Kd) :=
  Γ.take s ++ ks.map some ++ Γ.drop (s + ks.length)

/-- the slot reads of `loc s w` are all known -/
def known (Γ : List (Option Kd)) (s w : Nat) (ks : List Kd) : Prop :=
  s + w ≤ Γ.length ∧ (Γ.drop s).take w = ks.map some

/-- signatures of callable defs: (parameter kinds, result kinds) -/
abbrev Sig := List Kd × List Kd

mutual
inductive TyN (D : List Sig) : List (Option Kd) → Option (List Kd) → Nd → List Kd → Prop
  | const {Γ S v} : TyN D Γ S (.const v) [.w]
  | loc {Γ S s w ks} : known Γ s w ks → TyN D Γ S (.loc s w) ks
  | bin {Γ S op a b} : 1 ≤ op → op ≤ 8 → TyN D Γ none a [.w] → TyN D Γ none b [.w] → TyN D Γ S (.bin op a b) [.w]
  | ite {Γ S c a b t e ks} : (c = 1 ∨ c = 2) → TyN D Γ none a [.w] → TyN D Γ none b [.w] →
      TyN D Γ S t ks → TyN D Γ S e ks → TyN D Γ S (.ite c a b t e) ks
  | letE {Γ S s w v b vs ks} : TyN D Γ none v vs → vs.length = w → s + w ≤ Γ.length →
      (∀ k, s ≤ k → k < s + w → Γ[k]? = some none) →
      TyN D (setK Γ s vs) S b ks → TyN D Γ S (.letE s w v b) ks
  | pair {Γ S cs ks} : TyL D Γ cs ks → TyN D Γ S (.pair cs) ks
  | call {Γ S i as ps rs} : TyL D Γ as ps → D[i]? = some (ps, rs) → TyN D Γ S (.call i as) rs
  | prim {Γ S p as ps rs} : TyL D Γ as ps → primK p ps = some rs → ((p = 1 ∨ p = 3 ∨ p = 5) → as = []) →
      TyN D Γ S (.prim p as) rs
  | cont {Γ sk e ks} : TyN D Γ none e sk → TyN D Γ (some sk) (.cont e) ks
inductive TyL (D : List Sig) : List (Option Kd) → List Nd → List Kd → Prop
  | nil {Γ} : TyL D Γ [] []
  | cons {Γ n r k ks} : TyN D Γ none n k → TyL D Γ r ks → TyL D Γ (n :: r) (k ++ ks)
end

/-- a def body: an expression, or the fuel loop (slot 0 = fuel, then the states `sk`, then let slots) -/
inductive TyB (D : List Sig) : List (Option Kd) → Nd → List Kd → Prop
  | plain {Γ e ks} : TyN D Γ none e ks → TyB D Γ e ks
  | loop {Γ z s sk n ks} : Γ = some .w :: sk.map some ++ List.replicate n none →
      TyN D Γ none z ks → TyN D Γ (some sk) s ks → TyB D Γ (.loop z s) ks

/-- slot value vs. known kind -/
def RK (v : W) (o : Option Kd) : Prop := ∀ k, o = some k → v.k = k

/-- the environment holds the known kinds (pointwise `RK`) -/
inductive EnvOK : List W → List (Option Kd) → Prop
  | nil : EnvOK [] []
  | cons {v l o Γ} : RK v o → EnvOK l Γ → EnvOK (v :: l) (o :: Γ)

theorem EnvOK.length_eq : ∀ {l Γ}, EnvOK l Γ → l.length = Γ.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length_eq]

theorem EnvOK.take : ∀ (n : Nat) {l Γ}, EnvOK l Γ → EnvOK (l.take n) (Γ.take n)
  | 0, _, _, _ => by simp; exact .nil
  | _ + 1, _, _, .nil => by simp; exact .nil
  | n + 1, _, _, .cons h1 h2 => by simp; exact .cons h1 (EnvOK.take n h2)

theorem EnvOK.drop : ∀ (n : Nat) {l Γ}, EnvOK l Γ → EnvOK (l.drop n) (Γ.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, _, _, .nil => by simp; exact .nil
  | n + 1, _, _, .cons _ h2 => by simpa using EnvOK.drop n h2

theorem EnvOK.append : ∀ {l Γ l' Γ'}, EnvOK l Γ → EnvOK l' Γ' → EnvOK (l ++ l') (Γ ++ Γ')
  | _, _, _, _, .nil, h => by simpa using h
  | _, _, _, _, .cons h1 h2, h => by simpa using EnvOK.cons h1 (EnvOK.append h2 h)

/-- a meaning respects a signature: never stuck on well-kinded arguments, values of the result kinds -/
def Resp (f : List W → Except Stop (List W)) (sg : Sig) : Prop :=
  ∀ xs, kOf xs = sg.1 → f xs ≠ .error .stuck ∧ ∀ v, f xs = .ok v → kOf v = sg.2

def CtxOK (cx : Ctx) (D : List Sig) : Prop :=
  cx.defs.length = D.length ∧ ∀ (i : Nat) f sg, cx.defs[i]? = some f → D[i]? = some sg → Resp f sg

/-- what a node evaluation promises -/
def OutOK (S : Option (List Kd)) (ks : List Kd) (r : Out) : Prop :=
  r ≠ .error .stuck ∧ (∀ v, r = .ok (.inl v) → kOf v = ks) ∧ (∀ st, r = .ok (.inr st) → ∃ sk, S = some sk ∧ kOf st = sk)

/-! ## helper facts -/

theorem kOf_append (a b : List W) : kOf (a ++ b) = kOf a ++ kOf b := by simp [kOf]
theorem kOf_length (a : List W) : (kOf a).length = a.length := by simp [kOf]

theorem f2_some : ∀ {l : List W} {ks : List Kd}, EnvOK l (ks.map some) → kOf l = ks
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | v :: l, k :: ks, h => by
    cases h with
    | cons h1 h2 => simp [kOf] at *; exact ⟨h1 k rfl, by simpa [kOf] using f2_some h2⟩

theorem f2_kOf : ∀ (l : List W), EnvOK l ((kOf l).map some)
  | [] => .nil
  | v :: l => .cons (fun k h => by simp at h; exact h) (f2_kOf l)

theorem known_ok {env Γ s w ks} (he : EnvOK env Γ) (hk : known Γ s w ks) :
    s + w ≤ env.length ∧ kOf ((env.drop s).take w) = ks := by
  obtain ⟨h1, h2⟩ := hk
  have hl := he.length_eq
  refine ⟨by omega, f2_some ?_⟩
  rw [← h2]; exact (he.drop s).take w

theorem setSlots_ok {env Γ s vs} (he : EnvOK env Γ) (hs : s + vs.length ≤ Γ.length) :
    ∃ env', setSlots env s vs = .ok env' ∧ EnvOK env' (setK Γ s (kOf vs)) := by
  have hl := he.length_eq
  refine ⟨_, by simp [setSlots, hl, hs]; rfl, ?_⟩
  unfold setK; rw [kOf_length]
  rw [← List.append_assoc]; exact ((he.take s).append (f2_kOf vs)).append (he.drop _)

theorem push_ok (κ : Nat) (l : List UInt64) (v : UInt64) :
    push κ l v ≠ .error .stuck ∧ ∀ r, push κ l v = .ok r → kOf r = [.b] := by
  unfold push; split <;> simp_all [kOf, W.k]

theorem prim_ok (cx : Ctx) (p : Nat) (as : List W) (rs : List Kd) (h : primK p (kOf as) = some rs) :
    prim cx p as ≠ .error .stuck ∧ ∀ v, prim cx p as = .ok v → kOf v = rs := by
  match as with
  | [] => simp only [kOf, List.map_nil, primK] at h; split at h <;> simp_all [prim, kOf, W.k]
  | [x] => cases x <;> (simp only [kOf, List.map, W.k, primK] at h; (try split at h) <;> simp_all [prim, kOf, W.k])
  | [x, y] =>
    cases x <;> cases y <;> (simp only [kOf, List.map, W.k, primK] at h; (try split at h) <;> simp_all [prim, kOf, W.k]) <;>
      (unfold push; split <;> simp_all [W.k])
  | [x, y, z] => cases x <;> cases y <;> cases z <;> (simp only [kOf, List.map, W.k, primK] at h; (try split at h) <;> simp_all [prim, kOf, W.k])
  | _ :: _ :: _ :: _ :: _ => simp only [kOf, List.map, primK] at h; split at h <;> simp_all

theorem val_ok {ks r} (h : OutOK none ks r) : val r ≠ .error .stuck ∧ ∀ v, val r = .ok v → kOf v = ks := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold val; split
  · simp; exact h2 _ rfl
  · obtain ⟨_, h, _⟩ := h3 _ rfl; cases h
  · simp_all

theorem binop_ok (op : Nat) (x y : UInt64) (h1 : 1 ≤ op) (h2 : op ≤ 8) : binop op x y ≠ .error .stuck := by
  unfold binop; split <;> simp_all <;> omega

theorem setK_loop0 (sk : List Kd) (n : Nat) :
    setK (some .w :: sk.map some ++ List.replicate n none) 0 [.w] = some .w :: sk.map some ++ List.replicate n none := by
  simp [setK]

theorem setK_loop1 (sk : List Kd) (n : Nat) :
    setK (some .w :: sk.map some ++ List.replicate n none) 1 sk = some .w :: sk.map some ++ List.replicate n none := by
  have : List.drop (1 + sk.length) (some Kd.w :: List.map some sk ++ List.replicate n none) = List.replicate n none :=
    List.drop_left' (by simp; omega)
  simp only [setK]; rw [this]; simp

theorem loopRun_ok {fz fs : List W → Out} {sk : List Kd} {n : Nat} {ks : List Kd}
    (hz : ∀ env, EnvOK env (some .w :: sk.map some ++ List.replicate n none) → OutOK none ks (fz env))
    (hs : ∀ env, EnvOK env (some .w :: sk.map some ++ List.replicate n none) → OutOK (some sk) ks (fs env)) :
    ∀ m env, EnvOK env (some .w :: sk.map some ++ List.replicate n none) →
      loopRun fz fs m env ≠ .error .stuck ∧ ∀ v, loopRun fz fs m env = .ok v → kOf v = ks
  | 0, env, he => by simp only [loopRun]; exact val_ok (hz env he)
  | m + 1, env, he => by
    obtain ⟨env1, e1, he1⟩ := setSlots_ok (vs := [.w (UInt64.ofNat m)]) (s := 0) he (by simp)
    simp only [kOf, List.map, W.k] at he1
    rw [show [Kd.w] = [Kd.w] from rfl, setK_loop0] at he1
    obtain ⟨o1, o2, o3⟩ := hs env1 he1
    simp only [loopRun, e1, bind, Except.bind]
    cases hr : fs env1 with
    | error e => cases e <;> simp_all
    | ok r =>
      cases r with
      | inl v => simp only [pure, Except.pure]; exact ⟨by simp, fun v' e => by cases e; exact o2 v hr⟩
      | inr st =>
        obtain ⟨sk', e, hk⟩ := o3 st hr
        cases e
        have hl : 1 + st.length ≤ (some Kd.w :: sk.map some ++ List.replicate n none).length := by
          rw [← kOf_length, hk]; simp; omega
        obtain ⟨env2, e2, he2⟩ := setSlots_ok he1 hl
        rw [hk, setK_loop1] at he2
        simp only [e2]
        exact loopRun_ok hz hs m env2 he2

theorem kw1 {v : List W} (h : kOf v = [Kd.w]) : ∃ x, v = [.w x] := by
  match v, h with
  | [.w x], _ => exact ⟨x, rfl⟩

theorem out_cap {S ks} : OutOK S ks (.error .cap) := ⟨by simp, by simp, by simp⟩

/-- case split on a non-stuck result -/
theorem ex_cases {α} {r : Except Stop α} (h : r ≠ .error .stuck) : r = .error .cap ∨ ∃ a, r = .ok a := by
  match r with
  | .error .cap => exact .inl rfl
  | .error .stuck => exact absurd rfl h
  | .ok a => exact .inr ⟨a, rfl⟩

mutual
theorem ev_ok {cx : Ctx} {D : List Sig} (hc : CtxOK cx D) : ∀ {Γ S e ks}, TyN D Γ S e ks → ∀ env, EnvOK env Γ →
    OutOK S ks (ev cx e env)
  | _, _, _, _, .const, env, he => by simp [ev, OutOK, kOf, W.k]
  | _, _, _, _, .loc hk, env, he => by
    obtain ⟨h1, h2⟩ := known_ok he hk
    simp only [ev, h1, if_true]; exact ⟨by simp, fun v e => by cases e; exact h2, by simp⟩
  | _, _, _, _, .bin o1 o2 ha hb, env, he => by
    obtain ⟨na, ka⟩ := val_ok (ev_ok hc ha env he)
    obtain ⟨nb, kb⟩ := val_ok (ev_ok hc hb env he)
    simp only [ev]
    rcases ex_cases na with ea | ⟨va, ea⟩
    · simp [ea, bind, Except.bind]; exact out_cap
    obtain ⟨x, rfl⟩ := kw1 (ka _ ea)
    rcases ex_cases nb with eb | ⟨vb, eb⟩
    · simp [ea, eb, bind, Except.bind]; exact out_cap
    obtain ⟨y, rfl⟩ := kw1 (kb _ eb)
    simp only [ea, eb, bind, Except.bind]
    rcases ex_cases (binop_ok _ x y o1 o2) with ec | ⟨z, ec⟩
    · simp [ec]; exact out_cap
    · simp [ec, pure, Except.pure, OutOK, kOf, W.k]
  | _, _, _, _, .ite hc12 ha hb ht he', env, he => by
    obtain ⟨na, ka⟩ := val_ok (ev_ok hc ha env he)
    obtain ⟨nb, kb⟩ := val_ok (ev_ok hc hb env he)
    simp only [ev]
    rcases ex_cases na with ea | ⟨va, ea⟩
    · simp [ea, bind, Except.bind]; exact out_cap
    obtain ⟨x, rfl⟩ := kw1 (ka _ ea)
    rcases ex_cases nb with eb | ⟨vb, eb⟩
    · simp [ea, eb, bind, Except.bind]; exact out_cap
    obtain ⟨y, rfl⟩ := kw1 (kb _ eb)
    simp only [ea, eb, bind, Except.bind]
    rcases hc12 with rfl | rfl
    · simp only [if_true]; split
      · exact ev_ok hc ht env he
      · exact ev_ok hc he' env he
    · simp only [show (2 : Nat) ≠ 1 by decide, if_false, if_true]; split
      · exact ev_ok hc ht env he
      · exact ev_ok hc he' env he
  | _, _, _, _, .letE (vs := vs) hv hw hs _ hb, env, he => by
    obtain ⟨nv, kv⟩ := val_ok (ev_ok hc hv env he)
    simp only [ev]
    rcases ex_cases nv with ev' | ⟨x, ev'⟩
    · simp [ev', bind, Except.bind]; exact out_cap
    have hk := kv _ ev'
    have hxl : x.length = vs.length := by rw [← kOf_length, hk]
    obtain ⟨env', e1, he'⟩ := setSlots_ok he (vs := x) (by rw [hxl, hw]; exact hs)
    rw [hk] at he'
    simp only [ev', bind, Except.bind]; rw [if_pos (by rw [hxl]; exact hw)]; simp only [e1]
    exact ev_ok hc hb env' he'
  | _, _, _, _, .pair hl, env, he => by
    obtain ⟨n1, k1⟩ := evL_ok hc hl env he
    simp only [ev]
    rcases ex_cases n1 with e | ⟨v, e⟩
    · simp [e, bind, Except.bind]; exact out_cap
    · simp only [e, bind, Except.bind, pure, Except.pure]
      exact ⟨by simp, fun v' h => by cases h; exact k1 _ e, by simp⟩
  | _, _, _, _, .call (i := i) hl hd, env, he => by
    obtain ⟨n1, k1⟩ := evL_ok hc hl env he
    simp only [ev]
    rcases ex_cases n1 with e | ⟨v, e⟩
    · simp [e, bind, Except.bind]; exact out_cap
    obtain ⟨hlen, hr⟩ := hc
    have hi : i < cx.defs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hd).1
    obtain ⟨f, hf⟩ : ∃ f, cx.defs[i]? = some f := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨r1, r2⟩ := hr i f _ hf hd v (k1 _ e)
    simp only [e, bind, Except.bind, hf]
    rcases ex_cases r1 with e2 | ⟨w, e2⟩
    · simp [e2]; exact out_cap
    · simp only [e2, pure, Except.pure]
      exact ⟨by simp, fun v' h => by cases h; exact r2 _ e2, by simp⟩
  | _, _, _, _, .prim (p := p) hl hp _, env, he => by
    obtain ⟨n1, k1⟩ := evL_ok hc hl env he
    simp only [ev]
    rcases ex_cases n1 with e | ⟨v, e⟩
    · simp [e, bind, Except.bind]; exact out_cap
    have hk := k1 _ e
    rw [← hk] at hp
    obtain ⟨r1, r2⟩ := prim_ok cx p v _ hp
    simp only [e, bind, Except.bind]
    rcases ex_cases r1 with e2 | ⟨w, e2⟩
    · simp [e2]; exact out_cap
    · simp only [e2, pure, Except.pure]
      exact ⟨by simp, fun v' h => by cases h; exact r2 _ e2, by simp⟩
  | _, _, _, _, .cont (sk := sk) hc', env, he => by
    obtain ⟨n1, k1⟩ := val_ok (ev_ok hc hc' env he)
    simp only [ev]
    rcases ex_cases n1 with e | ⟨v, e⟩
    · simp [e, bind, Except.bind]; exact out_cap
    · simp only [e, bind, Except.bind, pure, Except.pure]
      exact ⟨by simp, by simp, fun st h => by cases h; exact ⟨sk, rfl, k1 _ e⟩⟩

theorem evL_ok {cx : Ctx} {D : List Sig} (hc : CtxOK cx D) : ∀ {Γ cs ks}, TyL D Γ cs ks → ∀ env, EnvOK env Γ →
    evL cx cs env ≠ .error .stuck ∧ ∀ v, evL cx cs env = .ok v → kOf v = ks
  | _, _, _, .nil, env, he => by simp [evL, kOf]
  | _, _, _, .cons hn hr, env, he => by
    obtain ⟨n1, k1⟩ := val_ok (ev_ok hc hn env he)
    obtain ⟨n2, k2⟩ := evL_ok hc hr env he
    simp only [evL]
    rcases ex_cases n1 with e | ⟨v, e⟩
    · simp [e, bind, Except.bind]
    rcases ex_cases n2 with e2 | ⟨w, e2⟩
    · simp [e, e2, bind, Except.bind]
    · simp only [e, e2, bind, Except.bind, pure, Except.pure]
      exact ⟨by simp, fun v' h => by cases h; rw [kOf_append, k1 _ e, k2 _ e2]⟩
end

theorem evB_ok {cx : Ctx} {D : List Sig} (hc : CtxOK cx D) : ∀ {Γ e ks}, TyB D Γ e ks → ∀ env, EnvOK env Γ →
    OutOK none ks (ev cx e env)
  | _, _, _, .plain h, env, he => ev_ok hc h env he
  | _, _, _, .loop (sk := sk) (n := n) hΓ hz hs, env, he => by
    subst hΓ
    cases he with
    | cons h0 he1 =>
      rename_i v0 l
      have : ∃ x, v0 = .w x := by
        have := h0 .w rfl; cases v0 with | w x => exact ⟨x, rfl⟩ | b _ => cases this
      obtain ⟨x, rfl⟩ := this
      have he' : EnvOK (W.w x :: l) (some .w :: sk.map some ++ List.replicate n none) := .cons h0 he1
      obtain ⟨n1, k1⟩ := loopRun_ok (fun env h => ev_ok hc hz env h) (fun env h => ev_ok hc hs env h) x.toNat _ he'
      simp only [ev]
      rcases ex_cases n1 with e | ⟨v, e⟩
      · simp [e, bind, Except.bind]; exact out_cap
      · simp only [e, bind, Except.bind, pure, Except.pure]
        exact ⟨by simp, fun v' h => by cases h; exact k1 _ e, by simp⟩

/-! ## defs and programs -/

/-- a def is well-kinded for signature `sg` against the earlier signatures `D` -/
def TyDef (D : List Sig) (d : DefA) (sg : Sig) : Prop :=
  d.npw = sg.1.length ∧ d.npw ≤ d.nslots ∧ sg.2.length = d.nres ∧
  TyB D (sg.1.map some ++ List.replicate (d.nslots - d.npw) none) d.body sg.2

/-- a well-kinded program: every def against the signatures before it; main takes nothing and returns a buffer -/
def TyProg (p : List DefA) (sigs : List Sig) : Prop :=
  sigs.length = p.length ∧ (∀ (i : Nat) d sg, p[i]? = some d → sigs[i]? = some sg → TyDef (sigs.take i) d sg) ∧
  sigs.getLast? = some ([], [.b])

theorem envOK_rep (n : Nat) : EnvOK (List.replicate n (W.w 0)) (List.replicate n none) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (fun _ h => by cases h) ih

theorem defMean_ok {inp κ ms D d sg} (hc : CtxOK ⟨inp, κ, ms⟩ D) (hd : TyDef D d sg) : Resp (defMean inp κ ms d) sg := by
  obtain ⟨h1, h2, h3, h4⟩ := hd
  intro xs hx
  have hl : xs.length = d.npw := by rw [h1, ← hx, kOf_length]
  have he : EnvOK (xs ++ List.replicate (d.nslots - d.npw) (W.w 0)) (sg.1.map some ++ List.replicate (d.nslots - d.npw) none) := by
    rw [← hx]; exact (f2_kOf xs).append (envOK_rep _)
  obtain ⟨n1, k1⟩ := val_ok (evB_ok hc h4 _ he)
  simp only [defMean, hl, h2, and_self, if_true]
  rcases ex_cases n1 with e | ⟨v, e⟩
  · simp [e, bind, Except.bind]
  · have hv : v.length = d.nres := by rw [← kOf_length, k1 _ e, h3]
    simp only [e, bind, Except.bind, hv, if_true, pure, Except.pure]
    exact ⟨by simp, fun v' h => by cases h; exact k1 _ e⟩

theorem means_ok (inp : List UInt8) (κ : Nat) : ∀ (p : List DefA) (ms : List (List W → Except Stop (List W)))
    (D sigs : List Sig), CtxOK ⟨inp, κ, ms⟩ D → sigs.length = p.length →
    (∀ (i : Nat) d sg, p[i]? = some d → sigs[i]? = some sg → TyDef (D ++ sigs.take i) d sg) →
    CtxOK ⟨inp, κ, means inp κ ms p⟩ (D ++ sigs)
  | [], ms, D, sigs, hc, hl, _ => by
    have : sigs = [] := List.eq_nil_of_length_eq_zero hl
    subst this; simpa [means] using hc
  | d :: r, ms, D, sg :: sigs, hc, hl, ht => by
    simp only [means]
    have h0 := ht 0 d sg rfl rfl
    simp only [List.take_zero, List.append_nil] at h0
    have hc' : CtxOK ⟨inp, κ, ms ++ [defMean inp κ ms d]⟩ (D ++ [sg]) := by
      obtain ⟨hl1, hr⟩ := hc
      refine ⟨by simp [hl1], fun i f sg' hf hs => ?_⟩
      rw [List.getElem?_append] at hf hs
      by_cases hi : i < ms.length
      · have hi' : i < D.length := by simpa [hl1] using hi
        rw [if_pos hi] at hf; rw [if_pos hi'] at hs; exact hr i f sg' hf hs
      · have hi' : ¬ i < D.length := by simpa [hl1] using hi
        rw [if_neg hi] at hf; rw [if_neg hi'] at hs
        simp only at hl1; rw [hl1] at hf
        cases h : i - D.length with
        | zero => rw [h] at hf hs; simp at hf hs; subst hf; subst hs; exact defMean_ok ⟨hl1, hr⟩ h0
        | succ k => rw [h] at hf; simp at hf
    have := means_ok inp κ r _ (D ++ [sg]) sigs hc' (by simpa using hl) (fun i d' sg' hd hs => by
      have := ht (i + 1) d' sg' (by simpa using hd) (by simpa using hs)
      simpa [List.take_succ_cons] using this)
    simpa using this
  | _ :: _, _, _, [], _, hl, _ => by simp at hl

/-- **progress**: a well-kinded program's meaning is never `stuck` -/
theorem sem_ok (κ : Nat) (p : List DefA) (sigs : List Sig) (h : TyProg p sigs) (inp : List UInt8) :
    Sem κ p inp ≠ .error .stuck := by
  obtain ⟨hl, ht, hm⟩ := h
  have hc := means_ok inp κ p [] [] sigs ⟨rfl, by simp⟩ hl (by simpa using ht)
  simp only [List.nil_append] at hc
  obtain ⟨hl2, hr⟩ := hc
  have hne : sigs ≠ [] := by intro e; simp [e] at hm
  rw [List.getLast?_eq_getElem?] at hm
  have hlen : sigs.length - 1 < (means inp κ [] p).length := by rw [hl2]; have := List.length_pos_iff.2 hne; omega
  obtain ⟨r1, r2⟩ := hr (sigs.length - 1) _ _ (List.getElem?_eq_getElem hlen) hm [] rfl
  unfold Sem
  rw [List.getLast?_eq_getElem?, show (means inp κ [] p).length - 1 = sigs.length - 1 by rw [hl2]]
  rw [List.getElem?_eq_getElem hlen]
  simp only
  rcases ex_cases r1 with e | ⟨v, e⟩
  · simp [e]
  · have := r2 v e
    rw [e]
    match v, this with
    | [.b l], _ => simp

end NanoMain
