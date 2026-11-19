/- Nano/V2Self/Proof/Cert/Rules: the rule set of the C-WIDE MEANING CERTIFICATE (Sem of a parsed def = the Lean def).
`Ref r v`: `r` hit the buffer capacity or is `ok v` (Lean's `bpush`/`put` have no capacity).  `DenT cx e env t`: node `e`
in environment `env` denotes the Lean value `t` (encoded by `Enc`); `DenK`: the same in tail position of a loop's step
arm (a CONTINUE is discharged by the induction hypothesis); `DenP`: argument lists.  One rule per node kind; the rules
are applied syntax-directed by the generated scripts (Cert/Tac.lean). -/
import Nano.V2Self.Proof.Main.Main
import Nano.V2Self.Prelude

namespace Cert
open NanoMain ParSpec

def Ref {α : Type} (r : Except Stop α) (v : α) : Prop := r = .error .cap ∨ r = .ok v

/-- `wd`/`len`: the width is a property of the TYPE (so side conditions never look at a value: reducing a value such
as a loop call with literal fuel to a pair is ruinous) -/
class Enc (α : Type) where
  enc : α → List W
  wd : Nat
  len : ∀ a, (enc a).length = wd
export Enc (enc)
instance : Enc UInt64 := ⟨fun x => [.w x], 1, fun _ => rfl⟩
instance : Enc (List UInt64) := ⟨fun l => [.b l], 1, fun _ => rfl⟩
instance : Enc Nat := ⟨fun n => [.w (UInt64.ofNat n)], 1, fun _ => rfl⟩
instance : Enc Unit := ⟨fun _ => [], 0, fun _ => rfl⟩
instance {α β : Type} [Enc α] [Enc β] : Enc (α × β) :=
  ⟨fun p => enc p.1 ++ enc p.2, Enc.wd α + Enc.wd β, fun p => by simp [Enc.len]⟩

abbrev Fn := List W → Except Stop (List W)

def DenT (cx : Ctx) (e : Nd) (env : List W) {α : Type} [Enc α] (t : α) : Prop := Ref (ev cx e env) (.inl (enc t))
def DenP (cx : Ctx) (es : List Nd) (env : List W) {α : Type} [Enc α] (t : α) : Prop := Ref (evL cx es env) (enc t)
def DenK (cx : Ctx) (K : List W → List W → Prop) (e : Nd) (env : List W) {α : Type} [Enc α] (t : α) : Prop :=
  ev cx e env = .error .cap ∨ ev cx e env = .ok (.inl (enc t)) ∨ ∃ st, ev cx e env = .ok (.inr st) ∧ K st (enc t)

variable {cx : Ctx} {env : List W}

theorem DenT.toVal {α : Type} [Enc α] {e : Nd} {t : α} (h : DenT cx e env t) : Ref (val (ev cx e env)) (enc t) := by
  rcases h with h | h <;> simp [Ref, NanoMain.val, h]

theorem DenT.const (c : UInt64) : DenT cx (.const c) env c := Or.inr (by simp [ev, enc])
theorem DenT.constN {c : UInt64} {n : Nat} (h : UInt64.ofNat n = c) : DenT cx (.const c) env n :=
  Or.inr (by simp [ev, enc, h])
theorem DenT.loc {α : Type} [Enc α] {s w : Nat} {t : α} (h : (env.drop s).take w = enc t) (hl : Nat.ble (s + w) env.length = true) :
    DenT cx (.loc s w) env t := Or.inr (by simp [ev, Nat.le_of_ble_eq_true hl, h])

theorem DenT.bin {op : Nat} {a b : Nd} {x y z : UInt64} (hz : binop op x y = .ok z) (ha : DenT cx a env x)
    (hb : DenT cx b env y) : DenT cx (.bin op a b) env z := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [DenT, Ref, ev, NanoMain.val, ha, hb, hz, enc, bind, Except.bind, pure, Except.pure]
theorem DenT.add {a b : Nd} {x y : UInt64} : DenT cx a env x → DenT cx b env y → DenT cx (.bin 1 a b) env (x + y) := DenT.bin rfl
theorem DenT.sub {a b : Nd} {x y : UInt64} : DenT cx a env x → DenT cx b env y → DenT cx (.bin 2 a b) env (x - y) := DenT.bin rfl
theorem DenT.mul {a b : Nd} {x y : UInt64} : DenT cx a env x → DenT cx b env y → DenT cx (.bin 3 a b) env (x * y) := DenT.bin rfl
theorem DenT.and {a b : Nd} {x y : UInt64} : DenT cx a env x → DenT cx b env y → DenT cx (.bin 4 a b) env (x &&& y) := DenT.bin rfl
theorem DenT.or {a b : Nd} {x y : UInt64} : DenT cx a env x → DenT cx b env y → DenT cx (.bin 5 a b) env (x ||| y) := DenT.bin rfl
theorem DenT.shl {a b : Nd} {x y : UInt64} : DenT cx a env x → DenT cx b env y → DenT cx (.bin 6 a b) env (x <<< y) := DenT.bin rfl
theorem DenT.shr {a b : Nd} {x y : UInt64} : DenT cx a env x → DenT cx b env y → DenT cx (.bin 7 a b) env (x >>> y) := DenT.bin rfl
theorem DenT.xor {a b : Nd} {x y : UInt64} : DenT cx a env x → DenT cx b env y → DenT cx (.bin 8 a b) env (x ^^^ y) := DenT.bin rfl

theorem DenT.iteEq {α : Type} [Enc α] {a b t e : Nd} {x y : UInt64} {T E : α} {inst : Decidable ((x == y) = true)} (ha : DenT cx a env x) (hb : DenT cx b env y)
    (ht : DenT cx t env T) (he : DenT cx e env E) : DenT cx (.ite 1 a b t e) env (@ite α ((x == y) = true) inst T E) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [DenT, Ref, ev, NanoMain.val, ha, hb, enc, bind, Except.bind]
  by_cases c : x = y
  · simp only [c, if_true]; exact ht
  · simp only [c, if_false]; exact he
theorem DenT.iteLt {α : Type} [Enc α] {a b t e : Nd} {x y : UInt64} {T E : α} {inst : Decidable (x < y)} (ha : DenT cx a env x) (hb : DenT cx b env y)
    (ht : DenT cx t env T) (he : DenT cx e env E) : DenT cx (.ite 2 a b t e) env (@ite α (x < y) inst T E) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [DenT, Ref, ev, NanoMain.val, ha, hb, enc, bind, Except.bind]
  by_cases c : x < y
  · simp only [c, if_true]; exact ht
  · simp only [c, if_false]; exact he

/-! a `let` of numerals only is a `Nat` for Lean and a word for C: comparisons agree below 2^64 -/
theorem ofNat_inj {x y : Nat} (hx : x < 18446744073709551616) (hy : y < 18446744073709551616) :
    UInt64.ofNat x = UInt64.ofNat y ↔ x = y := by
  constructor
  · intro h
    have := congrArg UInt64.toNat h
    simp only [UInt64.toNat_ofNat'] at this
    rw [Nat.mod_eq_of_lt (by simpa using hx), Nat.mod_eq_of_lt (by simpa using hy)] at this; exact this
  · intro h; rw [h]
theorem ofNat_lt {x y : Nat} (hx : x < 18446744073709551616) (hy : y < 18446744073709551616) :
    UInt64.ofNat x < UInt64.ofNat y ↔ x < y := by
  rw [UInt64.lt_iff_toNat_lt]
  simp only [UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by simpa using hx), Nat.mod_eq_of_lt (by simpa using hy)]

theorem DenT.iteEqN {α : Type} [Enc α] {a b t e : Nd} {x y : Nat} {T E : α} {inst : Decidable ((x == y) = true)} (ha : DenT cx a env x) (hb : DenT cx b env y)
    (hx : x < 18446744073709551616) (hy : y < 18446744073709551616)
    (ht : DenT cx t env T) (he : DenT cx e env E) : DenT cx (.ite 1 a b t e) env (@ite α ((x == y) = true) inst T E) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [DenT, Ref, ev, NanoMain.val, ha, hb, enc, bind, Except.bind]
  by_cases c : x = y
  · simp only [c, if_true]; exact ht
  · simp only [c, if_false]; rw [if_neg (fun h => c ((ofNat_inj hx hy).mp h))]; exact he
theorem DenT.iteLtN {α : Type} [Enc α] {a b t e : Nd} {x y : Nat} {T E : α} {inst : Decidable (x < y)} (ha : DenT cx a env x) (hb : DenT cx b env y)
    (hx : x < 18446744073709551616) (hy : y < 18446744073709551616)
    (ht : DenT cx t env T) (he : DenT cx e env E) : DenT cx (.ite 2 a b t e) env (@ite α (x < y) inst T E) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [DenT, Ref, ev, NanoMain.val, ha, hb, enc, bind, Except.bind]
  by_cases c : x < y
  · simp only [c, if_true]; rw [if_pos ((ofNat_lt hx hy).mpr c)]; exact ht
  · simp only [c, if_false]; rw [if_neg (fun h => c ((ofNat_lt hx hy).mp h))]; exact he

theorem DenT.letE {α β : Type} [Enc α] [Enc β] {s w : Nat} {v b : Nd} (a : α) (B : α → β) (hv : DenT cx v env a)
    (hw : Enc.wd α = w) (hb : ∀ y : α, y = a → ∃ env', setSlots env s (enc y) = .ok env' ∧ DenT cx b env' (B y)) :
    DenT cx (.letE s w v b) env (B a) := by
  obtain ⟨env', h1, h2⟩ := hb a rfl
  have hw : (enc a).length = w := by rw [Enc.len]; exact hw
  rcases hv with hv | hv <;> simp [DenT, Ref, ev, NanoMain.val, hv, hw, h1, bind, Except.bind]
  exact h2

theorem DenP.nil : DenP cx [] env () := Or.inr (by simp [evL, enc])
theorem DenP.one {α : Type} [Enc α] {e : Nd} {t : α} (h : DenT cx e env t) : DenP cx [e] env t := by
  rcases h with h | h <;> simp [DenP, Ref, evL, NanoMain.val, h, bind, Except.bind, pure, Except.pure]
theorem DenP.cons {α β : Type} [Enc α] [Enc β] {e : Nd} {r : List Nd} {a : α} {b : β} (h : DenT cx e env a)
    (hr : DenP cx r env b) : DenP cx (e :: r) env (a, b) := by
  rcases h with h | h <;> rcases hr with hr | hr <;> simp [DenP, Ref, evL, NanoMain.val, h, hr, enc, bind, Except.bind, pure, Except.pure]

theorem DenT.pair {α : Type} [Enc α] {cs : List Nd} {t : α} (h : DenP cx cs env t) : DenT cx (.pair cs) env t := by
  rcases h with h | h <;> simp [DenT, Ref, ev, h, bind, Except.bind, pure, Except.pure]

theorem DenT.call {α β : Type} [Enc α] [Enc β] {i : Nat} {as : List Nd} {F : Fn} {a : α} {r : β} (hd : cx.defs[i]? = some F)
    (ha : DenP cx as env a) (hs : Ref (F (enc a)) (enc r)) : DenT cx (.call i as) env r := by
  rcases ha with ha | ha <;> rcases hs with hs | hs <;> simp [DenT, Ref, ev, ha, hs, hd, bind, Except.bind, pure, Except.pure]

/-! prims -/
theorem DenT.lenN : DenT cx (.prim 1 []) env (_root_.len' cx.inp) := Or.inr (by simp [ev, evL, prim, enc, len', bind, Except.bind, pure, Except.pure])
theorem DenT.rd {e : Nd} {i : UInt64} (h : DenT cx e env i) : DenT cx (.prim 2 [e]) env (_root_.rd cx.inp i) := by
  rcases h with h | h <;> simp [DenT, Ref, ev, evL, NanoMain.val, prim, h, enc, _root_.rd, bind, Except.bind, pure, Except.pure]
theorem DenT.len : DenT cx (.prim 3 []) env (_root_.len cx.inp) := Or.inr (by simp [ev, evL, prim, enc, _root_.len, bind, Except.bind, pure, Except.pure])
theorem DenT.put {e1 e2 : Nd} {l : Buf} {v : UInt64} (h1 : DenT cx e1 env l) (h2 : DenT cx e2 env v) :
    DenT cx (.prim 4 [e1, e2]) env (_root_.bpush l v) := by
  by_cases c : l.length < cx.κ <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [DenT, Ref, ev, evL, NanoMain.val, prim, push, c, h1, h2, enc, _root_.bpush, bind, Except.bind, pure, Except.pure]
theorem DenT.bnew : DenT cx (.prim 5 []) env _root_.bnew := Or.inr (by simp [ev, evL, prim, enc, _root_.bnew, bind, Except.bind, pure, Except.pure])
theorem DenT.bsize {e : Nd} {l : Buf} (h : DenT cx e env l) : DenT cx (.prim 6 [e]) env (_root_.bsize l) := by
  rcases h with h | h <;> simp [DenT, Ref, ev, evL, NanoMain.val, prim, h, enc, _root_.bsize, bind, Except.bind, pure, Except.pure]
theorem DenT.bget {e1 e2 : Nd} {l : Buf} {i : UInt64} (h1 : DenT cx e1 env l) (h2 : DenT cx e2 env i) :
    DenT cx (.prim 7 [e1, e2]) env (_root_.bget l i) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [DenT, Ref, ev, evL, NanoMain.val, prim, h1, h2, enc, _root_.bget, bind, Except.bind, pure, Except.pure]
theorem DenT.bset {e1 e2 e3 : Nd} {l : Buf} {i v : UInt64} (h1 : DenT cx e1 env l) (h2 : DenT cx e2 env i) (h3 : DenT cx e3 env v) :
    DenT cx (.prim 8 [e1, e2, e3]) env (_root_.bset l i v) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    simp [DenT, Ref, ev, evL, NanoMain.val, prim, h1, h2, h3, enc, _root_.bset, bind, Except.bind, pure, Except.pure]
theorem DenT.bpush {e1 e2 : Nd} {l : Buf} {v : UInt64} (h1 : DenT cx e1 env l) (h2 : DenT cx e2 env v) :
    DenT cx (.prim 9 [e1, e2]) env (_root_.bpush l v) := by
  by_cases c : l.length < cx.κ <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [DenT, Ref, ev, evL, NanoMain.val, prim, push, c, h1, h2, enc, _root_.bpush, bind, Except.bind, pure, Except.pure]

/-! tail position of a step arm -/
variable {K : List W → List W → Prop}
theorem DenK.ofT {α : Type} [Enc α] {e : Nd} {t : α} (h : DenT cx e env t) : DenK cx K e env t := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
theorem DenK.cont {α β : Type} [Enc α] [Enc β] {e : Nd} {a : α} {t : β} (h : DenT cx e env a) (hk : K (enc a) (enc t)) :
    DenK cx K (.cont e) env t := by
  rcases h with h | h
  · exact Or.inl (by simp [ev, NanoMain.val, h, bind, Except.bind])
  · exact Or.inr (Or.inr ⟨enc a, by simp [ev, NanoMain.val, h, bind, Except.bind, pure, Except.pure], hk⟩)
theorem DenK.iteEq {α : Type} [Enc α] {a b t e : Nd} {x y : UInt64} {T E : α} {inst : Decidable ((x == y) = true)} (ha : DenT cx a env x) (hb : DenT cx b env y)
    (ht : DenK cx K t env T) (he : DenK cx K e env E) : DenK cx K (.ite 1 a b t e) env (@ite α ((x == y) = true) inst T E) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [DenK, ev, NanoMain.val, ha, hb, enc, bind, Except.bind]
  by_cases c : x = y
  · simp only [c, if_true]; exact ht
  · simp only [c, if_false]; exact he
theorem DenK.iteLt {α : Type} [Enc α] {a b t e : Nd} {x y : UInt64} {T E : α} {inst : Decidable (x < y)} (ha : DenT cx a env x) (hb : DenT cx b env y)
    (ht : DenK cx K t env T) (he : DenK cx K e env E) : DenK cx K (.ite 2 a b t e) env (@ite α (x < y) inst T E) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [DenK, ev, NanoMain.val, ha, hb, enc, bind, Except.bind]
  by_cases c : x < y
  · simp only [c, if_true]; exact ht
  · simp only [c, if_false]; exact he
theorem DenK.iteEqN {α : Type} [Enc α] {a b t e : Nd} {x y : Nat} {T E : α} {inst : Decidable ((x == y) = true)} (ha : DenT cx a env x) (hb : DenT cx b env y)
    (hx : x < 18446744073709551616) (hy : y < 18446744073709551616)
    (ht : DenK cx K t env T) (he : DenK cx K e env E) : DenK cx K (.ite 1 a b t e) env (@ite α ((x == y) = true) inst T E) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [DenK, ev, NanoMain.val, ha, hb, enc, bind, Except.bind]
  by_cases c : x = y
  · simp only [c, if_true]; exact ht
  · simp only [c, if_false]; rw [if_neg (fun h => c ((ofNat_inj hx hy).mp h))]; exact he
theorem DenK.iteLtN {α : Type} [Enc α] {a b t e : Nd} {x y : Nat} {T E : α} {inst : Decidable (x < y)} (ha : DenT cx a env x) (hb : DenT cx b env y)
    (hx : x < 18446744073709551616) (hy : y < 18446744073709551616)
    (ht : DenK cx K t env T) (he : DenK cx K e env E) : DenK cx K (.ite 2 a b t e) env (@ite α (x < y) inst T E) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [DenK, ev, NanoMain.val, ha, hb, enc, bind, Except.bind]
  by_cases c : x < y
  · simp only [c, if_true]; rw [if_pos ((ofNat_lt hx hy).mpr c)]; exact ht
  · simp only [c, if_false]; rw [if_neg (fun h => c ((ofNat_lt hx hy).mp h))]; exact he

theorem DenK.letE {α β : Type} [Enc α] [Enc β] {s w : Nat} {v b : Nd} (a : α) (B : α → β) (hv : DenT cx v env a)
    (hw : Enc.wd α = w) (hb : ∀ y : α, y = a → ∃ env', setSlots env s (enc y) = .ok env' ∧ DenK cx K b env' (B y)) :
    DenK cx K (.letE s w v b) env (B a) := by
  obtain ⟨env', h1, h2⟩ := hb a rfl
  have hw : (enc a).length = w := by rw [Enc.len]; exact hw
  rcases hv with hv | hv <;> simp [DenK, ev, NanoMain.val, hv, hw, h1, bind, Except.bind]
  exact h2

/-! loops and defs -/
theorem loop_zero {α : Type} [Enc α] {z : Nd} {fs : List W → Out} {t : α} (h : DenT cx z env t) :
    Ref (loopRun (fun e => ev cx z e) fs 0 env) (enc t) := by
  simp only [loopRun]; exact h.toVal

/-- the continuation of a step arm: the CONTINUE payload goes to slots 1.., then the loop runs on with fuel `n` -/
def KL (cx : Ctx) (fz : List W → Out) (s : Nd) (n : Nat) (env1 : List W) : List W → List W → Prop :=
  fun st r => ∃ env2, setSlots env1 1 st = .ok env2 ∧ Ref (loopRun fz (fun e => ev cx s e) n env2) r

theorem loop_succ {α : Type} [Enc α] {s : Nd} {fz : List W → Out} {n : Nat} {env1 : List W} {t : α}
    (h1 : setSlots env 0 [.w (UInt64.ofNat n)] = .ok env1) (h2 : DenK cx (KL cx fz s n env1) s env1 t) :
    Ref (loopRun fz (fun e => ev cx s e) (n + 1) env) (enc t) := by
  simp only [loopRun, h1, bind, Except.bind]
  rcases h2 with h | h | ⟨st, h, env2, h3, h4⟩
  · simp [Ref, h]
  · simp [Ref, h, pure, Except.pure]
  · simp only [h, h3]; exact h4

theorem loop_ref {z s : Nd} {w0 : UInt64} {rest : List W} {v : List W}
    (h : Ref (loopRun (fun e => ev cx z e) (fun e => ev cx s e) w0.toNat (.w w0 :: rest)) v) :
    Ref (val (ev cx (.loop z s) (.w w0 :: rest))) v := by
  rcases h with h | h <;> simp [Ref, ev, NanoMain.val, h, bind, Except.bind, pure, Except.pure]

theorem defMean_ref {inp : List UInt8} {κ : Nat} {ms : List Fn} {d : DefA} {ps v : List W} (hps : ps.length = d.npw)
    (hle : d.npw ≤ d.nslots) (hres : v.length = d.nres)
    (h : Ref (val (ev ⟨inp, κ, ms⟩ d.body (ps ++ List.replicate (d.nslots - d.npw) (.w 0)))) v) : Ref (defMean inp κ ms d ps) v := by
  unfold defMean
  rw [if_pos ⟨hps, hle⟩]
  rcases h with h | h <;> simp [Ref, h, hres, bind, Except.bind, pure, Except.pure]

/-- `defMean_ref` with the body and the initial environment named explicitly (no unification through `DenT`); the
conclusion has a plain `v` (`hv` by `rfl`): unifying two `enc _` with a pending instance would unfold the value -/
theorem defMean_den {inp : List UInt8} {κ : Nat} {ms : List Fn} {d : DefA} {ps v : List W} {α : Type} [Enc α] (t : α) (e : Nd)
    (env : List W) (hv : v = enc t) (hps : ps.length = d.npw) (hle : d.npw ≤ d.nslots) (hres : Enc.wd α = d.nres) (hb : d.body = e)
    (henv : ps ++ List.replicate (d.nslots - d.npw) (.w 0) = env) (h : DenT ⟨inp, κ, ms⟩ e env t) :
    Ref (defMean inp κ ms d ps) v := by
  subst hv hb henv; exact defMean_ref hps hle (by rw [Enc.len]; exact hres) h.toVal

/-- `defMean_ref` for a loop def, the result width taken from the type -/
theorem defMean_loop {inp : List UInt8} {κ : Nat} {ms : List Fn} {d : DefA} {ps v : List W} {α : Type} [Enc α] (t : α)
    (hv : v = enc t) (hps : ps.length = d.npw) (hle : d.npw ≤ d.nslots) (hres : Enc.wd α = d.nres)
    (h : Ref (NanoMain.val (ev ⟨inp, κ, ms⟩ d.body (ps ++ List.replicate (d.nslots - d.npw) (.w 0)))) (enc t)) :
    Ref (defMean inp κ ms d ps) v := by
  subst hv; exact defMean_ref hps hle (by rw [Enc.len]; exact hres) h

/-! the table of per-def specifications -/
def Good (specs : List (Fn → Prop)) (ms : List Fn) (n : Nat) : Prop :=
  ms.length = n ∧ ∀ (j : Nat) (F : Fn), ms[j]? = some F → ∃ S : Fn → Prop, specs[j]? = some S ∧ S F

theorem Good.get {specs : List (Fn → Prop)} {ms : List Fn} {n i : Nat} {S : Fn → Prop} (G : Good specs ms n) (hi : i < n)
    (hS : specs[i]? = some S) : ∃ F : Fn, ms[i]? = some F ∧ S F := by
  obtain ⟨hl, hg⟩ := G
  have hlt : i < ms.length := by omega
  obtain ⟨S', h1, h2⟩ := hg i ms[i] (List.getElem?_eq_getElem hlt)
  rw [hS] at h1; cases h1
  exact ⟨ms[i], List.getElem?_eq_getElem hlt, h2⟩

theorem means_good (inp : List UInt8) (κ : Nat) (specs : List (Fn → Prop)) :
    ∀ (r : List DefA) (ms : List Fn) (n : Nat), Good specs ms n →
      (∀ i (hi : i < r.length) ms', Good specs ms' (n + i) → ∃ S : Fn → Prop, specs[n + i]? = some S ∧ S (defMean inp κ ms' (r[i]'hi))) →
      Good specs (means inp κ ms r) (n + r.length)
  | [], ms, n, G, _ => by simpa [means] using G
  | d :: r, ms, n, G, H => by
    simp only [means, List.length_cons]
    have G' : Good specs (ms ++ [defMean inp κ ms d]) (n + 1) := by
      obtain ⟨S, hS, hSF⟩ := H 0 (by simp) ms (by simpa using G)
      refine ⟨by simp [G.1], fun j F hj => ?_⟩
      by_cases c : j < ms.length
      · rw [List.getElem?_append_left c] at hj; exact G.2 j F hj
      · have : j = ms.length := by
          have := (List.getElem?_eq_some_iff.mp hj).1; simp at this; omega
        subst this
        simp at hj; subst hj
        exact ⟨S, by rw [G.1]; simpa using hS, hSF⟩
    have := means_good inp κ specs r (ms ++ [defMean inp κ ms d]) (n + 1) G'
      (fun i hi ms' Gi => by
        have := H (i + 1) (by simp; omega) ms' (by rw [show n + (i + 1) = n + 1 + i by omega]; exact Gi)
        rw [show n + (i + 1) = n + 1 + i by omega] at this; simpa using this)
    rw [show n + (r.length + 1) = n + 1 + r.length by omega]; exact this

end Cert
