/- Nano/V2Self/Proof/MainPure: the CAP-FREE meaning `pev` (certificate lead).  `pev` is `NanoMain.ev` with pushes that never fail;
`ev_pev`: whenever `ev` returns a value, `pev` returns the same one.  Per-def certificates (MainCertC*) are EQUATIONS about
`pev` (`pdefMean … args = .ok [the Lean function's value]`); `sem_pure` transfers them to `Sem`. -/
import Nano.V2Self.Proof.Main.Main
namespace NanoMain
open ParSpec

/-- `prim` with unbounded buffers -/
def pprim (inp : List UInt8) (p : Nat) (as : List W) : Except Stop (List W) :=
  match p, as with
  | 1, [] => .ok [.w inp.length.toUInt64]
  | 2, [.w i] => .ok [.w (inp.getD i.toNat 0).toUInt64]
  | 3, [] => .ok [.w inp.length.toUInt64]
  | 4, [.b o, .w v] => .ok [.b (o ++ [v])]
  | 5, [] => .ok [.b []]
  | 6, [.b l] => .ok [.w l.length.toUInt64]
  | 7, [.b l, .w i] => .ok [.w (l.getD i.toNat 0)]
  | 8, [.b l, .w i, .w v] => .ok [.b (l.set i.toNat v)]
  | 9, [.b l, .w v] => .ok [.b (l ++ [v])]
  | _, _ => .error .stuck

abbrev Fn := List W → Except Stop (List W)

mutual
def pev (inp : List UInt8) (ms : List Fn) : Nd → List W → Out
  | .const v, _ => .ok (.inl [.w v])
  | .loc s w, env => if s + w ≤ env.length then .ok (.inl ((env.drop s).take w)) else .error .stuck
  | .bin op a b, env => do
    match ← val (pev inp ms a env), ← val (pev inp ms b env) with
    | [.w x], [.w y] => return .inl [.w (← binop op x y)]
    | _, _ => .error .stuck
  | .ite c a b t e, env => do
    match ← val (pev inp ms a env), ← val (pev inp ms b env) with
    | [.w x], [.w y] =>
      if c = 1 then (if x = y then pev inp ms t env else pev inp ms e env)
      else if c = 2 then (if x < y then pev inp ms t env else pev inp ms e env)
      else .error .stuck
    | _, _ => .error .stuck
  | .letE s w v b, env => do
    let x ← val (pev inp ms v env)
    if x.length = w then pev inp ms b (← setSlots env s x) else .error .stuck
  | .pair cs, env => return .inl (← pevL inp ms cs env)
  | .call i as, env => do
    let xs ← pevL inp ms as env
    match ms[i]? with
    | some f => return .inl (← f xs)
    | none => .error .stuck
  | .prim p as, env => do return .inl (← pprim inp p (← pevL inp ms as env))
  | .loop z s, env =>
    match env with
    | .w n :: _ => return .inl (← loopRun (fun e => pev inp ms z e) (fun e => pev inp ms s e) n.toNat env)
    | _ => .error .stuck
  | .cont e, env => do return .inr (← val (pev inp ms e env))
def pevL (inp : List UInt8) (ms : List Fn) : List Nd → List W → Except Stop (List W)
  | [], _ => .ok []
  | n :: r, env => do return (← val (pev inp ms n env)) ++ (← pevL inp ms r env)
end

def pdefMean (inp : List UInt8) (ms : List Fn) (d : DefA) : Fn := fun ps =>
  if ps.length = d.npw ∧ d.npw ≤ d.nslots then do
    let v ← val (pev inp ms d.body (ps ++ List.replicate (d.nslots - d.npw) (.w 0)))
    if v.length = d.nres then pure v else .error .stuck
  else .error .stuck

def pmeans (inp : List UInt8) : List Fn → List DefA → List Fn
  | ms, [] => ms
  | ms, d :: r => pmeans inp (ms ++ [pdefMean inp ms d]) r

/-- `g` returns whatever `f` returns -/
def Le (f g : Fn) : Prop := ∀ a r, f a = .ok r → g a = .ok r
def LeL (fs gs : List Fn) : Prop := fs.length = gs.length ∧ ∀ (i : Nat) f g, fs[i]? = some f → gs[i]? = some g → Le f g

theorem bind_ok {α β : Type} {x : Except Stop α} {f : α → Except Stop β} {r : β} (h : x >>= f = .ok r) :
    ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem pprim_of {cx : Ctx} {p : Nat} {as r : List W} (h : prim cx p as = .ok r) : pprim cx.inp p as = .ok r := by
  unfold prim at h; unfold pprim
  split at h <;> first | exact h | (unfold push at h; split at h <;> first | exact h | cases h) | cases h

/-- `y` returns whatever `x` returns -/
def Sub {α : Type} (x y : Except Stop α) : Prop := ∀ r, x = .ok r → y = .ok r

theorem Sub.refl {α : Type} {x : Except Stop α} : Sub x x := fun _ h => h

theorem Sub.bind {α β : Type} {x y : Except Stop α} {f g : α → Except Stop β} (h1 : Sub x y) (h2 : ∀ a, Sub (f a) (g a)) :
    Sub (x >>= f) (y >>= g) := by
  intro r h
  obtain ⟨a, ha, hf⟩ := bind_ok h
  rw [h1 a ha]; exact h2 a r hf

theorem Sub.val {x y : Out} (h : Sub x y) : Sub (val x) (val y) := by
  intro r hr
  cases x with
  | error e => cases hr
  | ok v => rw [h v (Eq.refl _)]; exact hr

theorem loopRun_sub {fz fs gz gs : List W → Out} (hz : ∀ e, Sub (fz e) (gz e)) (hs : ∀ e, Sub (fs e) (gs e)) :
    ∀ n env, Sub (loopRun fz fs n env) (loopRun gz gs n env)
  | 0, env => (hz env).val
  | n + 1, env => by
    simp only [loopRun]
    refine Sub.bind Sub.refl fun env1 => Sub.bind (hs env1) fun o => ?_
    cases o with
    | inl v => exact Sub.refl
    | inr st => exact Sub.bind Sub.refl fun e2 => loopRun_sub hz hs n e2

mutual
theorem ev_pev (cx : Ctx) (pms : List Fn) (hL : LeL cx.defs pms) : ∀ (n : Nd) (env : List W), Sub (ev cx n env) (pev cx.inp pms n env)
  | .const v, _ => by simp only [ev, pev]; exact Sub.refl
  | .loc s w, env => by simp only [ev, pev]; exact Sub.refl
  | .bin op a b, env => by
    simp only [ev, pev]
    refine Sub.bind (ev_pev cx pms hL a env).val fun x => Sub.bind (ev_pev cx pms hL b env).val fun y => Sub.refl
  | .ite c a b t e, env => by
    simp only [ev, pev]
    refine Sub.bind (ev_pev cx pms hL a env).val fun x => Sub.bind (ev_pev cx pms hL b env).val fun y => ?_
    split
    · dsimp only
      split
      · split
        · exact ev_pev cx pms hL t env
        · exact ev_pev cx pms hL e env
      · split
        · split
          · exact ev_pev cx pms hL t env
          · exact ev_pev cx pms hL e env
        · exact Sub.refl
    · intro r h; cases h
  | .letE s w v b, env => by
    simp only [ev, pev]
    refine Sub.bind (ev_pev cx pms hL v env).val fun x => ?_
    split
    · exact Sub.bind Sub.refl fun e2 => ev_pev cx pms hL b e2
    · exact Sub.refl
  | .pair cs, env => by
    simp only [ev, pev]
    exact Sub.bind (evL_pevL cx pms hL cs env) fun _ => Sub.refl
  | .call i as, env => by
    simp only [ev, pev]
    refine Sub.bind (evL_pevL cx pms hL as env) fun xs => ?_
    cases hf : cx.defs[i]? with
    | none => intro r h; cases h
    | some f =>
      have hi : i < pms.length := by rw [← hL.1]; exact (List.getElem?_eq_some_iff.mp hf).1
      have hg : pms[i]? = some pms[i] := List.getElem?_eq_getElem hi
      rw [hg]
      exact Sub.bind (fun r h => hL.2 i f _ hf hg xs r h) fun _ => Sub.refl
  | .prim p as, env => by
    simp only [ev, pev]
    exact Sub.bind (evL_pevL cx pms hL as env) fun xs => Sub.bind (fun r h => pprim_of h) fun _ => Sub.refl
  | .loop z s, env => by
    simp only [ev, pev]
    split
    · exact Sub.bind (loopRun_sub (fun e => ev_pev cx pms hL z e) (fun e => ev_pev cx pms hL s e) _ _) fun _ => Sub.refl
    · intro r h; cases h
  | .cont e, env => by
    simp only [ev, pev]
    exact Sub.bind (ev_pev cx pms hL e env).val fun _ => Sub.refl
theorem evL_pevL (cx : Ctx) (pms : List Fn) (hL : LeL cx.defs pms) : ∀ (ns : List Nd) (env : List W), Sub (evL cx ns env) (pevL cx.inp pms ns env)
  | [], _ => by simp only [evL, pevL]; exact Sub.refl
  | n :: r, env => by
    simp only [evL, pevL]
    exact Sub.bind (ev_pev cx pms hL n env).val fun _ => Sub.bind (evL_pevL cx pms hL r env) fun _ => Sub.refl
end

theorem defMean_le {inp : List UInt8} {κ : Nat} {ms pms : List Fn} (hL : LeL ms pms) (d : DefA) :
    Le (defMean inp κ ms d) (pdefMean inp pms d) := by
  intro ps r h
  have : Sub (defMean inp κ ms d ps) (pdefMean inp pms d ps) := by
    unfold defMean pdefMean
    split
    · exact Sub.bind (ev_pev ⟨inp, κ, ms⟩ pms hL d.body _).val fun _ => Sub.refl
    · exact Sub.refl
  exact this r h

theorem LeL.snoc {fs gs : List Fn} {f g : Fn} (h : LeL fs gs) (hf : Le f g) : LeL (fs ++ [f]) (gs ++ [g]) := by
  refine ⟨by simp [h.1], fun i f' g' h1 h2 => ?_⟩
  by_cases hi : i < fs.length
  · rw [List.getElem?_append_left hi] at h1
    rw [List.getElem?_append_left (by rw [← h.1]; exact hi)] at h2
    exact h.2 i f' g' h1 h2
  · rw [List.getElem?_append_right (by omega)] at h1
    rw [List.getElem?_append_right (by rw [← h.1]; omega)] at h2
    have hi0 : i - fs.length = 0 := by
      cases hk : i - fs.length with
      | zero => rfl
      | succ k => rw [hk] at h1; simp at h1
    rw [hi0] at h1; rw [← h.1, hi0] at h2
    simp at h1 h2; subst h1 h2; exact hf

theorem means_le {inp : List UInt8} {κ : Nat} : ∀ (ds : List DefA) {ms pms : List Fn}, LeL ms pms →
    LeL (means inp κ ms ds) (pmeans inp pms ds)
  | [], _, _, h => h
  | d :: r, _, _, h => means_le r (h.snoc (defMean_le h d))

/-- **transfer**: an accepted run of `Sem` is the cap-free main's value -/
theorem sem_pure {κ : Nat} {p : List DefA} {inp y : List UInt8} (h : Sem κ p inp = .ok y) :
    ∃ f l, (pmeans inp [] p).getLast? = some f ∧ f [] = .ok [.b l] ∧ y = l.map UInt64.toUInt8 := by
  have hL : LeL (means inp κ [] p) (pmeans inp [] p) := means_le p ⟨rfl, fun i f g h => by simp at h⟩
  unfold Sem at h
  cases hm : (means inp κ [] p).getLast? with
  | none => rw [hm] at h; cases h
  | some f =>
    rw [hm] at h
    have hne : means inp κ [] p ≠ [] := by intro e; rw [e] at hm; cases hm
    have hlen : 0 < (means inp κ [] p).length := List.length_pos_iff.mpr hne
    have hf : (means inp κ [] p)[(means inp κ [] p).length - 1]? = some f := by rw [← List.getLast?_eq_getElem?]; exact hm
    obtain ⟨G, hg⟩ : ∃ G, (pmeans inp [] p)[(means inp κ [] p).length - 1]? = some G :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hL.1]; omega)⟩
    have hle := hL.2 _ f G hf hg
    dsimp only at h
    split at h
    · rename_i l hr
      exact ⟨G, l, by rw [List.getLast?_eq_getElem?, ← hL.1]; exact hg, hle [] _ hr, by cases h; rfl⟩
    · cases h
    · cases h

end NanoMain
