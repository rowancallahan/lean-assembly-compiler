/- Nano/Tests/SelfInCapFree: step A towards `Nonempty SelfIn` (the meaning of C's source does not hit the
buffer capacity on some input).  A node that contains no push (prims 4 `put`, 9 `bpush`) and calls only defs that never
report `cap` never reports `cap` itself: `ev_nocap`.  With the certificate (`Ref`: cap or the Lean value) this turns the
specification of every push-free def into an exact equation. -/
import Nano.SelfHost.Cert.Rules

namespace Cert.CapFree
open NanoMain ParSpec

mutual
/-- no push, and calls only into `S` -/
def nf (S : List Nat) : Nd → Bool
  | .const _ => true
  | .loc _ _ => true
  | .bin _ a b => nf S a && nf S b
  | .ite _ a b t e => nf S a && nf S b && nf S t && nf S e
  | .letE _ _ v b => nf S v && nf S b
  | .pair cs => nfs S cs
  | .call i as => S.contains i && nfs S as
  | .prim p as => p != 4 && p != 9 && nfs S as
  | .loop z s => nf S z && nf S s
  | .cont e => nf S e
def nfs (S : List Nat) : List Nd → Bool
  | [] => true
  | e :: r => nf S e && nfs S r
end

/-- the callees in `S` never report `cap` -/
def Quiet (S : List Nat) (ds : List Fn) : Prop := ∀ i ∈ S, ∀ F, ds[i]? = some F → ∀ ps, F ps ≠ .error .cap

theorem val_nocap {r : Out} (h : r ≠ .error .cap) : NanoMain.val r ≠ .error .cap := by
  rcases r with e | (v | v) <;> simp_all [NanoMain.val]

theorem setSlots_nocap (env : List W) (k : Nat) (vs : List W) : setSlots env k vs ≠ .error .cap := by
  unfold setSlots; split <;> simp

theorem binop_nocap (op : Nat) (a b : UInt64) : binop op a b ≠ .error .cap := by
  unfold binop; split <;> simp

theorem prim_nocap (cx : Ctx) (p : Nat) (as : List W) (h4 : p ≠ 4) (h9 : p ≠ 9) : prim cx p as ≠ .error .cap := by
  unfold prim; split <;> simp_all

theorem loopRun_nocap {fz fs : List W → Out} (hz : ∀ env, fz env ≠ .error .cap) (hs : ∀ env, fs env ≠ .error .cap) :
    ∀ (n : Nat) (env : List W), loopRun fz fs n env ≠ .error .cap
  | 0, env => by simp only [loopRun]; exact val_nocap (hz env)
  | n + 1, env => by
    simp only [loopRun, bind, Except.bind]
    have h1 := setSlots_nocap env 0 [.w (UInt64.ofNat n)]
    rcases hq : setSlots env 0 [.w (UInt64.ofNat n)] with e | env1
    · rw [hq] at h1; simpa using h1
    · simp only
      have h2 := hs env1
      rcases hr : fs env1 with e | (v | st)
      · rw [hr] at h2; simpa using h2
      · simp [pure, Except.pure]
      · simp only
        have h3 := setSlots_nocap env1 1 st
        rcases hq2 : setSlots env1 1 st with e | env2
        · rw [hq2] at h3; simpa using h3
        · exact loopRun_nocap hz hs n env2

/-- a helper for sequencing: binding a cap-free computation with a cap-free continuation -/
theorem bind_nocap {α β : Type} {x : Except Stop α} {f : α → Except Stop β} (hx : x ≠ .error .cap)
    (hf : ∀ a, f a ≠ .error .cap) : (x >>= f) ≠ .error .cap := by
  rcases x with e | a
  · simpa [bind, Except.bind] using hx
  · simpa [bind, Except.bind] using hf a

variable {S : List Nat} {cx : Ctx}

mutual
theorem ev_nocap (hQ : Quiet S cx.defs) : ∀ (e : Nd) (env : List W), nf S e = true → ev cx e env ≠ .error .cap
  | .const v, env, _ => by simp [ev]
  | .loc s w, env, _ => by simp only [ev]; split <;> simp
  | .bin op a b, env, h => by
    simp only [nf, Bool.and_eq_true] at h
    simp only [ev]
    refine bind_nocap (val_nocap (ev_nocap hQ a env h.1)) fun x => bind_nocap (val_nocap (ev_nocap hQ b env h.2)) fun y => ?_
    split
    · exact bind_nocap (binop_nocap _ _ _) fun z => by simp [pure, Except.pure]
    · simp
  | .ite c a b t e, env, h => by
    simp only [nf, Bool.and_eq_true] at h
    simp only [ev]
    refine bind_nocap (val_nocap (ev_nocap hQ a env h.1.1.1)) fun x => bind_nocap (val_nocap (ev_nocap hQ b env h.1.1.2)) fun y => ?_
    split
    · split
      · split
        · exact ev_nocap hQ t env h.1.2
        · exact ev_nocap hQ e env h.2
      · split
        · split
          · exact ev_nocap hQ t env h.1.2
          · exact ev_nocap hQ e env h.2
        · simp
    · simp
  | .letE s w v b, env, h => by
    simp only [nf, Bool.and_eq_true] at h
    simp only [ev]
    refine bind_nocap (val_nocap (ev_nocap hQ v env h.1)) fun x => ?_
    split
    · exact bind_nocap (setSlots_nocap _ _ _) fun env' => ev_nocap hQ b env' h.2
    · simp
  | .pair cs, env, h => by
    simp only [nf] at h
    simp only [ev]
    exact bind_nocap (evL_nocap hQ cs env h) fun x => by simp [pure, Except.pure]
  | .call i as, env, h => by
    simp only [nf, Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [ev]
    refine bind_nocap (evL_nocap hQ as env h.2) fun xs => ?_
    split
    · rename_i f hf
      exact bind_nocap (hQ i h.1 f hf xs) fun x => by simp [pure, Except.pure]
    · simp
  | .prim p as, env, h => by
    simp only [nf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [ev]
    exact bind_nocap (evL_nocap hQ as env h.2) fun xs => bind_nocap (prim_nocap cx p xs h.1.1 h.1.2) fun x => by
      simp [pure, Except.pure]
  | .loop z s, env, h => by
    simp only [nf, Bool.and_eq_true] at h
    simp only [ev]
    split
    · exact bind_nocap (loopRun_nocap (fun e => ev_nocap hQ z e h.1) (fun e => ev_nocap hQ s e h.2) _ _) fun x => by
        simp [pure, Except.pure]
    · simp
  | .cont e, env, h => by
    simp only [nf] at h
    simp only [ev]
    exact bind_nocap (val_nocap (ev_nocap hQ e env h)) fun x => by simp [pure, Except.pure]
theorem evL_nocap (hQ : Quiet S cx.defs) : ∀ (es : List Nd) (env : List W), nfs S es = true → evL cx es env ≠ .error .cap
  | [], env, _ => by simp [evL]
  | e :: r, env, h => by
    simp only [nfs, Bool.and_eq_true] at h
    simp only [evL]
    exact bind_nocap (val_nocap (ev_nocap hQ e env h.1)) fun x => bind_nocap (evL_nocap hQ r env h.2) fun y => by
      simp [pure, Except.pure]
end

/-- a def with a push-free body: its meaning never reports `cap` -/
theorem defMean_nocap {inp : List UInt8} {κ : Nat} {ms : List Fn} {d : DefA} (hQ : Quiet S ms) (h : nf S d.body = true)
    (ps : List W) : defMean inp κ ms d ps ≠ .error .cap := by
  unfold defMean
  split
  · exact bind_nocap (val_nocap (ev_nocap (cx := ⟨inp, κ, ms⟩) hQ d.body _ h)) fun v => by split <;> simp [pure, Except.pure]
  · simp

end Cert.CapFree
