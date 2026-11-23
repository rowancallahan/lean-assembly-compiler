/- Bridge.Iota: (1) `TypingW` for the trimmed model, from `TermTyping.wf_mem`; (2) the Nat.casesOn iota facts
`FactsM.natZ` / `FactsM.natS` DISCHARGED by transfer from two stored theorems (S2's `bo_nat_z/s`, stated with
`Nat.zero` / `Nat.succ n` and motive `fun _ => R`), with typing through Nat.casesOn's declared type.
Note for the real bridge: the stored iota theorems must use `Nat.zero`/`Nat.succ n` (not `0`/`n+1`), else a
`litN`-style step is needed in between.

STATUS: proved, no sorry. -/
import Bridge.HeadTyping

namespace Bridge.Iota
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env} (L : SetLaws O)
include L

/-- the typing package for `EvM.ev_denotes`, from `wf_mem` -/
theorem typingW (H : EncEnv env) {sig : Sig} (HT : HeadTy M sig) : TypingW O M.cval sig (encM M) (tyS M) where
  laws := L
  wt := fun hw hρ R hR => wf_mem L HT hw _ hρ R hR
  encTy := fun {s v} hv => by rw [← tyE_tyS M hv]; exact (encM_mem (M := M) (L := L) H (fun _ => M.cval "Nat" []) v).1
  shD := fun s => shTy_tyS M s

/-- Nat.casesOn typing with the motive given as a set function equal to `T` on `Nat` -/
theorem natC_set (H : EncEnv env) (HC : CasesNEnv env) {ρ : Nat → S} {T N Z Lb : S} {F : S → S}
    (hF : ∀ x, O.mem x (M.cval "Nat" []) → F x = T) (hT : O.mem T (O.univ 1))
    (hN : O.mem N (M.cval "Nat" [])) (hZ : O.mem Z T) (hL : O.mem Lb (O.piR 1 (M.cval "Nat" []) fun _ => T)) :
    O.mem (O.app (O.app (O.app (O.app (M.cval "Nat.casesOn" [1]) (O.lamR (regime false) (M.cval "Nat" []) F)) N) Z) Lb) T := by
  have hzero := natEnc_mem' (M := M) (L := L) H ρ 0
  have hsucc : ∀ n, O.mem n (M.cval "Nat" []) → O.mem (O.app (M.cval "Nat.succ" []) n) (M.cval "Nat" []) := by
    intro n hn
    have dP : D O M.cval ρ (.forallE tNat tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
    exact mem_app' L dP (mem_ty M L H.succ dP) .const hn .const
  have hMv : ∀ x, O.mem x (M.cval "Nat" []) → O.app (O.lamR (regime false) (M.cval "Nat" []) F) x = T :=
    fun x hx => by rw [L.app_lamR_pos (by simp [regime]) hx, hF x hx]
  have dT : D O M.cval ρ (.forallE (.forallE tNat (.sort 1) false) (.forallE tNat
      (.forallE (.app (.bvar 1) (.const "Nat.zero" []))
        (.forallE (.forallE tNat (.app (.bvar 3) (.app (.const "Nat.succ" []) (.bvar 0))) false)
          (.app (.bvar 3) (.bvar 2)) false) false) false) false)
      (O.piR 1 (O.piR 1 (M.cval "Nat" []) fun _ => O.univ 1) fun m => O.piR 1 (M.cval "Nat" []) fun t =>
        O.piR 1 (O.app m (M.cval "Nat.zero" [])) fun _ =>
          O.piR 1 (O.piR 1 (M.cval "Nat" []) fun n => O.app m (O.app (M.cval "Nat.succ" []) n)) fun _ => O.app m t) :=
    .pi (.pi .const (fun _ _ => .sort) (np rfl)) (fun _ _ => .pi .const (fun _ _ => .pi (.app .bvar .const)
      (fun _ _ => .pi (.pi .const (fun _ _ => .app .bvar (.app .const .bvar)) (np rfl)) (fun _ _ => .app .bvar .bvar)
        (np rfl)) (np rfl)) (np rfl)) (np rfl)
  have hMt : O.mem (O.lamR (regime false) (M.cval "Nat" []) F) (O.piR 1 (M.cval "Nat" []) fun _ => O.univ 1) :=
    L.lamR_mem fun x hx => by rw [hF x hx]; exact hT
  have g1 := L.app_mem_piR (mem_ty M L HC dT) hMt (np rfl)
  have g2 := L.app_mem_piR g1 hN (np rfl)
  have hZ' : O.mem Z (O.app (O.lamR (regime false) (M.cval "Nat" []) F) (M.cval "Nat.zero" [])) := by
    show O.mem Z (O.app (O.lamR (regime false) (M.cval "Nat" []) F) (natEnc M 0)); rw [hMv _ hzero]; exact hZ
  have g3 := L.app_mem_piR g2 hZ' (np rfl)
  have hL' : O.mem Lb (O.piR 1 (M.cval "Nat" []) fun n =>
      O.app (O.lamR (regime false) (M.cval "Nat" []) F) (O.app (M.cval "Nat.succ" []) n)) := by
    rw [L.piR_congr (B' := fun _ => T) fun n hn => hMv _ (hsucc n hn)]; exact hL
  have g4 := L.app_mem_piR g3 hL' (np rfl)
  rwa [hMv N hN] at g4

/-- the motive `λ (_ : Nat). R` in a theorem, `R` the bound variable at index `i` outside the λ -/
def motive (i : Nat) : E := .lam tNat (.bvar (i + 1)) false

/-- the stored iota theorems (motive `fun _ => R`, `R : Type`):
`nat_z : ∀ (R : Type) (z : R) (s : Nat → R), Nat.casesOn (motive := fun _ => R) Nat.zero z s = z` and
`nat_s : ∀ (R : Type) (z : R) (s : Nat → R) (n : Nat), Nat.casesOn (motive := fun _ => R) (Nat.succ n) z s = s n` -/
structure IotaEnv (env : List Const) : Prop where
  z : HasTy env "nat_z" [] (piN [(.sort 1, true), (.bvar 0, true), (.forallE tNat (.bvar 2) false, true)]
    (eqE 1 (.bvar 2) (.app (.app (.app (.app (.const "Nat.casesOn" [1]) (motive 2)) (.const "Nat.zero" []))
      (.bvar 1)) (.bvar 0)) (.bvar 1)))
  s : HasTy env "nat_s" [] (piN [(.sort 1, true), (.bvar 0, true), (.forallE tNat (.bvar 2) false, true),
      (tNat, true)]
    (eqE 1 (.bvar 3) (.app (.app (.app (.app (.const "Nat.casesOn" [1]) (motive 3))
      (.app (.const "Nat.succ" []) (.bvar 0))) (.bvar 2)) (.bvar 1)) (.app (.bvar 1) (.bvar 0))))

/-- the program's motive `λ (_ : Nat). shTy Rs` and the theorem's `λ (_ : Nat). R` (at `R := ⟦shTy Rs⟧`) denote
the same set -/
theorem motive_eq {ρ ρ' : Nat → S} {Rs : Sh} {i : Nat} {Mv : S} (hi : ρ' i = tyS M Rs)
    (hM : D O M.cval ρ (trM (.lam (.c "Nat" []) (shTy Rs))) Mv) :
    D O M.cval ρ' (motive i) Mv ∧ ∃ F, Mv = O.lamR (regime false) (M.cval "Nat" []) F ∧
      ∀ x, O.mem x (M.cval "Nat" []) → F x = tyS M Rs := by
  obtain ⟨A, F, hA, hF, hP, rfl⟩ := lam_inv hM
  cases hA
  have hF' : ∀ x, O.mem x (M.cval "Nat" []) → F x = tyS M Rs := fun x hx => D_functional L (hF x hx) (shTy_tyS M Rs)
  refine ⟨?_, F, rfl, hF'⟩
  rw [L.lamR_congr hF']
  exact .lam .const (fun x _ => by show D O M.cval (push x ρ') (.bvar (i + 1)) _; rw [← hi]; exact .bvar)
    (fun h => by simp [regime] at h)

/-- **`FactsM.natZ`, discharged** -/
theorem natZ_field (H : EncEnv env) (HC : CasesNEnv env) (HI : IotaEnv env) {ρ : Nat → S} {Rs : Sh} {Hv Z Lb : S}
    (hH : D O M.cval ρ (trM (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy Rs)])) Hv)
    (hZ : O.mem Z (tyS M Rs)) (hL : O.mem Lb (O.piR 1 (tyS M .nt) fun _ => tyS M Rs)) :
    O.app (O.app (O.app Hv (encM M (.n 0))) Z) Lb = Z := by
  obtain ⟨Hd, Mv, hHd, hM, rfl⟩ := app_inv hH
  cases hHd
  let ρ' := push Lb (push Z (push (tyS M Rs) ρ))
  obtain ⟨hM', F, rfl, hF⟩ := motive_eq L (ρ' := ρ') (i := 2) (by rfl) hM
  have hRu := tyS_univ (M := M) L H ρ Rs
  obtain ⟨ty, hc, hty⟩ := HI.z
  have hlhs := natC_set (ρ := ρ) L H HC hF hRu (natEnc_mem' (M := M) (L := L) H ρ 0) hZ hL
  exact transferN L M hc (ls := []) hty ρ
    (.cons .sort hRu (.cons .bvar hZ (.cons (.pi .const (fun _ _ => .bvar) (np rfl)) hL .nil)))
    .bvar (.app (.app (.app (.app .const hM') .const) .bvar) .bvar) .bvar hRu hlhs hZ

/-- **`FactsM.natS`, discharged** -/
theorem natS_field (H : EncEnv env) (HC : CasesNEnv env) (HI : IotaEnv env) {ρ : Nat → S} {Rs : Sh} {s : X}
    {Hv Z Lb R : S} {k : Nat}
    (hH : D O M.cval ρ (trM (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy Rs)])) Hv)
    (hLD : D O M.cval ρ (trM (.lam (.c "Nat" []) s)) Lb)
    (hZ : O.mem Z (tyS M Rs)) (hL : O.mem Lb (O.piR 1 (tyS M .nt) fun _ => tyS M Rs))
    (hR : R = O.app (O.app (O.app Hv (encM M (.n (k + 1)))) Z) Lb) :
    D O M.cval (push (encM M (.n k)) ρ) (trM s) R := by
  obtain ⟨Hd, Mv, hHd, hM, rfl⟩ := app_inv hH
  cases hHd
  have hk := natEnc_mem' (M := M) (L := L) H ρ k
  let ρ' := push (natEnc M k) (push Lb (push Z (push (tyS M Rs) ρ)))
  obtain ⟨hM', F, rfl, hF⟩ := motive_eq L (ρ' := ρ') (i := 3) (by rfl) hM
  have hRu := tyS_univ (M := M) L H ρ Rs
  obtain ⟨ty, hc, hty⟩ := HI.s
  have hsk : O.mem (O.app (M.cval "Nat.succ" []) (natEnc M k)) (M.cval "Nat" []) := by
    have dP : D O M.cval ρ (.forallE tNat tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
    exact mem_app' L dP (mem_ty M L H.succ dP) .const hk .const
  have hlhs := natC_set (ρ := ρ) L H HC hF hRu hsk hZ hL
  have hrhs : O.mem (O.app Lb (natEnc M k)) (tyS M Rs) := L.app_mem_piR hL hk (np rfl)
  have key := transferN L M hc (ls := []) hty ρ
    (.cons .sort hRu (.cons .bvar hZ (.cons (.pi .const (fun _ _ => .bvar) (np rfl)) hL (.cons .const hk .nil))))
    .bvar (.app (.app (.app (.app .const hM') (.app .const .bvar)) .bvar) .bvar) (.app .bvar .bvar) hRu hlhs hrhs
  simp only [push] at key
  subst hR
  show D O M.cval (push (natEnc M k) ρ) (trM s) _
  rw [show encM M (.n (k + 1)) = O.app (M.cval "Nat.succ" []) (natEnc M k) from rfl, key]
  obtain ⟨A, G, hA, hG, hP, rfl⟩ := lam_inv hLD
  cases hA
  rw [L.app_lamR_pos (by simp [regime]) hk]; exact hG _ hk

end Bridge.Iota
