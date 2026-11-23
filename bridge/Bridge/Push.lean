/- Bridge.Push: prelude ops `bnew` and `bpush`, DISCHARGED.  Stored theorems: `bo_bnew : bnew = @List.nil UInt64`,
`bo_bpush : ∀ (b : List UInt64) (v : UInt64), bpush b v = List.append b [v]` (S2's equation, stated with `List.append`,
not `++`, to avoid `HAppend`'s instances), and the `List.append` recursion on constructors.

STATUS: proved, no sorry. -/
import Bridge.Len

namespace Bridge.Push
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Asm Bridge.Add Bridge.Final
  Bridge.Call Bridge.Len

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def nilE (T : E) : E := .app (.const "List.nil" [0]) T
def consE (T a l : E) : E := .app (.app (.app (.const "List.cons" [0]) T) a) l
def appE (T l m : E) : E := .app (.app (.app (.const "List.append" [0]) T) l) m

structure PushEnv (env : List Const) : Prop where
  appH : HasTy env "List.append" [0] (.forallE (.sort 1) (.forallE (tList (.bvar 0)) (.forallE (tList (.bvar 1))
    (tList (.bvar 2)) false) false) false)
  appNil : HasTy env "app_nil" [] (piN [(.sort 1, true), (tList (.bvar 0), true)]
    (eqE 1 (tList (.bvar 1)) (appE (.bvar 1) (nilE (.bvar 1)) (.bvar 0)) (.bvar 0)))
  appCons : HasTy env "app_cons" [] (piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (tList (.bvar 2), true)]
    (eqE 1 (tList (.bvar 3)) (appE (.bvar 3) (consE (.bvar 3) (.bvar 2) (.bvar 1)) (.bvar 0))
      (consE (.bvar 3) (.bvar 2) (appE (.bvar 3) (.bvar 1) (.bvar 0)))))
  boBnew : HasTy env "bo_bnew" [] (eqE 1 (tList tU) (.const "bnew" []) (nilE tU))
  boBpush : HasTy env "bo_bpush" [] (piN [(tList tU, true), (tU, true)]
    (eqE 1 (tList tU) (.app (.app (.const "bpush" []) (.bvar 1)) (.bvar 0))
      (appE tU (.bvar 1) (consE tU (.bvar 0) (nilE tU)))))

variable (L : SetLaws O)
include L

theorem list_univ (H : EncEnv env) {ρ : Nat → S} {T : S} (hT : O.mem T (O.univ 1)) :
    O.mem (O.app (M.cval "List" [0]) T) (O.univ 1) := by
  have dL : D O M.cval ρ (.forallE (.sort 1) (.sort 1) false) (O.piR (regime false) (O.univ 1) fun _ => O.univ 1) :=
    .pi .sort (fun _ _ => .sort) (np rfl)
  exact mem_app' L dL (mem_ty M L H.list dL) .sort hT .sort

theorem app_mem (HP : PushEnv env) {ρ : Nat → S} {T X Y : S} (hT : O.mem T (O.univ 1))
    (hX : O.mem X (O.app (M.cval "List" [0]) T)) (hY : O.mem Y (O.app (M.cval "List" [0]) T)) :
    O.mem (O.app (O.app (O.app (M.cval "List.append" [0]) T) X) Y) (O.app (M.cval "List" [0]) T) := by
  have dT : D O M.cval ρ (.forallE (.sort 1) (.forallE (tList (.bvar 0)) (.forallE (tList (.bvar 1))
      (tList (.bvar 2)) false) false) false)
      (O.piR 1 (O.univ 1) fun t => O.piR 1 (O.app (M.cval "List" [0]) t) fun _ => O.piR 1 (O.app (M.cval "List" [0]) t)
        fun _ => O.app (M.cval "List" [0]) t) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .app .const .bvar)
      (np rfl)) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HP.appH dT) hT (np rfl)) hX (np rfl)) hY (np rfl)

/-- `List.append` on canonical lists -/
theorem append_set (H : EncEnv env) (HP : PushEnv env) (ρ : Nat → S) {α : Type} {T : S} (hT : O.mem T (O.univ 1))
    (f : α → S) (hf : ∀ a, O.mem (f a) T) :
    ∀ l m, O.app (O.app (O.app (M.cval "List.append" [0]) T) (listEnc M T f l)) (listEnc M T f m) =
      listEnc M T f (l ++ m) := by
  have hl := listEnc_mem (M := M) (L := L) H ρ hT f hf
  have hLu := list_univ (M := M) L H (ρ := ρ) hT
  intro l m
  induction l with
  | nil =>
    obtain ⟨ty, hc, hty⟩ := HP.appNil
    exact transferN L M hc (ls := []) hty ρ (.cons .sort hT (.cons (.app .const .bvar) (hl m) .nil)) (.app .const .bvar)
      (.app (.app (.app .const .bvar) (.app .const .bvar)) .bvar) .bvar hLu
      (app_mem L HP (ρ := ρ) hT (hl []) (hl m)) (hl m)
  | cons a l ih =>
    obtain ⟨ty, hc, hty⟩ := HP.appCons
    have hcons : ∀ X, O.mem X (O.app (M.cval "List" [0]) T) →
        O.mem (O.app (O.app (O.app (M.cval "List.cons" [0]) T) (f a)) X) (O.app (M.cval "List" [0]) T) := by
      intro X hX
      have := listEnc_mem (M := M) (L := L) H ρ hT f hf (a :: [])
      have dP : D O M.cval ρ (.forallE (.sort 1) (.forallE (.bvar 0)
          (.forallE (.app (.const "List" [0]) (.bvar 1)) (.app (.const "List" [0]) (.bvar 2)) false) false) false)
          (O.piR (regime false) (O.univ 1) fun t => O.piR (regime false) t fun _ =>
            O.piR (regime false) (O.app (M.cval "List" [0]) t) fun _ => O.app (M.cval "List" [0]) t) :=
        .pi .sort (fun t _ => .pi .bvar (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .app .const .bvar) (np rfl))
          (np rfl)) (np rfl)
      exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L H.cons dP) hT (np rfl)) (hf a) (np rfl)) hX (np rfl)
    have key := transferN L M hc (ls := []) hty ρ
      (.cons .sort hT (.cons .bvar (hf a) (.cons (.app .const .bvar) (hl l) (.cons (.app .const .bvar) (hl m) .nil))))
      (.app .const .bvar) (.app (.app (.app .const .bvar) (.app (.app (.app .const .bvar) .bvar) .bvar)) .bvar)
      (.app (.app (.app .const .bvar) .bvar) (.app (.app (.app .const .bvar) .bvar) .bvar)) hLu
      (app_mem L HP (ρ := ρ) hT (hl (a :: l)) (hl m)) (hcons _ (app_mem L HP (ρ := ρ) hT (hl l) (hl m)))
    simp only [push] at key
    show O.app (O.app (O.app (M.cval "List.append" [0]) T)
      (O.app (O.app (O.app (M.cval "List.cons" [0]) T) (f a)) (listEnc M T f l))) (listEnc M T f m) = _
    rw [key, ih]; rfl

theorem bnew_field (E : Env env sig P) (HP : PushEnv env) (ρ : Nat → S) : M.cval "bnew" [] = encM M (.b []) := by
  have H := E.enc
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hLu := list_univ (M := M) L H (ρ := ρ) hUu
  have hb : O.mem (M.cval "bnew" []) (O.app (M.cval "List" [0]) (M.cval "UInt64" [])) := by
    rw [← buf_eq (M := M) (L := L) H ρ]; exact mem_ty M L E.bnew (ρ := ρ) .const
  obtain ⟨ty, hc, hty⟩ := HP.boBnew
  exact transferN L M hc (ls := []) (ts := []) hty ρ .nil (.app .const .const) .const (.app .const .const) hLu hb
    (by have := (encM_mem (M := M) (L := L) H ρ (.b [])).1; rw [show tyE M (.b []) = M.cval "Buf" [] from rfl,
      buf_eq (M := M) (L := L) H ρ] at this; exact this)

theorem bpush_field (E : Env env sig P) (HP : PushEnv env) (ρ : Nat → S) (b : List UInt64) (v : UInt64) :
    O.app (O.app (M.cval "bpush" []) (encM M (.b b))) (encM M (.w v)) = encM M (.b (b ++ [v])) := by
  have H := E.enc
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hLu := list_univ (M := M) L H (ρ := ρ) hUu
  have dP : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have hf : ∀ w : UInt64, O.mem (O.app (M.cval "UInt64.ofNat" []) (natEnc M w.toNat)) (M.cval "UInt64" []) := fun w =>
    mem_app' L dP (mem_ty M L H.ofNat dP) .const (natEnc_mem' (M := M) (L := L) H ρ _) .const
  let f : UInt64 → S := fun w => O.app (M.cval "UInt64.ofNat" []) (natEnc M w.toNat)
  have hl := listEnc_mem (M := M) (L := L) H ρ hUu f hf
  have hbuf := buf_eq (M := M) (L := L) H ρ
  -- bpush's type (Buf → UInt64 → Buf), applied
  have hty2 := app_piS L .bf (mem_ty M L (E.primTy (p := 9) rfl (by decide) (by decide) (by decide)) (ρ := ρ)
    (piPs_D .bf _)) (.cons (show O.mem (listEnc M _ f b) (tyS M .bf) by show O.mem _ (M.cval "Buf" []); rw [hbuf]; exact hl b)
      (.cons (hf v) .nil))
  obtain ⟨ty, hc, hty⟩ := HP.boBpush
  have key := transferN L M hc (ls := []) hty ρ (.cons (.app .const .const) (hl b) (.cons .const (hf v) .nil))
    (.app .const .const) (.app (.app .const .bvar) .bvar)
    (.app (.app (.app .const .const) .bvar) (.app (.app (.app .const .const) .bvar) (.app .const .const))) hLu
    (by have := hty2; simp only [List.foldl, tyS] at this; rw [hbuf] at this; exact this)
    (app_mem L HP (ρ := ρ) hUu (hl b) (hl [v]))
  simp only [push] at key
  show O.app (O.app (M.cval "bpush" []) (listEnc M _ f b)) (f v) = listEnc M _ f (b ++ [v])
  rw [key, ← append_set L H HP ρ hUu f hf b [v]]; rfl

end Bridge.Push
