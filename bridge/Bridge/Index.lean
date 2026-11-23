/- Bridge.Index: prelude ops `bget` and `bset`, DISCHARGED.  Stored theorems: S2's `bo_bget : ∀ b i, bget b i =
b.getD i.toNat 0` and `bo_bset : ∀ b i v, bset b i v = b.set i.toNat v`; the `List.getD` / `List.set` recursion on
constructors (with `Nat.zero`/`Nat.succ`); and the guarded `toNat_ofNat : ∀ n, Nat.blt n 2^64 = true →
(UInt64.ofNat n).toNat = n` (the Bool guard's proof element as in Cmp; DENOTES-S2's `hmod` gap).

STATUS: proved, no sorry. -/
import Bridge.Final4

namespace Bridge.Index
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Asm Bridge.Add Bridge.Final
  Bridge.Call Bridge.Len Bridge.Push Bridge.Cmp Bridge.Final4

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def getDE (T l i d : E) : E := .app (.app (.app (.app (.const "List.getD" [0]) T) l) i) d
def setE (T l i v : E) : E := .app (.app (.app (.app (.const "List.set" [0]) T) l) i) v
def toNatE (a : E) : E := .app (.const "UInt64.toNat" []) a
def lit0 : E := .app (.app (.app (.const "OfNat.ofNat" [0]) tU) (.lit 0)) (.app (.const "UInt64.instOfNat" []) (.lit 0))

structure IdxEnv (env : List Const) : Prop where
  toNatH : HasTy env "UInt64.toNat" [] (.forallE tU tNat false)
  toNatG : HasTy env "toNat_ofNat" [] (piN [(tNat, true), (guard (.bvar 0), true)]
    (eqE 1 tNat (toNatE (ofN (.bvar 1))) (.bvar 1)))
  getDH : HasTy env "List.getD" [0] (.forallE (.sort 1) (.forallE (tList (.bvar 0)) (.forallE tNat
    (.forallE (.bvar 2) (.bvar 3) false) false) false) false)
  getDnil : HasTy env "getD_nil" [] (piN [(.sort 1, true), (tNat, true), (.bvar 1, true)]
    (eqE 1 (.bvar 2) (getDE (.bvar 2) (nilE (.bvar 2)) (.bvar 1) (.bvar 0)) (.bvar 0)))
  getDcz : HasTy env "getD_cz" [] (piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (.bvar 2, true)]
    (eqE 1 (.bvar 3) (getDE (.bvar 3) (consE (.bvar 3) (.bvar 2) (.bvar 1)) nz (.bvar 0)) (.bvar 2)))
  getDcs : HasTy env "getD_cs" [] (piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (tNat, true),
      (.bvar 3, true)]
    (eqE 1 (.bvar 4) (getDE (.bvar 4) (consE (.bvar 4) (.bvar 3) (.bvar 2)) (sc (.bvar 1)) (.bvar 0))
      (getDE (.bvar 4) (.bvar 2) (.bvar 1) (.bvar 0))))
  setH : HasTy env "List.set" [0] (.forallE (.sort 1) (.forallE (tList (.bvar 0)) (.forallE tNat
    (.forallE (.bvar 2) (tList (.bvar 3)) false) false) false) false)
  setNil : HasTy env "set_nil" [] (piN [(.sort 1, true), (tNat, true), (.bvar 1, true)]
    (eqE 1 (tList (.bvar 2)) (setE (.bvar 2) (nilE (.bvar 2)) (.bvar 1) (.bvar 0)) (nilE (.bvar 2))))
  setCz : HasTy env "set_cz" [] (piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (.bvar 2, true)]
    (eqE 1 (tList (.bvar 3)) (setE (.bvar 3) (consE (.bvar 3) (.bvar 2) (.bvar 1)) nz (.bvar 0))
      (consE (.bvar 3) (.bvar 0) (.bvar 1))))
  setCs : HasTy env "set_cs" [] (piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true), (tNat, true),
      (.bvar 3, true)]
    (eqE 1 (tList (.bvar 4)) (setE (.bvar 4) (consE (.bvar 4) (.bvar 3) (.bvar 2)) (sc (.bvar 1)) (.bvar 0))
      (consE (.bvar 4) (.bvar 3) (setE (.bvar 4) (.bvar 2) (.bvar 1) (.bvar 0)))))
  boBget : HasTy env "bo_bget" [] (piN [(tList tU, true), (tU, true)]
    (eqE 1 tU (.app (.app (.const "bget" []) (.bvar 1)) (.bvar 0)) (getDE tU (.bvar 1) (toNatE (.bvar 0)) lit0)))
  boBset : HasTy env "bo_bset" [] (piN [(tList tU, true), (tU, true), (tU, true)]
    (eqE 1 (tList tU) (.app (.app (.app (.const "bset" []) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (setE tU (.bvar 2) (toNatE (.bvar 1)) (.bvar 0))))

variable (L : SetLaws O)
include L

theorem getD_mem (HI : IdxEnv env) {ρ : Nat → S} {T X K Dv : S} (hT : O.mem T (O.univ 1))
    (hX : O.mem X (O.app (M.cval "List" [0]) T)) (hK : O.mem K (M.cval "Nat" [])) (hD : O.mem Dv T) :
    O.mem (O.app (O.app (O.app (O.app (M.cval "List.getD" [0]) T) X) K) Dv) T := by
  have dT : D O M.cval ρ (.forallE (.sort 1) (.forallE (tList (.bvar 0)) (.forallE tNat
      (.forallE (.bvar 2) (.bvar 3) false) false) false) false)
      (O.piR 1 (O.univ 1) fun t => O.piR 1 (O.app (M.cval "List" [0]) t) fun _ => O.piR 1 (M.cval "Nat" []) fun _ =>
        O.piR 1 t fun _ => t) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .pi .const (fun _ _ => .pi .bvar (fun _ _ => .bvar)
      (np rfl)) (np rfl)) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HI.getDH dT) hT (np rfl)) hX (np rfl))
    hK (np rfl)) hD (np rfl)

theorem set_mem (HI : IdxEnv env) {ρ : Nat → S} {T X K V : S} (hT : O.mem T (O.univ 1))
    (hX : O.mem X (O.app (M.cval "List" [0]) T)) (hK : O.mem K (M.cval "Nat" [])) (hV : O.mem V T) :
    O.mem (O.app (O.app (O.app (O.app (M.cval "List.set" [0]) T) X) K) V) (O.app (M.cval "List" [0]) T) := by
  have dT : D O M.cval ρ (.forallE (.sort 1) (.forallE (tList (.bvar 0)) (.forallE tNat
      (.forallE (.bvar 2) (tList (.bvar 3)) false) false) false) false)
      (O.piR 1 (O.univ 1) fun t => O.piR 1 (O.app (M.cval "List" [0]) t) fun _ => O.piR 1 (M.cval "Nat" []) fun _ =>
        O.piR 1 t fun _ => O.app (M.cval "List" [0]) t) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .pi .const (fun _ _ => .pi .bvar (fun _ _ => .app .const .bvar)
      (np rfl)) (np rfl)) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HI.setH dT) hT (np rfl)) hX (np rfl))
    hK (np rfl)) hV (np rfl)

theorem cons_mem (H : EncEnv env) {ρ : Nat → S} {T a X : S} (hT : O.mem T (O.univ 1)) (ha : O.mem a T)
    (hX : O.mem X (O.app (M.cval "List" [0]) T)) :
    O.mem (O.app (O.app (O.app (M.cval "List.cons" [0]) T) a) X) (O.app (M.cval "List" [0]) T) := by
  have dP : D O M.cval ρ (.forallE (.sort 1) (.forallE (.bvar 0)
      (.forallE (.app (.const "List" [0]) (.bvar 1)) (.app (.const "List" [0]) (.bvar 2)) false) false) false)
      (O.piR (regime false) (O.univ 1) fun t => O.piR (regime false) t fun _ =>
        O.piR (regime false) (O.app (M.cval "List" [0]) t) fun _ => O.app (M.cval "List" [0]) t) :=
    .pi .sort (fun t _ => .pi .bvar (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .app .const .bvar) (np rfl))
      (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L H.cons dP) hT (np rfl)) ha (np rfl)) hX (np rfl)

/-- `List.getD` on canonical lists -/
theorem getD_set (H : EncEnv env) (HI : IdxEnv env) (ρ : Nat → S) {α : Type} {T : S} (hT : O.mem T (O.univ 1))
    (f : α → S) (hf : ∀ a, O.mem (f a) T) {Dv : S} (hD : O.mem Dv T) :
    ∀ (l : List α) (k : Nat), O.app (O.app (O.app (O.app (M.cval "List.getD" [0]) T) (listEnc M T f l)) (natEnc M k)) Dv =
      (match l[k]? with | some a => f a | none => Dv) := by
  have hl := listEnc_mem (M := M) (L := L) H ρ hT f hf
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  intro l
  induction l with
  | nil =>
    intro k
    obtain ⟨ty, hc, hty⟩ := HI.getDnil
    exact transferN L M hc (ls := []) hty ρ (.cons .sort hT (.cons .const (hn k) (.cons .bvar hD .nil))) .bvar
      (.app (.app (.app (.app .const .bvar) (.app .const .bvar)) .bvar) .bvar) .bvar hT
      (getD_mem L HI (ρ := ρ) hT (hl []) (hn k) hD) hD
  | cons a l ih =>
    intro k
    cases k with
    | zero =>
      obtain ⟨ty, hc, hty⟩ := HI.getDcz
      exact transferN L M hc (ls := []) hty ρ (.cons .sort hT (.cons .bvar (hf a) (.cons (.app .const .bvar) (hl l)
        (.cons .bvar hD .nil)))) .bvar
        (.app (.app (.app (.app .const .bvar) (.app (.app (.app .const .bvar) .bvar) .bvar)) .const) .bvar) .bvar hT
        (getD_mem L HI (ρ := ρ) hT (hl (a :: l)) (hn 0) hD) (hf a)
    | succ k =>
      obtain ⟨ty, hc, hty⟩ := HI.getDcs
      have key := transferN L M hc (ls := []) hty ρ (.cons .sort hT (.cons .bvar (hf a) (.cons (.app .const .bvar) (hl l)
        (.cons .const (hn k) (.cons .bvar hD .nil))))) .bvar
        (.app (.app (.app (.app .const .bvar) (.app (.app (.app .const .bvar) .bvar) .bvar)) (.app .const .bvar)) .bvar)
        (.app (.app (.app (.app .const .bvar) .bvar) .bvar) .bvar) hT
        (getD_mem L HI (ρ := ρ) hT (hl (a :: l)) (hn (k + 1)) hD) (getD_mem L HI (ρ := ρ) hT (hl l) (hn k) hD)
      simp only [push] at key
      show O.app (O.app (O.app (O.app (M.cval "List.getD" [0]) T)
        (O.app (O.app (O.app (M.cval "List.cons" [0]) T) (f a)) (listEnc M T f l)))
        (O.app (M.cval "Nat.succ" []) (natEnc M k))) Dv = _
      rw [key, ih k]; rfl

/-- `List.set` on canonical lists -/
theorem set_set (H : EncEnv env) (HI : IdxEnv env) (ρ : Nat → S) {α : Type} {T : S} (hT : O.mem T (O.univ 1))
    (f : α → S) (hf : ∀ a, O.mem (f a) T) (v : α) :
    ∀ (l : List α) (k : Nat), O.app (O.app (O.app (O.app (M.cval "List.set" [0]) T) (listEnc M T f l)) (natEnc M k)) (f v) =
      listEnc M T f (l.set k v) := by
  have hl := listEnc_mem (M := M) (L := L) H ρ hT f hf
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have hLu := list_univ (M := M) L H (ρ := ρ) hT
  intro l
  induction l with
  | nil =>
    intro k
    obtain ⟨ty, hc, hty⟩ := HI.setNil
    exact transferN L M hc (ls := []) hty ρ (.cons .sort hT (.cons .const (hn k) (.cons .bvar (hf v) .nil))) (.app .const .bvar)
      (.app (.app (.app (.app .const .bvar) (.app .const .bvar)) .bvar) .bvar) (.app .const .bvar) hLu
      (set_mem L HI (ρ := ρ) hT (hl []) (hn k) (hf v)) (hl [])
  | cons a l ih =>
    intro k
    cases k with
    | zero =>
      obtain ⟨ty, hc, hty⟩ := HI.setCz
      exact transferN L M hc (ls := []) hty ρ (.cons .sort hT (.cons .bvar (hf a) (.cons (.app .const .bvar) (hl l)
        (.cons .bvar (hf v) .nil)))) (.app .const .bvar)
        (.app (.app (.app (.app .const .bvar) (.app (.app (.app .const .bvar) .bvar) .bvar)) .const) .bvar)
        (.app (.app (.app .const .bvar) .bvar) .bvar) hLu
        (set_mem L HI (ρ := ρ) hT (hl (a :: l)) (hn 0) (hf v)) (hl (v :: l))
    | succ k =>
      obtain ⟨ty, hc, hty⟩ := HI.setCs
      have key := transferN L M hc (ls := []) hty ρ (.cons .sort hT (.cons .bvar (hf a) (.cons (.app .const .bvar) (hl l)
        (.cons .const (hn k) (.cons .bvar (hf v) .nil))))) (.app .const .bvar)
        (.app (.app (.app (.app .const .bvar) (.app (.app (.app .const .bvar) .bvar) .bvar)) (.app .const .bvar)) .bvar)
        (.app (.app (.app .const .bvar) .bvar) (.app (.app (.app (.app .const .bvar) .bvar) .bvar) .bvar)) hLu
        (set_mem L HI (ρ := ρ) hT (hl (a :: l)) (hn (k + 1)) (hf v))
        (cons_mem L H (ρ := ρ) hT (hf a) (set_mem L HI (ρ := ρ) hT (hl l) (hn k) (hf v)))
      simp only [push] at key
      show O.app (O.app (O.app (O.app (M.cval "List.set" [0]) T)
        (O.app (O.app (O.app (M.cval "List.cons" [0]) T) (f a)) (listEnc M T f l)))
        (O.app (M.cval "Nat.succ" []) (natEnc M k))) (f v) = _
      rw [key, ih k]; rfl

/-- `(ofNat k).toNat = k` on canonical numerals below 2^64 (guarded transfer) -/
theorem toNat_set (H : EncEnv env) (HL : LitEnv env) (HN : InstN env) (HC : CmpEnv env) (HI : IdxEnv env)
    (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S) {k : Nat} (hk : k < UInt64.size) :
    O.app (M.cval "UInt64.toNat" []) (O.app (M.cval "UInt64.ofNat" []) (natEnc M k)) = natEnc M k := by
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have dTN : D O M.cval ρ (.forallE tU tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have hof := mem_app' L dOF (mem_ty M L H.ofNat dOF) .const (hn k) .const
  obtain ⟨G, hG, hp⟩ := guard_mem (ρ := push (natEnc M k) ρ) (i := 0) L H HL HN HC hbl rfl hk
  obtain ⟨ty, hc, hty⟩ := HI.toNatG
  exact transferN L M hc (ls := []) hty ρ (.cons .const (hn k) (.cons hG hp .nil)) .const (.app .const (.app .const .bvar))
    .bvar hNu (mem_app' L dTN (mem_ty M L HI.toNatH dTN) .const hof .const) (hn k)

/-- **`bget`** -/
theorem bget_field (E : Env4 env sig P) (HI : IdxEnv env) (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S)
    (b : List UInt64) (i : UInt64) :
    O.app (O.app (M.cval "bget" []) (encM M (.b b))) (encM M (.w i)) = encM M (.w (b.getD i.toNat 0)) := by
  have H := E.enc
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have dP : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  let f : UInt64 → S := fun w => O.app (M.cval "UInt64.ofNat" []) (natEnc M w.toNat)
  have hf : ∀ w : UInt64, O.mem (f w) (M.cval "UInt64" []) := fun w =>
    mem_app' L dP (mem_ty M L H.ofNat dP) .const (natEnc_mem' (M := M) (L := L) H ρ _) .const
  have hl := listEnc_mem (M := M) (L := L) H ρ hUu f hf
  have hbuf := buf_eq (M := M) (L := L) H ρ
  have hlit : ∀ ρ', D O M.cval ρ' lit0 (f 0) := by
    intro ρ'
    obtain ⟨R, hR⟩ : ∃ R, D O M.cval ρ' lit0 R :=
      ⟨_, .app (.app (.app .const .const) (lit_denotes M ρ' _)) (.app .const (lit_denotes M ρ' _))⟩
    have := litU_field M L E.lit (ρ := ρ') (k := 0) (by decide) hR
    rw [this] at hR; exact hR
  have dTN : D O M.cval ρ (.forallE tU tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have hK : O.mem (O.app (M.cval "UInt64.toNat" []) (f i)) (M.cval "Nat" []) :=
    mem_app' L dTN (mem_ty M L HI.toNatH dTN) .const (hf i) .const
  have hty2 := app_piS L .uw (mem_ty M L (E.primTy (p := 7) rfl (by decide) (by decide) (by decide)) (ρ := ρ)
    (piPs_D .uw _)) (.cons (show O.mem (listEnc M _ f b) (tyS M .bf) by show O.mem _ (M.cval "Buf" []); rw [hbuf]; exact hl b)
      (.cons (hf i) .nil))
  obtain ⟨ty, hc, hty⟩ := HI.boBget
  have key := transferN L M hc (ls := []) hty ρ (.cons (.app .const .const) (hl b) (.cons .const (hf i) .nil))
    .const (.app (.app .const .bvar) .bvar) (.app (.app (.app (.app .const .const) .bvar) (.app .const .bvar)) (hlit _)) hUu
    hty2 (getD_mem L HI (ρ := ρ) hUu (hl b) hK (hf 0))
  simp only [push] at key
  show O.app (O.app (M.cval "bget" []) (listEnc M _ f b)) (f i) = f (b.getD i.toNat 0)
  rw [key, toNat_set L H E.lit E.instN E.cmp HI hbl ρ i.toNat_lt_size, getD_set L H HI ρ hUu f hf (hf 0) b i.toNat]
  rw [List.getD_eq_getElem?_getD]
  cases b[i.toNat]? <;> rfl

/-- **`bset`** -/
theorem bset_field (E : Env4 env sig P) (HI : IdxEnv env) (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S)
    (b : List UInt64) (i v : UInt64) :
    O.app (O.app (O.app (M.cval "bset" []) (encM M (.b b))) (encM M (.w i))) (encM M (.w v)) =
      encM M (.b (b.set i.toNat v)) := by
  have H := E.enc
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hLu := list_univ (M := M) L H (ρ := ρ) hUu
  have dP : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  let f : UInt64 → S := fun w => O.app (M.cval "UInt64.ofNat" []) (natEnc M w.toNat)
  have hf : ∀ w : UInt64, O.mem (f w) (M.cval "UInt64" []) := fun w =>
    mem_app' L dP (mem_ty M L H.ofNat dP) .const (natEnc_mem' (M := M) (L := L) H ρ _) .const
  have hl := listEnc_mem (M := M) (L := L) H ρ hUu f hf
  have hbuf := buf_eq (M := M) (L := L) H ρ
  have dTN : D O M.cval ρ (.forallE tU tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have hK : O.mem (O.app (M.cval "UInt64.toNat" []) (f i)) (M.cval "Nat" []) :=
    mem_app' L dTN (mem_ty M L HI.toNatH dTN) .const (hf i) .const
  have hty3 := app_piS L .bf (mem_ty M L (E.primTy (p := 8) rfl (by decide) (by decide) (by decide)) (ρ := ρ)
    (piPs_D .bf _)) (.cons (show O.mem (listEnc M _ f b) (tyS M .bf) by show O.mem _ (M.cval "Buf" []); rw [hbuf]; exact hl b)
      (.cons (hf i) (.cons (hf v) .nil)))
  obtain ⟨ty, hc, hty⟩ := HI.boBset
  have key := transferN L M hc (ls := []) hty ρ (.cons (.app .const .const) (hl b) (.cons .const (hf i) (.cons .const (hf v) .nil)))
    (.app .const .const) (.app (.app (.app .const .bvar) .bvar) .bvar)
    (.app (.app (.app (.app .const .const) .bvar) (.app .const .bvar)) .bvar) hLu
    (by have := hty3; simp only [List.foldl, tyS] at this; rw [hbuf] at this; exact this)
    (set_mem L HI (ρ := ρ) hUu (hl b) hK (hf v))
  simp only [push] at key
  show O.app (O.app (O.app (M.cval "bset" []) (listEnc M _ f b)) (f i)) (f v) = listEnc M _ f (b.set i.toNat v)
  rw [key, toNat_set L H E.lit E.instN E.cmp HI hbl ρ i.toNat_lt_size, set_set L H HI ρ hUu f hf v b i.toNat]

end Bridge.Index
