/- Bridge.Len: the prelude ops `len'`, `len`, `bsize` (the length family) DISCHARGED, from DENOTES-S2's unfolding
equations (`bo_len'`, `bo_len`, `bo_bsize`, all `rfl`), the `List.length` recursion on constructors, `Nat.toUInt64 = ofNat`,
and the 2^64 wrap (`ofNat k = ofNat (k % 2^64)`, from `br_wrap` + Nat add recursion).

STATUS: proved, no sorry. -/
import Bridge.Final3

namespace Bridge.Len
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Asm Bridge.Add Bridge.Final
  Bridge.Call

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def tList (T : E) : E := .app (.const "List" [0]) T
def lenE (T l : E) : E := .app (.app (.const "List.length" [0]) T) l
def tU8 : E := .const "UInt8" []

structure LenEnv (env : List Const) : Prop where
  lenH : HasTy env "List.length" [0] (.forallE (.sort 1) (.forallE (tList (.bvar 0)) tNat false) false)
  lenNil : HasTy env "len_nil" [] (piN [(.sort 1, true)]
    (eqE 1 tNat (lenE (.bvar 0) (.app (.const "List.nil" [0]) (.bvar 0))) (.const "Nat.zero" [])))
  lenCons : HasTy env "len_cons" [] (piN [(.sort 1, true), (.bvar 0, true), (tList (.bvar 1), true)]
    (eqE 1 tNat (lenE (.bvar 2) (.app (.app (.app (.const "List.cons" [0]) (.bvar 2)) (.bvar 1)) (.bvar 0)))
      (.app (.const "Nat.succ" []) (lenE (.bvar 2) (.bvar 0)))))
  toUH : HasTy env "Nat.toUInt64" [] (.forallE tNat tU false)
  toU : HasTy env "toU" [] (piN [(tNat, true)] (eqE 1 tU (.app (.const "Nat.toUInt64" []) (.bvar 0)) (ofN (.bvar 0))))
  boLen' : HasTy env "bo_len'" [] (piN [(tList tU8, true)] (eqE 1 tNat (.app (.const "len'" []) (.bvar 0))
    (lenE tU8 (.bvar 0))))
  boLen : HasTy env "bo_len" [] (piN [(tList tU8, true)] (eqE 1 tU (.app (.const "len" []) (.bvar 0))
    (.app (.const "Nat.toUInt64" []) (lenE tU8 (.bvar 0)))))
  boBsize : HasTy env "bo_bsize" [] (piN [(tList tU, true)] (eqE 1 tU (.app (.const "bsize" []) (.bvar 0))
    (.app (.const "Nat.toUInt64" []) (lenE tU (.bvar 0)))))

variable (L : SetLaws O)
include L

theorem len_mem (HE : LenEnv env) {ρ : Nat → S} {T X : S} (hT : O.mem T (O.univ 1))
    (hX : O.mem X (O.app (M.cval "List" [0]) T)) :
    O.mem (O.app (O.app (M.cval "List.length" [0]) T) X) (M.cval "Nat" []) := by
  have dT : D O M.cval ρ (.forallE (.sort 1) (.forallE (tList (.bvar 0)) tNat false) false)
      (O.piR 1 (O.univ 1) fun t => O.piR 1 (O.app (M.cval "List" [0]) t) fun _ => M.cval "Nat" []) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .const) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (mem_ty M L HE.lenH dT) hT (np rfl)) hX (np rfl)

/-- `List.length` on canonical lists -/
theorem length_set (H : EncEnv env) (HE : LenEnv env) (ρ : Nat → S) {α : Type} {T : S} (hT : O.mem T (O.univ 1))
    (f : α → S) (hf : ∀ a, O.mem (f a) T) :
    ∀ l, O.app (O.app (M.cval "List.length" [0]) T) (listEnc M T f l) = natEnc M l.length := by
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hl := listEnc_mem (M := M) (L := L) H ρ hT f hf
  intro l
  induction l with
  | nil =>
    obtain ⟨ty, hc, hty⟩ := HE.lenNil
    exact transferN L M hc (ls := []) hty ρ (.cons .sort hT .nil) .const (.app (.app .const .bvar) (.app .const .bvar))
      .const hNu (len_mem L HE (ρ := ρ) hT (hl [])) (natEnc_mem' (M := M) (L := L) H ρ 0)
  | cons a l ih =>
    obtain ⟨ty, hc, hty⟩ := HE.lenCons
    have hS : ∀ x, O.mem x (M.cval "Nat" []) → O.mem (O.app (M.cval "Nat.succ" []) x) (M.cval "Nat" []) := by
      intro x hx
      have dP : D O M.cval ρ (.forallE tNat tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
      exact mem_app' L dP (mem_ty M L H.succ dP) .const hx .const
    have key := transferN L M hc (ls := []) hty ρ (.cons .sort hT (.cons .bvar (hf a) (.cons (.app .const .bvar) (hl l) .nil)))
      .const (.app (.app .const .bvar) (.app (.app (.app .const .bvar) .bvar) .bvar)) (.app .const (.app (.app .const .bvar) .bvar))
      hNu (len_mem L HE (ρ := ρ) hT (hl (a :: l))) (hS _ (len_mem L HE (ρ := ρ) hT (hl l)))
    simp only [push] at key
    show O.app (O.app (M.cval "List.length" [0]) T) (listEnc M T f (a :: l)) = _
    rw [show listEnc M T f (a :: l) = O.app (O.app (O.app (M.cval "List.cons" [0]) T) (f a)) (listEnc M T f l) from rfl,
      key, ih]; rfl

/-- the 2^64 wrap on canonical numerals: `ofNat k = ofNat (k % 2^64)` -/
theorem wrap_mod (H : EncEnv env) (HL : LitEnv env) (HN : InstN env) (hbl : HasTy env "br_litN" [] brLitNTy)
    (HA : AddEnv env) (ρ : Nat → S) :
    ∀ k, O.app (M.cval "UInt64.ofNat" []) (natEnc M k) = O.app (M.cval "UInt64.ofNat" []) (natEnc M (k % UInt64.size)) := by
  -- the add facts (as in `Add.add_field`)
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hnat := natEnc_mem' (M := M) (L := L) H ρ
  have dAddN : D O M.cval ρ (.app (.const "Add" [0]) tNat) _ := .app .const .const
  have hAN := hAdd_mem (M := M) L HA (ρ := ρ) hNu (mem_ty M L HA.addNat dAddN)
  let ADD := O.app (O.app (O.app (O.app (M.cval "HAdd.hAdd" [0, 0, 0]) (M.cval "Nat" [])) (M.cval "Nat" []))
    (M.cval "Nat" [])) (O.app (O.app (M.cval "instHAdd" [0]) (M.cval "Nat" [])) (M.cval "instAddNat" []))
  let OF := M.cval "UInt64.ofNat" []
  have addMem : ∀ a b, O.mem a (M.cval "Nat" []) → O.mem b (M.cval "Nat" []) → O.mem (O.app (O.app ADD a) b) (M.cval "Nat" []) :=
    fun a b ha hb => L.app_mem_piR (L.app_mem_piR hAN ha (np rfl)) hb (np rfl)
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app OF a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  have dS : D O M.cval ρ (.forallE tNat tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have sMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "Nat.succ" []) a) (M.cval "Nat" []) :=
    fun a ha => mem_app' L dS (mem_ty M L H.succ dS) .const ha .const
  have dAddNE : ∀ ρ', D O M.cval ρ' (hAdd tNat (instH tNat "instAddNat")) ADD := fun _ =>
    .app (.app (.app (.app .const .const) .const) .const) (.app (.app .const .const) .const)
  have hz : ∀ a, O.mem a (M.cval "Nat" []) → O.app (O.app ADD a) (M.cval "Nat.zero" []) = a := by
    intro a ha
    obtain ⟨ty, hc, hty⟩ := HA.add0
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha .nil) .const (.app (.app (dAddNE _) .bvar) .const) .bvar
      hNu (addMem _ _ ha (hnat 0)) ha
  have hs : ∀ a b, O.mem a (M.cval "Nat" []) → O.mem b (M.cval "Nat" []) →
      O.app (O.app ADD a) (O.app (M.cval "Nat.succ" []) b) = O.app (M.cval "Nat.succ" []) (O.app (O.app ADD a) b) := by
    intro a b ha hb
    obtain ⟨ty, hc, hty⟩ := HA.addS
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha (.cons .const hb .nil)) .const
      (.app (.app (dAddNE _) .bvar) (.app .const .bvar)) (.app .const (.app (.app (dAddNE _) .bvar) .bvar))
      hNu (addMem _ _ ha (sMem _ hb)) (sMem _ (addMem _ _ ha hb))
  have hlit : ∀ ρ', D O M.cval ρ' (litNat UInt64.size) (natEnc M UInt64.size) := fun ρ' =>
    Cmp.nLit_D L H HL HN hbl ρ'
  have hwrap : ∀ a, O.mem a (M.cval "Nat" []) →
      O.app OF (O.app (O.app ADD a) (natEnc M UInt64.size)) = O.app OF a := by
    intro a ha
    obtain ⟨ty, hc, hty⟩ := HA.brWrap
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha .nil) .const
      (.app .const (.app (.app (dAddNE _) .bvar) (hlit _))) (.app .const .bvar) hUu
      (ofMem _ (addMem _ _ ha (hnat _))) (ofMem _ ha)
  have hAdd := add_nat (O := O) (M.cval "Nat.zero" []) (M.cval "Nat.succ" []) ADD (M.cval "Nat" []) (natEnc M) rfl
    (fun _ => rfl) hnat hz hs
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h : k < UInt64.size
    · rw [Nat.mod_eq_of_lt h]
    · have hk : k = (k - UInt64.size) + UInt64.size := by omega
      have := ih (k - UInt64.size) (by have : 0 < UInt64.size := by decide
                                       omega)
      rw [hk, ← hAdd, hwrap _ (hnat _), this, Nat.add_mod_right]

/-- `Nat.toUInt64 n` is `ofNat n` -/
theorem toU_set (H : EncEnv env) (HE : LenEnv env) (ρ : Nat → S) (k : Nat) :
    O.app (M.cval "Nat.toUInt64" []) (natEnc M k) = O.app (M.cval "UInt64.ofNat" []) (natEnc M k) := by
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hk := natEnc_mem' (M := M) (L := L) H ρ k
  have dT : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  obtain ⟨ty, hc, hty⟩ := HE.toU
  exact transferN L M hc (ls := []) hty ρ (.cons .const hk .nil) .const (.app .const .bvar) (.app .const .bvar)
    hUu (mem_app' L dT (mem_ty M L HE.toUH dT) .const hk .const) (mem_app' L dT (mem_ty M L H.ofNat dT) .const hk .const)

/-- a prim's declared type, applied to one typed argument -/
theorem prim1_mem (E : Env env sig P) {p : Nat} {n : String} {s : Ps} {r : Sh} (hp : primInfo p = (n, [s], r)) (h5 : p ≠ 5)
    (h0 : p ≠ 0) (h9 : p ≤ 9) {ρ : Nat → S} {X : S} (hX : O.mem X (tyS M (psSh s))) :
    O.mem (O.app (M.cval n []) X) (tyS M r) := by
  have := app_piS L r (mem_ty M L (E.primTy hp h5 h0 h9) (ρ := ρ) (piPs_D r _)) (.cons hX .nil)
  simpa using this

/-- **`len'`** -/
theorem len'_field (E : Env env sig P) (HE : LenEnv env) (ρ : Nat → S) (x : List UInt8) :
    O.app (M.cval "len'" []) (encM M (.l x)) = encM M (.n x.length) := by
  have H := E.enc
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hX := (encM_mem (M := M) (L := L) H ρ (.l x)).1
  have hU8u := univ1 (M := M) (L := L) H H.u8 ρ
  have dP : D O M.cval ρ (.forallE tNat (.const "UInt8" []) false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have hf : ∀ b : UInt8, O.mem (O.app (M.cval "UInt8.ofNat" []) (natEnc M b.toNat)) (M.cval "UInt8" []) := fun b =>
    mem_app' L dP (mem_ty M L H.ofNat8 dP) .const (natEnc_mem' (M := M) (L := L) H ρ _) .const
  obtain ⟨ty, hc, hty⟩ := HE.boLen'
  have key := transferN L M hc (ls := []) hty ρ (.cons (.app .const .const) hX .nil) .const (.app .const .bvar)
    (.app (.app .const .const) .bvar) hNu (prim1_mem (p := 1) L E rfl (by decide) (by decide) (by decide) (ρ := ρ) hX)
    (len_mem L HE (ρ := ρ) hU8u hX)
  simp only [push] at key
  rw [key]; exact length_set L H HE ρ hU8u _ hf x

/-- **`len`** -/
theorem len_field (E : Env env sig P) (HE : LenEnv env) (HA : AddEnv env) (hbl : HasTy env "br_litN" [] brLitNTy)
    (ρ : Nat → S) (x : List UInt8) :
    O.app (M.cval "len" []) (encM M (.l x)) = encM M (.w x.length.toUInt64) := by
  have H := E.enc
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hX := (encM_mem (M := M) (L := L) H ρ (.l x)).1
  have hU8u := univ1 (M := M) (L := L) H H.u8 ρ
  have dP : D O M.cval ρ (.forallE tNat (.const "UInt8" []) false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have hf : ∀ b : UInt8, O.mem (O.app (M.cval "UInt8.ofNat" []) (natEnc M b.toNat)) (M.cval "UInt8" []) := fun b =>
    mem_app' L dP (mem_ty M L H.ofNat8 dP) .const (natEnc_mem' (M := M) (L := L) H ρ _) .const
  have dT : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  obtain ⟨ty, hc, hty⟩ := HE.boLen
  have key := transferN L M hc (ls := []) hty ρ (.cons (.app .const .const) hX .nil) .const (.app .const .bvar)
    (.app .const (.app (.app .const .const) .bvar)) hUu
    (prim1_mem (p := 3) L E rfl (by decide) (by decide) (by decide) (ρ := ρ) hX)
    (mem_app' L dT (mem_ty M L HE.toUH dT) .const (len_mem L HE (ρ := ρ) hU8u hX) .const)
  simp only [push] at key
  rw [key, show encM M (.l x) = listEnc M (M.cval "UInt8" []) (fun b => O.app (M.cval "UInt8.ofNat" [])
    (natEnc M b.toNat)) x from rfl, length_set L H HE ρ hU8u _ hf x, toU_set L H HE ρ, wrap_mod L H E.lit E.instN hbl HA ρ]
  show _ = O.app (M.cval "UInt64.ofNat" []) (natEnc M (x.length.toUInt64).toNat)
  congr 2

/-- **`bsize`** -/
theorem bsize_field (E : Env env sig P) (HE : LenEnv env) (HA : AddEnv env) (hbl : HasTy env "br_litN" [] brLitNTy)
    (ρ : Nat → S) (b : List UInt64) :
    O.app (M.cval "bsize" []) (encM M (.b b)) = encM M (.w b.length.toUInt64) := by
  have H := E.enc
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hX := (encM_mem (M := M) (L := L) H ρ (.b b)).1
  have hXl : O.mem (encM M (.b b)) (O.app (M.cval "List" [0]) (M.cval "UInt64" [])) := by
    rw [← buf_eq (M := M) (L := L) H ρ]; exact hX
  have dP : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have hf : ∀ w : UInt64, O.mem (O.app (M.cval "UInt64.ofNat" []) (natEnc M w.toNat)) (M.cval "UInt64" []) := fun w =>
    mem_app' L dP (mem_ty M L H.ofNat dP) .const (natEnc_mem' (M := M) (L := L) H ρ _) .const
  obtain ⟨ty, hc, hty⟩ := HE.boBsize
  have key := transferN L M hc (ls := []) hty ρ (.cons (.app .const .const) hXl .nil) .const (.app .const .bvar)
    (.app .const (.app (.app .const .const) .bvar)) hUu
    (prim1_mem (p := 6) L E rfl (by decide) (by decide) (by decide) (ρ := ρ) hX)
    (mem_app' L dP (mem_ty M L HE.toUH dP) .const (len_mem L HE (ρ := ρ) hUu hXl) .const)
  simp only [push] at key
  rw [key, show encM M (.b b) = listEnc M (M.cval "UInt64" []) (fun w => O.app (M.cval "UInt64.ofNat" [])
    (natEnc M w.toNat)) b from rfl, length_set L H HE ρ hUu _ hf b, toU_set L H HE ρ, wrap_mod L H E.lit E.instN hbl HA ρ]
  show _ = O.app (M.cval "UInt64.ofNat" []) (natEnc M (b.length.toUInt64).toNat)
  congr 2

end Bridge.Len
