/- Opus box E: Gen's node bounds `NB` (NdCG) from the kind typing `TyN` (MainTy), the serialization length and the prim
operand counts `PAr` (a parser fact). -/
import Nano.Main.Compile
namespace Templates
open ParSpec NanoMain

mutual
/-- every prim node has the operand count Gen reads (`g33`) -/
def PAr : Nd → Prop
  | .const _ => True
  | .loc _ _ => True
  | .bin _ a b => PAr a ∧ PAr b
  | .ite _ a b t e => PAr a ∧ PAr b ∧ PAr t ∧ PAr e
  | .letE _ _ v b => PAr v ∧ PAr b
  | .pair cs => PArL cs
  | .call _ as => PArL as
  | .prim pn as => as.length = (C.g33 pn.toUInt64).toNat ∧ PArL as
  | .loop z s => PAr z ∧ PAr s
  | .cont e => PAr e
def PArL : List Nd → Prop
  | [] => True
  | c :: cs => PAr c ∧ PArL cs
end

theorem nd_ser_pos (n : Nd) : 1 ≤ n.ser.length := by cases n <;> simp [Nd.ser]

theorem serL_len : ∀ cs : List Nd, cs.length ≤ (serL cs).length
  | [] => by simp
  | c :: cs => by have := nd_ser_pos c; have := serL_len cs; simp [serL]; omega

theorem setK_length (Γ : List (Option Kd)) (s : Nat) (ks : List Kd) (h : s + ks.length ≤ Γ.length) :
    (setK Γ s ks).length = Γ.length := by
  simp [setK]; omega

theorem primK_le : ∀ {p ps rs}, primK p ps = some rs → p ≤ 9 := by
  intro p ps rs h
  match p, ps with
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => omega
  | 0, _ => simp [primK] at h
  | n + 10, _ => simp [primK] at h

mutual
theorem nb_ty (p : Nat) {D : List Sig} : ∀ {Γ S n ks}, TyN D Γ S n ks → Γ.length < 2 ^ 32 → D.length < 2 ^ 32 →
    (S.isSome → 1 ≤ p) → n.ser.length < 2 ^ 32 → PAr n → NB p n
  | _, _, _, _, .const, _, _, _, _, _ => by simp [NB]
  | _, _, _, _, .loc hk, hΓ, _, _, _, _ => by simp only [NB]; have := hk.1; omega
  | _, _, _, _, .bin _ o2 ha hb, hΓ, hD, _, hs, hp => by
    simp only [Nd.ser, List.length_cons, List.length_append] at hs; simp only [PAr] at hp
    exact ⟨by omega, nb_ty p ha hΓ hD (by simp) (by omega) hp.1, nb_ty p hb hΓ hD (by simp) (by omega) hp.2⟩
  | _, _, _, _, .ite hc ha hb ht he, hΓ, hD, hS, hs, hp => by
    simp only [Nd.ser, List.length_cons, List.length_append] at hs; simp only [PAr] at hp
    exact ⟨by omega, nb_ty p ha hΓ hD (by simp) (by omega) hp.1, nb_ty p hb hΓ hD (by simp) (by omega) hp.2.1,
      nb_ty p ht hΓ hD hS (by omega) hp.2.2.1, nb_ty p he hΓ hD hS (by omega) hp.2.2.2⟩
  | _, _, _, _, .letE (vs := vs) hv hw hsw _ hb, hΓ, hD, hS, hs, hp => by
    simp only [Nd.ser, List.length_cons, List.length_append] at hs; simp only [PAr] at hp
    have hl := setK_length _ _ vs (hw ▸ hsw)
    exact ⟨by omega, by omega, nb_ty p hv hΓ hD (by simp) (by omega) hp.1,
      nb_ty p hb (by omega) hD hS (by omega) hp.2⟩
  | _, _, _, _, .pair (cs := cs) hl, hΓ, hD, _, hs, hp => by
    simp only [Nd.ser, List.length_cons] at hs; simp only [PAr] at hp
    have := serL_len cs
    exact ⟨by omega, nbl_ty p hl hΓ hD (by omega) hp⟩
  | _, _, _, _, .call (as := as) hl hi, hΓ, hD, _, hs, hp => by
    simp only [Nd.ser, List.length_cons] at hs; simp only [PAr] at hp
    have := serL_len as
    have := (List.getElem?_eq_some_iff.1 hi).1
    exact ⟨by omega, by omega, nbl_ty p hl hΓ hD (by omega) hp⟩
  | _, _, _, _, .prim hl hk _, hΓ, hD, _, hs, hp => by
    simp only [Nd.ser, List.length_cons] at hs; simp only [PAr] at hp
    have := primK_le hk
    exact ⟨by omega, hp.1, nbl_ty p hl hΓ hD (by omega) hp.2⟩
  | _, _, _, _, .cont he, hΓ, hD, hS, hs, hp => by
    simp only [Nd.ser, List.length_cons] at hs; simp only [PAr] at hp
    exact ⟨hS (by simp), nb_ty p he hΓ hD (by simp) (by omega) hp⟩
theorem nbl_ty (p : Nat) {D : List Sig} : ∀ {Γ cs ks}, TyL D Γ cs ks → Γ.length < 2 ^ 32 → D.length < 2 ^ 32 →
    (serL cs).length < 2 ^ 32 → PArL cs → NBL p cs
  | _, _, _, .nil, _, _, _, _ => by simp [NBL]
  | _, _, _, .cons hn hr, hΓ, hD, hs, hp => by
    simp only [serL, List.length_append] at hs; simp only [PArL] at hp
    exact ⟨nb_ty p hn hΓ hD (by simp) (by omega) hp.1, nbl_ty p hr hΓ hD (by omega) hp.2⟩
end

end Templates
