/- Nano/Parser/NumP26: one def: `u48` accepts only if `numOkD` holds. -/
import Nano.Parser.NumP25
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem numOkD_eq (ks ws : List Nat) (df : DefA) : NumSpec.numOkD ks ws df =
    ((NumSpec.col (2 ^ 24) ks ws [] 1 df.body).2 &&
      (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).1.all
        (gspec (NumSpec.marked 1 (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).1 (df.nslots + 1) [])
          (NumSpec.marked 2 (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).1 (df.nslots + 1) []))) := by
  unfold NumSpec.numOkD
  generalize NumSpec.col (2 ^ 24) ks ws [] 1 df.body = R
  obtain ⟨gs, sh⟩ := R
  rfl

theorem def_ok {x d : Buf} {ks ws : List Nat} (hK : LK x d ks ws) {df : DefA} (hdb : Templates.DB df) {rest : Buf}
    {i : Nat} (hx : x.drop i = df.ser ++ rest) (hi : 0 < i) :
    (u48 x d (u i + 6) (bget x (u i + 3))).2 = 1 →
      (u48 x d (u i + 6) (bget x (u i + 3))).1 = u (i + 6 + df.body.ser.length) ∧ NumSpec.numOkD ks ws df = true := by
  obtain ⟨-, -, hns, -, -, hnb⟩ := hdb
  have hxl := hK.lc.xl
  have hcl := drop_len hx (by simp [DefA.ser])
  have hx3 : bget x (u i + 3) = u df.nslots := by
    rw [u3, uadd, rd hx (k := 3) (by simp [DefA.ser]) (by omega)]; simp [DefA.ser, toU]
  have hx6 : x.drop (i + 6) = df.body.ser ++ ([21] ++ rest) := by
    have h0 : x.drop i = [20, u df.id, u df.npw, u df.nslots, u df.kind, u df.nres] ++ (df.body.ser ++ ([21] ++ rest)) := by
      rw [hx]; simp [DefA.ser, toU]
    simpa using drop_shift h0
  rw [hx3, show u i + 6 = u (i + 6) by rw [show (6 : UInt64) = u 6 from rfl, uadd]]
  intro h
  have hf : df.body.ser.length + 1 ≤ 2 ^ 24 := by simp [DefA.ser] at hcl; omega
  obtain ⟨h1, h2, X, hX, hXl, h50⟩ := u48_ok hK hx6 (by omega) hnb hf (u df.nslots) h
  refine ⟨h1, ?_⟩
  rw [numOkD_eq, h2, Bool.true_and]
  have hgb := (sb_all df.npw (2 ^ 24) df.body ks ws [] hnb).1 1 (by omega)
  have hXb : ∀ G ∈ X, G.d < 3 ∧ ∀ v ∈ G.vs, v < 2 ^ 64 := by
    intro G hG
    obtain ⟨h1, h2⟩ := hgb G (hX.subset hG)
    exact ⟨h1, fun v hv => by have := h2 v hv; omega⟩
  exact all_perm hX _ (u50_ok (by omega) hXb (by omega) h50)

end NumP
