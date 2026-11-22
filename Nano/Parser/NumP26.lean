/- Nano/Parser/NumP26: one def: `u48` accepts only if `numOkD` holds. -/
import Nano.Parser.NumP25
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- the class part of `numOkD` -/
def numC (ks ws : List Nat) (df : DefA) : Bool :=
  (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).2 &&
    (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).1.all
      (gspec (NumSpec.marked 1 (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).1 (df.nslots + 1) [])
        (NumSpec.marked 2 (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).1 (df.nslots + 1) []))

theorem numOkD_eq (ks ws : List Nat) (df : DefA) : NumSpec.numOkD ks ws df =
    ((NumSpec.col (2 ^ 24) ks ws [] 1 df.body).2 && NumSpec.lateOk (2 ^ 24) df.body &&
      (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).1.all
        (gspec (NumSpec.marked 1 (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).1 (df.nslots + 1) [])
          (NumSpec.marked 2 (NumSpec.col (2 ^ 24) ks ws [] 1 df.body).1 (df.nslots + 1) []))) := by
  unfold NumSpec.numOkD NumSpec.colD NumSpec.markD
  generalize NumSpec.col (2 ^ 24) ks ws [] 1 df.body = R
  obtain ⟨gs, sh⟩ := R
  rfl

theorem def_ok {x d : Buf} {ks ws : List Nat} (hK : LK x d ks ws) {df : DefA} (hdb : Templates.DB df) {rest : Buf}
    {i : Nat} (hx : x.drop i = df.ser ++ rest) (hi : 0 < i) {b t g s y y1 y2 : Buf} (hB : BI b t g s y y1 y2)
    {A : List NumSpec.G} (hgA : g = encG A) :
    (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).2.2.2.2.2.2.1 = 1 →
      (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).1 = u (i + 6 + df.body.ser.length) ∧
      numC ks ws df = true ∧
      ∃ A', (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).2.1 = encG A' ∧
        BI (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).2.2.1
          (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).2.2.2.1
          (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).2.1
          (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).2.2.2.2.1
          (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).2.2.2.2.2.2.2.1
          (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).2.2.2.2.2.2.2.2
          (u48 x d (u i + 6) (bget x (u i + 3)) b t g s y y1 y2).2.2.2.2.2.1 := by
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
  obtain ⟨h1, h2, X, f, hh, hX, hXl, hfl, hhl, hU, hg1, hb1, ht1, hs1, hy5⟩ :=
    u48_ok hK hx6 (by omega) hnb hf (u df.nslots) hB hgA h
  have hgb := (sb_all df.npw (2 ^ 24) df.body ks ws [] hnb).1 1 (by omega)
  have hXb : ∀ G ∈ X, G.d < 3 ∧ ∀ v ∈ G.vs, v < 2 ^ 64 := by
    intro G hG
    obtain ⟨h1, h2⟩ := hgb G (hX.subset hG)
    exact ⟨h1, fun v hv => by have := h2 v hv; omega⟩
  have h50 : (u50 (encG A ++ encG X) (bsize (encG A)) (u df.nslots) f hh).1 = 1 := by rw [← hU]; exact h
  obtain ⟨hspec, hf', hh'⟩ := u50_ok rfl rfl (by omega) hXb (by omega) hfl hhl h50
  refine ⟨h1, ?_, A ++ X, by rw [hg1, encG_app], ⟨hb1, ht1, by rw [hg1]; omega, hs1, ?_⟩⟩
  · rw [numC, h2, Bool.true_and]
    exact all_perm hX _ hspec
  · rw [hU]; exact ⟨hf', hh', hy5⟩

end NumP
