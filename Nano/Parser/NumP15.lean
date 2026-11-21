/- Nano/Parser/NumP15: COL at fuel f + 1 from the four statements at fuel f. -/
import Nano.Parser.NumP14
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem m_col_succ {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    (hLIT : MLIT x d np ks ws f) (hCMP : MCMP x d np ks ws f) (hLETG : MLETG x d np ks ws f) :
    MCOL x d np ks ws (f + 1) := by
  intro e dd Q bs ts c rest b t g s S gb hfe hnb hdd hQ hx hc hI hP
  have hf : e.ser.length ≤ f := by omega
  have hH : CH x d np f e Q c rest := ⟨hf, hnb, hQ, hx, hc⟩
  cases hl : NumSpec.isL f ws (envOf bs) e
  · cases e with
    | const v => exact (m_col_const hf hl).elim
    | loc sl w => exact m_col_loc hK hH hI hl hP
    | bin op a bb =>
      cases hsh : NumSpec.isShift op
      · exact m_col_tree hK hCOL hH hsh hI hl hP
      · exact m_col_shift hK hCOL hH hsh hI hl hP
    | ite cm a bb tb eb => exact m_col_ite hK hCOL hCMP hH hdd hI hl hP
    | letE sl w v bd => exact m_col_let hK hCOL hLETG hH hdd hI hl hP
    | pair cs => exact m_col_pair hK hCOL hH hI hl hP
    | call id cs => exact m_col_call hK hCOL hH hI hl hP
    | prim pn cs => exact m_col_prim hK hCOL hH hI hl hP
    | loop z sv => exact m_col_loop hK hCOL hH hI hl hP
    | cont a => exact m_col_cont hK hCOL hH hI hl hP
  · exact m_col_lit hK hLIT hf hnb hdd hQ hx hc hI hl hP

end NumP
