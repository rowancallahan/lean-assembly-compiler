/- Nano/V2Self/Proof/ParInvAtom: Layer 3, pieces for task 43 `argAtom` (v120), box G: `tok_num` (a numeral under the cursor),
`v9_cw` (v9's width word = Layer 2's `cw`), `ShapeCode.nt_code`.  The handler itself waits for `rep_v5` without the
`A, B < 2^64` bounds (a LOC node's slot is only known mod 2^64). -/
import Nano.V2Self.Proof.ParInvArgName
namespace ParInv
open C BufL ParSpec ParRun

theorem tok_num {h ts : Buf} {p : UInt64} {toks : List Tok} (r : TokAt h p toks) (hT : TokensAt h ts) (hc : bget h (d11 + p) = 5) :
    ∃ v rest, toks = .num v :: rest := by
  cases r with
  | nil e => exfalso; rw [e, hT.2.2.2, hT.2.1] at hc; exact absurd hc (by decide)
  | kw t _ b t5 _ _ _ => rw [b] at hc; exact absurd hc t5
  | num _ _ _ => exact ⟨_, _, rfl⟩
  | id _ a _ => rw [a.1] at hc; exact absurd hc (by decide)

theorem ShapeCode.nt_code {h : Buf} {c : UInt64} (r : ShapeCode h c .nt) : c = 4 := by
  cases r; rfl

/-- v9's width word is `cw` of the decoded shape (code 0 counts 1) -/
theorem v9_cw {h : Buf} {w : UInt64} {o : Option Sh} (r : ShOpt h w o) :
    (if w < 5 then 1 else bget h ((d7 + 8192) + 3 * (w - 5) + 2)) = (cw o).toUInt64 := by
  cases o with
  | none => simp only [ShOpt] at r; subst r; rfl
  | some s =>
    simp only [ShOpt] at r
    cases r with
    | uw => rfl
    | bf => rfl
    | ls => rfl
    | nt => rfl
    | pr h5 _ _ _ hw _ _ =>
      have : ¬ w < 5 := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
      simp only [this, if_false, hw, cw, Sh.width]

end ParInv
