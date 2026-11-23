/- Bridge.CheckForm: `Call.DefEnv.form` (every def value is the λ-chain `lamSh ps b` over its body) as a decidable
check, with soundness; kernel-checked for C's own program.

STATUS: proved, no sorry. -/
import Bridge.Call
import Bridge.CheckC

namespace Bridge.CheckForm
open ExprSpec ParSpec Bridge.Typed Bridge.Call Bridge.Check Bridge.CheckEx

def formChk (sig : Sig) (P : Prog) : Bool :=
  P.all fun (n, body) => match sig n with
    | some (ps, _) => match strip ps.length body with
      | some b => body == lamSh ps b
      | none => false
    | none => true

theorem formChk_sound {sig : Sig} {P : Prog} (h : formChk sig P = true) :
    ∀ {n ps r body}, sig n = some (ps, r) → P.lookup n = some body → ∃ b, body = lamSh ps b := by
  intro n ps r body hs hl
  have := List.all_eq_true.mp h _ (lookup_mem hl)
  simp only [hs] at this
  split at this
  · rename_i b _; exact ⟨b, by simpa using this⟩
  · cases this

set_option maxHeartbeats 0 in
theorem cForm : formChk (sigOf oC) (ExprSpec.progOf oC) = true := by decide +kernel

/-- C's defs have the λ-chain form -/
theorem cDefForm : ∀ {n ps r body}, sigOf oC n = some (ps, r) → (ExprSpec.progOf oC).lookup n = some body →
    ∃ b, body = lamSh ps b := formChk_sound cForm

end Bridge.CheckForm
