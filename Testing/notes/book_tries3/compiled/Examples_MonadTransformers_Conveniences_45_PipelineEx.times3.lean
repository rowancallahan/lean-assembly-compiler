import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/MonadTransformers/Conveniences.lean:45-45
section
namespace PipelineEx
variable (α : Type)
variable (β : Type)
variable (γ : Type)
variable (δ : Type)
variable (E₁ : α)
variable (E₂ : α → β)
variable (E₃ : β → γ)
variable (E₄ : γ → δ)
def times3 (n : Nat) : Nat := n * 3
frontx_compile PipelineEx.times3
#check @PipelineEx.times3
end PipelineEx
end

end Proven.Frontx.Run
