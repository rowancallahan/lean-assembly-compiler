/- Integration glue: a stage compiled by the PAGED front end (`wp_compile`: growing arrays, in-place updates, so a
stack is available; theorem form `Implements1Pg`, `Riscv/Frontx/WpImpl.lean`) is a stage for the linker
(`Nano/Link.lean`, form `Implements1With`): `of_pg`.  `space` is any bound under which the paged run fits. -/
import Nano.Link
import Riscv.Frontx.WpImpl

set_option linter.unusedVariables false

namespace Nano.Link
open Proven Proven.Mach.Riscv

/-- a paged stage with enough work space is an `Implements1With` stage -/
theorem of_pg {α β : Type} {encA : α → List UInt8} {encB : β → List UInt8} {code : List (BitVec 32)} {f : α → β}
    {Lmin : Nat} {fits : α → Nat → Prop} {maxLen : Nat} {rl : Bool}
    (h : Implements1Pg encA encB code f Lmin fits maxLen rl) (space : Nat → Nat)
    (hfit : ∀ a L, (encA a).length ≤ maxLen → space (encA a).length ≤ L → Lmin ≤ L ∧ fits a L) :
    Implements1With encA encB code f space maxLen rl := by
  intro a s entry ra input output work
  dsimp only
  intro hx hc hpc hent hcode h10 h11 h12 h13 h2 h1 hra hrad hin hinl hzl hsp hwal hram hdis hmo hmw
  obtain ⟨hmin, hf⟩ := hfit a work.len hx hsp
  refine runsTo_mono (h a s entry ra input output work hx hc hpc hent hcode h10 h11 h12 h13 h2 h1 hra hrad hin hinl
    hzl hmin hwal hram hdis hmo hmw) fun s' hs' => ?_
  obtain ⟨hpc', hun, habi, hcfg, hok, -⟩ := hs'
  obtain ⟨hout, hlen⟩ := hok hf
  exact ⟨hpc', hout, hun, habi, hcfg, hlen⟩

/-- the result as raw bytes (the form `link_stage` takes for the first stage) -/
theorem out_bytes {α β : Type} {encA : α → List UInt8} {encB : β → List UInt8} {c : List (BitVec 32)} {f : α → β}
    {sp : Nat → Nat} {m : Nat} {rl : Bool} (h : Implements1With encA encB c f sp m rl) :
    Implements1With encA (fun l => l) c (fun a => encB (f a)) sp m rl := h

end Nano.Link
