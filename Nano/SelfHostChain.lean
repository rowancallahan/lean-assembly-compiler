/- **The target from the four stages of the staged compiler** (integration, nano-int).
`selfHosted_four`: given machine theorems (front-end list form, result length in `a1`) for
  `fe` : source text ↦ the NON-inlined micro-op stream `serU u` (`Nano/SerU.lean`; only for accepted sources),
  `fi` = the inliner `inlB`,  `fm` = the micro-op expander `mexp`,  `fa` = the assembler `asm`,
the binary `link (link (link ce ci) cm) ca` is a proven self-hosted nano compiler (`SelfHosted … nanoCompileA`).
Everything else is proved: (L2) `nano_stack_correct`/`nano_stack_runs`, the linker, and the Lean-level equation
`chain_eq` (`asm (mexp (inlB (serU u))) = nanoGen p`).  `D` = the size conditions; `K` bounds every intermediate
length and stage work space on `D`. -/
import Nano.SelfHost
import Nano.ElabUWF

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link Nano.U

/-- the size conditions on a source: arities < 256, at most 65536 defs, every intermediate stream within the stages'
input bound and within `K`, every stage's work space within `K` -/
def Sized (K : Nat) (se si sm sa : Nat → Nat) (src : List UInt8) : Prop :=
  ∃ u, nanoElabU src = some u ∧ (∀ d ∈ u, d.1 < 256) ∧ u.length ≤ 65536 ∧
    (serU u).length ≤ 2 ^ 20 ∧ (serU u).length ≤ K ∧ se src.length ≤ K ∧ si (serU u).length ≤ K ∧
    (inlB (serU u)).length ≤ 2 ^ 20 ∧ (inlB (serU u)).length ≤ K ∧ sm (inlB (serU u)).length ≤ K ∧
    (mexp (inlB (serU u))).length ≤ 2 ^ 20 ∧ (mexp (inlB (serU u))).length ≤ K ∧
    sa (mexp (inlB (serU u))).length ≤ K

theorem selfHosted_four {ce ci cm ca : List (BitVec 32)} {fe fi fm fa : ByteArray → List UInt8}
    {se si sm sa : Nat → Nat} (K : Nat)
    (he : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ce fe se (2 ^ 20) true)
    (hi : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ci fi si (2 ^ 20) true)
    (hm : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) cm fm sm (2 ^ 20) true)
    (ha : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ca fa sa (2 ^ 20) true)
    (hci : ci.length < 2 ^ 17) (hcm : cm.length < 2 ^ 17) (hca : ca.length < 2 ^ 17)
    (hfe : ∀ src u, nanoElabU src = some u → fe (ofL src) = serU u)
    (hfi : ∀ x, fi (ofL x) = inlB x) (hfm : ∀ x, fm (ofL x) = mexp x) (hfa : ∀ x, fa (ofL x) = asm x) :
    SelfHosted (link (link (link ce ci) cm) ca) (fun _ => 4 * (4 * (4 * K + 96) + 96) + 96)
      (Sized K se si sm sa) nanoCompileA := by
  have h1 := link_stage (α := SrcIn (Sized K se si sm sa)) K (comap he fun s => ofL s.1) hi hci fun a _ => by
    obtain ⟨u, hu, -, -, b1, b2, b3, b4, -⟩ := a.2
    rw [hfe a.1 u hu]; exact ⟨b1, b2, b3, b4⟩
  have h2 := link_stage (4 * K + 96) h1 hm hcm fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, b5, b6, b7, -⟩ := a.2
    rw [hfe a.1 u hu, hfi]; exact ⟨b5, by omega, by omega, by omega⟩
  have h3 := link_stage (4 * (4 * K + 96) + 96) h2 ha hca fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, -, -, -, b8, b9, b10⟩ := a.2
    rw [hfe a.1 u hu, hfi, hfm]; exact ⟨b8, by omega, by omega, by omega⟩
  refine selfHosted_stack (cb := fun src => fa (ofL (fm (ofL (fi (ofL (fe (ofL src)))))))) h3 fun src p hD hp => ?_
  obtain ⟨u, hu, hb, hl, -⟩ := hD
  obtain ⟨u', hu', hc⟩ := chain_eq src p hp
  rw [hu] at hu'; cases hu'
  show fa (ofL (fm (ofL (fi (ofL (fe (ofL src))))))) = nanoGen p
  rw [hfe src u hu, hfi, hfm, hfa]; exact hc hb hl

end Nano.SelfHost
