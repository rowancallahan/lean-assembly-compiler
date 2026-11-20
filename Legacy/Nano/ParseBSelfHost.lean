/- nano stage 2 in the self-hosting composition (branch `nano-parse`).
`selfHosted_parse`: the target `SelfHosted … nanoCompileA` from FIVE stage machine theorems (front-end list form,
result length in `a1`): `f1` = stage 1 (`lexB`, compiled: `Nano.Self.lexBE.implements1`), `f2` = stage 2
(`Nano.PB.stage2`, NOT compiled yet), `fi` = `inlB`, `fm` = `mexp`, `fa` = `asm` (compiled).  The equation premise of
`selfHosted_four` (`hfe`: the front end emits `serU u`) is discharged by `stage2_hfe`; only the stage machine theorems
and the size domain remain. -/
import Legacy.Nano.SelfHostChain
import Legacy.Nano.ParseBGas
import Legacy.Nano.AsmSelf

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link Nano.U Nano.B Nano.PB

/-- the size conditions of the five-stage binary on a source -/
def Sized5 (K : Nat) (s1 s2 si sm sa : Nat → Nat) (src : List UInt8) : Prop :=
  ∃ u, nanoElabU src = some u ∧ (∀ d ∈ u, d.1 < 256) ∧ u.length ≤ 65536 ∧
    (lexB src).length ≤ 2 ^ 20 ∧ (lexB src).length ≤ K ∧ s1 src.length ≤ K ∧ s2 (lexB src).length ≤ K ∧
    (serU u).length ≤ 2 ^ 20 ∧ (serU u).length ≤ K ∧ si (serU u).length ≤ K ∧
    (inlB (serU u)).length ≤ 2 ^ 20 ∧ (inlB (serU u)).length ≤ K ∧ sm (inlB (serU u)).length ≤ K ∧
    (mexp (inlB (serU u))).length ≤ 2 ^ 20 ∧ (mexp (inlB (serU u))).length ≤ K ∧
    sa (mexp (inlB (serU u))).length ≤ K

set_option maxRecDepth 20000 in
theorem selfHosted_parse {c1 c2 ci cm ca : List (BitVec 32)} {f1 f2 fi fm fa : ByteArray → List UInt8}
    {s1 s2 si sm sa : Nat → Nat} (K : Nat)
    (h1 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c1 f1 s1 (2 ^ 20) true)
    (h2 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c2 f2 s2 (2 ^ 20) true)
    (hi : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ci fi si (2 ^ 20) true)
    (hm : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) cm fm sm (2 ^ 20) true)
    (ha : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ca fa sa (2 ^ 20) true)
    (hc2 : c2.length < 2 ^ 17) (hci : ci.length < 2 ^ 17) (hcm : cm.length < 2 ^ 17) (hca : ca.length < 2 ^ 17)
    (hf1 : ∀ x, f1 (ofL x) = lexB x) (hf2 : ∀ x, f2 (ofL x) = stage2 x)
    (hfi : ∀ x, fi (ofL x) = inlB x) (hfm : ∀ x, fm (ofL x) = mexp x) (hfa : ∀ x, fa (ofL x) = asm x) :
    SelfHosted (link (link (link (link c1 c2) ci) cm) ca)
      (fun _ => 4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96) (Sized5 K s1 s2 si sm sa) nanoCompileA := by
  have hfe : ∀ src u, nanoElabU src = some u → f2 (ofL (f1 (ofL src))) = serU u := fun src u hu => by
    rw [hf1, hf2, stage2_hfe src u hu]
  have h0 := link_stage (α := SrcIn (Sized5 K s1 s2 si sm sa)) K (comap h1 fun s => ofL s.1) h2 hc2 fun a _ => by
    obtain ⟨u, hu, -, -, b1, b2, b3, b4, -⟩ := a.2
    show (f1 (ofL a.1)).length ≤ 2 ^ 20 ∧ (f1 (ofL a.1)).length ≤ K ∧ s1 (ofL a.1).data.toList.length ≤ K ∧
      s2 (f1 (ofL a.1)).length ≤ K
    rw [hf1]; exact ⟨b1, b2, b3, b4⟩
  have h01 := link_stage (4 * K + 96) h0 hi hci fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, b5, b6, b7, -⟩ := a.2
    rw [hfe a.1 u hu]; exact ⟨b5, by omega, by omega, Nat.le_trans b7 (by omega)⟩
  have h02 := link_stage (4 * (4 * K + 96) + 96) h01 hm hcm fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, -, -, -, b8, b9, b10, -⟩ := a.2
    rw [hfe a.1 u hu, hfi]; exact ⟨b8, by omega, by omega, Nat.le_trans b10 (by omega)⟩
  have h03 := link_stage (4 * (4 * (4 * K + 96) + 96) + 96) h02 ha hca fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, -, -, -, -, -, -, b11, b12, b13⟩ := a.2
    rw [hfe a.1 u hu, hfi, hfm]; exact ⟨b11, by omega, by omega, Nat.le_trans b13 (by omega)⟩
  refine selfHosted_stack (cb := fun src => fa (ofL (fm (ofL (fi (ofL (f2 (ofL (f1 (ofL src)))))))))) h03
    fun src p hD hp => ?_
  obtain ⟨u, hu, hb, hl, -⟩ := hD
  obtain ⟨u', hu', hc⟩ := chain_eq src p hp
  rw [hu] at hu'; cases hu'
  show fa (ofL (fm (ofL (fi (ofL (f2 (ofL (f1 (ofL src))))))))) = nanoGen p
  rw [hfe src u hu, hfi, hfm, hfa]; exact hc hb hl

end Nano.SelfHost

namespace Nano.SelfHost
open Proven Nano Nano.Link Nano.B Nano.PB

set_option maxRecDepth 100000 in
theorem nanoAsm_code_len : Nano.Self.nanoAsm.code.length < 2 ^ 17 := by decide +kernel

/-- `selfHosted_parse` with the compiled assembler (`Nano.Self.nanoAsm.implements1`) plugged in: what remains are
the machine theorems of stage 1, stage 2, the inliner and the expander -/
theorem selfHosted_parse_asm {c1 c2 ci cm : List (BitVec 32)} {f1 f2 fi fm : ByteArray → List UInt8}
    {s1 s2 si sm : Nat → Nat} (K : Nat)
    (h1 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c1 f1 s1 (2 ^ 20) true)
    (h2 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c2 f2 s2 (2 ^ 20) true)
    (hi : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ci fi si (2 ^ 20) true)
    (hm : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) cm fm sm (2 ^ 20) true)
    (hc2 : c2.length < 2 ^ 17) (hci : ci.length < 2 ^ 17) (hcm : cm.length < 2 ^ 17)
    (hf1 : ∀ x, f1 (ofL x) = lexB x) (hf2 : ∀ x, f2 (ofL x) = stage2 x)
    (hfi : ∀ x, fi (ofL x) = U.inlB x) (hfm : ∀ x, fm (ofL x) = mexp x) :
    SelfHosted (link (link (link (link c1 c2) ci) cm) Nano.Self.nanoAsm.code)
      (fun _ => 4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96)
      (Sized5 K s1 s2 si sm (fun _ => 8 * (Nano.Self.nanoAsm.slots + 1) + 7)) nanoCompileA :=
  selfHosted_parse K h1 h2 hi hm Nano.Self.nanoAsm.implements1 hc2 hci hcm nanoAsm_code_len hf1 hf2 hfi hfm
    (fun _ => rfl)

end Nano.SelfHost
