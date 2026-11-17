/- nano self-hosting with the lexer split in two compiled stages (branch nano-closeA): `vB` (validator) and `eB`
(emitter), `eB (vB xs) = lexB xs` (`Nano.B.eB_vB`, Nano/ElabBSplit.lean).  `selfHosted_parse6`: the target
`SelfHosted … nanoCompileA` from SIX stage machine theorems (front-end list form, result length in `a1`): `f1a` = `vB`,
`f1b` = `eB`, `f2` = `stage2`, `fi` = `inlB`, `fm` = `mexp`, `fa` = `asm`; the same proof as `selfHosted_parse`
(Nano/ParseBSelfHost.lean) with one more `link_stage` in front. -/
import Nano.ParseBSelfHost
import Nano.ElabBSplit

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link Nano.U Nano.B Nano.PB

/-- the size conditions of the six-stage binary on a source -/
def Sized6 (K : Nat) (s1a s1b s2 si sm sa : Nat → Nat) (src : List UInt8) : Prop :=
  ∃ u, nanoElabU src = some u ∧ (∀ d ∈ u, d.1 < 256) ∧ u.length ≤ 65536 ∧
    (vB src).length ≤ 2 ^ 20 ∧ (vB src).length ≤ K ∧ s1a src.length ≤ K ∧ s1b (vB src).length ≤ K ∧
    (lexB src).length ≤ 2 ^ 20 ∧ (lexB src).length ≤ K ∧ s2 (lexB src).length ≤ K ∧
    (serU u).length ≤ 2 ^ 20 ∧ (serU u).length ≤ K ∧ si (serU u).length ≤ K ∧
    (inlB (serU u)).length ≤ 2 ^ 20 ∧ (inlB (serU u)).length ≤ K ∧ sm (inlB (serU u)).length ≤ K ∧
    (mexp (inlB (serU u))).length ≤ 2 ^ 20 ∧ (mexp (inlB (serU u))).length ≤ K ∧
    sa (mexp (inlB (serU u))).length ≤ K

/-- the work space of the six-stage binary -/
def space6 (K : Nat) : Nat := 4 * (4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96) + 96

set_option maxRecDepth 20000 in
theorem selfHosted_parse6 {c1a c1b c2 ci cm ca : List (BitVec 32)} {f1a f1b f2 fi fm fa : ByteArray → List UInt8}
    {s1a s1b s2 si sm sa : Nat → Nat} (K : Nat)
    (h1a : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c1a f1a s1a (2 ^ 20) true)
    (h1b : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c1b f1b s1b (2 ^ 20) true)
    (h2 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c2 f2 s2 (2 ^ 20) true)
    (hi : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ci fi si (2 ^ 20) true)
    (hm : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) cm fm sm (2 ^ 20) true)
    (ha : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ca fa sa (2 ^ 20) true)
    (hc1b : c1b.length < 2 ^ 17) (hc2 : c2.length < 2 ^ 17) (hci : ci.length < 2 ^ 17) (hcm : cm.length < 2 ^ 17)
    (hca : ca.length < 2 ^ 17)
    (hf1a : ∀ x, f1a (ofL x) = vB x) (hf1b : ∀ x, f1b (ofL x) = eB x) (hf2 : ∀ x, f2 (ofL x) = stage2 x)
    (hfi : ∀ x, fi (ofL x) = inlB x) (hfm : ∀ x, fm (ofL x) = mexp x) (hfa : ∀ x, fa (ofL x) = asm x) :
    SelfHosted (link (link (link (link (link c1a c1b) c2) ci) cm) ca)
      (fun _ => space6 K) (Sized6 K s1a s1b s2 si sm sa) nanoCompileA := by
  have hf1 : ∀ src, f1b (ofL (f1a (ofL src))) = lexB src := fun src => by rw [hf1a, hf1b, eB_vB]
  have hfe : ∀ src u, nanoElabU src = some u → f2 (ofL (f1b (ofL (f1a (ofL src))))) = serU u := fun src u hu => by
    rw [hf1, hf2, stage2_hfe src u hu]
  have h00 := link_stage (α := SrcIn (Sized6 K s1a s1b s2 si sm sa)) K (comap h1a fun s => ofL s.1) h1b hc1b
    fun a _ => by
      obtain ⟨u, hu, -, -, b1, b2, b3, b4, -⟩ := a.2
      show (f1a (ofL a.1)).length ≤ 2 ^ 20 ∧ (f1a (ofL a.1)).length ≤ K ∧ s1a (ofL a.1).data.toList.length ≤ K ∧
        s1b (f1a (ofL a.1)).length ≤ K
      rw [hf1a]; exact ⟨b1, b2, b3, b4⟩
  have h0 := link_stage (4 * K + 96) h00 h2 hc2 fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, b5, b6, b7, -⟩ := a.2
    rw [hf1]; exact ⟨b5, by omega, by omega, Nat.le_trans b7 (by omega)⟩
  have h01 := link_stage (4 * (4 * K + 96) + 96) h0 hi hci fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, -, -, -, b8, b9, b10, -⟩ := a.2
    rw [hfe a.1 u hu]; exact ⟨b8, by omega, by omega, Nat.le_trans b10 (by omega)⟩
  have h02 := link_stage (4 * (4 * (4 * K + 96) + 96) + 96) h01 hm hcm fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, -, -, -, -, -, -, b11, b12, b13, -⟩ := a.2
    rw [hfe a.1 u hu, hfi]; exact ⟨b11, by omega, by omega, Nat.le_trans b13 (by omega)⟩
  have h03 := link_stage (4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96) h02 ha hca fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, b14, b15, b16⟩ := a.2
    rw [hfe a.1 u hu, hfi, hfm]; exact ⟨b14, by omega, by omega, Nat.le_trans b16 (by omega)⟩
  refine selfHosted_stack
    (cb := fun src => fa (ofL (fm (ofL (fi (ofL (f2 (ofL (f1b (ofL (f1a (ofL src)))))))))))) h03 fun src p hD hp => ?_
  obtain ⟨u, hu, hb, hl, -⟩ := hD
  obtain ⟨u', hu', hc⟩ := chain_eq src p hp
  rw [hu] at hu'; cases hu'
  show fa (ofL (fm (ofL (fi (ofL (f2 (ofL (f1b (ofL (f1a (ofL src))))))))))) = nanoGen p
  rw [hfe src u hu, hfi, hfm, hfa]; exact hc hb hl

end Nano.SelfHost
