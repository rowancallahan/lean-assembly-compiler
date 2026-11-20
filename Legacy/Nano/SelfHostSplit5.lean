/- nano self-hosting with FIVE stages, the front end in two S3 stages: `fA` = lexer + parser 2a (`stage2a ∘ lexB`, box
nano-final's `lexA`), `f2b` = the parser machine `stage2b` (`stage2b (stage2a x) = stage2 x`, Nano/ParseS3B.lean),
then the inliner, the expander and the assembler. The same proof as `selfHosted_parse7` (Nano/SelfHostSplit7.lean)
with fewer `link_stage`s; the size conditions are the fields of `Sz5`. -/
import Legacy.Nano.SelfHostSplit
import Legacy.Nano.ParseS3B

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link Nano.U Nano.B Nano.PB Nano.PS

/-- the size conditions, given the elaborated program `u` -/
structure Sz5 (K : Nat) (sA s2b si sm sa : Nat → Nat) (src : List UInt8) (u : List (Nat × Ex)) : Prop where
  arity : ∀ d ∈ u, d.1 < 256
  defs : u.length ≤ 65536
  t1 : (stage2a (lexB src)).length ≤ 2 ^ 20
  t2 : (stage2a (lexB src)).length ≤ K
  tA : sA src.length ≤ K
  t3 : s2b (stage2a (lexB src)).length ≤ K
  s1 : (serU u).length ≤ 2 ^ 20
  s2 : (serU u).length ≤ K
  s3 : si (serU u).length ≤ K
  i1 : (inlB (serU u)).length ≤ 2 ^ 20
  i2 : (inlB (serU u)).length ≤ K
  i3 : sm (inlB (serU u)).length ≤ K
  m1 : (mexp (inlB (serU u))).length ≤ 2 ^ 20
  m2 : (mexp (inlB (serU u))).length ≤ K
  m3 : sa (mexp (inlB (serU u))).length ≤ K

/-- the size conditions of the five-stage binary on a source -/
def Sized5S (K : Nat) (sA s2b si sm sa : Nat → Nat) (src : List UInt8) : Prop :=
  ∃ u, nanoElabU src = some u ∧ Sz5 K sA s2b si sm sa src u

/-- the work space of the five-stage binary -/
def space5S (K : Nat) : Nat := 4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96

set_option maxRecDepth 20000 in
theorem selfHosted_parse5S {cA c2b ci cm ca : List (BitVec 32)} {fA f2b fi fm fa : ByteArray → List UInt8}
    {sA s2b si sm sa : Nat → Nat} (K : Nat)
    (hA : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) cA fA sA (2 ^ 20) true)
    (h2b : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c2b f2b s2b (2 ^ 20) true)
    (hi : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ci fi si (2 ^ 20) true)
    (hm : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) cm fm sm (2 ^ 20) true)
    (ha : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ca fa sa (2 ^ 20) true)
    (hc2b : c2b.length < 2 ^ 17) (hci : ci.length < 2 ^ 17) (hcm : cm.length < 2 ^ 17) (hca : ca.length < 2 ^ 17)
    (hfA : ∀ x, fA (ofL x) = stage2a (lexB x)) (hf2b : ∀ x, f2b (ofL x) = stage2b x)
    (hfi : ∀ x, fi (ofL x) = inlB x) (hfm : ∀ x, fm (ofL x) = mexp x) (hfa : ∀ x, fa (ofL x) = asm x) :
    SelfHosted (link (link (link (link cA c2b) ci) cm) ca)
      (fun _ => space5S K) (Sized5S K sA s2b si sm sa) nanoCompileA := by
  have hfe : ∀ src u, nanoElabU src = some u → f2b (ofL (fA (ofL src))) = serU u := fun src u hu => by
    rw [hfA, hf2b, stage2b_stage2a, stage2_hfe src u hu]
  have h0 := link_stage (α := SrcIn (Sized5S K sA s2b si sm sa)) K (comap hA fun s => ofL s.1) h2b hc2b
    fun a _ => by
      obtain ⟨u, hu, h⟩ := a.2
      show (fA (ofL a.1)).length ≤ 2 ^ 20 ∧ (fA (ofL a.1)).length ≤ K ∧ sA (ofL a.1).data.toList.length ≤ K ∧
        s2b (fA (ofL a.1)).length ≤ K
      rw [hfA]; exact ⟨h.t1, h.t2, h.tA, h.t3⟩
  have h01 := link_stage (4 * K + 96) h0 hi hci fun a _ => by
    obtain ⟨u, hu, h⟩ := a.2
    rw [hfe a.1 u hu]; exact ⟨h.s1, by have := h.s2; omega, by omega, Nat.le_trans h.s3 (by omega)⟩
  have h02 := link_stage (4 * (4 * K + 96) + 96) h01 hm hcm fun a _ => by
    obtain ⟨u, hu, h⟩ := a.2
    rw [hfe a.1 u hu, hfi]; exact ⟨h.i1, by have := h.i2; omega, by omega, Nat.le_trans h.i3 (by omega)⟩
  have h03 := link_stage (4 * (4 * (4 * K + 96) + 96) + 96) h02 ha hca fun a _ => by
    obtain ⟨u, hu, h⟩ := a.2
    rw [hfe a.1 u hu, hfi, hfm]; exact ⟨h.m1, by have := h.m2; omega, by omega, Nat.le_trans h.m3 (by omega)⟩
  refine selfHosted_stack (cb := fun src => fa (ofL (fm (ofL (fi (ofL (f2b (ofL (fA (ofL src)))))))))) h03
    fun src p hD hp => ?_
  obtain ⟨u, hu, hD⟩ := hD
  obtain ⟨u', hu', hc⟩ := chain_eq src p hp
  rw [hu] at hu'; cases hu'
  show fa (ofL (fm (ofL (fi (ofL (f2b (ofL (fA (ofL src))))))))) = nanoGen p
  rw [hfe src u hu, hfi, hfm, hfa]; exact hc hD.arity hD.defs

end Nano.SelfHost
