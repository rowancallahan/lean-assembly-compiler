/- nano self-hosting with SEVEN stages: the lexer halves `vB`/`eB`, the parser split in 2a (`stage2a`: stage 1's
bytes → tag format) and 2b (`stage2b`: the parser machine), the inliner, the expander, the assembler
(`Nano/ParseS3B.lean`: `stage2b (stage2a x) = stage2 x`). The same proof as `selfHosted_parse6`
(Nano/SelfHostSplit.lean) with one more `link_stage`. The size conditions of the domain are the fields of
`Sized7` (bounds on every intermediate result and every stage's work space). -/
import Legacy.Nano.SelfHostSplit
import Legacy.Nano.ParseS3B

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link Nano.U Nano.B Nano.PB Nano.PS

/-- the size conditions, given the elaborated program `u` -/
structure Sz7 (K : Nat) (s1a s1b s2a s2b si sm sa : Nat → Nat) (src : List UInt8) (u : List (Nat × Ex)) : Prop where
  arity : ∀ d ∈ u, d.1 < 256
  defs : u.length ≤ 65536
  v1 : (vB src).length ≤ 2 ^ 20
  v2 : (vB src).length ≤ K
  v3 : s1a src.length ≤ K
  v4 : s1b (vB src).length ≤ K
  l1 : (lexB src).length ≤ 2 ^ 20
  l2 : (lexB src).length ≤ K
  l3 : s2a (lexB src).length ≤ K
  t1 : (stage2a (lexB src)).length ≤ 2 ^ 20
  t2 : (stage2a (lexB src)).length ≤ K
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

/-- the size conditions of the seven-stage binary on a source -/
def Sized7 (K : Nat) (s1a s1b s2a s2b si sm sa : Nat → Nat) (src : List UInt8) : Prop :=
  ∃ u, nanoElabU src = some u ∧ Sz7 K s1a s1b s2a s2b si sm sa src u

/-- the work space of the seven-stage binary -/
def space7 (K : Nat) : Nat := 4 * (4 * (4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96) + 96) + 96

set_option maxRecDepth 20000 in
theorem selfHosted_parse7 {c1a c1b c2a c2b ci cm ca : List (BitVec 32)}
    {f1a f1b f2a f2b fi fm fa : ByteArray → List UInt8} {s1a s1b s2a s2b si sm sa : Nat → Nat} (K : Nat)
    (h1a : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c1a f1a s1a (2 ^ 20) true)
    (h1b : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c1b f1b s1b (2 ^ 20) true)
    (h2a : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c2a f2a s2a (2 ^ 20) true)
    (h2b : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c2b f2b s2b (2 ^ 20) true)
    (hi : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ci fi si (2 ^ 20) true)
    (hm : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) cm fm sm (2 ^ 20) true)
    (ha : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ca fa sa (2 ^ 20) true)
    (hc1b : c1b.length < 2 ^ 17) (hc2a : c2a.length < 2 ^ 17) (hc2b : c2b.length < 2 ^ 17)
    (hci : ci.length < 2 ^ 17) (hcm : cm.length < 2 ^ 17) (hca : ca.length < 2 ^ 17)
    (hf1a : ∀ x, f1a (ofL x) = vB x) (hf1b : ∀ x, f1b (ofL x) = eB x) (hf2a : ∀ x, f2a (ofL x) = stage2a x)
    (hf2b : ∀ x, f2b (ofL x) = stage2b x) (hfi : ∀ x, fi (ofL x) = inlB x) (hfm : ∀ x, fm (ofL x) = mexp x)
    (hfa : ∀ x, fa (ofL x) = asm x) :
    SelfHosted (link (link (link (link (link (link c1a c1b) c2a) c2b) ci) cm) ca)
      (fun _ => space7 K) (Sized7 K s1a s1b s2a s2b si sm sa) nanoCompileA := by
  have hf1 : ∀ src, f1b (ofL (f1a (ofL src))) = lexB src := fun src => by rw [hf1a, hf1b, eB_vB]
  have hf2 : ∀ src, f2a (ofL (f1b (ofL (f1a (ofL src))))) = stage2a (lexB src) := fun src => by rw [hf1, hf2a]
  have hfe : ∀ src u, nanoElabU src = some u →
      f2b (ofL (f2a (ofL (f1b (ofL (f1a (ofL src))))))) = serU u := fun src u hu => by
    rw [hf2, hf2b, stage2b_stage2a, stage2_hfe src u hu]
  have h00 := link_stage (α := SrcIn (Sized7 K s1a s1b s2a s2b si sm sa)) K (comap h1a fun s => ofL s.1) h1b hc1b
    fun a _ => by
      obtain ⟨u, hu, h⟩ := a.2
      show (f1a (ofL a.1)).length ≤ 2 ^ 20 ∧ (f1a (ofL a.1)).length ≤ K ∧ s1a (ofL a.1).data.toList.length ≤ K ∧
        s1b (f1a (ofL a.1)).length ≤ K
      rw [hf1a]; exact ⟨h.v1, h.v2, h.v3, h.v4⟩
  have h0a := link_stage (4 * K + 96) h00 h2a hc2a fun a _ => by
    obtain ⟨u, hu, h⟩ := a.2
    rw [hf1]; exact ⟨h.l1, by have := h.l2; omega, by omega, Nat.le_trans h.l3 (by omega)⟩
  have h0 := link_stage (4 * (4 * K + 96) + 96) h0a h2b hc2b fun a _ => by
    obtain ⟨u, hu, h⟩ := a.2
    rw [hf2]; exact ⟨h.t1, by have := h.t2; omega, by omega, Nat.le_trans h.t3 (by omega)⟩
  have h01 := link_stage (4 * (4 * (4 * K + 96) + 96) + 96) h0 hi hci fun a _ => by
    obtain ⟨u, hu, h⟩ := a.2
    rw [hfe a.1 u hu]; exact ⟨h.s1, by have := h.s2; omega, by omega, Nat.le_trans h.s3 (by omega)⟩
  have h02 := link_stage (4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96) h01 hm hcm fun a _ => by
    obtain ⟨u, hu, h⟩ := a.2
    rw [hfe a.1 u hu, hfi]
    exact ⟨h.i1, by have := h.i2; omega, by omega, Nat.le_trans h.i3 (by omega)⟩
  have h03 := link_stage (4 * (4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96) + 96) h02 ha hca fun a _ => by
    obtain ⟨u, hu, h⟩ := a.2
    rw [hfe a.1 u hu, hfi, hfm]
    exact ⟨h.m1, by have := h.m2; omega, by omega, Nat.le_trans h.m3 (by omega)⟩
  refine selfHosted_stack
    (cb := fun src => fa (ofL (fm (ofL (fi (ofL (f2b (ofL (f2a (ofL (f1b (ofL (f1a (ofL src)))))))))))))) h03
    fun src p hD hp => ?_
  obtain ⟨u, hu, hD⟩ := hD
  obtain ⟨u', hu', hc⟩ := chain_eq src p hp
  rw [hu] at hu'; cases hu'
  show fa (ofL (fm (ofL (fi (ofL (f2b (ofL (f2a (ofL (f1b (ofL (f1a (ofL src))))))))))))) = nanoGen p
  rw [hfe src u hu, hfi, hfm, hfa]; exact hc hD.arity hD.defs

end Nano.SelfHost
