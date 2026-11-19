/- Nano/V2Self/Proof/Tests/AuditSpace: audit gap A2 — a CONCRETE memory bound.  For ParSpec's `ex1` (MainWitness.x2) on
input `[5]`, C's work bound `spaceC` (= `memoryNeeded` of `compileC`) is at most 4,194,416 bytes, far below RAM (2^31).
The run of main with that much room is evaluated in the kernel at one position (2^31, empty output buffer); `shiftInv`
moves it to every admissible position, `semAtF_pcT` to every output buffer. -/
import Nano.V2Self.Proof.Bridge.MainShift4
import Nano.V2Self.Proof.Machine.RunsThr
import Nano.V2Self.Proof.Tests.MainWitness
namespace NanoMain.AuditSpace
open ParSpec Templates

theorem hs2 : (refParse (C.s10 Witness.x2)).isSome = true := by decide +kernel

/-- ex1's reference parse -/
def p2 : List DefA := (refParse (C.s10 Witness.x2)).get hs2

theorem hp2 : ParsesProgram (C.s10 Witness.x2) p2 := by unfold ParsesProgram p2; simp

theorem pOf2 : pOf Witness.x2 = some p2 := pOf_eq Witness.w2.1 hp2

theorem lin2 : LinearK p2 := by
  obtain ⟨p, hp, -, hL, -⟩ := Witness.w2.2.1
  rw [Option.some.inj (hp2.symm.trans hp)]; exact hL

/-! ## kernel-reducible copies of `svF` and `semAtF` (both are compiled by well-founded recursion) -/
mutual
def svS (K : SC) (fsX : Nat → SemDX) : Nd → SemWX
  | .const v => leafF (fun _ => v)
  | .loc s w => localF s w
  | .bin op a b => fin2F (pairF 1 (svS K fsX a) (svS K fsX b)) (fun a b sp H => ofO .stuck (aluF2 op a b sp H))
  | .ite c a b t e => ifF c (pairF 1 (svS K fsX a) (svS K fsX b)) (svS K fsX t) (svS K fsX e)
  | .letE s w v b => letF s w (svS K fsX v) (svS K fsX b)
  | .pair cs => svLS K fsX cs
  | .call id as => callF (K.npwOf id) (svLS K fsX as) (fsX id)
  | .prim pn as =>
    if pn = 1 ∨ pn = 3 then leafF (fun _ => K.c29)
    else if pn = 5 then oneF (bnewF K.κ)
    else if pn = 2 ∨ pn = 6 then fin1F (svLS K fsX as) (fun a sp H => ofO .stuck (primF1 K pn a sp H))
    else if pn = 8 then fin3F (svLS K fsX as) (fun a b c sp H => ofO .stuck (bsetF K.hb a b c sp H))
    else fin2F (svLS K fsX as) (primF2F K pn)
  | .loop z s => loopF K.p (stS K fsX z) (stS K fsX s)
  | .cont _ => fun _ _ _ => .error .stuck
termination_by structural e => e
def stS (K : SC) (fsX : Nat → SemDX) : Nd → SemTX
  | .ite c a b t e => ifTF c (pairF 1 (svS K fsX a) (svS K fsX b)) (stS K fsX t) (stS K fsX e)
  | .letE s w v b => letTF s w (svS K fsX v) (stS K fsX b)
  | .cont e => contF (svS K fsX e)
  | .const v => exitF (leafF (fun _ => v))
  | .loc s w => exitF (localF s w)
  | .bin op a b => exitF (fin2F (pairF 1 (svS K fsX a) (svS K fsX b)) (fun a b sp H => ofO .stuck (aluF2 op a b sp H)))
  | .pair cs => exitF (svLS K fsX cs)
  | .call id as => exitF (callF (K.npwOf id) (svLS K fsX as) (fsX id))
  | .prim pn as => exitF (
    if pn = 1 ∨ pn = 3 then leafF (fun _ => K.c29)
    else if pn = 5 then oneF (bnewF K.κ)
    else if pn = 2 ∨ pn = 6 then fin1F (svLS K fsX as) (fun a sp H => ofO .stuck (primF1 K pn a sp H))
    else if pn = 8 then fin3F (svLS K fsX as) (fun a b c sp H => ofO .stuck (bsetF K.hb a b c sp H))
    else fin2F (svLS K fsX as) (primF2F K pn))
  | .loop z s => exitF (loopF K.p (stS K fsX z) (stS K fsX s))
termination_by structural e => e
def svLS (K : SC) (fsX : Nat → SemDX) : List Nd → SemWX
  | [] => nilF
  | c :: cs => pairF (wd K c) (svS K fsX c) (svLS K fsX cs)
termination_by structural cs => cs
end

mutual
theorem svS_eq (K : SC) (fsX : Nat → SemDX) : ∀ e : Nd, svS K fsX e = svF K fsX e
  | .const v => by rw [svS, svF]
  | .loc s w => by rw [svS, svF]
  | .bin op a b => by rw [svS, svF, svS_eq K fsX a, svS_eq K fsX b]
  | .ite c a b t e => by rw [svS, svF, svS_eq K fsX a, svS_eq K fsX b, svS_eq K fsX t, svS_eq K fsX e]
  | .letE s w v b => by rw [svS, svF, svS_eq K fsX v, svS_eq K fsX b]
  | .pair cs => by rw [svS, svF, svLS_eq K fsX cs]
  | .call id as => by rw [svS, svF, svLS_eq K fsX as]
  | .prim pn as => by rw [svS, svF, svLS_eq K fsX as]
  | .loop z s => by rw [svS, svF, stS_eq K fsX z, stS_eq K fsX s]
  | .cont _ => by rw [svS, svF]
theorem stS_eq (K : SC) (fsX : Nat → SemDX) : ∀ e : Nd, stS K fsX e = stF K fsX e
  | .ite c a b t e => by rw [stS, stF, svS_eq K fsX a, svS_eq K fsX b, stS_eq K fsX t, stS_eq K fsX e]
  | .letE s w v b => by rw [stS, stF, svS_eq K fsX v, stS_eq K fsX b]
  | .cont e => by rw [stS, stF, svS_eq K fsX e]
  | .const v => by simp only [stS, stF, svF]
  | .loc s w => by simp only [stS, stF, svF]
  | .bin op a b => by simp only [stS, stF, svF, svS_eq K fsX a, svS_eq K fsX b]
  | .pair cs => by simp only [stS, stF, svF, svLS_eq K fsX cs]
  | .call id as => by simp only [stS, stF, svF, svLS_eq K fsX as]
  | .prim pn as => by simp only [stS, stF, svF, svLS_eq K fsX as]
  | .loop z s => by simp only [stS, stF, svF, stS_eq K fsX z, stS_eq K fsX s]
theorem svLS_eq (K : SC) (fsX : Nat → SemDX) : ∀ cs : List Nd, svLS K fsX cs = svLF K fsX cs
  | [] => by rw [svLS, svLF]
  | c :: cs => by rw [svLS, svLF, svS_eq K fsX c, svLS_eq K fsX cs]
end

/-- `semAtF` by structural recursion (kernel-reducible): `tab P ds k n = semAtF P ds n` for `n < k` -/
def tab (P : Templates.PC) (ds : List DefA) : Nat → Nat → SemDX
  | 0 => fun _ => dfltF
  | k + 1 => fun n => if n < k then tab P ds k n else
      defSF (dA ds k).npw (dA ds k).nslots (svS (scAt P ds k) (fun m => if m < k then tab P ds k m else dfltF) (dA ds k).body)

theorem tab_eq (P : Templates.PC) (ds : List DefA) : ∀ k n, n < k → tab P ds k n = semAtF P ds n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, h => by
    simp only [tab]
    split
    · exact tab_eq P ds k n ‹_›
    · have e : n = k := by omega
      subst e
      rw [semAtF, svS_eq]; congr 2; funext m
      by_cases hm : m < n
      · rw [if_pos hm, dif_pos hm, tab_eq P ds n m hm]
      · rw [if_neg hm, dif_neg hm]

def notRoom : Except Fail (List UInt64 × Hp) → Bool
  | .error .room => false
  | _ => true

/-- kernel run: with 4,194,400 usable bytes at position 2^31, main on `[5]` does not run out of room -/
theorem run2 : notRoom (RS p2 [5] [] (2 ^ 31) 4194400) = true := by
  unfold RS; rw [← tab_eq _ _ (p2.length - 1 + 1) _ (Nat.lt_succ_self _)]; decide +kernel

theorem good2 : GoodU p2 [5] 4194400 := by
  intro T hb h8 h31 h32 hr
  have hr' : RS p2 [5] [] hb 4194400 = .error .room := by
    unfold RS at hr ⊢; rw [SimW.semAtF_pcT κC hb _ _ [] T p2]; exact hr
  have := (shiftInv _ p2 hp2 (by decide +kernel) lin2 [5] (by decide) [] hb (2 ^ 31) 4194400 h8 (by decide) h31
    (Nat.le_refl _) h32 (by decide)).1 hr'
  have r := run2; rw [this] at r; cases r

/-- **audit A2**: `memoryNeeded` for ex1 on input `[5]` is at most 4,194,416 bytes -/
theorem spaceC_ex1 : spaceC Witness.x2 [5] ≤ 4194416 := by
  have h := lfind_le (GoodU p2 [5]) (2 ^ 32) 0 4194400 (Nat.zero_le _) (by decide) good2
  have h16 := Msp_ge p2 [5]
  unfold spaceC; rw [pOf2]; simp only; unfold Msp; unfold thr at *; omega

/-- kernel run: with 4,194,399 usable bytes main on `[5]` DOES run out of room -/
theorem run2' : notRoom (RS p2 [5] [] (2 ^ 31) 4194399) = false := by
  unfold RS; rw [← tab_eq _ _ (p2.length - 1 + 1) _ (Nat.lt_succ_self _)]; decide +kernel

/-- **audit A2, exact**: `memoryNeeded` for ex1 on input `[5]` is exactly 4,194,416 bytes (4 MiB for one BNEW buffer of
capacity κC = 524,288 words, plus headers, frames and the 16-byte reserve) -/
theorem spaceC_ex1_eq : spaceC Witness.x2 [5] = 4194416 := by
  have hr : RS p2 [5] [] (2 ^ 31) 4194399 = .error .room := by
    have := run2'; revert this; cases RS p2 [5] [] (2 ^ 31) 4194399 with
    | error f => cases f <;> simp [notRoom]
    | ok _ => simp [notRoom]
  have hlt := room_lt (by decide) (Nat.le_refl _) (by decide) hr
  have h := lfind_le (GoodU p2 [5]) (2 ^ 32) 0 4194400 (Nat.zero_le _) (by decide) good2
  unfold spaceC; rw [pOf2]; simp only; unfold Msp; unfold thr at *; omega

end NanoMain.AuditSpace
