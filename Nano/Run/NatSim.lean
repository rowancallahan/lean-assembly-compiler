/- The bridge between the general relation `GTarget.Rel` of the native target at an anchor and ArmNat's `NMid`
(M3): at an anchor whose byte offset is word `q` of the image's words `A`, a related machine state shows the VIEW
`mview s st` (the machine's registers through `armReg`, J's memory) at word `q`, and the view agrees with the J state
off the anchor's dead registers (`Agree`); conversely an `NMid` state whose view agrees with a J state off the dead
set of an anchor is related there.  A segment case of an atom is then: `nmid_of_rel`, ArmNat steps on the view, the J
steps on the J state, `rel_of_nmid`. -/
import Nano.Run.NatImg
import Nano.Run.NatTarget
import Nano.Run.GUniform
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {V : List J → Img → Prop}

/-- the machine's view of the J state: registers from the machine, the rest from `st` -/
def mview (s : M.State) (st : CallProbe.St) : CallProbe.St :=
  { st with x := fun j => if 0 < j ∧ j < 32 then (M.observe s).register (armReg j) else 0 }

/-- the view `v` agrees with the J state `st` off the registers `D` -/
structure Agree (D : Nat → Prop) (v st : CallProbe.St) : Prop where
  x : ∀ j, 0 < j → j < 32 → ¬ D j → v.x j = st.x j
  m : v.m = st.m
  x0 : st.x 0 = 0

theorem wordBytes_len (A : List Nat) : (wordBytes A).length = 4 * A.length := by
  unfold wordBytes; exact flat_len _ 4 (fun _ => rfl) A

theorem wordBytes_get (A : List Nat) (i : Nat) (hi : i < A.length) (k : Nat) (hk : k < 4) :
    (wordBytes A)[4 * i + k]? = some (wbyte (BitVec.ofNat 32 A[i]) k) := by
  unfold wordBytes
  rw [flat_get _ 4 (fun _ => rfl) A i k hi hk]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- **from the relation to the view**: at an anchor at word `q` of the image's words `A` -/
theorem nmid_of_rel {K : LayW} {C : List J} {I : Img} {s0 s : M.State} {p : Nat × CallProbe.St} {A : List Nat} {q : Nat}
    (hl : JTarget.LayOK M I.code.length K) (hR : (natTarget M X W V).Rel K C I s0 p s) (hI : I.code = wordBytes A)
    (hq : I.off p.1 = 4 * q) :
    NMid X W K A s0 (mview s p.2) q s ∧ Agree (I.dead p.1) (mview s p.2) p.2 := by
  have hlen : I.code.length = 4 * A.length := by rw [hI, wordBytes_len]
  refine ⟨⟨hR.cfg, by rw [← hq]; exact hR.pc, ?_, by simp [mview], fun j h0 h32 => by simp [mview, h0, h32],
    hR.keep, hR.w, hR.bw, hR.fr, hlen ▸ hl, (show PermOK X W K (4 * A.length) s by rw [← hlen]; exact hR.inv)⟩, ⟨fun j h0 h32 hd => ?_, rfl, hR.x0⟩⟩
  · intro i hi k hk
    have hlt : 4 * i + k < I.code.length := by omega
    have : (M.observe s).memory (UInt64.ofNat (K.base + (4 * i + k))) = some I.code[4 * i + k] := hR.code (4 * i + k) hlt
    rw [show K.base + 4 * i + k = K.base + (4 * i + k) by omega, this]
    have e := wordBytes_get A i hi k hk
    rw [← hI, List.getElem?_eq_getElem hlt] at e
    exact e
  · simp only [mview, h0, h32, and_self, if_true]; exact hR.x j h0 h32 hd

/-- **from the view to the relation**: at an anchor `pc` at word `q` -/
theorem rel_of_nmid {K : LayW} {C : List J} {I : Img} {s0 s : M.State} {A : List Nat} {q pc : Nat}
    {v st : CallProbe.St} (hM : NMid X W K A s0 v q s) (hag : Agree (I.dead pc) v st) (hI : I.code = wordBytes A)
    (hq : I.off pc = 4 * q) (hb : st.b = K.base) (hly : st.ly = I.ly) :
    (natTarget M X W V).Rel K C I s0 (pc, st) s := by
  have hlen : I.code.length = 4 * A.length := by rw [hI, wordBytes_len]
  refine ⟨hM.cfg, by show (M.observe s).programCounter = _; rw [hq]; exact hM.pc, ?_, hag.x0, hb, hly,
    fun j h0 h32 hd => (hM.x j h0 h32).trans (hag.x j h0 h32 hd), hM.keep, fun a ha k hk => by rw [← hag.m]; exact hM.w a ha k hk,
    fun a ha => by rw [← hag.m]; exact hM.bw a ha, hM.fr, (show PermOK X W K I.code.length s by rw [hlen]; exact hM.pm)⟩
  intro a ha
  have hi : a / 4 < A.length := by omega
  have hk := Nat.mod_lt a (show 0 < 4 by decide)
  have e := wordBytes_get A (a / 4) hi (a % 4) hk
  rw [show 4 * (a / 4) + a % 4 = a by omega, ← hI, List.getElem?_eq_getElem ha] at e
  have := hM.code (a / 4) hi (a % 4) hk
  rw [show K.base + 4 * (a / 4) + a % 4 = K.base + a by omega] at this
  exact (this.trans e.symm : (M.observe s).memory (UInt64.ofNat (K.base + a)) = some I.code[a])

end JT
