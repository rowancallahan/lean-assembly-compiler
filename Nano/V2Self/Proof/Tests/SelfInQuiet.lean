/- Nano/V2Self/Proof/Tests/SelfInQuiet: step B towards `Nonempty SelfIn`.  `F inp j`: the meaning of def `j` of C's
source inside the whole program; `quiet`: the 171 push-free defs (`S`, closed under calls; checked by the kernel) never
report `cap`, on any input and any arguments. -/
import Nano.V2Self.Proof.Tests.SelfInCapFree
import Nano.V2Self.Proof.Cert.PC

namespace Cert.CapFree
open NanoMain ParSpec

/-- the defs of C's source without a push whose callees are all in the list (generated: fixpoint over PC.all) -/
def S : List Nat := [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 18, 19, 20, 21, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 130, 132, 140, 141, 143, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 158, 159, 160, 161, 163, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 213, 217, 221, 226, 229, 234, 238, 239, 241, 242, 243]

/-- every def in `S` has a push-free body calling only earlier members of `S` -/
theorem S_ok : (S.all fun j => match PC.all[j]? with
    | some d => nf (S.filter (· < j)) d.body
    | none => false) = true := by decide +kernel

/-- the meanings of the first `j` defs -/
def Pre (inp : List UInt8) (j : Nat) : List Fn := means inp κC [] (PC.all.take j)

theorem means_append (inp : List UInt8) (κ : Nat) : ∀ (p q : List DefA) (ms : List Fn),
    means inp κ ms (p ++ q) = means inp κ (means inp κ ms p) q
  | [], q, ms => rfl
  | d :: p, q, ms => by simp only [List.cons_append, means]; exact means_append inp κ p q _

theorem means_prefix (inp : List UInt8) (κ : Nat) : ∀ (p : List DefA) (ms : List Fn), ∃ r, means inp κ ms p = ms ++ r ∧ r.length = p.length
  | [], ms => ⟨[], by simp [means], rfl⟩
  | d :: p, ms => by
    obtain ⟨r, h1, h2⟩ := means_prefix inp κ p (ms ++ [defMean inp κ ms d])
    exact ⟨defMean inp κ ms d :: r, by simp only [means, h1, List.append_assoc, List.singleton_append], by simp [h2]⟩

/-- the meaning of def `j` inside the program -/
def F (inp : List UInt8) (j : Nat) (d : DefA) : Fn := defMean inp κC (Pre inp j) d

theorem pre_length (inp : List UInt8) (j : Nat) (hj : j ≤ PC.all.length) : (Pre inp j).length = j := by
  obtain ⟨r, h1, h2⟩ := means_prefix inp κC (PC.all.take j) []
  unfold Pre; rw [h1]; simp [h2]; omega

/-- looking up an earlier def in a prefix -/
theorem pre_get (inp : List UInt8) {i j : Nat} (hij : i < j) (hj : j ≤ PC.all.length) :
    (Pre inp j)[i]? = some (F inp i (PC.all[i]'(by omega))) := by
  have e : PC.all.take j = PC.all.take i ++ (PC.all[i]'(by omega) :: (PC.all.take j).drop (i + 1)) := by
    have h1 : (PC.all.take j).take i = PC.all.take i := by rw [List.take_take]; congr 1; omega
    have h2 : (PC.all.take j)[i]'(by simp; omega) = PC.all[i]'(by omega) := by simp
    have h3 := List.take_append_drop i (PC.all.take j)
    rw [List.drop_eq_getElem_cons (by simp; omega), h1, h2] at h3
    exact h3.symm
  unfold Pre
  rw [e, means_append]
  simp only [means]
  obtain ⟨r, h1, _⟩ := means_prefix inp κC ((PC.all.take j).drop (i + 1)) (means inp κC [] (PC.all.take i) ++ [defMean inp κC (means inp κC [] (PC.all.take i)) (PC.all[i]'(by omega))])
  rw [h1, List.append_assoc]
  have hl := pre_length inp i (by omega)
  unfold Pre at hl
  rw [List.getElem?_append_right (by omega), hl]; simp [F, Pre]

/-- **the push-free defs never report `cap`** -/
theorem quiet (inp : List UInt8) : ∀ (j : Nat) (hj : j < PC.all.length), j ∈ S → ∀ ps, F inp j (PC.all[j]) ps ≠ .error .cap := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hj hS ps
    have hok := List.all_eq_true.mp S_ok j hS
    rw [List.getElem?_eq_getElem hj] at hok
    refine defMean_nocap (S := S.filter (· < j)) (fun i hi G hG ps' => ?_) hok ps
    simp only [List.mem_filter, decide_eq_true_eq] at hi
    rw [pre_get inp hi.2 (by omega)] at hG
    cases hG
    exact ih i hi.2 (by omega) hi.1 ps'

end Cert.CapFree
