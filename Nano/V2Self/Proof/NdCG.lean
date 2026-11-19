/- Machine bridge (Opus box E), part (B): Gen's reference code relation (GenRef's CG / CT / CGs) emits exactly the
J templates of Proof/NdSem.lean: `Mt c l h E X` = the words c are `l.map encG`, except at the exit placeholders E
(absolute word indices, inside [h, h + |l|)), where c has 0 and l has `jal x0` to the exit target X. -/
import Nano.V2Self.Proof.NdRun
import Nano.V2Self.Proof.GenRef
import Nano.V2Self.Proof.MachExact
import Nano.V2Self.Proof.ExprBridge
namespace Templates
open CallProbe C GenRef ParSpec

def Mt (c : List UInt64) (l : List J) (h : Nat) (E : List Nat) (X : Nat) : Prop :=
  c.length = l.length ∧ (∀ e ∈ E, h ≤ e ∧ e < h + l.length) ∧
  ∀ j, j < l.length → (h + j ∈ E → c[j]? = some 0 ∧ l[j]? = some (.jal 0 ((X : Int) - ((h + j : Nat) : Int)))) ∧
    (h + j ∉ E → c[j]? = l[j]?.map encG)

theorem Mt.plain (l : List J) (h X : Nat) : Mt (l.map encG) l h [] X :=
  ⟨by simp, by simp, fun j hj => ⟨by simp, fun _ => by simp⟩⟩

theorem Mt.app {c1 c2 : List UInt64} {l1 l2 : List J} {h : Nat} {E1 E2 : List Nat} {X : Nat}
    (h1 : Mt c1 l1 h E1 X) (h2 : Mt c2 l2 (h + l1.length) E2 X) : Mt (c1 ++ c2) (l1 ++ l2) h (E1 ++ E2) X := by
  obtain ⟨a1, b1, f1⟩ := h1; obtain ⟨a2, b2, f2⟩ := h2
  refine ⟨by simp [a1, a2], ?_, ?_⟩
  · intro e he; simp only [List.mem_append] at he
    rcases he with he | he
    · have := b1 e he; simp; omega
    · have := b2 e he; simp; omega
  · intro j hj
    by_cases hj1 : j < l1.length
    · have q := f1 j hj1
      have n2 : h + j ∉ E2 := fun m => by have := b2 _ m; omega
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left hj1]
      refine ⟨fun m => q.1 (by simp only [List.mem_append] at m; exact m.resolve_right n2),
        fun m => q.2 (fun m' => m (List.mem_append_left _ m'))⟩
    · have q := f2 (j - l1.length) (by simp at hj; omega)
      have n1 : h + j ∉ E1 := fun m => by have := b1 _ m; omega
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), a1]
      rw [show h + l1.length + (j - l1.length) = h + j by omega] at q
      refine ⟨fun m => q.1 (by simp only [List.mem_append] at m; exact m.resolve_left n1),
        fun m => q.2 (fun m' => m (List.mem_append_right _ m'))⟩

/-- an emitter with the template property, emitted at word h -/
theorem em_of {F : Buf → Buf} {t : Nat → List J} {B h : Nat}
    (hF : ∀ o : Buf, o.length < B → F o = o ++ (t o.length).map encG) (hh : h < B) : em F h = (t h).map encG := by
  unfold em; rw [hF _ (by simpa using hh)]; simp

/-- Gen's jump word `g13 rd a b` (a, b < 2^32) is `jal rd (b − a)` -/
theorem g13_enc (rd : Nat) (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    g13 rd.toUInt64 a.toUInt64 b.toUInt64 = encG (.jal rd ((b : Int) - (a : Int))) := by
  unfold g13; simp only [encG]; congr 1
  rw [Fixup.off_eq, iu_ofInt]
  congr 1
  simp [Nat.toUInt64, UInt64.toNat_ofNat]; omega

theorem jw_enc (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    jw 0 a b = encG (.jal 0 ((b : Int) - (a : Int))) := g13_enc 0 a b ha hb

theorem ifHd_enc (c : Nat) (hc : c < 2 ^ 32) : ifHd c.toUInt64 = (ifHead4 (cmpJ c)).map encG := by
  have i8 : iu 16 = 16 := by decide
  have i0 : iu 0 = 0 := by decide
  have i8' : iu 8 = 8 := by decide
  have i4 : iu (4 * 2) = 8 := by decide
  unfold ifHd cmpJ
  by_cases h1 : c = 1
  · subst h1; simp [ifHead4, encG, i8, i0, i8', i4]
  · have : (c.toUInt64 == 1) = false := by
      simp [Nat.toUInt64]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    simp [this, h1, ifHead4, encG, i8, i0, i8', i4]

theorem lp_enc (p : Nat) (hp : p < 251) :
    lpHd p.toUInt64 = [encG (.ld 5 8 (slotOff p 0)), encG (.beq 5 0 2)] ∧
    lpDec p.toUInt64 = [encG (.addi 5 5 (-1)), encG (.sd 5 8 (slotOff p 0))] := by
  have g := g24_off p 0 hp (by decide)
  have e0 : (0 : Nat).toUInt64 = 0 := rfl
  rw [e0] at g
  have ho : offOf p 0 = slotOff p 0 := by unfold offOf slotOff; split <;> rfl
  have i4 : iu (4 * 2) = 8 := by decide
  have im : iu (-1) = g_901 := by decide
  refine ⟨?_, ?_⟩ <;> simp [lpHd, lpDec, encG, g, ho, i4, im] <;> rfl

end Templates
