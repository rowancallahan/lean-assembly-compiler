/- Machine bridge (Opus box E): the side conditions of the node theorem, `OkV` / `OkT` / `OkL`: widths (Gen's g53
pass) and scoping (the parser's slot discipline), and `At` helpers.  The node theorem itself is `runVO` / `runTO` /
`runLO` (CapNode.lean, all outcomes). -/
import Nano.V2Self.Proof.Machine.NdSem
namespace Templates
open CallProbe ParSpec

/-- operand count of a prim -/
def arity (pn : Nat) : Nat := if pn = 1 ∨ pn = 3 ∨ pn = 5 then 0 else if pn = 2 ∨ pn = 6 then 1 else if pn = 8 then 3 else 2

mutual
def OkV (K : SC) : Nd → Prop
  | .const _ => True
  | .loc s w => s + w ≤ K.nl
  | .bin _ a b => OkV K a ∧ OkV K b ∧ wd K a = 1 ∧ wd K b = 1 ∧ (∀ k, rd b k → ¬ wr K.p a k)
  | .ite _ a b t e => OkV K a ∧ OkV K b ∧ OkV K t ∧ OkV K e ∧ wd K a = 1 ∧ wd K b = 1 ∧ wd K e = wd K t ∧
      (∀ k, rd b k → ¬ wr K.p a k) ∧ (∀ k, rd t k → ¬ (wr K.p a k ∨ wr K.p b k)) ∧
      (∀ k, rd e k → ¬ (wr K.p a k ∨ wr K.p b k))
  | .letE s w v b => OkV K v ∧ OkV K b ∧ wd K v = w ∧ s + w ≤ K.nl ∧
      (∀ k, rd b k → ¬ (s ≤ k ∧ k < s + w) → ¬ wr K.p v k)
  | .pair cs => OkL K cs
  | .call id as => OkL K as ∧ id < K.nd ∧ wdL K as = K.npwOf id
  | .prim pn as => OkL K as ∧ wdL K as = arity pn ∧ ((pn = 1 ∨ pn = 3 ∨ pn = 5) → as = [])
  | .loop z s => OkT K z K.q ∧ OkT K s K.q ∧ 1 ≤ K.p ∧ K.p ≤ K.nl ∧
      (∀ k, (wr K.p z k ∨ wr K.p s k) → K.p ≤ k) ∧ (∀ k, (rd z k ∨ rd s k) → ¬ (wr K.p z k ∨ wr K.p s k))
  | .cont _ => False
/-- tail mode with exit width w -/
def OkT (K : SC) : Nd → Nat → Prop
  | .ite _ a b t e, w => OkV K a ∧ OkV K b ∧ OkT K t w ∧ OkT K e w ∧ wd K a = 1 ∧ wd K b = 1 ∧
      (∀ k, rd b k → ¬ wr K.p a k) ∧ (∀ k, rd t k → ¬ (wr K.p a k ∨ wr K.p b k)) ∧
      (∀ k, rd e k → ¬ (wr K.p a k ∨ wr K.p b k))
  | .letE s w' v b, w => OkV K v ∧ OkT K b w ∧ wd K v = w' ∧ s + w' ≤ K.nl ∧
      (∀ k, rd b k → ¬ (s ≤ k ∧ k < s + w') → ¬ wr K.p v k)
  | .cont e, _ => OkV K e ∧ wd K e = K.p - 1 ∧ 1 ≤ K.p ∧ K.p ≤ K.nl
  | e, w => OkV K e ∧ wd K e = w
def OkL (K : SC) : List Nd → Prop
  | [] => True
  | c :: cs => OkV K c ∧ OkL K cs ∧ (∀ k, rdL cs k → ¬ wr K.p c k)
end


theorem At.mid {C : List J} {h : Nat} {l1 l2 l3 : List J} (hC : At C h (l1 ++ l2 ++ l3)) :
    At C h l1 ∧ At C (h + l1.length) l2 ∧ At C (h + l1.length + l2.length) l3 := by
  refine ⟨hC.left.left, hC.left.right, ?_⟩
  have := hC.right; simpa [Nat.add_assoc] using this

theorem At.cast {C : List J} {a b : Nat} {l : List J} (h : At C a l) (e : a = b) : At C b l := e ▸ h

theorem At.one {C : List J} {a : Nat} {x : J} (h : At C a [x]) : C[a]? = some x := by
  have := h 0 (by simp); simpa using this

end Templates
