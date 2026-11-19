/- Machine bridge (Opus box E): the node theorem's side conditions split by origin.
`WdV`/`WdT`/`WdL` = the WIDTH facts (Gen's width pass g53, A's `W`); `ScV`/`ScT`/`ScL` = SCOPING and slot facts
(the parser's slot discipline).  `okV_of` : WdV ∧ ScV → OkV (and the tail / list versions). -/
import Nano.V2Self.Proof.Machine.NdRun
namespace Templates
open CallProbe ParSpec

mutual
def WdV (K : SC) : Nd → Prop
  | .const _ => True
  | .loc _ _ => True
  | .bin _ a b => WdV K a ∧ WdV K b ∧ wd K a = 1 ∧ wd K b = 1
  | .ite _ a b t e => WdV K a ∧ WdV K b ∧ WdV K t ∧ WdV K e ∧ wd K a = 1 ∧ wd K b = 1 ∧ wd K e = wd K t
  | .letE _ w v b => WdV K v ∧ WdV K b ∧ wd K v = w
  | .pair cs => WdL K cs
  | .call n as => WdL K as ∧ wdL K as = K.npwOf n
  | .prim pn as => WdL K as ∧ wdL K as = arity pn ∧ ((pn = 1 ∨ pn = 3 ∨ pn = 5) → as = [])
  | .loop z s => WdT K z K.q ∧ WdT K s K.q
  | .cont _ => True
def WdT (K : SC) : Nd → Nat → Prop
  | .ite _ a b t e, w => WdV K a ∧ WdV K b ∧ WdT K t w ∧ WdT K e w ∧ wd K a = 1 ∧ wd K b = 1
  | .letE _ w' v b, w => WdV K v ∧ WdT K b w ∧ wd K v = w'
  | .cont e, _ => WdV K e ∧ wd K e = K.p - 1
  | e, w => WdV K e ∧ wd K e = w
def WdL (K : SC) : List Nd → Prop
  | [] => True
  | c :: cs => WdV K c ∧ WdL K cs
end

mutual
def ScV (K : SC) : Nd → Prop
  | .const _ => True
  | .loc s w => s + w ≤ K.nl
  | .bin _ a b => ScV K a ∧ ScV K b ∧ (∀ k, rd b k → ¬ wr K.p a k)
  | .ite _ a b t e => ScV K a ∧ ScV K b ∧ ScV K t ∧ ScV K e ∧
      (∀ k, rd b k → ¬ wr K.p a k) ∧ (∀ k, rd t k → ¬ (wr K.p a k ∨ wr K.p b k)) ∧
      (∀ k, rd e k → ¬ (wr K.p a k ∨ wr K.p b k))
  | .letE s w v b => ScV K v ∧ ScV K b ∧ s + w ≤ K.nl ∧ (∀ k, rd b k → ¬ (s ≤ k ∧ k < s + w) → ¬ wr K.p v k)
  | .pair cs => ScL K cs
  | .call n as => ScL K as ∧ n < K.nd
  | .prim _ as => ScL K as
  | .loop z s => ScT K z ∧ ScT K s ∧ 1 ≤ K.p ∧ K.p ≤ K.nl ∧
      (∀ k, (wr K.p z k ∨ wr K.p s k) → K.p ≤ k) ∧ (∀ k, (rd z k ∨ rd s k) → ¬ (wr K.p z k ∨ wr K.p s k))
  | .cont _ => False
def ScT (K : SC) : Nd → Prop
  | .ite _ a b t e => ScV K a ∧ ScV K b ∧ ScT K t ∧ ScT K e ∧
      (∀ k, rd b k → ¬ wr K.p a k) ∧ (∀ k, rd t k → ¬ (wr K.p a k ∨ wr K.p b k)) ∧
      (∀ k, rd e k → ¬ (wr K.p a k ∨ wr K.p b k))
  | .letE s w v b => ScV K v ∧ ScT K b ∧ s + w ≤ K.nl ∧ (∀ k, rd b k → ¬ (s ≤ k ∧ k < s + w) → ¬ wr K.p v k)
  | .cont e => ScV K e ∧ 1 ≤ K.p ∧ K.p ≤ K.nl
  | e => ScV K e
def ScL (K : SC) : List Nd → Prop
  | [] => True
  | c :: cs => ScV K c ∧ ScL K cs ∧ (∀ k, rdL cs k → ¬ wr K.p c k)
end

mutual
theorem okV_of (K : SC) : ∀ e : Nd, WdV K e → ScV K e → OkV K e
  | .const _, _, _ => by simp [OkV]
  | .loc _ _, _, s => by simpa [OkV, ScV] using s
  | .bin _ a b, w, s => by
    simp only [WdV, ScV, OkV] at w s ⊢
    exact ⟨okV_of K a w.1 s.1, okV_of K b w.2.1 s.2.1, w.2.2.1, w.2.2.2, s.2.2⟩
  | .ite _ a b t e, w, s => by
    simp only [WdV, ScV, OkV] at w s ⊢
    exact ⟨okV_of K a w.1 s.1, okV_of K b w.2.1 s.2.1, okV_of K t w.2.2.1 s.2.2.1, okV_of K e w.2.2.2.1 s.2.2.2.1,
      w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2, s.2.2.2.2⟩
  | .letE _ _ v b, w, s => by
    simp only [WdV, ScV, OkV] at w s ⊢
    exact ⟨okV_of K v w.1 s.1, okV_of K b w.2.1 s.2.1, w.2.2, s.2.2⟩
  | .pair cs, w, s => by simp only [WdV, ScV, OkV] at w s ⊢; exact okL_of K cs w s
  | .call _ as, w, s => by
    simp only [WdV, ScV, OkV] at w s ⊢; exact ⟨okL_of K as w.1 s.1, s.2, w.2⟩
  | .prim _ as, w, s => by
    simp only [WdV, ScV, OkV] at w s ⊢; exact ⟨okL_of K as w.1 s, w.2⟩
  | .loop z s', w, s => by
    simp only [WdV, ScV, OkV] at w s ⊢
    exact ⟨okT_of K z _ w.1 s.1, okT_of K s' _ w.2 s.2.1, s.2.2⟩
  | .cont _, _, s => by simp [ScV] at s
theorem okT_of (K : SC) : ∀ (e : Nd) (wi : Nat), WdT K e wi → ScT K e → OkT K e wi
  | .ite _ a b t e, wi, w, s => by
    simp only [WdT, ScT, OkT] at w s ⊢
    exact ⟨okV_of K a w.1 s.1, okV_of K b w.2.1 s.2.1, okT_of K t wi w.2.2.1 s.2.2.1, okT_of K e wi w.2.2.2.1 s.2.2.2.1,
      w.2.2.2.2.1, w.2.2.2.2.2, s.2.2.2.2⟩
  | .letE _ _ v b, wi, w, s => by
    simp only [WdT, ScT, OkT] at w s ⊢
    exact ⟨okV_of K v w.1 s.1, okT_of K b wi w.2.1 s.2.1, w.2.2, s.2.2⟩
  | .cont e, wi, w, s => by
    simp only [WdT, ScT, OkT] at w s ⊢; exact ⟨okV_of K e w.1 s.1, w.2, s.2⟩
  | .const v, wi, w, s => by simp only [WdT, ScT, OkT] at w s ⊢; exact ⟨okV_of K _ w.1 s, w.2⟩
  | .loc a b, wi, w, s => by simp only [WdT, ScT, OkT] at w s ⊢; exact ⟨okV_of K _ w.1 s, w.2⟩
  | .bin o a b, wi, w, s => by simp only [WdT, ScT, OkT] at w s ⊢; exact ⟨okV_of K _ w.1 s, w.2⟩
  | .pair cs, wi, w, s => by simp only [WdT, ScT, OkT] at w s ⊢; exact ⟨okV_of K _ w.1 s, w.2⟩
  | .call n as, wi, w, s => by simp only [WdT, ScT, OkT] at w s ⊢; exact ⟨okV_of K _ w.1 s, w.2⟩
  | .prim pn as, wi, w, s => by simp only [WdT, ScT, OkT] at w s ⊢; exact ⟨okV_of K _ w.1 s, w.2⟩
  | .loop z s', wi, w, s => by simp only [WdT, ScT, OkT] at w s ⊢; exact ⟨okV_of K _ w.1 s, w.2⟩
theorem okL_of (K : SC) : ∀ cs : List Nd, WdL K cs → ScL K cs → OkL K cs
  | [], _, _ => by simp [OkL]
  | c :: cs, w, s => by
    simp only [WdL, ScL, OkL] at w s ⊢
    exact ⟨okV_of K c w.1 s.1, okL_of K cs w.2 s.2.1, s.2.2⟩
end

end Templates
