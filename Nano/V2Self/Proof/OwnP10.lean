/- Nano/V2Self/Proof/OwnP10: the children of an argument-list frame = `OwnSpec.lstA`. -/
import Nano.V2Self.Proof.OwnP9
namespace OwnP
open C OwnSpec ParSpec

/-- the walk of node `n` from any running state below a frame reaches `Done` (or an error) -/
def SimOK (W : WCx) (n : Nd) : Prop :=
  ∀ (A : AS) (s f v : Buf) (rest : List UInt64), St W s f v A → A.ph = 0 → A.Φ ≠ [] →
    W.x.drop A.i = n.ser ++ rest → Reach W (s, f, v) (Done W A n)

/-- the frame after its children: same but `c`, `vc` -/
def Fr.after (r r' : Fr) : Prop := r'.g = r.g ∧ r'.n = r.n ∧ r'.c = r.n ∧ r'.d = r.d ∧ r'.vb = r.vb ∧ r'.a = r.a ∧ r'.b = r.b

theorem serL_cons (n : Nd) (cs : List Nd) : serL (n :: cs) = n.ser ++ serL cs := rfl

theorem dsOf_set (W : WCx) (r : Fr) {k : Nat} (hk : k = 2 ∨ k = 5) (x : Nat) : dsOf W (r.set k x) = dsOf W r := by
  rcases hk with rfl | rfl <;> rfl

theorem ok_set {W : WCx} {r : Fr} (hr : r.ok W) {k : Nat} (hk : k = 2 ∨ k = 5) (x : Nat) : (r.set k x).ok W := by
  rcases hk with rfl | rfl <;> exact hr

theorem lst_sim (W : WCx) : ∀ (cs : List Nd), (∀ n ∈ cs, SimOK W n) →
    ∀ (A : AS) (s f v : Buf) (rest : List UInt64) (Φ0 : List Fr) (r : Fr) (pre acc : List Nat),
    St W s f v A → A.ph = 2 → A.Φ = Φ0 ++ [r] → r.ok W → r.g ≠ 5 → r.g ≠ 10 → (r.g = 4 → r.c + cs.length ≤ 2) →
    r.c + cs.length = r.n → A.es = pre ++ acc → pre.length = r.vb → W.x.drop A.i = serL cs ++ rest →
    Reach W (s, f, v) (fun σ => ∃ F' acc' r', lstA W.oc cs (dsOf W r) A.F acc = some (F', acc') ∧ r.after r' ∧
      St W σ.1 σ.2.1 σ.2.2 { A with i := A.i + (serL cs).length, F := F', es := pre ++ acc', Φ := Φ0 ++ [r'], ph := 2 })
  | [], _, A, s, f, v, rest, Φ0, r, pre, acc, hSt, hp, hΦ, hr, h5, h10, h4, hn, hes, hpre, hx => by
    apply reach_now
    refine ⟨A.F, acc, r, by simp [lstA], ⟨rfl, rfl, by simpa using hn, rfl, rfl, rfl, rfl⟩, ?_⟩
    have : { A with i := A.i + (serL []).length, F := A.F, es := pre ++ acc, Φ := Φ0 ++ [r], ph := 2 } = A := by
      cases A; simp_all [serL]
    rw [this]; exact hSt
  | n :: cs, hsim, A, s, f, v, rest, Φ0, r, pre, acc, hSt, hp, hΦ, hr, h5, h10, h4, hn, hes, hpre, hx => by
    have hsm := hSt.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r (by rw [hΦ]; simp)
    have hcn := hsm 1 (by omega); simp only [Fr.fld] at hcn
    have hl : 1 ≤ (n :: cs).length := by simp
    apply reach_trans (ph2_next hSt hp hΦ (by omega) h10 (fun h => by have := h4 h; simp at this; omega))
    intro σ1 hσ1
    have hx1 : W.x.drop A.i = n.ser ++ (serL cs ++ rest) := by rw [hx, serL_cons, List.append_assoc]
    apply reach_trans (hsim n (by simp) _ σ1.1 σ1.2.1 σ1.2.2 _ hσ1 rfl (by simp) hx1)
    intro σ2 ⟨F1, en, hchk, hσ2⟩
    have hr1 : (r.set 5 A.es.length).ok W := ok_set hr (by omega) _
    have hesl : A.es.length = pre.length + acc.length := by rw [hes]; simp
    apply reach_trans (ph1_arg hσ2 rfl (Φ0 := Φ0) (r := r.set 5 A.es.length) rfl hr1 h5 h10
      (fun h => by have := h4 h; simp [Fr.set] at this ⊢; omega) (by simp [Fr.set]; omega) (by simp [Fr.set]) (by simp [Fr.set]; omega))
    intro σ3 ⟨hok, hσ3⟩
    have ih := lst_sim W cs (fun m hm => hsim m (by simp [hm])) _ σ3.1 σ3.2.1 σ3.2.2 rest Φ0
      ((r.set 5 A.es.length).set 2 ((r.set 5 A.es.length).c + 1)) pre (acc ++ en) hσ3 rfl rfl (ok_set hr1 (by omega) _)
      (by simp [Fr.set]; exact h5) (by simp [Fr.set]; exact h10) (fun h => by have := h4 (by simpa [Fr.set] using h); simp [Fr.set] at this ⊢; omega)
      (by simp [Fr.set] at hn ⊢; omega) (by simp [hes]) (by simp [Fr.set, hpre])
      (by simp only; rw [show A.i + n.ser.length = A.i + n.ser.length from rfl, ← List.drop_drop, hx1, List.drop_left])
    apply reach_mono ih
    intro σ ⟨F', acc', r', hl', hafter, hσ⟩
    refine ⟨F', acc', r', ?_, ?_, ?_⟩
    · simp only [lstA, hchk, Option.bind_some]
      rw [dsOf_set W (r.set 5 A.es.length) (k := 2) (Or.inl rfl), dsOf_set W r (k := 5) (Or.inr rfl)] at hl'
      have hok' : okAll (dsOf W r) F1 acc.length en = true := by
        rw [dsOf_set W r (k := 5) (Or.inr rfl)] at hok
        simpa [Fr.set, hesl, hpre] using hok
      simp only [hok', if_true]; exact hl'
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hafter
      simp [Fr.set] at a1 a2 a3 a4 a5 a6 a7
      exact ⟨a1, a2, a3, a4, a5, a6, a7⟩
    · have e1 : A.i + n.ser.length + (serL cs).length = A.i + (serL (n :: cs)).length := by simp [serL_cons]; omega
      simp only [e1] at hσ
      exact hσ

end OwnP
