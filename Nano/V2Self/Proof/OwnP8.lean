/- Nano/V2Self/Proof/OwnP8: runs of the walk (`Reach`: finitely many `o30` steps, never stopped before, then P or the
error flag) and the phase-0 steps (start a node). -/
import Nano.V2Self.Proof.OwnP7
namespace OwnP
open C OwnSpec ParSpec

abbrev SB := Buf × Buf × Buf

def stp (W : WCx) (σ : SB) : SB := let r := o30 W.x σ.1 σ.2.1 σ.2.2 W.t; (r.1, r.2.1, r.2.2)

def stopped (σ : SB) : Prop := bget σ.1 1 = 1 ∨ bget σ.1 5 = 1

/-- k steps -/
def it (W : WCx) : Nat → SB → SB
  | 0, σ => σ
  | k + 1, σ => it W k (stp W σ)

theorem it_add (W : WCx) : ∀ (a b : Nat) (σ : SB), it W (a + b) σ = it W b (it W a σ)
  | 0, b, σ => by simp [it]
  | a + 1, b, σ => by rw [show a + 1 + b = (a + b) + 1 by omega, it, it, it_add W a b]

def Reach (W : WCx) (σ : SB) (P : SB → Prop) : Prop :=
  ∃ k, (∀ j < k, ¬ stopped (it W j σ) ∧ 2 ≤ (it W j σ).1.length) ∧ (P (it W k σ) ∨ bget (it W k σ).1 1 = 1)

theorem reach_now {W : WCx} {σ : SB} {P : SB → Prop} (h : P σ) : Reach W σ P := ⟨0, fun _ h => absurd h (by omega), .inl h⟩

theorem reach_err {W : WCx} {σ : SB} {P : SB → Prop} (h : bget σ.1 1 = 1) : Reach W σ P :=
  ⟨0, fun _ h => absurd h (by omega), .inr h⟩

theorem reach_step {W : WCx} {σ : SB} {P : SB → Prop} (hn : ¬ stopped σ) (hl : 2 ≤ σ.1.length)
    (h : Reach W (stp W σ) P) : Reach W σ P := by
  obtain ⟨k, h1, h2⟩ := h
  refine ⟨k + 1, fun j hj => ?_, by rw [it]; exact h2⟩
  rcases j with _ | j
  · exact ⟨hn, hl⟩
  · rw [it]; exact h1 j (by omega)

theorem reach_trans {W : WCx} {σ : SB} {P Q : SB → Prop} (h : Reach W σ P) (hq : ∀ σ', P σ' → Reach W σ' Q) :
    Reach W σ Q := by
  obtain ⟨k, h1, h2⟩ := h
  rcases h2 with hp | he
  · obtain ⟨k', h1', h2'⟩ := hq _ hp
    refine ⟨k + k', fun j hj => ?_, by rw [it_add]; exact h2'⟩
    by_cases hjk : j < k
    · exact h1 j hjk
    · have := h1' (j - k) (by omega)
      rwa [← it_add, show k + (j - k) = j by omega] at this
  · exact ⟨k, h1, .inr he⟩

theorem reach_mono {W : WCx} {σ : SB} {P Q : SB → Prop} (h : Reach W σ P) (hq : ∀ σ', P σ' → Q σ') : Reach W σ Q :=
  reach_trans h (fun σ' hp => reach_now (hq σ' hp))

/-- a represented state is running -/
theorem st_run {W : WCx} {s f v : Buf} {A : AS} (h : RS W s A) : ¬ stopped (s, f, v) := by
  have r := regs h
  unfold stopped; simp only [r.2.1, r.2.2.2.2.1]; decide

/-- one step whose result is P or an error -/
theorem reach_one {W : WCx} {s f v : Buf} {A : AS} {P : SB → Prop} (h : RS W s A)
    (hs : P (stp W (s, f, v)) ∨ bget (stp W (s, f, v)).1 1 = 1) : Reach W (s, f, v) P := by
  apply reach_step (st_run h) (by have := h.1; simp only; omega)
  rcases hs with h1 | h1
  · exact reach_now h1
  · exact reach_err h1

/-! ## reading the AST -/
theorem xw {x : Buf} {i : Nat} {l rest : List UInt64} (h : x.drop i = l ++ rest) {k : Nat} (hk : k < l.length)
    (hi : i + k < 2 ^ 64) : bget x (u (i + k)) = l.getD k 0 := by
  rw [bget_u x hi, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have : x[i + k]? = (x.drop i)[k]? := by simp
  rw [this, h, List.getElem?_append_left hk]

theorem ser_len_pos (n : Nd) : 1 ≤ n.ser.length := by cases n <;> simp [Nd.ser]

/-- the result of walking node `n` from state `A` (phase 0 at its first word): phase 1 after it, its entries pushed -/
def Done (W : WCx) (A : AS) (n : Nd) (σ : SB) : Prop :=
  ∃ F' en, chk W.oc n A.F = some (F', en) ∧
    St W σ.1 σ.2.1 σ.2.2 { A with i := A.i + n.ser.length, F := F', es := A.es ++ en, ph := 1 }

theorem stp_eq (W : WCx) (s f v : Buf) : stp W (s, f, v) =
    ((o30 W.x s f v W.t).1, (o30 W.x s f v W.t).2.1, (o30 W.x s f v W.t).2.2) := rfl

theorem o30_ph0 {W : WCx} {s f v : Buf} {A : AS} (h : RS W s A) (hp : A.ph = 0) : o30 W.x s f v W.t = o31 W.x s f v W.t := by
  have r := (regs h).2.2.2.2.2.2.2.2.2.1
  unfold o30; simp only [lit] at r ⊢; simp only [r, hp, beq_self_eq_true, if_true]

theorem o30_ph1 {W : WCx} {s f v : Buf} {A : AS} (h : RS W s A) (hp : A.ph = 1) : o30 W.x s f v W.t = o32 W.x s f v W.t := by
  have r := (regs h).2.2.2.2.2.2.2.2.2.1
  unfold o30; simp only [lit] at r ⊢; simp only [r, hp]; rw [if_neg (by decide), if_pos (by decide)]

theorem o30_ph2 {W : WCx} {s f v : Buf} {A : AS} (h : RS W s A) (hp : A.ph = 2) : o30 W.x s f v W.t = o33 W.x s f v W.t := by
  have r := (regs h).2.2.2.2.2.2.2.2.2.1
  unfold o30; simp only [lit] at r ⊢; simp only [r, hp]; rw [if_neg (by decide), if_neg (by decide)]

/-- set the cursor and the phase -/
theorem rs_ip {W : WCx} {s : Buf} {A : AS} (h : RS W s A) (i ph : Nat) :
    RS W (bset (bset s (u 0) (u i)) (u 11) (u ph)) { A with i := i, ph := ph } := by
  have h1 : RS W (bset s (u 0) (u i)) { A with i := i } := rs_set h (r := 0) (by omega) _ (by simp [regL]) rfl
  exact rs_set h1 (r := 11) (by omega) _ (by simp [regL]) rfl

theorem bnd_ip {W : WCx} {A : AS} (hB : Bnd W A) {i ph : Nat} (hi : i < 2 ^ 40) (hp : ph < 3) :
    Bnd W { A with i := i, ph := ph } := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hB
  exact ⟨b1, b2, b3, b4, hi, b6, b7, b8, b9, b10, hp⟩

theorem drop_len {x : Buf} {i : Nat} {l rest : List UInt64} (h : x.drop i = l ++ rest) (hl : 0 < l.length) :
    i + l.length ≤ x.length := by
  have := congrArg List.length h; simp at this; omega

/-- CONST -/
theorem sim_const {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 0) (c : UInt64) {rest : List UInt64}
    (hx : W.x.drop A.i = (Nd.const c).ser ++ rest) : Reach W (s, f, v) (Done W A (.const c)) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  have hxl := drop_len hx (by simp [Nd.ser]); simp [Nd.ser] at hxl
  have hx40 := hB.2.2.2.1
  apply reach_one hS
  rw [stp_eq, o30_ph0 hS hp]
  unfold o31
  have r0 := (regs hS).1
  simp only [lit] at r0 ⊢
  rw [r0, show A.i = A.i + 0 from rfl, xw hx (k := 0) (by simp [Nd.ser]) (by omega)]
  simp only [Nd.ser, List.getD_cons_zero, show ((1 : UInt64) == u 1) = true from rfl, if_true]
  rw [show u (A.i + 0) + u 2 = u (A.i + 2) from u_add _ _]
  have hS1 := rs_ip hS (A.i + 2) 1
  have hB1 := bnd_ip hB (i := A.i + 2) (ph := 1) (by omega) (by omega)
  rcases o6_ok hS1 hV hB1 (e := 0) (by omega) with ⟨-, ho6, hS2, hV2, hB2⟩ | herr
  · rw [ho6]; left
    refine ⟨A.F, [0], by simp [chk], hS2, hF, hV2, hT, hB2⟩
  · right; exact herr

/-- LOCAL -/
theorem sim_loc {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 0) {s0 w0 : Nat}
    (hs0 : s0 < 2 ^ 64) (hw0 : w0 < 2 ^ 64) {rest : List UInt64}
    (hx : W.x.drop A.i = (Nd.loc s0 w0).ser ++ rest) : Reach W (s, f, v) (Done W A (.loc s0 w0)) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  have hxl := drop_len hx (by simp [Nd.ser]); simp [Nd.ser] at hxl
  have hx40 := hB.2.2.2.1
  have hns := hB.1
  have hnsK : W.ns = W.K.length := rfl
  apply reach_one hS
  rw [stp_eq, o30_ph0 hS hp]
  unfold o31
  have r0 := (regs hS).1
  have r6 := (regs hS).2.2.2.2.2.1
  simp only [lit] at r0 r6 ⊢
  rw [r0, show A.i = A.i + 0 from rfl, xw hx (k := 0) (by simp [Nd.ser]) (by omega),
    show u (A.i + 0) + u 1 = u (A.i + 1) from u_add _ _, xw hx (k := 1) (by simp [Nd.ser]) (by omega),
    show u (A.i + 0) + u 2 = u (A.i + 2) from u_add _ _, xw hx (k := 2) (by simp [Nd.ser]) (by omega)]
  simp only [Nd.ser, List.getD_cons_zero, List.getD_cons_succ, show ((2 : UInt64) == u 1) = false from rfl,
    show ((2 : UInt64) == u 2) = true from rfl, Bool.false_eq_true, if_false, if_true]
  simp only [show s0.toUInt64 = u s0 from rfl, show w0.toUInt64 = u w0 from rfl, r6]
  simp only [u_lt' (show 1048575 < 2 ^ 64 by omega) hs0, u_lt' (show 1048575 < 2 ^ 64 by omega) hw0]
  by_cases b1 : 1048575 < s0
  · simp only [b1, if_true]; right; exact err_o5 (by have := hS.1; omega)
  simp only [b1, if_false]
  by_cases b2 : 1048575 < w0
  · simp only [b2, if_true]; right; exact err_o5 (by have := hS.1; omega)
  simp only [b2, if_false, u_add, u_lt' (show W.ns < 2 ^ 64 by omega) (show s0 + w0 < 2 ^ 64 by omega)]
  by_cases b3 : W.ns < s0 + w0
  · simp only [b3, if_true]; right; exact err_o5 (by have := hS.1; omega)
  simp only [b3, if_false, show A.i + 0 + 3 = A.i + 3 from rfl]
  have hS1 := rs_ip hS (A.i + 3) 1
  have hB1 := bnd_ip hB (i := A.i + 3) (ph := 1) (by omega) (by omega)
  rcases o27_ok (W := W) (f := f) (x := s0) (w := w0) (by omega) 16777216 { A with i := A.i + 3, ph := 1 } _ v 0 hS1 hF hV
    hB1 (by omega) with ⟨s', v', h1, h2, h3, h4⟩ | herr
  · rw [h1]; left
    refine ⟨A.F, locE W.K s0 w0, ?_, h2, hF, h3, hT, h4⟩
    simp [chk, WCx.oc, show s0 + w0 ≤ W.K.length by omega]
  · right; exact herr

/-- push a frame (or the frame cap error) -/
theorem o3_ok {W : WCx} {s : Buf} {A : AS} (h : RS W s A) (hΦ : A.Φ.length ≤ 2 ^ 30) (g n d a b : Nat) (hg : g < 2 ^ 60) (hn : n < 2 ^ 60)
    (hd : d < 2 ^ 60) (ha : a < 2 ^ 60) (hb : b < 2 ^ 60) :
    (A.Φ.length < 2 ^ 30 ∧ RS W (o3 s (u g) (u n) (u d) (u a) (u b))
      { A with Φ := A.Φ ++ [⟨g, n, 0, d, A.es.length, A.es.length, a, b⟩] }) ∨
    bget (o3 s (u g) (u n) (u d) (u a) (u b)) 1 = 1 := by
  by_cases hq : A.Φ.length < 2 ^ 30
  · left; exact ⟨hq, o3_eq h hq g n d a b hg hn hd ha hb⟩
  · right
    have h4 := (regs h).2.2.2.1
    unfold o3; simp only [h4]
    rw [if_neg (by rw [show (1073741824 : UInt64) = u 1073741824 from rfl, u_lt' (by omega) (by omega)]; omega)]
    exact err_o5 (by have := h.1; omega)

end OwnP
