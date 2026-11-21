/- Nano/Parser/NumP10: the leaves of an operator tree as COLAT tasks (`u43`), and the COLAT chain. -/
import Nano.Parser.NumP9
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

def colat (p : List UInt64) : List T3 := p.reverse.map fun q => (8, q, 0)

theorem u43_ok (p : Buf) (hp : p.length < 2 ^ 32) : ∀ (n j : Nat) (ts : List T3) (t : Buf), j ≤ p.length → j < n →
    encT ts <+: t → t.length < 2 ^ 41 → 3 * (ts.length + j) < 2 ^ 41 →
    (u43 n t (u ts.length) p (u j)).2.2 = 1 ∧
    encT (ts ++ colat (p.take j)) <+: (u43 n t (u ts.length) p (u j)).1 ∧
    (∀ L, t.length ≤ L → 3 * (ts.length + j) ≤ L → (u43 n t (u ts.length) p (u j)).1.length ≤ L) ∧
    (u43 n t (u ts.length) p (u j)).2.1 = u (ts.length + j)
  | n, 0, ts, t, _, hn, ht, _, _ => by
    cases n with
    | zero => omega
    | succ n => simp [u43, show u 0 = 0 from rfl, colat, ht]; intro L h _; exact h
  | 0, j + 1, _, _, _, hn, _, _, _ => by omega
  | n + 1, j + 1, ts, t, hj, hn, ht, htl, hts => by
    have hj0 : (u (j + 1) == 0) = false := by rw [u0, ueq (by omega) (by omega)]; simp
    have hrd : bget p (u (j + 1) - 1) = p.getD j 0 := by rw [upred _ (by omega), bget_u _ (by omega)]
    have h1 := u27_ok ht (by omega) (by omega) 8 (p.getD j 0) 0
    have h2 := h1.2
    have e1 : u ts.length + 1 = u (ts ++ [(8, p.getD j 0, 0)]).length := by simp [u1, uadd]
    have hj1 : j ≤ p.length := by omega
    have hn1 : j < n := by omega
    have ht1 : (u27 t (u ts.length) 8 (p.getD j 0) 0).length < 2 ^ 41 := by
      have : 3 * ts.length + 3 < 2 ^ 41 := by omega
      have := Nat.le_trans h2 (Nat.max_le.2 ⟨Nat.le_of_lt htl, Nat.le_of_lt this⟩); omega
    have ih := u43_ok p hp n j (ts ++ [(8, p.getD j 0, 0)]) _ hj1 hn1 h1.1 ht1 (by simp; omega)
    simp only [u43, hj0, Bool.false_eq_true, if_false]
    rw [hrd, upred _ (by omega), e1]
    have et : colat (p.take (j + 1)) = (8, p.getD j 0, 0) :: colat (p.take j) := by
      have : p.take (j + 1) = p.take j ++ [p.getD j 0] := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < p.length by omega)]
      simp [colat, this]
    refine ⟨ih.1, by rw [et]; simpa using ih.2.1, ?_, by rw [ih.2.2.2]; congr 1; simp; omega⟩
    intro L hL1 hL2
    refine ih.2.2.1 L (Nat.le_trans h2 (Nat.max_le.2 ⟨hL1, by omega⟩)) (by simp; omega)

/-- where the cursor ends after the leaves -/
def lend (c : Nat) (ls : List (Nd × Nat)) : Nat := ls.foldl (fun _ q => q.2 + q.1.ser.length) c

theorem lend_append (c : Nat) (A B : List (Nd × Nat)) : lend c (A ++ B) = lend (lend c A) B := by
  simp [lend, List.foldl_append]

theorem lend_cons (c : Nat) (q : Nd × Nat) (ls : List (Nd × Nat)) : lend c (q :: ls) = lend (q.2 + q.1.ser.length) ls := rfl

theorem lvP_ne : ∀ (f : Nat) (e : Nd) (pos : Nat), lvP f e pos ≠ []
  | 0, e, pos => by cases e <;> simp [lvP]
  | f + 1, e, pos => by
    cases e with
    | bin op a b =>
      simp only [lvP]; split
      · simp
      · simp [lvP_ne f a]
    | _ => simp [lvP]

theorem lend_ne (z z' : Nat) : ∀ (B : List (Nd × Nat)), B ≠ [] → lend z B = lend z' B
  | [], h => absurd rfl h
  | q :: B, _ => by rw [lend_cons, lend_cons]

theorem lvP_lend : ∀ (f : Nat) (e : Nd) (pos z : Nat), lend z (lvP f e pos) = pos + e.ser.length
  | 0, e, pos, z => by cases e <;> simp [lvP, lend]
  | f + 1, e, pos, z => by
    cases e with
    | bin op a b =>
      simp only [lvP]; split
      · simp [lend]
      · rw [lend_append, lend_ne _ (b.ser.length + 0) _ (lvP_ne f b _), ← lend_ne 0 _ _ (lvP_ne f b _), lvP_lend f b]
        simp [Nd.ser]; omega
    | _ => simp [lvP, lend]

/-- the leaves are subtrees at their positions -/
theorem lvP_sp {x : Buf} {np : Nat} : ∀ (f : Nat) (e : Nd) (pos : Nat) (r : Buf), x.drop pos = e.ser ++ r → NB np e →
    0 < pos → ∀ q ∈ lvP f e pos, (∃ r', x.drop q.2 = q.1.ser ++ r') ∧ q.1.ser.length ≤ e.ser.length ∧ NB np q.1 ∧ 0 < q.2
  | 0, e, pos, r, hx, hnb, hp, q, hq => by
    have : q = (e, pos) := by cases e <;> simpa [lvP] using hq
    subst this; exact ⟨⟨r, hx⟩, Nat.le_refl _, hnb, hp⟩
  | f + 1, e, pos, r, hx, hnb, hp, q, hq => by
    cases e with
    | bin op a b =>
      simp only [lvP] at hq
      split at hq
      · simp at hq; subst hq; exact ⟨⟨r, hx⟩, Nat.le_refl _, hnb, hp⟩
      · obtain ⟨-, hna, hnb1⟩ := hnb
        have hx2 : x.drop (pos + 2) = a.ser ++ (b.ser ++ r) := by
          have h0 : x.drop pos = [3, u op] ++ (a.ser ++ (b.ser ++ r)) := by rw [hx]; simp [Nd.ser, toU]
          simpa using drop_shift h0
        have hx3 := drop_shift hx2
        have hl : (Nd.bin op a b).ser.length = 2 + a.ser.length + b.ser.length := by simp [Nd.ser]; omega
        rcases List.mem_append.1 hq with hq | hq
        · obtain ⟨h1, h2, h3, h4⟩ := lvP_sp f a _ _ hx2 hna (by omega) q hq; exact ⟨h1, by omega, h3, h4⟩
        · obtain ⟨h1, h2, h3, h4⟩ := lvP_sp f b _ _ hx3 hnb1 (by omega) q hq; exact ⟨h1, by omega, h3, h4⟩
    | _ => simp [lvP] at hq; subst hq; exact ⟨⟨r, hx⟩, Nat.le_refl _, hnb, hp⟩

/-- the leaves of a non-shift operator are proper subtrees -/
theorem lvP_lt {x : Buf} {np : Nat} {f : Nat} {op : Nat} {a b : Nd} {pos : Nat} {r : Buf}
    (hx : x.drop pos = (Nd.bin op a b).ser ++ r) (hnb : NB np (Nd.bin op a b)) (hp : 0 < pos)
    (hsh : NumSpec.isShift op = false) :
    ∀ q ∈ lvP (f + 1) (Nd.bin op a b) pos, q.1.ser.length < (Nd.bin op a b).ser.length := by
  intro q hq
  simp only [lvP, hsh, Bool.false_eq_true, if_false] at hq
  obtain ⟨-, hna, hnb1⟩ := hnb
  have hx2 : x.drop (pos + 2) = a.ser ++ (b.ser ++ r) := by
    have h0 : x.drop pos = [3, u op] ++ (a.ser ++ (b.ser ++ r)) := by rw [hx]; simp [Nd.ser, toU]
    simpa using drop_shift h0
  have hx3 := drop_shift hx2
  have hl : (Nd.bin op a b).ser.length = 2 + a.ser.length + b.ser.length := by simp [Nd.ser]; omega
  rcases List.mem_append.1 hq with hq | hq
  · have := (lvP_sp f a _ _ hx2 hna (by omega) q hq).2.1; omega
  · have := (lvP_sp f b _ _ hx3 hnb1 (by omega) q hq).2.1; omega

/-- the COLAT chain: COL 1 at each leaf, the first on top -/
theorem m_colats {x d : Buf} {np : Nat} {ks ws : List Nat} {f : Nat} (hCOL : MCOL x d np ks ws f) {Q : MO → Prop}
    (hQ : QM Q) (bs : List (Nat × List Bool)) (ts : List T3) (S : List UInt64) (gb : UInt64) :
    ∀ (ls : List (Nd × Nat)) (c : Nat) (b t g s : Buf),
    (∀ q ∈ ls, (∃ r, x.drop q.2 = q.1.ser ++ r) ∧ q.1.ser.length + 1 ≤ f ∧ NB np q.1 ∧ 0 < q.2) →
    MI b bs t (ts ++ colat (ls.map fun q => u q.2)) g s S →
    MCp x d Q bs ts g S gb (lend c ls) (colL f ks ws (envOf bs) (ls.map Prod.fst)) →
    GM x d Q b (u (encB bs).length) t (u (ts.length + ls.length)) (u c) g s (u S.length) gb
  | [], c, b, t, g, s, _, hI, hP => by
    exact (hP rfl b t g s (by simpa [colat] using hI) (GA.nil g)).cast rfl (by simp) rfl rfl rfl
  | q :: ls, c, b, t, g, s, hls, hI, hP => by
    obtain ⟨⟨r, hx⟩, hf, hnb, hp⟩ := hls q (by simp)
    have hI1 : MI b bs t ((ts ++ colat (ls.map fun q => u q.2)) ++ [(8, u q.2, 0)]) g s S := by
      simpa [colat] using hI
    refine (m_colat hQ (c := u c) (gb := gb) hI1 ?_).cast rfl (congrArg u (by simp [colat]; omega)) rfl rfl rfl
    intro t' hI'
    refine (hCOL q.1 1 Q bs _ q.2 r b t' g s S gb hf hnb (by omega) hQ hx hp
      (by rw [show (u 1 : UInt64) = 1 from rfl]; exact hI') ?_)
    intro hA b1 t1 g1 s1 hI1 hga
    have := m_colats hCOL hQ bs ts S gb ls (q.2 + q.1.ser.length) b1 t1 g1 s1 (fun q hq => hls q (by simp [hq])) hI1
      (MCp.app (A := NumSpec.col f ks ws (envOf bs) 1 q.1) (B := colL f ks ws (envOf bs) (ls.map Prod.fst))
          (by simpa [colL, lend_cons] using hP) hA hga)
    exact this.cast rfl (by simp [colat]) rfl rfl rfl

end NumP
