/- Nano/Parser/NumP7: the main machine walks `col` / `litG` / `cmpG` / `letG` (statements; COL cases). -/
import Nano.Parser.NumP6
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- the def table: kinds and widths -/
structure LK (x d : Buf) (ks ws : List Nat) : Prop where
  lc : LC x d ws
  kl : ks.length = ws.length
  dk : ∀ i, i < ws.length → d.getD (2 * i) 0 = u (ks.getD i 0)
  kb : ∀ i, i < ws.length → ks.getD i 0 < 2 ^ 32

/-- the groups buffer grew by a permutation of `gs` -/
def GA (g g' : Buf) (gs : List NumSpec.G) : Prop := ∃ X, X.Perm gs ∧ g' = g ++ encG X

theorem GA.trans {g g1 g2 : Buf} {A B : List NumSpec.G} (h1 : GA g g1 A) (h2 : GA g1 g2 B) : GA g g2 (A ++ B) := by
  obtain ⟨X, hX, rfl⟩ := h1; obtain ⟨Y, hY, rfl⟩ := h2
  exact ⟨X ++ Y, hX.append hY, by simp [encG_app]⟩

theorem GA.perm {g g1 : Buf} {A B : List NumSpec.G} (h : GA g g1 A) (hp : A.Perm B) : GA g g1 B := by
  obtain ⟨X, hX, rfl⟩ := h; exact ⟨X, hX.trans hp, rfl⟩

theorem GA.nil (g : Buf) : GA g g [] := ⟨[], List.Perm.refl _, by simp [encG]⟩

theorem u49_0 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb a a2 : UInt64) (y y1 y2 : Buf) :
    u49 x d b bt t tt c s st gb 0 a a2 y y1 y2 = u41 x d b bt t tt c s st gb a y y1 y2 := by
  unfold u49; rw [if_pos (keq (show ((0 : UInt64) == 0) = true from rfl))]

theorem u41_eq {x d b : Buf} {bt : UInt64} {t : Buf} {tt c : UInt64} {s : Buf} {st gb e : UInt64} {y y1 y2 : Buf}
    {b1 : Buf} {r : UInt64} {y3 y4 : Buf}
    (h : u32 x d b bt y y1 c = (b1, (r, (y3, y4)))) :
    u41 x d b bt t tt c s st gb e y y1 y2 =
      if r == 2 then u64 b1 t s y3 y4 y2
      else if r == 1 then (b1, (bt, (u27 (u27 t tt 4 e gb) (tt + 1) 1 0 0, (tt + 2, (c, (u20 s st 0, (st + 1, (st, (1, (y3, (y4, y2)))))))))))
      else u42 x d b1 bt t tt c s st gb e y3 y4 y2 := by
  unfold u41; rw [h]
  all_goals (try (unfold u65; rfl))

/-- the scratch buffers of a tree task's result -/
abbrev SCR (R : R12) : Prop := SC R.2.2.2.2.2.2.2.2.2.1 R.2.2.2.2.2.2.2.2.2.2.1 R.2.2.2.2.2.2.2.2.2.2.2

/-- a task that reads the tree, by its u49 result -/
theorem m_read {x d : Buf} {Q : MO → Prop} (hQ : QM Q) {b bs t ts g s S} {k a a2 c gb : UInt64}
    (hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 9) (hI : MI b bs t (ts ++ [(k, a, a2)]) g s S)
    (hg : SZ b t g s → ∀ y y1 y2, SC y y1 y2 → ∀ R : R12,
      u49 x d b (u (encB bs).length) t (u ts.length) c s (u S.length) gb k a a2 y y1 y2 = R →
      R.2.2.2.2.2.2.2.2.1 = 1 →
      SCR R ∧ GM x d Q R.1 R.2.1 R.2.2.1 R.2.2.2.1 R.2.2.2.2.1 g R.2.2.2.2.2.1 R.2.2.2.2.2.2.1 R.2.2.2.2.2.2.2.1) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) c g s (u S.length) gb := by
  apply gm_top hQ hI
  intro hsz y y1 y2 hsc n
  have hts := hI.lts; simp at hts
  have hk' : (k == 4) = false ∧ (k == 5) = false ∧ (k == 6) = false ∧ (k == 7) = false ∧ (k == 8) = false := by
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
  have e1 : u (ts.length + 1) - 1 = u ts.length := upred _ (by omega)
  rw [M40_r 16777216 n x d b _ t _ c g s _ gb k a a2 y y1 y2 hk'.1 hk'.2.1 hk'.2.2.1 hk'.2.2.2.1 hk'.2.2.2.2 _ rfl, e1]
  have hR := hg hsz y y1 y2 hsc _ rfl
  generalize u49 x d b (u (encB bs).length) t (u ts.length) c s (u S.length) gb k a a2 y y1 y2 = R at hR ⊢
  by_cases hok : R.2.2.2.2.2.2.2.2.1 = 1
  · rw [if_pos (by simp [hok])]; obtain ⟨h1, h2⟩ := hR hok; exact h2 _ _ _ h1 n
  · rw [if_neg (by simpa using hok)]; exact hQ _ (show u 0 ≠ 1 by decide)

/-! ## the spec, one fuel step -/
theorem col_succ (f : Nat) (ks ws : List Nat) (env : List Bool) (dd : Nat) (e : Nd) : NumSpec.col (f + 1) ks ws env dd e =
    if NumSpec.isL f ws env e then
      (⟨(NumSpec.litG f ks ws env e).1.1, dd, (NumSpec.litG f ks ws env e).1.2⟩ :: (NumSpec.litG f ks ws env e).2.1, (NumSpec.litG f ks ws env e).2.2)
    else match e with
    | .bin op a b =>
      if NumSpec.isShift op then NumSpec.R.app ([], !NumSpec.isL f ws env a && !NumSpec.spineLet f a) ((NumSpec.col f ks ws env 1 a).app (NumSpec.col f ks ws env 1 b))
      else
        let ls := NumSpec.leaves f e
        NumSpec.R.app ([], NumSpec.shapeOk f ws env ls) (ls.attach.foldr (fun ⟨l, _⟩ r => (NumSpec.col f ks ws env 1 l).app r) NumSpec.R.ok)
    | .ite _ a b t e =>
      let r5 := !(dd == 0 && ((NumSpec.isL f ws env t && NumSpec.spineLet f e) || (NumSpec.isL f ws env e && NumSpec.spineLet f t)))
      NumSpec.R.app ([], r5) ((NumSpec.cmpG f ks ws env a b).app ((NumSpec.col f ks ws env 1 t).app (NumSpec.col f ks ws env 1 e)))
    | .letE s w v b => (NumSpec.letG f ks ws env s w v).app (NumSpec.col f ks ws (NumSpec.setW env s (NumSpec.lw f ws env v)) dd b)
    | .pair cs => cs.attach.foldr (fun ⟨c, _⟩ r => (NumSpec.col f ks ws env 1 c).app r) NumSpec.R.ok
    | .call id as => as.zipIdx.attach.foldr (fun ⟨(a, i), _⟩ r =>
        (NumSpec.col f ks ws env (if ks.getD id 0 == 1 && i == 0 then 2 else 1) a).app r) NumSpec.R.ok
    | .prim _ as => as.attach.foldr (fun ⟨a, _⟩ r => (NumSpec.col f ks ws env 1 a).app r) NumSpec.R.ok
    | .loop z s => (NumSpec.col f ks ws env 1 z).app (NumSpec.col f ks ws env 1 s)
    | .cont c => NumSpec.col f ks ws env 1 c
    | _ => NumSpec.R.ok := rfl


theorem litG_succ (f : Nat) (ks ws : List Nat) (env : List Bool) (e : Nd) : NumSpec.litG (f + 1) ks ws env e =
    match e with
    | .loc s _ => (([s], false), NumSpec.R.ok)
    | .bin _ a b =>
      (((NumSpec.litG f ks ws env a).1.1 ++ (NumSpec.litG f ks ws env b).1.1, true),
        (NumSpec.litG f ks ws env a).2.app (NumSpec.litG f ks ws env b).2)
    | .ite _ a b t e =>
      (((NumSpec.litG f ks ws env t).1.1 ++ (NumSpec.litG f ks ws env e).1.1,
        (NumSpec.litG f ks ws env t).1.2 || (NumSpec.litG f ks ws env e).1.2),
        (NumSpec.cmpG f ks ws env a b).app ((NumSpec.litG f ks ws env t).2.app (NumSpec.litG f ks ws env e).2))
    | .letE s w v b =>
      ((NumSpec.litG f ks ws (NumSpec.setW env s (NumSpec.lw f ws env v)) b).1,
        (NumSpec.letG f ks ws env s w v).app (NumSpec.litG f ks ws (NumSpec.setW env s (NumSpec.lw f ws env v)) b).2)
    | _ => (([], false), NumSpec.R.ok) := by
  cases e <;> rfl

theorem cmpG_succ (f : Nat) (ks ws : List Nat) (env : List Bool) (a b : Nd) : NumSpec.cmpG (f + 1) ks ws env a b =
    if NumSpec.isL f ws env a && NumSpec.isL f ws env b then
      NumSpec.R.app ([], NumSpec.shapeOk f ws env (NumSpec.leaves f a ++ NumSpec.leaves f b))
        ((⟨(NumSpec.litG f ks ws env a).1.1 ++ (NumSpec.litG f ks ws env b).1.1, 0,
            (NumSpec.litG f ks ws env a).1.2 || (NumSpec.litG f ks ws env b).1.2⟩ ::
          ((NumSpec.litG f ks ws env a).2.app (NumSpec.litG f ks ws env b).2).1,
          ((NumSpec.litG f ks ws env a).2.app (NumSpec.litG f ks ws env b).2).2))
    else NumSpec.R.app ([], NumSpec.shapeOk f ws env (NumSpec.leaves f a ++ NumSpec.leaves f b))
      ((NumSpec.col f ks ws env 1 a).app (NumSpec.col f ks ws env 1 b)) := rfl

/-- the continuation after COL / CMP / LETG: shape true, the groups grew by a permutation of the result's -/
def MCp (x d : Buf) (Q : MO → Prop) (bs : List (Nat × List Bool)) (ts : List T3) (g : Buf) (S : List UInt64) (gb : UInt64)
    (c' : Nat) (R : NumSpec.R) : Prop :=
  R.2 = true → ∀ b' t' g' s', MI b' bs t' ts g' s' S → GA g g' R.1 →
    GM x d Q b' (u (encB bs).length) t' (u ts.length) (u c') g' s' (u S.length) gb

/-- the continuation after LIT: the open group (flag at S0's end) got the slots and the arithmetic flag -/
def MLp (x d : Buf) (Q : MO → Prop) (bs : List (Nat × List Bool)) (ts : List T3) (g : Buf) (S0 : List UInt64) (a0 : Bool)
    (SL : List UInt64) (c' : Nat) (L : (List Nat × Bool) × NumSpec.R) : Prop :=
  L.2.2 = true → ∀ b' t' g' s', MI b' bs t' ts g' s' (S0 ++ w2 (a0 || L.1.2) :: (SL ++ L.1.1.map u)) → GA g g' L.2.1 →
    GM x d Q b' (u (encB bs).length) t' (u ts.length) (u c') g' s' (u (S0 ++ w2 (a0 || L.1.2) :: (SL ++ L.1.1.map u)).length)
      (u S0.length)

/-- COL d at fuel F -/
def MCOL (x d : Buf) (np : Nat) (ks ws : List Nat) (F : Nat) : Prop :=
  ∀ (e : Nd) (dd : Nat) (Q : MO → Prop) (bs : List (Nat × List Bool)) (ts : List T3) (c : Nat) (rest b t g s : Buf)
    (S : List UInt64) (gb : UInt64),
    e.ser.length + 1 ≤ F → NB np e → dd < 3 → QM Q → x.drop c = e.ser ++ rest → 0 < c →
    MI b bs t (ts ++ [(0, u dd, 0)]) g s S →
    MCp x d Q bs ts g S gb (c + e.ser.length) (NumSpec.col F ks ws (envOf bs) dd e) →
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb

/-- LIT at fuel F -/
def MLIT (x d : Buf) (np : Nat) (ks ws : List Nat) (F : Nat) : Prop :=
  ∀ (e : Nd) (Q : MO → Prop) (bs : List (Nat × List Bool)) (ts : List T3) (c : Nat) (rest b t g s : Buf)
    (S0 : List UInt64) (a0 : Bool) (SL : List UInt64),
    e.ser.length ≤ F → NB np e → QM Q → x.drop c = e.ser ++ rest → 0 < c →
    MI b bs t (ts ++ [(1, 0, 0)]) g s (S0 ++ w2 a0 :: SL) →
    MLp x d Q bs ts g S0 a0 SL (c + e.ser.length) (NumSpec.litG F ks ws (envOf bs) e) →
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u (S0 ++ w2 a0 :: SL).length) (u S0.length)

/-- CMP at fuel F: the operands a, e2 at the cursor -/
def MCMP (x d : Buf) (np : Nat) (ks ws : List Nat) (F : Nat) : Prop :=
  ∀ (a e2 : Nd) (Q : MO → Prop) (bs : List (Nat × List Bool)) (ts : List T3) (c : Nat) (rest b t g s : Buf)
    (S : List UInt64) (gb : UInt64),
    a.ser.length + 2 ≤ F → e2.ser.length + 2 ≤ F → NB np a → NB np e2 → QM Q → x.drop c = a.ser ++ (e2.ser ++ rest) →
    0 < c → MI b bs t (ts ++ [(2, 0, 0)]) g s S →
    MCp x d Q bs ts g S gb (c + a.ser.length + e2.ser.length) (NumSpec.cmpG F ks ws (envOf bs) a e2) →
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb

/-- LETG slot at fuel F: the value at the cursor -/
def MLETG (x d : Buf) (np : Nat) (ks ws : List Nat) (F : Nat) : Prop :=
  ∀ (v : Nd) (sl w : Nat) (Q : MO → Prop) (bs : List (Nat × List Bool)) (ts : List T3) (c : Nat) (rest b t g s : Buf)
    (S : List UInt64) (gb : UInt64),
    v.ser.length + 2 ≤ F → NB np v → sl < 2 ^ 32 → QM Q → x.drop c = v.ser ++ rest → 0 < c →
    MI b bs t (ts ++ [(3, u sl, 0)]) g s S →
    MCp x d Q bs ts g S gb (c + v.ser.length) (NumSpec.letG F ks ws (envOf bs) sl w v) →
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb

theorem GM.cast {x d Q b bt bt' t tt tt' c c' g s st st' gb gb'} (h : GM x d Q b bt t tt c g s st gb) (h0 : bt' = bt)
    (h1 : tt' = tt) (h2 : c' = c) (h3 : st' = st) (h4 : gb' = gb) : GM x d Q b bt' t tt' c' g s st' gb' := by
  subst h0 h1 h2 h3 h4; exact h

theorem MI.pushw {b bs t ts g s S} (h : MI b bs t ts g s S) {n : UInt64} (hn : n = u ts.length) (ht : t.length < 2 ^ 41)
    (k a c : UInt64) : MI b bs (u27 t n k a c) (ts ++ [(k, a, c)]) g s S ∧ (u27 t n k a c).length ≤ t.length + 3 := by
  subst hn
  have h3 := h.pt.length_le; rw [encT_len] at h3
  have := u27_ok h.pt (by omega) (by omega) k a c
  exact ⟨⟨h.pb, h.lb, h.sb, this.1, by omega, h.lg, h.ps, h.ls⟩, by omega⟩

theorem MI.spush {b bs t ts g s S} (h : MI b bs t ts g s S) (hs : s.length < 2 ^ 41) (w : UInt64) :
    MI b bs t ts g (u20 s (u S.length) w) (S ++ [w]) ∧ (u20 s (u S.length) w).length ≤ s.length + 1 := by
  have h1 := u20_push h.ps (by omega) w
  have h2 := h.ps.length_le
  exact ⟨⟨h.pb, h.lb, h.sb, h.pt, h.lt, h.lg, h1.1, by have := h1.2; omega⟩, by have := h1.2; omega⟩

end NumP
