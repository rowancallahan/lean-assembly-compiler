/- Nano/Parser/NumP6: the main machine's tasks that do not read the tree: CLOSE, POPM, BINDM, COLSEQ, COLAT. -/
import Nano.Parser.NumP5
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem kne {a b : UInt64} (h : (a == b) = false) : ¬ (a == b) = true := by simp [h]
theorem keq {a b : UInt64} (h : (a == b) = true) : (a == b) = true := h

theorem M40_4 (N n : Nat) (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb a a2 : UInt64) :
    M40 N n x d b bt t tt c g s st gb 4 a a2 =
      if (u47 N (bpush (bpush (bpush g (st - gb - 1)) a) (bget s gb)) s (gb + 1) st).2 == 1 then
        u40 n x d b bt t (tt - 1) c (u47 N (bpush (bpush (bpush g (st - gb - 1)) a) (bget s gb)) s (gb + 1) st).1 s gb a2
      else ((u47 N (bpush (bpush (bpush g (st - gb - 1)) a) (bget s gb)) s (gb + 1) st).1, (c, 0)) := by
  unfold M40; rw [if_pos (keq (show ((4 : UInt64) == 4) = true from rfl))]
theorem M40_5 (N n : Nat) (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb a a2 : UInt64) :
    M40 N n x d b bt t tt c g s st gb 5 a a2 = u40 n x d b a t (tt - 1) c g s st gb := by
  unfold M40; rw [if_neg (kne (show ((5 : UInt64) == 4) = false from rfl)), if_pos (keq (show ((5 : UInt64) == 5) = true from rfl))]
theorem M40_6 (N n : Nat) (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb a a2 : UInt64)
    (R : LO) (hR : u31 x d b bt a2 = R) (R2 : Buf × (UInt64 × UInt64)) (hR2 : u26 R.1 bt R.2.1 0 R.2.2.1 a = R2) :
    M40 N n x d b bt t tt c g s st gb 6 a a2 =
      if R.2.2.2.2 == 1 then
        (if R2.2.2 == 1 then u40 n x d R2.1 R2.2.1 t (tt - 1) c g s st gb else (g, (c, 0)))
      else (g, (c, 0)) := by
  unfold M40
  rw [if_neg (kne (show ((6 : UInt64) == 4) = false from rfl)), if_neg (kne (show ((6 : UInt64) == 5) = false from rfl)),
    if_pos (keq (show ((6 : UInt64) == 6) = true from rfl)), hR]
  clear hR
  obtain ⟨b1, v, vt, e, ok⟩ := R
  replace hR2 : u26 b1 bt v 0 vt a = R2 := hR2
  show (if ok == 1 then (if (u26 b1 bt v 0 vt a).2.2 == 1 then u40 n x d (u26 b1 bt v 0 vt a).1 (u26 b1 bt v 0 vt a).2.1 t
    (tt - 1) c g s st gb else (g, (c, 0))) else (g, (c, 0))) = _
  rw [hR2]
theorem M40_7 (N n : Nat) (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb a a2 : UInt64) :
    M40 N n x d b bt t tt c g s st gb 7 a a2 = (if a == 0 then u40 n x d b bt t (tt - 1) c g s st gb
     else u40 n x d b bt (u27 (bset t (3 * tt - 2) (a - 1)) tt 0 1 0) (tt + 1) c g s st gb) := by
  unfold M40; rw [if_neg (kne (show ((7 : UInt64) == 4) = false from rfl)), if_neg (kne (show ((7 : UInt64) == 5) = false from rfl)), if_neg (kne (show ((7 : UInt64) == 6) = false from rfl)), if_pos (keq (show ((7 : UInt64) == 7) = true from rfl))]
theorem M40_8 (N n : Nat) (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb a a2 : UInt64) :
    M40 N n x d b bt t tt c g s st gb 8 a a2 = u40 n x d b bt (u27 t (tt - 1) 0 1 0) tt a g s st gb := by
  unfold M40; rw [if_neg (kne (show ((8 : UInt64) == 4) = false from rfl)), if_neg (kne (show ((8 : UInt64) == 5) = false from rfl)), if_neg (kne (show ((8 : UInt64) == 6) = false from rfl)), if_neg (kne (show ((8 : UInt64) == 7) = false from rfl)), if_pos (keq (show ((8 : UInt64) == 8) = true from rfl))]
abbrev R9 := Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64)))))))
/-- the tasks that read the tree: k ∈ {0, 1, 2, 3, 9} -/
theorem M40_r (N n : Nat) (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb k a a2 : UInt64)
    (h4 : (k == 4) = false) (h5 : (k == 5) = false) (h6 : (k == 6) = false) (h7 : (k == 7) = false)
    (h8 : (k == 8) = false) (R : R9) (hR : u49 x d b bt t (tt - 1) c s st gb k a a2 = R) :
    M40 N n x d b bt t tt c g s st gb k a a2 =
      if R.2.2.2.2.2.2.2.2 == 1 then u40 n x d R.1 R.2.1 R.2.2.1 R.2.2.2.1 R.2.2.2.2.1 g R.2.2.2.2.2.1 R.2.2.2.2.2.2.1 R.2.2.2.2.2.2.2.1
      else (g, (R.2.2.2.2.1, 0)) := by
  unfold M40
  rw [if_neg (by simp [h4]), if_neg (by simp [h5]), if_neg (by simp [h6]), if_neg (by simp [h7]), if_neg (by simp [h8]), hR]

theorem u47_ok : ∀ (n : Nat) (L W g s : Buf), W ++ L <+: s → s.length < 2 ^ 62 →
    (u47 n g s (u W.length) (u (W.length + L.length))).2 = 1 → (u47 n g s (u W.length) (u (W.length + L.length))).1 = g ++ L
  | 0, _, _, _, _, _, _, h => by simp [u47] at h
  | n + 1, [], W, g, s, hv, _, _ => by
    have := hv.length_le
    have : (u W.length < u (W.length + 0)) = False := by rw [ult (by simp at *; omega) (by simp at *; omega)]; simp
    simp [u47, this]
  | n + 1, w :: L, W, g, s, hv, hl, h => by
    have hl2 := hv.length_le; simp at hl2
    have c1 : (u W.length < u (W.length + (w :: L).length)) = True := by
      rw [ult (by omega) (by simp; omega)]; simp
    have r1 : bget s (u W.length) = w := by
      rw [bget_pre hv (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD]
    have e2 : u W.length + 1 = u (W ++ [w]).length := by simp [u1, uadd]
    have e3 : u (W.length + (w :: L).length) = u ((W ++ [w]).length + L.length) := by
      simp only [List.length_cons, List.length_append, List.length_nil]; congr 1; omega
    simp only [u47] at h ⊢
    simp only [c1, if_true] at h ⊢
    rw [r1, e2, e3] at h ⊢
    rw [u47_ok n L (W ++ [w]) _ s (by simpa using hv) hl h]; simp [bpush]

end NumP
