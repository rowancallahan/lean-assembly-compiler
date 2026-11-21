/- Nano/Parser/NumP5: the main machine `u40`: its invariant and the tasks that do not read the tree (CLOSE, POPM, BINDM,
COLSEQ, COLAT). -/
import Nano.Parser.NumP4
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

def encGr (g : NumSpec.G) : List UInt64 := [u g.vs.length, u g.d, w2 g.ar] ++ g.vs.map u
def encG (gs : List NumSpec.G) : List UInt64 := gs.flatMap encGr

theorem encG_app (a b : List NumSpec.G) : encG (a ++ b) = encG a ++ encG b := by simp [encG]

/-- the body of `u40` after the checks -/
def M40 (n : Nat) (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb k a a2 : UInt64) :
    Buf × (UInt64 × UInt64) :=
  let u := tt - 1;
  if k == 4 then
    (let (g1, ok) := u47 16777216 (bpush (bpush (bpush g (st - gb - 1)) a) (bget s gb)) s (gb + 1) st;
     if ok == 1 then u40 n x d b bt t u c g1 s gb a2 else (g1, (c, 0)))
  else if k == 5 then u40 n x d b a t u c g s st gb
  else if k == 6 then
    (let (b1, z) := u31 x d b bt a2;
     let (v, z1) := z;
     let (vt, z2) := z1;
     let (e, ok) := z2;
     if ok == 1 then
       (let (b2, z3) := u26 b1 bt v 0 vt a;
        let (bt1, ok1) := z3;
        if ok1 == 1 then u40 n x d b2 bt1 t u c g s st gb else (g, (c, 0)))
     else (g, (c, 0)))
  else if k == 7 then
    (if a == 0 then u40 n x d b bt t u c g s st gb
     else u40 n x d b bt (u27 (bset t (3 * tt - 2) (a - 1)) tt 0 1 0) (tt + 1) c g s st gb)
  else if k == 8 then u40 n x d b bt (u27 t u 0 1 0) tt a g s st gb
  else
    (let (b1, z) := u49 x d b bt t u c s st gb k a a2;
     let (bt1, z1) := z;
     let (t1, z2) := z1;
     let (tt1, z3) := z2;
     let (c1, z4) := z3;
     let (s1, z5) := z4;
     let (st1, z6) := z5;
     let (gb1, ok) := z6;
     if ok == 1 then u40 n x d b1 bt1 t1 tt1 c1 g s1 st1 gb1 else (g, (c1, 0)))

theorem u40_unf (n : Nat) (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb : UInt64) :
    u40 (n + 1) x d b bt t tt c g s st gb =
      if tt == 0 then (g, (c, 1)) else if u36 b t g s == 0 then (g, (c, 0)) else
      M40 n x d b bt t tt c g s st gb (bget t (3 * tt - 3)) (bget t (3 * tt - 2)) (bget t (3 * tt - 1)) := rfl

theorem u40_zero (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb : UInt64) :
    u40 0 x d b bt t tt c g s st gb = (g, (c, 0)) := rfl

theorem u40_eq (n : Nat) (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb : UInt64)
    (h0 : (tt == 0) = false) (h1 : (u36 b t g s == 0) = false) :
    u40 (n + 1) x d b bt t tt c g s st gb =
      M40 n x d b bt t tt c g s st gb (bget t (3 * tt - 3)) (bget t (3 * tt - 2)) (bget t (3 * tt - 1)) := by
  rw [u40_unf, h0, h1]; rfl

abbrev MO := Buf × (UInt64 × UInt64)
def QM (Q : MO → Prop) : Prop := ∀ r : MO, r.2.2 ≠ 1 → Q r

def GM (x d : Buf) (Q : MO → Prop) (b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (g s : Buf) (st gb : UInt64) : Prop :=
  ∀ n, Q (u40 n x d b bt t tt c g s st gb)

/-- the main machine's invariant: chain, tasks and slot stack are prefixes; the groups buffer is exact -/
structure MI (b : Buf) (bs : List (Nat × List Bool)) (t : Buf) (ts : List T3) (g s : Buf) (S : List UInt64) : Prop where
  pb : encB bs <+: b
  lb : b.length < 2 ^ 42
  sb : ∀ r ∈ bs, r.1 < 2 ^ 32
  pt : encT ts <+: t
  lt : t.length < 2 ^ 42
  lg : g.length < 2 ^ 42
  ps : S <+: s
  ls : s.length < 2 ^ 42

theorem MI.lts {b bs t ts g s S} (h : MI b bs t ts g s S) : ts.length < 2 ^ 41 := by
  have := h.pt.length_le; have := h.lt; rw [encT_len] at *; omega
theorem MI.lS {b bs t ts g s S} (h : MI b bs t ts g s S) : S.length < 2 ^ 42 := by
  have := h.ps.length_le; have := h.ls; omega
theorem MI.pop {b bs t ts g s S r} (h : MI b bs t (ts ++ [r]) g s S) : MI b bs t ts g s S :=
  ⟨h.pb, h.lb, h.sb, (by rw [encT_snoc]; exact List.prefix_append _ _ : encT ts <+: encT (ts ++ [r])).trans h.pt,
    h.lt, h.lg, h.ps, h.ls⟩

theorem u36_eq {b t g s : Buf} (hb : b.length < 2 ^ 42) (ht : t.length < 2 ^ 42) (hg : g.length < 2 ^ 42)
    (hs : s.length < 2 ^ 42) :
    (u36 b t g s == 0) = !(decide (b.length < 2 ^ 40) && decide (t.length < 2 ^ 40) && decide (g.length < 2 ^ 40) &&
      decide (s.length < 2 ^ 40)) := by
  unfold u36
  have e : (1099511627776 : UInt64) = u (2 ^ 40) := rfl
  simp only [bsize_u, e, ult (show b.length < 2 ^ 64 by omega) (show 2 ^ 40 < 2 ^ 64 by omega),
    ult (show t.length < 2 ^ 64 by omega) (show 2 ^ 40 < 2 ^ 64 by omega),
    ult (show g.length < 2 ^ 64 by omega) (show 2 ^ 40 < 2 ^ 64 by omega),
    ult (show s.length < 2 ^ 64 by omega) (show 2 ^ 40 < 2 ^ 64 by omega)]
  by_cases h1 : b.length < 2 ^ 40 <;> by_cases h2 : t.length < 2 ^ 40 <;> by_cases h3 : g.length < 2 ^ 40 <;>
    by_cases h4 : s.length < 2 ^ 40 <;> simp [h1, h2, h3, h4]

/-- sizes below 2^40 at a loop head -/
def SZ (b t g s : Buf) : Prop := b.length < 2 ^ 40 ∧ t.length < 2 ^ 40 ∧ g.length < 2 ^ 40 ∧ s.length < 2 ^ 40

theorem gm_top {x d : Buf} {Q : MO → Prop} (hQ : QM Q) {b : Buf} {bs : List (Nat × List Bool)} {t : Buf} {ts : List T3}
    {g s : Buf} {S : List UInt64} {k a a2 c gb : UInt64}
    (hI : MI b bs t (ts ++ [(k, a, a2)]) g s S)
    (H : SZ b t g s → ∀ n, Q (M40 n x d b (u (encB bs).length) t (u (ts.length + 1)) c g s (u S.length) gb k a a2)) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) c g s (u S.length) gb := by
  intro n
  have htl := hI.pt.length_le
  simp only [encT_len, List.length_append, List.length_singleton] at htl
  have lt := hI.lt
  cases n with
  | zero => exact hQ _ (by rw [u40_zero]; exact (show u 0 ≠ 1 by decide))
  | succ n =>
    have h0 : (u (ts.length + 1) == 0) = false := by rw [u0, ueq (by omega) (by omega)]; simp
    have h36 := u36_eq hI.lb hI.lt hI.lg hI.ls
    by_cases hs : SZ b t g s
    · have h1 : (u36 b t g s == 0) = false := by rw [h36]; simp [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]
      rw [u40_eq n x d b _ t _ c g s _ gb h0 h1]
      obtain ⟨r1, r2, r3⟩ := top_rd hI.pt (by omega)
      rw [r1, r2, r3]; exact H hs n
    · have h1 : (u36 b t g s == 0) = true := by
        rw [h36]; unfold SZ at hs
        by_cases h1 : b.length < 2 ^ 40 <;> by_cases h2 : t.length < 2 ^ 40 <;> by_cases h3 : g.length < 2 ^ 40 <;> simp_all
      apply hQ; rw [u40_unf, h0, h1]; exact (show u 0 ≠ 1 by decide)

end NumP
