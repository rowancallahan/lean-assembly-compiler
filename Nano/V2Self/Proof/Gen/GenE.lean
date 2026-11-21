/- GenRef, part 1 (generic): **the g39 work-item invariant for any Gen source and any encoders**.
`Src` = a Gen source's dispatch (`g36` node visit, `g37` work-item step); `Em` = the encoders and emitters it calls
(RISC-V-shaped: one code cell per control-flow instruction).  `SrcOK` = the dispatch equations (per source: unfolding
lemmas), `EmOK` = what the proofs need from the emitters (append-only `PI`, length bounds, the jump helpers g19/g20).
For any instances, `visit_all`: from a visit item, the main loop fails or emits exactly the reference code `CG`/`CT`.
The RISC-V instance is in GenRef.lean and gives back the concrete theorems.  The proof text is GenRef's former one;
the names g4 … g37 here are the class fields, not `C.g4` … -/
import Nano.V2Self.Proof.Gen.GenBase
namespace GenEmit
open GenRef CallProbe
open C (g15 g16 g17 g18 g24 g27 g33 g43 g_0 g_1 g_901)

/-- a Gen source: node visit and work-item step -/
class Src where
  g36 : Buf → Buf → Buf → Buf → UInt64 → Buf × (Buf × Buf)
  g37 : Buf → Buf → Buf → Buf → Buf → Buf → Buf × (Buf × (Buf × Buf))

/-- the encoders (g4 branch, g10 addi, g11 ld, g12 sd, g13 jal from word a to word b, g14 its range check) and the
emitters built from them (g19/g20 jump / patch, g21/g22 push, g23 li, g25 LOCAL, g26 pop, g30 pop2, g31 BIN, g32 prims) -/
class Em where
  g4 : UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  g10 : UInt64 → UInt64 → UInt64 → UInt64
  g11 : UInt64 → UInt64 → UInt64 → UInt64
  g12 : UInt64 → UInt64 → UInt64 → UInt64
  g13 : UInt64 → UInt64 → UInt64 → UInt64
  g14 : UInt64 → UInt64 → UInt64
  g19 : Buf → Buf → UInt64 → UInt64 → Buf × Buf
  g20 : Buf → Buf → UInt64 → Buf × Buf
  g21 : Buf → Buf
  g22 : Buf → UInt64 → Buf
  g23 : Buf → UInt64 → UInt64 → Buf
  g25 : Nat → UInt64 → UInt64 → UInt64 → Buf → Buf
  g26 : Nat → UInt64 → UInt64 → UInt64 → Buf → Buf
  g30 : Buf → UInt64 → Buf
  g31 : Buf → UInt64 → Buf
  g32 : Buf → UInt64 → UInt64 → Buf
open Src Em
variable [Src] [Em]

/-- what the item proofs use about the emitters -/
class EmOK : Prop where
  g31_len (o : Buf) (p : UInt64) : (g31 o p).length ≤ o.length + 5
  pi_g21 : PI g21
  pi_g22 (d) : PI (fun o => g22 o d)
  pi_g23 (d v) : PI (fun o => g23 o d v)
  pi_g31 (p) : PI (fun o => g31 o p)
  pi_g32 (p u : UInt64) : PI (fun o => g32 o p u)
  g23_len (o : Buf) (d v : UInt64) : (g23 o d v).length ≤ o.length + 17
  g21_len (o : Buf) : (g21 o).length = o.length + 4
  g25_len : ∀ (n : Nat) (p s w : UInt64) (o : Buf), (g25 n p s w o).length ≤ o.length + 5 * n
  g26_len : ∀ (n : Nat) (p s w : UInt64) (o : Buf), (g26 n p s w o).length ≤ o.length + 3 * n
  g32_len (o : Buf) (p u : UInt64) : (g32 o p u).length ≤ o.length + 64
  pi_g25 : ∀ (n : Nat) (p s w : UInt64), PI (g25 n p s w)
  pi_g26 : ∀ (n : Nat) (p s w : UInt64), PI (g26 n p s w)
  g20_eq (r o : Buf) (p : UInt64) :
      g20 r o p = (if g14 p (bsize o) == 1 then r else g16 r, bset o p (g13 0 p (bsize o)))
  g30_eq (o : Buf) : g30 o 16 = o ++ [g11 6 31 0, g11 5 31 8, g10 31 31 16]
  g19_eq (r o : Buf) (d b : UInt64) :
      g19 r o d b = (if g14 (bsize o) b == 1 then r else g16 r, bpush o (g13 d (bsize o) b))

/-- the dispatch equations of the source -/
class SrcOK : Prop where
  g37_visit (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 1) :
      g37 x r o k t f = (match g36 x (g15 r 6 (bget r 6 - 1)) o k (bget k ((bget r 6 - 1) * 3 + 1)) with
        | (r2, (o2, k2)) => (r2, (o2, (k2, f))))
  g36_const (x r o k : Buf) (hc : bget x (bget r 0) = 1) :
      g36 x r o k 0 = (g15 r 0 (bget r 0 + 2), (g21 (g23 o 5 (bget x (bget r 0 + 1))), k))
  g36_local (x r o k : Buf) (hc : bget x (bget r 0) = 2) :
      g36 x r o k 0 = (if g43 r (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2)) == 1 then (g16 r, (o, k)) else
        (g15 r 0 (bget r 0 + 3), (g25 256 (bget r 1) (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2)) o, k)))
  g36_bin (x r o k : Buf) (hc : bget x (bget r 0) = 3) (hb : bget x (bget r 0 + 1) - 1 < 8) :
      g36 x r o k 0 = (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + 3), (o, g18 (g18 (g18 k (bget r 6) 2 (bget x (bget r 0 + 1)) 0)
        (bget r 6 + 1) 1 0 0) (bget r 6 + 2) 1 0 0))
  g36_bin_bad (x r o k : Buf) (hc : bget x (bget r 0) = 3) (hb : ¬ bget x (bget r 0 + 1) - 1 < 8) :
      g36 x r o k 0 = (g16 r, (o, k))
  g37_t2 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 2) :
      g37 x r o k t f = (g15 r 6 (bget r 6 - 1), (g31 o (bget k ((bget r 6 - 1) * 3 + 1)), (k, f)))
  g36_let (x r o k : Buf) (hc : bget x (bget r 0) = 5) :
      g36 x r o k 0 = (if g43 r (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2)) == 1 then (g16 r, (o, k)) else
        (g15 (g15 r 0 (bget r 0 + 3)) 6 (bget r 6 + 3), (o, g18 (g18 (g18 k (bget r 6) 1 0 0) (bget r 6 + 1) 6
          (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2))) (bget r 6 + 2) 1 0 0)))
  g37_t6 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 6) :
      g37 x r o k t f = (g15 r 6 (bget r 6 - 1), (g26 256 (bget (g15 r 6 (bget r 6 - 1)) 1) (bget k ((bget r 6 - 1) * 3 + 1))
        (bget k ((bget r 6 - 1) * 3 + 2)) o, (k, f)))
  g36_if (x r o k : Buf) (hc : bget x (bget r 0) = 4) (hb : bget x (bget r 0 + 1) - 1 < 2) :
      g36 x r o k 0 = (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + 7),
        (o, g18 (g18 (g18 (g18 (g18 (g18 (g18 k (bget r 6) 5 0 0) (bget r 6 + 1) 1 0 0) (bget r 6 + 2) 4 0 0) (bget r 6 + 3) 1 0 0)
          (bget r 6 + 4) 3 (bget x (bget r 0 + 1)) 0) (bget r 6 + 5) 1 0 0) (bget r 6 + 6) 1 0 0))
  g36_if_bad (x r o k : Buf) (y : UInt64) (hc : bget x (bget r 0) = 4) (hb : ¬ bget x (bget r 0 + 1) - 1 < 2) :
      g36 x r o k y = (g16 r, (o, k))
  g37_t3 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 3) :
      g37 x r o k t f = (g15 r 6 (bget r 6 - 1), (bpush (bpush (g30 o 16)
        (if bget k ((bget r 6 - 1) * 3 + 1) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0,
        (bset k ((bget r 6 - 1 - 2) * 3 + 1) (bsize o + 4), f)))
  g37_t4 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 4) :
      g37 x r o k t f = (match g20 (g15 r 6 (bget r 6 - 1)) (bpush o 0) (bget k ((bget r 6 - 1) * 3 + 1)) with
        | (r2, o2) => (r2, (o2, (bset k ((bget r 6 - 1 - 2) * 3 + 1) (bsize o), f))))
  g37_t5 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 5) :
      g37 x r o k t f = (match g20 (g15 r 6 (bget r 6 - 1)) o (bget k ((bget r 6 - 1) * 3 + 1)) with
        | (r2, o2) => (r2, (o2, (k, f))))
  g36_pair (x r o k : Buf) (hc : bget x (bget r 0) = 6) :
      g36 x r o k 0 = (if bget x (bget r 0 + 1) < 251 then
        (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + bget x (bget r 0 + 1)), (o, g27 256 k (bget r 6) (bget x (bget r 0 + 1))))
        else (g16 r, (o, k)))
  g36_call (x r o k : Buf) (hc : bget x (bget r 0) = 8) :
      g36 x r o k 0 = (if bget x (bget r 0 + 2) < 251 then
        (g15 (g15 r 0 (bget r 0 + 3)) 6 (bget r 6 + 1 + bget x (bget r 0 + 2)),
          (o, g27 256 (g18 k (bget r 6) 7 (bget x (bget r 0 + 1)) 0) (bget r 6 + 1) (bget x (bget r 0 + 2))))
        else (g16 r, (o, k)))
  g36_prim (x r o k : Buf) (hc : bget x (bget r 0) = 9) (hb : bget x (bget r 0 + 1) - 1 < 9) :
      g36 x r o k 0 = (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + 1 + g33 (bget x (bget r 0 + 1))),
          (o, g27 256 (g18 k (bget r 6) 8 (bget x (bget r 0 + 1)) 0) (bget r 6 + 1) (g33 (bget x (bget r 0 + 1)))))
  g36_prim_bad (x r o k : Buf) (y : UInt64) (hc : bget x (bget r 0) = 9) (hb : ¬ bget x (bget r 0 + 1) - 1 < 9) :
      g36 x r o k y = (g16 r, (o, k))
  g37_t7 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 7) :
      g37 x r o k t f = (match (if bget k ((bget r 6 - 1) * 3 + 1) < bsize t then
          g19 (g15 r 6 (bget r 6 - 1)) o 1 (bget t (bget k ((bget r 6 - 1) * 3 + 1)))
          else (g16 (g15 r 6 (bget r 6 - 1)), o)) with
        | (r2, o2) => (r2, (o2, (k, f))))
  g37_t8 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 8) :
      g37 x r o k t f = (g15 r 6 (bget r 6 - 1), (g32 o (bget k ((bget r 6 - 1) * 3 + 1)) (bget (g15 r 6 (bget r 6 - 1)) 9), (k, f)))
  g36_tval (x r o k : Buf) (hz : nt (bget x (bget r 0)) ≠ 4 ∧ nt (bget x (bget r 0)) ≠ 5 ∧ nt (bget x (bget r 0)) ≠ 10) :
      g36 x r o k 1 = (if rngA (nt (bget x (bget r 0))) (bget x (bget r 0 + 1)) == 0 then (g16 r, (o, k)) else
        (g15 r 6 (bget r 6 + 2), (o, g18 (g18 k (bget r 6) 9 0 0) (bget r 6 + 1) 1 0 0)))
  g36_tcont (x r o k : Buf) (hc : bget x (bget r 0) = 11) :
      g36 x r o k 1 = (g15 (g15 r 0 (bget r 0 + 1)) 6 (bget r 6 + 2), (o, g18 (g18 k (bget r 6) 10 0 0) (bget r 6 + 1) 1 0 0))
  g37_t9 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 9) :
      g37 x r o k t f = (if 65535 < bget (g15 r 6 (bget r 6 - 1)) 8 then (g16 (g15 r 6 (bget r 6 - 1)), (o, (k, f))) else
        (g15 (g15 r 6 (bget r 6 - 1)) 8 (bget (g15 r 6 (bget r 6 - 1)) 8 + 1), (bpush o 0,
          (k, g17 f (bget (g15 r 6 (bget r 6 - 1)) 8) (bsize o)))))
  g37_t10 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 10) :
      g37 x r o k t f =
        (if g14 (bsize (g26 256 (bget (g15 r 6 (bget r 6 - 1)) 1) 1 (bget (g15 r 6 (bget r 6 - 1)) 1 - 1) o))
            (bget (g15 r 6 (bget r 6 - 1)) 3) == 1 then g15 r 6 (bget r 6 - 1) else g16 (g15 r 6 (bget r 6 - 1)),
          (bpush (g26 256 (bget (g15 r 6 (bget r 6 - 1)) 1) 1 (bget (g15 r 6 (bget r 6 - 1)) 1 - 1) o)
            (g13 0 (bsize (g26 256 (bget (g15 r 6 (bget r 6 - 1)) 1) 1 (bget (g15 r 6 (bget r 6 - 1)) 1 - 1) o))
              (bget (g15 r 6 (bget r 6 - 1)) 3)), (k, f)))
  g36_tif (x r o k : Buf) (hc : bget x (bget r 0) = 4) (hb : bget x (bget r 0 + 1) - 1 < 2) :
      g36 x r o k 1 = (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + 7),
        (o, g18 (g18 (g18 (g18 (g18 (g18 (g18 k (bget r 6) 5 0 0) (bget r 6 + 1) 1 1 0) (bget r 6 + 2) 4 0 0) (bget r 6 + 3) 1 1 0)
          (bget r 6 + 4) 3 (bget x (bget r 0 + 1)) 0) (bget r 6 + 5) 1 0 0) (bget r 6 + 6) 1 0 0))
  g36_tlet (x r o k : Buf) (hc : bget x (bget r 0) = 5) :
      g36 x r o k 1 = (if g43 r (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2)) == 1 then (g16 r, (o, k)) else
        (g15 (g15 r 0 (bget r 0 + 3)) 6 (bget r 6 + 3), (o, g18 (g18 (g18 k (bget r 6) 1 1 0) (bget r 6 + 1) 6
          (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2))) (bget r 6 + 2) 1 0 0)))
  g36_loop (x r o k : Buf) (hc : bget x (bget r 0) = 10) :
      g36 x r o k 0 = (if bget r 6 == 1 then
        (g15 (g15 (g15 r 0 (bget r 0 + 1)) 3 (bsize o)) 6 (bget r 6 + 3),
          (bpush (bpush (bpush o (g11 5 8 (g24 (bget r 1) 0))) (g4 0 5 0 8)) 0,
           g18 (g18 (g18 k (bget r 6) 1 1 0) (bget r 6 + 1) 11 (bsize o + 2) 0) (bget r 6 + 2) 1 1 0))
        else (g16 r, (o, k)))
  g37_t11 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 11) :
      g37 x r o k t f = (if g14 (bget k ((bget r 6 - 1) * 3 + 1)) (bsize o) == 1 then g15 r 6 (bget r 6 - 1)
          else g16 (g15 r 6 (bget r 6 - 1)),
        (bpush (bpush (bset o (bget k ((bget r 6 - 1) * 3 + 1)) (g13 0 (bget k ((bget r 6 - 1) * 3 + 1)) (bsize o)))
          (g10 5 5 g_901)) (g12 5 8 (g24 (bget (g15 r 6 (bget r 6 - 1)) 1) 0)), (k, f)))
  g36_bad (x r o k : Buf) (hc : nt (bget x (bget r 0)) ≠ 1 ∧ nt (bget x (bget r 0)) ≠ 2 ∧ nt (bget x (bget r 0)) ≠ 3 ∧
      nt (bget x (bget r 0)) ≠ 4 ∧ nt (bget x (bget r 0)) ≠ 5 ∧ nt (bget x (bget r 0)) ≠ 6 ∧ nt (bget x (bget r 0)) ≠ 7 ∧
      nt (bget x (bget r 0)) ≠ 8 ∧ nt (bget x (bget r 0)) ≠ 9) :
      g36 x r o k 0 = (g16 r, (o, k))
open EmOK SrcOK
variable [EmOK] [SrcOK]

/-- one work item (g39's `bget r 6 ≠ 0` branch) -/
def st (s : GS) : GS :=
  match g37 s.x s.r s.o s.k s.t s.f with
  | (r1, (o1, (k1, f1))) => ⟨s.x, r1, o1, k1, s.t, f1⟩

/-- `it m s` = m work items from s -/
def it : Nat → GS → GS
  | 0, s => s
  | n + 1, s => it n (st s)

theorem it_add : ∀ (n m : Nat) (s : GS), it (n + m) s = it n (it m s)
  | n, 0, s => rfl
  | n, m + 1, s => by rw [show n + (m + 1) = (n + m) + 1 by omega]; simp only [it]; exact it_add n m (st s)

def Reach (s : GS) (P : GS → Prop) : Prop :=
  ∃ m, (∀ j < m, live (it j s)) ∧ (P (it m s) ∨ err (it m s) ∨ big (it m s))

theorem Reach.done {s : GS} {P : GS → Prop} (h : P s) : Reach s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inl h⟩

theorem Reach.error {s : GS} {P : GS → Prop} (h : err s) : Reach s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inr (.inl h)⟩

theorem Reach.toobig {s : GS} {P : GS → Prop} (h : big s) : Reach s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inr (.inr h)⟩

theorem Reach.step {s : GS} {P : GS → Prop} (hl : live s) (h : Reach (st s) P) : Reach s P := by
  obtain ⟨m, hm, hp⟩ := h
  refine ⟨m + 1, fun j hj => ?_, hp⟩
  rcases j with _ | j
  · exact hl
  · exact hm j (by omega)

theorem Reach.bind {s : GS} {P Q : GS → Prop} (h : Reach s P) (hq : ∀ s', P s' → Reach s' Q) : Reach s Q := by
  obtain ⟨m, hm, hp⟩ := h
  rcases hp with hp | he
  · obtain ⟨n, hn, hq⟩ := hq _ hp
    refine ⟨n + m, fun j hj => ?_, by rw [it_add]; exact hq⟩
    by_cases hjm : j < m
    · exact hm j hjm
    · have := hn (j - m) (by omega)
      rw [← it_add] at this
      rwa [show j - m + m = j by omega] at this
  · exact ⟨m, hm, .inr he⟩

/-- `jal rd` from word a to word b -/
def jw (rd : UInt64) (a b : Nat) : UInt64 := g13 rd a.toUInt64 b.toUInt64

/-- IF's compare + branch -/
def ifHd (cmp : UInt64) : List UInt64 := [g11 6 31 0, g11 5 31 8, g10 31 31 16, if cmp == 1 then g4 0 5 6 8 else g4 6 5 6 8]

/-- LOOP's head: t0 := fuel; beq t0, x0, +8; (placeholder → the step arm) -/
def lpHd (p : UInt64) : List UInt64 := [g11 5 8 (g24 p 0), g4 0 5 0 8]

/-- LOOP's decrement (item 11) -/
def lpDec (p : UInt64) : List UInt64 := [g10 5 5 g_901, g12 5 8 (g24 p 0)]

/-- Gen's range check on a jump from word a to word b passed -/
def JOk (a b : Nat) : Prop := g14 a.toUInt64 b.toUInt64 = 1

mutual
inductive CG (K : Cx) : Nat → Nat → Nat → List UInt64 → Nat → List Nat → Prop
  | const {d i h} : tg K.X i = 1 → CG K d i h (em (fun o => g21 (g23 o 5 (tg K.X (i + 1)))) h) (i + 2) []
  | local {d i h} : tg K.X i = 2 → SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2)) →
      CG K d i h (em (g25 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) h) (i + 3) []
  | bin {d i h ca cb i1 i2 Ea Eb} : tg K.X i = 3 → tg K.X (i + 1) - 1 < 8 →
      CG K (d + 2) (i + 2) h ca i1 Ea → CG K (d + 1) i1 (h + ca.length) cb i2 Eb →
      CG K d i h (ca ++ cb ++ em (fun o => g31 o (tg K.X (i + 1))) (h + ca.length + cb.length)) i2 (Ea ++ Eb)
  | ite {d i h ca cb ct ce i1 i2 i3 i4 Ea Eb Et Ee} : tg K.X i = 4 → tg K.X (i + 1) - 1 < 2 →
      CG K (d + 6) (i + 2) h ca i1 Ea → CG K (d + 5) i1 (h + ca.length) cb i2 Eb →
      CG K (d + 3) i2 (h + ca.length + cb.length + 5) ct i3 Et →
      CG K (d + 1) i3 (h + ca.length + cb.length + 5 + ct.length + 1) ce i4 Ee →
      JOk (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1) →
      JOk (h + ca.length + cb.length + 5 + ct.length) (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length) →
      CG K d i h (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
        [jw 0 (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
        [jw 0 (h + ca.length + cb.length + 5 + ct.length) (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)
        i4 (Ea ++ Eb ++ Et ++ Ee)
  | lett {d i h cv cb i1 i2 Ev Eb} : tg K.X i = 5 → SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2)) →
      CG K (d + 2) (i + 3) h cv i1 Ev →
      CG K d i1 (h + cv.length + (em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (h + cv.length)).length) cb i2 Eb →
      CG K d i h (cv ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (h + cv.length) ++ cb) i2 (Ev ++ Eb)
  | pair {d i h c i' E} : tg K.X i = 6 → tg K.X (i + 1) < 251 →
      CGs K d (i + 2) h (tg K.X (i + 1)).toNat c i' E → CG K d i h c i' E
  | call {d i h c i' E} : tg K.X i = 8 → tg K.X (i + 2) < 251 → tg K.X (i + 1) < bsize K.T →
      CGs K (d + 1) (i + 3) h (tg K.X (i + 2)).toNat c i' E →
      g14 (h + c.length).toUInt64 (bget K.T (tg K.X (i + 1))) = 1 →
      CG K d i h (c ++ [g13 1 (h + c.length).toUInt64 (bget K.T (tg K.X (i + 1)))]) i' E
  | prim {d i h c i' E} : tg K.X i = 9 → tg K.X (i + 1) - 1 < 9 →
      CGs K (d + 1) (i + 2) h (g33 (tg K.X (i + 1))).toNat c i' E →
      CG K d i h (c ++ em (fun o => g32 o (tg K.X (i + 1)) K.u) (h + c.length)) i' E
  | loop {i h cz cs i1 i2 Ez Es} : tg K.X i = 10 →
      CT K h 3 (i + 1) (h + 3) cz i1 Ez →
      CT K h 1 i1 (h + 3 + cz.length + 2) cs i2 Es →
      JOk (h + 2) (h + 3 + cz.length) →
      CG K 1 i h (lpHd K.p ++ [jw 0 (h + 2) (h + 3 + cz.length)] ++ cz ++ lpDec K.p ++ cs) i2 (Ez ++ Es)
inductive CT (K : Cx) : Nat → Nat → Nat → Nat → List UInt64 → Nat → List Nat → Prop
  /-- a value node in tail position: value, then an exit placeholder -/
  | val {hd d i h c i' E} : tg K.X i ≠ 4 → tg K.X i ≠ 5 → tg K.X i ≠ 11 →
      CG K (d + 1) i h c i' E → CT K hd d i h (c ++ [0]) i' (E ++ [h + c.length])
  | cont {hd d i h c i'} : tg K.X i = 11 →
      CG K (d + 1) (i + 1) h c i' [] →
      JOk (h + c.length + (em (g26 256 K.p 1 (K.p - 1)) (h + c.length)).length) hd →
      CT K hd d i h (c ++ em (g26 256 K.p 1 (K.p - 1)) (h + c.length) ++
        [jw 0 (h + c.length + (em (g26 256 K.p 1 (K.p - 1)) (h + c.length)).length) hd]) i' []
  | ite {hd d i h ca cb ct ce i1 i2 i3 i4 Ea Eb Et Ee} : tg K.X i = 4 → tg K.X (i + 1) - 1 < 2 →
      CG K (d + 6) (i + 2) h ca i1 Ea → CG K (d + 5) i1 (h + ca.length) cb i2 Eb →
      CT K hd (d + 3) i2 (h + ca.length + cb.length + 5) ct i3 Et →
      CT K hd (d + 1) i3 (h + ca.length + cb.length + 5 + ct.length + 1) ce i4 Ee →
      JOk (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1) →
      JOk (h + ca.length + cb.length + 5 + ct.length) (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length) →
      CT K hd d i h (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
        [jw 0 (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
        [jw 0 (h + ca.length + cb.length + 5 + ct.length) (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)
        i4 (Ea ++ Eb ++ Et ++ Ee)
  | lett {hd d i h cv cb i1 i2 Ev Eb} : tg K.X i = 5 → SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2)) →
      CG K (d + 2) (i + 3) h cv i1 Ev →
      CT K hd d i1 (h + cv.length + (em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (h + cv.length)).length) cb i2 Eb →
      CT K hd d i h (cv ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (h + cv.length) ++ cb) i2 (Ev ++ Eb)
inductive CGs (K : Cx) : Nat → Nat → Nat → Nat → List UInt64 → Nat → List Nat → Prop
  | nil {d i h} : CGs K d i h 0 [] i []
  | cons {d i h n c cs i1 i2 E Es} : CG K (d + n) i h c i1 E → CGs K d i1 (h + c.length) n cs i2 Es →
      CGs K d i h (n + 1) (c ++ cs) i2 (E ++ Es)
end

/-- popping a visit item: `st` is g36 on the popped register file -/
theorem st_visit {K s L F} {m : UInt64} (hI : Inv K s (L ++ [(1, m, 0)]) F) :
    st s = (match g36 s.x (bset s.r 6 L.length.toUInt64) s.o s.k m with
      | (r2, (o2, k2)) => ⟨s.x, r2, o2, k2, s.t, s.f⟩) := by
  have hL := hI.Ll; simp at hL
  obtain ⟨t0, t1, t2⟩ := stk_top hI.stk
  have hn : bget s.r 6 - 1 = L.length.toUInt64 := by
    apply UInt64.toNat.inj; rw [hI.r6]; simp [Nat.toUInt64]
  have e0 : bget s.k (L.length.toUInt64 * 3) = 1 := by
    simp only [bget]; rw [show (L.length.toUInt64 * 3).toNat = 3 * L.length by simp [Nat.toUInt64]; omega, t0]
  have e1 : bget s.k (L.length.toUInt64 * 3 + 1) = m := by
    simp only [bget]; rw [show (L.length.toUInt64 * 3 + 1).toNat = 3 * L.length + 1 by simp [Nat.toUInt64]; omega, t1]
  unfold st
  rw [g37_visit _ _ _ _ _ _ (by rw [hn, e0]), hn, e1]
  rfl

/-- the value-visit postcondition: the node at i emitted c (CG), the item is gone, cursor at i' -/
def VPost (K : Cx) (s0 : GS) (L : List Item) (F : List UInt64) (d i : Nat) (s' : GS) : Prop :=
  ∃ c i' E, CG K d i s0.o.length c i' E ∧ Inv K s' L (F ++ E.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ (i < i' ∧ i' ≤ K.X.length + 3) ∧ (2 ≤ d → E = [] ∧ bget s'.r 3 = bget s0.r 3)

theorem pi_const (v : UInt64) : PI (fun o => g21 (g23 o 5 v)) := pi_comp (pi_g23 5 v) pi_g21

/-- CONST -/
theorem v_const {K s L F d i} (hI : Inv K s (L ++ [(1, 0, 0)]) F) (hr0 : bget s.r 0 = i.toUInt64) (hi : i < 2 ^ 31) (hiX : i < K.X.length)
    (ht : tg K.X i = 1) : Reach s (VPost K s L F d i) := by
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, -⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 1 := by rw [hI.x, tg_u _ _ (by omega), ht]
  rw [g36_const _ _ _ _ (by rw [h0]; exact hx), h0]
  dsimp only
  have hv : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have e : g21 (g23 s.o 5 (tg K.X (i + 1))) = s.o ++ em (fun o => g21 (g23 o 5 (tg K.X (i + 1)))) s.o.length :=
    pi_const _ s.o
  rw [hv, e]
  by_cases hb : 2 ^ 24 ≤ (s.o ++ em (fun o => g21 (g23 o 5 (tg K.X (i + 1)))) s.o.length).length
  · exact Reach.toobig ⟨hb, by have := hI.ol; have := em_le (fun o => g21 (g23 o 5 (tg K.X (i + 1)))) s.o.length 21 (fun o => by have := g23_len o 5 (tg K.X (i + 1)); rw [g21_len]; omega); simp; omega⟩
  obtain ⟨q1, q2, q3, q4⟩ := r06 s.r hI.rl L.length.toUInt64 (i.toUInt64 + 2)
  refine Reach.done ⟨_, i + 2, [], .const ht, ?_, rfl, ?_, by omega, fun _ => ⟨rfl, ?_⟩⟩
  · simp only [List.map_nil, List.append_nil]
    exact inv_mk hI _ _ _ L q4 q1 q2 (stk_pop hI.stk) hI.kl (by have := hI.Ll; simp at this; omega) (by omega)
  · simp only [g15]; rw [q3]; simp [Nat.toUInt64, UInt64.ofNat_add]
  · simp only [g15]; rw [q4 3 (by decide) (by decide)]

/-- LOCAL -/
theorem v_local {K s L F d i} (hI : Inv K s (L ++ [(1, 0, 0)]) F) (hr0 : bget s.r 0 = i.toUInt64) (hi : i < 2 ^ 31) (hiX : i < K.X.length)
    (ht : tg K.X i = 2) : Reach s (VPost K s L F d i) := by
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, -⟩ := r6_get hI hr0 L.length.toUInt64
  have h1 : bget (bset s.r 6 L.length.toUInt64) 1 = K.p := by
    rw [rget _ hI.rl 6 1 _ (by decide), if_neg (by decide), hI.r1]
  have h7 : bget (bset s.r 6 L.length.toUInt64) 7 = K.ns := by
    rw [rget _ hI.rl 6 7 _ (by decide), if_neg (by decide), hI.r7]
  have hx : bget s.x i.toUInt64 = 2 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have hv2 : bget s.x (i.toUInt64 + 2) = tg K.X (i + 2) := by rw [hI.x]; exact tg_u1 _ i 2 (by omega)
  rw [g36_local _ _ _ _ (by rw [h0]; exact hx), h0, hv1, hv2, h1, g43_ok _ _ _ _ h7]
  by_cases hs : SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2))
  · have hs' : tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2) := hs
    rw [if_pos hs']
    simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false]
    have e := pi_g25 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s.o
    rw [e]
    by_cases hb : 2 ^ 24 ≤ (s.o ++ em (g25 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s.o.length).length
    · exact Reach.toobig ⟨hb, by have := hI.ol; have := em_le (g25 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s.o.length 1280 (fun o => by have := g25_len 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) o; omega); simp; omega⟩
    obtain ⟨q1, q2, q3, q4⟩ := r06 s.r hI.rl L.length.toUInt64 (i.toUInt64 + 3)
    refine Reach.done ⟨_, i + 3, [], .local ht hs, ?_, rfl, ?_, by omega, fun _ => ⟨rfl, ?_⟩⟩
    · simp only [List.map_nil, List.append_nil]
      exact inv_mk hI _ _ _ L q4 q1 q2 (stk_pop hI.stk) hI.kl (by have := hI.Ll; simp at this; omega) (by omega)
    · simp only [g15]; rw [q3]; simp [Nat.toUInt64, UInt64.ofNat_add]
    · simp only [g15]; rw [q4 3 (by decide) (by decide)]
  · have hs' : ¬ (tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2)) := hs
    rw [if_neg hs']
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    exact Reach.error (g16_err _ hl6)

/-- value visit at AST word i (the induction statement) -/
def VS (K : Cx) (i : Nat) : Prop := i ≤ K.X.length + 3 → ∀ s L F, Inv K s (L ++ [(1, 0, 0)]) F → bget s.r 0 = i.toUInt64 →
  L.length + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach s (VPost K s L F L.length i)

/-- BIN -/
theorem v_bin {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 3) :
    VS K i := by
  intro hiX s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 3 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  by_cases hb' : ¬ tg K.X (i + 1) - 1 < 8
  · rw [g36_bin_bad _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb')]
    exact Reach.error (g16_err _ hl6)
  have hb : tg K.X (i + 1) - 1 < 8 := Classical.not_not.mp hb'
  rw [g36_bin _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb), h0, h6, hv1]
  dsimp only
  have hLl := hI.Ll; simp at hLl
  have hsk := stk_pop hI.stk
  obtain ⟨sk1, kl1⟩ := stk_push3 s.k L (2, tg K.X (i + 1), 0) (1, 0, 0) (1, 0, 0) hsk hI.kl (by omega)
  simp only at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + 3) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 3)) _ s.o
    (L ++ [(2, tg K.X (i + 1), 0), (1, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
    (by simp; omega) hI.ol
  -- child a at i + 2
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 3)) 0 = (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  refine Reach.bind (IH (i + 2) (by omega) (by omega) _ (L ++ [(2, tg K.X (i + 1), 0), (1, 0, 0)]) F (by simpa using hI1) hra
    (by simp; omega)) ?_
  rintro s2 ⟨ca, i1, Ea, hca, hI2, ho2, hr2, hi1, hd2⟩
  refine Reach.bind (IH i1 (by omega) (by omega) s2 (L ++ [(2, tg K.X (i + 1), 0)]) (F ++ Ea.map Nat.toUInt64)
    (by simpa using hI2) hr2 (by simp; omega)) ?_
  rintro s3 ⟨cb, i2, Eb, hcb, hI3, ho3, hr3, hi2, hd3⟩
  refine Reach.step (live_of hI3 (by simp)) ?_
  obtain ⟨n3, c3, a3, -⟩ := top_item hI3
  have hst : st s3 = ⟨s3.x, g15 s3.r 6 L.length.toUInt64, g31 s3.o (tg K.X (i + 1)), s3.k, s3.t, s3.f⟩ := by
    unfold st; rw [g37_t2 _ _ _ _ _ _ c3, a3, n3]
  rw [hst]
  have e := pi_g31 (tg K.X (i + 1)) s3.o
  simp only at e
  rw [e]
  by_cases hbig : 2 ^ 24 ≤ (s3.o ++ em (fun o => g31 o (tg K.X (i + 1))) s3.o.length).length
  · exact Reach.toobig ⟨hbig, by have := hI3.ol; have := em_le (fun o => g31 o (tg K.X (i + 1))) s3.o.length 5 (fun o => g31_len o _); simp; omega⟩
  have ho : s3.o = s.o ++ ca ++ cb := by rw [ho3, ho2]
  have hI4 := inv_mk hI3 (g15 s3.r 6 L.length.toUInt64) s3.k (s3.o ++ em (fun o => g31 o (tg K.X (i + 1))) s3.o.length) L
    (fun j a b => by simp only [g15]; rw [rget _ hI3.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (by simp only [g15]; rw [BufL.length_bset]; exact hI3.rl)
    (by simp only [g15]; rw [rget _ hI3.rl 6 6 _ (by decide), if_pos rfl]) (stk_pop hI3.stk) hI3.kl (by omega) (by omega)
  refine Reach.done ⟨ca ++ cb ++ em (fun o => g31 o (tg K.X (i + 1))) (s.o.length + ca.length + cb.length), i2, Ea ++ Eb,
    ?_, ?_, ?_, ?_, by omega, fun hd => ?_⟩
  · have hca' : CG K (L.length + 2) (i + 2) s.o.length ca i1 Ea := by simpa using hca
    have hcb' : CG K (L.length + 1) i1 (s.o.length + ca.length) cb i2 Eb := by
      have : s2.o.length = s.o.length + ca.length := by rw [ho2]; simp
      simpa [this] using hcb
    exact .bin ht hb hca' hcb'
  · rw [List.map_append, ← List.append_assoc]; exact hI4
  · simp only; rw [ho]; simp [List.append_assoc, Nat.add_assoc]
  · simp only [g15]; rw [rget _ hI3.rl 6 0 _ (by decide), if_neg (by decide), hr3]
  · obtain ⟨ea, r3a⟩ := hd2 (by simp)
    obtain ⟨eb, r3b⟩ := hd3 (by simp; omega)
    refine ⟨by rw [ea, eb]; rfl, ?_⟩
    simp only [g15]; rw [rget _ hI3.rl 6 3 _ (by decide), if_neg (by decide), r3b, r3a]
    simp only [g15]
    rw [rset2 _ hl6 0 6 _ _ (by decide) (by decide), if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]

/-- LET (value mode) -/
theorem v_let {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 5) :
    VS K i := by
  intro hiX s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have h7 : bget (bset s.r 6 L.length.toUInt64) 7 = K.ns := by
    rw [rget _ hI.rl 6 7 _ (by decide), if_neg (by decide), hI.r7]
  have hx : bget s.x i.toUInt64 = 5 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have hv2 : bget s.x (i.toUInt64 + 2) = tg K.X (i + 2) := by rw [hI.x]; exact tg_u1 _ i 2 (by omega)
  rw [g36_let _ _ _ _ (by rw [h0]; exact hx), h0, h6, hv1, hv2, g43_ok _ _ _ _ h7]
  by_cases hs : SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2))
  · have hs' : tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2) := hs
    rw [if_pos hs']
    simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false]
    have hLl := hI.Ll; simp at hLl
    have hsk := stk_pop hI.stk
    obtain ⟨sk1, kl1⟩ := stk_push3 s.k L (1, 0, 0) (6, tg K.X (i + 1), tg K.X (i + 2)) (1, 0, 0) hsk hI.kl (by omega)
    simp only at sk1 kl1
    have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 3) (L.length.toUInt64 + 3) (by decide) (by decide)
    have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 3)) _ s.o
      (L ++ [(1, 0, 0), (6, tg K.X (i + 1), tg K.X (i + 2)), (1, 0, 0)])
      (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
      (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
      (by simp; omega) hI.ol
    have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 3)) 0 = (i + 3).toUInt64 := by
      simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
    refine Reach.bind (IH (i + 3) (by omega) (by omega) _ (L ++ [(1, 0, 0), (6, tg K.X (i + 1), tg K.X (i + 2))]) F (by simpa using hI1) hra
      (by simp; omega)) ?_
    rintro s2 ⟨cv, i1, Ev, hcv, hI2, ho2, hr2, hi1, hd2⟩
    -- the slot-pop item
    have hI2' : Inv K s2 ((L ++ [(1, 0, 0)]) ++ [(6, tg K.X (i + 1), tg K.X (i + 2))]) (F ++ Ev.map Nat.toUInt64) := by simpa using hI2
    refine Reach.step (live_of hI2' (by simp)) ?_
    obtain ⟨n2, c2, a2, b2⟩ := top_item hI2'
    have hp2 : bget (g15 s2.r 6 (L ++ [(1, 0, 0)]).length.toUInt64) 1 = K.p := by
      simp only [g15]; rw [rget _ hI2.rl 6 1 _ (by decide), if_neg (by decide), hI2.r1]
    have hst : st s2 = ⟨s2.x, g15 s2.r 6 (L ++ [(1, 0, 0)]).length.toUInt64,
        g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s2.o, s2.k, s2.t, s2.f⟩ := by
      unfold st; rw [g37_t6 _ _ _ _ _ _ c2, a2, b2, n2, hp2]
    rw [hst]
    have e := pi_g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s2.o
    rw [e]
    by_cases hbig : 2 ^ 24 ≤ (s2.o ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length).length
    · exact Reach.toobig ⟨hbig, by have := hI2.ol; have := em_le (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length 768 (fun o => by have := g26_len 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) o; omega); simp; omega⟩
    have hI3 := inv_mk hI2' (g15 s2.r 6 (L ++ [(1, 0, 0)]).length.toUInt64) s2.k
      (s2.o ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length) (L ++ [(1, 0, 0)])
      (fun j a b => by simp only [g15]; rw [rget _ hI2.rl 6 j _ (by decide), if_neg (Ne.symm b)])
      (by simp only [g15]; rw [BufL.length_bset]; exact hI2.rl)
      (by simp only [g15]; rw [rget _ hI2.rl 6 6 _ (by decide), if_pos rfl]) (stk_pop hI2'.stk) hI2.kl (by simp; omega) (by omega)
    have hr3 : bget (g15 s2.r 6 (L ++ [(1, 0, 0)]).length.toUInt64) 0 = i1.toUInt64 := by
      simp only [g15]; rw [rget _ hI2.rl 6 0 _ (by decide), if_neg (by decide), hr2]
    refine Reach.bind (IH i1 (by omega) (by omega) _ L (F ++ Ev.map Nat.toUInt64) hI3 hr3 (by omega)) ?_
    rintro s4 ⟨cb, i2, Eb, hcb, hI4, ho4, hr4, hi2, hd4⟩
    have hem : s2.o.length = s.o.length + cv.length := by rw [ho2]; simp
    refine Reach.done ⟨cv ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (s.o.length + cv.length) ++ cb, i2, Ev ++ Eb,
      ?_, ?_, ?_, hr4, by omega, fun hd => ?_⟩
    · have hcv' : CG K (L.length + 2) (i + 3) s.o.length cv i1 Ev := by simpa using hcv
      have hcb' : CG K L.length i1 (s.o.length + cv.length +
          (em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (s.o.length + cv.length)).length) cb i2 Eb := by
        simpa [hem, Nat.add_assoc] using hcb
      exact .lett ht hs hcv' hcb'
    · rw [List.map_append, ← List.append_assoc]; exact hI4
    · rw [ho4, ho2]; simp [hem, List.append_assoc]
    · obtain ⟨ev, r3a⟩ := hd2 (by simp)
      obtain ⟨eb, r3b⟩ := hd4 hd
      refine ⟨by rw [ev, eb]; rfl, ?_⟩
      rw [r3b]; simp only [g15]; rw [rget _ hI2.rl 6 3 _ (by decide), if_neg (by decide), r3a]
      simp only [g15]
      rw [rset2 _ hl6 0 6 _ _ (by decide) (by decide), if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  · have hs' : ¬ (tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2)) := hs
    rw [if_neg hs']
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    exact Reach.error (g16_err _ hl6)

theorem st_t4 (s : GS) (n P : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 4)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = P) :
    st s = ⟨s.x, if g14 P (bsize (bpush s.o 0)) == 1 then g15 s.r 6 n else g16 (g15 s.r 6 n),
      bset (bpush s.o 0) P (g13 0 P (bsize (bpush s.o 0))), bset s.k ((n - 2) * 3 + 1) (bsize s.o), s.t, s.f⟩ := by
  unfold st; rw [g37_t4 _ _ _ _ _ _ hc, ha, hn, g20_eq]

theorem st_t5 (s : GS) (n P : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 5)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = P) :
    st s = ⟨s.x, if g14 P (bsize s.o) == 1 then g15 s.r 6 n else g16 (g15 s.r 6 n),
      bset s.o P (g13 0 P (bsize s.o)), s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t5 _ _ _ _ _ _ hc, ha, hn, g20_eq]

/-- IF (value mode) -/
theorem v_if {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 4) :
    VS K i := by
  intro hiX s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 4 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  by_cases hb' : ¬ tg K.X (i + 1) - 1 < 2
  · rw [g36_if_bad _ _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb')]
    exact Reach.error (g16_err _ hl6)
  have hb : tg K.X (i + 1) - 1 < 2 := Classical.not_not.mp hb'
  rw [g36_if _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb), h0, h6, hv1]
  dsimp only
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk1, kl1⟩ := stk_push7 s.k L (5, 0, 0) (1, 0, 0) (4, 0, 0) (1, 0, 0) (3, (tg K.X (i + 1)), 0) (1, 0, 0) (1, 0, 0)
    (stk_pop hI.stk) hI.kl (by omega)
  simp only at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + 7) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) _ s.o
    (L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0), (3, (tg K.X (i + 1)), 0), (1, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) 0 = (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have hr3_1 : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) 3 = bget s.r 3 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  -- operand a
  refine Reach.bind (IH (i + 2) (by omega) (by omega) _ (L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0), (3, (tg K.X (i + 1)), 0), (1, 0, 0)]) F
    (by simpa using hI1) hra (by simp; omega)) ?_
  rintro s2 ⟨ca, i1, Ea, hca, hI2, ho2, hr2, hi1, hd2⟩
  obtain ⟨ea, r3a⟩ := hd2 (by simp)
  subst ea
  -- operand b
  refine Reach.bind (IH i1 (by omega) (by omega) s2 (L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0), (3, (tg K.X (i + 1)), 0)]) F
    (by simpa using hI2) hr2 (by simp; omega)) ?_
  rintro s3 ⟨cb, i2, Eb, hcb, hI3, ho3, hr3, hi2, hd3⟩
  obtain ⟨eb, r3b⟩ := hd3 (by simp)
  subst eb
  simp only [List.map_nil, List.append_nil] at hI3
  -- compare item
  have hI3' : Inv K s3 ((L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0)]) ++ [(3, (tg K.X (i + 1)), 0)]) F := by simpa using hI3
  refine Reach.step (live_of hI3' (by simp)) ?_
  obtain ⟨n3, c3, a3, -⟩ := top_item hI3'
  simp only [List.length_append, List.length_cons, List.length_nil] at n3
  have hidx : ((L.length + 4).toUInt64 - 2) * 3 + 1 = (3 * (L.length + 2) + 1).toUInt64 := by
    apply UInt64.toNat.inj; simp [Nat.toUInt64, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_add]; omega
  have hst : st s3 = ⟨s3.x, g15 s3.r 6 (L.length + 4).toUInt64, bpush (bpush (g30 s3.o 16)
      (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0,
      bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4), s3.t, s3.f⟩ := by
    unfold st; rw [g37_t3 _ _ _ _ _ _ c3, a3, n3, hidx]
  rw [hst]
  have ho3' : s3.o = s.o ++ ca ++ cb := by rw [ho3, ho2]
  by_cases hbig : 2 ^ 24 ≤ (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0).length
  · exact Reach.toobig ⟨hbig, by have := hI3.ol; simp [g30_eq, bpush]; omega⟩
  obtain ⟨q1, q2, q3⟩ := r6set s3.r hI3.rl (L.length + 4).toUInt64
  have sk4 : Stk (bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4))
      (L ++ [(5, 0, 0), (1, 0, 0), (4, bsize s3.o + 4, 0), (1, 0, 0)]) := by
    have hp := stk_pop hI3'.stk
    have := stk_set hp (L.length + 2) (4, 0, 0) (by simp) (bsize s3.o + 4)
    simp only [bset]
    rw [u_toNat _ (by omega)]
    have e : (L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0)]).set (L.length + 2) ((4 : UInt64), bsize s3.o + 4, (0 : UInt64)) =
        L ++ [(5, 0, 0), (1, 0, 0), (4, bsize s3.o + 4, 0), (1, 0, 0)] := by
      rw [List.set_append_right _ _ (by omega)]; simp
    rw [← e]; simpa using this
  have hI4 := inv_mk hI3' (g15 s3.r 6 (L.length + 4).toUInt64) (bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4))
    (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0)
    (L ++ [(5, 0, 0), (1, 0, 0), (4, bsize s3.o + 4, 0), (1, 0, 0)])
    (fun j a b => q3 j b) q1 (by simp only [g15]; rw [q2]; simp) sk4 (by rw [BufL.length_bset]; exact hI3.kl) (by simp; omega) (by omega)
  have hr4 : bget (g15 s3.r 6 (L.length + 4).toUInt64) 0 = i2.toUInt64 := by simp only [g15]; rw [q3 0 (by decide), hr3]
  -- then branch
  refine Reach.bind (IH i2 (by omega) (by omega) _ (L ++ [(5, 0, 0), (1, 0, 0), (4, bsize s3.o + 4, 0)]) F
    (by simpa using hI4) hr4 (by simp; omega)) ?_
  rintro s5 ⟨ct, i3, Et, hct, hI5, ho5, hr5, hi3, hd5⟩
  obtain ⟨et, r3t⟩ := hd5 (by simp)
  subst et
  simp only [List.map_nil, List.append_nil] at hI5
  -- item 4: patch the compare's jump to here + 1, leave the end placeholder
  have hI5' : Inv K s5 ((L ++ [(5, 0, 0), (1, 0, 0)]) ++ [(4, bsize s3.o + 4, 0)]) F := by simpa using hI5
  refine Reach.step (live_of hI5' (by simp)) ?_
  obtain ⟨n5, c5, a5, -⟩ := top_item hI5'
  simp only [List.length_append, List.length_cons, List.length_nil] at n5
  have hidx5 : ((L.length + 2).toUInt64 - 2) * 3 + 1 = (3 * L.length + 1).toUInt64 := by
    apply UInt64.toNat.inj; simp [Nat.toUInt64, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_add]; omega
  have hst5 : st s5 = ⟨s5.x, if g14 (bsize s3.o + 4) (bsize (bpush s5.o 0)) == 1 then g15 s5.r 6 (L.length + 2).toUInt64
      else g16 (g15 s5.r 6 (L.length + 2).toUInt64),
      bset (bpush s5.o 0) (bsize s3.o + 4) (g13 0 (bsize s3.o + 4) (bsize (bpush s5.o 0))),
      bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o), s5.t, s5.f⟩ := by
    rw [st_t4 s5 _ _ n5 c5 a5, hidx5]
  rw [hst5]
  obtain ⟨p1, p2, p3⟩ := r6set s5.r hI5.rl (L.length + 2).toUInt64
  by_cases hg' : ¬ (g14 (bsize s3.o + 4) (bsize (bpush s5.o 0)) == 1) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ p1)
  have hg1 := Classical.not_not.mp hg'
  rw [if_pos hg1]
  -- the code so far
  have hA : s5.o = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++ 0 :: ct := by
    rw [ho5, ho3']; simp [g30_eq, bpush, ifHd, List.append_assoc]
  have hl3 : s3.o.length = s.o.length + ca.length + cb.length := by rw [ho3']; simp [Nat.add_assoc]
  have hol3 := hI3.ol
  have hpj : bsize s3.o + 4 = (s.o.length + ca.length + cb.length + 4).toUInt64 := by
    rw [ulen _ _ hl3]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have j1 : JOk (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) := by
    have hl5 : (bpush s5.o 0).length = s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by
      rw [bpush, hA]; simp [ifHd]; omega
    unfold JOk; rw [← hpj, ← ulen _ _ hl5]; simpa using hg1
  have hP : (bsize s3.o + 4).toNat = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))).length := by
    rw [hpj, u_toNat _ (by omega)]; simp [ifHd]; omega
  have ho6 : bset (bpush s5.o 0) (bsize s3.o + 4) (g13 0 (bsize s3.o + 4) (bsize (bpush s5.o 0))) =
      (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0]) := by
    have hl5 : (bpush s5.o 0).length = s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by
      rw [bpush, hA]; simp [ifHd]; omega
    rw [ulen _ _ hl5, show bpush s5.o 0 = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++ 0 :: (ct ++ [0]) by rw [bpush, hA]; simp,
      bset_mid _ _ _ _ _ hP, jw, ← hpj]
  rw [ho6]
  by_cases hbig6 : 2 ^ 24 ≤ ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])).length
  · exact Reach.toobig ⟨hbig6, by have := hI5.ol; rw [hA] at this; simp [ifHd] at this ⊢; omega⟩
  have sk6 : Stk (bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o)) (L ++ [(5, bsize s5.o, 0), (1, 0, 0)]) := by
    have hp := stk_pop hI5'.stk
    have := stk_set hp L.length (5, 0, 0) (by simp) (bsize s5.o)
    simp only [bset]
    rw [u_toNat _ (by omega)]
    have e : (L ++ [(5, 0, 0), (1, 0, 0)]).set L.length ((5 : UInt64), bsize s5.o, (0 : UInt64)) =
        L ++ [(5, bsize s5.o, 0), (1, 0, 0)] := by
      rw [List.set_append_right _ _ (by omega)]; simp
    rw [← e]; simpa using this
  have hI6 := inv_mk hI5' (g15 s5.r 6 (L.length + 2).toUInt64) (bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o))
    ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0]))
    (L ++ [(5, bsize s5.o, 0), (1, 0, 0)]) (fun j a b => p3 j b) p1 (by simp only [g15]; rw [p2]; simp) sk6
    (by rw [BufL.length_bset]; exact hI5.kl) (by simp; omega) (by omega)
  have hr6 : bget (g15 s5.r 6 (L.length + 2).toUInt64) 0 = i3.toUInt64 := by simp only [g15]; rw [p3 0 (by decide), hr5]
  -- else branch
  refine Reach.bind (IH i3 (by omega) (by omega) _ (L ++ [(5, bsize s5.o, 0)]) F (by simpa using hI6) hr6 (by simp; omega)) ?_
  rintro s7 ⟨ce, i4, Ee, hce, hI7, ho7, hr7, hi4, hd7⟩
  -- item 5: patch the end placeholder
  have hI7' : Inv K s7 (L ++ [(5, bsize s5.o, 0)]) (F ++ Ee.map Nat.toUInt64) := hI7
  refine Reach.step (live_of hI7' (by simp)) ?_
  obtain ⟨n7, c7, a7, -⟩ := top_item hI7'
  have hst7 : st s7 = ⟨s7.x, if g14 (bsize s5.o) (bsize s7.o) == 1 then g15 s7.r 6 L.length.toUInt64
      else g16 (g15 s7.r 6 L.length.toUInt64), bset s7.o (bsize s5.o) (g13 0 (bsize s5.o) (bsize s7.o)), s7.k, s7.t, s7.f⟩ := by
    rw [st_t5 s7 _ _ n7 c7 a7]
  rw [hst7]
  obtain ⟨w1, w2, w3⟩ := r6set s7.r hI7.rl L.length.toUInt64
  by_cases hg7 : ¬ (g14 (bsize s5.o) (bsize s7.o) == 1) = true
  · rw [if_neg hg7]; exact Reach.error (g16_err _ w1)
  rw [if_pos (Classical.not_not.mp hg7)]
  have e1 : bsize s5.o = (s.o.length + ca.length + cb.length + 5 + ct.length).toUInt64 :=
    ulen _ _ (by rw [hA]; simp [ifHd]; omega)
  have e2 : bsize s7.o = (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length).toUInt64 :=
    ulen _ _ (by rw [ho7]; simp [ifHd]; omega)
  have j2 : JOk (s.o.length + ca.length + cb.length + 5 + ct.length)
      (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length) := by
    unfold JOk; rw [← e1, ← e2]; simpa using Classical.not_not.mp hg7
  have hQ : (s.o.length + ca.length + cb.length + 5 + ct.length).toUInt64.toNat = ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: ct).length := by
    have hl : s5.o.length < 2 ^ 24 := hI5.ol
    have : s5.o.length = s.o.length + ca.length + cb.length + 5 + ct.length := by rw [hA]; simp [ifHd]; omega
    rw [u_toNat _ (by omega)]; simp [ifHd]; omega
  have ho8 : bset s7.o (bsize s5.o) (g13 0 (bsize s5.o) (bsize s7.o)) = s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce) := by
    rw [e1, e2, ho7, show ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])) ++ ce =
        ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: ct) ++ 0 :: ce by simp]
    rw [bset_mid _ _ _ _ _ hQ]
    simp only [jw, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  rw [ho8]
  by_cases hbig8 : 2 ^ 24 ≤ (s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)).length
  · exact Reach.toobig ⟨hbig8, by have := hI7.ol; rw [ho7] at this; simp [ifHd] at this ⊢; omega⟩
  have hI8 := inv_mk hI7' (g15 s7.r 6 L.length.toUInt64) s7.k
    (s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)) L (fun j a b => w3 j b) w1
    (by simp only [g15]; rw [w2]) (stk_pop hI7'.stk) hI7.kl (by omega) (by omega)
  refine Reach.done ⟨_, i4, [] ++ [] ++ [] ++ Ee, ?_, ?_, rfl, ?_, by omega, fun hd => ?_⟩
  · have hca' : CG K (L.length + 6) (i + 2) s.o.length ca i1 [] := by simpa using hca
    have hcb' : CG K (L.length + 5) i1 (s.o.length + ca.length) cb i2 [] := by
      have : s2.o.length = s.o.length + ca.length := by rw [ho2]; simp
      simpa [this] using hcb
    have hct' : CG K (L.length + 3) i2 (s.o.length + ca.length + cb.length + 5) ct i3 [] := by
      have : (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1) == 1) = true then g4 0 5 6 8 else g4 6 5 6 8)) 0).length =
          s.o.length + ca.length + cb.length + 5 := by rw [g30_eq, ho3']; simp [bpush]; omega
      simp only at hct; rw [this] at hct; simpa using hct
    have hce' : CG K (L.length + 1) i3 (s.o.length + ca.length + cb.length + 5 + ct.length + 1) ce i4 Ee := by
      have : (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])).length =
          s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by simp [ifHd]; omega
      simp only at hce; rw [this] at hce; simpa using hce
    exact .ite ht hb hca' hcb' hct' hce' j1 j2
  · simpa using hI8
  · simp only [g15]; rw [w3 0 (by decide), hr7]
  · obtain ⟨ee, r3e⟩ := hd7 (by simp; omega)
    subst ee
    refine ⟨rfl, ?_⟩
    simp only [g15]
    rw [w3 3 (by decide), r3e]; simp only [g15]
    rw [p3 3 (by decide), r3t]; simp only [g15]
    rw [q3 3 (by decide), r3b, r3a, hr3_1]

/-- the postcondition of n consecutive value visits -/
def SPost (K : Cx) (s0 : GS) (L : List Item) (F : List UInt64) (i n : Nat) (s' : GS) : Prop :=
  ∃ c i' E, CGs K L.length i s0.o.length n c i' E ∧ Inv K s' L (F ++ E.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ (i ≤ i' ∧ i' ≤ K.X.length + 3) ∧ (2 ≤ L.length → E = [] ∧ bget s'.r 3 = bget s0.r 3)

/-- n operand visits (pushed by g27) -/
theorem seq {K i0} (hV : ∀ j, i0 ≤ j → VS K j) : ∀ (n i : Nat) (s : GS) (L : List Item) (F : List UInt64), i0 ≤ i →
    i ≤ K.X.length + 3 → Inv K s (L ++ List.replicate n (1, 0, 0)) F → bget s.r 0 = i.toUInt64 →
    L.length + n + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach s (SPost K s L F i n)
  | 0, i, s, L, F, _, hiX, hI, hr0, _ => .done ⟨[], i, [], .nil, by simpa using hI, by simp, hr0, ⟨Nat.le_refl _, hiX⟩, fun _ => ⟨rfl, rfl⟩⟩
  | n + 1, i, s, L, F, hi, hiX, hI, hr0, hB => by
    have hI' : Inv K s ((L ++ List.replicate n (1, 0, 0)) ++ [(1, 0, 0)]) F := by
      rw [List.append_assoc, ← List.replicate_succ']; exact hI
    refine Reach.bind (hV i hi hiX s _ F hI' hr0 (by simp; omega)) ?_
    rintro s2 ⟨c, i1, E, hc, hI2, ho2, hr2, hi1, hd2⟩
    refine Reach.bind (seq hV n i1 s2 L (F ++ E.map Nat.toUInt64) (by omega) (by omega) hI2 hr2 (by omega)) ?_
    rintro s3 ⟨cs, i2, Es, hcs, hI3, ho3, hr3, hi2, hd3⟩
    refine Reach.done ⟨c ++ cs, i2, E ++ Es, ?_, by rw [List.map_append, ← List.append_assoc]; exact hI3,
      by rw [ho3, ho2, List.append_assoc], hr3, by omega, fun hd => ?_⟩
    · have hc' : CG K (L.length + n) i s.o.length c i1 E := by simpa using hc
      have hcs' : CGs K L.length i1 (s.o.length + c.length) n cs i2 Es := by
        have : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
        rw [← this]; exact hcs
      exact .cons hc' hcs'
    · obtain ⟨e1, r1⟩ := hd2 (by simp; omega)
      obtain ⟨e2, r2⟩ := hd3 hd
      exact ⟨by rw [e1, e2]; rfl, by rw [r2, r1]⟩

/-- PAIR -/
theorem v_pair {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 6) :
    VS K i := by
  intro hiX s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 6 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  rw [g36_pair _ _ _ _ (by rw [h0]; exact hx), h0, h6, hv1]
  by_cases hq' : ¬ tg K.X (i + 1) < 251
  · rw [if_neg hq']; exact Reach.error (g16_err _ hl6)
  have hq : tg K.X (i + 1) < 251 := Classical.not_not.mp hq'
  rw [if_pos hq]
  obtain ⟨qn, qe⟩ := u_small _ hq
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk1, kl1⟩ := stk_g27 256 s.k L (tg K.X (i + 1)).toNat (by omega) (stk_pop hI.stk) hI.kl (by omega)
  rw [qe] at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + tg K.X (i + 1)) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + tg K.X (i + 1)))
    _ s.o (L ++ List.replicate (tg K.X (i + 1)).toNat (1, 0, 0))
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; rw [← qe]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + tg K.X (i + 1))) 0 =
      (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  refine Reach.bind (seq (i0 := i + 2) (fun j hj => IH j (by omega)) _ (i + 2) _ L F (Nat.le_refl _) (by omega) hI1 hra (by omega)) ?_
  rintro s2 ⟨c, i2, E, hc, hI2, ho2, hr2, hi2, hd2⟩
  refine Reach.done ⟨c, i2, E, .pair ht hq hc, hI2, ho2, hr2, by omega, fun hd => ?_⟩
  obtain ⟨e, r3⟩ := hd2 hd
  refine ⟨e, ?_⟩
  rw [r3]; simp only [g15]
  rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]

theorem st_t7 (s : GS) (n D : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 7)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = D) (hD : D < bsize s.t) :
    st s = ⟨s.x, if g14 (bsize s.o) (bget s.t D) == 1 then g15 s.r 6 n else g16 (g15 s.r 6 n),
      bpush s.o (g13 1 (bsize s.o) (bget s.t D)), s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t7 _ _ _ _ _ _ hc, ha, hn, if_pos hD, g19_eq]

theorem st_t7_bad (s : GS) (n D : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 7)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = D) (hD : ¬ D < bsize s.t) :
    st s = ⟨s.x, g16 (g15 s.r 6 n), s.o, s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t7 _ _ _ _ _ _ hc, ha, hn, if_neg hD]

theorem st_t8 (s : GS) (n P : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 8)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = P) :
    st s = ⟨s.x, g15 s.r 6 n, g32 s.o P (bget (g15 s.r 6 n) 9), s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t8 _ _ _ _ _ _ hc, ha, hn]

/-- CALL -/
theorem v_call {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 8) :
    VS K i := by
  intro hiX s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 8 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have hv2 : bget s.x (i.toUInt64 + 2) = tg K.X (i + 2) := by rw [hI.x]; exact tg_u1 _ i 2 (by omega)
  rw [g36_call _ _ _ _ (by rw [h0]; exact hx), h0, h6, hv1, hv2]
  by_cases hq' : ¬ tg K.X (i + 2) < 251
  · rw [if_neg hq']; exact Reach.error (g16_err _ hl6)
  have hq : tg K.X (i + 2) < 251 := Classical.not_not.mp hq'
  rw [if_pos hq]
  obtain ⟨qn, qe⟩ := u_small _ hq
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk0, kl0⟩ := stk_push s.k L 7 (tg K.X (i + 1)) 0 (stk_pop hI.stk) hI.kl (by omega)
  have e1 : L.length.toUInt64 + 1 = (L ++ [(7, tg K.X (i + 1), 0)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
  have hkl := hI.kl
  obtain ⟨sk1, kl1⟩ := stk_g27 256 _ (L ++ [(7, tg K.X (i + 1), 0)]) (tg K.X (i + 2)).toNat (by omega) sk0 (by rw [kl0]; omega)
    (by simp; omega)
  rw [qe, ← e1] at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 3) (L.length.toUInt64 + 1 + tg K.X (i + 2)) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 1 + tg K.X (i + 2)))
    _ s.o (L ++ [(7, tg K.X (i + 1), 0)] ++ List.replicate (tg K.X (i + 2)).toNat (1, 0, 0))
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; rw [← qe]; simp [Nat.toUInt64, UInt64.ofNat_add]; ac_rfl) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 1 + tg K.X (i + 2))) 0 =
      (i + 3).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  refine Reach.bind (seq (i0 := i + 3) (fun j hj => IH j (by omega)) _ (i + 3) _ (L ++ [(7, tg K.X (i + 1), 0)]) F (Nat.le_refl _) (by omega)
    hI1 hra (by simp; omega)) ?_
  rintro s2 ⟨c, i2, E, hc, hI2, ho2, hr2, hi2, hd2⟩
  refine Reach.step (live_of hI2 (by simp)) ?_
  obtain ⟨n2, c2, a2, -⟩ := top_item hI2
  have ht2 : s2.t = K.T := hI2.t
  by_cases hD' : ¬ tg K.X (i + 1) < bsize s2.t
  · rw [st_t7_bad s2 _ _ n2 c2 a2 hD']
    obtain ⟨p1, -, -⟩ := r6set s2.r hI2.rl L.length.toUInt64
    exact Reach.error (g16_err _ p1)
  have hD : tg K.X (i + 1) < bsize s2.t := Classical.not_not.mp hD'
  rw [st_t7 s2 _ _ n2 c2 a2 hD]
  obtain ⟨p1, p2, p3⟩ := r6set s2.r hI2.rl L.length.toUInt64
  by_cases hg' : ¬ (g14 (bsize s2.o) (bget s2.t (tg K.X (i + 1))) == 1) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ p1)
  rw [if_pos (Classical.not_not.mp hg')]
  by_cases hbig : 2 ^ 24 ≤ (bpush s2.o (g13 1 (bsize s2.o) (bget s2.t (tg K.X (i + 1))))).length
  · exact Reach.toobig ⟨hbig, by have := hI2.ol; simp [bpush]; omega⟩
  have hI3 := inv_mk hI2 (g15 s2.r 6 L.length.toUInt64) s2.k (bpush s2.o (g13 1 (bsize s2.o) (bget s2.t (tg K.X (i + 1))))) L
    (fun j a b => p3 j b) p1 (by simp only [g15]; rw [p2]) (stk_pop hI2.stk) hI2.kl (by omega) (by omega)
  have hl2 : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
  have jc : g14 (s.o.length + c.length).toUInt64 (bget K.T (tg K.X (i + 1))) = 1 := by
    rw [← ulen _ _ hl2, ← ht2]; simpa using Classical.not_not.mp hg'
  refine Reach.done ⟨c ++ [g13 1 (s.o.length + c.length).toUInt64 (bget K.T (tg K.X (i + 1)))], i2, E, ?_, hI3, ?_, ?_, by omega,
    fun hd => ?_⟩
  · exact .call ht hq (by rw [← ht2]; exact hD) (by simpa using hc) jc
  · simp only; rw [bpush, ulen _ _ hl2, ho2, ht2]; simp
  · simp only [g15]; rw [p3 0 (by decide), hr2]
  · obtain ⟨e, r3⟩ := hd2 (by simp; omega)
    refine ⟨e, ?_⟩
    simp only [g15]; rw [p3 3 (by decide), r3]; simp only [g15]
    rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]

/-- PRIM -/
theorem v_prim {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 9) :
    VS K i := by
  intro hiX s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 9 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  by_cases hb' : ¬ tg K.X (i + 1) - 1 < 9
  · rw [g36_prim_bad _ _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb')]
    exact Reach.error (g16_err _ hl6)
  have hb : tg K.X (i + 1) - 1 < 9 := Classical.not_not.mp hb'
  rw [g36_prim _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb), h0, h6, hv1]
  have hq : g33 (tg K.X (i + 1)) < 251 := by
    have := g33_lt (tg K.X (i + 1)); rw [UInt64.lt_iff_toNat_lt] at this ⊢; simp at this ⊢; omega
  obtain ⟨qn, qe⟩ := u_small _ hq
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk0, kl0⟩ := stk_push s.k L 8 (tg K.X (i + 1)) 0 (stk_pop hI.stk) hI.kl (by omega)
  have e1 : L.length.toUInt64 + 1 = (L ++ [(8, tg K.X (i + 1), 0)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
  have hkl := hI.kl
  obtain ⟨sk1, kl1⟩ := stk_g27 256 _ (L ++ [(8, tg K.X (i + 1), 0)]) (g33 (tg K.X (i + 1))).toNat (by omega) sk0
    (by rw [kl0]; omega) (by simp; omega)
  rw [qe, ← e1] at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + 1 + g33 (tg K.X (i + 1))) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 1 + g33 (tg K.X (i + 1))))
    _ s.o (L ++ [(8, tg K.X (i + 1), 0)] ++ List.replicate (g33 (tg K.X (i + 1))).toNat (1, 0, 0))
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; rw [← qe]; simp [Nat.toUInt64, UInt64.ofNat_add]; ac_rfl) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 1 + g33 (tg K.X (i + 1)))) 0 =
      (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  refine Reach.bind (seq (i0 := i + 2) (fun j hj => IH j (by omega)) _ (i + 2) _ (L ++ [(8, tg K.X (i + 1), 0)]) F (Nat.le_refl _) (by omega)
    hI1 hra (by simp; omega)) ?_
  rintro s2 ⟨c, i2, E, hc, hI2, ho2, hr2, hi2, hd2⟩
  refine Reach.step (live_of hI2 (by simp)) ?_
  obtain ⟨n2, c2, a2, -⟩ := top_item hI2
  rw [st_t8 s2 _ _ n2 c2 a2]
  obtain ⟨p1, p2, p3⟩ := r6set s2.r hI2.rl L.length.toUInt64
  have hu : bget (g15 s2.r 6 L.length.toUInt64) 9 = K.u := by simp only [g15]; rw [p3 9 (by decide), hI2.r9]
  rw [hu]
  have e := pi_g32 (tg K.X (i + 1)) K.u s2.o
  simp only at e
  rw [e]
  by_cases hbig : 2 ^ 24 ≤ (s2.o ++ em (fun o => g32 o (tg K.X (i + 1)) K.u) s2.o.length).length
  · exact Reach.toobig ⟨hbig, by have := hI2.ol; have := em_le (fun o => g32 o (tg K.X (i + 1)) K.u) s2.o.length 64 (fun o => g32_len o _ _); simp; omega⟩
  have hI3 := inv_mk hI2 (g15 s2.r 6 L.length.toUInt64) s2.k (s2.o ++ em (fun o => g32 o (tg K.X (i + 1)) K.u) s2.o.length) L
    (fun j a b => p3 j b) p1 (by simp only [g15]; rw [p2]) (stk_pop hI2.stk) hI2.kl (by omega) (by omega)
  have hl2 : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
  refine Reach.done ⟨c ++ em (fun o => g32 o (tg K.X (i + 1)) K.u) (s.o.length + c.length), i2, E, ?_, hI3, ?_, ?_, by omega,
    fun hd => ?_⟩
  · exact .prim ht hb (by simpa using hc)
  · simp only; rw [hl2, ho2]; simp
  · simp only [g15]; rw [p3 0 (by decide), hr2]
  · obtain ⟨e, r3⟩ := hd2 (by simp; omega)
    refine ⟨e, ?_⟩
    simp only [g15]; rw [p3 3 (by decide), r3]; simp only [g15]
    rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]

theorem st_t9 (s : GS) (n : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 9) :
    st s = if 65535 < bget (g15 s.r 6 n) 8 then ⟨s.x, g16 (g15 s.r 6 n), s.o, s.k, s.t, s.f⟩ else
      ⟨s.x, g15 (g15 s.r 6 n) 8 (bget (g15 s.r 6 n) 8 + 1), bpush s.o 0, s.k, s.t, g17 s.f (bget (g15 s.r 6 n) 8) (bsize s.o)⟩ := by
  unfold st; rw [g37_t9 _ _ _ _ _ _ hc, hn]
  by_cases h : 65535 < bget (g15 s.r 6 n) 8
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- the tail-visit postcondition -/
def TPost (K : Cx) (hd : Nat) (s0 : GS) (L : List Item) (F : List UInt64) (i : Nat) (s' : GS) : Prop :=
  ∃ c i' E, CT K hd L.length i s0.o.length c i' E ∧ Inv K s' L (F ++ E.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ (i < i' ∧ i' ≤ K.X.length + 3) ∧ bget s'.r 3 = bget s0.r 3

/-- tail visit at AST word i, loop head hd -/
def TS (K : Cx) (hd i : Nat) : Prop := i ≤ K.X.length + 3 → ∀ s L F, 1 ≤ L.length → Inv K s (L ++ [(1, 1, 0)]) F → bget s.r 0 = i.toUInt64 →
  bget s.r 3 = hd.toUInt64 → L.length + 1 + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach s (TPost K hd s L F i)

/-- a value node in tail position: the value, then an exit placeholder recorded in f -/
theorem t_val {K hd i} (hX : K.X.length < 2 ^ 31) (hi : i ≤ K.X.length + 3) (hV : VS K i)
    (h4 : tg K.X i ≠ 4) (h5 : tg K.X i ≠ 5) (h11 : tg K.X i ≠ 11) : TS K hd i := by
  intro hiX s L F hL1 hI hr0 hr3 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = tg K.X i := by rw [hI.x, tg_u _ _ (by omega)]
  rw [g36_tval _ _ _ _ (by rw [h0, hx]; exact nt_tail _ h4 h5 h11), h0, h6]
  by_cases ha : (rngA (nt (bget s.x i.toUInt64)) (bget s.x (i.toUInt64 + 1)) == 0) = true
  · rw [if_pos ha]; exact Reach.error (g16_err _ hl6)
  rw [if_neg ha]
  have hLl := hI.Ll; simp at hLl
  have q1 : L.length.toUInt64 + 1 = (L ++ [(9, 0, 0)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
  obtain ⟨sk0, kl0⟩ := stk_push_at s.k L _ 9 0 0 rfl (stk_pop hI.stk) hI.kl (by omega)
  obtain ⟨sk1, kl1⟩ := stk_push_at _ _ _ 1 0 0 q1 sk0 kl0 (by simp; omega)
  obtain ⟨p1, p2, p3⟩ := r6set (bset s.r 6 L.length.toUInt64) hl6 (L.length.toUInt64 + 2)
  have hI1 := inv_mk hI (g15 (bset s.r 6 L.length.toUInt64) 6 (L.length.toUInt64 + 2)) _ s.o (L ++ [(9, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [p3 j b, rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)]) p1
    (by simp only [g15]; rw [p2]; simp [Nat.toUInt64, UInt64.ofNat_add]) (by simpa using sk1) kl1 (by simp; omega) hI.ol
  have hra : bget (g15 (bset s.r 6 L.length.toUInt64) 6 (L.length.toUInt64 + 2)) 0 = i.toUInt64 := by
    simp only [g15]; rw [p3 0 (by decide), h0]
  have hr31 : bget (g15 (bset s.r 6 L.length.toUInt64) 6 (L.length.toUInt64 + 2)) 3 = bget s.r 3 := by
    simp only [g15]; rw [p3 3 (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  refine Reach.bind (hV (by omega) _ (L ++ [(9, 0, 0)]) F (by simpa using hI1) hra (by simp; omega)) ?_
  rintro s2 ⟨c, i', E, hc, hI2, ho2, hr2, hi', hd2⟩
  obtain ⟨eE, r32⟩ := hd2 (by simp; omega)
  subst eE
  simp only [List.map_nil, List.append_nil] at hI2
  refine Reach.step (live_of hI2 (by simp)) ?_
  obtain ⟨n2, c2, -, -⟩ := top_item hI2
  rw [st_t9 s2 _ n2 c2]
  obtain ⟨w1, w2, w3⟩ := r6set s2.r hI2.rl L.length.toUInt64
  have hq : bget (g15 s2.r 6 L.length.toUInt64) 8 = F.length.toUInt64 := by simp only [g15]; rw [w3 8 (by decide), hI2.r8]
  rw [hq]
  have hfl := hI2.fx.1
  have hF : F.length ≤ 65536 := Nat.le_trans hfl hI2.fl
  by_cases hbigF : 65535 < F.length.toUInt64
  · rw [if_pos hbigF]; exact Reach.error (g16_err _ w1)
  rw [if_neg hbigF]
  have hF' : F.length ≤ 65535 := by
    have : ¬ (65535 : UInt64).toNat < F.length.toUInt64.toNat := fun h => hbigF (UInt64.lt_iff_toNat_lt.mpr h)
    rw [u_toNat _ (by omega)] at this; simp at this; omega
  by_cases hbig : 2 ^ 24 ≤ (bpush s2.o 0).length
  · exact Reach.toobig ⟨hbig, by have := hI2.ol; simp [bpush]; omega⟩
  obtain ⟨fx3, fl3⟩ := fx_push s2.f F (bsize s2.o) hI2.fx hF' hI2.fl
  have hr8 := rset2 _ hI2.rl 6 8 L.length.toUInt64 (F.length.toUInt64 + 1) (by decide) (by decide)
  have hI3 := inv_mk2 hI2 (g15 (g15 s2.r 6 L.length.toUInt64) 8 (F.length.toUInt64 + 1)) s2.k (bpush s2.o 0)
    (g17 s2.f F.length.toUInt64 (bsize s2.o)) L (F ++ [bsize s2.o])
    (fun j a b c => by simp only [g15]; rw [hr8, if_neg (Ne.symm c), if_neg (Ne.symm b)])
    (len2 _ hI2.rl _ _ _ _) (by simp only [g15]; rw [hr8, if_neg (by decide), if_pos rfl])
    (stk_pop hI2.stk) hI2.kl (by omega) fx3 (by simp only [g15]; rw [hr8, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) fl3
    (by omega)
  have hl2 : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
  refine Reach.done ⟨c ++ [0], i', [s.o.length + c.length], ?_, ?_, ?_, ?_, by omega, ?_⟩
  · exact .val h4 h5 h11 (by simpa using hc)
  · have : bsize s2.o = (s.o.length + c.length).toUInt64 := ulen _ _ hl2
    simp only [List.map_cons, List.map_nil]; rw [← this]; exact hI3
  · simp only; rw [bpush, ho2]; simp
  · simp only [g15]; rw [hr8, if_neg (by decide), if_neg (by decide), hr2]
  · simp only [g15]; rw [hr8, if_neg (by decide), if_neg (by decide), r32, hr31]

theorem st_t10 (s : GS) (n : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 10) :
    st s = ⟨s.x, if g14 (bsize (g26 256 (bget (g15 s.r 6 n) 1) 1 (bget (g15 s.r 6 n) 1 - 1) s.o)) (bget (g15 s.r 6 n) 3) == 1
        then g15 s.r 6 n else g16 (g15 s.r 6 n),
      bpush (g26 256 (bget (g15 s.r 6 n) 1) 1 (bget (g15 s.r 6 n) 1 - 1) s.o)
        (g13 0 (bsize (g26 256 (bget (g15 s.r 6 n) 1) 1 (bget (g15 s.r 6 n) 1 - 1) s.o)) (bget (g15 s.r 6 n) 3)),
      s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t10 _ _ _ _ _ _ hc, hn]

/-- CONTINUE (tail mode): the new state, stored into slots 1…p−1, then the jump to the loop head -/
theorem t_cont {K hd i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 11) :
    TS K hd i := by
  intro hiX s L F hL1 hI hr0 hr3 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 11 := by rw [hI.x, tg_u _ _ (by omega), ht]
  rw [g36_tcont _ _ _ _ (by rw [h0]; exact hx), h0, h6]
  have hLl := hI.Ll; simp at hLl
  have q1 : L.length.toUInt64 + 1 = (L ++ [(10, 0, 0)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
  obtain ⟨sk0, kl0⟩ := stk_push_at s.k L _ 10 0 0 rfl (stk_pop hI.stk) hI.kl (by omega)
  obtain ⟨sk1, kl1⟩ := stk_push_at _ _ _ 1 0 0 q1 sk0 kl0 (by simp; omega)
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 1) (L.length.toUInt64 + 2) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 1)) 6 (L.length.toUInt64 + 2)) _ s.o
    (L ++ [(10, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) (by simpa using sk1) kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 1)) 6 (L.length.toUInt64 + 2)) 0 = (i + 1).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have hr31 : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 1)) 6 (L.length.toUInt64 + 2)) 3 = bget s.r 3 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  refine Reach.bind (IH (i + 1) (by omega) (by omega) _ (L ++ [(10, 0, 0)]) F (by simpa using hI1) hra (by simp; omega)) ?_
  rintro s2 ⟨c, i', E, hc, hI2, ho2, hr2, hi', hd2⟩
  obtain ⟨eE, r32⟩ := hd2 (by simp; omega)
  subst eE
  simp only [List.map_nil, List.append_nil] at hI2
  refine Reach.step (live_of hI2 (by simp)) ?_
  obtain ⟨n2, c2, -, -⟩ := top_item hI2
  rw [st_t10 s2 _ n2 c2]
  obtain ⟨w1, w2, w3⟩ := r6set s2.r hI2.rl L.length.toUInt64
  have hp : bget (g15 s2.r 6 L.length.toUInt64) 1 = K.p := by simp only [g15]; rw [w3 1 (by decide), hI2.r1]
  have hh : bget (g15 s2.r 6 L.length.toUInt64) 3 = hd.toUInt64 := by
    simp only [g15]; rw [w3 3 (by decide), r32, hr31, hr3]
  rw [hp, hh]
  have e := pi_g26 256 K.p 1 (K.p - 1) s2.o
  rw [e]
  have hl2 : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
  have hb : bsize (s2.o ++ em (g26 256 K.p 1 (K.p - 1)) s2.o.length) =
      (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length).toUInt64 :=
    ulen _ _ (by simp [hl2])
  rw [hb]
  by_cases hg' : ¬ (g14 (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length).toUInt64
      hd.toUInt64 == 1) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ w1)
  rw [if_pos (Classical.not_not.mp hg')]
  by_cases hbig : 2 ^ 24 ≤ (bpush (s2.o ++ em (g26 256 K.p 1 (K.p - 1)) s2.o.length)
      (g13 0 (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length).toUInt64 hd.toUInt64)).length
  · exact Reach.toobig ⟨hbig, by have := hI2.ol; have := em_le (g26 256 K.p 1 (K.p - 1)) s2.o.length 768 (fun o => by have := g26_len 256 K.p 1 (K.p - 1) o; omega); simp [bpush]; omega⟩
  have hI3 := inv_mk hI2 (g15 s2.r 6 L.length.toUInt64) s2.k (bpush (s2.o ++ em (g26 256 K.p 1 (K.p - 1)) s2.o.length)
      (g13 0 (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length).toUInt64 hd.toUInt64))
    L (fun j a b => w3 j b) w1 (by simp only [g15]; rw [w2])
    (stk_pop hI2.stk) hI2.kl (by omega) (by omega)
  refine Reach.done ⟨c ++ em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length) ++
    [jw 0 (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length) hd], i', [], ?_, ?_, ?_, ?_,
    by omega, ?_⟩
  · exact .cont ht (by simpa using hc) (by unfold JOk; simpa using Classical.not_not.mp hg')
  · simpa using hI3
  · simp only; rw [bpush, hl2, ho2]; simp [jw]
  · simp only [g15]; rw [w3 0 (by decide), hr2]
  · simp only [g15]; rw [w3 3 (by decide), r32, hr31]

theorem t_if {K hd i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j)
    (IHT : ∀ j, i < j → TS K hd j) (ht : tg K.X i = 4) : TS K hd i := by
  intro hiX s L F hL1 hI hr0 hhd hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 4 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  by_cases hb' : ¬ tg K.X (i + 1) - 1 < 2
  · rw [g36_if_bad _ _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb')]
    exact Reach.error (g16_err _ hl6)
  have hb : tg K.X (i + 1) - 1 < 2 := Classical.not_not.mp hb'
  rw [g36_tif _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb), h0, h6, hv1]
  dsimp only
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk1, kl1⟩ := stk_push7 s.k L (5, 0, 0) (1, 1, 0) (4, 0, 0) (1, 1, 0) (3, (tg K.X (i + 1)), 0) (1, 0, 0) (1, 0, 0)
    (stk_pop hI.stk) hI.kl (by omega)
  simp only at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + 7) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) _ s.o
    (L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0), (3, (tg K.X (i + 1)), 0), (1, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) 0 = (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have hr3_1 : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) 3 = bget s.r 3 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  -- operand a
  refine Reach.bind (IH (i + 2) (by omega) (by omega) _ (L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0), (3, (tg K.X (i + 1)), 0), (1, 0, 0)]) F
    (by simpa using hI1) hra (by simp; omega)) ?_
  rintro s2 ⟨ca, i1, Ea, hca, hI2, ho2, hr2, hi1, hd2⟩
  obtain ⟨ea, r3a⟩ := hd2 (by simp)
  subst ea
  -- operand b
  refine Reach.bind (IH i1 (by omega) (by omega) s2 (L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0), (3, (tg K.X (i + 1)), 0)]) F
    (by simpa using hI2) hr2 (by simp; omega)) ?_
  rintro s3 ⟨cb, i2, Eb, hcb, hI3, ho3, hr3, hi2, hd3⟩
  obtain ⟨eb, r3b⟩ := hd3 (by simp)
  subst eb
  simp only [List.map_nil, List.append_nil] at hI3
  -- compare item
  have hI3' : Inv K s3 ((L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0)]) ++ [(3, (tg K.X (i + 1)), 0)]) F := by simpa using hI3
  refine Reach.step (live_of hI3' (by simp)) ?_
  obtain ⟨n3, c3, a3, -⟩ := top_item hI3'
  simp only [List.length_append, List.length_cons, List.length_nil] at n3
  have hidx : ((L.length + 4).toUInt64 - 2) * 3 + 1 = (3 * (L.length + 2) + 1).toUInt64 := by
    apply UInt64.toNat.inj; simp [Nat.toUInt64, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_add]; omega
  have hst : st s3 = ⟨s3.x, g15 s3.r 6 (L.length + 4).toUInt64, bpush (bpush (g30 s3.o 16)
      (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0,
      bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4), s3.t, s3.f⟩ := by
    unfold st; rw [g37_t3 _ _ _ _ _ _ c3, a3, n3, hidx]
  rw [hst]
  have ho3' : s3.o = s.o ++ ca ++ cb := by rw [ho3, ho2]
  by_cases hbig : 2 ^ 24 ≤ (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0).length
  · exact Reach.toobig ⟨hbig, by have := hI3.ol; simp [g30_eq, bpush]; omega⟩
  obtain ⟨q1, q2, q3⟩ := r6set s3.r hI3.rl (L.length + 4).toUInt64
  have sk4 : Stk (bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4))
      (L ++ [(5, 0, 0), (1, 1, 0), (4, bsize s3.o + 4, 0), (1, 1, 0)]) := by
    have hp := stk_pop hI3'.stk
    have := stk_set hp (L.length + 2) (4, 0, 0) (by simp) (bsize s3.o + 4)
    simp only [bset]
    rw [u_toNat _ (by omega)]
    have e : (L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0)]).set (L.length + 2) ((4 : UInt64), bsize s3.o + 4, (0 : UInt64)) =
        L ++ [(5, 0, 0), (1, 1, 0), (4, bsize s3.o + 4, 0), (1, 1, 0)] := by
      rw [List.set_append_right _ _ (by omega)]; simp
    rw [← e]; simpa using this
  have hI4 := inv_mk hI3' (g15 s3.r 6 (L.length + 4).toUInt64) (bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4))
    (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0)
    (L ++ [(5, 0, 0), (1, 1, 0), (4, bsize s3.o + 4, 0), (1, 1, 0)])
    (fun j a b => q3 j b) q1 (by simp only [g15]; rw [q2]; simp) sk4 (by rw [BufL.length_bset]; exact hI3.kl) (by simp; omega) (by omega)
  have hr4 : bget (g15 s3.r 6 (L.length + 4).toUInt64) 0 = i2.toUInt64 := by simp only [g15]; rw [q3 0 (by decide), hr3]
  -- then branch
  refine Reach.bind (IHT i2 (by omega) (by omega) _ (L ++ [(5, 0, 0), (1, 1, 0), (4, bsize s3.o + 4, 0)]) F (by simp)
    (by simpa using hI4) hr4 (by simp only [g15]; rw [q3 3 (by decide), r3b, r3a, hr3_1, hhd]) (by simp; omega)) ?_
  rintro s5 ⟨ct, i3, Et, hct, hI5, ho5, hr5, hi3, r3t⟩
  -- item 4: patch the compare's jump to here + 1, leave the end placeholder
  have hI5' : Inv K s5 ((L ++ [(5, 0, 0), (1, 1, 0)]) ++ [(4, bsize s3.o + 4, 0)]) (F ++ Et.map Nat.toUInt64) := by simpa using hI5
  refine Reach.step (live_of hI5' (by simp)) ?_
  obtain ⟨n5, c5, a5, -⟩ := top_item hI5'
  simp only [List.length_append, List.length_cons, List.length_nil] at n5
  have hidx5 : ((L.length + 2).toUInt64 - 2) * 3 + 1 = (3 * L.length + 1).toUInt64 := by
    apply UInt64.toNat.inj; simp [Nat.toUInt64, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_add]; omega
  have hst5 : st s5 = ⟨s5.x, if g14 (bsize s3.o + 4) (bsize (bpush s5.o 0)) == 1 then g15 s5.r 6 (L.length + 2).toUInt64
      else g16 (g15 s5.r 6 (L.length + 2).toUInt64),
      bset (bpush s5.o 0) (bsize s3.o + 4) (g13 0 (bsize s3.o + 4) (bsize (bpush s5.o 0))),
      bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o), s5.t, s5.f⟩ := by
    rw [st_t4 s5 _ _ n5 c5 a5, hidx5]
  rw [hst5]
  obtain ⟨p1, p2, p3⟩ := r6set s5.r hI5.rl (L.length + 2).toUInt64
  by_cases hg' : ¬ (g14 (bsize s3.o + 4) (bsize (bpush s5.o 0)) == 1) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ p1)
  have hg1 := Classical.not_not.mp hg'
  rw [if_pos hg1]
  -- the code so far
  have hA : s5.o = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++ 0 :: ct := by
    rw [ho5, ho3']; simp [g30_eq, bpush, ifHd, List.append_assoc]
  have hl3 : s3.o.length = s.o.length + ca.length + cb.length := by rw [ho3']; simp [Nat.add_assoc]
  have hol3 := hI3.ol
  have hpj : bsize s3.o + 4 = (s.o.length + ca.length + cb.length + 4).toUInt64 := by
    rw [ulen _ _ hl3]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have j1 : JOk (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) := by
    have hl5 : (bpush s5.o 0).length = s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by
      rw [bpush, hA]; simp [ifHd]; omega
    unfold JOk; rw [← hpj, ← ulen _ _ hl5]; simpa using hg1
  have hP : (bsize s3.o + 4).toNat = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))).length := by
    rw [hpj, u_toNat _ (by omega)]; simp [ifHd]; omega
  have ho6 : bset (bpush s5.o 0) (bsize s3.o + 4) (g13 0 (bsize s3.o + 4) (bsize (bpush s5.o 0))) =
      (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0]) := by
    have hl5 : (bpush s5.o 0).length = s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by
      rw [bpush, hA]; simp [ifHd]; omega
    rw [ulen _ _ hl5, show bpush s5.o 0 = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++ 0 :: (ct ++ [0]) by rw [bpush, hA]; simp,
      bset_mid _ _ _ _ _ hP, jw, ← hpj]
  rw [ho6]
  by_cases hbig6 : 2 ^ 24 ≤ ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])).length
  · exact Reach.toobig ⟨hbig6, by have := hI5.ol; rw [hA] at this; simp [ifHd] at this ⊢; omega⟩
  have sk6 : Stk (bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o)) (L ++ [(5, bsize s5.o, 0), (1, 1, 0)]) := by
    have hp := stk_pop hI5'.stk
    have := stk_set hp L.length (5, 0, 0) (by simp) (bsize s5.o)
    simp only [bset]
    rw [u_toNat _ (by omega)]
    have e : (L ++ [(5, 0, 0), (1, 1, 0)]).set L.length ((5 : UInt64), bsize s5.o, (0 : UInt64)) =
        L ++ [(5, bsize s5.o, 0), (1, 1, 0)] := by
      rw [List.set_append_right _ _ (by omega)]; simp
    rw [← e]; simpa using this
  have hI6 := inv_mk hI5' (g15 s5.r 6 (L.length + 2).toUInt64) (bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o))
    ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0]))
    (L ++ [(5, bsize s5.o, 0), (1, 1, 0)]) (fun j a b => p3 j b) p1 (by simp only [g15]; rw [p2]; simp) sk6
    (by rw [BufL.length_bset]; exact hI5.kl) (by simp; omega) (by omega)
  have hr6 : bget (g15 s5.r 6 (L.length + 2).toUInt64) 0 = i3.toUInt64 := by simp only [g15]; rw [p3 0 (by decide), hr5]
  -- else branch
  refine Reach.bind (IHT i3 (by omega) (by omega) _ (L ++ [(5, bsize s5.o, 0)]) (F ++ Et.map Nat.toUInt64) (by simp) (by simpa using hI6) hr6
    (by simp only [g15]; rw [p3 3 (by decide), r3t]; simp only [g15]; rw [q3 3 (by decide), r3b, r3a, hr3_1, hhd])
    (by simp; omega)) ?_
  rintro s7 ⟨ce, i4, Ee, hce, hI7, ho7, hr7, hi4, r3e⟩
  -- item 5: patch the end placeholder
  have hI7' : Inv K s7 (L ++ [(5, bsize s5.o, 0)]) (F ++ Et.map Nat.toUInt64 ++ Ee.map Nat.toUInt64) := hI7
  refine Reach.step (live_of hI7' (by simp)) ?_
  obtain ⟨n7, c7, a7, -⟩ := top_item hI7'
  have hst7 : st s7 = ⟨s7.x, if g14 (bsize s5.o) (bsize s7.o) == 1 then g15 s7.r 6 L.length.toUInt64
      else g16 (g15 s7.r 6 L.length.toUInt64), bset s7.o (bsize s5.o) (g13 0 (bsize s5.o) (bsize s7.o)), s7.k, s7.t, s7.f⟩ := by
    rw [st_t5 s7 _ _ n7 c7 a7]
  rw [hst7]
  obtain ⟨w1, w2, w3⟩ := r6set s7.r hI7.rl L.length.toUInt64
  by_cases hg7 : ¬ (g14 (bsize s5.o) (bsize s7.o) == 1) = true
  · rw [if_neg hg7]; exact Reach.error (g16_err _ w1)
  rw [if_pos (Classical.not_not.mp hg7)]
  have e1 : bsize s5.o = (s.o.length + ca.length + cb.length + 5 + ct.length).toUInt64 :=
    ulen _ _ (by rw [hA]; simp [ifHd]; omega)
  have e2 : bsize s7.o = (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length).toUInt64 :=
    ulen _ _ (by rw [ho7]; simp [ifHd]; omega)
  have j2 : JOk (s.o.length + ca.length + cb.length + 5 + ct.length)
      (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length) := by
    unfold JOk; rw [← e1, ← e2]; simpa using Classical.not_not.mp hg7
  have hQ : (s.o.length + ca.length + cb.length + 5 + ct.length).toUInt64.toNat = ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: ct).length := by
    have hl : s5.o.length < 2 ^ 24 := hI5.ol
    have : s5.o.length = s.o.length + ca.length + cb.length + 5 + ct.length := by rw [hA]; simp [ifHd]; omega
    rw [u_toNat _ (by omega)]; simp [ifHd]; omega
  have ho8 : bset s7.o (bsize s5.o) (g13 0 (bsize s5.o) (bsize s7.o)) = s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce) := by
    rw [e1, e2, ho7, show ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])) ++ ce =
        ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: ct) ++ 0 :: ce by simp]
    rw [bset_mid _ _ _ _ _ hQ]
    simp only [jw, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  rw [ho8]
  by_cases hbig8 : 2 ^ 24 ≤ (s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)).length
  · exact Reach.toobig ⟨hbig8, by have := hI7.ol; rw [ho7] at this; simp [ifHd] at this ⊢; omega⟩
  have hI8 := inv_mk hI7' (g15 s7.r 6 L.length.toUInt64) s7.k
    (s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)) L (fun j a b => w3 j b) w1
    (by simp only [g15]; rw [w2]) (stk_pop hI7'.stk) hI7.kl (by omega) (by omega)
  refine Reach.done ⟨_, i4, [] ++ [] ++ Et ++ Ee, ?_, ?_, rfl, ?_, by omega, ?_⟩
  · have hca' : CG K (L.length + 6) (i + 2) s.o.length ca i1 [] := by simpa using hca
    have hcb' : CG K (L.length + 5) i1 (s.o.length + ca.length) cb i2 [] := by
      have : s2.o.length = s.o.length + ca.length := by rw [ho2]; simp
      simpa [this] using hcb
    have hct' : CT K hd (L.length + 3) i2 (s.o.length + ca.length + cb.length + 5) ct i3 Et := by
      have : (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1) == 1) = true then g4 0 5 6 8 else g4 6 5 6 8)) 0).length =
          s.o.length + ca.length + cb.length + 5 := by rw [g30_eq, ho3']; simp [bpush]; omega
      simp only at hct; rw [this] at hct; simpa using hct
    have hce' : CT K hd (L.length + 1) i3 (s.o.length + ca.length + cb.length + 5 + ct.length + 1) ce i4 Ee := by
      have : (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])).length =
          s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by simp [ifHd]; omega
      simp only at hce; rw [this] at hce; simpa using hce
    exact .ite ht hb hca' hcb' hct' hce' j1 j2
  · simpa using hI8
  · simp only [g15]; rw [w3 0 (by decide), hr7]
  · simp only [g15]
    rw [w3 3 (by decide), r3e]; simp only [g15]
    rw [p3 3 (by decide), r3t]; simp only [g15]
    rw [q3 3 (by decide), r3b, r3a, hr3_1]

theorem t_let {K hd i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j)
    (IHT : ∀ j, i < j → TS K hd j) (ht : tg K.X i = 5) : TS K hd i := by
  intro hiX s L F hL1 hI hr0 hhd hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have h7 : bget (bset s.r 6 L.length.toUInt64) 7 = K.ns := by
    rw [rget _ hI.rl 6 7 _ (by decide), if_neg (by decide), hI.r7]
  have hx : bget s.x i.toUInt64 = 5 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have hv2 : bget s.x (i.toUInt64 + 2) = tg K.X (i + 2) := by rw [hI.x]; exact tg_u1 _ i 2 (by omega)
  rw [g36_tlet _ _ _ _ (by rw [h0]; exact hx), h0, h6, hv1, hv2, g43_ok _ _ _ _ h7]
  by_cases hs : SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2))
  · have hs' : tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2) := hs
    rw [if_pos hs']
    simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false]
    have hLl := hI.Ll; simp at hLl
    have hsk := stk_pop hI.stk
    obtain ⟨sk1, kl1⟩ := stk_push3 s.k L (1, 1, 0) (6, tg K.X (i + 1), tg K.X (i + 2)) (1, 0, 0) hsk hI.kl (by omega)
    simp only at sk1 kl1
    have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 3) (L.length.toUInt64 + 3) (by decide) (by decide)
    have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 3)) _ s.o
      (L ++ [(1, 1, 0), (6, tg K.X (i + 1), tg K.X (i + 2)), (1, 0, 0)])
      (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
      (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
      (by simp; omega) hI.ol
    have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 3)) 0 = (i + 3).toUInt64 := by
      simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
    refine Reach.bind (IH (i + 3) (by omega) (by omega) _ (L ++ [(1, 1, 0), (6, tg K.X (i + 1), tg K.X (i + 2))]) F (by simpa using hI1) hra
      (by simp; omega)) ?_
    rintro s2 ⟨cv, i1, Ev, hcv, hI2, ho2, hr2, hi1, hd2⟩
    -- the slot-pop item
    have hI2' : Inv K s2 ((L ++ [(1, 1, 0)]) ++ [(6, tg K.X (i + 1), tg K.X (i + 2))]) (F ++ Ev.map Nat.toUInt64) := by simpa using hI2
    refine Reach.step (live_of hI2' (by simp)) ?_
    obtain ⟨n2, c2, a2, b2⟩ := top_item hI2'
    have hp2 : bget (g15 s2.r 6 (L ++ [(1, 1, 0)]).length.toUInt64) 1 = K.p := by
      simp only [g15]; rw [rget _ hI2.rl 6 1 _ (by decide), if_neg (by decide), hI2.r1]
    have hst : st s2 = ⟨s2.x, g15 s2.r 6 (L ++ [(1, 1, 0)]).length.toUInt64,
        g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s2.o, s2.k, s2.t, s2.f⟩ := by
      unfold st; rw [g37_t6 _ _ _ _ _ _ c2, a2, b2, n2, hp2]
    rw [hst]
    have e := pi_g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s2.o
    rw [e]
    by_cases hbig : 2 ^ 24 ≤ (s2.o ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length).length
    · exact Reach.toobig ⟨hbig, by have := hI2.ol; have := em_le (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length 768 (fun o => by have := g26_len 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) o; omega); simp; omega⟩
    have hI3 := inv_mk hI2' (g15 s2.r 6 (L ++ [(1, 1, 0)]).length.toUInt64) s2.k
      (s2.o ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length) (L ++ [(1, 1, 0)])
      (fun j a b => by simp only [g15]; rw [rget _ hI2.rl 6 j _ (by decide), if_neg (Ne.symm b)])
      (by simp only [g15]; rw [BufL.length_bset]; exact hI2.rl)
      (by simp only [g15]; rw [rget _ hI2.rl 6 6 _ (by decide), if_pos rfl]) (stk_pop hI2'.stk) hI2.kl (by simp; omega) (by omega)
    have hr3 : bget (g15 s2.r 6 (L ++ [(1, 1, 0)]).length.toUInt64) 0 = i1.toUInt64 := by
      simp only [g15]; rw [rget _ hI2.rl 6 0 _ (by decide), if_neg (by decide), hr2]
    obtain ⟨ev, r3a⟩ := hd2 (by simp)
    refine Reach.bind (IHT i1 (by omega) (by omega) _ L (F ++ Ev.map Nat.toUInt64) hL1 hI3 hr3 (by
      simp only [g15]; rw [rget _ hI2.rl 6 3 _ (by decide), if_neg (by decide), r3a]
      simp only [g15]
      rw [rset2 _ hl6 0 6 _ _ (by decide) (by decide), if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide),
        if_neg (by decide), hhd]) (by omega)) ?_
    rintro s4 ⟨cb, i2, Eb, hcb, hI4, ho4, hr4, hi2, r3b⟩
    have hem : s2.o.length = s.o.length + cv.length := by rw [ho2]; simp
    refine Reach.done ⟨cv ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (s.o.length + cv.length) ++ cb, i2, Ev ++ Eb,
      ?_, ?_, ?_, hr4, by omega, ?_⟩
    · have hcv' : CG K (L.length + 2) (i + 3) s.o.length cv i1 Ev := by simpa using hcv
      have hcb' : CT K hd L.length i1 (s.o.length + cv.length +
          (em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (s.o.length + cv.length)).length) cb i2 Eb := by
        simpa [hem, Nat.add_assoc] using hcb
      exact .lett ht hs hcv' hcb'
    · rw [List.map_append, ← List.append_assoc]; exact hI4
    · rw [ho4, ho2]; simp [hem, List.append_assoc]
    · rw [r3b]; simp only [g15]; rw [rget _ hI2.rl 6 3 _ (by decide), if_neg (by decide), r3a]
      simp only [g15]
      rw [rset2 _ hl6 0 6 _ _ (by decide) (by decide), if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  · have hs' : ¬ (tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2)) := hs
    rw [if_neg hs']
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    exact Reach.error (g16_err _ hl6)

theorem st_t11 (s : GS) (n Z : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 11)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = Z) :
    st s = ⟨s.x, if g14 Z (bsize s.o) == 1 then g15 s.r 6 n else g16 (g15 s.r 6 n),
      bpush (bpush (bset s.o Z (g13 0 Z (bsize s.o))) (g10 5 5 g_901)) (g12 5 8 (g24 (bget (g15 s.r 6 n) 1) 0)), s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t11 _ _ _ _ _ _ hc, ha, hn]

/-- LOOP: only as the def body (one item below, the ENDDEF) -/
theorem v_loop {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (ht : tg K.X i = 10)
    (IHT : ∀ hd j, i < j → TS K hd j) : VS K i := by
  intro hiX s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have h1 : bget (bset s.r 6 L.length.toUInt64) 1 = K.p := by
    rw [rget _ hI.rl 6 1 _ (by decide), if_neg (by decide), hI.r1]
  have hx : bget s.x i.toUInt64 = 10 := by rw [hI.x, tg_u _ _ (by omega), ht]
  rw [g36_loop _ _ _ _ (by rw [h0]; exact hx), h0, h6, h1]
  have hLl := hI.Ll; simp at hLl
  by_cases hL : L.length ≠ 1
  · have : ¬ (L.length.toUInt64 == 1) = true := by
      simp; intro h; have := congrArg UInt64.toNat h; rw [u_toNat _ (by omega)] at this; exact hL this
    rw [if_neg this]; exact Reach.error (g16_err _ hl6)
  have hL1 : L.length = 1 := Classical.not_not.mp hL
  rw [if_pos (by rw [hL1]; rfl)]
  -- the head
  obtain ⟨sk1, kl1⟩ := stk_push3 s.k L (1, 1, 0) (11, bsize s.o + 2, 0) (1, 1, 0) (stk_pop hI.stk) hI.kl (by omega)
  simp only at sk1 kl1
  have hO1 : bpush (bpush (bpush s.o (g11 5 8 (g24 K.p 0))) (g4 0 5 0 8)) 0 = (s.o ++ lpHd K.p) ++ [0] := by
    simp [bpush, lpHd]
  rw [hO1]
  by_cases hbig : 2 ^ 24 ≤ ((s.o ++ lpHd K.p) ++ [0]).length
  · exact Reach.toobig ⟨hbig, by have := hI.ol; simp [lpHd]; omega⟩
  have hr3 : ∀ j : UInt64, bget (g15 (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 1)) 3 (bsize s.o)) 6
      (L.length.toUInt64 + 3)) j = if 6 = j then L.length.toUInt64 + 3 else if 3 = j then bsize s.o else
        if 0 = j then i.toUInt64 + 1 else bget (bset s.r 6 L.length.toUInt64) j := by
    intro j; simp only [g15]
    rw [rget _ (len2 _ hl6 _ _ _ _) 6 j _ (by decide), rset2 _ hl6 0 3 _ _ (by decide) (by decide)]
  have hI1 := inv_mk3 hI (g15 (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 1)) 3 (bsize s.o)) 6 (L.length.toUInt64 + 3))
    _ ((s.o ++ lpHd K.p) ++ [0]) (L ++ [(1, 1, 0), (11, bsize s.o + 2, 0), (1, 1, 0)])
    (fun j a b c => by rw [hr3, if_neg (Ne.symm c), if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide),
      if_neg (Ne.symm c)])
    (by simp only [g15]; rw [BufL.length_bset]; exact len2 _ hl6 _ _ _ _) (by rw [hr3, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add])
    sk1 kl1 (by simp; omega) (by omega)
  -- the zero arm (tail mode, head = h)
  refine Reach.bind (IHT s.o.length (i + 1) (by omega) (by omega) _ (L ++ [(1, 1, 0), (11, bsize s.o + 2, 0)]) F (by simp)
    (by simpa using hI1) (by rw [hr3, if_neg (by decide), if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add])
    (by rw [hr3, if_neg (by decide), if_pos rfl]; rfl) (by simp; omega)) ?_
  rintro s2 ⟨cz, i1, Ez, hcz, hI2, ho2, hr2, hi1, r3z⟩
  -- item 11: patch the head's jump to here, decrement the fuel
  have hI2' : Inv K s2 ((L ++ [(1, 1, 0)]) ++ [(11, bsize s.o + 2, 0)]) (F ++ Ez.map Nat.toUInt64) := by simpa using hI2
  refine Reach.step (live_of hI2' (by simp)) ?_
  obtain ⟨n2, c2, a2, -⟩ := top_item hI2'
  rw [st_t11 s2 _ _ n2 c2 a2]
  obtain ⟨w1, w2, w3⟩ := r6set s2.r hI2.rl (L ++ [(1, 1, 0)]).length.toUInt64
  by_cases hg' : ¬ (g14 (bsize s.o + 2) (bsize s2.o) == 1) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ w1)
  rw [if_pos (Classical.not_not.mp hg')]
  have hp2 : bget (g15 s2.r 6 (L ++ [(1, 1, 0)]).length.toUInt64) 1 = K.p := by simp only [g15]; rw [w3 1 (by decide), hI2.r1]
  rw [hp2]
  have hol := hI.ol
  have hP : (bsize s.o + 2).toNat = (s.o ++ lpHd K.p).length := by
    rw [bsize_u, show s.o.length.toUInt64 + 2 = (s.o.length + 2).toUInt64 by simp [Nat.toUInt64, UInt64.ofNat_add],
      u_toNat _ (by omega)]; simp [lpHd]
  have hl2 : s2.o.length = s.o.length + 3 + cz.length := by rw [ho2]; simp [lpHd]; omega
  have ho3 : bpush (bpush (bset s2.o (bsize s.o + 2) (g13 0 (bsize s.o + 2) (bsize s2.o))) (g10 5 5 g_901)) (g12 5 8 (g24 K.p 0)) =
      s.o ++ (lpHd K.p ++ [jw 0 (s.o.length + 2) (s.o.length + 3 + cz.length)] ++ cz ++ lpDec K.p) := by
    rw [ulen _ _ hl2, ho2, show (s.o ++ lpHd K.p) ++ [0] ++ cz = (s.o ++ lpHd K.p) ++ 0 :: cz by simp, bset_mid _ _ _ _ _ hP]
    simp [bpush, jw, lpDec, bsize_u, Nat.toUInt64, UInt64.ofNat_add]
  rw [ho3]
  by_cases hbig3 : 2 ^ 24 ≤ (s.o ++ (lpHd K.p ++ [jw 0 (s.o.length + 2) (s.o.length + 3 + cz.length)] ++ cz ++ lpDec K.p)).length
  · exact Reach.toobig ⟨hbig3, by have := hI2.ol; rw [hl2] at this; simp [lpHd, lpDec]; omega⟩
  have hI3 := inv_mk hI2' (g15 s2.r 6 (L ++ [((1 : UInt64), (1 : UInt64), (0 : UInt64))]).length.toUInt64) s2.k
    (s.o ++ (lpHd K.p ++ [jw 0 (s.o.length + 2) (s.o.length + 3 + cz.length)] ++ cz ++ lpDec K.p)) (L ++ [(1, 1, 0)])
    (fun j a b => by simp only [g15]; exact w3 j b) (by simp only [g15]; exact w1) (by simp only [g15]; rw [w2]) (stk_pop hI2'.stk) hI2.kl (by simp; omega) (by omega)
  -- the step arm
  refine Reach.bind (IHT s.o.length i1 (by omega) (by omega) _ L (F ++ Ez.map Nat.toUInt64) (by omega) hI3
    (by simp only [g15]; rw [w3 0 (by decide), hr2])
    (by simp only [g15]; rw [w3 3 (by decide), r3z, hr3, if_neg (by decide), if_pos rfl]; rfl) (by omega)) ?_
  rintro s4 ⟨cs, i2, Es, hcs, hI4, ho4, hr4, hi2, r3s⟩
  refine Reach.done ⟨lpHd K.p ++ [jw 0 (s.o.length + 2) (s.o.length + 3 + cz.length)] ++ cz ++ lpDec K.p ++ cs, i2, Ez ++ Es,
    ?_, ?_, ?_, hr4, by omega, fun hd => absurd hd (by omega)⟩
  · rw [hL1]
    have hcz' : CT K s.o.length 3 (i + 1) (s.o.length + 3) cz i1 Ez := by
      have : ((s.o ++ lpHd K.p) ++ [0]).length = s.o.length + 3 := by simp [lpHd]
      simp only at hcz; rw [this] at hcz; simpa [hL1] using hcz
    have hcs' : CT K s.o.length 1 i1 (s.o.length + 3 + cz.length + 2) cs i2 Es := by
      have : (s.o ++ (lpHd K.p ++ [jw 0 (s.o.length + 2) (s.o.length + 3 + cz.length)] ++ cz ++ lpDec K.p)).length =
          s.o.length + 3 + cz.length + 2 := by simp [lpHd, lpDec]; omega
      simp only at hcs; rw [this] at hcs; simpa [hL1] using hcs
    refine .loop ht hcz' hcs' ?_
    unfold JOk
    rw [show (s.o.length + 2).toUInt64 = bsize s.o + 2 by simp [bsize_u, Nat.toUInt64, UInt64.ofNat_add], ← ulen _ _ hl2]
    simpa using Classical.not_not.mp hg'
  · rw [List.map_append, ← List.append_assoc]; exact hI4
  · rw [ho4]; simp [List.append_assoc]

/-- a value visit of an invalid tag (0, 7, CONTINUE, ≥ 12) is an error -/
theorem v_bad {K i} (hX : K.X.length < 2 ^ 31) (hc : ∀ v : Nat, 1 ≤ v → v ≤ 9 → tg K.X i ≠ (if v < 7 then v else v + 1).toUInt64) :
    VS K i := by
  intro hiX s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, -⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = tg K.X i := by rw [hI.x, tg_u _ _ (by omega)]
  have hn : ∀ v : Nat, 1 ≤ v → v ≤ 9 → nt (tg K.X i) ≠ v.toUInt64 := fun v h1 h2 h => hc v h1 h2 (nt_val _ v ⟨h1, h2⟩ h)
  rw [g36_bad _ _ _ _ (by rw [h0, hx]; exact ⟨hn 1 (by omega) (by omega), hn 2 (by omega) (by omega), hn 3 (by omega) (by omega),
    hn 4 (by omega) (by omega), hn 5 (by omega) (by omega), hn 6 (by omega) (by omega), hn 7 (by omega) (by omega),
    hn 8 (by omega) (by omega), hn 9 (by omega) (by omega)⟩)]
  exact Reach.error (g16_err _ hl6)

/-- **the g39 visit invariant**: from any state with a visit item on top, Gen's main loop either fails (error / code
too big) or finishes that node, having emitted exactly the reference code (CG / CT) -/
theorem visit_all (K : Cx) (hX : K.X.length < 2 ^ 31) (i : Nat) : VS K i ∧ ∀ hd, TS K hd i := by
  have IHa : ∀ j, i < j → VS K j ∧ ∀ hd, TS K hd j := fun j hj => by
    by_cases hb : j ≤ K.X.length + 3
    · exact visit_all K hX j
    · exact ⟨fun h => absurd h hb, fun _ h => absurd h hb⟩
  have IH : ∀ j, i < j → VS K j := fun j hj => (IHa j hj).1
  have IHT : ∀ hd j, i < j → TS K hd j := fun hd j hj => (IHa j hj).2 hd
  have hV : VS K i := by
    by_cases h1 : tg K.X i = 1
    · intro hiX s L F hI hr0 hB; exact v_const hI hr0 (by have := tg_lt _ _ (by rw [h1]; decide); omega) (tg_lt _ _ (by rw [h1]; decide)) h1
    by_cases h2 : tg K.X i = 2
    · intro hiX s L F hI hr0 hB; exact v_local hI hr0 (by have := tg_lt _ _ (by rw [h2]; decide); omega) (tg_lt _ _ (by rw [h2]; decide)) h2
    by_cases h3 : tg K.X i = 3
    · exact v_bin hX (tg_lt _ _ (by rw [h3]; decide)) IH h3
    by_cases h4 : tg K.X i = 4
    · exact v_if hX (tg_lt _ _ (by rw [h4]; decide)) IH h4
    by_cases h5 : tg K.X i = 5
    · exact v_let hX (tg_lt _ _ (by rw [h5]; decide)) IH h5
    by_cases h6 : tg K.X i = 6
    · exact v_pair hX (tg_lt _ _ (by rw [h6]; decide)) IH h6
    by_cases h8 : tg K.X i = 8
    · exact v_call hX (tg_lt _ _ (by rw [h8]; decide)) IH h8
    by_cases h9 : tg K.X i = 9
    · exact v_prim hX (tg_lt _ _ (by rw [h9]; decide)) IH h9
    by_cases h10 : tg K.X i = 10
    · exact v_loop hX (tg_lt _ _ (by rw [h10]; decide)) h10 IHT
    refine v_bad hX fun v hv1 hv2 h => ?_
    rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
    · exact h5 h
    · exact h6 h
    · exact h8 h
    · exact h9 h
    · exact h10 h
  refine ⟨hV, fun hd => ?_⟩
  by_cases h4 : tg K.X i = 4
  · exact t_if hX (tg_lt _ _ (by rw [h4]; decide)) IH (IHT hd) h4
  by_cases h5 : tg K.X i = 5
  · exact t_let hX (tg_lt _ _ (by rw [h5]; decide)) IH (IHT hd) h5
  by_cases h11 : tg K.X i = 11
  · exact t_cont hX (tg_lt _ _ (by rw [h11]; decide)) IH h11
  intro hiX
  exact t_val hX hiX hV h4 h5 h11 hiX
termination_by K.X.length + 3 - i

end GenEmit
