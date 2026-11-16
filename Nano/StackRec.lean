/- Route (a), in progress: the meaning of nano-e2e's stack generator `genR` (StartCorrect convention, nano-e2e
4c64d61) on a RECORD MACHINE (`Nano.R`: the semantics of `Nano/Asm.lean`'s record table, before encoding), proved
block by block (`push_ok`, `ld_ok`, `addSp_ok`, `sd0_ok`, `rop_ok`, `binop_ok`, `li_ok`, and **`genE_ok`/`genA_ok`**: an expression's records push `den e env`; value stack `Stk` in the work block).
`Nano.S` is a verbatim COPY of nano-e2e 4c64d61's `Nano/Gen.lean` definitions (r .. depth): nano-e2e does not build
yet (Nano/AsmSelf.lean), so it cannot be merged; replace `Nano.S` by `import Nano.Gen` at the merge.
Remaining (Testing/notes/NANO_PROOF.md): `pro`/`wr8`, the record machine refined by
Sail (record -> word lemmas + `G.step_*`), glue to `CompileCorrect`. -/
import Nano.Ast
import Spec.Encode
import Compiler.IndBytes
namespace Nano.S
open Nano
def r (a b c d : UInt8) : List UInt8 := [a, b, c, d]
-- registers: sp = 2, t0 = 5, t1 = 6, a0 = 10, a2 = 12, a3 = 13, t3 = 28, t6 = 31 (stack pointer).  Slots are 8 bytes.
def ld (rd rs slot : Nat) : List UInt8 := r 0 rd.toUInt8 rs.toUInt8 slot.toUInt8
def sd (rs2 rs1 slot : Nat) : List UInt8 := r 1 rs2.toUInt8 rs1.toUInt8 slot.toUInt8
def addSp (k : Nat) : List UInt8 := r 2 31 31 k.toUInt8           -- t6 += 8k
/-- t6 -= 8; if t6 < a2 then (a0 := -1; ret); sd t0, 0(t6) -/
def push : List UInt8 := r 2 31 31 255 ++ r 13 31 12 0 ++ r 14 10 0 255 ++ r 8 0 0 0 ++ sd 5 31 0

/-- t0 := n by shifting in its 8 bytes, most significant first -/
def li (n : UInt64) : List UInt8 :=
  r 2 5 0 0 ++
  r 4 5 5 8 ++ r 3 5 5 ((n >>> 56).toUInt8) ++ r 4 5 5 8 ++ r 3 5 5 ((n >>> 48).toUInt8) ++
  r 4 5 5 8 ++ r 3 5 5 ((n >>> 40).toUInt8) ++ r 4 5 5 8 ++ r 3 5 5 ((n >>> 32).toUInt8) ++
  r 4 5 5 8 ++ r 3 5 5 ((n >>> 24).toUInt8) ++ r 4 5 5 8 ++ r 3 5 5 ((n >>> 16).toUInt8) ++
  r 4 5 5 8 ++ r 3 5 5 ((n >>> 8).toUInt8) ++ r 4 5 5 8 ++ r 3 5 5 (n.toUInt8)

/-- pops b, a; pushes a ∘ b (`k`: 5 add, 6 sub, 7 mul) -/
def binop (k : UInt8) : List UInt8 := ld 6 31 0 ++ ld 5 31 1 ++ addSp 1 ++ r k 5 5 6 ++ sd 5 31 0

/-- stack slots of k fresh variables starting at depth b, newest first -/
def mkSc : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, b => (b + k) :: mkSc k b

def cnt : Ex → Nat
  | .acons _ r => cnt r + 1
  | _ => 0

-- `sc`: absolute stack slot of each variable (newest first), `d`: number of slots on the stack (frame base 0)
mutual
def genE : List Nat → Nat → Ex → List UInt8
  | _, _, .num n => li n ++ push
  | sc, d, .var i => ld 5 31 (d - 1 - sc.getD i 0) ++ push
  | sc, d, .add a b => genE sc d a ++ genE sc (d + 1) b ++ binop 5
  | sc, d, .sub a b => genE sc d a ++ genE sc (d + 1) b ++ binop 6
  | sc, d, .mul a b => genE sc d a ++ genE sc (d + 1) b ++ binop 7
  | sc, d, .let_ v b => genE sc d v ++ genE (d :: sc) (d + 1) b ++ ld 5 31 0 ++ addSp 1 ++ sd 5 31 0
  | sc, d, .call b as =>
    genA sc d as ++ genE (mkSc (cnt as) d) (d + cnt as) b ++ ld 5 31 0 ++ addSp (cnt as) ++ sd 5 31 0
  | _, _, _ => []
def genA : List Nat → Nat → Ex → List UInt8
  | sc, d, .acons e r => genE sc d e ++ genA sc (d + 1) r
  | _, _, _ => []
end

/-- argument words: t0 := the 8 bytes at t3 (LE, bytewise), pushed; t3 += 8 -/
def rd8 : List UInt8 :=
  r 9 5 28 7 ++ (List.range 7).foldr (fun j acc => r 4 5 5 8 ++ r 9 6 28 (6 - j).toUInt8 ++ r 12 5 5 6 ++ acc) []

/-- load the k arguments from t3 onto the stack, in order -/
def pro : Nat → List UInt8
  | 0 => []
  | k + 1 => rd8 ++ push ++ r 2 28 28 1 ++ pro k

/-- result t0 -> 8 bytes at a3, bytewise -/
def wr8 : List UInt8 := (List.range 8).foldr (fun k acc => r 11 6 5 (8 * k).toUInt8 ++ r 10 6 13 k.toUInt8 ++ acc) []

/-- the records of a program -/
def genR (p : Prog) : List UInt8 :=
  r 2 31 2 0 ++ r 2 28 10 0 ++ pro p.1 ++ genE (mkSc p.1 0) p.1 p.2 ++ ld 5 31 0 ++ wr8 ++ r 8 0 0 0

-- most stack slots in use (what `genR`'s pushes need); `memoryNeeded` = 8 * `depth p`
mutual
def depE : Nat → Ex → Nat
  | d, .num _ => d + 1
  | d, .var _ => d + 1
  | d, .add a b => max (depE d a) (depE (d + 1) b)
  | d, .sub a b => max (depE d a) (depE (d + 1) b)
  | d, .mul a b => max (depE d a) (depE (d + 1) b)
  | d, .let_ v b => max (depE d v) (depE (d + 1) b)
  | d, .call b as => max (depA d as) (depE (d + cnt as) b)
  | _, _ => 0
def depA : Nat → Ex → Nat
  | d, .acons e r => max (depE d e) (depA (d + 1) r)
  | _, _ => 0
end
def depth (p : Prog) : Nat := max p.1 (depE p.1 p.2)
end Nano.S

/-! ## the record machine: the meaning of `genR`'s records (`Nano/Asm.lean`'s table), before encoding -/
namespace Nano.R
open Proven

/-- registers (`x 0` is read as 0), byte memory, record index -/
structure St where
  x : Nat → BitVec 64
  m : Nat → UInt8
  pc : Nat

def St.get (s : St) (r : Nat) : BitVec 64 := if r = 0 then 0 else s.x r
def St.set (s : St) (r : Nat) (v : BitVec 64) : St := { s with x := fun j => if j = r then v else s.x j }

/-- `k` bytes at `a` -/
def rdL (m : Nat → UInt8) (a k : Nat) : List UInt8 := (List.range k).map fun i => m (a + i)
/-- the bytes `L` written at `a` -/
def wrL (m : Nat → UInt8) (a : Nat) (L : List UInt8) : Nat → UInt8 :=
  fun j => if a ≤ j ∧ j < a + L.length then L.getD (j - a) 0 else m j
def rd64 (m : Nat → UInt8) (a : Nat) : BitVec 64 := BitVec.ofNat 64 (unle (rdL m a 8))
def wr64 (m : Nat → UInt8) (a : Nat) (v : BitVec 64) : Nat → UInt8 := wrL m a (leN 8 v.toNat)

def sext8 (c : UInt8) : BitVec 64 := (c.toBitVec).signExtend 64

inductive Out where
  | next (s : St)
  | halt (s : St)
  | stuck

/-- one record `[op, a, b, c]` -/
def exec (s : St) (op a b c : UInt8) : Out :=
  let A := a.toNat; let B := b.toNat
  let s1 := { s with pc := s.pc + 1 }
  match op.toNat with
  | 0 => .next (s1.set A (rd64 s.m (s.get B + BitVec.ofNat 64 (8 * c.toNat)).toNat))
  | 1 => .next { s1 with m := wr64 s.m (s.get B + BitVec.ofNat 64 (8 * c.toNat)).toNat (s.get A) }
  | 2 => .next (s1.set A (s.get B + 8 * sext8 c))
  | 3 => .next (s1.set A (s.get B ||| BitVec.ofNat 64 c.toNat))
  | 4 => .next (s1.set A (s.get B <<< c.toNat))
  | 5 => .next (s1.set A (s.get B + s.get c.toNat))
  | 6 => .next (s1.set A (s.get B - s.get c.toNat))
  | 7 => .next (s1.set A (s.get B * s.get c.toNat))
  | 8 => .halt s
  | 9 => .next (s1.set A (BitVec.ofNat 64 (s.m (s.get B + BitVec.ofNat 64 c.toNat).toNat).toNat))
  | 10 => .next { s1 with m := wrL s.m (s.get B + BitVec.ofNat 64 c.toNat).toNat [UInt8.ofBitVec ((s.get A).setWidth 8)] }
  | 11 => .next (s1.set A (s.get B >>> c.toNat))
  | 12 => .next (s1.set A (s.get B ||| s.get c.toNat))
  | 13 => .next (if s.get B ≤ s.get A then { s with pc := s.pc + 3 } else s1)
  | 14 => .next (s1.set A (s.get B + sext8 c))
  | _ => .next s1

/-- one step of a program (records as bytes) -/
def step (P : List UInt8) (s : St) : Out :=
  match P.drop (4 * s.pc) with
  | op :: a :: b :: c :: _ => exec s op a b c
  | _ => .stuck

/-- many steps without halting -/
inductive Star (P : List UInt8) : St → St → Prop
  | refl (s : St) : Star P s s
  | step {s s' s''} : step P s = .next s' → Star P s' s'' → Star P s s''

theorem Star.trans {P : List UInt8} {a b c : St} (h₁ : Star P a b) (h₂ : Star P b c) : Star P a c := by
  induction h₁ with
  | refl => exact h₂
  | step e _ ih => exact .step e (ih h₂)

/-- the code `code` (whole records) at record `pc` of `P` -/
def CodeAt (P : List UInt8) (pc : Nat) (code : List UInt8) : Prop :=
  ∃ pre post, P = pre ++ code ++ post ∧ pre.length = 4 * pc

theorem CodeAt.app {P : List UInt8} {pc : Nat} {c₁ c₂ : List UInt8} (h : CodeAt P pc (c₁ ++ c₂)) (h4 : c₁.length % 4 = 0) :
    CodeAt P pc c₁ ∧ CodeAt P (pc + c₁.length / 4) c₂ := by
  obtain ⟨pre, post, hP, hl⟩ := h
  exact ⟨⟨pre, c₂ ++ post, by rw [hP]; simp, hl⟩, ⟨pre ++ c₁, post, by rw [hP]; simp, by simp; omega⟩⟩

theorem step_at {P : List UInt8} {s : St} {op a b c : UInt8} {rest : List UInt8}
    (h : CodeAt P s.pc (op :: a :: b :: c :: rest)) : step P s = exec s op a b c := by
  obtain ⟨pre, post, hP, hl⟩ := h
  unfold step; rw [hP, ← hl]; simp


/-! ## registers and memory -/

@[simp] theorem get_set_same (s : St) {r : Nat} (hr : r ≠ 0) (v : BitVec 64) : (s.set r v).get r = v := by
  simp [St.get, St.set, hr]
theorem get_set_ne (s : St) {r j : Nat} (h : j ≠ r) (v : BitVec 64) : (s.set r v).get j = s.get j := by
  simp [St.get, St.set, h]
@[simp] theorem set_m (s : St) (r : Nat) (v : BitVec 64) : (s.set r v).m = s.m := rfl
@[simp] theorem set_pc (s : St) (r : Nat) (v : BitVec 64) : (s.set r v).pc = s.pc := rfl
@[simp] theorem get_pc (s : St) (n : Nat) (r : Nat) : ({ s with pc := n } : St).get r = s.get r := rfl
@[simp] theorem pc_set (s : St) (n : Nat) (r : Nat) (v : BitVec 64) :
    (({ s with pc := n } : St).set r v) = { s.set r v with pc := n } := rfl
@[simp] theorem get_m (s : St) (m) (n : Nat) (r : Nat) : ({ s with m := m, pc := n } : St).get r = s.get r := rfl

theorem rdL_length (m : Nat → UInt8) (a k : Nat) : (rdL m a k).length = k := by simp [rdL]

theorem rdL_wrL_same (m : Nat → UInt8) (a : Nat) (L : List UInt8) : rdL (wrL m a L) a L.length = L := by
  apply List.ext_getElem (by simp [rdL])
  intro i h1 h2
  simp only [rdL, List.getElem_map, List.getElem_range, wrL]
  rw [rdL_length] at h1; rw [if_pos (by omega)]
  simp [List.getD_eq_getElem?_getD, h2]

theorem rdL_wrL_out (m : Nat → UInt8) (a b k : Nat) (L : List UInt8) (h : b + k ≤ a ∨ a + L.length ≤ b) :
    rdL (wrL m a L) b k = rdL m b k := by
  apply List.ext_getElem (by simp [rdL])
  intro i h1 h2
  simp only [rdL, List.getElem_map, List.getElem_range, wrL]
  rw [rdL_length] at h1; rw [if_neg (by omega)]

theorem rd64_wr64_same (m : Nat → UInt8) (a : Nat) (v : BitVec 64) : rd64 (wr64 m a v) a = v := by
  unfold rd64 wr64
  have := rdL_wrL_same m a (leN 8 v.toNat)
  rw [leN_length] at this
  rw [this, unle_leN]
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem rd64_wr64_out (m : Nat → UInt8) (a b : Nat) (v : BitVec 64) (h : b + 8 ≤ a ∨ a + 8 ≤ b) :
    rd64 (wr64 m a v) b = rd64 m b := by
  unfold rd64 wr64; rw [rdL_wrL_out _ _ _ _ _ (by rw [leN_length]; exact h)]

/-! ## addresses -/

theorem addr_add {t c : Nat} (h : t + c < 2 ^ 64) : (BitVec.ofNat 64 t + BitVec.ofNat 64 c).toNat = t + c := by
  simp [BitVec.toNat_add]; omega

theorem sext8_255 : sext8 255 = -1 := by decide
theorem sext8_small : ∀ n, n < 128 → sext8 (UInt8.ofNat n) = BitVec.ofNat 64 n := by decide +kernel

theorem one {P : List UInt8} {s s' : St} {op a b c : UInt8} {rest : List UInt8}
    (h : CodeAt P s.pc (op :: a :: b :: c :: rest)) (he : exec s op a b c = .next s') : Star P s s' :=
  .step (by rw [step_at h]; exact he) (.refl _)

theorem codeAt_drop {P : List UInt8} {pc : Nat} {op a b c : UInt8} {rest : List UInt8}
    (h : CodeAt P pc (op :: a :: b :: c :: rest)) : CodeAt P (pc + 1) rest := by
  have := CodeAt.app (c₁ := [op, a, b, c]) (c₂ := rest) h (by simp)
  simpa using this.2

theorem ofNat_sub8 {t : Nat} (h : 8 ≤ t) (ht : t < 2 ^ 64) :
    BitVec.ofNat 64 t + 8 * sext8 255 = BitVec.ofNat 64 (t - 8) := by
  rw [sext8_255, show (8 : BitVec 64) * -1 = -8 by decide, ← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show BitVec.toNat (8 : BitVec 64) = 8 from rfl]
  have : t % 2 ^ 64 = t := Nat.mod_eq_of_lt ht
  rw [this, Nat.mod_eq_of_lt (a := t - 8) (by omega)]
  omega

/-- : , the bound check passes,  -/
theorem push_ok {P : List UInt8} {s : St} {rest : List UInt8} (h : CodeAt P s.pc (S.push ++ rest)) {t W : Nat}
    (h31 : s.get 31 = BitVec.ofNat 64 t) (h12 : s.get 12 = BitVec.ofNat 64 W) (hW : W + 8 ≤ t) (ht : t < 2 ^ 64) :
    ∃ s', Star P s s' ∧ s'.pc = s.pc + 5 ∧ s'.get 31 = BitVec.ofNat 64 (t - 8) ∧
      s'.m = wr64 s.m (t - 8) (s.get 5) ∧ ∀ j, j ≠ 31 → s'.get j = s.get j := by
  simp only [S.push, S.r, S.sd, List.cons_append, List.nil_append] at h
  have h1 := codeAt_drop h; have h2 := codeAt_drop h1; have h3 := codeAt_drop h2; have h4 := codeAt_drop h3
  -- addi t6, t6, -8
  have x1 := one h (s' := (({ s with pc := s.pc + 1 } : St).set 31 (BitVec.ofNat 64 (t - 8))))
    (by show Out.next _ = _; simp only [UInt8.reduceToNat]; rw [h31, ofNat_sub8 (by omega) ht])
  -- bgeu t6, a2: taken
  generalize hs1 : (({ s with pc := s.pc + 1 } : St).set 31 (BitVec.ofNat 64 (t - 8))) = s1 at x1
  have p1 : s1.pc = s.pc + 1 := by rw [← hs1]; rfl
  have g31 : s1.get 31 = BitVec.ofNat 64 (t - 8) := by rw [← hs1]; simp
  have g12 : s1.get 12 = BitVec.ofNat 64 W := by rw [← hs1, get_set_ne _ (by decide)]; exact h12
  have hle : s1.get 12 ≤ s1.get 31 := by
    rw [g31, g12]; rw [BitVec.le_def]; simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have x2 := one (p1 ▸ h1) (s' := { s1 with pc := s1.pc + 3 }) (by show Out.next _ = _; simp only [UInt8.reduceToNat]; rw [if_pos hle])
  -- sd t0, 0(t6)
  have h4' : CodeAt P ({ s1 with pc := s1.pc + 3 } : St).pc (1 :: Nat.toUInt8 5 :: Nat.toUInt8 31 :: Nat.toUInt8 0 :: rest) := by
    show CodeAt P (s1.pc + 3) _; rw [p1]; exact h4
  have x3 := one h4' (s' := { s1 with pc := s1.pc + 3 + 1, m := wr64 s1.m (t - 8) (s.get 5) }) (by
    show Out.next _ = _
    have e5 : s1.get 5 = s.get 5 := by rw [← hs1, get_set_ne _ (by decide)]; rfl
    have e31 : s1.get 31 = BitVec.ofNat 64 (t - 8) := g31
    simp [St.get] at e5 e31 ⊢
    simp [e5, e31]; rw [Nat.mod_eq_of_lt (by omega)])
  refine ⟨_, x1.trans (x2.trans x3), by simp [p1], ?_, ?_, fun j hj => ?_⟩
  · exact g31
  · rw [← hs1]; rfl
  · show s1.get j = _; rw [← hs1, get_set_ne _ hj]; rfl

/-! ## the records the generator uses, one at a time -/

theorem toU8 {n : Nat} (h : n < 256) : (Nat.toUInt8 n).toNat = n := by simp [Nat.toUInt8, UInt8.toNat_ofNat]; omega

theorem addr8 {t k : Nat} (h : t + 8 * k < 2 ^ 64) :
    (BitVec.ofNat 64 t + BitVec.ofNat 64 (8 * k)).toNat = t + 8 * k := addr_add h

/-- `ld rd, 8k(t6)` -/
theorem ld_ok {P : List UInt8} {s : St} {rd k : Nat} {rest : List UInt8} (h : CodeAt P s.pc (S.ld rd 31 k ++ rest))
    (hrd : rd < 256) (hk : k < 256) {t : Nat} (h31 : s.get 31 = BitVec.ofNat 64 t) (ht : t + 8 * k < 2 ^ 64) :
    Star P s ((({ s with pc := s.pc + 1 } : St)).set rd (rd64 s.m (t + 8 * k))) ∧ CodeAt P (s.pc + 1) rest := by
  simp only [S.ld, S.r, List.cons_append, List.nil_append] at h
  refine ⟨one h ?_, codeAt_drop h⟩
  show Out.next _ = _
  rw [toU8 hrd, toU8 (show 31 < 256 by decide), toU8 hk, h31, addr8 ht]

/-- `addi t6, t6, 8k` (`k < 128`) -/
theorem addSp_ok {P : List UInt8} {s : St} {k : Nat} {rest : List UInt8} (h : CodeAt P s.pc (S.addSp k ++ rest))
    (hk : k < 128) {t : Nat} (h31 : s.get 31 = BitVec.ofNat 64 t) (ht : t + 8 * k < 2 ^ 64) :
    Star P s ((({ s with pc := s.pc + 1 } : St)).set 31 (BitVec.ofNat 64 (t + 8 * k))) ∧ CodeAt P (s.pc + 1) rest := by
  simp only [S.addSp, S.r, List.cons_append, List.nil_append] at h
  refine ⟨one h ?_, codeAt_drop h⟩
  show Out.next _ = _
  simp only [UInt8.reduceToNat]
  rw [h31, show Nat.toUInt8 k = UInt8.ofNat k from rfl, sext8_small k hk]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show BitVec.toNat (8 : BitVec 64) = 8 from rfl]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := 8 * k) (by omega)]
  rw [Nat.mod_eq_of_lt (a := t) (by omega)]

/-- `sd t0, 0(t6)` -/
theorem sd0_ok {P : List UInt8} {s : St} {rest : List UInt8} (h : CodeAt P s.pc (S.sd 5 31 0 ++ rest))
    {t : Nat} (h31 : s.get 31 = BitVec.ofNat 64 t) (ht : t < 2 ^ 64) :
    Star P s { s with pc := s.pc + 1, m := wr64 s.m t (s.get 5) } ∧ CodeAt P (s.pc + 1) rest := by
  simp only [S.sd, S.r, List.cons_append, List.nil_append] at h
  refine ⟨one h ?_, codeAt_drop h⟩
  show Out.next _ = _
  rw [toU8 (show 5 < 256 by decide), toU8 (show 31 < 256 by decide), toU8 (show 0 < 256 by decide), h31,
    addr8 (by omega)]
  rfl

/-- the operator of `binop k` -/
def opv (k : Nat) (a b : BitVec 64) : BitVec 64 := if k = 5 then a + b else if k = 6 then a - b else a * b

/-- `t0 := t0 ∘ t1` -/
theorem rop_ok {P : List UInt8} {s : St} {k : Nat} {rest : List UInt8} (hk : k = 5 ∨ k = 6 ∨ k = 7)
    (h : CodeAt P s.pc (S.r k.toUInt8 5 5 6 ++ rest)) :
    Star P s ((({ s with pc := s.pc + 1 } : St)).set 5 (opv k (s.get 5) (s.get 6))) ∧ CodeAt P (s.pc + 1) rest := by
  simp only [S.r, List.cons_append, List.nil_append] at h
  refine ⟨one h ?_, codeAt_drop h⟩
  rcases hk with rfl | rfl | rfl <;> rfl

/-! ## the value stack -/

/-- the value stack below `T`: `t6` at its top, slot `k` (8 bytes at `T - 8 (k + 1)`) holds `vals[k]` -/
def Stk (s : St) (T : Nat) (vals : List (BitVec 64)) : Prop :=
  s.get 31 = BitVec.ofNat 64 (T - 8 * vals.length) ∧
    ∀ k (hk : k < vals.length), rd64 s.m (T - 8 * (k + 1)) = vals[k]

/-- registers other than `t0 t1 t6` kept -/
def Kept (s s' : St) : Prop := ∀ j, j ≠ 5 → j ≠ 6 → j ≠ 31 → s'.get j = s.get j

theorem Kept.trans {a b c : St} (h₁ : Kept a b) (h₂ : Kept b c) : Kept a c := fun j x y z => by rw [h₂ j x y z, h₁ j x y z]

/-- `binop k`: pop `b`, `a`; push `a ∘ b` -/
theorem binop_ok {P : List UInt8} {s : St} {k : Nat} {rest : List UInt8} (hk : k = 5 ∨ k = 6 ∨ k = 7)
    (h : CodeAt P s.pc (S.binop k.toUInt8 ++ rest)) {T : Nat} {vals : List (BitVec 64)} {va vb : BitVec 64}
    (hs : Stk s T (vals ++ [va, vb])) (hT : 8 * (vals.length + 2) ≤ T) (hT2 : T < 2 ^ 64) :
    ∃ s', Star P s s' ∧ s'.pc = s.pc + 5 ∧ Stk s' T (vals ++ [opv k va vb]) ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  obtain ⟨h31, hv⟩ := hs
  simp only [List.length_append, List.length_cons, List.length_nil] at h31 hv
  obtain ⟨n, hn⟩ : ∃ n, vals.length = n := ⟨_, rfl⟩
  rw [hn] at h31 hT
  have hva : rd64 s.m (T - 8 * (n + 1)) = va := by
    have := hv n (by omega); rw [List.getElem_append_right (by omega)] at this; simpa [hn] using this
  have hvb : rd64 s.m (T - 8 * (n + 2)) = vb := by
    have := hv (n + 1) (by omega); rw [List.getElem_append_right (by omega)] at this; simpa [hn] using this
  simp only [S.binop, List.append_assoc] at h
  generalize ht : T - 8 * (n + 2) = t at h31 hvb
  obtain ⟨x1, c1⟩ := ld_ok (rd := 6) (k := 0) h (by decide) (by decide) h31 (by omega)
  generalize hs1 : ((({ s with pc := s.pc + 1 } : St)).set 6 (rd64 s.m (t + 8 * 0))) = s1 at x1
  have p1 : s1.pc = s.pc + 1 := by rw [← hs1]; rfl
  have g31 : s1.get 31 = BitVec.ofNat 64 t := by rw [← hs1, get_set_ne _ (by decide)]; exact h31
  obtain ⟨x2, c2⟩ := ld_ok (s := s1) (rd := 5) (k := 1) (p1 ▸ c1) (by decide) (by decide) g31 (by omega)
  generalize hs2 : ((({ s1 with pc := s1.pc + 1 } : St)).set 5 (rd64 s1.m (t + 8 * 1))) = s2 at x2
  have p2 : s2.pc = s.pc + 2 := by rw [← hs2]; simp [p1]
  have g31' : s2.get 31 = BitVec.ofNat 64 t := by rw [← hs2, get_set_ne _ (by decide)]; exact g31
  obtain ⟨x3, c3⟩ := addSp_ok (s := s2) (k := 1) (by rw [p2]; rw [p1] at c2; exact c2) (by decide) g31' (by omega)
  generalize hs3 : ((({ s2 with pc := s2.pc + 1 } : St)).set 31 (BitVec.ofNat 64 (t + 8 * 1))) = s3 at x3
  have p3 : s3.pc = s.pc + 3 := by rw [← hs3]; simp [p2]
  obtain ⟨x4, c4⟩ := rop_ok (s := s3) hk (by rw [p3]; rw [p2] at c3; exact c3)
  generalize hs4 : ((({ s3 with pc := s3.pc + 1 } : St)).set 5 (opv k (s3.get 5) (s3.get 6))) = s4 at x4
  have p4 : s4.pc = s.pc + 4 := by rw [← hs4]; simp [p3]
  have g31'' : s4.get 31 = BitVec.ofNat 64 (t + 8) := by
    rw [← hs4, get_set_ne _ (by decide)]; show s3.get 31 = _; rw [← hs3]; simp
  obtain ⟨x5, c5⟩ := sd0_ok (s := s4) (by rw [p4]; rw [p3] at c4; exact c4) g31'' (by omega)
  have m4 : s4.m = s.m := by rw [← hs4, ← hs3, ← hs2, ← hs1]; rfl
  have v5 : s4.get 5 = opv k va vb := by
    rw [← hs4]; simp only [get_set_same _ (show (5 : Nat) ≠ 0 by decide)]
    have e5 : s3.get 5 = va := by
      rw [← hs3, get_set_ne _ (by decide)]; show s2.get 5 = _
      rw [← hs2]; simp only [get_set_same _ (show (5 : Nat) ≠ 0 by decide)]
      rw [show s1.m = s.m by rw [← hs1]; rfl, ← hva]; congr 1; omega
    have e6 : s3.get 6 = vb := by
      rw [← hs3, get_set_ne _ (by decide)]; show s2.get 6 = _
      rw [← hs2, get_set_ne _ (by decide)]; show s1.get 6 = _
      rw [← hs1]; simp only [get_set_same _ (show (6 : Nat) ≠ 0 by decide)]; rw [← hvb]; congr 1
    rw [e5, e6]
  refine ⟨_, x1.trans (x2.trans (x3.trans (x4.trans x5))), by simp [p4], ⟨?_, fun j hj => ?_⟩, fun j a b c => ?_, ?_⟩
  · show s4.get 31 = _; rw [g31'']; congr 1; simp; omega
  · simp only [List.length_append, List.length_singleton] at hj
    show rd64 (wr64 s4.m (t + 8) (s4.get 5)) _ = _
    by_cases hjn : j = n
    · subst hjn
      rw [show T - 8 * (j + 1) = t + 8 by omega, rd64_wr64_same, v5]; simp [hn]
    · rw [rd64_wr64_out _ _ _ _ (by omega), m4, List.getElem_append_left (by omega)]
      have := hv j (by omega); rwa [List.getElem_append_left (by omega)] at this
  · show s4.get j = s.get j
    rw [← hs4, ← hs3, ← hs2, ← hs1]; simp [St.get, St.set, a, b, c]
  · show CodeAt P (s4.pc + 1) rest; rw [p4]; rw [p4] at c5; exact c5

/-! ## constants (`li`) -/

theorem shl_or (x : Nat) (b : Nat) (hx : x < 2 ^ 56) (hb : b < 256) :
    (BitVec.ofNat 64 x <<< 8 ||| BitVec.ofNat 64 b) = BitVec.ofNat 64 (x * 256 + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := x) (by omega), Nat.mod_eq_of_lt (a := b) (by omega),
    Nat.mod_eq_of_lt (a := x * 256 + b) (by omega), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by rw [show 2 ^ 8 = 256 from rfl]; omega)]
  rw [Nat.mul_comm x, ← Nat.two_pow_add_eq_or_of_lt (i := 8) (by omega)]

theorem horner_step (n m : Nat) : n / 256 ^ (m + 1) * 256 + n / 256 ^ m % 256 = n / 256 ^ m := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (n / 256 ^ m) 256
  omega

/-- one byte of `li`: `t0 := t0 << 8 | byte m` -/
theorem pair_ok {P : List UInt8} {s : St} {n sh : UInt64} {m : Nat} {rest : List UInt8} (hsh : sh.toNat = 8 * m)
    (hm : m < 8) (h : CodeAt P s.pc (S.r 4 5 5 8 ++ S.r 3 5 5 ((n >>> sh).toUInt8) ++ rest))
    (h5 : s.get 5 = BitVec.ofNat 64 (n.toNat / 256 ^ (m + 1))) :
    ∃ s', Star P s s' ∧ s'.get 5 = BitVec.ofNat 64 (n.toNat / 256 ^ m) ∧ s'.m = s.m ∧
      (∀ j, j ≠ 5 → s'.get j = s.get j) ∧ CodeAt P s'.pc rest := by
  simp only [S.r, List.cons_append, List.nil_append] at h
  have h1 := codeAt_drop h
  have x1 := one h (s' := (({ s with pc := s.pc + 1 } : St).set 5 (s.get 5 <<< 8))) rfl
  generalize hs1 : (({ s with pc := s.pc + 1 } : St).set 5 (s.get 5 <<< 8)) = s1 at x1
  have p1 : s1.pc = s.pc + 1 := by rw [← hs1]; rfl
  have g5 : s1.get 5 = s.get 5 <<< 8 := by rw [← hs1]; simp
  have x2 := one (s := s1) (p1 ▸ h1)
    (s' := ((({ s1 with pc := s1.pc + 1 } : St).set 5 (s1.get 5 ||| BitVec.ofNat 64 ((n >>> sh).toUInt8).toNat)))) rfl
  refine ⟨_, x1.trans x2, ?_, by rw [← hs1]; rfl, fun j hj => ?_, by simp [p1]; exact codeAt_drop h1⟩
  · simp only [get_set_same _ (show (5 : Nat) ≠ 0 by decide), g5]
    have hb : ((n >>> sh).toUInt8).toNat = n.toNat / 256 ^ m % 256 := by
      simp [UInt64.toNat_shiftRight, hsh]
      rw [Nat.mod_eq_of_lt (a := 8 * m) (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_mul]
    have hlt : n.toNat / 256 ^ (m + 1) < 2 ^ 56 := by
      apply Nat.div_lt_of_lt_mul
      have h1 : 256 ≤ 256 ^ (m + 1) := Nat.le_self_pow (by omega) _
      have h2 : n.toNat < 2 ^ 56 * 2 ^ 8 := by rw [← Nat.pow_add]; exact n.toNat_lt
      have h3 : 2 ^ 56 * 2 ^ 8 ≤ 256 ^ (m + 1) * 2 ^ 56 := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ h1
      exact Nat.lt_of_lt_of_le h2 h3
    rw [h5, hb, shl_or _ _ hlt (Nat.mod_lt _ (by decide)), horner_step]
  · rw [← hs1] at ⊢; simp [St.get, St.set, hj]

theorem li_eq (n : UInt64) (rest : List UInt8) : S.li n ++ rest =
    S.r 2 5 0 0 ++ (S.r 4 5 5 8 ++ S.r 3 5 5 ((n >>> 56).toUInt8) ++ (S.r 4 5 5 8 ++ S.r 3 5 5 ((n >>> 48).toUInt8) ++
    (S.r 4 5 5 8 ++ S.r 3 5 5 ((n >>> 40).toUInt8) ++ (S.r 4 5 5 8 ++ S.r 3 5 5 ((n >>> 32).toUInt8) ++
    (S.r 4 5 5 8 ++ S.r 3 5 5 ((n >>> 24).toUInt8) ++ (S.r 4 5 5 8 ++ S.r 3 5 5 ((n >>> 16).toUInt8) ++
    (S.r 4 5 5 8 ++ S.r 3 5 5 ((n >>> 8).toUInt8) ++ (S.r 4 5 5 8 ++ S.r 3 5 5 ((n >>> 0).toUInt8) ++ rest)))))))) := by
  simp [S.li, S.r]

/-- `li n`: `t0 := n` -/
theorem li_ok {P : List UInt8} {s : St} {n : UInt64} {rest : List UInt8} (h : CodeAt P s.pc (S.li n ++ rest)) :
    ∃ s', Star P s s' ∧ s'.get 5 = n.toBitVec ∧ s'.m = s.m ∧ (∀ j, j ≠ 5 → s'.get j = s.get j) ∧ CodeAt P s'.pc rest := by
  rw [li_eq] at h
  have x0 := one (op := 2) (a := 5) (b := 0) (c := 0) h (s' := (({ s with pc := s.pc + 1 } : St).set 5 (s.get 0 + 8 * sext8 0))) rfl
  generalize hs0 : (({ s with pc := s.pc + 1 } : St).set 5 (s.get 0 + 8 * sext8 0)) = s0 at x0
  have c0 := codeAt_drop (op := 2) (a := 5) (b := 0) (c := 0) h
  rw [show s.pc + 1 = s0.pc by rw [← hs0]; rfl] at c0
  have g0 : s0.get 5 = BitVec.ofNat 64 (n.toNat / 256 ^ (7 + 1)) := by
    rw [← hs0]; simp only [get_set_same _ (show (5 : Nat) ≠ 0 by decide)]
    rw [Nat.div_eq_of_lt (by have := n.toNat_lt; omega)]
    rw [show s.get 0 = 0 from rfl, show sext8 0 = 0 by decide]; rfl
  have k0 : ∀ j, j ≠ 5 → s0.get j = s.get j := fun j hj => by rw [← hs0]; simp [St.get, St.set, hj]
  have m0 : s0.m = s.m := by rw [← hs0]; rfl
  obtain ⟨s1, x1, g1, m1, k1, c1⟩ := pair_ok (m := 7) (by decide) (by decide) c0 g0
  obtain ⟨s2, x2, g2, m2, k2, c2⟩ := pair_ok (m := 6) (by decide) (by decide) c1 g1
  obtain ⟨s3, x3, g3, m3, k3, c3⟩ := pair_ok (m := 5) (by decide) (by decide) c2 g2
  obtain ⟨s4, x4, g4, m4, k4, c4⟩ := pair_ok (m := 4) (by decide) (by decide) c3 g3
  obtain ⟨s5, x5, g5, m5, k5, c5⟩ := pair_ok (m := 3) (by decide) (by decide) c4 g4
  obtain ⟨s6, x6, g6, m6, k6, c6⟩ := pair_ok (m := 2) (by decide) (by decide) c5 g5
  obtain ⟨s7, x7, g7, m7, k7, c7⟩ := pair_ok (m := 1) (by decide) (by decide) c6 g6
  obtain ⟨s8, x8, g8, m8, k8, c8⟩ := pair_ok (m := 0) (by decide) (by decide) c7 g7
  refine ⟨s8, x0.trans (x1.trans (x2.trans (x3.trans (x4.trans (x5.trans (x6.trans (x7.trans x8))))))), ?_,
    by rw [m8, m7, m6, m5, m4, m3, m2, m1, m0], fun j hj => ?_, c8⟩
  · rw [g8]; simp
  · rw [k8 j hj, k7 j hj, k6 j hj, k5 j hj, k4 j hj, k3 j hj, k2 j hj, k1 j hj, k0 j hj]

/-! ## stack operations -/

/-- `push` on the stack: `t0` becomes the new top slot -/
theorem push_stk {P : List UInt8} {s : St} {rest : List UInt8} (h : CodeAt P s.pc (S.push ++ rest)) {T W : Nat}
    {vals : List (BitVec 64)} (hs : Stk s T vals) (h12 : s.get 12 = BitVec.ofNat 64 W)
    (hW : W + 8 * (vals.length + 1) ≤ T) (hT : T < 2 ^ 64) :
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [s.get 5]) ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  obtain ⟨h31, hv⟩ := hs
  obtain ⟨s', x, p', g31, m', k'⟩ := push_ok h h31 h12 (by omega) (by omega)
  refine ⟨s', x, ⟨?_, fun k hk => ?_⟩, fun j a b c => k' j c, ?_⟩
  · rw [g31]; congr 1; simp; omega
  · rw [m']
    simp only [List.length_append, List.length_singleton] at hk
    by_cases hkn : k = vals.length
    · subst hkn; rw [show T - 8 * (vals.length + 1) = T - 8 * vals.length - 8 by omega, rd64_wr64_same]; simp
    · rw [rd64_wr64_out _ _ _ _ (by omega), List.getElem_append_left (by omega)]; exact hv k (by omega)
  · obtain ⟨pre, post, hP, hl⟩ := h
    exact ⟨pre ++ S.push, post, by rw [hP]; simp, by rw [p']; simp [S.push, S.r, S.sd]; omega⟩

/-- `ld t0, 8k(t6)` reading slot `j` -/
theorem ldslot_ok {P : List UInt8} {s : St} {j : Nat} {rest : List UInt8} {T : Nat} {vals : List (BitVec 64)}
    (h : CodeAt P s.pc (S.ld 5 31 (vals.length - 1 - j) ++ rest)) (hs : Stk s T vals) (hj : j < vals.length)
    (hd : vals.length ≤ 256) (hT : 8 * vals.length ≤ T) (hT2 : T < 2 ^ 64) :
    ∃ s', Star P s s' ∧ s'.get 5 = vals[j] ∧ s'.m = s.m ∧ (∀ i, i ≠ 5 → s'.get i = s.get i) ∧ CodeAt P s'.pc rest := by
  obtain ⟨x, c⟩ := ld_ok (rd := 5) h (by decide) (by omega) hs.1 (by omega)
  refine ⟨_, x, ?_, rfl, fun i hi => by simp [St.get, St.set, hi], c⟩
  simp only [get_set_same _ (show (5 : Nat) ≠ 0 by decide), set_m]
  rw [show T - 8 * vals.length + 8 * (vals.length - 1 - j) = T - 8 * (j + 1) by omega]
  exact hs.2 j hj

/-- `ld t0, 0(t6); t6 += 8k; sd t0, 0(t6)`: the top value replaces the `k + 1` slots it sits on -/
theorem tail_ok {P : List UInt8} {s : St} {k : Nat} {rest : List UInt8}
    (h : CodeAt P s.pc (S.ld 5 31 0 ++ S.addSp k ++ S.sd 5 31 0 ++ rest)) {T : Nat} {vals mid : List (BitVec 64)}
    {x : BitVec 64} (hs : Stk s T (vals ++ mid ++ [x])) (hk : mid.length = k) (hk2 : k < 128)
    (hT : 8 * (vals.length + k + 1) ≤ T) (hT2 : T < 2 ^ 64) :
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [x]) ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  obtain ⟨h31, hv⟩ := hs
  simp only [List.length_append, List.length_singleton, hk] at h31 hv
  have hx : rd64 s.m (T - 8 * (vals.length + k + 1)) = x := by
    have := hv (vals.length + k) (by omega)
    rw [List.getElem_append_right (by simp [hk])] at this; simpa [hk] using this
  simp only [List.append_assoc] at h
  obtain ⟨x1, c1⟩ := ld_ok (rd := 5) (k := 0) h (by decide) (by decide) h31 (by omega)
  generalize hs1 : ((({ s with pc := s.pc + 1 } : St)).set 5 (rd64 s.m (T - 8 * (vals.length + k + 1) + 8 * 0))) = s1 at x1
  have p1 : s1.pc = s.pc + 1 := by rw [← hs1]; rfl
  have g31 : s1.get 31 = BitVec.ofNat 64 (T - 8 * (vals.length + k + 1)) := by rw [← hs1, get_set_ne _ (by decide)]; exact h31
  obtain ⟨x2, c2⟩ := addSp_ok (s := s1) (k := k) (p1 ▸ c1) hk2 g31 (by omega)
  generalize hs2 : ((({ s1 with pc := s1.pc + 1 } : St)).set 31 (BitVec.ofNat 64 (T - 8 * (vals.length + k + 1) + 8 * k))) = s2 at x2
  have p2 : s2.pc = s.pc + 2 := by rw [← hs2]; simp [p1]
  have g31' : s2.get 31 = BitVec.ofNat 64 (T - 8 * (vals.length + 1)) := by
    rw [← hs2]; simp only [get_set_same _ (show (31 : Nat) ≠ 0 by decide)]; congr 1; omega
  obtain ⟨x3, c3⟩ := sd0_ok (s := s2) (by rw [p2]; rw [p1] at c2; exact c2) g31' (by omega)
  have m2 : s2.m = s.m := by rw [← hs2, ← hs1]; rfl
  have v5 : s2.get 5 = x := by
    rw [← hs2, get_set_ne _ (by decide)]; show s1.get 5 = _
    rw [← hs1]; simp only [get_set_same _ (show (5 : Nat) ≠ 0 by decide)]; rw [Nat.mul_zero, Nat.add_zero, hx]
  refine ⟨_, x1.trans (x2.trans x3), ⟨?_, fun j hj => ?_⟩, fun j a b c => ?_, ?_⟩
  · show s2.get 31 = _; rw [g31']; simp
  · simp only [List.length_append, List.length_singleton] at hj
    show rd64 (wr64 s2.m (T - 8 * (vals.length + 1)) (s2.get 5)) _ = _
    by_cases hjn : j = vals.length
    · subst hjn; rw [rd64_wr64_same, v5]; simp
    · rw [rd64_wr64_out _ _ _ _ (by omega), m2, List.getElem_append_left (by omega)]
      have := hv j (by omega); rwa [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega)] at this
  · show s2.get j = s.get j
    rw [← hs2, ← hs1]; simp [St.get, St.set, a, c]
  · show CodeAt P (s2.pc + 1) rest; rw [p2]; rw [p2] at c3; exact c3

/-! ## expressions -/

mutual
/-- variables in scope (`n` of them), argument lists of fewer than 128 entries, no stray `anil`/`acons` -/
def ScE : Ex → Nat → Bool
  | .num _, _ => true
  | .var i, n => decide (i < n)
  | .add a b, n => ScE a n && ScE b n
  | .sub a b, n => ScE a n && ScE b n
  | .mul a b, n => ScE a n && ScE b n
  | .let_ v b, n => ScE v n && ScE b (n + 1)
  | .call b as, n => ScA as n && ScE b (S.cnt as) && decide (S.cnt as < 128)
  | .anil, _ => false
  | .acons _ _, _ => false
def ScA : Ex → Nat → Bool
  | .acons e r, n => ScE e n && ScA r n
  | _, _ => true
end

/-- the scope: variable `i` is slot `sc[i]`, holding `env[i]` -/
def ScOk (sc : List Nat) (env : List UInt64) (vals : List (BitVec 64)) : Prop :=
  ∀ i, i < env.length → ∃ h : sc.getD i 0 < vals.length, vals[sc.getD i 0] = (env.getD i 0).toBitVec

theorem ScOk.mono {sc : List Nat} {env : List UInt64} {vals : List (BitVec 64)} (h : ScOk sc env vals)
    (more : List (BitVec 64)) : ScOk sc env (vals ++ more) := fun i hi => by
  obtain ⟨h1, h2⟩ := h i hi
  exact ⟨by rw [List.length_append]; omega, by rw [List.getElem_append_left h1]; exact h2⟩

theorem ScOk.push {sc : List Nat} {env : List UInt64} {vals : List (BitVec 64)} (h : ScOk sc env vals) (v : UInt64) :
    ScOk (vals.length :: sc) (v :: env) (vals ++ [v.toBitVec]) := fun i hi => by
  cases i with
  | zero => exact ⟨by simp, by simp⟩
  | succ i =>
    obtain ⟨h1, h2⟩ := h i (by simp at hi; omega)
    exact ⟨by simp only [List.getD_cons_succ, List.length_append, List.length_singleton]; omega,
      by simp only [List.getD_cons_succ]; rw [List.getElem_append_left h1]; exact h2⟩

theorem mkSc_getD : ∀ (k b i : Nat), i < k → (S.mkSc k b).getD i 0 = b + k - 1 - i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, b, 0, _ => by simp [S.mkSc]
  | k + 1, b, i + 1, h => by simp only [S.mkSc, List.getD_cons_succ]; rw [mkSc_getD k b i (by omega)]; omega

theorem ScOk.args (vals args : List (BitVec 64)) (as : List UInt64) (hl : as.length = args.length)
    (ha : ∀ j (h : j < args.length), args[j] = (as[j]'(by omega)).toBitVec) :
    ScOk (S.mkSc args.length vals.length) as.reverse (vals ++ args) := fun i hi => by
  simp only [List.length_reverse] at hi
  rw [mkSc_getD _ _ _ (by omega)]
  refine ⟨by simp; omega, ?_⟩
  rw [List.getElem_append_right (by omega)]
  rw [ha _ (by omega), List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]; congr 2; omega

theorem depE_ge : ∀ (e : Ex) (d n : Nat), ScE e n = true → d + 1 ≤ S.depE d e
  | .num _, d, n, _ => by simp [S.depE]
  | .var _, d, n, _ => by simp [S.depE]
  | .add a b, d, n, h => by simp only [ScE, Bool.and_eq_true] at h; have := depE_ge a d n h.1; simp only [S.depE]; omega
  | .sub a b, d, n, h => by simp only [ScE, Bool.and_eq_true] at h; have := depE_ge a d n h.1; simp only [S.depE]; omega
  | .mul a b, d, n, h => by simp only [ScE, Bool.and_eq_true] at h; have := depE_ge a d n h.1; simp only [S.depE]; omega
  | .let_ v b, d, n, h => by simp only [ScE, Bool.and_eq_true] at h; have := depE_ge v d n h.1; simp only [S.depE]; omega
  | .call b as, d, n, h => by
    simp only [ScE, Bool.and_eq_true] at h; have := depE_ge b (d + S.cnt as) _ h.1.2; simp only [S.depE]; omega
  | .anil, _, _, h => by simp [ScE] at h
  | .acons _ _, _, _, h => by simp [ScE] at h

theorem toBV_opv5 (a b : UInt64) : opv 5 a.toBitVec b.toBitVec = (a + b).toBitVec := by simp [opv]
theorem toBV_opv6 (a b : UInt64) : opv 6 a.toBitVec b.toBitVec = (a - b).toBitVec := by simp [opv]
theorem toBV_opv7 (a b : UInt64) : opv 7 a.toBitVec b.toBitVec = (a * b).toBitVec := by simp [opv]

theorem stk_kept {s s' : St} {T : Nat} {vals : List (BitVec 64)} (hs : Stk s T vals) (hm : s'.m = s.m)
    (h31 : s'.get 31 = s.get 31) : Stk s' T vals := ⟨by rw [h31]; exact hs.1, fun k hk => by rw [hm]; exact hs.2 k hk⟩

variable {P : List UInt8} {T W : Nat}

/-- a binary operator node -/
theorem bin_node (k : Nat) (hk : k = 5 ∨ k = 6 ∨ k = 7) (hT2 : T < 2 ^ 64) {a b : Ex} {sc : List Nat}
    {vals : List (BitVec 64)} {s : St} {rest : List UInt8} {va vb : UInt64}
    (ha : ∀ (s : St) (rest : List UInt8), CodeAt P s.pc (S.genE sc vals.length a ++ rest) → Stk s T vals →
      s.get 12 = BitVec.ofNat 64 W →
      ∃ s', Star P s s' ∧ Stk s' T (vals ++ [va.toBitVec]) ∧ Kept s s' ∧ CodeAt P s'.pc rest)
    (hb : ∀ (s : St) (rest : List UInt8), CodeAt P s.pc (S.genE sc (vals ++ [va.toBitVec]).length b ++ rest) →
      Stk s T (vals ++ [va.toBitVec]) → s.get 12 = BitVec.ofNat 64 W →
      ∃ s', Star P s s' ∧ Stk s' T (vals ++ [va.toBitVec] ++ [vb.toBitVec]) ∧ Kept s s' ∧ CodeAt P s'.pc rest)
    (h : CodeAt P s.pc (S.genE sc vals.length a ++ S.genE sc (vals.length + 1) b ++ S.binop k.toUInt8 ++ rest))
    (hs : Stk s T vals) (h12 : s.get 12 = BitVec.ofNat 64 W) (hT : 8 * (vals.length + 2) ≤ T) :
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [opv k va.toBitVec vb.toBitVec]) ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  simp only [List.append_assoc] at h
  obtain ⟨s1, x1, st1, k1, c1⟩ := ha s _ h hs h12
  obtain ⟨s2, x2, st2, k2, c2⟩ := hb s1 _ (by simpa using c1) st1 (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12)
  obtain ⟨s3, x3, -, st3, k3, c3⟩ := binop_ok hk c2 (vals := vals) (by simpa using st2) hT hT2
  exact ⟨s3, x1.trans (x2.trans x3), st3, k1.trans (k2.trans k3), c3⟩

mutual
/-- **an expression's records push its value** (on the record machine; the stack fits in the work block) -/
theorem genE_ok (hT2 : T < 2 ^ 64) : ∀ (e : Ex) (sc : List Nat) (env : List UInt64) (vals : List (BitVec 64)) (s : St)
    (rest : List UInt8), CodeAt P s.pc (S.genE sc vals.length e ++ rest) → ScE e env.length = true →
    ScOk sc env vals → Stk s T vals → s.get 12 = BitVec.ofNat 64 W → W + 8 * S.depE vals.length e ≤ T →
    S.depE vals.length e ≤ 256 →
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [(den e env).toBitVec]) ∧ Kept s s' ∧ CodeAt P s'.pc rest
  | .num n, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [S.genE, List.append_assoc] at h
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := li_ok h
    obtain ⟨s2, x2, st2, k2, c2⟩ := push_stk c1 (stk_kept hs m1 (k1 31 (by decide)))
      (by rw [k1 12 (by decide)]; exact h12) (by simp only [S.depE] at hW; omega) hT2
    exact ⟨s2, x1.trans x2, by rw [g1] at st2; simpa [den] using st2, fun j a b c => by rw [k2 j a b c, k1 j a], c2⟩
  | .var i, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [S.genE, List.append_assoc] at h
    simp only [ScE, decide_eq_true_eq] at hsc
    simp only [S.depE] at hW hd
    obtain ⟨hj, hv⟩ := hok i hsc
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := ldslot_ok h hs hj (by omega) (by omega) hT2
    obtain ⟨s2, x2, st2, k2, c2⟩ := push_stk c1 (stk_kept hs m1 (k1 31 (by decide)))
      (by rw [k1 12 (by decide)]; exact h12) (by omega) hT2
    exact ⟨s2, x1.trans x2, by rw [g1, hv] at st2; simpa [den] using st2, fun j a b c => by rw [k2 j a b c, k1 j a], c2⟩
  | .add a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [S.depE] at hW hd
    have := depE_ge b (vals.length + 1) _ hsc.2
    obtain ⟨s', x, st, k, c⟩ := bin_node 5 (by decide) hT2 (va := den a env) (vb := den b env)
      (fun s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 (by omega) (by omega))
      (fun s rest h hs h12 => by
        have := genE_ok hT2 b sc env (vals ++ [(den a env).toBitVec]) s rest h hsc.2 (hok.mono _) hs h12
          (by simp; omega) (by simp; omega)
        simpa using this) (by simpa [S.genE] using h) hs h12 (by omega)
    exact ⟨s', x, by rw [toBV_opv5] at st; simpa [den] using st, k, c⟩
  | .sub a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [S.depE] at hW hd
    have := depE_ge b (vals.length + 1) _ hsc.2
    obtain ⟨s', x, st, k, c⟩ := bin_node 6 (by decide) hT2 (va := den a env) (vb := den b env)
      (fun s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 (by omega) (by omega))
      (fun s rest h hs h12 => by
        have := genE_ok hT2 b sc env (vals ++ [(den a env).toBitVec]) s rest h hsc.2 (hok.mono _) hs h12
          (by simp; omega) (by simp; omega)
        simpa using this) (by simpa [S.genE] using h) hs h12 (by omega)
    exact ⟨s', x, by rw [toBV_opv6] at st; simpa [den] using st, k, c⟩
  | .mul a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [S.depE] at hW hd
    have := depE_ge b (vals.length + 1) _ hsc.2
    obtain ⟨s', x, st, k, c⟩ := bin_node 7 (by decide) hT2 (va := den a env) (vb := den b env)
      (fun s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 (by omega) (by omega))
      (fun s rest h hs h12 => by
        have := genE_ok hT2 b sc env (vals ++ [(den a env).toBitVec]) s rest h hsc.2 (hok.mono _) hs h12
          (by simp; omega) (by simp; omega)
        simpa using this) (by simpa [S.genE] using h) hs h12 (by omega)
    exact ⟨s', x, by rw [toBV_opv7] at st; simpa [den] using st, k, c⟩
  | .let_ v b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [S.depE] at hW hd
    have := depE_ge b (vals.length + 1) _ hsc.2
    simp only [S.genE, List.append_assoc] at h
    obtain ⟨s1, x1, st1, k1, c1⟩ := genE_ok hT2 v sc env vals s _ h hsc.1 hok hs h12 (by omega) (by omega)
    obtain ⟨s2, x2, st2, k2, c2⟩ := genE_ok hT2 b (vals.length :: sc) (den v env :: env)
      (vals ++ [(den v env).toBitVec]) s1 _ (by simpa using c1) (by simpa using hsc.2) (hok.push _) st1
      (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12) (by simp; omega) (by simp; omega)
    obtain ⟨s3, x3, st3, k3, c3⟩ := tail_ok (k := 1) (mid := [(den v env).toBitVec]) (by simpa using c2)
      (by simpa using st2) rfl (by decide) (by omega) hT2
    exact ⟨s3, x1.trans (x2.trans x3), by simpa [den] using st3, k1.trans (k2.trans k3), c3⟩
  | .call b as, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true, decide_eq_true_eq] at hsc; simp only [S.depE] at hW hd
    obtain ⟨⟨ha, hb⟩, hc⟩ := hsc
    have := depE_ge b (vals.length + S.cnt as) _ hb
    simp only [S.genE, List.append_assoc] at h
    obtain ⟨s1, x1, st1, k1, c1, hcnt⟩ := genA_ok hT2 as sc env vals s _ h ha hok hs h12 (by omega) (by omega)
    have hl : ((denA as env).map UInt64.toBitVec).length = S.cnt as := by simp [hcnt]
    obtain ⟨s2, x2, st2, k2, c2⟩ := genE_ok hT2 b (S.mkSc (S.cnt as) vals.length) (denA as env).reverse
      (vals ++ (denA as env).map UInt64.toBitVec) s1 _ (by simpa [hl] using c1) (by simpa [hcnt] using hb)
      (by rw [← hl]; exact ScOk.args _ _ _ (by simp) (fun j h => by simp)) st1
      (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12) (by simp [hl]; omega) (by simp [hl]; omega)
    obtain ⟨s3, x3, st3, k3, c3⟩ := tail_ok (k := S.cnt as) (mid := (denA as env).map UInt64.toBitVec)
      (by simpa using c2) (by simpa using st2) hl hc (by omega) hT2
    exact ⟨s3, x1.trans (x2.trans x3), by simpa [den] using st3, k1.trans (k2.trans k3), c3⟩
  | .anil, _, _, _, _, _, _, hsc, _, _, _, _, _ => by simp [ScE] at hsc
  | .acons _ _, _, _, _, _, _, _, hsc, _, _, _, _, _ => by simp [ScE] at hsc
/-- an argument list pushes its values -/
theorem genA_ok (hT2 : T < 2 ^ 64) : ∀ (as : Ex) (sc : List Nat) (env : List UInt64) (vals : List (BitVec 64)) (s : St)
    (rest : List UInt8), CodeAt P s.pc (S.genA sc vals.length as ++ rest) → ScA as env.length = true →
    ScOk sc env vals → Stk s T vals → s.get 12 = BitVec.ofNat 64 W → W + 8 * S.depA vals.length as ≤ T →
    S.depA vals.length as ≤ 256 →
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ (denA as env).map UInt64.toBitVec) ∧ Kept s s' ∧ CodeAt P s'.pc rest ∧
      S.cnt as = (denA as env).length
  | .acons e r, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScA, Bool.and_eq_true] at hsc; simp only [S.depA] at hW hd
    simp only [S.genA, List.append_assoc] at h
    obtain ⟨s1, x1, st1, k1, c1⟩ := genE_ok hT2 e sc env vals s _ h hsc.1 hok hs h12 (by omega) (by omega)
    obtain ⟨s2, x2, st2, k2, c2, hc2⟩ := genA_ok hT2 r sc env (vals ++ [(den e env).toBitVec]) s1 _ (by simpa using c1)
      hsc.2 (hok.mono _) st1 (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12) (by simp; omega)
      (by simp; omega)
    exact ⟨s2, x1.trans x2, by simpa [denA] using st2, k1.trans k2, c2, by simp [S.cnt, denA, hc2]⟩
  | .num _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [denA] using hs, fun _ _ _ _ => rfl,
      by simpa [S.genA] using h, rfl⟩
  | .var _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [denA] using hs, fun _ _ _ _ => rfl,
      by simpa [S.genA] using h, rfl⟩
  | .add _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [denA] using hs, fun _ _ _ _ => rfl,
      by simpa [S.genA] using h, rfl⟩
  | .sub _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [denA] using hs, fun _ _ _ _ => rfl,
      by simpa [S.genA] using h, rfl⟩
  | .mul _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [denA] using hs, fun _ _ _ _ => rfl,
      by simpa [S.genA] using h, rfl⟩
  | .let_ _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [denA] using hs, fun _ _ _ _ => rfl,
      by simpa [S.genA] using h, rfl⟩
  | .call _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [denA] using hs, fun _ _ _ _ => rfl,
      by simpa [S.genA] using h, rfl⟩
  | .anil, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [denA] using hs, fun _ _ _ _ => rfl,
      by simpa [S.genA] using h, rfl⟩
end

end Nano.R
