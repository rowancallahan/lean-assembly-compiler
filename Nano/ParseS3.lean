/- Stage 2 (`Nano.PB.stage2`, the parser machine) in the form the S3 front end accepts (`s3_compile`,
Compiler/S3/Front.lean), and the bridge `stage2S_eq : stage2S = stage2` (all inputs).
`Testing/notes/NANO_PARSE_S3.md`.

What differs from the verbatim source (the S3 front end rejects, or its certificates fail on, these):
* `Nat.toUInt8` ↦ `u8N` (through `natW`, a structural `Nat → UInt64`); `Nat` subtraction ↦ `subN` (structural);
  `(j / 256).toUInt8`, `(j % 256).toUInt8` ↦ `((natW j) >>> 8).toUInt8`, `(natW j).toUInt8`;
* the token decoder `dec` ↦ `decS`: `Option.map` with a lambda capturing run-time values ↦ an explicit match
  (`consO`); `UInt8` subtraction `(b - 48).toUInt64` ↦ `b.toUInt64 - 48` (`48 ≤ b` holds there);
* `gasOf ts = 13 * ts.length + 6` ↦ `gasS` (structural, `+ 13` per token).
Everything else (`lookS`, `findD`, `mo`, `sLi`, the datatypes `Tok`, `Fr`, `Ctl`, `St`, `Res`) is the original. -/
import Nano.ParseBGas

namespace Nano.PS
open Nano Nano.B Nano.PB

/-! ## helpers -/

/-- a `Nat` as a word (wraps) -/
def natW : Nat → UInt64
  | 0 => 0
  | n + 1 => natW n + 1

/-- `Nat.toUInt8` -/
def u8N (n : Nat) : UInt8 := (natW n).toUInt8

/-- `Nat` subtraction (truncated) -/
def subN : Nat → Nat → Nat
  | n, 0 => n
  | 0, _ + 1 => 0
  | n + 1, k + 1 => subN n k

theorem natW_eq : ∀ n, natW n = n.toUInt64
  | 0 => rfl
  | n + 1 => by
    rw [natW, natW_eq n]
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_add, Nat.add_mod]

theorem u8N_eq (n : Nat) : u8N n = n.toUInt8 := by
  unfold u8N; rw [natW_eq]
  apply UInt8.toNat_inj.mp
  simp

theorem subN_eq : ∀ n k, subN n k = n - k
  | n, 0 => by simp [subN]
  | 0, k + 1 => by simp [subN]
  | n + 1, k + 1 => by simp [subN, subN_eq n k]

theorem hi_eq (j : Nat) : ((natW j) >>> 8).toUInt8 = (j / 256).toUInt8 := by
  rw [natW_eq]
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toUInt8, UInt64.toNat_shiftRight, Nat.toUInt8, UInt64.toNat_ofNat]
  simp [Nat.shiftRight_eq_div_pow]
  omega

theorem lo_eq (j : Nat) : (natW j).toUInt8 = (j % 256).toUInt8 := by
  rw [← u8N, u8N_eq]
  apply UInt8.toNat_inj.mp
  simp

/-! ## the token decoder -/

/-- `Option.map (t :: ·)` without a lambda -/
def consO (t : Tok) : Option (List Tok) → Option (List Tok)
  | some l => some (t :: l)
  | none => none

def decS : List UInt8 → List UInt8 → Option UInt64 → Option (List Tok)
  | [], [], none => some []
  | [], _, _ => none
  | b :: r, _, some a =>
    if b == 6 then consO (Tok.num a) (decS r [] none)
    else if 48 ≤ b && b ≤ 57 then decS r [] (some (a * 10 + (b.toUInt64 - 48))) else none
  | b :: r, wd, none =>
    if isW b then decS r (b :: wd) none
    else if !wd.isEmpty then
      if b == 0 then consO (Tok.id wd.reverse) (decS r [] none)
      else if b == 1 then consO Tok.kdef (decS r [] none)
      else if b == 2 then consO Tok.klet (decS r [] none)
      else if b == 3 then consO (Tok.kty false) (decS r [] none)
      else if b == 4 then consO (Tok.kty true) (decS r [] none)
      else none
    else if b == 5 then decS r [] (some 0)
    else if b == 40 then consO Tok.lp (decS r [] none)
    else if b == 41 then consO Tok.rp (decS r [] none)
    else if b == 42 then consO Tok.star (decS r [] none)
    else if b == 43 then consO Tok.plus (decS r [] none)
    else if b == 45 then consO Tok.minus (decS r [] none)
    else if b == 58 then consO Tok.colon (decS r [] none)
    else if b == 59 then consO Tok.semi (decS r [] none)
    else if b == 61 then consO Tok.assign (decS r [] none)
    else none

theorem consO_eq (t : Tok) (o : Option (List Tok)) : consO t o = o.map (t :: ·) := by cases o <;> rfl

theorem sub48 (b : UInt8) (h : (48 ≤ b && b ≤ 57) = true) : (b - 48).toUInt64 = b.toUInt64 - 48 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : 48 ≤ b.toNat := (UInt8.le_iff_toNat_le).1 h.1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using h1), UInt8.toNat_toUInt64,
    UInt8.toNat_toUInt64, UInt8.toNat_sub_of_le _ _ h.1]
  rfl

theorem decS_eq : ∀ bs wd o, decS bs wd o = dec bs wd o
  | [], [], none => rfl
  | [], _ :: _, none => rfl
  | [], _, some _ => by cases ‹List UInt8› <;> rfl
  | b :: r, wd, some a => by
    rw [decS, dec]
    by_cases hd : (48 ≤ b && b ≤ 57) = true
    · rw [sub48 b hd]; simp only [consO_eq, decS_eq r]
    · simp only [hd, consO_eq, decS_eq r, if_false, Bool.false_eq_true]
  | b :: r, wd, none => by
    rw [decS, dec]
    simp only [consO_eq, decS_eq r]

/-- `decL` -/
def decLS : List UInt8 → Option (Bool × List Tok)
  | 1 :: r => (decS r [] none).map (false, ·)
  | 2 :: r => (decS r [] none).map (true, ·)
  | _ => none

theorem decLS_eq (bs : List UInt8) : decLS bs = decL bs := by
  unfold decLS decL
  simp only [decS_eq]
  repeat' split
  all_goals simp_all

/-! ## the machine -/

def sCallS (j k : Nat) : List UInt8 := mo 14 ((natW j) >>> 8).toUInt8 ++ mo 15 (natW j).toUInt8 ++ mo 9 (u8N k)
def sVarS (d k : Nat) : List UInt8 := mo 7 (u8N (subN (subN d 1) k)) ++ mo 3 0

theorem sCallS_eq (j k : Nat) : sCallS j k = sCall j k := by
  simp only [sCallS, sCall, hi_eq, lo_eq, u8N_eq]
theorem sVarS_eq (d k : Nat) : sVarS d k = sVar d k := by
  simp only [sVarS, sVar, u8N_eq, subN_eq]

def retFS (s : St) : Fr → List Fr → Res
  | .letV f x, K =>
    match s.ts with
    | Tok.semi :: r => .go (.expr f) { s with ts := r, sc := (x, subN s.d 1) :: s.sc, K := .letB :: K }
    | _ => .fail
  | .letB, K => .go .ret { s with out := s.out ++ mo 9 1, d := subN s.d 1, sc := s.sc.tail, K := K }
  | .exprAdd f, K => .go (.add f) { s with K := K }
  | .addOp f op, K => .go (.add f) { s with out := s.out ++ mo 8 op, d := subN s.d 1, K := K }
  | .mulT f, K => .go (.mulT f) { s with K := K }
  | .mulOp f, K => .go (.mulT f) { s with out := s.out ++ mo 8 40, d := subN s.d 1, K := K }
  | .call j k, K => .go .ret { s with out := s.out ++ sCallS j k, d := subN (s.d + 1) k, K := K }
  | .args f k, K => .go (.args f k) { s with K := K }
  | .paren, K =>
    match s.ts with
    | Tok.rp :: r => .go .ret { s with ts := r, K := K }
    | _ => .fail

theorem retFS_eq (s : St) (fr : Fr) (K : List Fr) : retFS s fr K = retF s fr K := by
  cases fr <;> simp only [retFS, retF, subN_eq, sCallS_eq] <;> (repeat' split) <;> simp_all

def endDefS (s : St) : Res :=
  match s.ts with
  | [] => .done (s.out ++ mo 13 (u8N s.na))
  | _ => .go (.defs s.cf) { s with out := s.out ++ mo 13 (u8N s.na), ds := (s.cg, s.na, s.ds.length) :: s.ds }

theorem endDefS_eq (s : St) : endDefS s = endDef s := by
  simp only [endDefS, endDef, u8N_eq]
  repeat' split
  all_goals simp_all

def stepS : Ctl → St → Res
  | .defs f, s =>
    match f, s.ts with
    | f + 1, Tok.kdef :: Tok.id g :: ts => .go (.params f 0) { s with ts := ts, cg := g, cf := f, sc := [] }
    | _, _ => .fail
  | .params f n, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.lp :: ts => .go (.names f f n) { s with ts := ts }
    | _ + 1, _ => .go .dbody { s with na := n }
  | .names f fp n, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.id x :: ts => .go (.names f fp (n + 1)) { s with ts := ts, sc := (x, n) :: s.sc }
    | _ + 1, Tok.colon :: Tok.kty _ :: Tok.rp :: ts => .go (.params fp n) { s with ts := ts }
    | _, _ => .fail
  | .dbody, s =>
    match s.ts with
    | Tok.colon :: Tok.kty _ :: Tok.assign :: r =>
      match findD s.cg s.ds with
      | some _ => .fail
      | none => .go (.expr s.cf) { s with ts := r, d := s.na, K := [] }
    | _ => .fail
  | .ret, s =>
    match s.K with
    | [] => endDefS s
    | fr :: K => retFS s fr K
  | .expr f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.klet :: Tok.id x :: Tok.assign :: ts => .go (.expr f) { s with ts := ts, K := .letV f x :: s.K }
    | f + 1, _ => .go (.mul f) { s with K := .exprAdd f :: s.K }
  | .add f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.plus :: ts => .go (.mul f) { s with ts := ts, K := .addOp f 24 :: s.K }
    | f + 1, Tok.minus :: ts => .go (.mul f) { s with ts := ts, K := .addOp f 32 :: s.K }
    | _ + 1, _ => .go .ret s
  | .mul f, s =>
    match f with
    | 0 => .fail
    | f + 1 => .go (.app f) { s with K := .mulT f :: s.K }
  | .mulT f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.star :: ts => .go (.app f) { s with ts := ts, K := .mulOp f :: s.K }
    | _ + 1, _ => .go .ret s
  | .app f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.id g :: ts =>
      match lookS g s.sc with
      | some k => .go .ret { s with ts := ts, out := s.out ++ sVarS s.d k, d := s.d + 1 }
      | none =>
        match findD g s.ds with
        | some (k, j) => .go (.args f k) { s with ts := ts, K := .call j k :: s.K }
        | none => .fail
    | _ + 1, Tok.minus :: Tok.num n :: ts =>
      .go .ret { s with ts := ts, out := s.out ++ (sLi (0 - n) ++ mo 3 0), d := s.d + 1 }
    | f + 1, _ => .go (.atom f) s
  | .args f k, s =>
    match f, k with
    | 0, _ => .fail
    | _ + 1, 0 => .go .ret s
    | f + 1, k + 1 => .go (.atom f) { s with K := .args f k :: s.K }
  | .atom f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | _ + 1, Tok.num n :: ts => .go .ret { s with ts := ts, out := s.out ++ (sLi n ++ mo 3 0), d := s.d + 1 }
    | _ + 1, Tok.id g :: ts =>
      match lookS g s.sc with
      | some k => .go .ret { s with ts := ts, out := s.out ++ sVarS s.d k, d := s.d + 1 }
      | none =>
        match findD g s.ds with
        | some (0, j) => .go .ret { s with ts := ts, out := s.out ++ sCallS j 0, d := s.d + 1 }
        | _ => .fail
    | f + 1, Tok.lp :: ts => .go (.expr f) { s with ts := ts, K := .paren :: s.K }
    | _, _ => .fail

theorem stepS_eq (c : Ctl) (s : St) : stepS c s = step c s := by
  cases c <;> simp only [stepS, step, sVarS_eq, sCallS_eq, endDefS_eq, retFS_eq] <;> (repeat' split) <;> simp_all

def runS : Nat → Ctl → St → Option (List UInt8)
  | 0, _, _ => none
  | g + 1, c, s =>
    match stepS c s with
    | .go c' s' => runS g c' s'
    | .done o => some o
    | .fail => none

theorem runS_eq : ∀ g c s, runS g c s = run g c s
  | 0, _, _ => rfl
  | g + 1, c, s => by
    simp only [runS, run, stepS_eq]
    cases step c s <;> simp [runS_eq g]

/-- `gasOf` -/
def gasS : List Tok → Nat
  | [] => 6
  | _ :: r => gasS r + 13

theorem gasS_eq : ∀ ts, gasS ts = gasOf ts
  | [] => rfl
  | _ :: r => by simp only [gasS, gasS_eq r, gasOf, List.length_cons]; omega

/-- **stage 2, S3 form** -/
def stage2S (bs : List UInt8) : List UInt8 :=
  match decLS bs with
  | some (_, ts) => (runS (gasS ts) (.defs (ts.length + 1)) (st0 ts)).getD []
  | none => []

/-- **the bridge**: the S3 form is stage 2, on every input -/
theorem stage2S_eq (bs : List UInt8) : stage2S bs = stage2 bs := by
  unfold stage2S stage2
  rw [decLS_eq]
  cases decL bs with
  | none => rfl
  | some p => obtain ⟨_, ts⟩ := p; simp [runS_eq, gasS_eq, parseA]

end Nano.PS
