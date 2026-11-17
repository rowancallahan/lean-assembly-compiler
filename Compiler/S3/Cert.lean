/- **The bridge from Lean functions to S3 programs** (`Testing/notes/IR_S3.md`).

* `Enc α`: how a Lean value is an S3 value (`enc`, with a left inverse `dec`); instances for `UInt64`, `UInt8`,
  `Int64`, `Bool`, lists, pairs, options; a front end adds one per user datatype / structure.  A byte list is the
  input / output value of a program (`enc_bytes`).
* `evalO P φ env e`: evaluation of ONE body with every call answered by the oracle `φ` (no recursion, so it is a
  plain structural function that `simp` runs), and `CallsOk`: every call it made has, in `P`'s meaning, the value
  `φ` gave.  `evalO_sound`: then `Ev P env e v`.  The per-function certificate `∀ x, Ev P [enc x] (body f) (enc (f x))`
  is proved with `φ` = the Lean functions, by the Lean function's own (functional) induction: the recursive calls
  are the induction hypotheses, calls of earlier functions their certificates.  Termination is the Lean function's.
* `computes_of_main`: the certificate of `main` (a byte-list function `encOut ∘ f ∘ decIn`) gives
  `Computes P f encIn encOut`, the hypothesis of `S3.compile_correct`. -/
import Compiler.S3.Syntax
import Compiler.S3.SimpAttr

namespace Proven.S3
set_option autoImplicit false

/-! ## evaluation of one body with an oracle -/

section
variable (S : Sig) (φ : Fin S.fns.length → List V → V)

def evalO : {Γ : List Ty} → {τ : Ty} → List V → Expr S Γ τ → Option V
  | _, _, env, .var x => env[x.idx]?
  | _, _, _, .lit c => some (.w c)
  | _, _, _, .blit c => some (.w (bv c))
  | _, _, env, .bin o a b => match env[a.idx]?, env[b.idx]? with
    | some (.w x), some (.w y) => some (.w (o.eval x y))
    | _, _ => none
  | _, _, env, .cmp c a b => match env[a.idx]?, env[b.idx]? with
    | some (.w x), some (.w y) => some (.w (bv (c.eval x y)))
    | _, _ => none
  | _, _, env, .bnot a => match env[a.idx]? with
    | some (.w x) => some (.w (x ^^^ 1))
    | _ => none
  | _, _, env, .let_ e₁ e₂ => match evalO env e₁ with
    | some v₁ => evalO (v₁ :: env) e₂
    | none => none
  | _, _, env, .ite c e₁ e₂ => match env[c.idx]? with
    | some (.w x) => if x = 0 then evalO env e₂ else evalO env e₁
    | _ => none
  | _, _, env, .mk _ j xs => (xs.get env).map (.c j)
  | _, _, env, .cas (i := i) x arms => match env[x.idx]? with
    | some (.c j fs) => if h : j < S.nc i then
        (if fs.length = (S.fld i ⟨j, h⟩).length then evalO (fs ++ env) (arms ⟨j, h⟩) else none) else none
    | _ => none
  | _, _, env, .call f xs _ => (xs.get env).map (φ f)

variable (R : Fin S.fns.length → List V → Prop)

/-- every call that `evalO` made satisfies `R` (used with `R f vs` = "the call of `f` on `vs` has the value
`φ f vs`", `Good`) -/
def CallsOk : {Γ : List Ty} → {τ : Ty} → List V → Expr S Γ τ → Prop
  | _, _, env, .let_ e₁ e₂ => CallsOk env e₁ ∧ (match evalO S φ env e₁ with
    | some v₁ => CallsOk (v₁ :: env) e₂
    | none => True)
  | _, _, env, .ite c e₁ e₂ => match env[c.idx]? with
    | some (.w x) => if x = 0 then CallsOk env e₂ else CallsOk env e₁
    | _ => True
  | _, _, env, .cas (i := i) x arms => match env[x.idx]? with
    | some (.c j fs) => if h : j < S.nc i then CallsOk (fs ++ env) (arms ⟨j, h⟩) else True
    | _ => True
  | _, _, env, .call f xs _ => match xs.get env with
    | some vs => R f vs
    | none => True
  | _, _, _, _ => True

end

section
variable (P : Prog) (φ : Fin P.S.fns.length → List V → V)

/-- **the call of `f` on `vs` has, in `P`'s meaning, the value the oracle gives** -/
def Good (f : Fin P.S.fns.length) (vs : List V) : Prop := Ev P vs (P.body f) (φ f vs)

/-- **the oracle evaluation is sound** -/
theorem evalO_sound : ∀ {Γ : List Ty} {τ : Ty} (e : Expr P.S Γ τ) (env : List V) (v : V),
    evalO P.S φ env e = some v → CallsOk P.S φ (Good P φ) env e → Ev P env e v
  | _, _, .var x, env, v, h, _ => .var h
  | _, _, .lit c, env, v, h, _ => by simp [evalO] at h; subst h; exact .lit
  | _, _, .blit c, env, v, h, _ => by simp [evalO] at h; subst h; exact .blit
  | _, _, .bin o a b, env, v, h, _ => by
    simp only [evalO] at h
    split at h
    · next x y ha hb => cases h; exact .bin ha hb
    · exact nomatch h
  | _, _, .cmp c a b, env, v, h, _ => by
    simp only [evalO] at h
    split at h
    · next x y ha hb => cases h; exact .cmp ha hb
    · exact nomatch h
  | _, _, .bnot a, env, v, h, _ => by
    simp only [evalO] at h
    split at h
    · next x ha => cases h; exact .bnot ha
    · exact nomatch h
  | _, _, .let_ e₁ e₂, env, v, h, hc => by
    simp only [evalO] at h
    simp only [CallsOk] at hc
    split at h
    · next v₁ h₁ =>
      rw [h₁] at hc
      exact .let_ (evalO_sound e₁ env v₁ h₁ hc.1) (evalO_sound e₂ _ v h hc.2)
    · exact nomatch h
  | _, _, .ite c e₁ e₂, env, v, h, hc => by
    simp only [evalO] at h
    simp only [CallsOk] at hc
    split at h
    · next x hx =>
      rw [hx] at hc
      simp only at hc
      by_cases h0 : x = 0
      · subst h0; rw [if_pos rfl] at h hc; exact .iteF hx (evalO_sound e₂ env v h hc)
      · rw [if_neg h0] at h hc; exact .iteT hx h0 (evalO_sound e₁ env v h hc)
    · exact nomatch h
  | _, _, .mk i j xs, env, v, h, _ => by
    simp only [evalO] at h
    cases hx : xs.get env with
    | none => rw [hx] at h; exact nomatch h
    | some vs => rw [hx] at h; cases h; exact .mk hx
  | _, _, .cas x arms, env, v, h, hc => by
    simp only [evalO] at h
    simp only [CallsOk] at hc
    split at h
    · next j fs hx =>
      rw [hx] at hc
      simp only at hc
      split at h
      · next hj =>
        rw [dif_pos hj] at hc
        split at h
        · next hl => exact .cas hj hx hl (evalO_sound _ _ v h hc)
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  | _, _, .call f xs _, env, v, h, hc => by
    simp only [evalO] at h
    simp only [CallsOk] at hc
    cases hx : xs.get env with
    | none => rw [hx] at h; exact nomatch h
    | some vs => rw [hx] at h hc; cases h; exact .call hx hc

/-- **the certificate of one call**: its body, evaluated with the oracle, gives the oracle's value, and every call
it makes is good -/
theorem good_intro {f : Fin P.S.fns.length} {vs : List V} (h : evalO P.S φ vs (P.body f) = some (φ f vs))
    (hc : CallsOk P.S φ (Good P φ) vs (P.body f)) : Good P φ f vs :=
  evalO_sound P φ _ vs _ h hc

end

/-! ## encodings of Lean values -/

/-- a Lean type as S3 values -/
class Enc (α : Type) where
  enc : α → V
  dec : V → α
  dec_enc : ∀ x, dec (enc x) = x

attribute [simp] Enc.dec_enc

instance : Enc UInt64 where
  enc x := .w x.toBitVec
  dec | .w x => UInt64.ofBitVec x | _ => 0
  dec_enc _ := rfl

instance : Enc Int64 where
  enc x := .w x.toBitVec
  dec | .w x => Int64.ofBitVec x | _ => 0
  dec_enc _ := rfl

instance : Enc UInt8 where
  enc x := .w (x.toBitVec.setWidth 64)
  dec | .w x => UInt8.ofBitVec (x.setWidth 8) | _ => 0
  dec_enc x := by
    show UInt8.ofBitVec ((x.toBitVec.setWidth 64).setWidth 8) = x
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]; simp

instance : Enc Bool where
  enc b := .w (bv b)
  dec | .w x => x != 0 | _ => false
  dec_enc b := by cases b <;> decide

def encList {α : Type} [Enc α] : List α → V
  | [] => .c 0 []
  | a :: l => .c 1 [Enc.enc a, encList l]

def decList {α : Type} [Enc α] : V → List α
  | .c 1 [a, l] => Enc.dec a :: decList l
  | _ => []

instance {α : Type} [Enc α] : Enc (List α) where
  enc := encList
  dec := decList
  dec_enc l := by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [encList, decList, Enc.dec_enc, ih]

instance {α β : Type} [Enc α] [Enc β] : Enc (α × β) where
  enc p := .c 0 [Enc.enc p.1, Enc.enc p.2]
  dec | .c 0 [a, b] => (Enc.dec a, Enc.dec b) | _ => (Enc.dec (.w 0), Enc.dec (.w 0))
  dec_enc p := by simp

instance {α : Type} [Enc α] : Enc (Option α) where
  enc | none => .c 0 [] | some a => .c 1 [Enc.enc a]
  dec | .c 1 [a] => some (Enc.dec a) | _ => none
  dec_enc o := by cases o <;> simp

instance : Enc Unit where
  enc _ := .c 0 []
  dec _ := ()
  dec_enc _ := rfl

instance : Enc (BitVec 64) where
  enc x := .w x
  dec | .w x => x | _ => 0
  dec_enc _ := rfl

/-- `Nat` as its own inductive type (unary: `zero`, `succ`): exact, values cost their size -/
def natV : Nat → V
  | 0 => .c 0 []
  | n + 1 => .c 1 [natV n]

def natD : V → Nat
  | .c 1 [v] => natD v + 1
  | _ => 0

instance : Enc Nat where
  enc := natV
  dec := natD
  dec_enc n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [natV, natD, ih]

@[simp] theorem enc_bv64 (x : BitVec 64) : Enc.enc x = .w x := rfl
@[simp] theorem dec_bv64 (x : BitVec 64) : (Enc.dec (V.w x) : BitVec 64) = x := rfl
@[simp] theorem enc_nat_zero : Enc.enc (0 : Nat) = .c 0 [] := rfl
@[simp] theorem enc_nat_zero' : Enc.enc Nat.zero = .c 0 [] := rfl
@[simp] theorem enc_nat_succ (n : Nat) : Enc.enc (n + 1) = .c 1 [Enc.enc n] := rfl
@[simp] theorem enc_nat_succ' (n : Nat) : Enc.enc (Nat.succ n) = .c 1 [Enc.enc n] := rfl
@[simp] theorem dec_nat_zero : (Enc.dec (V.c 0 []) : Nat) = 0 := rfl
@[simp] theorem dec_nat_succ (v : V) : (Enc.dec (V.c 1 [v]) : Nat) = Enc.dec v + 1 := rfl
attribute [s3_norm] Nat.beq_eq Nat.add_eq Nat.succ_eq_add_one Bool.or_eq_true Bool.and_eq_true
@[s3_norm] theorem nat_beq_false (a b : Nat) : (Nat.beq a b = false) = ¬ a = b := by
  rw [← Nat.beq_eq, Bool.not_eq_true]
@[s3_norm] theorem nat_blt_false (a b : Nat) : (Nat.blt a b = false) = ¬ a < b := by
  rw [← Nat.blt_eq, Bool.not_eq_true]
@[s3_norm] theorem nat_ble_false (a b : Nat) : (Nat.ble a b = false) = ¬ a ≤ b := by
  rw [← Nat.ble_eq, Bool.not_eq_true]

instance instEncExceptT {ε α : Type} {m : Type → Type} [h : Enc (m (Except ε α))] : Enc (ExceptT ε m α) := h

@[simp] theorem enc_exceptT {ε α : Type} {m : Type → Type} [h : Enc (m (Except ε α))] (x : ExceptT ε m α) :
    @Enc.enc (ExceptT ε m α) instEncExceptT x = @Enc.enc (m (Except ε α)) h x.run := rfl
@[simp] theorem dec_exceptT {ε α : Type} {m : Type → Type} [h : Enc (m (Except ε α))] (v : V) :
    @Enc.dec (ExceptT ε m α) instEncExceptT v = ExceptT.mk (@Enc.dec (m (Except ε α)) h v) := rfl

@[simp] theorem enc_unit (u : Unit) : Enc.enc u = .c 0 [] := rfl
@[simp] theorem dec_unit (v : V) : (Enc.dec v : Unit) = () := rfl

@[simp] theorem enc_u64 (x : UInt64) : Enc.enc x = .w x.toBitVec := rfl
@[simp] theorem enc_i64 (x : Int64) : Enc.enc x = .w x.toBitVec := rfl
@[simp] theorem enc_u8 (x : UInt8) : Enc.enc x = .w (x.toBitVec.setWidth 64) := rfl
@[simp] theorem enc_bool (x : Bool) : Enc.enc x = .w (bv x) := rfl
@[simp] theorem enc_nil {α : Type} [Enc α] : Enc.enc ([] : List α) = .c 0 [] := rfl
@[simp] theorem enc_cons {α : Type} [Enc α] (a : α) (l : List α) : Enc.enc (a :: l) = .c 1 [Enc.enc a, Enc.enc l] := rfl
@[simp] theorem enc_pair {α β : Type} [Enc α] [Enc β] (a : α) (b : β) : Enc.enc (a, b) = .c 0 [Enc.enc a, Enc.enc b] := rfl
@[simp] theorem enc_none {α : Type} [Enc α] : Enc.enc (none : Option α) = .c 0 [] := rfl
@[simp] theorem enc_some {α : Type} [Enc α] (a : α) : Enc.enc (some a) = .c 1 [Enc.enc a] := rfl

@[simp] theorem dec_u64 (x : BitVec 64) : (Enc.dec (V.w x) : UInt64) = UInt64.ofBitVec x := rfl
@[simp] theorem dec_i64 (x : BitVec 64) : (Enc.dec (V.w x) : Int64) = Int64.ofBitVec x := rfl
@[simp] theorem dec_u8 (x : BitVec 64) : (Enc.dec (V.w x) : UInt8) = UInt8.ofBitVec (x.setWidth 8) := rfl
@[simp] theorem dec_bool (x : BitVec 64) : (Enc.dec (V.w x) : Bool) = (x != 0) := rfl
@[simp] theorem dec_nil {α : Type} [Enc α] : (Enc.dec (V.c 0 []) : List α) = [] := rfl
@[simp] theorem dec_cons {α : Type} [Enc α] (a l : V) : (Enc.dec (V.c 1 [a, l]) : List α) = Enc.dec a :: Enc.dec l := rfl
@[simp] theorem dec_pair {α β : Type} [Enc α] [Enc β] (a b : V) :
    (Enc.dec (V.c 0 [a, b]) : α × β) = (Enc.dec a, Enc.dec b) := rfl
@[simp] theorem dec_none {α : Type} [Enc α] : (Enc.dec (V.c 0 []) : Option α) = none := rfl
@[simp] theorem dec_some {α : Type} [Enc α] (a : V) : (Enc.dec (V.c 1 [a]) : Option α) = some (Enc.dec a) := rfl
@[simp] theorem bv_ne_zero (c : Bool) : (bv c != 0#64) = c := by cases c <;> decide

/-! ### word lemmas for the certificates -/

@[simp] theorem setWidth_8_64 (x : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 8 x) = x &&& 255 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
  rw [show (255 : BitVec 64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

@[simp] theorem u8_bv (b : UInt8) : (BitVec.setWidth 64 b.toBitVec).toNat = b.toNat := by
  simp [BitVec.toNat_setWidth]
@[simp] theorem u8_beq (b : UInt8) (y : BitVec 64) : (BitVec.setWidth 64 b.toBitVec == y) = (b.toNat == y.toNat) := by
  rw [Bool.eq_iff_iff]; simp [← BitVec.toNat_inj]
@[simp] theorem u8_eq_bv (b : UInt8) (y : BitVec 64) : (BitVec.setWidth 64 b.toBitVec = y) ↔ b.toNat = y.toNat := by
  simp [← BitVec.toNat_inj]
@[simp] theorem u8_lt (b : UInt8) (y : BitVec 64) : (BitVec.setWidth 64 b.toBitVec < y) ↔ b.toNat < y.toNat := by
  simp [BitVec.lt_def]
@[simp] theorem u8_lt' (b : UInt8) (y : BitVec 64) : (y < BitVec.setWidth 64 b.toBitVec) ↔ y.toNat < b.toNat := by
  simp [BitVec.lt_def]
@[simp] theorem u8_le (b : UInt8) (y : BitVec 64) : (BitVec.setWidth 64 b.toBitVec ≤ y) ↔ b.toNat ≤ y.toNat := by
  simp [BitVec.le_def]
@[simp] theorem u8_le' (b : UInt8) (y : BitVec 64) : (y ≤ BitVec.setWidth 64 b.toBitVec) ↔ y.toNat ≤ b.toNat := by
  simp [BitVec.le_def]

@[s3_norm] theorem u8_beq_toNat (a b : UInt8) : (a == b) = (a.toNat == b.toNat) := by
  rw [Bool.eq_iff_iff]; simp [UInt8.toNat_inj]
@[s3_norm] theorem u8_bne_toNat (a b : UInt8) : (a != b) = !(a.toNat == b.toNat) := by
  rw [bne, u8_beq_toNat]
@[simp] theorem u8_bne (b : UInt8) (y : BitVec 64) : (BitVec.setWidth 64 b.toBitVec != y) = !(b.toNat == y.toNat) := by
  rw [bne, u8_beq]
@[s3_norm] theorem u8_eq_iff (a b : UInt8) : (a = b) = (a.toNat = b.toNat) := by
  simp [UInt8.toNat_inj]
@[s3_norm] theorem u8_lt_iff (a b : UInt8) : (a < b) = (a.toNat < b.toNat) := by
  simp [UInt8.lt_iff_toNat_lt]
@[s3_norm] theorem u8_le_iff (a b : UInt8) : (a ≤ b) = (a.toNat ≤ b.toNat) := by
  simp [UInt8.le_iff_toNat_le]
@[s3_norm] theorem u8_toNat_lit (n : Nat) : (OfNat.ofNat n : UInt8).toNat = n % 256 := rfl
@[s3_norm] theorem u64_beq_bv (a b : UInt64) : (a == b) = (a.toBitVec == b.toBitVec) := by
  rw [Bool.eq_iff_iff]; simp [UInt64.toBitVec_inj]
@[s3_norm] theorem u64_eq_iff (a b : UInt64) : (a = b) = (a.toBitVec = b.toBitVec) := by
  simp [UInt64.toBitVec_inj]
@[s3_norm] theorem u64_lt_iff (a b : UInt64) : (a < b) = (a.toBitVec < b.toBitVec) := rfl
@[s3_norm] theorem u64_le_iff (a b : UInt64) : (a ≤ b) = (a.toBitVec ≤ b.toBitVec) := rfl
@[s3_norm, simp] theorem bv64_beq_decide (a b : BitVec 64) : (a == b) = decide (a = b) := by
  cases h : decide (a = b) <;> simp_all
@[simp] theorem failure_option {α : Type} : (failure : Option α) = none := rfl
@[simp] theorem pure_option {α : Type} (a : α) : (pure a : Option α) = some a := rfl
@[simp] theorem bv_xor_one (c : Bool) : bv c ^^^ 1#64 = bv (!c) := by cases c <;> decide
@[simp] theorem bv_eq_zero (c : Bool) : (bv c = 0#64) = (c = false) := by cases c <;> decide
@[simp] theorem bv_eq_one (c : Bool) : (bv c = 1#64) = (c = true) := by cases c <;> decide
attribute [s3_norm] UInt8.toNat_zero
attribute [s3_norm] UInt64.toBitVec_ofNat

@[simp] theorem u8_and_ff (x : UInt8) : (x &&& @OfNat.ofNat UInt8 (255 : Nat) UInt8.instOfNat) = x := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and]
  show x.toNat &&& 255 = x.toNat
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt x.toNat_lt

/-- a byte list is the input / output value -/
theorem enc_bytes : ∀ l : List UInt8, Enc.enc l = bytesV l
  | [] => rfl
  | b :: l => by simp [bytesV, enc_bytes l]

theorem bytesOut_bytesV : ∀ l : List UInt8, bytesOut (bytesV l) = some l
  | [] => rfl
  | b :: l => by
    simp only [bytesV, bytesOut, bytesOut_bytesV l, Option.map_some]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]; simp

/-! ## the bridge -/

/-- **from the certificate of `main` to `Computes`**: if `main` computes the byte-list function `mainL`, and
`mainL` maps the encoding of `x` to the encoding of `f x`, then `P` computes `f` -/
theorem computes_of_main {P : Prog} {φ : Fin P.S.fns.length → List V → V} {α β : Type} (f : α → β)
    (encIn : α → List UInt8) (encOut : β → List UInt8)
    (mainL : List UInt8 → List UInt8) (hmain : ∀ x, mainL (encIn x) = encOut (f x))
    (hφ : ∀ bs : List UInt8, φ P.main [Enc.enc bs] = Enc.enc (mainL bs))
    (cert : ∀ bs : List UInt8, Good P φ P.main [Enc.enc bs]) :
    Proven.Top.Computes P f encIn encOut := by
  intro x
  have h : Ev P [Enc.enc (encIn x)] (P.body P.main) (Enc.enc (mainL (encIn x))) := by
    have := cert (encIn x); unfold Good at this; rwa [hφ] at this
  rw [enc_bytes, enc_bytes, hmain] at h
  show P.run (encIn x) = _
  rw [Prog.run_eq h, bytesOut_bytesV]

/-- **the termination certificate from the certificates**: every good call has a well-founded call tree -/
theorem wfCert_of_good (P : Prog) (φ : Fin P.S.fns.length → List V → V) : WfCert P (Good P φ) :=
  ⟨fun _ _ h => acc_of_ev h⟩

end Proven.S3
