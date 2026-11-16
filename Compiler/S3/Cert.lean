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

variable (R : Fin S.fns.length → List V → V → Prop)

/-- every call that `evalO` made has the value `φ` gave it (`R`: the meaning of calls) -/
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
    | some vs => R f vs (φ f vs)
    | none => True
  | _, _, _, _ => True

end

/-- the meaning of calls in `P` -/
def EvF (P : Prog) (f : Fin P.S.fns.length) (vs : List V) (v : V) : Prop := Ev P vs (P.body f) v

section
variable (P : Prog) (φ : Fin P.S.fns.length → List V → V)

/-- **the oracle evaluation is sound** -/
theorem evalO_sound : ∀ {Γ : List Ty} {τ : Ty} (e : Expr P.S Γ τ) (env : List V) (v : V),
    evalO P.S φ env e = some v → CallsOk P.S φ (EvF P) env e → Ev P env e v
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

@[simp] theorem enc_u64 (x : UInt64) : Enc.enc x = .w x.toBitVec := rfl
@[simp] theorem enc_i64 (x : Int64) : Enc.enc x = .w x.toBitVec := rfl
@[simp] theorem enc_u8 (x : UInt8) : Enc.enc x = .w (x.toBitVec.setWidth 64) := rfl
@[simp] theorem enc_bool (x : Bool) : Enc.enc x = .w (bv x) := rfl
@[simp] theorem enc_nil {α : Type} [Enc α] : Enc.enc ([] : List α) = .c 0 [] := rfl
@[simp] theorem enc_cons {α : Type} [Enc α] (a : α) (l : List α) : Enc.enc (a :: l) = .c 1 [Enc.enc a, Enc.enc l] := rfl
@[simp] theorem enc_pair {α β : Type} [Enc α] [Enc β] (a : α) (b : β) : Enc.enc (a, b) = .c 0 [Enc.enc a, Enc.enc b] := rfl
@[simp] theorem enc_none {α : Type} [Enc α] : Enc.enc (none : Option α) = .c 0 [] := rfl
@[simp] theorem enc_some {α : Type} [Enc α] (a : α) : Enc.enc (some a) = .c 1 [Enc.enc a] := rfl

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
theorem computes_of_main {P : Prog} {α β : Type} (f : α → β) (encIn : α → List UInt8) (encOut : β → List UInt8)
    (mainL : List UInt8 → List UInt8) (hmain : ∀ x, mainL (encIn x) = encOut (f x))
    (cert : ∀ bs : List UInt8, Ev P [Enc.enc bs] (P.body P.main) (Enc.enc (mainL bs))) :
    Proven.Top.Computes P f encIn encOut := by
  intro x
  have h := cert (encIn x)
  rw [enc_bytes, enc_bytes, hmain] at h
  show P.run (encIn x) = _
  rw [Prog.run_eq h, bytesOut_bytesV]

end Proven.S3
