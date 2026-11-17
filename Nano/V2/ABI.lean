import Nano.V2.Front
/- nano v2 increment 6 (result/status + the contract), definitions: the byte-level contract `ImplementsBytes`
(NANO_V2_SPEC §8, verbatim from Testing/notes/NANO_V2_SKELETONS.lean `NanoABI`), the program's `Result`
(`Prog.result`), and the front end's status convention: Lean's empty output ↦ `error 1` (`mainProg_eval`).
The theorem `compile_correct : gen p = some B → ImplementsBytes M B p.result` needs the Sail refinement of the
abstract machine (layers 3–4 of NANO_V2_BACKEND.md): NOT yet. -/
namespace Nano.V2B.ABI

abbrev Bytes := Array UInt8
inductive Result where
  | ok (out : Bytes)
  | error (code : UInt64)
  deriving DecidableEq, Repr

-- Adapters to the actual Sail model, not a new machine semantics.
structure Model where
  State : Type
  reg : State → Nat → UInt64
  readByte : State → UInt64 → UInt8
  status : State → UInt64
  oom : State → Bool
  oomCode : UInt64
  Runs : Bytes → State → State → Prop
  -- every maximal permitted execution reaches the return boundary (no stuck/infinite executions)
  AllReturn : Bytes → State → Prop
  initExtra : Bytes → Bytes → UInt64 → UInt64 → State → Prop
  frame : State → State → Prop

def Initial (M : Model) (B input : Bytes) (ip op : UInt64) (s : M.State) : Prop :=
  input.size < 2^64 ∧
  ip.toNat + input.size ≤ 2^64 ∧
  M.reg s 10 = ip ∧
  M.reg s 11 = UInt64.ofNat input.size ∧
  M.reg s 13 = op ∧
  (∀ i (h : i < input.size), M.readByte s (ip + UInt64.ofNat i) = input[i]) ∧
  M.initExtra B input ip op s

def Observes (M : Model) (op : UInt64) (r : Result) (s : M.State) : Prop :=
  match r with
  | .ok out =>
    M.status s = 0 ∧ M.oom s = false ∧
    out.size < 2^64 ∧ op.toNat + out.size ≤ 2^64 ∧
    M.reg s 11 = UInt64.ofNat out.size ∧
    (∀ i (h : i < out.size), M.readByte s (op + UInt64.ofNat i) = out[i])
  | .error code =>
    code ≠ 0 ∧ M.status s = code ∧
    M.oom s = decide (code = M.oomCode) ∧ M.reg s 11 = 0

def ImplementsBytes (M : Model) (B : Bytes) (Cκ : Bytes → Result) : Prop :=
  ∀ input ip op s, Initial M B input ip op s →
    M.AllReturn B s ∧
    (∃ t, M.Runs B s t) ∧
    (∀ t, M.Runs B s t → Observes M op (Cκ input) t ∧ M.frame s t)

/-- the backend's status/output pair as a `Result` -/
def ofExcept : Except UInt64 (List UInt8) → Result
  | .ok out => .ok out.toArray
  | .error code => .error code

/-- **the program's byte function** -/
def _root_.Nano.V2B.Prog.result (p : Prog) (input : Bytes) : Result := ofExcept (p.eval input.toList)

/-- the front end's main program: the output buffer's words as bytes, or `error 1` when it is empty (Lean's error
convention of the stages: the empty output) -/
theorem mainProg_eval (b : Ex) (input : List UInt8)
    (hl : (den (input.map (·.toUInt64)) b []).list.length < 2 ^ 64) :
    (mainProg b).eval input =
      if (den (input.map (·.toUInt64)) b []).list = [] then .error 1
      else .ok ((den (input.map (·.toUInt64)) b []).list.map (·.toUInt8)) := by
  generalize hv : den (input.map (·.toUInt64)) b [] = v at hl
  simp only [Prog.eval, mainProg, den, hv]
  cases v with
  | bf l =>
    simp only [Val.list] at hl ⊢
    by_cases h : l = []
    · subst h; rfl
    · have h2 : l.length.toUInt64 ≠ 0 := by
        intro e
        have e2 : (UInt64.ofNat l.length).toNat = 0 := by rw [← Nat.toUInt64_eq]; rw [e]; rfl
        simp only [UInt64.toNat_ofNat'] at e2
        rw [Nat.mod_eq_of_lt hl] at e2
        exact h (List.length_eq_zero_iff.mp e2)
      simp [h, h2, Cmp.eval, Val.word, Val.fst, Val.snd, Val.list]
  | wd x => simp [Cmp.eval, Val.word, Val.fst, Val.snd, Val.list]
  | pr a c => simp [Cmp.eval, Val.word, Val.fst, Val.snd, Val.list]

end Nano.V2B.ABI
