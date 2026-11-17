-- Nano v2 proof templates (Astra round 5). VERIFIED on Lean 4.29.0 (this repo toolchain) by the main session,
-- 2026-11-17: no errors; axioms ⊆ {propext, Classical.choice, Quot.sound} (loop_correct, meaning_count: none).
-- Standalone (import Lean only). Copy/adapt; explanations in Testing/notes/NANO_V2_ROUND5.md.
import Lean

namespace NanoSkeleton
abbrev St := UInt64 × Array UInt64
def done (s : St) : Prop := s.1.toNat ≥ s.2.size
instance (s : St) : Decidable (done s) := inferInstanceAs (Decidable (s.1.toNat ≥ s.2.size))
def tick (s : St) : St := (s.1 + 1, s.2)
def scan (fuel : Nat) (s : St) : St :=
  match fuel with
  | 0 => s
  | n + 1 => if done s then s else scan n (tick s)
termination_by structural fuel
@[simp] theorem scan_zero (s : St) : scan 0 s = s := rfl
theorem scan_succ (n : Nat) (s : St) : scan (n+1) s = (if done s then s else scan n (tick s)) := rfl
theorem scan_done (n : Nat) (s : St) (h : done s) : scan n s = s := by
  cases n <;> simp [scan, h]
theorem scan_add (n k : Nat) (s : St) : scan (n+k) s = scan k (scan n s) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add, scan_succ, scan_succ]
    by_cases h : done s
    · simp [h, scan_done k s h]
    · simp only [if_neg h]
      exact ih (tick s)
theorem scan_stable (needed extra : Nat) (s : St) (h : done (scan needed s)) :
    scan (needed + extra) s = scan needed s := by
  rw [scan_add, scan_done extra _ h]
theorem scan_stable_ge (needed fuel : Nat) (s : St)
    (hle : needed ≤ fuel) (h : done (scan needed s)) :
    scan fuel s = scan needed s := by
  have heq : fuel = needed + (fuel - needed) := by omega
  rw [heq]
  exact scan_stable needed (fuel - needed) s h

def splitLet (s : St) : St := let (a,b) := s; (a+1,b)
def splitMatch (s : St) : St := match s with | (a,b) => (a+1,b)
theorem split_same (s : St) : splitLet s = splitMatch s := rfl

def ult (a b : UInt64) : Bool := decide (a < b)
example (a b : UInt64) : (a < b) = (a.toNat < b.toNat) := rfl
example (a b x y : UInt64) : (if a == b then x else y) = (if a = b then x else y) := by
  simp only [beq_iff_eq]
def readD (a : Array UInt64) (i default : UInt64) : UInt64 := a.getD i.toNat default
def writeChecked (a : Array UInt64) (i v : UInt64) : Bool × Array UInt64 :=
  if h : i.toNat < a.size then (true, a.set i.toNat v h) else (false, a)
def appendChecked (cap : UInt64) (a : Array UInt64) (v : UInt64) : Bool × Array UInt64 :=
  if a.size < cap.toNat then (true, a.push v) else (false, a)
theorem append_ok (cap v : UInt64) (a : Array UInt64) (h : a.size < cap.toNat) :
    appendChecked cap a v = (true, a.push v) := by simp [appendChecked, h]

def word (n : Nat) : UInt64 := UInt64.ofNat n
theorem word_toNat (n : Nat) (h : n < 2^64) : (word n).toNat = n := by
  exact UInt64.toNat_ofNat_of_lt' h
theorem word_zero (n : Nat) (h : n < 2^64) : word n = 0 ↔ n = 0 := by
  constructor
  · intro hz
    have he := congrArg UInt64.toNat hz
    simpa [word_toNat n h] using he
  · intro hz; subst n; rfl
theorem word_zero_bool (n : Nat) (h : n < 2^64) : (word n == 0) = true ↔ n = 0 := by
  rw [beq_iff_eq, word_zero n h]
theorem word_pred (n : Nat) (hpos : 0 < n) (h : n < 2^64) : word n - 1 = word (n-1) := by
  apply UInt64.toNat.inj
  have hle : (1 : UInt64) ≤ word n := by
    rw [UInt64.le_iff_toNat_le, word_toNat n h]
    change 1 ≤ n
    omega
  rw [UInt64.toNat_sub_of_le _ _ hle, word_toNat n h,
      word_toNat (n-1) (by omega)]
  rfl
end NanoSkeleton



namespace NanoProofs

-- A. Abstract machine loop.
namespace Loops

inductive Star {M : Type} (Step : M → M → Prop) : M → M → Prop where
  | refl (m : M) : Star Step m m
  | tail {a b c : M} : Step a b → Star Step b c → Star Step a c

namespace Star

theorem trans {M : Type} {Step : M → M → Prop} {a b c : M}
    (hab : Star Step a b) (hbc : Star Step b c) : Star Step a c := by
  induction hab with
  | refl => exact hbc
  | tail h _ ih => exact .tail h (ih hbc)

end Star

inductive Action (S R : Type) where
  | continue (s : S)
  | exit (r : R)

def loopSpec {S R : Type} (zeroResult : S → R) (body : Nat → S → Action S R)
    (fuel : Nat) (s : S) : R :=
  match fuel with
  | 0 => zeroResult s
  | n + 1 =>
    match body n s with
    | .continue s' => loopSpec zeroResult body n s'
    | .exit r => r
termination_by structural fuel

theorem loop_correct {S R M : Type}
    (Step : M → M → Prop)
    (zeroResult : S → R) (body : Nat → S → Action S R)
    (H BodyEntry : Nat → S → M → Prop)
    (ContinueAt : Nat → S → M → Prop)
    (Exit : R → M → Prop)
    (header_zero : ∀ s m, H 0 s m →
      ∃ m', Star Step m m' ∧ Exit (zeroResult s) m')
    (header_nonzero : ∀ n s m, H (n+1) s m →
      ∃ m', Star Step m m' ∧ BodyEntry n s m')
    (body_correct : ∀ n s m, BodyEntry n s m →
      ∃ m', Star Step m m' ∧
        match body n s with
        | .continue s' => ContinueAt n s' m'
        | .exit r => Exit r m')
    (update_backedge : ∀ n s m, ContinueAt n s m →
      ∃ m', Star Step m m' ∧ H n s m') :
    ∀ n s m, H n s m →
      ∃ m', Star Step m m' ∧ Exit (loopSpec zeroResult body n s) m' := by
  intro n
  induction n with
  | zero =>
    intro s m hm
    exact header_zero s m hm
  | succ n ih =>
    intro s m hm
    obtain ⟨m1, h01, hentry⟩ := header_nonzero n s m hm
    obtain ⟨m2, h12, hbody⟩ := body_correct n s m1 hentry
    cases hb : body n s with
    | exit r =>
      have hexit : Exit r m2 := by simpa only [hb] using hbody
      refine ⟨m2, Star.trans h01 h12, ?_⟩
      simpa only [loopSpec, hb] using hexit
    | «continue» s' =>
      have hcont : ContinueAt n s' m2 := by simpa only [hb] using hbody
      obtain ⟨m3, h23, hhead⟩ := update_backedge n s' m2 hcont
      obtain ⟨m4, h34, hresult⟩ := ih s' m3 hhead
      refine ⟨m4, Star.trans h01 (Star.trans h12 (Star.trans h23 h34)), ?_⟩
      simpa only [loopSpec, hb] using hresult

end Loops

-- B. Word-cell memory; Nat addresses are byte offsets.
namespace Buffers

abbrev Mem := Nat → UInt64
abbrev Footprint := Nat → Prop

structure Desc where
  base : Nat  -- address of the len header
  cap : Nat
  len : Nat

def dataBase (d : Desc) : Nat := d.base + 16

def footprint (d : Desc) : Footprint :=
  fun p => d.base ≤ p ∧ p < dataBase d + 8 * d.cap

def Disjoint (F G : Footprint) : Prop :=
  ∀ p, F p → G p → False

def SameOutside (F : Footprint) (m m' : Mem) : Prop :=
  ∀ p, ¬ F p → m' p = m p

def update (m : Mem) (p : Nat) (v : UInt64) : Mem :=
  fun q => if q = p then v else m q

structure BufferRep (a : Array UInt64) (d : Desc) (m : Mem) : Prop where
  size_eq : a.size = d.len
  len_le_cap : d.len ≤ d.cap
  cap_lt : d.cap < 2^64
  aligned : d.base % 8 = 0
  header_len : m d.base = UInt64.ofNat d.len
  header_cap : m (d.base + 8) = UInt64.ofNat d.cap
  elems : ∀ i (hi : i < a.size), m (dataBase d + 8*i) = a[i]

theorem update_sameOutside (m : Mem) (F : Footprint) (p : Nat) (v : UInt64)
    (hp : F p) : SameOutside F m (update m p v) := by
  intro q hq
  have hne : q ≠ p := by
    intro h; subst q; exact hq hp
  simp [update, hne]

theorem buffer_set (a : Array UInt64) (d : Desc) (m : Mem)
    (i : Nat) (v : UInt64) (hr : BufferRep a d m) (hi : i < a.size) :
    BufferRep (a.set i v hi) d (update m (dataBase d + 8*i) v) ∧
    SameOutside (footprint d) m (update m (dataBase d + 8*i) v) := by
  have hicap : i < d.cap := by have := hr.size_eq; have := hr.len_le_cap; omega
  have hp : footprint d (dataBase d + 8*i) := by
    simp only [footprint, dataBase]
    constructor <;> omega
  constructor
  · refine ⟨?_, hr.len_le_cap, hr.cap_lt, hr.aligned, ?_, ?_, ?_⟩
    · simpa only [Array.size_set] using hr.size_eq
    · have hne : d.base ≠ dataBase d + 8*i := by simp only [dataBase]; omega
      simpa only [update, if_neg hne] using hr.header_len
    · have hne : d.base + 8 ≠ dataBase d + 8*i := by simp only [dataBase]; omega
      simpa only [update, if_neg hne] using hr.header_cap
    · intro j hj
      have hjold : j < a.size := by simpa only [Array.size_set] using hj
      by_cases hij : i = j
      · subst j
        simp [update, Array.getElem_set]
      · have haddr : dataBase d + 8*j ≠ dataBase d + 8*i := by omega
        simp only [update, if_neg haddr, Array.getElem_set, if_neg hij]
        exact hr.elems j hjold
  · exact update_sameOutside m (footprint d) _ v hp

theorem buffer_frame (b : Array UInt64) (d' : Desc) (m m' : Mem)
    (F : Footprint) (hr : BufferRep b d' m)
    (hd : Disjoint F (footprint d')) (hs : SameOutside F m m') :
    BufferRep b d' m' := by
  have preserve : ∀ p, footprint d' p → m' p = m p := by
    intro p hp
    exact hs p (fun hf => hd p hf hp)
  refine ⟨hr.size_eq, hr.len_le_cap, hr.cap_lt, hr.aligned, ?_, ?_, ?_⟩
  · rw [preserve d'.base (by simp only [footprint, dataBase]; constructor <;> omega)]
    exact hr.header_len
  · rw [preserve (d'.base + 8) (by simp only [footprint, dataBase]; constructor <;> omega)]
    exact hr.header_cap
  · intro i hi
    have hicap : i < d'.cap := by have := hr.size_eq; have := hr.len_le_cap; omega
    rw [preserve (dataBase d' + 8*i) (by simp only [footprint, dataBase]; constructor <;> omega)]
    exact hr.elems i hi

end Buffers

-- C. Runner refinement with a bounded stutter rank.
namespace Refinement

inductive Tick (N R : Type) where
  | halt (r : R)
  | next (n : N)

def runNew {N R : Type} (step : N → Tick N R) : Nat → N → Option R
  | 0, _ => none
  | fuel + 1, n =>
    match step n with
    | .halt r => some r
    | .next n' => runNew step fuel n'

def potential {O N : Type} (work : O → Nat) (rank : N → Nat)
    (K : Nat) (o : O) (n : N) : Nat := work o * (K+1) + rank n

theorem potential_progress {O N : Type}
    (work : O → Nat) (rank : N → Nat) (K : Nat)
    (o o' : O) (n n' : N)
    (hw : work o' < work o) (hr : rank n' ≤ K) :
    potential work rank K o' n' < potential work rank K o n := by
  have hm := Nat.mul_le_mul_right (K+1) (show work o' + 1 ≤ work o by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hm
  unfold potential
  omega

theorem runner_correct {O N R : Type}
    (runOld : O → R) (oldStep : O → O → Prop)
    (step : N → Tick N R) (Rel : O → N → Prop)
    (work : O → Nat) (rank : N → Nat) (K : Nat)
    (old_preserves : ∀ o o', oldStep o o' → runOld o' = runOld o)
    (rank_bound : ∀ o n, Rel o n → rank n ≤ K)
    (finish : ∀ o n r, Rel o n → step n = .halt r → r = runOld o)
    (advance : ∀ o n n', Rel o n → step n = .next n' →
      ∃ o', Rel o' n' ∧
        ((oldStep o o' ∧ work o' < work o) ∨
         (o' = o ∧ rank n' < rank n))) :
    ∀ fuel o n, Rel o n → potential work rank K o n < fuel →
      runNew step fuel n = some (runOld o) := by
  intro fuel
  induction fuel with
  | zero =>
    intro o n hrel hbudget
    omega
  | succ fuel ih =>
    intro o n hrel hbudget
    cases ht : step n with
    | halt r =>
      simp only [runNew, ht]
      exact congrArg some (finish o n r hrel ht)
    | next n' =>
      obtain ⟨o', hrel', hmove⟩ := advance o n n' hrel ht
      have hdrop : potential work rank K o' n' < potential work rank K o n := by
        rcases hmove with ⟨_, hw⟩ | ⟨heq, hr⟩
        · exact potential_progress work rank K o o' n n' hw (rank_bound o' n' hrel')
        · subst o'
          unfold potential
          omega
      have heq : runOld o' = runOld o := by
        rcases hmove with ⟨hs, _⟩ | ⟨heq, _⟩
        · exact old_preserves o o' hs
        · rw [heq]
      have hbudget' : potential work rank K o' n' < fuel := by omega
      simpa only [runNew, ht, heq] using ih o' n' hrel' hbudget'

theorem stage_correct {X O N R : Type}
    (runOld : O → R) (oldStep : O → O → Prop)
    (step : N → Tick N R) (Rel : O → N → Prop)
    (work : O → Nat) (rank : N → Nat) (K : Nat)
    (old_preserves : ∀ o o', oldStep o o' → runOld o' = runOld o)
    (rank_bound : ∀ o n, Rel o n → rank n ≤ K)
    (finish : ∀ o n r, Rel o n → step n = .halt r → r = runOld o)
    (advance : ∀ o n n', Rel o n → step n = .next n' →
      ∃ o', Rel o' n' ∧
        ((oldStep o o' ∧ work o' < work o) ∨
         (o' = o ∧ rank n' < rank n)))
    (initOld : X → O) (initNew : X → N)
    (init : ∀ x, Rel (initOld x) (initNew x))
    (fuel : Nat) (x : X)
    (adequate : potential work rank K (initOld x) (initNew x) < fuel) :
    runNew step fuel (initNew x) = some (runOld (initOld x)) := by
  exact runner_correct runOld oldStep step Rel work rank K
    old_preserves rank_bound finish advance fuel _ _ (init x) adequate

end Refinement

-- D. A deliberately small two-signature source language.
namespace Meaning

def inc (x : UInt64) : UInt64 := x + 1

def count (fuel : Nat) (acc : UInt64) : UInt64 :=
  match fuel with
  | 0 => acc
  | n+1 => count n (inc acc)
termination_by structural fuel

inductive Atom where
  | arg
  | lit (v : UInt64)
  | add (a b : Atom)

def Atom.eval : Atom → UInt64 → UInt64
  | .arg, x => x
  | .lit v, _ => v
  | .add a b, x => a.eval x + b.eval x

inductive Expr where
  | atom (a : Atom)
  | callInc (arg : Expr)

def Expr.eval (helper : UInt64 → UInt64) : Expr → UInt64 → UInt64
  | .atom a, x => a.eval x
  | .callInc e, x => helper (e.eval helper x)

inductive Fn where
  | inc
  | count

inductive Body where
  | scalar (a : Atom)
  | loop (e : Expr)

structure Prog where
  incBody : Atom
  countBody : Expr

def Prog.lookup (p : Prog) : Fn → Body
  | .inc => .scalar p.incBody
  | .count => .loop p.countBody

def iterate (step : UInt64 → UInt64) : Nat → UInt64 → UInt64
  | 0, x => x
  | n+1, x => iterate step n (step x)

def Prog.eval (p : Prog) (f : Fn) (fuel : Nat) (x : UInt64) : UInt64 :=
  match f with
  | .inc => p.incBody.eval x
  | .count => iterate (p.countBody.eval p.incBody.eval) fuel x

def body_inc : Atom := .add .arg (.lit 1)
def body_count : Expr := .callInc (.atom .arg)
def toy : Prog := ⟨body_inc, body_count⟩

theorem lookup_inc : toy.lookup .inc = .scalar body_inc := rfl
theorem lookup_count : toy.lookup .count = .loop body_count := rfl

-- Reusable evaluator rules: later certificates do not unfold the program.
theorem Prog.eval_inc_of_lookup (p : Prog) (a : Atom)
    (h : p.lookup .inc = .scalar a) (fuel : Nat) (x : UInt64) :
    p.eval .inc fuel x = a.eval x := by
  have heq : p.incBody = a := Body.scalar.inj h
  change p.incBody.eval x = a.eval x
  rw [heq]

theorem Prog.eval_count_zero (p : Prog) (x : UInt64) : p.eval .count 0 x = x := rfl

theorem Prog.eval_count_succ_of_lookup (p : Prog) (e : Expr)
    (h : p.lookup .count = .loop e) (n : Nat) (x : UInt64) :
    p.eval .count (n+1) x = p.eval .count n (e.eval (p.eval .inc 0) x) := by
  have heq : p.countBody = e := Body.loop.inj h
  change iterate (p.countBody.eval p.incBody.eval) n
      (p.countBody.eval p.incBody.eval x) =
    iterate (p.countBody.eval p.incBody.eval) n (e.eval p.incBody.eval x)
  rw [heq]

theorem meaning_inc (x : UInt64) : toy.eval .inc 0 x = inc x := by
  rw [Prog.eval_inc_of_lookup toy body_inc lookup_inc]
  rfl

theorem meaning_count (fuel : Nat) (acc : UInt64) :
    toy.eval .count fuel acc = count fuel acc := by
  induction fuel generalizing acc with
  | zero => rw [Prog.eval_count_zero]; rfl
  | succ n ih =>
    rw [Prog.eval_count_succ_of_lookup toy body_count lookup_count]
    change toy.eval .count n (toy.eval .inc 0 acc) = count n (inc acc)
    rw [meaning_inc, ih]

example : toy.eval .count 5 10 = 15 := by decide +kernel

end Meaning
end NanoProofs


namespace NanoABI
abbrev Bytes := Array UInt8
inductive Result where
  | ok (out : Bytes)
  | error (code : UInt64)

-- Adapters to your actual Sail model, not a new machine semantics.
structure Model where
  State : Type
  reg : State → Nat → UInt64
  readByte : State → UInt64 → UInt8
  status : State → UInt64
  oom : State → Bool
  oomCode : UInt64
  Runs : Bytes → State → State → Prop
  -- Must mean every maximal permitted execution reaches the return boundary,
  -- with no stuck/infinite executions; ordinary reachability is insufficient.
  AllReturn : Bytes → State → Prop
  initExtra : Bytes → Bytes → UInt64 → UInt64 → State → Prop
  frame : State → State → Prop

def Initial (M : Model) (B input : Bytes) (ip op : UInt64) (s : M.State) : Prop :=
  input.size < 2^64 ∧
  ip.toNat + input.size ≤ 2^64 ∧
  M.reg s 10 = ip ∧       -- a0
  M.reg s 11 = UInt64.ofNat input.size ∧ -- a1
  M.reg s 13 = op ∧       -- a3
  (∀ i (h : i < input.size),
    M.readByte s (ip + UInt64.ofNat i) = input[i]) ∧
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
end NanoABI


#print axioms NanoProofs.Loops.loop_correct
#print axioms NanoProofs.Buffers.buffer_set
#print axioms NanoProofs.Buffers.buffer_frame
#print axioms NanoProofs.Refinement.runner_correct
#print axioms NanoProofs.Meaning.meaning_count
#print axioms NanoSkeleton.word_pred
#print axioms NanoSkeleton.scan_stable_ge
