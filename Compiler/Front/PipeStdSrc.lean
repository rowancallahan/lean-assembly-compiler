/- Source-level correctness of the `XPipe` translation (`Compiler/Front/PipeStd.lean`): every stage keeps the
view invariant `InvE` of `Compiler/Front/PipeSrc.lean`, with the stage's standard-library function applied. -/
import Compiler.Front.PipeStd
import Compiler.Front.PipeSrc
import Compiler.Front.PipeEncode

set_option linter.unusedVariables false

namespace Proven

/-! ## Helpers -/

theorem ExecL.env_keep : ∀ {l : List AStmt} {σ σ' : AState}, ExecL l σ σ' → ∀ {v : Fin 8},
    (∀ s ∈ l, v ∉ s.assigns) → σ'.env v = σ.env v
  | [], _, _, h, _, _ => by cases h; rfl
  | a :: r, _, _, ⟨τ, h, h1⟩, v, hv => by
    rw [ExecL.env_keep h1 (fun s hs => hv s (List.mem_cons_of_mem _ hs)),
      h.env_keep (hv a (List.mem_cons_self ..))]

theorem ExecL.heap_len_keep : ∀ {l : List AStmt} {σ σ' : AState}, ExecL l σ σ' → True := fun _ => trivial

theorem zx_ofNat (u : UInt8) : zx u = BitVec.ofNat 64 u.toNat := by
  apply BitVec.eq_of_toNat_eq; rw [zx_toNat, ofNat_toNat_lt (by have := u.toNat_lt; omega)]

theorem u8and01 : ∀ a b : Bool, ((if a then 1 else 0 : UInt8) &&& (if b then 1 else 0)) = if (a && b) then 1 else 0 := by decide
theorem u8or01 : ∀ a b : Bool, ((if a then 1 else 0 : UInt8) ||| (if b then 1 else 0)) = if (a || b) then 1 else 0 := by decide
theorem u8xor01 : ∀ a : Bool, ((if a then 1 else 0 : UInt8) ^^^ 1) = if (!a) then 1 else 0 := by decide

theorem BPred.bit_denote (x : UInt8) : ∀ p : BPred, p.bit.denote 0 x = if p.denote x then 1 else 0
  | .cmp c a b => by cases c <;> simp [BPred.bit, BPred.denote, BExp.denote, BCmp.eval]
  | .and p q => by
    simp only [BPred.bit, BPred.denote, BExp.denote, BOp.eval, p.bit_denote x, q.bit_denote x]
    exact u8and01 _ _
  | .or p q => by
    simp only [BPred.bit, BPred.denote, BExp.denote, BOp.eval, p.bit_denote x, q.bit_denote x]
    exact u8or01 _ _
  | .not p => by
    simp only [BPred.bit, BPred.denote, BExp.denote, BOp.eval, p.bit_denote x]
    exact u8xor01 _
  | .tt => rfl
  | .ff => rfl

theorem BPred.bit_noAcc : ∀ p : BPred, p.noAcc = true → p.bit.noAcc = true
  | .cmp c a b, h => by simpa [BPred.bit, BPred.noAcc, BExp.noAcc] using h
  | .and p q, h => by
    simp only [BPred.noAcc, Bool.and_eq_true] at h
    simp [BPred.bit, BExp.noAcc, p.bit_noAcc h.1, q.bit_noAcc h.2]
  | .or p q, h => by
    simp only [BPred.noAcc, Bool.and_eq_true] at h
    simp [BPred.bit, BExp.noAcc, p.bit_noAcc h.1, q.bit_noAcc h.2]
  | .not p, h => by simp [BPred.bit, BExp.noAcc, p.bit_noAcc h]
  | .tt, _ | .ff, _ => rfl

def b01 (b : Bool) : BitVec 64 := if b then 1 else 0

/-- the bit expression computes the predicate as a 0/1 word, whatever the accumulator -/
theorem BPred.bit_tr {p : BPred} (hp : p.noAcc = true) (env : AEnv) (x : UInt8) (h6 : env 6 = zx x) :
    p.bit.tr.denote env = b01 (p.denote x) := by
  rw [BExp.tr_ok 0 x env h6 _ (.inl (p.bit_noAcc hp)), p.bit_denote]
  unfold b01; split <;> rfl

theorem eqB_noAcc (b : UInt8) : (eqB b).noAcc = true := rfl
theorem eqB_denote (b x : UInt8) : (eqB b).denote x = (x == b) := rfl

/-! ## Reductions: the generic code -/

theorem Inv.ofSet {L cs xs cur out fs} {env : AEnv} {heap : Heap} (h : Inv L cs xs cur ⟨env, heap⟩ out fs) (v : Fin 8)
    (a : BitVec 64) (h1 : v ≠ 1) (h4 : v ≠ 4) : Inv L cs xs cur (AState.mk (env.set v a) heap) out fs := h.set v a h1 h4

theorem optA_exec_5 {e : Option AExp} {σ : AState} :
    ExecL (optA 5 e) σ ⟨σ.env.set 5 ((e.getD (.var 5)).denote σ.env), σ.heap⟩ := by
  cases e with
  | none =>
    show _ = _
    obtain ⟨env, heap⟩ := σ
    simp only [Option.getD_none, AExp.denote, AState.mk.injEq, and_true]
    funext i; simp only [AEnv.set]; split <;> simp_all
  | some f => exact ExecL.one (AExec.assign' rfl)

theorem optA_exec_1 {e : Option AExp} {σ : AState} :
    ExecL (optA 1 e) σ ⟨σ.env.set 1 ((e.getD (.var 1)).denote σ.env), σ.heap⟩ := by
  cases e with
  | none =>
    show _ = _
    obtain ⟨env, heap⟩ := σ
    simp only [Option.getD_none, AExp.denote, AState.mk.injEq, and_true]
    funext i; simp only [AEnv.set]; split <;> simp_all
  | some f => exact ExecL.one (AExec.assign' rfl)

theorem emitC_keep5 (k : Nat) : ∀ s ∈ emitC k, (5 : Fin 8) ∉ s.assigns := by
  simp [emitC, loopV, AStmt.assigns]

/-- **A reduction**: the result is the `k` low bytes of `G A` cut to `Lf A`, where `A` is the fold of `F`
over the view (or `I m` without a loop) -/
theorem red_exec {α : Type} (enc : α → BitVec 64) (F : α → UInt8 → α) (I : Nat → α) (G : α → BitVec 64)
    (Lf : α → Nat) (c : RedC)
    (hI : ∀ env : AEnv, c.init.denote env = enc (I (env 1).toNat))
    (hS : c.loop = true → ∀ (env : AEnv) (a : α) (x : UInt8), env 5 = enc a → env 6 = zx x →
      c.step.denote env = enc (F a x))
    (hG : ∀ (env : AEnv) (a : α), env 5 = enc a → (c.fin.getD (.var 5)).denote env = G a)
    (hLf : ∀ (env : AEnv) (a : α), env 5 = G a → env 1 = .ofNat 64 c.k →
      (c.len.getD (.var 1)).denote env = .ofNat 64 (Lf a))
    (hLk : ∀ a, Lf a ≤ c.k) (hk : c.k ≤ 8)
    {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} (hI0 : InvE L cs xs cur σ) (hkL : c.k ≤ L)
    (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (redC cs c) σ σ' ∧
      InvE L csClean xs ((leBytes (G (if c.loop then cur.foldl F (I cur.length) else I cur.length)) c.k).take
        (Lf (if c.loop then cur.foldl F (I cur.length) else I cur.length))) σ' := by
  obtain ⟨out, fs, hI0⟩ := hI0
  obtain ⟨env, heap⟩ := σ
  have hh := hI0.heap; dsimp only at hh; subst hh
  have hlen := hI0.len; dsimp only at hlen
  have hI1 := hI0.set 5 (c.init.denote env) (by decide) (by decide)
  have h51 : (env.set 5 (c.init.denote env)) 5 = enc (I cur.length) := by
    simp only [AEnv.set, if_true, hI, hlen]
  generalize hA : (if c.loop then cur.foldl F (I cur.length) else I cur.length) = A
  -- the loop
  obtain ⟨σ₂, hex₂, hh₂, h5₂⟩ : ∃ σ₂, ExecL (if c.loop then [loopV 1 (.seq (fetch cs) (.assign 5 c.step))] else [])
      ⟨env.set 5 (c.init.denote env), [tbs xs, tbs out]⟩ σ₂ ∧ σ₂.heap = [tbs xs, tbs out] ∧ σ₂.env 5 = enc A := by
    cases hl : c.loop
    · simp only [hl, Bool.false_eq_true, if_false] at hA ⊢
      exact ⟨_, rfl, rfl, by dsimp only; rw [h51, hA]⟩
    · simp only [hl, if_true] at hA ⊢
      obtain ⟨σ₂, hex, hh₂, h5⟩ := foldLoop_exec enc F c.step (hS hl) hI1 (I cur.length) h51 hx hL
      exact ⟨σ₂, ExecL.one hex, hh₂, by rw [h5, hA]⟩
  obtain ⟨env₂, heap₂⟩ := σ₂
  dsimp only at hh₂ h5₂; subst hh₂
  -- fin
  have hG₂ := hG env₂ A h5₂
  -- emit
  obtain ⟨⟨env₄, heap₄⟩, out', hex₄, hh₄, hol₄, htk, h1₄, h4₄⟩ :=
    emit_exec (xs := xs) (env := env₂.set 5 ((c.fin.getD (.var 5)).denote env₂)) hI0.olen hk hkL
  have k5 := ExecL.env_keep hex₄ (emitC_keep5 c.k)
  dsimp only at hh₄ h1₄ h4₄ k5; subst hh₄
  simp only [AEnv.set, if_true, hG₂] at htk k5
  have hL₅ := hLf env₄ A k5 h1₄
  refine ⟨_, ExecL.append (ExecL.append (ExecL.append (ExecL.append (ExecL.one (AExec.assign' rfl)) hex₂)
    optA_exec_5) hex₄) optA_exec_1, out', [], Inv.ofClean hol₄ ?_ ?_ ?_⟩
  · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h4₄
  · simp only [AEnv.set, if_true, hL₅, ofNat_toNat_lt (show Lf A < 2 ^ 64 by have := hLk A; omega)]
    rw [← htk, List.take_take, Nat.min_eq_left (hLk A)]
  · simp only [AEnv.set, if_true, hL₅, ofNat_toNat_lt (show Lf A < 2 ^ 64 by have := hLk A; omega)]
    have := hLk A; omega

/-! ## Word encodings of the reduction states -/

theorem b01_eq0 (b : Bool) : b01 b = 0 ↔ b = false := by cases b <;> decide
theorem b01_or (a b : Bool) : b01 a ||| b01 b = b01 (a || b) := by cases a <;> cases b <;> decide
theorem b01_and (a b : Bool) : b01 a &&& b01 b = b01 (a && b) := by cases a <;> cases b <;> decide
theorem b01_ofNat (b : Bool) : b01 b = BitVec.ofNat 64 (if b then 1 else 0) := by cases b <;> rfl
theorem leBytes_b01 (b : Bool) : (leBytes (b01 b) 1).take 1 = enc b := by cases b <;> decide

theorem leBytes_zx (u : UInt8) : (leBytes (zx u) 1).take 1 = enc u := by
  simp [leBytes, zx_setWidth]; rfl

theorem leBytes_w8 (w : BitVec 64) : (leBytes w 8).take 8 = enc w := by
  rw [List.take_of_length_le (by simp [leBytes]), leBytes_eq_enc]

/-- option words: `none ↦ 0`, `some v ↦ 1 + 256 v` -/
def oW : Option UInt8 → BitVec 64
  | none => 0
  | some v => .ofNat 64 (1 + 256 * v.toNat)

theorem oW_tag (o : Option UInt8) : oW o &&& 1 = b01 o.isSome := by
  cases o with
  | none => decide
  | some v =>
    apply BitVec.eq_of_toNat_eq
    have := v.toNat_lt
    simp only [oW, BitVec.toNat_and, BitVec.toNat_ofNat, Option.isSome_some, b01, if_true]
    show (1 + 256 * v.toNat) % 2 ^ 64 &&& 1 = 1
    rw [Nat.and_one_is_mod]; omega

theorem tag_val {env : AEnv} {o : Option UInt8} (h5 : env 5 = oW o) : optTagE.denote env = b01 o.isSome := by
  simp only [optTagE, AExp.denote, Op.eval, h5]; exact oW_tag o

theorem some_val {env : AEnv} {x : UInt8} (h6 : env 6 = zx x) : optSomeE.denote env = oW (some x) := by
  apply BitVec.eq_of_toNat_eq
  have := x.toNat_lt
  simp only [optSomeE, AExp.denote, Op.eval, h6, oW, BitVec.toNat_add, BitVec.toNat_shiftLeft, zx_toNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  show (1 + x.toNat * 2 ^ (8 % 64) % 2 ^ 64) % 2 ^ 64 = (1 + 256 * x.toNat) % 2 ^ 64
  rw [show (2 : Nat) ^ (8 % 64) = 256 from rfl]; omega

theorem val_val {env : AEnv} {v : UInt8} (h5 : env 5 = oW (some v)) : optValE.denote env = zx v := by
  apply BitVec.eq_of_toNat_eq
  have := v.toNat_lt
  simp only [optValE, AExp.denote, Op.eval, h5, oW, BitVec.toNat_ushiftRight, zx_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  show (1 + 256 * v.toNat) % 2 ^ 64 / 2 ^ (8 % 64) = v.toNat
  rw [show (2 : Nat) ^ (8 % 64) = 256 from rfl]; omega

theorem oW_bytes (o : Option UInt8) : (leBytes (oW o) 2).take (if o.isSome then 2 else 1) = enc o := by
  cases o with
  | none => decide
  | some v =>
    have := v.toNat_lt
    simp only [leBytes, List.range, List.range.loop, List.map, leByte, oW, Option.isSome_some, if_true,
      BitVec.toNat_ofNat, List.take]
    show [UInt8.ofNat _, UInt8.ofNat _] = [1, v]
    congr 2
    · show (1 + 256 * v.toNat) % 2 ^ 64 / 256 ^ 0 % 256 = 1
      omega
    · rw [show (1 + 256 * v.toNat) % 2 ^ 64 / 256 ^ 1 % 256 = v.toNat by omega]; exact UInt8.ofNat_toNat

theorem tag1_val {env : AEnv} {o : Option UInt8} (h5 : env 5 = oW o) :
    (AExp.bin .add optTagE (.const 1)).denote env = .ofNat 64 (if o.isSome then 2 else 1) := by
  simp only [AExp.denote, Op.eval, tag_val h5]; cases o.isSome <;> rfl

theorem ite_b01 (b : Bool) (x y : BitVec 64) : (if b01 b = 0 then y else x) = if b then x else y := by
  cases b <;> simp [b01]

/-! ## Reductions: list lemmas -/

theorem foldl_u8sum (l : List UInt8) (a : UInt8) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, UInt8.add_assoc]

theorem foldl_natsum (l : List UInt8) (a : Nat) : l.foldl (fun a x => a + x.toNat) a = a + (l.map UInt8.toNat).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem foldl_countP (p : UInt8 → Bool) (l : List UInt8) (a : Nat) :
    l.foldl (fun a x => a + (if p x then 1 else 0)) a = a + l.countP p := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.countP_cons]; omega

theorem foldl_any (p : UInt8 → Bool) (l : List UInt8) (a : Bool) : l.foldl (fun a x => a || p x) a = (a || l.any p) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.any_cons, Bool.or_assoc]

theorem foldl_all (p : UInt8 → Bool) (l : List UInt8) (a : Bool) : l.foldl (fun a x => a && p x) a = (a && l.all p) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]

theorem contains_eq (l : List UInt8) (b : UInt8) : l.contains b = l.any (fun x => x == b) := by
  rw [List.contains_eq_any_beq]
  have : (fun x => b == x) = (fun x => x == b) := by
    funext x; by_cases h : x = b
    · subst h; rfl
    · rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨fun e => (h e.symm).elim, fun e => (h e).elim⟩
  rw [this]

/-! ## Reductions: per function -/

/-- the result of a reduction on the list after its `pre` stages -/
def Red.core : Red → List UInt8 → List UInt8
  | .head, l | .getLast, l => enc l.head?
  | r, l => r.denote l

theorem Red.denote_pre (r : Red) (l : List UInt8) : r.denote l = r.core (Pipe.denote r.pre l) := by
  cases r <;> try rfl
  · cases l <;> rfl
  · simp only [Red.denote, Red.core, Red.pre, Pipe.denote, List.foldl, Stage.denote]
    rw [List.getLast?_eq_head?_reverse]; cases l.reverse <;> rfl

theorem countP_core (p : UInt8 → Bool) (q : BPred) (hq : q.noAcc = true) (hpq : ∀ x, q.denote x = p x)
    {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} (hI : InvE L cs xs cur σ) (hkL : 8 ≤ L)
    (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (redC cs ⟨.const 0, true, .bin .add (.var 5) q.bit.tr, none, 8, none⟩) σ σ' ∧
      InvE L csClean xs (enc (BitVec.ofNat 64 (cur.countP p))) σ' := by
  obtain ⟨σ', h, hI'⟩ := red_exec (α := Nat) (fun n => BitVec.ofNat 64 n) (fun a x => a + (if p x then 1 else 0))
    (fun _ => 0) (fun n => .ofNat 64 n) (fun _ => 8) ⟨.const 0, true, .bin .add (.var 5) q.bit.tr, none, 8, none⟩
    (fun env => rfl)
    (fun _ env a x h5 h6 => by
      simp only [AExp.denote, Op.eval, h5, BPred.bit_tr hq env x h6, b01_ofNat, hpq, BitVec.ofNat_add])
    (fun env a h5 => h5) (fun env a h5 h1 => h1) (fun _ => Nat.le_refl _) (by dsimp only; omega) hI hkL hx hL
  refine ⟨σ', h, ?_⟩
  simpa only [if_true, foldl_countP, Nat.zero_add, leBytes_w8] using hI'

theorem any_core (p : UInt8 → Bool) (q : BPred) (hq : q.noAcc = true) (hpq : ∀ x, q.denote x = p x)
    {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} (hI : InvE L cs xs cur σ) (hkL : 1 ≤ L)
    (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (redC cs ⟨.const 0, true, .bin .or (.var 5) q.bit.tr, none, 1, none⟩) σ σ' ∧
      InvE L csClean xs (enc (cur.any p)) σ' := by
  obtain ⟨σ', h, hI'⟩ := red_exec (α := Bool) b01 (fun a x => a || p x)
    (fun _ => false) b01 (fun _ => 1) ⟨.const 0, true, .bin .or (.var 5) q.bit.tr, none, 1, none⟩
    (fun env => rfl)
    (fun _ env a x h5 h6 => by simp only [AExp.denote, Op.eval, h5, BPred.bit_tr hq env x h6, b01_or, hpq])
    (fun env a h5 => h5) (fun env a h5 h1 => h1) (fun _ => Nat.le_refl _) (by dsimp only; omega) hI hkL hx hL
  refine ⟨σ', h, ?_⟩
  simpa only [if_true, foldl_any, Bool.false_or, leBytes_b01] using hI'

theorem all_core (p : UInt8 → Bool) (q : BPred) (hq : q.noAcc = true) (hpq : ∀ x, q.denote x = p x)
    {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} (hI : InvE L cs xs cur σ) (hkL : 1 ≤ L)
    (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (redC cs ⟨.const 1, true, .bin .and (.var 5) q.bit.tr, none, 1, none⟩) σ σ' ∧
      InvE L csClean xs (enc (cur.all p)) σ' := by
  obtain ⟨σ', h, hI'⟩ := red_exec (α := Bool) b01 (fun a x => a && p x)
    (fun _ => true) b01 (fun _ => 1) ⟨.const 1, true, .bin .and (.var 5) q.bit.tr, none, 1, none⟩
    (fun env => rfl)
    (fun _ env a x h5 h6 => by simp only [AExp.denote, Op.eval, h5, BPred.bit_tr hq env x h6, b01_and, hpq])
    (fun env a h5 => h5) (fun env a h5 h1 => h1) (fun _ => Nat.le_refl _) (by dsimp only; omega) hI hkL hx hL
  refine ⟨σ', h, ?_⟩
  simpa only [if_true, foldl_all, Bool.true_and, leBytes_b01] using hI'

theorem Inv.len_lt {L cs xs cur σ out fs} (h : Inv L cs xs cur σ out fs) (hx : xs.length < 2 ^ 32)
    (hL : L < 2 ^ 32) : cur.length < 2 ^ 32 := by
  have := h.len; have := h.bound; have := h.olen
  split at *  <;> omega

theorem InvE.len_lt {L cs xs cur σ} (h : InvE L cs xs cur σ) (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    cur.length < 2 ^ 32 := by obtain ⟨_, _, h⟩ := h; exact h.len_lt hx hL

theorem oSome (m : UInt8) : (1 : BitVec 64) + zx m <<< ((8 : BitVec 64).toNat % 64) = oW (some m) := by
  have := some_val (env := fun i => if i = 6 then zx m else 0) (x := m) (by simp)
  simpa [optSomeE, AExp.denote, Op.eval] using this

theorem foldl_head (l : List UInt8) (o : Option UInt8) : l.foldl (fun o x => o.or (some x)) o = o.or l.head? := by
  induction l generalizing o with
  | nil => cases o <;> rfl
  | cons x l ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_find (p : UInt8 → Bool) (l : List UInt8) (o : Option UInt8) :
    l.foldl (fun o x => o.or (if p x then some x else none)) o = o.or (l.find? p) := by
  induction l generalizing o with
  | nil => cases o <;> rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.find?_cons]
    cases o <;> cases p x <;> rfl

theorem foldl_minO (l : List UInt8) (a : UInt8) :
    l.foldl (fun o x => some (o.elim x fun v => min v x)) (some a) = some (l.foldl min a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, List.foldl_cons, ← ih]; rfl

theorem foldl_maxO (l : List UInt8) (a : UInt8) :
    l.foldl (fun o x => some (o.elim x fun v => max v x)) (some a) = some (l.foldl max a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, List.foldl_cons, ← ih]; rfl

theorem foldl_min_none (l : List UInt8) : l.foldl (fun o x => some (o.elim x fun v => min v x)) none = l.min? := by
  cases l with
  | nil => rfl
  | cons x l => rw [List.foldl_cons]; exact foldl_minO l x

theorem foldl_max_none (l : List UInt8) : l.foldl (fun o x => some (o.elim x fun v => max v x)) none = l.max? := by
  cases l with
  | nil => rfl
  | cons x l => rw [List.foldl_cons]; exact foldl_maxO l x

/-- the result of an option-valued reduction with step `F` (code `S`) -/
theorem opt_core (F : Option UInt8 → UInt8 → Option UInt8) (S : AExp)
    (hS : ∀ (env : AEnv) (a : Option UInt8) (x : UInt8), env 5 = oW a → env 6 = zx x → S.denote env = oW (F a x))
    {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} (hI : InvE L cs xs cur σ) (hkL : 2 ≤ L)
    (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (redC cs ⟨.const 0, true, S, none, 2, some (.bin .add optTagE (.const 1))⟩) σ σ' ∧
      InvE L csClean xs (enc (cur.foldl F none)) σ' := by
  obtain ⟨σ', h, hI'⟩ := red_exec (α := Option UInt8) oW F (fun _ => none) oW (fun o => if o.isSome then 2 else 1)
    ⟨.const 0, true, S, none, 2, some (.bin .add optTagE (.const 1))⟩
    (fun env => rfl) (fun _ => hS) (fun env a h5 => h5) (fun env a h5 h1 => tag1_val h5)
    (fun o => by dsimp only; split <;> omega) (by dsimp only; omega) hI hkL hx hL
  refine ⟨σ', h, ?_⟩
  simpa only [if_true, oW_bytes] using hI'

theorem ite_tag {env : AEnv} {o : Option UInt8} (h5 : env 5 = oW o) (a b : AExp) :
    (AExp.ite optTagE a b).denote env = if o.isSome then a.denote env else b.denote env := by
  simp only [AExp.denote, tag_val h5, ite_b01]

theorem zx_ult (a b : UInt8) : Op.eval .ult (zx a) (zx b) = b01 (decide (a < b)) := by
  simp only [Op.eval, zx_lt]; by_cases h : a < b <;> simp [h, b01]

theorem findIdx_tag (i : Nat) (f : Bool) :
    BitVec.ofNat 64 (2 * i + if f then 1 else 0) &&& 1 = b01 f := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  cases f <;> simp [b01] <;> omega

def fiF (p : UInt8 → Bool) (a : Nat × Bool) (x : UInt8) : Nat × Bool :=
  if a.2 then a else if p x then (a.1, true) else (a.1 + 1, false)

def fiW (a : Nat × Bool) : BitVec 64 := .ofNat 64 (2 * a.1 + if a.2 then 1 else 0)

theorem foldl_fi_true (p : UInt8 → Bool) (l : List UInt8) (i : Nat) : l.foldl (fiF p) (i, true) = (i, true) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons]; exact ih

theorem foldl_fi (p : UInt8 → Bool) (l : List UInt8) (i : Nat) :
    (l.foldl (fiF p) (i, false)).1 = i + l.findIdx p := by
  induction l generalizing i with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, List.findIdx_cons]
    by_cases h : p x
    · simp [fiF, h, foldl_fi_true]
    · simp only [fiF, h, Bool.false_eq_true, if_false, ih, cond_false]; omega

theorem findIdx_core (p : UInt8 → Bool) (q : BPred) (hq : q.noAcc = true) (hpq : ∀ x, q.denote x = p x)
    {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} (hI : InvE L cs xs cur σ) (hkL : 8 ≤ L)
    (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (redC cs ⟨.const 0, true,
      .ite optTagE (.var 5) (.ite q.bit.tr (.bin .add (.var 5) (.const 1)) (.bin .add (.var 5) (.const 2))),
      some (.bin .lshr (.var 5) (.const 1)), 8, none⟩) σ σ' ∧
      InvE L csClean xs (enc (BitVec.ofNat 64 (cur.findIdx p))) σ' := by
  have hcl := hI.len_lt hx hL
  obtain ⟨σ', h, hI'⟩ := red_exec (α := Nat × Bool) fiW (fiF p) (fun _ => (0, false)) (fun a => fiW a >>> 1)
    (fun _ => 8) ⟨.const 0, true,
      .ite optTagE (.var 5) (.ite q.bit.tr (.bin .add (.var 5) (.const 1)) (.bin .add (.var 5) (.const 2))),
      some (.bin .lshr (.var 5) (.const 1)), 8, none⟩
    (fun env => rfl)
    (fun _ env a x h5 h6 => by
      obtain ⟨i, f⟩ := a
      have ht : optTagE.denote env = b01 f := by simp only [optTagE, AExp.denote, Op.eval, h5]; exact findIdx_tag i f
      simp only [AExp.denote, ht, ite_b01, BPred.bit_tr hq env x h6, hpq, h5]
      cases f <;> cases hp : p x <;> simp only [fiF, fiW, if_true, Bool.false_eq_true, if_false, Op.eval, hp] <;>
        (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [show (1 : BitVec 64).toNat = 1 from rfl, show (2 : BitVec 64).toNat = 2 from rfl]; omega))
    (fun env a h5 => by simp only [Option.getD_some, AExp.denote, Op.eval, h5]; rfl)
    (fun env a h5 h1 => h1) (fun _ => Nat.le_refl _) (by dsimp only; omega) hI hkL hx hL
  refine ⟨σ', h, ?_⟩
  have hfi := foldl_fi p cur 0
  have hle := List.findIdx_le_length (p := p) (xs := cur)
  have e : fiW (cur.foldl (fiF p) (0, false)) >>> 1 = BitVec.ofNat 64 (cur.findIdx p) := by
    generalize cur.foldl (fiF p) (0, false) = A at hfi
    obtain ⟨i, f⟩ := A
    simp only [Nat.zero_add] at hfi; subst hfi
    apply BitVec.eq_of_toNat_eq
    simp only [fiW, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    cases f <;> simp <;> omega
  simpa only [if_true, e, leBytes_w8] using hI'

theorem min_sel (v x : UInt8) : (if x < v then zx x else zx v) = zx (min v x) := by
  show _ = zx (if v ≤ x then v else x)
  by_cases h : x < v
  · simp [h, UInt8.not_le.mpr h]
  · simp [h, UInt8.not_lt.mp h]

theorem max_sel (v x : UInt8) : (if v < x then zx x else zx v) = zx (max v x) := by
  show _ = zx (if v ≤ x then x else v)
  by_cases h : v < x
  · simp [h, UInt8.le_of_lt h]
  · by_cases h' : v ≤ x
    · have : v = x := UInt8.le_antisymm h' (UInt8.not_lt.mp h)
      simp [h, h', this]
    · simp [h, h']

theorem minmax_step (sel : UInt8 → UInt8 → UInt8) (C : AExp)
    (hC : ∀ (env : AEnv) (v x : UInt8), env 5 = oW (some v) → env 6 = zx x → C.denote env = zx (sel v x))
    (env : AEnv) (a : Option UInt8) (x : UInt8) (h5 : env 5 = oW a) (h6 : env 6 = zx x) :
    (AExp.bin .add (.const 1) (.bin .shl (.ite optTagE C (.var 6)) (.const 8))).denote env =
      oW (some (a.elim x fun v => sel v x)) := by
  have : (AExp.ite optTagE C (.var 6)).denote env = zx (a.elim x fun v => sel v x) := by
    rw [ite_tag h5]
    cases a with
    | none => exact h6
    | some v => exact hC env v x h5 h6
  simp only [AExp.denote, Op.eval, this]; exact oSome _

/-- every reduction, on the view after its `pre` stages -/
theorem Red.core_exec (r : Red) (hc : r.chk = none) {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState}
    (hI : InvE L cs xs cur σ) (hkL : r.code.k ≤ L) (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (redC cs r.code) σ σ' ∧ InvE L csClean xs (r.core cur) σ' := by
  have hp : ∀ p : BPred, (if p.noAcc then (none : Option String) else some "predicate mentions the fold accumulator") = none →
      p.noAcc = true := fun p h => by by_cases hp : p.noAcc = true
                                      · exact hp
                                      · simp [hp] at h
  cases r with
  | length =>
    obtain ⟨σ', h, hI'⟩ := red_exec (α := Nat) (fun n => BitVec.ofNat 64 n) (fun a _ => a) id
      (fun n => .ofNat 64 n) (fun _ => 8) Red.length.code (fun env => by simp [Red.code, AExp.denote])
      (fun h => by simp [Red.code] at h) (fun env a h5 => h5) (fun env a h5 h1 => h1) (fun _ => Nat.le_refl _)
      (by decide) hI hkL hx hL
    exact ⟨σ', h, by simpa only [Red.code, Bool.false_eq_true, if_false, id, leBytes_w8] using hI'⟩
  | isEmpty =>
    obtain ⟨σ', h, hI'⟩ := red_exec (α := Bool) b01 (fun a _ => a) (fun n => n == 0) b01 (fun _ => 1)
      Red.isEmpty.code (fun env => by
        simp only [Red.code, AExp.denote, Op.eval]
        by_cases h0 : env 1 = 0
        · simp [h0, b01]
        · have : (env 1).toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e))
          simp [h0, this, b01])
      (fun h => by simp [Red.code] at h) (fun env a h5 => h5) (fun env a h5 h1 => h1) (fun _ => Nat.le_refl _)
      (by decide) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    simp only [Red.code, Bool.false_eq_true, if_false, leBytes_b01] at hI'
    show InvE L csClean xs (enc cur.isEmpty) σ'
    cases cur <;> exact hI'
  | sum8 =>
    obtain ⟨σ', h, hI'⟩ := red_exec (α := UInt8) zx (· + ·) (fun _ => 0) zx (fun _ => 1) Red.sum8.code
      (fun env => rfl) (fun _ env a x h5 h6 => BExp.tr_ok a x env h6 _ (.inr h5)) (fun env a h5 => h5)
      (fun env a h5 h1 => h1) (fun _ => Nat.le_refl _) (by decide) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    simpa only [Red.code, if_true, leBytes_zx, foldl_u8sum, UInt8.zero_add] using hI'
  | sum64 =>
    obtain ⟨σ', h, hI'⟩ := red_exec (α := Nat) (fun n => BitVec.ofNat 64 n) (fun a x => a + x.toNat) (fun _ => 0)
      (fun n => .ofNat 64 n) (fun _ => 8) Red.sum64.code (fun env => rfl)
      (fun _ env a x h5 h6 => by simp only [Red.code, AExp.denote, Op.eval, h5, h6, zx_ofNat, BitVec.ofNat_add])
      (fun env a h5 => h5) (fun env a h5 h1 => h1) (fun _ => Nat.le_refl _) (by decide) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    simpa only [Red.code, if_true, leBytes_w8, foldl_natsum, Nat.zero_add] using hI'
  | countP p => exact countP_core p.denote p (hp p hc) (fun _ => rfl) hI hkL hx hL
  | count b => exact countP_core (· == b) (eqB b) rfl (fun _ => rfl) hI hkL hx hL
  | any p => exact any_core p.denote p (hp p hc) (fun _ => rfl) hI hkL hx hL
  | all p => exact all_core p.denote p (hp p hc) (fun _ => rfl) hI hkL hx hL
  | contains b =>
    obtain ⟨σ', h, hI'⟩ := any_core (· == b) (eqB b) rfl (fun _ => rfl) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    show InvE L csClean xs (enc (cur.contains b)) σ'
    rw [contains_eq]; exact hI'
  | head | getLast =>
    obtain ⟨σ', h, hI'⟩ := opt_core (fun o x => o.or (some x)) _ (fun env a x h5 h6 => by
      rw [ite_tag h5, some_val h6]; simp only [AExp.denote, h5]; cases a <;> rfl) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    rw [foldl_head] at hI'; exact hI'
  | find p =>
    have hq := hp p hc
    obtain ⟨σ', h, hI'⟩ := opt_core (fun o x => o.or (if p.denote x then some x else none)) _ (fun env a x h5 h6 => by
      rw [ite_tag h5]; simp only [AExp.denote, h5, BPred.bit_tr hq env x h6, ite_b01, some_val h6]
      cases a <;> cases p.denote x <;> rfl) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    rw [foldl_find] at hI'; exact hI'
  | min =>
    obtain ⟨σ', h, hI'⟩ := opt_core (fun o x => some (o.elim x fun v => Min.min v x)) _
      (minmax_step (fun v x => Min.min v x) _ (fun env v x h5 h6 => by
        rw [ite_tag h5]; simp only [AExp.denote, h6, val_val h5, zx_ult, ite_b01, Option.isSome_some, if_true]
        exact min_sel v x)) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    rw [foldl_min_none] at hI'; exact hI'
  | max =>
    obtain ⟨σ', h, hI'⟩ := opt_core (fun o x => some (o.elim x fun v => Max.max v x)) _
      (minmax_step (fun v x => Max.max v x) _ (fun env v x h5 h6 => by
        rw [ite_tag h5]; simp only [AExp.denote, h6, val_val h5, zx_ult, ite_b01, Option.isSome_some, if_true]
        exact max_sel v x)) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    rw [foldl_max_none] at hI'; exact hI'
  | findIdx p => exact findIdx_core p.denote p (hp p hc) (fun _ => rfl) hI hkL hx hL
  | idxOf b => exact findIdx_core (· == b) (eqB b) rfl (fun _ => rfl) hI hkL hx hL

end Proven
