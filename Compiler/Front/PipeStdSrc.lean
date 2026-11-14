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
      simp [this]
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
  show (1 : BitVec 64) + ((AExp.ite optTagE C (.var 6)).denote env) <<< (((8 : BitVec 64)).toNat % 64) = _
  rw [this]; exact oSome _

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
          rw [if_neg h0]; simp [this, b01])
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
    obtain ⟨σ', h, hI'⟩ := opt_core (fun o x => o.or (some x)) (.ite optTagE (.var 5) optSomeE) (fun env a x h5 h6 => by
      rw [ite_tag h5, some_val h6]; simp only [AExp.denote, h5]; cases a <;> simp [Option.or]) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    rw [foldl_head] at hI'; exact hI'
  | find p =>
    have hq := hp p hc
    obtain ⟨σ', h, hI'⟩ := opt_core (fun o x => o.or (if p.denote x then some x else none))
      (.ite optTagE (.var 5) (.ite p.bit.tr optSomeE (.const 0))) (fun env a x h5 h6 => by
      rw [ite_tag h5]; simp only [AExp.denote, h5, BPred.bit_tr hq env x h6, ite_b01, some_val h6]
      cases a <;> cases p.denote x <;> rfl) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    rw [foldl_find] at hI'; exact hI'
  | min =>
    obtain ⟨σ', h, hI'⟩ := opt_core (fun o x => some (o.elim x fun v => Min.min v x)) _
      (minmax_step (fun v x => Min.min v x) (.ite (.bin .ult (.var 6) optValE) (.var 6) optValE) (fun env v x h5 h6 => by
        simp only [AExp.denote, h6, val_val h5, zx_ult, ite_b01, decide_eq_true_eq]
        exact min_sel v x)) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    rw [foldl_min_none] at hI'; exact hI'
  | max =>
    obtain ⟨σ', h, hI'⟩ := opt_core (fun o x => some (o.elim x fun v => Max.max v x)) _
      (minmax_step (fun v x => Max.max v x) (.ite (.bin .ult optValE (.var 6)) (.var 6) optValE) (fun env v x h5 h6 => by
        simp only [AExp.denote, h6, val_val h5, zx_ult, ite_b01, decide_eq_true_eq]
        exact max_sel v x)) hI hkL hx hL
    refine ⟨σ', h, ?_⟩
    rw [foldl_max_none] at hI'; exact hI'
  | findIdx p => exact findIdx_core p.denote p (hp p hc) (fun _ => rfl) hI hkL hx hL
  | idxOf b => exact findIdx_core (· == b) (eqB b) rfl (fun _ => rfl) hI hkL hx hL

/-! ## Old stages before a reduction -/

theorem preC_exec {L : Nat} {xs : List UInt8} (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∀ (p : Pipe) {cs : CS} {cur : List UInt8} {σ : AState},
    (∀ st ∈ p, st.chk = none ∧ ∀ cs n, st.space cs n = 0) → InvE L cs xs cur σ →
    ∃ σ', ExecL (preC p cs).1 σ σ' ∧ InvE L (preC p cs).2 xs (Pipe.denote p cur) σ'
  | [], cs, cur, σ, _, hI => ⟨σ, rfl, hI⟩
  | st :: r, cs, cur, σ, hc, hI => by
    have h0 := hc st (List.mem_cons_self ..)
    obtain ⟨σ₁, hex₁, hI₁⟩ := stage_exec hx hL st h0.1 hI (by rw [h0.2]; exact Nat.zero_le _)
    obtain ⟨σ₂, hex₂, hI₂⟩ := preC_exec hx hL r (fun s hs => hc s (List.mem_cons_of_mem _ hs)) hI₁
    exact ⟨σ₂, ExecL.append hex₁ hex₂, hI₂⟩

/-! ## Stateful filter -/

/-- keep `x` iff `K s x ≠ 0`; the state goes `s ↦ N s x` -/
def sfilt (K N : UInt8 → UInt8 → UInt8) : UInt8 → List UInt8 → List UInt8
  | _, [] => []
  | s, x :: l => (if K s x = 0 then [] else [x]) ++ sfilt K N (N s x) l

theorem sfilt_append (K N : UInt8 → UInt8 → UInt8) :
    ∀ (s : UInt8) (a b : List UInt8), sfilt K N s (a ++ b) = sfilt K N s a ++ sfilt K N (a.foldl N s) b
  | s, [], b => rfl
  | s, x :: a, b => by
    simp only [List.cons_append, sfilt, sfilt_append K N (N s x) a b, List.append_assoc, List.foldl_cons]

theorem sfilt_len (K N : UInt8 → UInt8 → UInt8) : ∀ s l, (sfilt K N s l).length ≤ l.length
  | s, [] => Nat.le_refl _
  | s, x :: l => by
    have := sfilt_len K N (N s x) l
    simp only [sfilt, List.length_append, List.length_cons]; split <;> simp <;> omega

theorem zx_eq0 (u : UInt8) : zx u = 0 ↔ u = 0 := by
  rw [show (0 : BitVec 64) = zx 0 from rfl, zx_inj]

theorem sf_loop_exec {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} {out : List UInt8}
    {fs : List (UInt8 → UInt8)} (hI : Inv L cs xs cur σ out fs) (hrev : cs.onOut = true → cs.rev = false)
    (Kb Nb : BExp) (s0 : UInt8) (hsp : cur.length ≤ L) (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL [.assign 5 (.const (zx s0)), .assign 7 (.const 0),
      loopV 1 (.seq (fetch cs) (.seq (.store 1 (.var 7) (.var 6))
        (.seq (.assign 7 (.bin .add (.var 7) (.ite Kb.tr (.const 1) (.const 0)))) (.assign 5 Nb.tr)))),
      .assign 1 (.var 7), .assign 4 (.const 0)] σ σ' ∧
      InvE L csClean xs (sfilt (fun s x => Kb.denote s x) (fun s x => Nb.denote s x) s0 cur) σ' := by
  generalize hK : (fun s x => Kb.denote s x) = K
  generalize hN : (fun s x => Nb.denote s x) = N
  obtain ⟨env, heap⟩ := σ
  have hh := hI.heap; dsimp only at hh; subst hh
  have hlen := hI.len; dsimp only at hlen
  have hbd := hI.bound; dsimp only at hbd
  have hcur := hI.cur; dsimp only at hcur
  have hol0 := hI.olen
  generalize hs : (env 4).toNat = s at *
  generalize hm : (env 1).toNat = m at *
  have hBl : (if cs.onOut then out else xs).length < 2 ^ 32 := by split <;> omega
  let env₀ := (env.set 5 (zx s0)).set 7 0
  obtain ⟨σ', hex, ⟨h4, o, hho, hol, h7, hpre, hR, h5, -⟩, h1⟩ := loopV_exec (c := 1) (by decide) (m := m) (by omega)
    (body := .seq (fetch cs) (.seq (.store 1 (.var 7) (.var 6))
        (.seq (.assign 7 (.bin .add (.var 7) (.ite Kb.tr (.const 1) (.const 0)))) (.assign 5 Nb.tr))))
    (fun i τ => τ.env 4 = env 4 ∧ ∃ o : List UInt8, τ.heap = [tbs xs, tbs o] ∧ o.length = L ∧
      τ.env 7 = .ofNat 64 (sfilt K N s0 (cur.take i)).length ∧
      (∀ k, k < (sfilt K N s0 (cur.take i)).length → o[k]? = (sfilt K N s0 (cur.take i))[k]?) ∧
      (sfilt K N s0 (cur.take i)).length ≤ i ∧
      τ.env 5 = zx ((cur.take i).foldl N s0) ∧
      (∀ j, i ≤ j → j < m → (if cs.onOut then o else xs)[idxN cs.rev s m j]? =
        (if cs.onOut then out else xs)[idxN cs.rev s m j]?))
    (fun i ⟨env', heap'⟩ hi ⟨h4, o, hho, hol, h7, hpre, hR, h5, hsrc⟩ h2 h1 => by
      dsimp only at h4 hho h2 h1 h7 h5; subst hho
      have ht := vIdx_val cs.rev (env := env') (s := s) (m := m) (by rw [h4]; exact hs)
        (by rw [h1]; exact ofNat_toNat_lt (by omega)) h2 hi (by omega)
      have hsi := hsrc i (Nat.le_refl _) hi
      have hidx : idxN cs.rev s m i < s + m := by unfold idxN; split <;> omega
      have hlt : idxN cs.rev s m i < (if cs.onOut then o else xs).length := by
        have : (if cs.onOut then o else xs).length = (if cs.onOut then out else xs).length := by split <;> omega
        omega
      have hci : cur[i]? = some (applyAll fs ((if cs.onOut then o else xs)[idxN cs.rev s m i])) := by
        rw [hcur, List.getElem?_map, view_get _ hbd hi, ← hsi, getElem?_some_of hlt]; rfl
      obtain ⟨⟨env'', heap''⟩, hf, hfh, hfe⟩ := fetch_exec hI.fsok ht hlt
      dsimp only at hfh hfe; subst hfh hfe
      generalize applyAll fs ((if cs.onOut then o else xs)[idxN cs.rev s m i]) = u at *
      generalize hRi : sfilt K N s0 (cur.take i) = R at *
      generalize hSi : (cur.take i).foldl N s0 = st at *
      have hti : cur.take (i + 1) = cur.take i ++ [u] := by
        rw [List.take_add_one, hci]; rfl
      have hR1 : sfilt K N s0 (cur.take (i + 1)) = R ++ (if K st u = 0 then [] else [u]) := by
        rw [hti, sfilt_append, hRi, hSi]; simp [sfilt]
      have hS1 : (cur.take (i + 1)).foldl N s0 = N st u := by rw [hti, List.foldl_append, hSi]; rfl
      have hko : R.length < o.length := by omega
      let e6 := env'.set 6 (zx u)
      have e7 : ((AExp.var 7).denote e6).toNat = R.length := by
        simp only [e6, AExp.denote, AEnv.set, Fin.reduceEq, if_false, h7]; exact ofNat_toNat_lt (by omega)
      have hst := AExec.store (b := 1) (i := .var 7) (e := .var 6) (σ := ⟨e6, [tbs xs, tbs o]⟩)
        (by simp) (by rw [e7]; simpa using hko)
      simp only [e7, List.getElem_cons_succ, List.getElem_cons_zero] at hst
      simp only [e6, AExp.denote, AEnv.set, if_true, zx_setWidth] at hst
      rw [heap_set1] at hst
      have hKv : Kb.tr.denote e6 = zx (K st u) := by
        rw [← hK]; exact BExp.tr_ok st u e6 (by simp [e6, AEnv.set]) Kb (.inr (by simp [e6, AEnv.set, h5]))
      let e7' := e6.set 7 ((AExp.bin .add (.var 7) (.ite Kb.tr (.const 1) (.const 0))).denote e6)
      have hNv : Nb.tr.denote e7' = zx (N st u) := by
        rw [← hN]; exact BExp.tr_ok st u e7' (by simp [e7', e6, AEnv.set]) Nb
          (.inr (by simp [e7', e6, AEnv.set, h5]))
      refine ⟨_, .seq hf (.seq hst (.seq (AExec.assign (v := 7) (σ := ⟨e6, _⟩)) AExec.assign)), ?_, ?_, ?_, ?_⟩
      · simp only [e6, AEnv.set, Fin.reduceEq, if_false]; exact h2
      · simp only [e6, AEnv.set, Fin.reduceEq, if_false]; exact h1
      · simp only [e6, AEnv.set, Fin.reduceEq, if_false]; exact h4
      · refine ⟨o.set R.length u, rfl, by simpa using hol, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hR1]
          simp only [e6, AExp.denote, Op.eval, AEnv.set, Fin.reduceEq, if_false, h7] at hKv ⊢
          rw [hKv]
          by_cases hk : K st u = 0
          · simp [hk]; rfl
          · have : zx (K st u) ≠ 0 := fun e => hk ((zx_eq0 _).1 e)
            simp only [this, hk, if_false, List.length_append, List.length_singleton, BitVec.ofNat_add]; rfl
        · intro k hk
          rw [hR1] at hk ⊢
          by_cases hkr : k = R.length
          · subst hkr
            rw [List.getElem?_set_self hko]
            by_cases hk0 : K st u = 0
            · simp [hk0] at hk
            · simp [hk0]
          · have hkl : k < R.length := by
              by_cases hk0 : K st u = 0 <;> simp [hk0] at hk <;> omega
            rw [List.getElem?_set_ne (Ne.symm hkr), List.getElem?_append_left hkl]; exact hpre k hkl
        · rw [hR1]; by_cases hk0 : K st u = 0 <;> simp [hk0] <;> omega
        · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hS1]; exact hNv
        · intro j hj hjm
          have := hsrc j (by omega) hjm
          cases hO : cs.onOut
          · simpa [hO] using this
          · simp only [hO, if_true] at this ⊢
            rw [hrev hO] at this ⊢
            simp only [idxN, Bool.false_eq_true, if_false] at this ⊢
            rw [List.getElem?_set_ne (by omega)]; exact this)
    ⟨env₀, [tbs xs, tbs out]⟩ (by rw [← hm]; simp [env₀, AEnv.set])
    ⟨by simp [env₀, AEnv.set], out, rfl, hol0, by simp [env₀, AEnv.set, sfilt], fun k hk => by simp [sfilt] at hk,
      by simp [sfilt], by simp [env₀, AEnv.set], fun j _ _ => rfl⟩
  obtain ⟨env', heap'⟩ := σ'
  dsimp only at hho h7 h1 h4; subst hho
  rw [List.take_of_length_le (by omega)] at h7 hpre hR
  have e7 : (env' 7).toNat = (sfilt K N s0 cur).length := by rw [h7]; exact ofNat_toNat_lt (by omega)
  refine ⟨_, ⟨_, AExec.assign' rfl, _, AExec.assign' rfl, _, hex, _, AExec.assign' rfl, ExecL.one (AExec.assign' rfl)⟩,
    o, [], Inv.ofClean hol (by simp [AEnv.set, AExp.denote]) ?_ ?_⟩
  · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, AExp.denote, e7]
    apply List.ext_getElem?; intro k
    rw [List.getElem?_take]
    split
    · exact hpre k (by omega)
    · exact (List.getElem?_eq_none (by omega)).symm
  · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, AExp.denote, e7]; omega

theorem sf_exec {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} (hI : InvE L cs xs cur σ)
    (Kb Nb : BExp) (s0 : UInt8) (hsp : cur.length ≤ L) (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (sfC cs Kb Nb s0) σ σ' ∧
      InvE L csClean xs (sfilt (fun s x => Kb.denote s x) (fun s x => Nb.denote s x) s0 cur) σ' := by
  cases hO : cs.onOut
  · obtain ⟨out, fs, hI⟩ := hI
    obtain ⟨σ', hex, hI'⟩ := sf_loop_exec hI (by simp [hO]) Kb Nb s0 hsp hx hL
    exact ⟨σ', by simpa [sfC, hO] using hex, hI'⟩
  · obtain ⟨σ₁, hex₁, out, fs, hI₁⟩ := mat_exec hx hL hI (.inr hsp)
    obtain ⟨σ', hex, hI'⟩ := sf_loop_exec hI₁ (fun _ => rfl) Kb Nb s0 hsp hx hL
    exact ⟨σ', by simpa [sfC, hO] using ExecL.append hex₁ hex, hI'⟩

theorem BExp.denote_noAcc {e : BExp} (h : e.noAcc = true) (a x : UInt8) : e.denote a x = e.denote 0 x := by
  let env : AEnv := fun i => if i = 5 then zx a else zx x
  have h1 := BExp.tr_ok a x env (by simp [env]) e (.inr (by simp [env]))
  have h2 := BExp.tr_ok 0 x env (by simp [env]) e (.inl h)
  exact zx_inj.1 (h1.symm.trans h2)

theorem bit_any {p : BPred} (hp : p.noAcc = true) (s x : UInt8) : p.bit.denote s x = if p.denote x then 1 else 0 := by
  rw [BExp.denote_noAcc (p.bit_noAcc hp), p.bit_denote]

theorem sfilt_filter (K N : UInt8 → UInt8 → UInt8) (p : UInt8 → Bool) (hK : ∀ s x, K s x = if p x then 1 else 0) :
    ∀ (s : UInt8) (l : List UInt8), sfilt K N s l = l.filter p
  | s, [] => rfl
  | s, x :: l => by
    rw [sfilt, hK, sfilt_filter K N p hK _ l, List.filter_cons]
    cases p x <;> simp

theorem sfilt_take0 (K : UInt8 → UInt8 → UInt8) (p : UInt8 → Bool) (hK : ∀ s x, K s x = s &&& if p x then 1 else 0) :
    ∀ l : List UInt8, sfilt K K 0 l = []
  | [] => rfl
  | x :: l => by rw [sfilt, hK, UInt8.zero_and, sfilt_take0 K p hK l]; simp

theorem sfilt_takeWhile (K : UInt8 → UInt8 → UInt8) (p : UInt8 → Bool) (hK : ∀ s x, K s x = s &&& if p x then 1 else 0) :
    ∀ l : List UInt8, sfilt K K 1 l = l.takeWhile p
  | [] => rfl
  | x :: l => by
    rw [sfilt, hK, List.takeWhile_cons]
    cases hx : p x
    · simp only [Bool.false_eq_true, if_false, show (1 : UInt8) &&& 0 = 0 from rfl, if_true, List.nil_append]
      exact sfilt_take0 K p hK l
    · simp only [if_true, show (1 : UInt8) &&& 1 = 1 from rfl, show (1 : UInt8) = 0 ↔ False from by decide]
      rw [sfilt_takeWhile K p hK l]; rfl

theorem sfilt_drop0 (K N : UInt8 → UInt8 → UInt8) (p : UInt8 → Bool)
    (hK : ∀ s x, K s x = (s &&& if p x then 1 else 0) ^^^ 1) (hN : ∀ s x, N s x = s &&& if p x then 1 else 0) :
    ∀ l : List UInt8, sfilt K N 0 l = l
  | [] => rfl
  | x :: l => by
    rw [sfilt, hK, hN, UInt8.zero_and, sfilt_drop0 K N p hK hN l]; rfl

theorem sfilt_dropWhile (K N : UInt8 → UInt8 → UInt8) (p : UInt8 → Bool)
    (hK : ∀ s x, K s x = (s &&& if p x then 1 else 0) ^^^ 1) (hN : ∀ s x, N s x = s &&& if p x then 1 else 0) :
    ∀ l : List UInt8, sfilt K N 1 l = l.dropWhile p
  | [] => rfl
  | x :: l => by
    rw [sfilt, hK, hN, List.dropWhile_cons]
    cases hx : p x
    · simp only [Bool.false_eq_true, if_false, show (1 : UInt8) &&& 0 = 0 from rfl]
      rw [sfilt_drop0 K N p hK hN l]; rfl
    · simp only [if_true, show (1 : UInt8) &&& 1 = 1 from rfl]
      rw [sfilt_dropWhile K N p hK hN l]; rfl

/-! ## Appending a constant list -/

theorem appStores_exec {xs : List UInt8} {env : AEnv} {m L : Nat} (h1 : env 1 = .ofNat 64 m) (hL : L < 2 ^ 32) :
    ∀ (c : List UInt8) (j : Nat) (o : List UInt8), o.length = L → m + j + c.length ≤ L →
    ∃ o', ExecL (appStores j c) ⟨env, [tbs xs, tbs o]⟩ ⟨env, [tbs xs, tbs o']⟩ ∧ o'.length = L ∧
      (∀ k, k < m + j → o'[k]? = o[k]?) ∧ (∀ i, i < c.length → o'[m + j + i]? = c[i]?)
  | [], j, o, hol, _ => ⟨o, rfl, hol, fun _ _ => rfl, fun i hi => by simp at hi⟩
  | b :: c, j, o, hol, hle => by
    simp only [List.length_cons] at hle
    have e : ((AExp.bin .add (.var 1) (.const (.ofNat 64 j))).denote env).toNat = m + j := by
      simp only [AExp.denote, Op.eval, h1, ← BitVec.ofNat_add]; exact ofNat_toNat_lt (by omega)
    have hst := AExec.store (b := 1) (i := .bin .add (.var 1) (.const (.ofNat 64 j))) (e := .const (zx b))
      (σ := ⟨env, [tbs xs, tbs o]⟩) (by simp) (by rw [e]; simp; omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hst
    rw [e] at hst
    simp only [AExp.denote, zx_setWidth] at hst
    rw [heap_set1] at hst
    obtain ⟨o', hex, hol', hlo, hhi⟩ := appStores_exec h1 hL c (j + 1) (o.set (m + j) b) (by simpa using hol)
      (by omega)
    refine ⟨o', ⟨_, hst, hex⟩, hol', fun k hk => ?_, fun i hi => ?_⟩
    · rw [hlo k (by omega), List.getElem?_set_ne (by omega)]
    · cases i with
      | zero =>
        rw [hlo _ (by omega), Nat.add_zero, List.getElem?_set_self (by omega)]; rfl
      | succ i =>
        rw [show m + j + (i + 1) = m + (j + 1) + i by omega, hhi i (by simp at hi; omega)]; rfl

theorem app_exec {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} (hI : InvE L cs xs cur σ)
    (c : List UInt8) (hsp : cur.length + c.length ≤ L) (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (appC cs c) σ σ' ∧ InvE L csClean xs (cur ++ c) σ' := by
  obtain ⟨σ₁, hex₁, out, fs, hI₁⟩ := mat_exec hx hL hI (.inr (by omega))
  obtain ⟨rfl, h4, hcur, hm⟩ := hI₁.clean
  have hol := hI₁.olen
  obtain ⟨env, heap⟩ := σ₁
  have hh := hI₁.heap; dsimp only at hh h4 hcur hm; subst hh
  have hlen := hI₁.len; dsimp only at hlen
  generalize hmm : (env 1).toNat = m at *
  have h1 : env 1 = .ofNat 64 m := by rw [← hmm]; simp
  obtain ⟨o', hex, hol', hlo, hhi⟩ := appStores_exec (xs := xs) h1 hL c 0 out hol (by omega)
  have e1 : ((env.set 1 ((AExp.bin .add (.var 1) (.const (.ofNat 64 c.length))).denote env)) 1).toNat =
      m + c.length := by
    simp only [AEnv.set, if_true, AExp.denote, Op.eval, h1, ← BitVec.ofNat_add]; exact ofNat_toNat_lt (by omega)
  refine ⟨_, ExecL.append (ExecL.append hex₁ hex) (ExecL.one (AExec.assign' rfl)), o', [],
    Inv.ofClean hol' (by simp only [AEnv.set, Fin.reduceEq, if_false]; exact h4) ?_ (by rw [e1]; omega)⟩
  rw [e1]
  apply List.ext_getElem?; intro k
  rw [List.getElem?_take]
  split
  · by_cases hk : k < m
    · rw [hlo k (by omega), List.getElem?_append_left (by omega), hcur, List.getElem?_take, if_pos hk]
    · have := hhi (k - m) (by omega)
      rw [show m + 0 + (k - m) = k by omega] at this
      rw [this, List.getElem?_append_right (by omega), hlen]
  · exact (List.getElem?_eq_none (by simp; omega)).symm

/-! ## Stages and pipes -/

theorem Stage.len_mono (st : Stage) {n n' : Nat} (h : n ≤ n') : st.len n ≤ st.len n' := by
  cases st <;> simp only [Stage.len] <;> omega

theorem XStage.len_mono (st : XStage) {n n' : Nat} (h : n ≤ n') : st.len n ≤ st.len n' := by
  cases st with
  | base st => exact st.len_mono h
  | _ => simp only [XStage.len] <;> omega

theorem XStage.space_mono (st : XStage) (cs : CS) {n n' : Nat} (h : n ≤ n') : st.space cs n ≤ st.space cs n' := by
  cases st with
  | base st => cases st <;> simp only [XStage.space, Stage.space] <;> (try split) <;> omega
  | _ => simp only [XStage.space] <;> omega

theorem XPipe.need_mono : ∀ (p : XPipe) (cs : CS) {n n' : Nat}, n ≤ n' → XPipe.need p cs n ≤ XPipe.need p cs n'
  | [], cs, n, n', h => by simp only [XPipe.need]; split <;> omega
  | st :: r, cs, n, n', h => by
    simp only [XPipe.need]
    have := st.space_mono cs h
    have := XPipe.need_mono r (xstageC st cs).2 (st.len_mono h)
    omega

theorem enc_w64_len (w : BitVec 64) : (enc w).length = 8 := leN_length 8 _
theorem enc_opt_len (o : Option UInt8) : (enc o).length ≤ 2 := by
  cases o with
  | none => decide
  | some v => exact Nat.le_refl _

theorem Red.denote_len (r : Red) (l : List UInt8) : (r.denote l).length ≤ r.code.k := by
  cases r <;> simp only [Red.denote, Red.code, enc_w64_len, Nat.le_refl] <;>
    first | exact enc_opt_len _ | (cases (l.isEmpty) <;> decide) | skip
  all_goals first | rfl | exact Nat.le_refl _ | (cases (List.any _ _) <;> decide) | (cases (List.all _ _) <;> decide) |
    (cases (List.contains _ _) <;> decide) | decide

theorem XStage.denote_len (st : XStage) (hc : st.chk = none) (l : List UInt8) :
    (st.denote l).length ≤ st.len l.length := by
  have hp : ∀ p : BPred, (if p.noAcc then (none : Option String) else some "predicate mentions the fold accumulator") = none →
      p.noAcc = true := fun p h => by by_cases hp : p.noAcc = true
                                      · exact hp
                                      · simp [hp] at h
  cases st with
  | base st => exact Nat.le_of_eq (st.denote_len l)
  | red r => exact r.denote_len l
  | filter p => exact List.length_filter_le _ _
  | takeWhile p =>
    show (l.takeWhile p.denote).length ≤ l.length
    rw [← sfilt_takeWhile (fun s x => (takeK p).denote s x) p.denote (fun s x => by
      simp [takeK, BExp.denote, BOp.eval, bit_any (hp p hc)])]
    exact sfilt_len _ _ _ _
  | dropWhile p =>
    show (l.dropWhile p.denote).length ≤ l.length
    rw [← sfilt_dropWhile (fun s x => (dropK p).denote s x) (fun s x => (takeK p).denote s x) p.denote
      (fun s x => by simp [dropK, BExp.denote, BOp.eval, bit_any (hp p hc)])
      (fun s x => by simp [takeK, BExp.denote, BOp.eval, bit_any (hp p hc)])]
    exact sfilt_len _ _ _ _
  | appendC c => simp [XStage.denote, XStage.len]

theorem xstage_exec {L : Nat} {xs : List UInt8} (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) (st : XStage) {cs : CS}
    {cur : List UInt8} {σ : AState} (hc : st.chk = none) (hI : InvE L cs xs cur σ)
    (hsp : st.space cs cur.length ≤ L) :
    ∃ σ', ExecL (xstageC st cs).1 σ σ' ∧ InvE L (xstageC st cs).2 xs (st.denote cur) σ' := by
  have hp : ∀ p : BPred, (if p.noAcc then (none : Option String) else some "predicate mentions the fold accumulator") = none →
      p.noAcc = true := fun p h => by by_cases hp : p.noAcc = true
                                      · exact hp
                                      · simp [hp] at h
  cases st with
  | base st => exact stage_exec hx hL st hc hI hsp
  | red r =>
    have hpre : ∀ st ∈ r.pre, st.chk = none ∧ ∀ cs n, st.space cs n = 0 := by
      cases r <;> simp [Red.pre, Stage.chk, Stage.space]
    obtain ⟨σ₁, hex₁, hI₁⟩ := preC_exec hx hL r.pre hpre hI
    obtain ⟨σ₂, hex₂, hI₂⟩ := r.core_exec hc hI₁ hsp hx hL
    refine ⟨σ₂, ExecL.append hex₁ hex₂, ?_⟩
    simp only [xstageC, XStage.denote]; rw [Red.denote_pre]; exact hI₂
  | filter p =>
    obtain ⟨σ', hex, hI'⟩ := sf_exec hI p.bit (.lit 0) 0 hsp hx hL
    refine ⟨σ', hex, ?_⟩
    rw [sfilt_filter _ _ p.denote (fun s x => bit_any (hp p hc) s x)] at hI'; exact hI'
  | takeWhile p =>
    obtain ⟨σ', hex, hI'⟩ := sf_exec hI (takeK p) (takeK p) 1 hsp hx hL
    refine ⟨σ', hex, ?_⟩
    rw [sfilt_takeWhile _ p.denote (fun s x => by simp [takeK, BExp.denote, BOp.eval, bit_any (hp p hc)])] at hI'
    exact hI'
  | dropWhile p =>
    obtain ⟨σ', hex, hI'⟩ := sf_exec hI (dropK p) (takeK p) 1 hsp hx hL
    refine ⟨σ', hex, ?_⟩
    rw [sfilt_dropWhile _ _ p.denote (fun s x => by simp [dropK, BExp.denote, BOp.eval, bit_any (hp p hc)])
      (fun s x => by simp [takeK, BExp.denote, BOp.eval, bit_any (hp p hc)])] at hI'
    exact hI'
  | appendC c => exact app_exec hI c hsp hx hL

theorem xstmts_exec {L : Nat} {xs : List UInt8} (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∀ (p : XPipe) {cs : CS} {cur : List UInt8} {σ : AState}, (∀ st ∈ p, st.chk = none) → InvE L cs xs cur σ →
    XPipe.need p cs cur.length ≤ L → ∃ σ', ExecL (xstmts p cs) σ σ' ∧ InvE L csClean xs (XPipe.denote p cur) σ'
  | [], cs, cur, σ, _, hI, hsp => by
    refine mat_exec hx hL hI ?_
    simp only [XPipe.need] at hsp
    by_cases h : cs.clean = true
    · exact .inl h
    · simp only [h, Bool.false_eq_true, if_false] at hsp; exact .inr hsp
  | st :: r, cs, cur, σ, hc, hI, hsp => by
    simp only [XPipe.need] at hsp
    have hst := hc st (List.mem_cons_self ..)
    obtain ⟨σ₁, hex₁, hI₁⟩ := xstage_exec hx hL st hst hI (by omega)
    obtain ⟨σ₂, hex₂, hI₂⟩ := xstmts_exec hx hL r (fun s hs => hc s (List.mem_cons_of_mem _ hs)) hI₁
      (Nat.le_trans (XPipe.need_mono r _ (st.denote_len hst cur)) (by omega))
    exact ⟨σ₂, ExecL.append hex₁ hex₂, hI₂⟩

/-- **Source-level correctness of the `XPipe` translation** (as `Pipe.prog_exec`) -/
theorem XPipe.prog_exec (p : XPipe) (hc : ∀ st ∈ p, st.chk = none) (xs : List UInt8) (out : List (BitVec 8))
    (env : AEnv) (h1 : env 1 = .ofNat 64 xs.length) (hx : xs.length < 2 ^ 32)
    (hsp : XPipe.space p xs.length ≤ out.length) (hL : out.length < 2 ^ 32) :
    ∃ σ' out', AExec (XPipe.prog p) ⟨env, [tbs xs, out]⟩ σ' ∧ σ'.heap = [tbs xs, out'] ∧
      out'.length = out.length ∧ out'.take (XPipe.denote p xs).length = tbs (XPipe.denote p xs) ∧
      σ'.env 1 = .ofNat 64 (XPipe.denote p xs).length := by
  have ho : out = tbs (out.map fun b => ⟨b⟩) := by simp [tbs, List.map_map, Function.comp_def]
  generalize out.map (fun b => (⟨b⟩ : UInt8)) = o at ho; subst ho
  have e1 : (env 1).toNat = xs.length := by rw [h1]; exact ofNat_toNat_lt (by omega)
  have hI0 : InvE (tbs o).length cs0 xs xs ⟨env.set 4 0, [tbs xs, tbs o]⟩ :=
    ⟨o, [], rfl, by simp, .nil, by simp [cs0, AEnv.set, e1], by simp [cs0, AEnv.set, e1, dirL, applyAll_nil],
      fun _ => by simp [AEnv.set]⟩
  obtain ⟨⟨env', heap'⟩, hex, out', fs, hI⟩ := xstmts_exec hx hL p hc hI0 hsp
  obtain ⟨rfl, h4, hcur, hm⟩ := hI.clean
  have hh := hI.heap; dsimp only at hh hcur; subst hh
  have : (XPipe.denote p xs).length = (env' 1).toNat := hI.len
  refine ⟨_, tbs out', ExecL.foldl (AExec.assign' rfl) hex, rfl, by simpa using hI.olen, ?_, ?_⟩
  · rw [this, hcur]; simp [tbs]
  · rw [this]; simp

end Proven
