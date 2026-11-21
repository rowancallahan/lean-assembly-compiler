/- Selection for the spill-slot language `BStmt` (byte blocks; `Compiler/BLang.lean`): IR code over virtual
registers, where each variable `8 + j` is either kept in a (virtual) register or, if `sp j`, in frame slot
`j`.  Variables `0 .. 7` are always registers.  A slot variable costs one `ldS` per read and one `stS` per
write; which variables are spilled is the caller's (untrusted) choice `sp`.

`irB_ok`: a `BExec` run is an IR run, for the relation `RelBI` (registers, slots, blocks). -/
import Nano.Base.Compiler.Opt.Sel
import Nano.Base.Compiler.Opt.Arr
import Nano.Base.Compiler.BStmt

namespace Proven.Mach
open IR Sel

section
variable (sp : Nat → Bool) (N : Nat)

/-- variable `i` is slot-resident -/
def isS (i : Nat) : Bool := decide (8 ≤ i) && sp (i - 8)

def toS : BExp → SExp
  | .var i => if isS sp i = true then .slot (i - 8) else if h : i < 32 then .var ⟨i, h⟩ else .const 0
  | .const c => .const c
  | .bin op a b => .bin op (toS a) (toS b)
  | .ite c a b => .ite (toS c) (toS a) (toS b)

/-- every variable is `< 8 + N` (checked) -/
def okE : BExp → Bool
  | .var i => decide (i < 8 + N)
  | .const _ => true
  | .bin _ a b => okE a && okE b
  | .ite c a b => okE c && okE a && okE b

def envB (env : BEnv) : Fin 32 → BitVec 64 := fun i => env i.val
def svB (env : BEnv) : Nat → BitVec 64 := fun j => env (8 + j)

/-- register-resident variables are below the temporaries (`< 32`); slot variables may be any -/
def LoR : Prop := ∀ i, i < 8 + N → isS sp i = false → i < 32

/-- checker for `LoR`: every local `j ≥ 24` is spilled -/
def loB : Bool := (List.range N).all fun j => sp j || decide (j < 24)

theorem loB_ok (h : loB sp N = true) : LoR sp N := fun i hi hs => by
  by_cases h8 : 8 ≤ i
  · have := List.all_eq_true.1 h (i - 8) (List.mem_range.2 (by omega))
    have hs' : sp (i - 8) = false := by unfold isS at hs; rw [decide_eq_true h8, Bool.true_and] at hs; exact hs
    rw [hs', Bool.false_or] at this; have := of_decide_eq_true this; omega
  · omega

theorem isS_ge {i : Nat} (h : isS sp i = true) : 8 ≤ i ∧ sp (i - 8) = true :=
  ⟨of_decide_eq_true (Wide.and2 h).1, (Wide.and2 h).2⟩

theorem toS_denote (hN : LoR sp N) (env : BEnv) : ∀ e : BExp, okE N e = true →
    (toS sp e).denote (envB env) (svB env) = e.denote env
  | .var i, h => by
    have hi : i < 8 + N := of_decide_eq_true h
    simp only [toS]
    by_cases hs : isS sp i = true
    · rw [if_pos hs]
      show env (8 + (i - 8)) = env i
      rw [Nat.add_sub_cancel' (isS_ge sp hs).1]
    · rw [if_neg hs, dif_pos (hN i hi (Bool.eq_false_iff.2 hs))]; rfl
  | .const _, _ => rfl
  | .bin op a b, h => by
    obtain ⟨ha, hb⟩ := Wide.and2 h
    simp only [toS, SExp.denote, BExp.denote, toS_denote hN env a ha, toS_denote hN env b hb]
  | .ite c a b, h => by
    obtain ⟨hc, ha, hb⟩ := Wide.and3 h
    simp only [toS, SExp.denote, BExp.denote, toS_denote hN env c hc, toS_denote hN env a ha,
      toS_denote hN env b hb]

/-- `d := value`, where `c d'` computes the value into `d'` -/
def setB (v : Nat) (c : Nat → Code Nat) : Code Nat :=
  if isS sp v = true then .seq (c (tk 0)) (.ins (.stS (v - 8) (tk 0))) else c v

/-- IR code of a statement -/
def irB (bv wv : List Nat) : BStmt → Code Nat
  | .assign v e => setB sp v fun d => into (toS sp e) d 0
  | .load v b i => .seq (into (toS sp (addrB bv b i)) (tk 0) 0) (setB sp v fun d => .ins (.lbu d (.r (tk 0)) 0))
  | .store b i e => .seq (into (toS sp (addrB bv b i)) (tk 0) 0)
      (.seq (opnd (toS sp e) 1 (into (toS sp e) (tk 1) 1)).1
        (.ins (.sb (opnd (toS sp e) 1 (into (toS sp e) (tk 1) 1)).2.1 (.r (tk 0)) 0)))
  | .seq p q => .seq (irB bv wv p) (irB bv wv q)
  | .loop c body => loopCode (toS sp c) (irB bv wv body)
  | .load64 v b i => .seq (into (toS sp (addrW wv b i)) (tk 0) 0) (setB sp v fun d => .ins (.ld d (tk 0) 0))
  | .store64 b i e => .seq (into (toS sp (addrW wv b i)) (tk 0) 0)
      (.seq (into (toS sp e) (tk 1) 1) (.ins (.sd (tk 1) (tk 0) 0)))
  | .mop m v a b => .seq (into (toS sp a) (tk 0) 0)
      (.seq (into (toS sp b) (tk 1) 1) (setB sp v fun d => .ins (.mop m d (.r (tk 0)) (.r (tk 1)))))

/-- the checks selection needs (word arrays are not supported) -/
def okB (bv wv : List Nat) : BStmt → Bool
  | .assign v e => okE N e && decide (v < 8 + N) && (decide (v ∉ bv) && decide (v ∉ wv))
  | .load v b i => okE N i && decide (v < 8 + N) && (decide (v ∉ bv) && decide (v ∉ wv)) &&
      (decide (b < bv.length) && decide (bv.getD b 0 < 8 + N))
  | .store b i e => okE N i && okE N e && (decide (b < bv.length) && decide (bv.getD b 0 < 8 + N))
  | .seq p q => okB bv wv p && okB bv wv q
  | .loop c body => okE N c && okB bv wv body
  | .load64 v b i => okE N i && decide (v < 8 + N) && (decide (v ∉ bv) && decide (v ∉ wv)) &&
      (decide (b < wv.length) && decide (wv.getD b 0 < 8 + N))
  | .store64 b i e => okE N i && okE N e && (decide (b < wv.length) && decide (wv.getD b 0 < 8 + N))
  | .mop _ v a b => okE N a && okE N b && decide (v < 8 + N) && (decide (v ∉ bv) && decide (v ∉ wv))

variable (fp : Nat)

/-- the frame and the blocks -/
structure LayI (R W : List Region) : Prop where
  al : fp % 8 = 0
  lt : ∀ r ∈ R, r.base + r.len < 2 ^ 64
  rp : R.Pairwise disjoint
  fr : ∀ r ∈ R, disjoint ⟨fp, 8 * (N + 1)⟩ r
  hN : LoR sp N
  wlt : ∀ w ∈ W, w.base + w.len < 2 ^ 64
  wp : W.Pairwise disjoint
  rw : ∀ r ∈ R, ∀ w ∈ W, disjoint r w
  fw : ∀ w ∈ W, disjoint ⟨fp, 8 * (N + 1)⟩ w
  wal : ∀ w ∈ W, w.base % 8 = 0

/-- the IR state represents `σ` -/
structure RelBI (bv wv : List Nat) (R W : List Region) (σ : BState) (τ : St Nat) : Prop where
  reg : ∀ i, i < 8 + N → isS sp i = false → τ.reg i = σ.env i
  slot : ∀ j, j < N → sp j = true → bytes τ.mem (fp + 8 * (j + 1)) 8 = (le8 (σ.env (8 + j))).map some
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  rbytes : ∀ b (hb : b < R.length), bytes τ.mem R[b].base R[b].len = (σ.heap[b]?.getD []).map some
  whlen : σ.wheap.length = W.length
  wvlen : wv.length = W.length
  wbase : ∀ b (hb : b < W.length), σ.env (wv.getD b 0) = BitVec.ofNat 64 W[b].base
  wblen : ∀ b (hb : b < W.length), 8 * (σ.wheap[b]?.getD []).length = W[b].len
  wbyts : ∀ b (hb : b < W.length), bytes τ.mem W[b].base W[b].len = (wbytes (σ.wheap[b]?.getD [])).map some

/-- writable addresses: the byte blocks, the word blocks and the slots -/
def ramB (R W : List Region) : Nat → Prop := ramR (R ++ W ++ slots N fp)

variable {sp N fp}

theorem ram_slot {R W : List Region} {j : Nat} (hj : j < N) (i : Nat) (hi : i < 8) :
    ramB N fp R W (fp + 8 * (j + 1) + i) :=
  ⟨⟨fp + 8 * (j + 1), 8⟩, List.mem_append_right _ (slot_mem_slots hj), by show fp + 8 * (j + 1) ≤ _; omega, by
    show _ < fp + 8 * (j + 1) + 8; omega⟩

theorem agree_mk_bin {ram : Nat → Prop} {env sv} {op : Op} {a b : SExp} {σ : St Nat}
    (ha : Agree ram fp env sv a σ) (hb : Agree ram fp env sv b σ) : Agree ram fp env sv (.bin op a b) σ :=
  ⟨fun i hi => by simp only [uses, Bool.or_eq_true] at hi; exact hi.elim (ha.1 i) (hb.1 i),
   fun j hj => by simp only [usesS, Bool.or_eq_true] at hj; exact hj.elim (ha.2 j) (hb.2 j)⟩

theorem agree_mk_ite {ram : Nat → Prop} {env sv} {c a b : SExp} {σ : St Nat}
    (hc : Agree ram fp env sv c σ) (ha : Agree ram fp env sv a σ) (hb : Agree ram fp env sv b σ) :
    Agree ram fp env sv (.ite c a b) σ :=
  ⟨fun i hi => by
    simp only [uses, Bool.or_eq_true] at hi; exact hi.elim (fun h => h.elim (hc.1 i) (ha.1 i)) (hb.1 i),
   fun j hj => by
    simp only [usesS, Bool.or_eq_true] at hj; exact hj.elim (fun h => h.elim (hc.2 j) (ha.2 j)) (hb.2 j)⟩

/-- a represented state agrees with every checked expression -/
theorem RelBI.agree {bv wv R W σ τ} (r : RelBI sp N fp bv wv R W σ τ) (L : LayI sp N fp R W) : ∀ e : BExp, okE N e = true →
    Agree (ramB N fp R W) fp (envB σ.env) (svB σ.env) (toS sp e) τ
  | .var i, h => by
    have hi : i < 8 + N := of_decide_eq_true h
    have hN := L.hN
    simp only [toS]
    by_cases hs : isS sp i = true
    · rw [if_pos hs]
      obtain ⟨h8, hsp⟩ := isS_ge sp hs
      refine ⟨fun x hx => (nomatch hx), fun j hj => ?_⟩
      have e : i - 8 = j := of_decide_eq_true hj
      subst e
      exact ⟨L.al, ram_slot (by omega), r.slot (i - 8) (by omega) hsp⟩
    · rw [if_neg hs, dif_pos (hN i hi (Bool.eq_false_iff.2 hs))]
      refine ⟨fun x hx => ?_, fun j hj => (nomatch hj)⟩
      have e : i = x.val := of_decide_eq_true hx
      show τ.reg x.val = σ.env x.val
      rw [← e]; exact r.reg i hi (Bool.eq_false_iff.2 hs)
  | .const _, _ => ⟨fun x hx => (nomatch hx), fun j hj => (nomatch hj)⟩
  | .bin op a b, h => agree_mk_bin (r.agree L a (Wide.and2 h).1) (r.agree L b (Wide.and2 h).2)
  | .ite c a b, h => agree_mk_ite (r.agree L c (Wide.and3 h).1) (r.agree L a (Wide.and3 h).2.1)
      (r.agree L b (Wide.and3 h).2.2)

theorem RelBI.frame {bv wv R W σ τ} (r : RelBI sp N fp bv wv R W σ τ) (L : LayI sp N fp R W) {τ' : St Nat} (f : Frame 32 τ τ') :
    RelBI sp N fp bv wv R W σ τ' := by
  have hN := L.hN
  exact ⟨fun i hi hs => (f.2 i (hN i hi hs)).trans (r.reg i hi hs), fun j hj hs => by rw [f.1]; exact r.slot j hj hs,
    r.hlen, r.bvlen, r.base, r.blen, fun b hb => by rw [f.1]; exact r.rbytes b hb, r.whlen, r.wvlen, r.wbase, r.wblen, fun b hb => by rw [f.1]; exact r.wbyts b hb⟩

/-- the address of an in-bounds element -/
theorem RelBI.addr {bv wv R W σ τ} (r : RelBI sp N fp bv wv R W σ τ) (L : LayI sp N fp R W) {b : Nat}
    (hb : b < σ.heap.length) {i : BExp} (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
    ∃ hbR : b < R.length, ((addrB bv b i).denote σ.env).toNat = R[b].base + (i.denote σ.env).toNat ∧
      (i.denote σ.env).toNat < R[b].len := by
  have hbR : b < R.length := r.hlen ▸ hb
  have hl := r.blen b hbR; rw [getD_get _ hb] at hl
  have := L.lt _ (List.getElem_mem hbR)
  refine ⟨hbR, ?_, by omega⟩
  show (σ.env (bv.getD b 0) + i.denote σ.env).toNat = _
  rw [r.base b hbR, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := R[b].base) (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- the address of an in-bounds word -/
theorem RelBI.waddr {bv wv R W σ τ} (r : RelBI sp N fp bv wv R W σ τ) (L : LayI sp N fp R W) {b : Nat}
    (hb : b < σ.wheap.length) {i : BExp} (hi : (i.denote σ.env).toNat < σ.wheap[b].length) :
    ∃ hbW : b < W.length, ((addrW wv b i).denote σ.env).toNat = W[b].base + 8 * (i.denote σ.env).toNat ∧
      (W[b].base + 8 * (i.denote σ.env).toNat) % 8 = 0 ∧ 8 * (i.denote σ.env).toNat + 8 ≤ W[b].len := by
  have hbW : b < W.length := r.whlen ▸ hb
  have hl := r.wblen b hbW; rw [getD_get _ hb] at hl
  have hlt := L.wlt _ (List.getElem_mem hbW)
  have hal := L.wal _ (List.getElem_mem hbW)
  refine ⟨hbW, ?_, by omega, by omega⟩
  show (σ.env (wv.getD b 0) + (i.denote σ.env) <<< ((BitVec.ofNat 64 3).toNat % 64)).toNat = _
  have e3 : (BitVec.ofNat 64 3).toNat % 64 = 3 := rfl
  rw [e3, r.wbase b hbW, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    Nat.mod_eq_of_lt (a := W[b].base) (by omega), Nat.shiftLeft_eq,
    show (2 : Nat) ^ 3 = 8 from rfl, Nat.mod_eq_of_lt (a := (i.denote σ.env).toNat * 8) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- assigning a variable (register or slot) -/
theorem setB_ok {bv wv R W σ} {τ : St Nat} (r : RelBI sp N fp bv wv R W σ τ) (L : LayI sp N fp R W) {v : Nat} (hv : v < 8 + N)
    (hvb : v ∉ bv) (hvw : v ∉ wv) {c : Nat → Code Nat} {x : BitVec 64}
    (hc : ∀ d, ∃ τ', Exec (ramB N fp R W) fp (c d) τ τ' ∧ τ'.reg d = x ∧ τ'.mem = τ.mem ∧
      ∀ y, y ≠ d → y < 32 → τ'.reg y = τ.reg y) :
    ∃ τ', Exec (ramB N fp R W) fp (setB sp v c) τ τ' ∧ RelBI sp N fp bv wv R W ⟨σ.env.set v x, σ.heap, σ.wheap⟩ τ' := by
  have hN := L.hN
  have hbase : ∀ b (hb : b < R.length), (σ.env.set v x) (bv.getD b 0) = BitVec.ofNat 64 R[b].base := fun b hb => by
    have : bv.getD b 0 ≠ v := fun e => hvb (e ▸ getD_mem bv (r.bvlen ▸ hb))
    show (if bv.getD b 0 = v then x else σ.env (bv.getD b 0)) = _
    rw [ite_neg this]; exact r.base b hb
  have hwbase : ∀ b (hb : b < W.length), (σ.env.set v x) (wv.getD b 0) = BitVec.ofNat 64 W[b].base := fun b hb => by
    have : wv.getD b 0 ≠ v := fun e => hvw (e ▸ getD_mem wv (r.wvlen ▸ hb))
    show (if wv.getD b 0 = v then x else σ.env (wv.getD b 0)) = _
    rw [ite_neg this]; exact r.wbase b hb
  unfold setB
  by_cases hs : isS sp v = true
  · rw [if_pos hs]
    obtain ⟨h8, hsp⟩ := isS_ge sp hs
    obtain ⟨τ₁, x₁, v₁, m₁, f₁⟩ := hc (tk 0)
    refine ⟨⟨τ₁.reg, τ₁.mem.wr (fp + 8 * (v - 8 + 1)) (le8 (τ₁.reg (tk 0)))⟩,
      .seq x₁ (.ins (.stS L.al (ram_slot (by omega)))), fun i hi hsi => ?_, fun j hj hsj => ?_, r.hlen, r.bvlen,
      hbase, r.blen, fun b hb => ?_, r.whlen, r.wvlen, hwbase, r.wblen, fun b hb => ?_⟩
    · have hiv : i ≠ v := fun e => by rw [e, hs] at hsi; exact nomatch hsi
      show τ₁.reg i = if i = v then x else σ.env i
      rw [ite_neg hiv, f₁ i (by have := hN i hi hsi; unfold tk; omega) (hN i hi hsi)]; exact r.reg i hi hsi
    · show bytes (Mem.wr _ _ _) _ _ = (le8 (if 8 + j = v then x else σ.env (8 + j))).map some
      by_cases hjv : 8 + j = v
      · rw [ite_pos hjv, v₁, show v - 8 = j by omega]
        have := bytes_wr_self (m := τ₁.mem) (a := fp + 8 * (j + 1)) (l := le8 x)
        rwa [length_le8] at this
      · rw [ite_neg hjv, bytes_wr_out (by rw [length_le8]; omega), m₁]; exact r.slot j hj hsj
    · have hd := L.fr _ (List.getElem_mem hb)
      unfold disjoint at hd; dsimp only at hd
      show bytes (Mem.wr _ _ _) _ _ = _
      rw [bytes_wr_out (by rw [length_le8]; omega), m₁]; exact r.rbytes b hb
    · have hd := L.fw _ (List.getElem_mem hb)
      unfold disjoint at hd; dsimp only at hd
      show bytes (Mem.wr _ _ _) _ _ = _
      rw [bytes_wr_out (by rw [length_le8]; omega), m₁]; exact r.wbyts b hb
  · rw [if_neg hs]
    obtain ⟨τ₁, x₁, v₁, m₁, f₁⟩ := hc v
    refine ⟨τ₁, x₁, fun i hi hsi => ?_, fun j hj hsj => ?_, r.hlen, r.bvlen, hbase, r.blen, fun b hb => by
      rw [m₁]; exact r.rbytes b hb, r.whlen, r.wvlen, hwbase, r.wblen, fun b hb => by rw [m₁]; exact r.wbyts b hb⟩
    · show τ₁.reg i = if i = v then x else σ.env i
      by_cases hiv : i = v
      · rw [ite_pos hiv, hiv, v₁]
      · rw [ite_neg hiv, f₁ i hiv (hN i hi hsi)]; exact r.reg i hi hsi
    · have hjv : ¬8 + j = v := fun e => hs (by
        unfold isS; rw [← e, show 8 + j - 8 = j by omega, hsj]; simp)
      show _ = (le8 (if 8 + j = v then x else σ.env (8 + j))).map some
      rw [ite_neg hjv, m₁]; exact r.slot j hj hsj

/-- selection preserves the statement semantics -/
theorem irB_ok (bv wv : List Nat) {R W : List Region} (L : LayI sp N fp R W) : ∀ {p : BStmt} {σ σ' : BState},
    BExec p σ σ' → okB N bv wv p = true → ∀ (τ : St Nat), RelBI sp N fp bv wv R W σ τ →
    ∃ τ', IR.Exec (ramB N fp R W) fp (irB sp bv wv p) τ τ' ∧ RelBI sp N fp bv wv R W σ' τ' := by
  intro p σ σ' h
  have hN := L.hN
  induction h with
  | @assign v e σ =>
    intro hp τ r
    obtain ⟨he, hv, hvb⟩ := Wide.and3 hp
    refine setB_ok r L (of_decide_eq_true hv) (of_decide_eq_true (Wide.and2 hvb).1) (of_decide_eq_true (Wide.and2 hvb).2) fun d => ?_
    obtain ⟨τ', hx, hval, hm, hf⟩ := into_ok (toS sp e) d 0 τ (r.agree L e he)
    rw [toS_denote sp N hN _ e he] at hval
    exact ⟨τ', hx, hval, hm, fun y hy h32 => hf y hy (by omega)⟩
  | @load v b i σ hb hi =>
    intro hp τ r
    obtain ⟨hie, hv, hvb⟩ := Wide.and3 (Wide.and2 hp).1
    have hbv := Wide.and2 (Wide.and2 hp).2
    have hA : okE N (addrB bv b i) = true := by
      show (decide (bv.getD b 0 < 8 + N) && okE N i) = true
      rw [hbv.2, hie]; rfl
    obtain ⟨hbR, ha, hil⟩ := r.addr L hb hi
    obtain ⟨τ₁, x₁, v₁, m₁, f₁⟩ := into_ok (toS sp (addrB bv b i)) (tk 0) 0 τ (r.agree L _ hA)
    rw [toS_denote sp N hN _ _ hA] at v₁
    have r₁ : RelBI sp N fp bv wv R W σ τ₁ := r.frame L ⟨m₁, fun x hx => f₁ x (by unfold tk; omega) (by omega)⟩
    have hB : bytes τ.mem R[b].base R[b].len = σ.heap[b].map some := by
      rw [← getD_get _ hb]; exact r.rbytes b hbR
    have hbyte := get_of_bytes hB hi
    have ea : (τ₁.reg (tk 0) + 0).toNat = R[b].base + (i.denote σ.env).toNat := by
      rw [show τ₁.reg (tk 0) + 0 = τ₁.reg (tk 0) from BitVec.add_zero _, v₁, ha]
    obtain ⟨τ₂, x₂, r₂⟩ := setB_ok r₁ L (of_decide_eq_true hv) (of_decide_eq_true (Wide.and2 hvb).1) (of_decide_eq_true (Wide.and2 hvb).2)
      (c := fun d => .ins (.lbu d (.r (tk 0)) 0)) (x := (σ.heap[b][(i.denote σ.env).toNat]).setWidth 64) fun d =>
      ⟨_, .ins (.lbu (v := σ.heap[b][(i.denote σ.env).toNat]) (by
          show ramB N fp R W (τ₁.reg (tk 0) + 0).toNat
          rw [ea]; exact ⟨R[b], List.mem_append_left _ (List.mem_append_left _ (List.getElem_mem hbR)), by omega, by omega⟩) (by
          show τ₁.mem (τ₁.reg (tk 0) + 0).toNat = _
          rw [ea, m₁]; exact hbyte)), upd_same _ _ _, rfl, fun y hy _ => upd_other _ _ hy⟩
    exact ⟨τ₂, .seq x₁ x₂, r₂⟩
  | @store b i e σ hb hi =>
    intro hp τ r
    obtain ⟨hie, hee, hbb⟩ := Wide.and3 hp
    obtain ⟨_, hbv⟩ := Wide.and2 hbb
    have hA : okE N (addrB bv b i) = true := by
      show (decide (bv.getD b 0 < 8 + N) && okE N i) = true
      rw [hbv, hie]; rfl
    obtain ⟨hbR, ha, hil⟩ := r.addr L hb hi
    obtain ⟨τ₁, x₁, v₁, m₁, f₁⟩ := into_ok (toS sp (addrB bv b i)) (tk 0) 0 τ (r.agree L _ hA)
    rw [toS_denote sp N hN _ _ hA] at v₁
    have r₁ : RelBI sp N fp bv wv R W σ τ₁ := r.frame L ⟨m₁, fun x hx => f₁ x (by unfold tk; omega) (by omega)⟩
    have g₁ := r₁.agree L e hee
    obtain ⟨τ₂, x₂, v₂, f₂, _, _⟩ := opnd_ok (k := 1) (into_ok (toS sp e) (tk 1) 1 τ₁ g₁) g₁
    rw [toS_denote sp N hN _ e hee] at v₂
    have ea : (τ₂.reg (tk 0) + 0).toNat = R[b].base + (i.denote σ.env).toNat := by
      rw [show τ₂.reg (tk 0) + 0 = τ₂.reg (tk 0) from BitVec.add_zero _, f₂.2 (tk 0) (by unfold tk; omega), v₁, ha]
    have hd := L.fr _ (List.getElem_mem hbR)
    unfold disjoint at hd; dsimp only at hd
    refine ⟨_, .seq x₁ (.seq x₂ (.ins (.sb ?_))), ?_⟩
    · show ramB N fp R W (τ₂.reg (tk 0) + 0).toNat
      rw [ea]; exact ⟨R[b], List.mem_append_left _ (List.mem_append_left _ (List.getElem_mem hbR)), by omega, by omega⟩
    · have hm : ∀ m, Mem.upd m ((Arg.r (tk 0)).eval τ₂.reg + 0).toNat = Mem.upd m (R[b].base + (i.denote σ.env).toNat) :=
        fun m => by show Mem.upd m (τ₂.reg (tk 0) + 0).toNat = _; rw [ea]
      refine ⟨fun j hj hs => (f₂.2 j (by have := hN j hj hs; omega)).trans (r₁.reg j hj hs), fun j hj hs => ?_,
        by rw [List.length_set, r.hlen], r.bvlen, r.base, fun b' hb' => ?_, fun b' hb' => ?_, r.whlen, r.wvlen,
        r.wbase, r.wblen, fun b' hb' => ?_⟩
      · show bytes (Mem.upd τ₂.mem _ _) _ _ = _
        rw [hm, bytes_upd_out (fun k hk => by omega), f₂.1]; exact r₁.slot j hj hs
      · by_cases hbb' : b' = b
        · subst hbb'
          rw [getD_set_self _ _ hb, List.length_set, ← getD_get _ hb]; exact r.blen b' hb'
        · rw [getD_set_ne _ _ hbb']; exact r.blen b' hb'
      · show bytes (Mem.upd τ₂.mem _ _) _ _ = _
        rw [hm, v₂, f₂.1, m₁]
        by_cases hbb' : b' = b
        · subst hbb'
          rw [bytes_upd_in hil, r.rbytes b' hb', getD_set_self _ _ hb, map_set, getD_get _ hb]
        · have hd' := pairwise_get L.rp hb' hbR hbb'
          unfold disjoint at hd'
          rw [bytes_upd_out (fun j hj => by omega), r.rbytes b' hb', getD_set_ne _ _ hbb']
      · have hd' := L.rw _ (List.getElem_mem hbR) _ (List.getElem_mem hb')
        unfold disjoint at hd'
        show bytes (Mem.upd τ₂.mem _ _) _ _ = _
        rw [hm, bytes_upd_out (fun j hj => by omega), f₂.1, m₁]; exact r.wbyts b' hb'
  | @load64 v b i σ hb hi =>
    intro hp τ r
    obtain ⟨hie, hv, hvb⟩ := Wide.and3 (Wide.and2 hp).1
    have hbw := Wide.and2 (Wide.and2 hp).2
    have hA : okE N (addrW wv b i) = true := by
      show (decide (wv.getD b 0 < 8 + N) && (okE N i && true)) = true
      rw [hbw.2, hie]; rfl
    obtain ⟨hbW, ha, hal, hil⟩ := r.waddr L hb hi
    obtain ⟨τ₁, x₁, v₁, m₁, f₁⟩ := into_ok (toS sp (addrW wv b i)) (tk 0) 0 τ (r.agree L _ hA)
    rw [toS_denote sp N hN _ _ hA] at v₁
    have r₁ : RelBI sp N fp bv wv R W σ τ₁ := r.frame L ⟨m₁, fun x hx => f₁ x (by unfold tk; omega) (by omega)⟩
    have ea : (τ₁.reg (tk 0) + 0).toNat = W[b].base + 8 * (i.denote σ.env).toNat := by
      rw [show τ₁.reg (tk 0) + 0 = τ₁.reg (tk 0) from BitVec.add_zero _, v₁, ha]
    have hl := r.wblen b hbW; rw [getD_get _ hb] at hl
    have hB : bytes τ₁.mem W[b].base (8 * σ.wheap[b].length) = (wbytes σ.wheap[b]).map some := by
      rw [hl, ← getD_get _ hb, m₁]; exact r.wbyts b hbW
    obtain ⟨τ₂, x₂, r₂⟩ := setB_ok r₁ L (of_decide_eq_true hv) (of_decide_eq_true (Wide.and2 hvb).1)
      (of_decide_eq_true (Wide.and2 hvb).2) (c := fun d => .ins (.ld d (tk 0) 0))
      (x := σ.wheap[b][(i.denote σ.env).toNat]) fun d =>
      ⟨_, .ins (.ld (by rw [ea]; exact fun j hj => ⟨W[b], List.mem_append_left _ (List.mem_append_right _
          (List.getElem_mem hbW)), by omega, by omega⟩) (by rw [ea]; exact hal)
          (by rw [ea]; exact bytes_word hB hi)), upd_same _ _ _, rfl, fun y hy _ => upd_other _ _ hy⟩
    exact ⟨τ₂, .seq x₁ x₂, r₂⟩
  | @store64 b i e σ hb hi =>
    intro hp τ r
    obtain ⟨hie, hee, hbb⟩ := Wide.and3 hp
    obtain ⟨_, hbw⟩ := Wide.and2 hbb
    have hA : okE N (addrW wv b i) = true := by
      show (decide (wv.getD b 0 < 8 + N) && (okE N i && true)) = true
      rw [hbw, hie]; rfl
    obtain ⟨hbW, ha, hal, hil⟩ := r.waddr L hb hi
    obtain ⟨τ₁, x₁, v₁, m₁, f₁⟩ := into_ok (toS sp (addrW wv b i)) (tk 0) 0 τ (r.agree L _ hA)
    rw [toS_denote sp N hN _ _ hA] at v₁
    have r₁ : RelBI sp N fp bv wv R W σ τ₁ := r.frame L ⟨m₁, fun x hx => f₁ x (by unfold tk; omega) (by omega)⟩
    obtain ⟨τ₂, x₂, v₂, m₂, f₂⟩ := into_ok (toS sp e) (tk 1) 1 τ₁ (r₁.agree L e hee)
    rw [toS_denote sp N hN _ e hee] at v₂
    have ea : (τ₂.reg (tk 0) + 0).toNat = W[b].base + 8 * (i.denote σ.env).toNat := by
      rw [show τ₂.reg (tk 0) + 0 = τ₂.reg (tk 0) from BitVec.add_zero _, f₂ (tk 0) (by unfold tk; omega)
        (by unfold tk; omega), v₁, ha]
    have hl := r.wblen b hbW; rw [getD_get _ hb] at hl
    have hd := L.fw _ (List.getElem_mem hbW)
    unfold disjoint at hd; dsimp only at hd
    refine ⟨_, .seq x₁ (.seq x₂ (.ins (.sd (by rw [ea]; exact fun j hj => ⟨W[b], List.mem_append_left _
      (List.mem_append_right _ (List.getElem_mem hbW)), by omega, by omega⟩) (by rw [ea]; exact hal)))), ?_⟩
    have hwr : ∀ m, Mem.wr m (τ₂.reg (tk 0) + 0).toNat (le8 (τ₂.reg (tk 1))) =
        Mem.wr m (W[b].base + 8 * (i.denote σ.env).toNat) (le8 (e.denote σ.env)) := fun m => by rw [ea, v₂]
    refine ⟨fun j hj hs => (f₂ j (by have := hN j hj hs; unfold tk; omega) (by have := hN j hj hs; omega)).trans (r₁.reg j hj hs), fun j hj hs => ?_,
      r.hlen, r.bvlen, r.base, r.blen, fun b' hb' => ?_, by rw [List.length_set, r.whlen], r.wvlen, r.wbase,
      fun b' hb' => ?_, fun b' hb' => ?_⟩
    · show bytes (Mem.wr _ _ _) _ _ = _
      rw [hwr, bytes_wr_out (by rw [length_le8]; omega), m₂]; exact r₁.slot j hj hs
    · have hd' := L.rw _ (List.getElem_mem hb') _ (List.getElem_mem hbW)
      unfold disjoint at hd'
      show bytes (Mem.wr _ _ _) _ _ = _
      rw [hwr, bytes_wr_out (by rw [length_le8]; omega), m₂, m₁]; exact r.rbytes b' hb'
    · by_cases hbb' : b' = b
      · subst hbb'
        rw [getD_set_self _ _ hb, List.length_set, ← getD_get _ hb]; exact r.wblen b' hb'
      · rw [getD_set_ne _ _ hbb']; exact r.wblen b' hb'
    · show bytes (Mem.wr _ _ _) _ _ = _
      rw [hwr, m₂, m₁]
      by_cases hbb' : b' = b
      · subst hbb'
        have hB : bytes τ.mem W[b'].base (8 * σ.wheap[b'].length) = (wbytes σ.wheap[b']).map some := by
          rw [hl, ← getD_get _ hb]; exact r.wbyts b' hb'
        rw [← hl, bytes_word_set hB hi, getD_set_self _ _ hb]
      · have hd' := pairwise_get L.wp hb' hbW hbb'
        unfold disjoint at hd'
        rw [bytes_wr_out (by rw [length_le8]; omega), r.wbyts b' hb', getD_set_ne _ _ hbb']
  | @mop m v a b σ =>
    intro hp τ r
    obtain ⟨habc, hvb⟩ := Wide.and2 hp
    obtain ⟨hae, hbe, hv⟩ := Wide.and3 habc
    obtain ⟨τ₁, x₁, v₁, m₁, f₁⟩ := into_ok (toS sp a) (tk 0) 0 τ (r.agree L a hae)
    rw [toS_denote sp N hN _ a hae] at v₁
    have r₁ : RelBI sp N fp bv wv R W σ τ₁ := r.frame L ⟨m₁, fun x hx => f₁ x (by unfold tk; omega) (by omega)⟩
    obtain ⟨τ₂, x₂, v₂, m₂, f₂⟩ := into_ok (toS sp b) (tk 1) 1 τ₁ (r₁.agree L b hbe)
    rw [toS_denote sp N hN _ b hbe] at v₂
    have r₂ : RelBI sp N fp bv wv R W σ τ₂ := r₁.frame L ⟨m₂, fun x hx => f₂ x (by unfold tk; omega) (by omega)⟩
    have v₁' : τ₂.reg (tk 0) = a.denote σ.env := by
      rw [f₂ (tk 0) (by unfold tk; omega) (by unfold tk; omega), v₁]
    obtain ⟨τ₃, x₃, r₃⟩ := setB_ok r₂ L (of_decide_eq_true hv) (of_decide_eq_true (Wide.and2 hvb).1)
      (of_decide_eq_true (Wide.and2 hvb).2) (c := fun d => .ins (.mop m d (.r (tk 0)) (.r (tk 1))))
      (x := m.eval (a.denote σ.env) (b.denote σ.env)) fun d =>
      ⟨_, .ins .mop, by simp only [Arg.eval, v₁', v₂, upd_same], rfl, fun y hy _ => upd_other _ _ hy⟩
    exact ⟨τ₃, .seq x₁ (.seq x₂ x₃), r₃⟩
  | seq _ _ iha ihb =>
    intro hp τ r
    obtain ⟨pa, pb⟩ := Wide.and2 hp
    obtain ⟨τ₁, x₁, r₁⟩ := iha pa τ r
    obtain ⟨τ₂, x₂, r₂⟩ := ihb pb τ₁ r₁
    exact ⟨τ₂, .seq x₁ x₂, r₂⟩
  | @loopF c body σ hc =>
    intro hp τ r
    obtain ⟨hce, _⟩ := Wide.and2 hp
    obtain ⟨τ₁, x₁, f₁⟩ := loopCode_exit (body := irB sp bv wv body) (r.agree L c hce)
      (by rw [toS_denote sp N hN _ c hce]; exact hc)
    exact ⟨τ₁, x₁, r.frame L f₁⟩
  | @loopT c body σ _ _ hc _ _ ihb ihl =>
    intro hp τ r
    obtain ⟨hce, hpb⟩ := Wide.and2 hp
    obtain ⟨τ₁, f₁, hx⟩ := loopCode_iter (body := irB sp bv wv body) (r.agree L c hce)
      (by rw [toS_denote sp N hN _ c hce]; exact hc)
    obtain ⟨τ₂, x₂, r₂⟩ := ihb hpb τ₁ (r.frame L f₁)
    obtain ⟨τ₃, x₃, r₃⟩ := ihl hp τ₂ r₂
    exact ⟨τ₃, hx τ₂ τ₃ x₂ x₃, r₃⟩

end
end Proven.Mach
