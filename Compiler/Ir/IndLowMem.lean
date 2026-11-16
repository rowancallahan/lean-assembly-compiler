/- The correctness of the inductive path's lowering to RTL (`Compiler/Ir/IndLow.lean`), part 1: how a value lives in
RTL memory (`Rv`: a pointer to a live block of 4 cells `[tag, x, l, r]`, `z` the word `0`), memory growth (`MLe`: the
input, the block table and every written cell stay), and the big-step meaning (`SC.Ex`) of the small pieces of code
(moves, constants, operations, loads, `mkCell`, `fld`). -/
import Compiler.Ir.StructLbl
import Compiler.Ir.IndLow

namespace Proven.Ir.IndLow
open Proven.Ir Proven.Mach Proven.Mach.Ind
set_option autoImplicit false

/-! ## registers -/

@[simp] theorem upd_same (g : VReg → Val) (d : VReg) (v : Val) : upd g d v d = v := by simp [upd]
theorem upd_ne (g : VReg → Val) {d q : Nat} (v : Val) (h : q ≠ d) : upd g d v q = g q := by simp [upd, h]

/-! ## values in memory -/

/-- **`v` is the value `c` in memory `m`** -/
inductive Rv (m : Mem) : Val → C → Prop
  | z : Rv m (.w 0) .z
  | c {b c0 : Nat} {t : Nat} {x : BitVec 64} {vl vr : Val} {l r : C} : m.blk b = some (c0, 4) → t < 256 →
      m.cells[c0]? = some (some (.w (BitVec.ofNat 64 t))) → m.cells[c0 + 1]? = some (some (.w x)) →
      m.cells[c0 + 2]? = some (some vl) → m.cells[c0 + 3]? = some (some vr) → Rv m vl l → Rv m vr r →
      Rv m (.p b 0) (.c t x l r)

/-- a value of kind `k`: a word, or a tree in memory -/
def RvK : (k : Kd) → Mem → Val → k.den → Prop
  | .w, _, v, y => v = .w y
  | .t, m, v, y => Rv m v y

/-- **memory grows**: same input, live blocks and written cells stay -/
def MLe (m m' : Mem) : Prop :=
  m'.inp = m.inp ∧ (∀ b c0 sz, m.blk b = some (c0, sz) → m'.blk b = some (c0, sz)) ∧
    ∀ (i : Nat) (v : Val), m.cells[i]? = some (some v) → m'.cells[i]? = some (some v)

theorem MLe.refl (m : Mem) : MLe m m := ⟨rfl, fun _ _ _ h => h, fun _ _ h => h⟩

theorem MLe.trans {m₁ m₂ m₃ : Mem} (a : MLe m₁ m₂) (b : MLe m₂ m₃) : MLe m₁ m₃ :=
  ⟨b.1.trans a.1, fun bk c0 sz h => b.2.1 _ _ _ (a.2.1 _ _ _ h), fun i v h => b.2.2 _ _ (a.2.2 _ _ h)⟩

theorem Rv.mono {m m' : Mem} (hm : MLe m m') {v : Val} {c : C} (h : Rv m v c) : Rv m' v c := by
  induction h with
  | z => exact .z
  | c hb ht e0 e1 e2 e3 _ _ ihl ihr =>
    exact .c (hm.2.1 _ _ _ hb) ht (hm.2.2 _ _ e0) (hm.2.2 _ _ e1) (hm.2.2 _ _ e2) (hm.2.2 _ _ e3) ihl ihr

theorem RvK.mono {m m' : Mem} (hm : MLe m m') {k : Kd} {v : Val} {y : k.den} (h : RvK k m v y) : RvK k m' v y := by
  cases k
  · exact h
  · exact Rv.mono hm h

/-- the default of a kind is the word `0` -/
theorem RvK.dflt (m : Mem) (k : Kd) : RvK k m (.w 0) k.dflt := by
  cases k
  · rfl
  · exact .z

/-! ## single instructions -/

section
variable {P : Prog VReg}

theorem ex_mov (g : VReg → Val) (m : Mem) (d s : VReg) : SC.Ex P (mov d s) g m (upd g d (g s)) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, Rhs.eval, Arg.eval])

theorem ex_setK (g : VReg → Val) (m : Mem) (d : VReg) (c : BitVec 64) : SC.Ex P (setK d c) g m (upd g d (.w c)) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, Rhs.eval, Arg.eval])

theorem ex_bin {g : VReg → Val} (m : Mem) (o : Op) (d a b : VReg) {x y : BitVec 64} (ha : g a = .w x) (hb : g b = .w y) :
    SC.Ex P (bin o d a b) g m (upd g d (.w (o.eval x y))) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, Rhs.eval, Arg.word, Arg.eval, ha, hb])

theorem ex_addK {g : VReg → Val} (m : Mem) (d a : VReg) (c : BitVec 64) {x : BitVec 64} (ha : g a = .w x) :
    SC.Ex P (addK d a c) g m (upd g d (.w (x + c))) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, Rhs.eval, Arg.word, Arg.eval, ha, Op.eval])

/-- load cell `k` of a 4-cell block -/
theorem ex_ld {g : VReg → Val} {m : Mem} {d p : VReg} {k : Nat} {b c0 : Nat} {v : Val} (hp : g p = .p b 0)
    (hb : m.blk b = some (c0, 4)) (hk : k < 4) (hc : m.cells[c0 + k]? = some (some v)) :
    SC.Ex P (.i (.ld d p k)) g m (upd g d v) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, hp, hb, hk, hc])

theorem nz_w {g : VReg → Val} {x : VReg} {y : BitVec 64} (h : g x = .w y) : (nz x).eval g = some (!decide (y = 0)) := by
  simp [nz, Tst.eval, Arg.eval, h, Cond.eval]

theorem nz_p {g : VReg → Val} {x : VReg} {b o : Nat} (h : g x = .p b o) : (nz x).eval g = some true := by
  simp [nz, Tst.eval, Arg.eval, h, nullTest]

theorem Rv.inv {m : Mem} {v : Val} {t : Nat} {x : BitVec 64} {l r : C} (h : Rv m v (.c t x l r)) :
    ∃ b c0 vl vr, v = .p b 0 ∧ m.blk b = some (c0, 4) ∧ t < 256 ∧ m.cells[c0]? = some (some (.w (BitVec.ofNat 64 t))) ∧
      m.cells[c0 + 1]? = some (some (.w x)) ∧ m.cells[c0 + 2]? = some (some vl) ∧ m.cells[c0 + 3]? = some (some vr) ∧
      Rv m vl l ∧ Rv m vr r := by
  cases h with
  | c hb ht e0 e1 e2 e3 rl rr => exact ⟨_, _, _, _, rfl, hb, ht, e0, e1, e2, e3, rl, rr⟩

/-- `fld`: a field of a value (`z` reads as `zk`) -/
theorem ex_fld {g : VReg → Val} {m : Mem} {d v : VReg} {c : C} (hv : Rv m (g v) c) (k : Nat) (hk : k < 4) (zk : BitVec 64) :
    ∃ w, SC.Ex P (fld d v k zk) g m (upd g d w) m ∧ (k = 0 → zk = 255 → w = .w (BitVec.ofNat 64 c.tag)) ∧
      (k = 1 → zk = 0 → w = .w c.xv) ∧ (k = 2 → zk = 0 → Rv m w c.lv) ∧ (k = 3 → zk = 0 → Rv m w c.rv) := by
  generalize hgv : g v = vv at hv
  cases hv with
  | z =>
    refine ⟨_, .iteF (by rw [nz_w hgv]; rfl) (ex_setK g m d zk), ?_, ?_, ?_, ?_⟩ <;> intro _ hz <;> subst hz
    · rfl
    · rfl
    · exact .z
    · exact .z
  | c hb ht e0 e1 e2 e3 rl rr =>
    rename_i b c0 t x vl vr l r
    have hc : ∃ w, m.cells[c0 + k]? = some (some w) ∧ (k = 0 → w = .w (BitVec.ofNat 64 t)) ∧ (k = 1 → w = .w x) ∧
        (k = 2 → w = vl) ∧ (k = 3 → w = vr) := by
      match k, hk with
      | 0, _ => exact ⟨_, e0, fun _ => rfl, (nomatch ·), (nomatch ·), (nomatch ·)⟩
      | 1, _ => exact ⟨_, e1, (nomatch ·), fun _ => rfl, (nomatch ·), (nomatch ·)⟩
      | 2, _ => exact ⟨_, e2, (nomatch ·), (nomatch ·), fun _ => rfl, (nomatch ·)⟩
      | 3, _ => exact ⟨_, e3, (nomatch ·), (nomatch ·), (nomatch ·), fun _ => rfl⟩
    obtain ⟨w, hw, h0, h1, h2, h3⟩ := hc
    refine ⟨w, .iteT (nz_p hgv) (ex_ld hgv hb hk hw), fun e _ => h0 e, fun e _ => h1 e, fun e _ => ?_, fun e _ => ?_⟩
    · rw [h2 e]; exact rl
    · rw [h3 e]; exact rr

/-- the memory after `mkCell` -/
def _root_.Proven.Ir.Mem.push4 (m : Mem) (a b c d : Val) : Mem :=
  { m with cells := m.cells ++ [some a, some b, some c, some d], blks := m.blks ++ [(m.cells.length, 4, true)] }

theorem blk_new (m : Mem) (cs : List (Option Val)) :
    ({ m with cells := cs, blks := m.blks ++ [(m.cells.length, 4, true)] } : Mem).blk (m.blks.length + 2) =
      some (m.cells.length, 4) := by
  simp [Mem.blk]

theorem ex_mkCell (g : VReg → Val) (m : Mem) (d : VReg) (t x l r : Arg VReg) :
    SC.Ex P (mkCell d t x l r) g m (upd g d (.p (m.blks.length + 2) 0))
      (m.push4 (t.eval (upd g d (.p (m.blks.length + 2) 0))) (x.eval (upd g d (.p (m.blks.length + 2) 0)))
        (l.eval (upd g d (.p (m.blks.length + 2) 0))) (r.eval (upd g d (.p (m.blks.length + 2) 0)))) := by
  generalize hg' : upd g d (.p (m.blks.length + 2) 0) = g'
  have hd : g' d = .p (m.blks.length + 2) 0 := by rw [← hg']; simp
  have hb : ∀ cs : List (Option Val), ({ m with cells := cs, blks := m.blks ++ [(m.cells.length, 4, true)] } : Mem).blk
      (m.blks.length + 2) = some (m.cells.length, 4) := blk_new m
  simp only [mkCell, SC.seqs]
  have e4 : List.replicate (BitVec.toNat (4 : BitVec 64)) (none : Option Val) = [none, none, none, none] := rfl
  refine .seq (g₁ := g') (m₁ := Mem.mk m.inp m.out (m.cells ++ [none, none, none, none])
      (m.blks ++ [(m.cells.length, 4, true)]))
    (.i (e := [.alloc 4]) (fun _ _ _ h => nomatch h) (by simp only [Inst.exec, Arg.word, Arg.eval, hg', e4]; rfl)) ?_
  refine .seq (.i (e := []) (fun _ _ _ h => nomatch h) (by simp only [Inst.exec, hd, hb]; rfl)) ?_
  refine .seq (.i (e := []) (fun _ _ _ h => nomatch h) (by simp only [Inst.exec, hd, hb]; rfl)) ?_
  refine .seq (.i (e := []) (fun _ _ _ h => nomatch h) (by simp only [Inst.exec, hd, hb]; rfl)) ?_
  refine .i (e := []) (fun _ _ _ h => nomatch h) ?_
  simp only [Inst.exec, hd, hb]
  simp [Mem.push4]

/-- `mkCell` makes the value -/
theorem mkCell_rv {m : Mem} {t : Nat} {x : BitVec 64} {vl vr : Val} {l r : C} (ht : t < 256) (hl : Rv m vl l)
    (hr : Rv m vr r) :
    MLe m (m.push4 (.w (BitVec.ofNat 64 t)) (.w x) vl vr) ∧
      Rv (m.push4 (.w (BitVec.ofNat 64 t)) (.w x) vl vr) (.p (m.blks.length + 2) 0) (.c t x l r) := by
  have hle : MLe m (m.push4 (.w (BitVec.ofNat 64 t)) (.w x) vl vr) := by
    refine ⟨rfl, fun b c0 sz h => ?_, fun i v h => ?_⟩
    · match b, h with
      | k + 2, h =>
        simp only [Mem.blk, Mem.push4] at h ⊢
        have hk : k < m.blks.length := by
          rcases e : m.blks[k]? with _ | ⟨a⟩
          · rw [e] at h; exact nomatch h
          · exact (List.getElem?_eq_some_iff.1 e).1
        rw [List.getElem?_append_left hk]; exact h
    · simp only [Mem.push4]
      have hi : i < m.cells.length := (List.getElem?_eq_some_iff.1 h).1
      rw [List.getElem?_append_left hi]; exact h
  refine ⟨hle, .c (blk_new m _) ht ?_ ?_ ?_ ?_ (hl.mono hle) (hr.mono hle)⟩ <;> simp [Mem.push4]

end

end Proven.Ir.IndLow
