/- The tree evaluator: an arithmetic expression tree given as bytes in prefix encoding (`Spec/Tree.lean`),
evaluated by a recursive-descent function, proved end to end against `Tree.eval ∘ decode` (`ImplementsW`).

`ev()` reads the tag at the cursor (global 5) and advances; for a leaf it reads the value byte, for a node
it calls itself twice (non-tail recursion, depth = depth of the tree) and combines the results. -/
import Nano.Base.Riscv.Examples.CallExamples
import Spec.Tree
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

namespace Proven.Mach.Riscv
open Proven.Mach

theorem load_exec {v b : Nat} {i : BExp} {σ : BState} {bs : List (BitVec 8)} {x : BitVec 8} {k : Nat}
    (hH : σ.heap[b]? = some bs) (hk : (i.denote σ.env).toNat = k) (hx : bs[k]? = some x) :
    BExec (.load v b i) σ ⟨σ.env.set v (x.setWidth 64), σ.heap, σ.wheap⟩ := by
  subst hk
  obtain ⟨hb, rfl⟩ := List.getElem?_eq_some_iff.1 hH
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  exact BExec.load hb hi

/-- `v := in[cursor]; cursor := cursor + 1` -/
def stepB (v : Nat) : BStmt := .seq (.load v 0 (.var 5)) (.assign 5 (.bin .add (.var 5) (.const 1)))

theorem step_exec {v : Nat} (hv : v ≠ 5) {env : BEnv} {bs : List (BitVec 8)} {Wh : WHeap} {p : Nat} {x : BitVec 8}
    (h5 : env 5 = BitVec.ofNat 64 p) (hlt : bs.length < 2 ^ 64) (hx : bs[p]? = some x) :
    BExec (stepB v) ⟨env, [bs], Wh⟩ ⟨(env.set v (x.setWidth 64)).set 5 (BitVec.ofNat 64 (p + 1)), [bs], Wh⟩ := by
  have hp : p < bs.length := (List.getElem?_eq_some_iff.1 hx).1
  refine .seq (load_exec (bs := bs) rfl (by
    show (env 5).toNat = p; rw [h5, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)) hx) ?_
  have := BExec.assign (v := 5) (e := .bin .add (.var 5) (.const 1)) (σ := ⟨env.set v (x.setWidth 64), [bs], Wh⟩)
  have e : (BExp.bin .add (.var 5) (.const 1)).denote (env.set v (x.setWidth 64)) = BitVec.ofNat 64 (p + 1) := by
    show (if 5 = v then _ else env 5) + 1 = _
    rw [if_neg (Ne.symm hv), h5, BitVec.ofNat_add]; rfl
  rw [e] at this; exact this

/-- the bytes of a tree as memory cells -/
def encB (t : Tree) : List (BitVec 8) := t.enc.map (·.toBitVec)

/-- the result expression's value: tag 1 add, tag 2 sub, otherwise xor -/
def selOp (t a b : BitVec 64) : BitVec 64 :=
  if (if t = 1 then (1 : BitVec 64) else 0) = 0 then (if (if t = 2 then (1 : BitVec 64) else 0) = 0 then a ^^^ b else a - b)
  else a + b

/-- `ev()`; locals: `tag`, `a`, `b` -/
def evFn : Fn :=
  ⟨0, 3, .seq (.base (stepB 8)) (.ite (.var 8) (.seq (.call 9 1 []) (.call 10 1 [])) (.base (stepB 9))),
    .ite (.bin .eq (.var 8) (.const 1)) (.bin .add (.var 9) (.var 10))
      (.ite (.bin .eq (.var 8) (.const 2)) (.bin .sub (.var 9) (.var 10)) (.bin .xor (.var 9) (.var 10)))⟩

/-- `main`: cursor := 0, call `ev`, store the result word -/
def mainT : Fn :=
  ⟨0, 1, .seq (.base (.assign 5 (.const 0))) (.seq (.call 8 1 []) (.base (.store64 0 (.const 0) (.var 8)))),
    .const 0⟩

def treeProg : Prog := [mainT, evFn]

theorem ev_spec : ∀ (t : Tree) (pre rest bs : List (BitVec 8)) (Wh : WHeap) (env : BEnv),
    bs = pre ++ encB t ++ rest → bs.length < 2 ^ 64 → env 5 = BitVec.ofNat 64 pre.length → env 10 = 0 →
    ∃ σ₁, CExec treeProg (32 * t.depth) evFn.body ⟨env, [bs], Wh⟩ σ₁ ∧
      σ₁.env 5 = BitVec.ofNat 64 (pre.length + (encB t).length) ∧ (∀ i, i < 8 → i ≠ 5 → σ₁.env i = env i) ∧
      σ₁.heap = [bs] ∧ σ₁.wheap = Wh ∧ evFn.ret.denote σ₁.env = t.eval
  | .leaf v, pre, rest, bs, Wh, env, hbs, hlt, h5, h10 => by
    have hx0 : bs[pre.length]? = some (0 : BitVec 8) := by rw [hbs]; simp [encB, Tree.enc]
    have hx1 : bs[pre.length + 1]? = some v.toBitVec := by rw [hbs]; simp [encB, Tree.enc]
    refine ⟨_, .seq (.base (step_exec (v := 8) (by decide) h5 hlt hx0))
      (.iteF rfl (.base (step_exec (v := 9) (by decide) rfl hlt hx1))), rfl, fun i hi hi5 => ?_, rfl, rfl, ?_⟩
    · show (if i = 5 then _ else (if i = 9 then _ else (if i = 5 then _ else (if i = 8 then _ else env i)))) = env i
      rw [if_neg hi5, if_neg (by omega), if_neg hi5, if_neg (by omega)]
    · show selOp ((0 : BitVec 8).setWidth 64) (v.toBitVec.setWidth 64) (env 10) = _
      rw [h10]
      show v.toBitVec.setWidth 64 ^^^ 0 = BitVec.ofNat 64 v.toNat
      rw [zx_byte]; exact BitVec.xor_zero
  | .node op l r, pre, rest, bs, Wh, env, hbs, hlt, h5, h10 => by
    have hx0 : bs[pre.length]? = some op.tag.toBitVec := by rw [hbs]; simp [encB, Tree.enc]
    obtain ⟨σl, hl, hl5, hlg, hlH, hlW, hlv⟩ := ev_spec l (pre ++ [op.tag.toBitVec]) (encB r ++ rest) bs Wh
      (callEnv ((env.set 8 (op.tag.toBitVec.setWidth 64)).set 5 (BitVec.ofNat 64 (pre.length + 1))) [])
      (by rw [hbs]; simp [encB, Tree.enc]) hlt (by
        show BitVec.ofNat 64 (pre.length + 1) = _; rw [List.length_append]; rfl) rfl
    obtain ⟨el, Hl, Wl⟩ := σl
    dsimp only at hl5 hlg hlH hlW hlv
    subst hlH; subst hlW
    obtain ⟨σr, hr, hr5, hrg, hrH, hrW, hrv⟩ := ev_spec r (pre ++ [op.tag.toBitVec] ++ encB l) rest bs Wl
      (callEnv ((retEnv ((env.set 8 (op.tag.toBitVec.setWidth 64)).set 5 (BitVec.ofNat 64 (pre.length + 1))) el).set 9
        (evFn.ret.denote el)) [])
      (by rw [hbs]; simp [encB, Tree.enc]) hlt (by
        show el 5 = _; rw [hl5, List.length_append (as := pre ++ [op.tag.toBitVec])]) rfl
    obtain ⟨er, Hr, Wr⟩ := σr
    dsimp only at hr5 hrg hrH hrW hrv
    subst hrH; subst hrW
    have htag : op.tag.toBitVec.setWidth 64 ≠ (0 : BitVec 64) := by cases op <;> decide
    refine ⟨_, .seq (.base (step_exec (v := 8) (by decide) h5 hlt hx0)) (.iteT htag (.seq
        (CExec.call (f := 1) (k' := 32 * l.depth) (by decide) rfl
          (by show 32 + 32 * l.depth ≤ 32 * (1 + max l.depth r.depth); omega) hl)
        (CExec.call (f := 1) (k' := 32 * r.depth) (by decide) rfl
          (by show 32 + 32 * r.depth ≤ 32 * (1 + max l.depth r.depth); omega) hr))),
      ?_, fun i hi hi5 => ?_, rfl, rfl, ?_⟩
    · show er 5 = _
      rw [hr5]; congr 1
      simp [encB, Tree.enc]; omega
    · show (if i = 10 then _ else if i < 8 then er i else _) = env i
      rw [if_neg (by omega), if_pos hi, hrg i hi hi5]
      show (if i < 8 then (if i = 9 then _ else if i < 8 then el i else _) else _) = env i
      rw [if_pos hi, if_neg (by omega), if_pos hi, hlg i hi hi5]
      show (if i < 8 then (if i = 5 then _ else if i = 8 then _ else env i) else _) = env i
      rw [if_pos hi, if_neg hi5, if_neg (by omega)]
    · show selOp (op.tag.toBitVec.setWidth 64) (evFn.ret.denote el) (evFn.ret.denote er) = _
      rw [hlv, hrv]
      cases op <;> rfl

/-- the reference: decode the bytes, evaluate the tree -/
def treeF (x : List UInt8) : BitVec 64 :=
  match decAll (α := Tree) x with
  | some t => t.eval
  | none => 0

theorem treeProg_computes : Computes treeProg 0 treeF (fun x => (∃ t : Tree, x = Bytes.enc t) ∧ x.length < 2 ^ 64)
    (fun n => 16 + (32 + 32 * n)) := by
  rintro x env w0 ⟨⟨t, rfl⟩, hlt⟩ henv
  obtain ⟨σ₁, h₁, -, -, hH, hW, hv⟩ := ev_spec t [] [] (encB t) [[w0]] (callEnv ((callEnv env []).set 5 0) [])
    (by simp) (by simp [encB]; exact hlt) rfl rfl
  obtain ⟨e1, H1, W1⟩ := σ₁
  dsimp only at hH hW hv
  subst hH; subst hW
  have hd := Tree.depth_le t
  refine ⟨_, CExec.call (f := 0) (k' := 32 + 32 * t.depth) (by decide) rfl
    (by show 16 + (32 + 32 * t.depth) ≤ 16 + (32 + 32 * (Tree.enc t).length); omega)
    (.seq (.base .assign) (.seq (CExec.call (f := 1) (k' := 32 * t.depth) (by decide) rfl (Nat.le_refl _) h₁)
      (.base (BExec.store64 (b := 0) (i := .const 0) (e := .var 8) (by exact Nat.succ_pos _)
        (by exact Nat.succ_pos _))))), ?_⟩
  show [[evFn.ret.denote e1]] = [[treeF (Bytes.enc t)]]
  rw [hv]; simp [treeF, decAll_enc]

theorem treeProg_wf : WfProg treeProg 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : f = 0 ∨ f = 1 := by simp [treeProg] at hf; omega
    rcases this with rfl | rfl <;> wf_calls [treeProg, mainT, evFn, stepB]
  · wf_calls [treeProg, mainT, evFn, stepB]

/-- **The tree evaluator on the Sail model.**  For every tree `t`, with `enc t` (`n` bytes) as the input,
the code leaves `enc (t.eval)` in the output word, using at most `space n = 32 n + 72` bytes of the work
block (the recursion depth is at most the depth of `t`, which is less than `n`). -/
theorem treeEval_implements : ImplementsW (callsCode treeProg 0) treeF
    (fun x => (∃ t : Tree, x = Bytes.enc t) ∧ x.length < 2 ^ 64) (fun n => 16 + (32 + 32 * n) + 24) :=
  callsCode_implements treeProg_wf treeProg_computes

end Proven.Mach.Riscv
