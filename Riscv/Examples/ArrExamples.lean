/- Byte-array examples, end to end from ordinary Lean functions:
(a) `sumBytes xs` (sum of the bytes, 64-bit), (b)/(c) `(xs.take n).map f` written to an output block
(`f = id`: copy / `List.take`; `f = (· + 1)`). -/
import Riscv.Direct.Arr

set_option linter.unusedVariables false

namespace Proven

/-! ## Small lemmas -/

theorem ult_ne {a b : BitVec 64} : (Op.eval .ult a b ≠ 0) ↔ a.toNat < b.toNat := by
  simp only [Op.eval]; by_cases h : a < b <;> simp [h]
  all_goals simpa [BitVec.lt_def] using h

theorem toNat_inc {a : BitVec 64} {n : Nat} (h : a.toNat < n) (hn : n < 2 ^ 64) : (a + 1).toNat = a.toNat + 1 := by
  have e : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, e]; omega

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by simp; omega

theorem setWidth_setWidth8 (x : BitVec 8) : (x.setWidth 64).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-! ## (a) sum of bytes -/

def sumBytes (xs : List (BitVec 8)) : BitVec 64 := xs.foldl (fun acc x => acc + x.setWidth 64) 0

theorem sumBytes_take_succ {xs : List (BitVec 8)} {i : Nat} (h : i < xs.length) :
    sumBytes (xs.take (i + 1)) = sumBytes (xs.take i) + xs[i].setWidth 64 := by
  rw [List.take_succ_eq_append_getElem h]; simp only [sumBytes, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `a2 := 0; a3 := 0; while a3 < a1 { a4 := in[a3]; a2 := a2 + a4; a3 := a3 + 1 }` (block 0 = input, base `a0`) -/
def sumProg : AStmt :=
  .seq (.assign 2 (.const 0)) (.seq (.assign 3 (.const 0))
    (.loop (.bin .ult (.var 3) (.var 1))
      (.seq (.load 4 0 (.var 3)) (.seq (.assign 2 (.bin .add (.var 2) (.var 4)))
        (.assign 3 (.bin .add (.var 3) (.const 1)))))))

theorem AExec.assign' {v : Fin 8} {e : AExp} {σ σ' : AState} (h : σ' = ⟨σ.env.set v (e.denote σ.env), σ.heap⟩) :
    AExec (.assign v e) σ σ' := h ▸ .assign

theorem sumProg_exec (σ : AState) (xs : List (BitVec 8)) (hh : σ.heap = [xs])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 64) :
    ∃ σ', AExec sumProg σ σ' ∧ σ'.heap = [xs] ∧ σ'.env 2 = sumBytes xs := by
  obtain ⟨σ₁, hl, hq⟩ := AExec.loop_inv (c := .bin .ult (.var 3) (.var 1))
    (b := .seq (.load 4 0 (.var 3)) (.seq (.assign 2 (.bin .add (.var 2) (.var 4)))
        (.assign 3 (.bin .add (.var 3) (.const 1)))))
    (fun τ => τ.heap = [xs] ∧ τ.env 1 = BitVec.ofNat 64 xs.length ∧ (τ.env 3).toNat ≤ xs.length ∧
      τ.env 2 = sumBytes (xs.take (τ.env 3).toNat))
    (fun τ => τ.heap = [xs] ∧ τ.env 2 = sumBytes xs)
    (fun τ => xs.length - (τ.env 3).toNat)
    (fun ⟨env, heap⟩ ⟨hh, h1, hle, hs⟩ hc => by
      dsimp only at hh h1 hle hs; subst hh
      simp only [AExp.denote, ult_ne, h1, toNat_ofNat_lt hn] at hc
      refine ⟨_, .seq (.load (by simp) (by simpa using hc)) (.seq .assign .assign), ?_⟩
      have e3 := toNat_inc hc hn
      refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩
      all_goals simp only [AEnv.set, AExp.denote, Op.eval]
      all_goals simp only [Fin.reduceEq, if_false, if_true]
      · exact h1
      · rw [e3]; omega
      · rw [e3, sumBytes_take_succ hc, hs]; rfl
      · rw [e3]; omega)
    (fun ⟨env, heap⟩ ⟨hh, h1, hle, hs⟩ hc => by
      dsimp only at hh h1 hle hs ⊢
      have : ¬ (env 3).toNat < xs.length := fun hlt =>
        (ult_ne (a := env 3) (b := env 1)).2 (by rw [h1, toNat_ofNat_lt hn]; exact hlt) hc
      refine ⟨hh, ?_⟩
      rw [hs, List.take_of_length_le (by omega)])
    ⟨(σ.env.set 2 0).set 3 0, σ.heap⟩ ⟨hh, by simpa [AEnv.set] using h1, by simp [AEnv.set], by simp [AEnv.set, sumBytes]⟩
  exact ⟨σ₁, .seq (AExec.assign' rfl) (.seq (AExec.assign' rfl) hl), hq⟩

/-! ## (b), (c) `(xs.take n).map f` into the output block -/

/-- `a4 := min a2 a1; a5 := 0; while a5 < a4 { a6 := in[a5]; out[a5] := g; a5 := a5 + 1 }`
(block 0 = input, base `a0`, length `a1`; block 1 = output, base `a3`; `n` in `a2`; `g` reads the byte in `a6`) -/
def mapProg (g : AExp) : AStmt :=
  .seq (.assign 4 (.ite (.bin .ult (.var 2) (.var 1)) (.var 2) (.var 1)))
  (.seq (.assign 5 (.const 0))
   (.loop (.bin .ult (.var 5) (.var 4))
     (.seq (.load 6 0 (.var 5)) (.seq (.store 1 (.var 5) g) (.assign 5 (.bin .add (.var 5) (.const 1)))))))

theorem map_take_set {xs out : List (BitVec 8)} (f : BitVec 8 → BitVec 8) {i : Nat} (hx : i < xs.length)
    (ho : i < out.length) :
    (List.map f (xs.take i) ++ out.drop i).set i (f xs[i]) = List.map f (xs.take (i + 1)) ++ out.drop (i + 1) := by
  have hl : (List.map f (xs.take i)).length = i := by simp; omega
  rw [List.set_append_right _ _ (by rw [hl]; exact Nat.le_refl _), hl, Nat.sub_self, List.drop_eq_getElem_cons ho, List.set_cons_zero,
    List.take_succ_eq_append_getElem hx, List.map_append, List.append_assoc]; rfl

theorem mapProg_exec (g : AExp) (f : BitVec 8 → BitVec 8)
    (hg : ∀ (env : AEnv) (x : BitVec 8), env 6 = x.setWidth 64 → (g.denote env).setWidth 8 = f x)
    (σ : AState) (xs out : List (BitVec 8)) (hh : σ.heap = [xs, out])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 64)
    (hout : min (σ.env 2).toNat xs.length ≤ out.length) :
    ∃ σ', AExec (mapProg g) σ σ' ∧
      σ'.heap = [xs, (xs.take (σ.env 2).toNat).map f ++ out.drop (min (σ.env 2).toNat xs.length)] := by
  let m := min (σ.env 2).toNat xs.length
  let v4 := (AExp.ite (.bin .ult (.var 2) (.var 1)) (.var 2) (.var 1)).denote σ.env
  have hm : v4.toNat = m := by
    simp only [v4, m, AExp.denote, Op.eval, h1]
    by_cases hlt : σ.env 2 < BitVec.ofNat 64 xs.length
    · rw [if_pos hlt]; simp only [BitVec.lt_def, toNat_ofNat_lt hn] at hlt; simp; omega
    · rw [if_neg hlt]; simp only [BitVec.lt_def, toNat_ofNat_lt hn] at hlt; simp; omega
  obtain ⟨σ₁, hl, hq⟩ := AExec.loop_inv (c := .bin .ult (.var 5) (.var 4))
    (b := .seq (.load 6 0 (.var 5)) (.seq (.store 1 (.var 5) g) (.assign 5 (.bin .add (.var 5) (.const 1)))))
    (fun τ => τ.heap = [xs, (xs.take (τ.env 5).toNat).map f ++ out.drop (τ.env 5).toNat] ∧
      (τ.env 4).toNat = m ∧ (τ.env 5).toNat ≤ m)
    (fun τ => τ.heap = [xs, (xs.take m).map f ++ out.drop m])
    (fun τ => m - (τ.env 5).toNat)
    (fun ⟨env, heap⟩ ⟨hh, h4, hle⟩ hc => by
      dsimp only at hh h4 hle; subst hh
      simp only [AExp.denote, ult_ne, h4] at hc
      have hx : (env 5).toNat < xs.length := by omega
      have ho : (env 5).toNat < out.length := by omega
      have e5 := toNat_inc (show (env 5).toNat < m by omega) (show m < 2 ^ 64 by omega)
      refine ⟨_, .seq (.load (by simp) (by simpa using hx))
        (.seq (.store (by simp) (by simp [AEnv.set, AExp.denote]; omega)) .assign), ⟨?_, ?_, ?_⟩, ?_⟩
      all_goals simp only [AEnv.set, AExp.denote, Op.eval]
      all_goals simp only [Fin.reduceEq, if_false, if_true]
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.set_cons_succ, List.set_cons_zero]
        rw [hg _ xs[(env 5).toNat] (by simp [AEnv.set]), map_take_set f hx ho, e5]
      · exact h4
      · rw [e5]; omega
      · rw [e5]; omega)
    (fun ⟨env, heap⟩ ⟨hh, h4, hle⟩ hc => by
      dsimp only at hh h4 hle ⊢
      have : ¬ (env 5).toNat < m := fun hlt => (ult_ne (a := env 5) (b := env 4)).2 (by rw [h4]; exact hlt) hc
      rw [hh, show (env 5).toNat = m by omega])
    ⟨(σ.env.set 4 v4).set 5 0, σ.heap⟩ ⟨by simpa [AEnv.set] using hh, by simpa [AEnv.set] using hm, by simp [AEnv.set]⟩
  refine ⟨σ₁, .seq (AExec.assign' rfl) (.seq (AExec.assign' rfl) hl), ?_⟩
  have : xs.take m = xs.take (σ.env 2).toNat := by
    simp only [m]; by_cases hle : (σ.env 2).toNat ≤ xs.length
    · rw [Nat.min_eq_left hle]
    · rw [Nat.min_eq_right (by omega), List.take_of_length_le (Nat.le_refl _),
        List.take_of_length_le (by omega)]
  rw [hq, this]

/-! ## Machine theorems -/

/-- memory unchanged: outside the regions, and each region reads back the same bytes -/
theorem mem_same {s s' : St} {R : List Region} (hu : unchangedOutside s s' R)
    (hb : ∀ r ∈ R, bytesAt s' r.base r.len = bytesAt s r.base r.len) : ∀ a : Nat, s'.mem[a]? = s.mem[a]? := by
  intro a
  by_cases h : ∃ r ∈ R, r.base ≤ a ∧ a < r.base + r.len
  · obtain ⟨r, hr, h1, h2⟩ := h
    have := congrArg (·[a - r.base]?) (hb r hr)
    simp only [bytesAt, List.getElem?_map, List.getElem?_range (show a - r.base < r.len by omega),
      Option.map_some, Option.some.injEq] at this
    rwa [Nat.add_sub_cancel' h1] at this
  · exact hu a fun r hr => by
      have : ¬ (r.base ≤ a ∧ a < r.base + r.len) := fun h' => h ⟨r, hr, h'⟩
      omega

theorem sumProg_wf : sumProg.wf [0] := by simp [sumProg, AStmt.wf, AExp.depth, compileA, gen8, addrE, opCode, genConst]

def sumCode : List (BitVec 32) := compileAF [0] sumProg

/-- **sum of bytes**: input `xs` at `a0` (length in `a1`): returns to `ra` with `a2 = sumBytes xs`,
memory unchanged, callee-saved registers and `Cfg` kept. -/
theorem sumCode_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc sumCode) (hok : codeOK pc sumCode.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs : List (BitVec 8)} {base : Nat} (hin : Region.inRAM ⟨base, xs.length⟩)
    (hcd : disjoint ⟨pc.toNat, 4 * sumCode.length⟩ ⟨base, xs.length⟩)
    (h0 : getX s 10 = BitVec.ofNat 64 base) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (hx : bytesAt s base xs.length = xs.map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 12 = sumBytes xs ∧
      (∀ a : Nat, s'.mem[a]? = s.mem[a]?) ∧ Cfg s' ∧ calleeSavedKept s s' := by
  have hn : xs.length < 2 ^ 64 := by unfold Region.inRAM at hin; dsimp only at hin; omega
  obtain ⟨σ', hex, hh, h2⟩ := sumProg_exec ⟨fun i => getX s (A8 i), [xs]⟩ xs rfl h1 hn
  have hrel : Rel [0] [⟨base, xs.length⟩] ⟨fun i => getX s (A8 i), [xs]⟩ s :=
    ⟨fun _ => rfl, rfl, rfl, fun b hb => by obtain _ | b := b; exact h0; simp at hb,
      fun b hb => by obtain _ | b := b; rfl; simp at hb, fun b hb => by obtain _ | b := b; exact hx; simp at hb⟩
  refine runsTo_mono (compileAF_ok [0] sumProg_wf ⟨fun r hr => by simp at hr; exact hr ▸ hin, by simp⟩
    hex h hpc hc hok (fun r hr => by simp at hr; exact hr ▸ hcd) hrel hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5⟩
  refine ⟨p1, by rw [← h2]; exact p2.env 2, mem_same p3 fun r hr => ?_, p4, p5⟩
  simp at hr; subst hr
  have := p2.bytes 0 (by simp); simp only [hh] at this; rw [hx]; exact this

theorem takeProg_wf : (mapProg (.var 6)).wf [0, 3] := by simp [mapProg, AStmt.wf, AExp.depth, compileA, gen8, addrE, opCode, genConst]
theorem incProg_wf : (mapProg (.bin .add (.var 6) (.const 1))).wf [0, 3] := by
  simp [mapProg, AStmt.wf, AExp.depth, compileA, gen8, addrE, opCode, genConst]

/-- a region that reads back the same bytes can be dropped from `unchangedOutside` -/
theorem unchanged_drop {s s' : St} {r : Region} {R : List Region} (hu : unchangedOutside s s' (r :: R))
    (hb : bytesAt s' r.base r.len = bytesAt s r.base r.len) : unchangedOutside s s' R := by
  intro a ha
  by_cases h : r.base ≤ a ∧ a < r.base + r.len
  · have := congrArg (·[a - r.base]?) hb
    simp only [bytesAt, List.getElem?_map, List.getElem?_range (show a - r.base < r.len by omega),
      Option.map_some, Option.some.injEq] at this
    rwa [Nat.add_sub_cancel' h.1] at this
  · exact hu a fun r' hr' => by
      simp only [List.mem_cons] at hr'; rcases hr' with rfl | hr'; · omega
      exact ha r' hr'

/-- **`(xs.take n).map f` into the output block** (`mapProg g`, `g` computing `f` on the byte in `a6`):
input `xs` at `a0` (length `a1`), `n` in `a2`, output block `out` at `a3` with room for `min n |xs|` bytes.
Returns to `ra` with the output block holding `(xs.take n).map f` followed by the rest of `out`, the
input unchanged, all memory outside the output block unchanged, callee-saved registers and `Cfg` kept. -/
theorem mapCode_ok (g : AExp) (f : BitVec 8 → BitVec 8)
    (hg : ∀ (env : AEnv) (x : BitVec 8), env 6 = x.setWidth 64 → (g.denote env).setWidth 8 = f x)
    (hwf : (mapProg g).wf [0, 3]) {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileAF [0, 3] (mapProg g))) (hok : codeOK pc (compileAF [0, 3] (mapProg g)).length)
    (hra : (getX s 1).toNat % 2 = 0)
    {xs out : List (BitVec 8)} {inb outb : Nat} (hR : RegOK [⟨inb, xs.length⟩, ⟨outb, out.length⟩])
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, out.length⟩],
      disjoint ⟨pc.toNat, 4 * (compileAF [0, 3] (mapProg g)).length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (h3 : getX s 13 = BitVec.ofNat 64 outb)
    (hx : bytesAt s inb xs.length = xs.map some) (ho : bytesAt s outb out.length = out.map some)
    (hout : min (getX s 12).toNat xs.length ≤ out.length) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' outb out.length =
        ((xs.take (getX s 12).toNat).map f ++ out.drop (min (getX s 12).toNat xs.length)).map some ∧
      bytesAt s' inb xs.length = xs.map some ∧ unchangedOutside s s' [⟨outb, out.length⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' := by
  have hn : xs.length < 2 ^ 64 := by
    have := hR.1 _ (List.mem_cons_self ..); unfold Region.inRAM at this; dsimp only at this; omega
  obtain ⟨σ', hex, hh⟩ := mapProg_exec g f hg ⟨fun i => getX s (A8 i), [xs, out]⟩ xs out rfl h1 hn hout
  have hrel : Rel [0, 3] [⟨inb, xs.length⟩, ⟨outb, out.length⟩] ⟨fun i => getX s (A8 i), [xs, out]⟩ s :=
    ⟨fun _ => rfl, rfl, rfl, fun b hb => by obtain _ | _ | b := b; exact h0; exact h3; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; rfl; rfl; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; exact hx; exact ho; simp at hb; omega⟩
  refine runsTo_mono (compileAF_ok [0, 3] hwf hR hex h hpc hc hok hcd hrel hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5⟩
  have e0 := p2.bytes 0 (by simp); have e1 := p2.bytes 1 (by simp)
  simp only [hh] at e0 e1
  exact ⟨p1, by simpa using e1, by simpa using e0, unchanged_drop p3 (by simpa [hx] using e0), p4, p5⟩

theorem setWidth_inc (x : BitVec 8) : (x.setWidth 64 + 1).setWidth 8 = x + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  have : (1 : BitVec 64).toNat = 1 := rfl
  have : (1 : BitVec 8).toNat = 1 := rfl
  have := x.isLt
  simp only [*]; omega

def takeCode : List (BitVec 32) := compileAF [0, 3] (mapProg (.var 6))
def incCode : List (BitVec 32) := compileAF [0, 3] (mapProg (.bin .add (.var 6) (.const 1)))

/-- **`List.take`** ("take n"): with an output block of exactly `min n |xs|` bytes, it ends up holding
`xs.take n`; the input and all memory outside the output block are unchanged. -/
theorem takeCode_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc takeCode) (hok : codeOK pc takeCode.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs out : List (BitVec 8)} {inb outb : Nat} (hR : RegOK [⟨inb, xs.length⟩, ⟨outb, out.length⟩])
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, out.length⟩], disjoint ⟨pc.toNat, 4 * takeCode.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (h3 : getX s 13 = BitVec.ofNat 64 outb)
    (hx : bytesAt s inb xs.length = xs.map some) (ho : bytesAt s outb out.length = out.map some)
    (hout : out.length = min (getX s 12).toNat xs.length) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' outb out.length = (xs.take (getX s 12).toNat).map some ∧
      bytesAt s' inb xs.length = xs.map some ∧ unchangedOutside s s' [⟨outb, out.length⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' := by
  refine runsTo_mono (mapCode_ok (.var 6) id (fun env x he => by simp [AExp.denote, he, setWidth_setWidth8])
    takeProg_wf h hpc hc hok hra hR hcd h0 h1 h3 hx ho (by omega)) ?_
  rintro s' ⟨p1, p2, p3⟩
  refine ⟨p1, ?_, p3⟩
  rw [p2, ← hout, List.drop_length]; simp

/-- **`List.map (· + 1)` of a prefix** -/
theorem incCode_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc incCode) (hok : codeOK pc incCode.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs out : List (BitVec 8)} {inb outb : Nat} (hR : RegOK [⟨inb, xs.length⟩, ⟨outb, out.length⟩])
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, out.length⟩], disjoint ⟨pc.toNat, 4 * incCode.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (h3 : getX s 13 = BitVec.ofNat 64 outb)
    (hx : bytesAt s inb xs.length = xs.map some) (ho : bytesAt s outb out.length = out.map some)
    (hout : out.length = min (getX s 12).toNat xs.length) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' outb out.length = ((xs.take (getX s 12).toNat).map (· + 1)).map some ∧
      bytesAt s' inb xs.length = xs.map some ∧ unchangedOutside s s' [⟨outb, out.length⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' := by
  refine runsTo_mono (mapCode_ok (.bin .add (.var 6) (.const 1)) (· + 1)
    (fun env x he => by simp only [AExp.denote, Op.eval, he]; exact setWidth_inc x)
    incProg_wf h hpc hc hok hra hR hcd h0 h1 h3 hx ho (by omega)) ?_
  rintro s' ⟨p1, p2, p3⟩
  refine ⟨p1, ?_, p3⟩
  rw [p2, ← hout, List.drop_length]; simp

end Proven
