/- The compiler with its result stored to memory: `compileStore e` computes `e` with the code of
`Proven/Code.lean` (`gen e 0`, result in `t0`), stores it with `sd t0, 0(s1)` and returns.
The output pointer is passed in `s1` (x9): every caller-saved register other than `a0..a3` is a
temporary of `gen`, and `gen_ok` only guarantees that registers outside the temporaries are kept.
`s1` is callee-saved and never written, so `calleeSavedKept` still holds. -/
import Proven.Compiler
import Proven.MemSteps

set_option linter.unusedVariables false

namespace Proven

def iSdOut : BitVec 32 := iSd 5 9                               -- sd t0, 0(s1)

def compileStore (e : Exp) : List (BitVec 32) := gen e 0 ++ [iSdOut, iRet]

theorem T_ne_9' : ∀ k < 11, T k ≠ 9 := by decide

theorem instrAt_frame {s s' : St} {p : BitVec 64} {w : BitVec 32} (h : instrAt s p w)
    (hm : ∀ i < 4, s'.mem[p.toNat + i]? = s.mem[p.toNat + i]?) : instrAt s' p w := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨by simpa [h0] using hm 0 (by omega), by rw [hm 1 (by omega)]; exact h1,
    by rw [hm 2 (by omega)]; exact h2, by rw [hm 3 (by omega)]; exact h3⟩

/-- **Store compiler correctness** (memory-model form).  From any `Cfg` state with the code at `pc`,
return address in `ra`, and the output pointer in `s1` naming block `L[k] = [s1, s1 + 8)` of an ok
layout `L` (8-aligned, not overlapping the code): the Sail model runs to `ra` with the 8
little-endian bytes of `e.denote (a0, a1, a2, a3)` in `L[k]`, every other block of `L` and every
address outside `L[k]` unchanged, callee-saved registers and `Cfg` kept. -/
theorem compileStore_ok (e : Exp) (he : e.depth < 11) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileStore e))
    (hok : codeOK pc (compileStore e).length) (hra : (getX s 1).toNat % 2 = 0)
    {L : Layout} (hL : L.ok) {k : Nat} (hk : k < L.length)
    (hout : L[k] = Region.cells ⟨(getX s 9).toNat, 8⟩) (hal : (getX s 9).toNat % 8 = 0)
    (hcode : Block.disj (Region.cells ⟨pc.toNat, 4 * (compileStore e).length⟩) L[k]) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesOf s' L[k] = (le8 (e.denote fun i => getX s (A i))).map some ∧
      (∀ j (hj : j < L.length), j ≠ k → bytesOf s' L[j] = bytesOf s L[j]) ∧
      (∀ a, a ∉ L[k] → s'.mem[a]? = s.mem[a]?) ∧
      Cfg s' ∧ calleeSavedKept s s' := by
  have hlen : (compileStore e).length = (gen e 0).length + 2 := by simp [compileStore]
  rw [hlen] at hcode
  simp only [compileStore] at hc hok
  rw [codeAt_append] at hc
  rw [List.length_append] at hok
  obtain ⟨ok1, ok2⟩ := codeOK_append hok
  obtain ⟨s₁, ⟨n₁, st₁⟩, R₁, v₁⟩ := gen_ok (fun i => getX s (A i)) e 0 (by omega) h hpc hc.1 ok1 (fun _ => rfl)
  have hc2 := codeAt_mem R₁.mem hc.2
  have h9 : getX s₁ 9 = getX s 9 := R₁.keep 9 (fun i _ hi => (T_ne_9' i hi).symm)
  have hra₁ : getX s₁ 1 = getX s 1 := R₁.keep 1 (fun i _ hi => (T_ne_1' i hi).symm)
  have hram : 0x80000000 ≤ (getX s 9).toNat ∧ (getX s 9).toNat + 8 ≤ 0x100000000 := by
    have hr := (hL.1 _ (List.getElem_mem hk)).1
    have h1 := hr (getX s 9).toNat (by rw [hout, Region.mem_cells]; dsimp only; omega)
    have h2 := hr ((getX s 9).toNat + 7) (by rw [hout, Region.mem_cells]; dsimp only; omega)
    omega
  -- `sd t0, 0(s1)`
  obtain ⟨s₂, hn₂⟩ := step_sd R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) 5 9 (by decide) (by decide)
    (by simpa [iSdOut] using hc2 0 (by simp)) (by rw [h9]; exact hram) (by rw [h9]; exact hal)
  have hra₂ : getX s₂ 1 = getX s 1 := by rw [hn₂.x, if_neg (by decide), hra₁]
  -- the `ret` word is outside the output block
  have hp : (pc + BitVec.ofNat 64 (4 * (gen e 0).length) + BitVec.ofNat 64 (4 * 1)).toNat =
      pc.toNat + 4 * (gen e 0).length + 4 := by
    have := hok.2.2; simp [BitVec.toNat_add]; omega
  have hret : instrAt s₂ (pc + BitVec.ofNat 64 (4 * (gen e 0).length) + BitVec.ofNat 64 (4 * 1)) iRet := by
    refine instrAt_frame (by simpa using hc2 1 (by simp)) fun i hi => ?_
    rw [hn₂.mem, storeBytes_eq, hp]
    refine writeCells_get_notMem fun hm => hcode (pc.toNat + 4 * (gen e 0).length + 4 + i) ?_ ?_
    · rw [Region.mem_cells]; dsimp only; omega
    · rw [hout]; rw [h9] at hm; simpa [le8] using hm
  obtain ⟨s₃, hn₃⟩ := step_ret hn₂.cfg hn₂.pc
    (codeOK_pcOK (codeOK_append (a := 1) (b := 1) ok2).2 (by simp)) hret (by rw [hra₂]; exact hra)
  have hm₃ : s₃.mem = storeBytes s.mem (getX s 9).toNat (le8 (e.denote fun i => getX s (A i))) := by
    rw [hn₃.mem, hn₂.mem, R₁.mem, h9, show (5 : Fin 32) = T 0 from rfl, v₁]
  obtain ⟨b1, b2, b3⟩ := store_block8_mem hL hk hout hm₃
  refine ⟨n₁ + 2, s₃, Steps.trans st₁ ⟨s₂, hn₂.ret, s₃, hn₃.ret, rfl⟩, by rw [hn₃.pc, hra₂], b1, b2, b3,
    hn₃.cfg, ?_⟩
  have keep : ∀ j : Fin 32, (∀ i, i < 11 → j ≠ T i) → getX s₃ j = getX s j := by
    intro j hj
    rw [hn₃.x, if_neg (by simp), hn₂.x, if_neg (by simp)]
    exact R₁.keep j (fun i _ hi => hj i hi)
  have ne : ∀ j ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)),
      ∀ i, i < 11 → j ≠ T i := by decide
  have h₃ := hn₃.cfg
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₃.x2, h.x2, keep 2 (ne 2 (by decide))]
  · rw [h₃.x8, h.x8, keep 8 (ne 8 (by decide))]
  · rw [h₃.x9, h.x9, keep 9 (ne 9 (by decide))]
  · rw [h₃.x18, h.x18, keep 18 (ne 18 (by decide))]
  · rw [h₃.x19, h.x19, keep 19 (ne 19 (by decide))]
  · rw [h₃.x20, h.x20, keep 20 (ne 20 (by decide))]
  · rw [h₃.x21, h.x21, keep 21 (ne 21 (by decide))]
  · rw [h₃.x22, h.x22, keep 22 (ne 22 (by decide))]
  · rw [h₃.x23, h.x23, keep 23 (ne 23 (by decide))]
  · rw [h₃.x24, h.x24, keep 24 (ne 24 (by decide))]
  · rw [h₃.x25, h.x25, keep 25 (ne 25 (by decide))]
  · rw [h₃.x26, h.x26, keep 26 (ne 26 (by decide))]
  · rw [h₃.x27, h.x27, keep 27 (ne 27 (by decide))]

/-- **Store compiler correctness** (contiguous regions): the output region `rs[k] = ⟨s1, 8⟩` of a
list of pairwise disjoint in-RAM regions receives the 8 little-endian bytes of the result; the other
regions and all memory outside the output region are unchanged. -/
theorem compileStore_regions (e : Exp) (he : e.depth < 11) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileStore e))
    (hok : codeOK pc (compileStore e).length) (hra : (getX s 1).toNat % 2 = 0)
    {rs : List Region} (hin : ∀ r ∈ rs, r.inRAM) (hd : rs.Pairwise disjoint) {k : Nat} (hk : k < rs.length)
    (hout : rs[k] = ⟨(getX s 9).toNat, 8⟩) (hal : (getX s 9).toNat % 8 = 0)
    (hcode : disjoint ⟨pc.toNat, 4 * (compileStore e).length⟩ rs[k]) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' (getX s 9).toNat 8 = (le8 (e.denote fun i => getX s (A i))).map some ∧
      (∀ j (hj : j < rs.length), j ≠ k → bytesAt s' rs[j].base rs[j].len = bytesAt s rs[j].base rs[j].len) ∧
      unchangedOutside s s' [rs[k]] ∧ Cfg s' ∧ calleeSavedKept s s' := by
  have hk' : k < (rs.map Region.cells).length := by simpa using hk
  obtain ⟨n, s', st, p1, p2, p3, p4, p5, p6⟩ := compileStore_ok e he h hpc hc hok hra (regions_ok hin hd) hk'
    (by simp [hout]) hal (by simpa using hcode.cells)
  simp only [List.getElem_map] at p2 p3 p4
  refine ⟨n, s', st, p1, by rw [bytesAt_eq]; simpa [hout] using p2,
    fun j hj hjk => by simpa [bytesAt_eq] using p3 j (by simpa using hj) hjk,
    unchangedOutside_of fun a ha => p4 a (ha _ (by simp)), p5, p6⟩

end Proven
