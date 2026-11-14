/- Load/store step lemmas in memory-model form: `ld` reads the little-endian value of 8 bytes,
`sb`/`sd` effects on the blocks of an ok layout and on contiguous regions.  Built from the
per-word lemmas of `Proven/MemWords.lean`; nothing here unfolds the Sail model. -/
import Proven.MemWords

set_option linter.unusedVariables false

namespace Proven

theorem le8_cat (x : BitVec 64) : (x.extractLsb' 56 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 40 8 ++
    x.extractLsb' 32 8 ++ x.extractLsb' 24 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 8 8 ++
    x.extractLsb' 0 8 : BitVec 64) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | (rw [show 0 + i = i by omega]; simp [*]; try (intro; omega)) | (rw [show 8 + (i - 8) = i by omega]; simp [*]; try (intro; omega)) | (rw [show 16 + (i - 8 - 8) = i by omega]; simp [*]; try (intro; omega)) | (rw [show 24 + (i - 8 - 8 - 8) = i by omega]; simp [*]; try (intro; omega)) | (rw [show 32 + (i - 8 - 8 - 8 - 8) = i by omega]; simp [*]; try (intro; omega)) | (rw [show 40 + (i - 8 - 8 - 8 - 8 - 8) = i by omega]; simp [*]; try (intro; omega)) | (rw [show 48 + (i - 8 - 8 - 8 - 8 - 8 - 8) = i by omega]; simp [*]; try (intro; omega)) | (rw [show 56 + (i - 8 - 8 - 8 - 8 - 8 - 8 - 8) = i by omega]; simp [*]; try (intro; omega)) | omega

theorem bytesAt_le8 {s : St} {a : Nat} {v : BitVec 64} (h : bytesAt s a 8 = (le8 v).map some) :
    s.mem[a]? = some (v.extractLsb' 0 8) ∧ s.mem[a + 1]? = some (v.extractLsb' 8 8) ∧
    s.mem[a + 2]? = some (v.extractLsb' 16 8) ∧ s.mem[a + 3]? = some (v.extractLsb' 24 8) ∧
    s.mem[a + 4]? = some (v.extractLsb' 32 8) ∧ s.mem[a + 5]? = some (v.extractLsb' 40 8) ∧
    s.mem[a + 6]? = some (v.extractLsb' 48 8) ∧ s.mem[a + 7]? = some (v.extractLsb' 56 8) := by
  simpa [bytesAt, le8, List.range, List.range.loop] using h

variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

/-- `ld rd, 0(rs1)`: if the 8 bytes at `x[rs1]` are the little-endian bytes of `v`, then `x[rd] := v` -/
theorem step_ld (rd rs1 : Fin 32) (hd : rd ∈ memD) (hb : rs1 ∈ memB) (hi : instrAt s pc (iLd rd rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 8 ≤ 0x100000000)
    (hal : (getX s rs1).toNat % 8 = 0) {v : BitVec 64}
    (hv : bytesAt s (getX s rs1).toNat 8 = (le8 v).map some) :
    ∃ s', Next s s' (pc + 4) rd v s.mem := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytesAt_le8 hv
  have := step_ld_raw h hpc hok rd rs1 hd hb hi ha hal h0 h1 h2 h3 h4 h5 h6 h7
  rwa [le8_cat] at this

/-- `lbu rd, 0(rs1)` -/
theorem step_lbu (rd rs1 : Fin 32) (hd : rd ∈ memD) (hb : rs1 ∈ memB) (hi : instrAt s pc (iLbu rd rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 1 ≤ 0x100000000) {b : BitVec 8}
    (hv : s.mem[(getX s rs1).toNat]? = some b) :
    ∃ s', Next s s' (pc + 4) rd (b.setWidth 64) s.mem :=
  step_lbu_raw h hpc hok rd rs1 hd hb hi ha hv

/-- `sb rs2, 0(rs1)` -/
theorem step_sb (rs2 rs1 : Fin 32) (hd : rs2 ∈ memD) (hb : rs1 ∈ memB) (hi : instrAt s pc (iSb rs2 rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 1 ≤ 0x100000000) :
    ∃ s', Next s s' (pc + 4) 0 0 (s.mem.insert (getX s rs1).toNat ((getX s rs2).setWidth 8)) :=
  step_sb_raw h hpc hok rs2 rs1 hd hb hi ha

/-- `sd rs2, 0(rs1)`: the 8 little-endian bytes of `x[rs2]` at `x[rs1]` -/
theorem step_sd (rs2 rs1 : Fin 32) (hd : rs2 ∈ memD) (hb : rs1 ∈ memB) (hi : instrAt s pc (iSd rs2 rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 8 ≤ 0x100000000)
    (hal : (getX s rs1).toNat % 8 = 0) :
    ∃ s', Next s s' (pc + 4) 0 0 (storeBytes s.mem (getX s rs1).toNat (le8 (getX s rs2))) :=
  step_sd_raw h hpc hok rs2 rs1 hd hb hi ha hal

omit h hpc hok

/-! ## Effects on an ok layout -/

/-- a one-byte store into cell `i` of block `L[k]` -/
theorem Next.store_cell {s s' : St} {pc rd v} {L : Layout} (hL : L.ok) {k i : Nat} (hk : k < L.length)
    (hi : i < L[k].length) {b : BitVec 8} (hn : Next s s' pc rd v (s.mem.insert L[k][i] b)) :
    bytesOf s' L[k] = (bytesOf s L[k]).set i (some b) ∧
    (∀ j (hj : j < L.length), j ≠ k → bytesOf s' L[j] = bytesOf s L[j]) ∧
    (∀ a, a ∉ L[k] → s'.mem[a]? = s.mem[a]?) := by
  simp only [bytesOf, hn.mem]; exact layout_write hL hk hi b

/-- an 8-byte store filling block `L[k] = [a, a + 8)` (memory form) -/
theorem store_block8_mem {s s' : St} {L : Layout} (hL : L.ok) {k : Nat} (hk : k < L.length)
    {a : Nat} (hout : L[k] = Region.cells ⟨a, 8⟩) {x : BitVec 64}
    (hmem : s'.mem = storeBytes s.mem a (le8 x)) :
    bytesOf s' L[k] = (le8 x).map some ∧
    (∀ j (hj : j < L.length), j ≠ k → bytesOf s' L[j] = bytesOf s L[j]) ∧
    (∀ a, a ∉ L[k] → s'.mem[a]? = s.mem[a]?) := by
  have hm : s'.mem = writeCells s.mem L[k] (le8 x) := by
    rw [hmem, storeBytes_eq, hout]; rfl
  simp only [bytesOf, hm]
  exact layout_writeAll hL hk (by rw [hout]; simp [Region.cells, le8])

/-- an 8-byte store filling block `L[k] = [a, a + 8)` -/
theorem Next.store_block8 {s s' : St} {pc rd v} {L : Layout} (hL : L.ok) {k : Nat} (hk : k < L.length)
    {a : Nat} (hout : L[k] = Region.cells ⟨a, 8⟩) {x : BitVec 64}
    (hn : Next s s' pc rd v (storeBytes s.mem a (le8 x))) :
    bytesOf s' L[k] = (le8 x).map some ∧
    (∀ j (hj : j < L.length), j ≠ k → bytesOf s' L[j] = bytesOf s L[j]) ∧
    (∀ a, a ∉ L[k] → s'.mem[a]? = s.mem[a]?) :=
  store_block8_mem hL hk hout hn.mem

/-! ## The same for contiguous regions (`bytesAt`, `unchangedOutside`) -/

theorem regions_ok {rs : List Region} (hin : ∀ r ∈ rs, r.inRAM) (hd : rs.Pairwise disjoint) :
    Layout.ok (rs.map Region.cells) := Layout.ok_regions hin hd

/-- `sb` to byte `i` of region `rs[k]` -/
theorem Next.store_region {s s' : St} {pc rd v} {rs : List Region} (hin : ∀ r ∈ rs, r.inRAM)
    (hd : rs.Pairwise disjoint) {k i : Nat} (hk : k < rs.length) (hi : i < rs[k].len) {b : BitVec 8}
    (hn : Next s s' pc rd v (s.mem.insert (rs[k].base + i) b)) :
    bytesAt s' rs[k].base rs[k].len = (bytesAt s rs[k].base rs[k].len).set i (some b) ∧
    (∀ j (hj : j < rs.length), j ≠ k → bytesAt s' rs[j].base rs[j].len = bytesAt s rs[j].base rs[j].len) ∧
    unchangedOutside s s' [rs[k]] := by
  have hk' : k < (rs.map Region.cells).length := by simpa using hk
  have hi' : i < (rs.map Region.cells)[k].length := by simpa [Region.cells] using hi
  have hc : (rs.map Region.cells)[k][i] = rs[k].base + i := by simp [Region.cells]
  obtain ⟨h1, h2, h3⟩ := Next.store_cell (regions_ok hin hd) hk' hi' (hc ▸ hn)
  simp only [List.getElem_map] at h1 h2 h3
  refine ⟨by simpa [bytesAt_eq] using h1, fun j hj hjk => by simpa [bytesAt_eq] using h2 j (by simpa using hj) hjk,
    unchangedOutside_of fun a ha => h3 a (ha _ (by simp))⟩

/-- `sd` filling region `rs[k] = ⟨a, 8⟩` -/
theorem Next.store_region8 {s s' : St} {pc rd v} {rs : List Region} (hin : ∀ r ∈ rs, r.inRAM)
    (hd : rs.Pairwise disjoint) {k : Nat} (hk : k < rs.length) {a : Nat} (hout : rs[k] = ⟨a, 8⟩)
    {x : BitVec 64} (hn : Next s s' pc rd v (storeBytes s.mem a (le8 x))) :
    bytesAt s' a 8 = (le8 x).map some ∧
    (∀ j (hj : j < rs.length), j ≠ k → bytesAt s' rs[j].base rs[j].len = bytesAt s rs[j].base rs[j].len) ∧
    unchangedOutside s s' [rs[k]] := by
  have hk' : k < (rs.map Region.cells).length := by simpa using hk
  obtain ⟨h1, h2, h3⟩ := Next.store_block8 (regions_ok hin hd) hk' (by simp [hout]) hn
  simp only [List.getElem_map] at h1 h2 h3
  refine ⟨by rw [bytesAt_eq]; simpa [hout] using h1,
    fun j hj hjk => by simpa [bytesAt_eq] using h2 j (by simpa using hj) hjk,
    unchangedOutside_of fun a ha => h3 a (ha _ (by simp))⟩

end Proven
