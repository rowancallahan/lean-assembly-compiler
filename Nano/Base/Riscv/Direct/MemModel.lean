/- The memory model: blocks of byte cells, layouts, and the separation / frame theorems.
A `Block` is a list of byte addresses (logical index `i` ↦ cell `b[i]`); a `Layout` is the list of blocks
in use (no allocator: a block is in use iff it is in the list).  Contiguous `Region`s are an instance
(`Region.cells`).  Nothing here mentions the Sail model beyond `St.mem`. -/
import Spec.Riscv

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Proven

abbrev Mem := Std.ExtHashMap Nat (BitVec 8)
abbrev Block := List Nat
abbrev Layout := List Block

/-- the bytes of block `b` in logical order -/
def readCells (m : Mem) (b : Block) : List (Option (BitVec 8)) := b.map (m[·]?)
def bytesOf (s : St) (b : Block) : List (Option (BitVec 8)) := readCells s.mem b

/-- write `vs` to the cells `cs`, pairwise (stops at the shorter list) -/
def writeCells : Mem → List Nat → List (BitVec 8) → Mem
  | m, c :: cs, v :: vs => writeCells (m.insert c v) cs vs
  | m, _, _ => m

/-- write `vs` at `a, a+1, ...` -/
def storeBytes (m : Mem) (a : Nat) (vs : List (BitVec 8)) : Mem := writeCells m (List.range' a vs.length) vs

def Block.inRAM (b : Block) : Prop := ∀ a ∈ b, 0x80000000 ≤ a ∧ a < 0x100000000
def Block.disj (b c : Block) : Prop := ∀ a ∈ b, a ∉ c

/-- all cells in RAM, no block repeats a cell, no two blocks share a cell -/
def Layout.ok (L : Layout) : Prop := (∀ b ∈ L, b.inRAM ∧ b.Nodup) ∧ L.Pairwise Block.disj

theorem Block.disj.symm {b c : Block} (h : b.disj c) : c.disj b := fun a hc hb => h a hb hc

theorem Layout.ok.disj {L : Layout} (h : L.ok) {i j : Nat} (hi : i < L.length) (hj : j < L.length)
    (hij : i ≠ j) : L[i].disj L[j] := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact List.pairwise_iff_getElem.mp h.2 i j hi hj hlt
  · exact (List.pairwise_iff_getElem.mp h.2 j i hj hi hlt).symm

/-! ## Single-cell writes -/

theorem get_insert_ne {m : Mem} {a c : Nat} {v} (h : a ≠ c) : (m.insert a v)[c]? = m[c]? := by
  simp [Std.ExtHashMap.getElem?_insert, h]

theorem readCells_insert_notMem {m : Mem} {a : Nat} {v} {b : Block} (h : a ∉ b) :
    readCells (m.insert a v) b = readCells m b := by
  simp only [readCells, List.map_inj_left]
  intro c hc; exact get_insert_ne (fun e => h (e ▸ hc))

theorem nodup_ne {b : List Nat} (hb : b.Nodup) {i j : Nat} (hi : i < b.length) (hj : j < b.length)
    (hij : i ≠ j) : b[i] ≠ b[j] := by
  have := List.pairwise_iff_getElem.mp hb
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact this i j hi hj h
  · exact Ne.symm (this j i hj hi h)

theorem readCells_insert_idx {m : Mem} {b : Block} (hb : b.Nodup) {i : Nat} (hi : i < b.length) {v} :
    readCells (m.insert b[i] v) b = (readCells m b).set i (some v) := by
  apply List.ext_getElem (by simp [readCells])
  intro j h1 h2
  have hj : j < b.length := by simpa [readCells] using h1
  simp only [readCells, List.getElem_map, List.getElem_set]
  by_cases hij : i = j
  · subst hij; simp
  · have : b[i] ≠ b[j] := nodup_ne hb hi hj hij
    simp [Std.ExtHashMap.getElem?_insert, this, hij]

/-- write cell `i` of block `L[k]` of an ok layout: (1) block `k` changes at index `i` only,
(2) every other block is unchanged, (3) every address outside block `k` is unchanged. -/
theorem layout_write {m : Mem} {L : Layout} (hL : L.ok) {k : Nat} (hk : k < L.length) {i : Nat}
    (hi : i < L[k].length) (v : BitVec 8) :
    readCells (m.insert L[k][i] v) L[k] = (readCells m L[k]).set i (some v) ∧
    (∀ j (hj : j < L.length), j ≠ k → readCells (m.insert L[k][i] v) L[j] = readCells m L[j]) ∧
    (∀ a, a ∉ L[k] → (m.insert L[k][i] v)[a]? = m[a]?) :=
  ⟨readCells_insert_idx (hL.1 _ (List.getElem_mem hk)).2 hi,
   fun j hj hjk => readCells_insert_notMem fun hm => hL.disj hk hj (Ne.symm hjk) _ (List.getElem_mem hi) hm,
   fun a ha => get_insert_ne fun e => ha (e ▸ List.getElem_mem hi)⟩

/-! ## Multi-cell writes -/

theorem writeCells_get_notMem {m : Mem} {cs : List Nat} {vs} {a : Nat} (h : a ∉ cs) :
    (writeCells m cs vs)[a]? = m[a]? := by
  induction cs generalizing m vs with
  | nil => rfl
  | cons c cs ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [List.mem_cons, not_or] at h
      simp only [writeCells]; rw [ih h.2, get_insert_ne (Ne.symm h.1)]

theorem readCells_writeCells_disj {m : Mem} {cs : List Nat} {vs} {b : Block} (h : Block.disj cs b) :
    readCells (writeCells m cs vs) b = readCells m b := by
  simp only [readCells, List.map_inj_left]
  intro a ha; exact writeCells_get_notMem fun hc => h a hc ha

theorem writeCells_get_mem {m : Mem} {cs : List Nat} {vs : List (BitVec 8)} (hn : cs.Nodup)
    (hl : cs.length = vs.length) {i : Nat} (hi : i < cs.length) :
    (writeCells m cs vs)[cs[i]]? = some (vs[i]'(hl ▸ hi)) := by
  induction cs generalizing m vs i with
  | nil => simp at hi
  | cons c cs ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.nodup_cons] at hn
      simp only [writeCells]
      cases i with
      | zero => simp [writeCells_get_notMem hn.1, Std.ExtHashMap.getElem?_insert]
      | succ i => simpa using ih hn.2 (by simpa using hl) (by simpa using hi)

/-- writing `vs` to all cells of `cs` makes the block read back `vs` -/
theorem readCells_writeCells {m : Mem} {cs : List Nat} {vs : List (BitVec 8)} (hn : cs.Nodup)
    (hl : cs.length = vs.length) : readCells (writeCells m cs vs) cs = vs.map some := by
  apply List.ext_getElem (by simp [readCells, hl])
  intro i h1 h2
  simp only [readCells, List.getElem_map]
  exact writeCells_get_mem hn hl (by simpa [readCells] using h1)

/-- write all cells of block `L[k]` of an ok layout: it reads back `vs`, every other block and every
address outside `L[k]` is unchanged. -/
theorem layout_writeAll {m : Mem} {L : Layout} (hL : L.ok) {k : Nat} (hk : k < L.length)
    {vs : List (BitVec 8)} (hl : L[k].length = vs.length) :
    readCells (writeCells m L[k] vs) L[k] = vs.map some ∧
    (∀ j (hj : j < L.length), j ≠ k → readCells (writeCells m L[k] vs) L[j] = readCells m L[j]) ∧
    (∀ a, a ∉ L[k] → (writeCells m L[k] vs)[a]? = m[a]?) :=
  ⟨readCells_writeCells (hL.1 _ (List.getElem_mem hk)).2 hl,
   fun j hj hjk => readCells_writeCells_disj (hL.disj hk hj (Ne.symm hjk)),
   fun _ ha => writeCells_get_notMem ha⟩

/-! ## Contiguous regions as an instance -/

def Region.cells (r : Region) : Block := List.range' r.base r.len

theorem Region.mem_cells {r : Region} {a : Nat} : a ∈ r.cells ↔ r.base ≤ a ∧ a < r.base + r.len := by
  simp [Region.cells, List.mem_range'_1]

theorem Region.nodup (r : Region) : r.cells.Nodup := List.nodup_range' ..

theorem Region.inRAM.cells {r : Region} (h : r.inRAM) : r.cells.inRAM := by
  intro a ha; rw [Region.mem_cells] at ha; unfold Region.inRAM at h; omega

theorem disjoint.cells {r₁ r₂ : Region} (h : disjoint r₁ r₂) : r₁.cells.disj r₂.cells := by
  intro a h1 h2; rw [Region.mem_cells] at h1 h2; unfold disjoint at h; omega

theorem bytesAt_eq (s : St) (a n : Nat) : bytesAt s a n = bytesOf s (Region.cells ⟨a, n⟩) := by
  simp [bytesAt, bytesOf, readCells, Region.cells, List.range'_eq_map_range]

theorem storeBytes_eq (m : Mem) (a : Nat) (vs : List (BitVec 8)) :
    storeBytes m a vs = writeCells m (Region.cells ⟨a, vs.length⟩) vs := rfl

/-- a list of disjoint in-RAM regions is an ok layout -/
theorem Layout.ok_regions {rs : List Region} (h1 : ∀ r ∈ rs, r.inRAM) (h2 : rs.Pairwise disjoint) :
    Layout.ok (rs.map Region.cells) := by
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb; exact ⟨(h1 r hr).cells, r.nodup⟩
  · rw [List.pairwise_map]; exact h2.imp disjoint.cells

/-- outside a region: the `unchangedOutside` form -/
theorem unchangedOutside_of {s s' : St} {rs : List Region}
    (h : ∀ a, (∀ r ∈ rs, a ∉ r.cells) → s'.mem[a]? = s.mem[a]?) : unchangedOutside s s' rs := by
  intro a ha; apply h; intro r hr hm; rw [Region.mem_cells] at hm; have := ha r hr; omega

/-- little-endian bytes of a 64-bit value -/
def le8 (x : BitVec 64) : List (BitVec 8) := (List.range 8).map fun i => x.extractLsb' (8 * i) 8

end Proven
