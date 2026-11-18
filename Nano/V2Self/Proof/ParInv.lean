/- Nano/V2Self/Proof/ParInv: groundwork for the parser-invariant proof (Astra 11): the entry of `y16` / `y13` and the task-machine framework.
(1) layout facts; (2) the loading phase of `v99` (zeroed regions, token copy) proved: `v99 x b = fin x b (v97 N (v1 (entryHeap x) 60 0 0))`;
(3) a decoded VIEW of the heap (cursor, task stack, operand stack, arena nodes) and `HeapRep` linking it to the cells;
(4) `ParserSound` (the final theorem statement against `ParSpec`) and `Completes`, the property the per-task invariants must establish:
   `Completes ts h` = whatever the task machine started at `h` finally ACCEPTS is `serialize p` for some `ParsesProgram ts p`.
Entry: `Completes ts (v1 (entryHeap ts) 60 0 0)` implies `ParserSound ts`.  Every task step is a deterministic `v96`; `completes_step` reduces
`Completes` at a state to `Completes` at its successor, so the remaining work is one lemma per task code relating the successor to ParSpec's grammar. -/
import Nano.V2Self.C.Par1
import Nano.V2Self.Proof.BufL
import Nano.V2Self.Proof.ParSpec
namespace ParInv
open C BufL

/-! ## layout -/
theorem d1v : d1 = 64 := rfl
theorem d3v : d3 = 12352 := rfl
theorem d5v : d5 = 16448 := rfl
theorem d7v : d7 = 147520 := rfl
theorem d9v : d9 = 180288 := rfl
theorem d11v : d11 = 184384 := rfl

/-! ## loading: y5 zero-fills, y14 copies the tokens -/
theorem y5_eq : ∀ (n : Nat) (h : Buf), y5 n h = h ++ List.replicate n 0
  | 0, h => by simp [y5]
  | n + 1, h => by
    simp only [y5, bpush]
    rw [y5_eq n (h ++ [0]), List.replicate_succ]
    simp

theorem y15_nil : y15 bnew = List.replicate 184384 0 := by
  unfold y15
  rw [y5_eq]
  rfl

theorem y14_eq (x : Buf) (hx : x.length < 2 ^ 64) :
    ∀ (n : Nat) (i : UInt64) (h : Buf), x.length - i.toNat ≤ n → i.toNat ≤ x.length → y14 n x i h = h ++ x.drop i.toNat
  | 0, i, h, h1, h2 => by
    have : x.length ≤ i.toNat := by omega
    simp [y14, List.drop_eq_nil_of_le this]
  | n + 1, i, h, h1, h2 => by
    by_cases hi : i.toNat < x.length
    · have hlt : i < bsize x := by
        rw [UInt64.lt_iff_toNat_lt]; simp [bsize, UInt64.toNat_ofNat']; omega
      have hs : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      simp only [y14, hlt, if_true]
      rw [y14_eq x hx n (i + 1) (bpush h (bget x i)) (by omega) (by omega)]
      simp only [bpush, bget, hs, List.append_assoc]
      congr 1
      rw [List.drop_eq_getElem_cons hi]; simp [List.getD, hi]
    · have hlt : ¬ i < bsize x := by
        rw [UInt64.lt_iff_toNat_lt]; simp [bsize, UInt64.toNat_ofNat']; omega
      simp only [y14, hlt, if_false]
      simp [List.drop_eq_nil_of_le (show x.length ≤ i.toNat by omega)]

/-- the heap right after loading: 184,384 zero cells (the layout), the tokens, h[7] = their number, h[0] = 1, then the sentinel 0 and the IRV word 2 -/
def entryHeap (x : Buf) : Buf :=
  bpush (bpush (bset (bset (List.replicate 184384 0 ++ x) 7 (bsize x)) 0 1) 0) 2

/-- the tail of `v99`: the acceptance checks and the output extraction, as a function of the final heap -/
def fin (x : Buf) (b : UInt64) (h : Buf) : Buf :=
  let c := bsize x
  if (bget h 0) == 2 then
    if 0 < (bget h 12) then
      if b == 0 then v98 16777216 h (d11 + c + 1) bnew else
        let j := d7 + 8*((bget h 12)-1);
        let x := bget h j;
        let u := bget h (j+5);
        if bget h (d11+x+2) == 109 then
          if bget h (d11+x+3) == 0 then
            if bget h (j+2) == 0 then
              if bget h (d7+4096+u) == 3 then
                if bget h (j+3) == 3 then v98 16777216 h (d11+c+1) bnew else bnew
              else bnew
            else bnew
          else bnew
        else bnew
    else bnew
  else bnew

theorem v99_eq (x : Buf) (b : UInt64) (hx : x.length ≤ 16777216) :
    v99 x b = fin x b (v97 16777216 (v1 (entryHeap x) 60 0 0)) := by
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have hy : y14 16777216 x 0 (y15 bnew) = List.replicate 184384 0 ++ x := by
    rw [y14_eq x (by omega) 16777216 0 _ (by rw [h0]; omega) (by rw [h0]; omega), y15_nil, h0, List.drop_zero]
  have hsz : bsize (List.replicate 184384 0 ++ x) = d11 + bsize x := by
    apply UInt64.toNat_inj.mp
    have e : (184384 : UInt64).toNat = 184384 := rfl
    rw [d11v]
    simp only [bsize, List.length_append, List.length_replicate, UInt64.toNat_add, UInt64.toNat_ofNat', e]
    omega
  unfold v99
  simp only [hy, hsz, beq_self_eq_true, if_true, fin, entryHeap]

/-! ## decoded view of the machine state -/
structure Task where
  code : UInt64
  a : UInt64
  b : UInt64

structure Node where
  tag : UInt64
  p1 : UInt64
  p2 : UInt64
  shape : UInt64
  pend : UInt64
  first : UInt64
  count : UInt64
  next : UInt64

/-- the cells the parser machine reads and writes, decoded -/
structure View where
  status : UInt64          -- h[0]: 1 running, 2 done, 0 failed
  cur : UInt64             -- h[3] token cursor
  depth : UInt64           -- h[4] binding depth
  ntasks : UInt64          -- h[5]
  ntok : UInt64            -- h[7]
  nops : UInt64            -- h[8]
  nnodes : UInt64          -- h[9]
  slot : UInt64            -- h[11] next free slot
  ndefs : UInt64           -- h[12]
  tasks : List Task        -- the stack, bottom first
  ops : List UInt64        -- operand node ids, bottom first
  nodes : List Node        -- the arena

def taskAt (h : Buf) (i : Nat) : Task :=
  ⟨bget h (d1 + 3 * i.toUInt64), bget h (d1 + 3 * i.toUInt64 + 1), bget h (d1 + 3 * i.toUInt64 + 2)⟩

def nodeAt (h : Buf) (i : Nat) : Node :=
  let q := d5 + 8 * i.toUInt64
  ⟨bget h q, bget h (q + 1), bget h (q + 2), bget h (q + 3), bget h (q + 4), bget h (q + 5), bget h (q + 6), bget h (q + 7)⟩

def view (h : Buf) : View where
  status := bget h 0
  cur := bget h 3
  depth := bget h 4
  ntasks := bget h 5
  ntok := bget h 7
  nops := bget h 8
  nnodes := bget h 9
  slot := bget h 11
  ndefs := bget h 12
  tasks := (List.range (bget h 5).toNat).map (taskAt h)
  ops := (List.range (bget h 8).toNat).map fun i => bget h (d3 + i.toUInt64)
  nodes := (List.range (bget h 9).toNat).map (nodeAt h)

/-- the machine state `h` represents the view `v` (the view is a function of the cells; invariants are stated on views) -/
def HeapRep (h : Buf) (v : View) : Prop := view h = v

/-- the token region of the heap holds `ts` (followed by the sentinel 0, 2) -/
def TokensAt (h : Buf) (ts : Buf) : Prop :=
  (∀ i, i < ts.length → bget h (d11 + i.toUInt64) = ts.getD i 0) ∧ bget h (d11 + ts.length.toUInt64) = 0 ∧
    bget h (d11 + ts.length.toUInt64 + 1) = 2 ∧ bget h 7 = ts.length.toUInt64

/-! ## the final statement and the run -/
/-- what the parser finally promises -/
def ParserSound (ts : Buf) : Prop :=
  y16 ts ≠ [] → ∃ p, ParSpec.ParsesProgram ts p ∧ y16 ts = ParSpec.serialize p

/-- from machine state `h`, everything the task machine finally ACCEPTS (non-empty output of `fin`) is the serialization of a parse of `ts` -/
def Completes (ts : Buf) (h : Buf) : Prop :=
  ∀ N, fin ts 1 (v97 N h) ≠ [] → ∃ p, ParSpec.ParsesProgram ts p ∧ fin ts 1 (v97 N h) = ParSpec.serialize p

/-- **Entry**: it suffices that the initial task completes -/
theorem entry (ts : Buf) (hx : ts.length ≤ 16777216)
    (h : Completes ts (v1 (entryHeap ts) 60 0 0)) : ParserSound ts := by
  intro hne
  have e : y16 ts = fin ts 1 (v97 16777216 (v1 (entryHeap ts) 60 0 0)) := v99_eq ts 1 hx
  rw [e] at hne ⊢
  exact h 16777216 hne

/-- the machine's one step (the body of `v97`): pop the top task and run its handler -/
def step (h : Buf) : Buf :=
  let g := bget h 5
  let j := d1 + 3 * (g - 1)
  v96 (bset h 5 (g - 1)) (bget h j) (bget h (j + 1)) (bget h (j + 2))

theorem v97_running (n : Nat) (h : Buf) (hs : bget h 0 = 1) (hg : bget h 5 ≠ 0) : v97 (n + 1) h = v97 n (step h) := by
  simp only [v97, hs, beq_self_eq_true, if_true]
  have : (bget h 5 == 0) = false := by simpa using hg
  simp [this, step]

theorem v97_stopped (n : Nat) (h : Buf) (hs : bget h 0 ≠ 1) : v97 (n + 1) h = h := by
  have : (bget h 0 == 1) = false := by simpa using hs
  simp [v97, this]

/-- one machine step preserves `Completes` backwards: if the successor completes, so does the running state -/
theorem completes_step (ts h : Buf) (hs : bget h 0 = 1) (hg : bget h 5 ≠ 0) (hc : Completes ts (step h)) : Completes ts h := by
  intro N hN
  cases N with
  | zero =>
    exfalso; apply hN
    have h0 : bget (v97 0 h) 0 = 0 := by
      simp only [v97]; rw [bget_bset]; by_cases hl : 0 < h.length <;> simp [hl, bget, List.getD]
    simp [fin, h0, bnew]
  | succ n =>
    rw [v97_running n h hs hg] at hN ⊢
    exact hc n hN

end ParInv
