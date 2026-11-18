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

/-! ## names: `v85` compares two zero-terminated identifier spellings in the token region -/
/-- the identifier spelling `(1, b)* 0` (without the leading tag 14) starts at token position `a` and spells `n` -/
def NameSeq (h : Buf) : UInt64 → List UInt64 → Prop
  | a, [] => bget h (d11 + a) = 0
  | a, c :: t => bget h (d11 + a) = 1 ∧ bget h (d11 + a + 1) = c ∧ NameSeq h (a + 2) t

theorem add2_toNat (a z : UInt64) (h : a.toNat < z.toNat) : (a + 2).toNat = a.toNat + 2 ∨ z.toNat ≤ a.toNat + 2 := by
  have := z.toNat_lt
  by_cases hh : a.toNat + 2 < 2 ^ 64
  · left; rw [UInt64.toNat_add]; simp; omega
  · right; omega

/-- `v85` decides name equality (and stays within the token region when both names are, with their terminator, below h[7]) -/
theorem v85_name : ∀ (l1 l2 : List UInt64) (n : Nat) (h : Buf) (a b : UInt64),
    l1.length + 1 ≤ n → NameSeq h a l1 → NameSeq h b l2 →
    a.toNat + 2 * l1.length < (bget h 7).toNat → b.toNat + 2 * l2.length < (bget h 7).toNat →
    v85 n h a b = bset h 31 (if l1 = l2 then 1 else 0)
  | [], l2, n + 1, h, a, b, hn, ha, hb, ba, bb => by
    have hz : a < bget h 7 := by rw [UInt64.lt_iff_toNat_lt]; omega
    cases l2 with
    | nil =>
      have hz2 : b < bget h 7 := by rw [UInt64.lt_iff_toNat_lt]; simp at bb; omega
      simp only [NameSeq] at ha hb
      simp [v85, hz, hz2, ha, hb]
    | cons d u =>
      have hz2 : b < bget h 7 := by rw [UInt64.lt_iff_toNat_lt]; simp at bb; omega
      simp only [NameSeq] at ha hb
      obtain ⟨hb1, _, _⟩ := hb
      simp [v85, hz, hz2, ha, hb1]
  | c :: t, l2, n + 1, h, a, b, hn, ha, hb, ba, bb => by
    have hz : a < bget h 7 := by rw [UInt64.lt_iff_toNat_lt]; simp at ba; omega
    have hz2 : b < bget h 7 := by rw [UInt64.lt_iff_toNat_lt]; cases l2 <;> simp at bb <;> omega
    simp only [NameSeq] at ha
    obtain ⟨ha1, ha2, ha3⟩ := ha
    cases l2 with
    | nil =>
      simp only [NameSeq] at hb
      simp [v85, hz, hz2, ha1, hb]
    | cons d u =>
      simp only [NameSeq] at hb
      obtain ⟨hb1, hb2, hb3⟩ := hb
      by_cases hcd : c = d
      · subst hcd
        have a2 := add2_toNat a (bget h 7) (by simp at ba; omega)
        have b2 := add2_toNat b (bget h 7) (by simp at bb; omega)
        have a2' : (a + 2).toNat = a.toNat + 2 := by simp at ba; omega
        have b2' : (b + 2).toNat = b.toNat + 2 := by simp at bb; omega
        have ih := v85_name t u n h (a + 2) (b + 2) (by simp at hn; omega) ha3 hb3 (by rw [a2']; simp at ba; omega) (by rw [b2']; simp at bb; omega)
        have hne : (1 : UInt64) ≠ 0 := by decide
        simp [v85, hz, hz2, ha1, hb1, ha2, hb2, hne, ih]
      · have : (c :: t ≠ d :: u) := fun e => hcd (List.cons.inj e).1
        simp [v85, hz, hz2, ha1, hb1, ha2, hb2, hcd, this]
  | _, _, 0, h, a, b, hn, _, _, _, _ => by simp at hn

/-! ## the binding table: `v7` finds the innermost binding with the same spelling -/
/-- the spelling of the identifier token at position `pos` (tag 14 then `(1,b)* 0`), below h[7] -/
def NameOK (h : Buf) (pos : UInt64) (n : List UInt64) : Prop :=
  bget h (d11 + pos) = 14 ∧ NameSeq h (pos + 1) n ∧ pos.toNat + 1 + 2 * n.length < (bget h 7).toNat

/-- `h'` differs from `h` at most in the result cell h[r] and the scratch cell h[31] (r = 21 for v7, 22 for v8) -/
def Same (r : Nat) (h h' : Buf) : Prop := h'.length = h.length ∧ ∀ i : UInt64, i.toNat ≠ r → i.toNat ≠ 31 → bget h' i = bget h i

theorem Same.refl (r : Nat) (h : Buf) : Same r h h := ⟨rfl, fun _ _ _ => rfl⟩
theorem Same.trans {r : Nat} {h h' h'' : Buf} (a : Same r h h') (b : Same r h' h'') : Same r h h'' :=
  ⟨b.1.trans a.1, fun i i1 i2 => (b.2 i i1 i2).trans (a.2 i i1 i2)⟩
theorem same_bset (r : Nat) (h : Buf) (i v : UInt64) (hi : i.toNat = r ∨ i.toNat = 31) : Same r h (bset h i v) :=
  ⟨by simp [bset], fun j j1 j2 => by rw [bget_bset_other _ _ _ _ (by omega)]⟩

theorem d11a (a : UInt64) (ha : a.toNat < 2 ^ 40) : (d11 + a).toNat = 184384 + a.toNat := by
  rw [UInt64.toNat_add, d11v]; simp; omega

theorem d11a1 (a : UInt64) (ha : a.toNat < 2 ^ 40) : (d11 + a + 1).toNat = 184384 + a.toNat + 1 := by
  rw [UInt64.toNat_add, d11a a ha]; simp; omega

theorem nameSeq_same {r : Nat} {h h' : Buf} (s : Same r h h') (hr : r < 184384) :
    ∀ (l : List UInt64) (a : UInt64), a.toNat + 2 * l.length + 1 < 2 ^ 40 → NameSeq h a l → NameSeq h' a l
  | [], a, ha, e => by
    simp only [NameSeq] at e ⊢
    rw [s.2 _ (by rw [d11a a (by omega)]; omega) (by rw [d11a a (by omega)]; omega)]; exact e
  | c :: t, a, ha, e => by
    simp only [NameSeq] at e ⊢
    obtain ⟨e1, e2, e3⟩ := e
    have a2 : (a + 2).toNat = a.toNat + 2 := by rw [UInt64.toNat_add]; simp; simp at ha; omega
    refine ⟨?_, ?_, nameSeq_same s hr t (a + 2) (by rw [a2]; simp at ha; omega) e3⟩
    · rw [s.2 _ (by rw [d11a a (by omega)]; omega) (by rw [d11a a (by omega)]; omega)]; exact e1
    · rw [s.2 _ (by rw [d11a1 a (by omega)]; omega) (by rw [d11a1 a (by omega)]; omega)]; exact e2

theorem nameOK_same {r : Nat} {h h' : Buf} (s : Same r h h') (hr : 7 < r ∧ r < 184384) (hn : (bget h 7).toNat < 2 ^ 40) {pos : UInt64} {n : List UInt64}
    (e : NameOK h pos n) : NameOK h' pos n := by
  obtain ⟨e1, e2, e3⟩ := e
  have p1 : (pos + 1).toNat = pos.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have h7 : bget h' 7 = bget h 7 := s.2 7 (by show 7 ≠ r; omega) (by decide)
  refine ⟨?_, nameSeq_same s hr.2 n (pos + 1) (by rw [p1]; omega) e2, by rw [h7]; exact e3⟩
  rw [s.2 _ (by rw [d11a pos (by omega)]; omega) (by rw [d11a pos (by omega)]; omega)]; exact e1

/-- the binding table (entries `d9 + 4 i`: name token position, …) holds the names `tab` (bottom first) -/
def TabRep (h : Buf) (tab : List (UInt64 × List UInt64)) : Prop :=
  ∀ (i : Nat) (hi : i < tab.length), bget h (d9 + 4 * i.toUInt64) = (tab[i]).1 ∧ NameOK h (tab[i]).1 (tab[i]).2 ∧ (tab[i]).2.length < 2 ^ 24

theorem tabRep_same {r : Nat} {h h' : Buf} (s : Same r h h') (hr : 7 < r ∧ r < 180288) (hn : (bget h 7).toNat < 2 ^ 40) {tab : List (UInt64 × List UInt64)}
    (hlen : tab.length < 2 ^ 20) (e : TabRep h tab) : TabRep h' tab := by
  intro i hi
  obtain ⟨e1, e2, e3⟩ := e i hi
  have hi' : i < 2 ^ 20 := by omega
  have q : (d9 + 4 * i.toUInt64).toNat = 180288 + 4 * i := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, d9v]; simp [UInt64.toNat_ofNat']; omega
  refine ⟨?_, nameOK_same s ⟨hr.1, by omega⟩ hn e2, e3⟩
  rw [s.2 _ (by rw [q]; omega) (by rw [q]; omega)]; exact e1

/-- the innermost match (1-based) among the first `j` entries, 0 if none -/
def idxOf (tab : List (UInt64 × List UInt64)) (x : List UInt64) : Nat → Nat
  | 0 => 0
  | j + 1 => if (tab.getD j (0, [])).2 = x then j + 1 else idxOf tab x j

/-- **v7 = innermost-binding lookup**: scanning the first `j` bindings for the spelling of the token at `x`, the result cell h[21] holds `idxOf`,
and only the scratch cells h[21], h[31] change -/
theorem v7_lookup (tab : List (UInt64 × List UInt64)) (x : UInt64) (nx : List UInt64) :
    ∀ (jn n : Nat) (h : Buf) (j : UInt64), j.toNat = jn → jn ≤ tab.length → tab.length < 2 ^ 20 → jn + 1 ≤ n →
      31 < h.length → (bget h 7).toNat < 2 ^ 40 → TabRep h tab → NameOK h x nx → nx.length < 2 ^ 24 →
      Same 21 h (v7 n h j x) ∧ bget (v7 n h j x) 21 = (idxOf tab nx jn).toUInt64
  | 0, n + 1, h, j, hj, _, _, _, h31, _, _, _, _ => by
    have : j = 0 := UInt64.toNat_inj.mp (by simpa using hj)
    subst this
    simp only [v7, beq_self_eq_true, if_true, idxOf]
    refine ⟨same_bset 21 h 21 0 (Or.inl rfl), ?_⟩
    rw [bget_bset_same _ _ _ (by simpa using (by omega : 21 < h.length))]; rfl
  | m + 1, n + 1, h, j, hj, hjt, hl, hn, h31, h7, tr, nm, nl => by
    have hj0 : (j == 0) = false := by
      have : j ≠ 0 := fun e => by subst e; simp at hj
      simpa using this
    have hjm : j - 1 = m.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp [hj])]; simp [hj, UInt64.toNat_ofNat']; omega
    obtain ⟨t1, t2, t3⟩ := tr m (by omega)
    have hcell : bget h (d9 + 4 * (j - 1)) = (tab[m]'(by omega)).1 := by rw [hjm]; exact t1
    obtain ⟨n1, n2, n3⟩ := nm
    obtain ⟨u1, u2, u3⟩ := t2
    have p1 : (x + 1).toNat = x.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have q1 : ((tab[m]'(by omega)).1 + 1).toNat = (tab[m]'(by omega)).1.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have eq85 := v85_name (tab[m]'(by omega)).2 nx 16777216 h ((tab[m]'(by omega)).1 + 1) (x + 1) (by omega) u2 n2
      (by rw [q1]; omega) (by rw [p1]; omega)
    have getD : tab.getD m (0, []) = tab[m]'(by omega) := by simp [List.getD, show m < tab.length by omega]
    have l31 : (31 : UInt64).toNat < h.length := h31
    have l21 : (21 : UInt64).toNat < h.length := by show 21 < h.length; omega
    by_cases hq : (tab[m]'(by omega)).2 = nx
    · have eq85' : v85 16777216 h ((tab[m]'(by omega)).1 + 1) (x + 1) = bset h 31 1 := by rw [eq85, if_pos hq]
      have e31 : bget (bset h 31 1) 31 = 1 := bget_bset_same h 31 1 l31
      have stp : v7 (n + 1) h j x = bset (bset h 31 1) 21 j := by
        simp only [v7, hj0, Bool.false_eq_true, if_false, hcell, eq85', e31, beq_self_eq_true, if_true]
      rw [stp]
      have s1 := same_bset 21 h 31 1 (Or.inr rfl)
      have s2 := same_bset 21 (bset h 31 1) 21 j (Or.inl rfl)
      refine ⟨s1.trans s2, ?_⟩
      have l21' : (21 : UInt64).toNat < (bset h 31 1).length := by simpa [bset] using l21
      rw [bget_bset_same _ _ _ l21']
      simp only [idxOf, getD, hq, if_true]
      apply UInt64.toNat_inj.mp; simp [UInt64.toNat_ofNat', hj]; omega
    · have eq85' : v85 16777216 h ((tab[m]'(by omega)).1 + 1) (x + 1) = bset h 31 0 := by rw [eq85, if_neg hq]
      have e31 : bget (bset h 31 0) 31 = 0 := bget_bset_same h 31 0 l31
      have stp : v7 (n + 1) h j x = v7 n (bset h 31 0) (j - 1) x := by
        simp only [v7, hj0, Bool.false_eq_true, if_false, hcell, eq85', e31]
        have : ((0 : UInt64) == 1) = false := by decide
        simp [this]
      rw [stp]
      have s1 := same_bset 21 h 31 0 (Or.inr rfl)
      have ih := v7_lookup tab x nx m n (bset h 31 0) (j - 1) (by rw [hjm]; simp [UInt64.toNat_ofNat']; omega) (by omega) hl (by omega)
        (by simpa [bset] using h31) (by rw [(s1.2 7 (by decide) (by decide))]; exact h7)
        (tabRep_same s1 ⟨by omega, by omega⟩ h7 hl tr) (nameOK_same s1 ⟨by omega, by omega⟩ h7 ⟨n1, n2, n3⟩) nl
      refine ⟨s1.trans ih.1, ?_⟩
      rw [ih.2]; simp only [idxOf, getD, hq, if_false]


/-- the def table (entries `d7 + 8 i`: name token position, …) holds the names `tab` (bottom first) -/
def DefTabRep (h : Buf) (tab : List (UInt64 × List UInt64)) : Prop :=
  ∀ (i : Nat) (hi : i < tab.length), bget h (d7 + 8 * i.toUInt64) = (tab[i]).1 ∧ NameOK h (tab[i]).1 (tab[i]).2 ∧ (tab[i]).2.length < 2 ^ 24

theorem defTabRep_same {r : Nat} {h h' : Buf} (s : Same r h h') (hr : 7 < r ∧ r < 147520) (hn : (bget h 7).toNat < 2 ^ 40) {tab : List (UInt64 × List UInt64)}
    (hlen : tab.length < 2 ^ 20) (e : DefTabRep h tab) : DefTabRep h' tab := by
  intro i hi
  obtain ⟨e1, e2, e3⟩ := e i hi
  have hi' : i < 2 ^ 20 := by omega
  have q : (d7 + 8 * i.toUInt64).toNat = 147520 + 8 * i := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, d7v]; simp [UInt64.toNat_ofNat']; omega
  refine ⟨?_, nameOK_same s ⟨hr.1, by omega⟩ hn e2, e3⟩
  rw [s.2 _ (by rw [q]; omega) (by rw [q]; omega)]; exact e1

/-- **v8 = innermost-def lookup**: scanning the first `j` bindings for the spelling of the token at `x`, the result cell h[22] holds `idxOf`,
and only the scratch cells h[22], h[31] change -/
theorem v8_lookup (tab : List (UInt64 × List UInt64)) (x : UInt64) (nx : List UInt64) :
    ∀ (jn n : Nat) (h : Buf) (j : UInt64), j.toNat = jn → jn ≤ tab.length → tab.length < 2 ^ 20 → jn + 1 ≤ n →
      31 < h.length → (bget h 7).toNat < 2 ^ 40 → DefTabRep h tab → NameOK h x nx → nx.length < 2 ^ 24 →
      Same 22 h (v8 n h j x) ∧ bget (v8 n h j x) 22 = (idxOf tab nx jn).toUInt64
  | 0, n + 1, h, j, hj, _, _, _, h31, _, _, _, _ => by
    have : j = 0 := UInt64.toNat_inj.mp (by simpa using hj)
    subst this
    simp only [v8, beq_self_eq_true, if_true, idxOf]
    refine ⟨same_bset 22 h 22 0 (Or.inl rfl), ?_⟩
    rw [bget_bset_same _ _ _ (by simpa using (by omega : 22 < h.length))]; rfl
  | m + 1, n + 1, h, j, hj, hjt, hl, hn, h31, h7, tr, nm, nl => by
    have hj0 : (j == 0) = false := by
      have : j ≠ 0 := fun e => by subst e; simp at hj
      simpa using this
    have hjm : j - 1 = m.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp [hj])]; simp [hj, UInt64.toNat_ofNat']; omega
    obtain ⟨t1, t2, t3⟩ := tr m (by omega)
    have hcell : bget h (d7 + 8 * (j - 1)) = (tab[m]'(by omega)).1 := by rw [hjm]; exact t1
    obtain ⟨n1, n2, n3⟩ := nm
    obtain ⟨u1, u2, u3⟩ := t2
    have p1 : (x + 1).toNat = x.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have q1 : ((tab[m]'(by omega)).1 + 1).toNat = (tab[m]'(by omega)).1.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have eq85 := v85_name (tab[m]'(by omega)).2 nx 16777216 h ((tab[m]'(by omega)).1 + 1) (x + 1) (by omega) u2 n2
      (by rw [q1]; omega) (by rw [p1]; omega)
    have getD : tab.getD m (0, []) = tab[m]'(by omega) := by simp [List.getD, show m < tab.length by omega]
    have l31 : (31 : UInt64).toNat < h.length := h31
    have l21 : (22 : UInt64).toNat < h.length := by show 22 < h.length; omega
    by_cases hq : (tab[m]'(by omega)).2 = nx
    · have eq85' : v85 16777216 h ((tab[m]'(by omega)).1 + 1) (x + 1) = bset h 31 1 := by rw [eq85, if_pos hq]
      have e31 : bget (bset h 31 1) 31 = 1 := bget_bset_same h 31 1 l31
      have stp : v8 (n + 1) h j x = bset (bset h 31 1) 22 j := by
        simp only [v8, hj0, Bool.false_eq_true, if_false, hcell, eq85', e31, beq_self_eq_true, if_true]
      rw [stp]
      have s1 := same_bset 22 h 31 1 (Or.inr rfl)
      have s2 := same_bset 22 (bset h 31 1) 22 j (Or.inl rfl)
      refine ⟨s1.trans s2, ?_⟩
      have l21' : (22 : UInt64).toNat < (bset h 31 1).length := by simpa [bset] using l21
      rw [bget_bset_same _ _ _ l21']
      simp only [idxOf, getD, hq, if_true]
      apply UInt64.toNat_inj.mp; simp [UInt64.toNat_ofNat', hj]; omega
    · have eq85' : v85 16777216 h ((tab[m]'(by omega)).1 + 1) (x + 1) = bset h 31 0 := by rw [eq85, if_neg hq]
      have e31 : bget (bset h 31 0) 31 = 0 := bget_bset_same h 31 0 l31
      have stp : v8 (n + 1) h j x = v8 n (bset h 31 0) (j - 1) x := by
        simp only [v8, hj0, Bool.false_eq_true, if_false, hcell, eq85', e31]
        have : ((0 : UInt64) == 1) = false := by decide
        simp [this]
      rw [stp]
      have s1 := same_bset 22 h 31 0 (Or.inr rfl)
      have ih := v8_lookup tab x nx m n (bset h 31 0) (j - 1) (by rw [hjm]; simp [UInt64.toNat_ofNat']; omega) (by omega) hl (by omega)
        (by simpa [bset] using h31) (by rw [(s1.2 7 (by decide) (by decide))]; exact h7)
        (defTabRep_same s1 ⟨by omega, by omega⟩ h7 hl tr) (nameOK_same s1 ⟨by omega, by omega⟩ h7 ⟨n1, n2, n3⟩) nl
      refine ⟨s1.trans ih.1, ?_⟩
      rw [ih.2]; simp only [idxOf, getD, hq, if_false]

end ParInv
