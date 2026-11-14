/- Middle layer, `BStmt` (byte arrays, word arrays, spill slots) to extended abstract operations, and its
correctness from the `MachineF` laws only (`execB_ok`, `compBF_ok`).

Variables `0 .. 7` live in `avar i`, variables `8 + j` in frame slot `j`; byte block `b` is region `R[b]`
(base in variable `bv[b]`), word block `b` is region `W[b]` (base in variable `wv[b]`, 8-aligned, word `i`
at `W[b].base + 8 i`); the frame is `F = ⟨fp, 8 (N + 1)⟩` (cell 0: the saved frame register). -/
import Compiler.BExp
import Compiler.Arr

namespace Proven.Mach

/-! ## Bytes of word blocks -/

/-- the bytes of a word block -/
def wbytes : List (BitVec 64) → List (BitVec 8)
  | [] => []
  | w :: ws => le8 w ++ wbytes ws

theorem length_wbytes : ∀ ws : List (BitVec 64), (wbytes ws).length = 8 * ws.length
  | [] => rfl
  | w :: ws => by
    show (le8 w ++ wbytes ws).length = _
    rw [List.length_append, length_le8, length_wbytes ws, List.length_cons]; omega

theorem getElem?_wbytes : ∀ (ws : List (BitVec 64)) (i j : Nat), j < 8 →
    (wbytes ws)[8 * i + j]? = (ws[i]?).bind fun w => (le8 w)[j]?
  | [], i, j, _ => rfl
  | w :: ws, 0, j, hj => by
    show (le8 w ++ wbytes ws)[8 * 0 + j]? = _
    rw [List.getElem?_append_left (by rw [length_le8]; omega), Nat.mul_zero, Nat.zero_add]; rfl
  | w :: ws, i + 1, j, hj => by
    show (le8 w ++ wbytes ws)[8 * (i + 1) + j]? = _
    rw [List.getElem?_append_right (by rw [length_le8]; omega), length_le8,
      show 8 * (i + 1) + j - 8 = 8 * i + j by omega, getElem?_wbytes ws i j hj]; rfl

theorem mem_of_bytes {m : Mem} {a n : Nat} {l : List (BitVec 8)} (h : bytes m a n = l.map some) {j : Nat}
    (hj : j < n) : m (a + j) = l[j]? := by
  have hl : l.length = n := by have := congrArg List.length h; rw [length_bytes, List.length_map] at this; omega
  rw [get_of_bytes h (by omega), List.getElem?_eq_getElem (by omega)]

theorem bytes_of_mem {m : Mem} {a n : Nat} {l : List (BitVec 8)} (hl : l.length = n)
    (h : ∀ j, j < n → m (a + j) = l[j]?) : bytes m a n = l.map some := by
  apply List.ext_getElem (by rw [length_bytes, List.length_map, hl])
  intro j h1 h2
  rw [List.getElem_map, bytes_getElem]
  rw [length_bytes] at h1
  rw [h j h1, List.getElem?_eq_getElem (by omega)]

theorem le8_get {w : BitVec 64} {j : Nat} (hj : j < 8) : ∃ b, (le8 w)[j]? = some b :=
  ⟨_, List.getElem?_eq_getElem (by rw [length_le8]; exact hj)⟩

/-- the 8 bytes of word `i` -/
theorem bytes_word {m : Mem} {a : Nat} {ws : List (BitVec 64)} (h : bytes m a (8 * ws.length) = (wbytes ws).map some)
    {i : Nat} (hi : i < ws.length) : bytes m (a + 8 * i) 8 = (le8 ws[i]).map some := by
  refine bytes_of_mem (length_le8 _) fun j hj => ?_
  rw [Nat.add_assoc, mem_of_bytes h (by omega), getElem?_wbytes ws i j hj, List.getElem?_eq_getElem hi]; rfl

/-- writing word `i` -/
theorem bytes_word_set {m : Mem} {a : Nat} {ws : List (BitVec 64)} (h : bytes m a (8 * ws.length) = (wbytes ws).map some)
    {i : Nat} (hi : i < ws.length) (v : BitVec 64) :
    bytes (m.wr (a + 8 * i) (le8 v)) a (8 * ws.length) = (wbytes (ws.set i v)).map some := by
  refine bytes_of_mem (by rw [length_wbytes, List.length_set]) fun J hJ => ?_
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ J = 8 * q + r := ⟨J / 8, J % 8, by omega, by omega⟩
  rw [getElem?_wbytes _ q r hr]
  by_cases hq : q = i
  · subst hq
    rw [List.getElem?_set_self hi, show a + (8 * q + r) = a + 8 * q + r by omega,
      Mem.wr_in (by rw [length_le8]; exact hr), ← List.getElem?_eq_getElem]; rfl
  · rw [Mem.wr_out (by rw [length_le8]; omega), mem_of_bytes h hJ, getElem?_wbytes _ q r hr,
      List.getElem?_set_ne (Ne.symm hq)]

theorem Out.wr {R : List Region} {m : Mem} {a : Nat} {l : List (BitVec 8)} {r : Region} (hr : r ∈ R)
    (h1 : r.base ≤ a) (h2 : a + l.length ≤ r.base + r.len) : Out R m (m.wr a l) :=
  fun x hx => Mem.wr_out (by have := hx r hr; omega)

/-! ## The compiler -/

/-- `v := r0` -/
def setV (v : Nat) : List XOp := if h : v < 8 then [.a (.mov (avar ⟨v, h⟩) (rk 0))] else [.f (.stS (v - 8) (rk 0))]

/-- address of byte `i` of byte block `b` -/
def addrB (bv : List Nat) (b : Nat) (i : BExp) : BExp := .bin .add (.var (bv.getD b 0)) i
/-- address of word `i` of word block `b` -/
def addrW (wv : List Nat) (b : Nat) (i : BExp) : BExp := .bin .add (.var (wv.getD b 0)) (.bin .shl i (.const 3))

/-- the frame slots `0 .. N-1` -/
def slots (N fp : Nat) : List Region := (List.range N).map fun j => ⟨fp + 8 * (j + 1), 8⟩

theorem mem_slots {N fp : Nat} {r : Region} (h : r ∈ slots N fp) : ∃ j, j < N ∧ r = ⟨fp + 8 * (j + 1), 8⟩ := by
  unfold slots at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  exact ⟨j, List.mem_range.1 hj, rfl⟩

theorem slot_mem_slots {N fp j : Nat} (hj : j < N) : (⟨fp + 8 * (j + 1), 8⟩ : Region) ∈ slots N fp :=
  List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

namespace MachineF
variable (M : MachineF)

def compB (bv wv : List Nat) : BStmt → List XOp
  | .assign v e => mgenB e 0 ++ setV v
  | .load v b i => mgenB (addrB bv b i) 0 ++ [.a (.lbu (rk 0) (rk 0))] ++ setV v
  | .store b i e => mgenB (addrB bv b i) 0 ++ mgenB e 1 ++ [.a (.sb (rk 1) (rk 0))]
  | .seq p q => compB bv wv p ++ compB bv wv q
  | .loop c body => mgenB c 0 ++ [.a (.bz (rk 0) ((M.codeF (compB bv wv body)).length + M.lenBz + M.lenJmp))] ++
      compB bv wv body ++ [.a (.jmp ((M.codeF (mgenB c 0)).length + M.lenBz + (M.codeF (compB bv wv body)).length))]
  | .load64 v b i => mgenB (addrW wv b i) 0 ++ [.f (.ld (rk 0) (rk 0))] ++ setV v
  | .store64 b i e => mgenB (addrW wv b i) 0 ++ mgenB e 1 ++ [.f (.sd (rk 1) (rk 0))]

/-- the function: open a frame of `N` slots, run, close the frame, return -/
def compBF (N : Nat) (bv wv : List Nat) (p : BStmt) : List XOp :=
  [.f (.enter N)] ++ M.compB bv wv p ++ [.f .leave, .a .ret]

/-- expressions fit 7 temporaries and use variables `< 8 + N`, base variables never assigned, blocks
exist, loop distances in range -/
def wfB (N : Nat) (bv wv : List Nat) : BStmt → Prop
  | .assign v e => e.depth < 7 ∧ e.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv ∧ v ∉ wv
  | .load v b i => i.depth < 6 ∧ i.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv ∧ v ∉ wv ∧ b < bv.length
  | .store b i e => i.depth < 6 ∧ e.depth < 6 ∧ i.vlt (8 + N) ∧ e.vlt (8 + N) ∧ b < bv.length
  | .seq p q => wfB N bv wv p ∧ wfB N bv wv q
  | .loop c body => c.depth < 7 ∧ c.vlt (8 + N) ∧ wfB N bv wv body ∧
      M.bzOK ((M.codeF (M.compB bv wv body)).length + M.lenBz + M.lenJmp) ∧
      M.jmpOK ((M.codeF (mgenB c 0)).length + M.lenBz + (M.codeF (M.compB bv wv body)).length)
  | .load64 v b i => i.depth < 6 ∧ i.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv ∧ v ∉ wv ∧ b < wv.length
  | .store64 b i e => i.depth < 6 ∧ e.depth < 6 ∧ i.vlt (8 + N) ∧ e.vlt (8 + N) ∧ b < wv.length

/-- the layout: regions in RAM, pairwise disjoint, disjoint from the frame; word blocks 8-aligned -/
structure Lay (N fp : Nat) (R W : List Region) : Prop where
  ram : ∀ r ∈ R, M.inRAM r.base r.len
  wram : ∀ r ∈ W, M.inRAM r.base r.len
  rp : R.Pairwise disjoint
  wp : W.Pairwise disjoint
  rw : ∀ r ∈ R, ∀ w ∈ W, disjoint r w
  fr : ∀ r ∈ R, disjoint ⟨fp, 8 * (N + 1)⟩ r
  fw : ∀ w ∈ W, disjoint ⟨fp, 8 * (N + 1)⟩ w
  wal : ∀ w ∈ W, w.base % 8 = 0
  /-- byte blocks may be stored to (`sb`; `Base.writable`) -/
  wr : ∀ r ∈ R, ∀ a, r.base ≤ a → a < r.base + r.len → ∀ s, M.ok s → M.writable s a

/-- the machine state represents `σ` -/
structure RelB (N fp : Nat) (bv wv : List Nat) (R W : List Region) (σ : BState) (s : M.S) : Prop where
  env : M.EnvB N fp σ.env s
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  rbytes : ∀ b (hb : b < R.length), bytes (M.mem s) R[b].base R[b].len = (σ.heap[b]?.getD []).map some
  whlen : σ.wheap.length = W.length
  wvlen : wv.length = W.length
  wbase : ∀ b (hb : b < W.length), σ.env (wv.getD b 0) = BitVec.ofNat 64 W[b].base
  wblen : ∀ b (hb : b < W.length), 8 * (σ.wheap[b]?.getD []).length = W[b].len
  wbyts : ∀ b (hb : b < W.length), bytes (M.mem s) W[b].base W[b].len = (wbytes (σ.wheap[b]?.getD [])).map some

/-- all regions a body may write -/
def AllR (N fp : Nat) (R W : List Region) : List Region := R ++ W ++ slots N fp

theorem memR {N fp : Nat} {R W : List Region} {r : Region} (h : r ∈ R) : r ∈ AllR N fp R W :=
  List.mem_append_left _ (List.mem_append_left _ h)
theorem memW {N fp : Nat} {R W : List Region} {r : Region} (h : r ∈ W) : r ∈ AllR N fp R W :=
  List.mem_append_left _ (List.mem_append_right _ h)
theorem memS {N fp : Nat} {R W : List Region} {r : Region} (h : r ∈ slots N fp) : r ∈ AllR N fp R W :=
  List.mem_append_right _ h

theorem disj_symm {a b : Region} (h : disjoint a b) : disjoint b a := by unfold disjoint at *; omega

/-- registers and memory unchanged: the relation survives -/
theorem RelB.same {N fp bv wv R W σ} {s s' : M.S} (r : M.RelB N fp bv wv R W σ s) (hm : M.mem s' = M.mem s)
    (hk : M.keep s s') (he : ∀ i : Fin 8, M.get s' (avar i) = M.get s (avar i)) : M.RelB N fp bv wv R W σ s' :=
  ⟨EnvB.of M r.env hm hk he, r.hlen, r.bvlen, r.base, r.blen, fun b hb => by rw [hm]; exact r.rbytes b hb,
    r.whlen, r.wvlen, r.wbase, r.wblen, fun b hb => by rw [hm]; exact r.wbyts b hb⟩

theorem getD_memN {l : List Nat} {b : Nat} (hb : b < l.length) : l.getD b 0 ∈ l := getD_mem l hb

/-- assigning a non-base variable -/
theorem RelB.setEnv {N fp bv wv R W σ} {s s' : M.S} (r : M.RelB N fp bv wv R W σ s) {v : Nat} (hvb : v ∉ bv)
    (hvw : v ∉ wv) {x : BitVec 64} (henv : M.EnvB N fp (σ.env.set v x) s')
    (hR : ∀ b (hb : b < R.length), bytes (M.mem s') R[b].base R[b].len = bytes (M.mem s) R[b].base R[b].len)
    (hW : ∀ b (hb : b < W.length), bytes (M.mem s') W[b].base W[b].len = bytes (M.mem s) W[b].base W[b].len) :
    M.RelB N fp bv wv R W ⟨σ.env.set v x, σ.heap, σ.wheap⟩ s' := by
  refine ⟨henv, r.hlen, r.bvlen, fun b hb => ?_, r.blen, fun b hb => by rw [hR b hb]; exact r.rbytes b hb,
    r.whlen, r.wvlen, fun b hb => ?_, r.wblen, fun b hb => by rw [hW b hb]; exact r.wbyts b hb⟩
  · have : bv.getD b 0 ≠ v := fun e => hvb (e ▸ getD_memN (r.bvlen ▸ hb))
    show (if bv.getD b 0 = v then x else σ.env (bv.getD b 0)) = _
    rw [ite_neg this]; exact r.base b hb
  · have : wv.getD b 0 ≠ v := fun e => hvw (e ▸ getD_memN (r.wvlen ▸ hb))
    show (if wv.getD b 0 = v then x else σ.env (wv.getD b 0)) = _
    rw [ite_neg this]; exact r.wbase b hb

theorem codeF_two (a b : XOp) : M.codeF [a, b] = M.encF a ++ M.encF b := by
  show M.encF a ++ (M.encF b ++ []) = _; rw [List.append_nil]

theorem avar_ne_rk0 (j : Fin 8) : avar j ≠ rk 0 := fun e => by
  have := avar_ge j; rw [e, rk_val (by omega)] at this; omega

/-- `v := r0` -/
theorem setV_ok {N fp : Nat} (hF : M.Frm N fp) {bv wv : List Nat} {R W : List Region} (hL : M.Lay N fp R W)
    {σ : BState} {v : Nat} (hv : v < 8 + N) (hvb : v ∉ bv) (hvw : v ∉ wv) {x : BitVec 64} {s : M.S}
    {pc : BitVec 64} (hA : M.At s pc (M.codeF (setV v))) (hx : M.get s (rk 0) = x)
    (hrel : M.RelB N fp bv wv R W σ s) :
    M.runsTo s fun s' => M.Done s s' (next pc (M.codeF (setV v)).length) ∧
      Out (AllR N fp R W) (M.mem s) (M.mem s') ∧ M.RelB N fp bv wv R W ⟨σ.env.set v x, σ.heap, σ.wheap⟩ s' := by
  by_cases h8 : v < 8
  · simp only [setV, dite_pos' h8, codeF_one] at hA ⊢
    have hmov : MovOK (avar ⟨v, h8⟩) (rk 0) := movA ⟨v, h8⟩
    refine M.runsTo_mono (M.law_mov hmov hA) fun s' ⟨d, st, m⟩ =>
      ⟨d, Out.of_eq m, RelB.setEnv M hrel hvb hvw ⟨fun i => ?_, by rw [M.keep_fr d.keep, hrel.env.fr],
        fun j hj => ?_⟩ (fun b _ => by rw [m]) (fun b _ => by rw [m])⟩
    · rw [st (avar i)]
      show _ = if i.val = v then x else σ.env i.val
      by_cases hi : i.val = v
      · rw [ite_pos (show avar i = avar ⟨v, h8⟩ from congrArg avar (Fin.ext hi)), ite_pos hi, hx]
      · rw [ite_neg (fun e => hi (congrArg Fin.val (avar_inj e))), ite_neg hi, hrel.env.reg]
    · rw [m, hrel.env.slot j hj]
      show _ = (le8 (if 8 + j = v then x else σ.env (8 + j))).map some
      rw [ite_neg (by omega)]
  · simp only [setV, dite_neg' h8, codeF_one] at hA ⊢
    have hj : v - 8 < N := by omega
    obtain ⟨hr, hal, hjm⟩ := Frm.slot M hF hj
    have hfr := Frm.fr M hF hrel.env.fr
    refine M.runsTo_mono (M.law_stS (rk_val (by omega)) hjm hA (by rw [hfr]; exact hr) (by rw [hfr]; exact hal))
      fun s' ⟨d, st, m⟩ => ?_
    rw [hfr, hx] at m
    have hl8 := length_le8 x
    have hS : ∀ (a n : Nat), (a + n ≤ fp + 8 * (v - 8 + 1) ∨ fp + 8 * (v - 8 + 1) + 8 ≤ a) →
        bytes (M.mem s') a n = bytes (M.mem s) a n := fun a n h => by
      rw [m]; exact bytes_wr_out (by rw [hl8]; omega)
    refine ⟨d, ?_, RelB.setEnv M hrel hvb hvw ⟨fun i => ?_, by rw [M.keep_fr d.keep, hrel.env.fr],
        fun j hj' => ?_⟩ (fun b hb => hS _ _ ?_) (fun b hb => hS _ _ ?_)⟩
    · rw [m]; exact Out.wr (memS (slot_mem_slots hj)) (Nat.le_refl _) (by rw [hl8]; exact Nat.le_refl _)
    · rw [st (avar i), hrel.env.reg]
      show _ = if i.val = v then x else σ.env i.val
      rw [ite_neg (by have := i.2; omega)]
    · show _ = (le8 (if 8 + j = v then x else σ.env (8 + j))).map some
      by_cases hjv : 8 + j = v
      · rw [ite_pos hjv, m, show j = v - 8 by omega]
        have := bytes_wr_self (m := M.mem s) (a := fp + 8 * (v - 8 + 1)) (l := le8 x)
        rw [hl8] at this; exact this
      · rw [ite_neg hjv, hS _ _ (by omega)]; exact hrel.env.slot j hj'
    · have := hL.fr _ (List.getElem_mem hb); unfold disjoint at this; dsimp only at this; omega
    · have := hL.fw _ (List.getElem_mem hb); unfold disjoint at this; dsimp only at this; omega

/-- code outside the regions survives -/
theorem codeAt_outF {s s' : M.S} {pc ws} {R : List Region} (hc : M.codeAt s pc ws) (hok : M.codeOK pc ws.length)
    (hd : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * ws.length⟩ r) (hu : Out R (M.mem s) (M.mem s')) : M.codeAt s' pc ws :=
  M.toMachine.codeAt_out hc hok hd hu

/-- the value of an in-bounds byte address -/
theorem addrB_ok {N fp bv wv R W σ} {s : M.S} (r : M.RelB N fp bv wv R W σ s) (hL : M.Lay N fp R W) {b : Nat}
    (hb : b < σ.heap.length) {i : BExp} (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
    ∃ hbR : b < R.length, ((addrB bv b i).denote σ.env).toNat = R[b].base + (i.denote σ.env).toNat ∧
      M.inRAM (R[b].base + (i.denote σ.env).toNat) 1 := by
  have hbR : b < R.length := r.hlen ▸ hb
  have hl := r.blen b hbR; rw [getD_get _ hb] at hl
  have hram := hL.ram _ (List.getElem_mem hbR)
  have hlt := M.ramHi_lt
  obtain ⟨h1, h2⟩ := hram
  have h1' : M.ramLo ≤ R[b].base := h1
  have h2' : R[b].base + R[b].len ≤ M.ramHi := h2
  refine ⟨hbR, ?_, ⟨by omega, by omega⟩⟩
  show (σ.env (bv.getD b 0) + i.denote σ.env).toNat = _
  rw [r.base b hbR, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := R[b].base) (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- the value of an in-bounds word address -/
theorem addrW_ok {N fp bv wv R W σ} {s : M.S} (r : M.RelB N fp bv wv R W σ s) (hL : M.Lay N fp R W) {b : Nat}
    (hb : b < σ.wheap.length) {i : BExp} (hi : (i.denote σ.env).toNat < σ.wheap[b].length) :
    ∃ hbW : b < W.length, ((addrW wv b i).denote σ.env).toNat = W[b].base + 8 * (i.denote σ.env).toNat ∧
      M.inRAM (W[b].base + 8 * (i.denote σ.env).toNat) 8 ∧ (W[b].base + 8 * (i.denote σ.env).toNat) % 8 = 0 ∧
      8 * (i.denote σ.env).toNat + 8 ≤ W[b].len := by
  have hbW : b < W.length := r.whlen ▸ hb
  have hl := r.wblen b hbW; rw [getD_get _ hb] at hl
  have hram := hL.wram _ (List.getElem_mem hbW)
  have hal := hL.wal _ (List.getElem_mem hbW)
  have hlt := M.ramHi_lt
  obtain ⟨h1, h2⟩ := hram
  have h1' : M.ramLo ≤ W[b].base := h1
  have h2' : W[b].base + W[b].len ≤ M.ramHi := h2
  refine ⟨hbW, ?_, ⟨by omega, by omega⟩, by omega, by omega⟩
  show (σ.env (wv.getD b 0) + (i.denote σ.env) <<< ((BitVec.ofNat 64 3).toNat % 64)).toNat = _
  have e3 : (BitVec.ofNat 64 3).toNat % 64 = 3 := rfl
  rw [e3, r.wbase b hbW, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    Nat.mod_eq_of_lt (a := W[b].base) (by omega), Nat.shiftLeft_eq,
    show (2 : Nat) ^ 3 = 8 from rfl, Nat.mod_eq_of_lt (a := (i.denote σ.env).toNat * 8) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem vlt_addrB {bv : List Nat} {b m : Nat} {i : BExp} (hb : b < bv.length) (hbv : ∀ x ∈ bv, x < m)
    (hi : i.vlt m) : (addrB bv b i).vlt m := ⟨hbv _ (getD_memN hb), hi⟩

theorem vlt_addrW {wv : List Nat} {b m : Nat} {i : BExp} (hb : b < wv.length) (hwv : ∀ x ∈ wv, x < m)
    (hi : i.vlt m) : (addrW wv b i).vlt m := ⟨hwv _ (getD_memN hb), hi, trivial⟩

theorem code_loopB (bv wv : List Nat) (c : BExp) (b : BStmt) : M.codeF (M.compB bv wv (.loop c b)) =
    M.codeF (mgenB c 0) ++ M.enc (.bz (rk 0) ((M.codeF (M.compB bv wv b)).length + M.lenBz + M.lenJmp)) ++
    M.codeF (M.compB bv wv b) ++
    M.enc (.jmp ((M.codeF (mgenB c 0)).length + M.lenBz + (M.codeF (M.compB bv wv b)).length)) := by
  simp only [compB, codeF_append, codeF_one]; rfl

theorem len_loopB (bv wv : List Nat) (c : BExp) (b : BStmt) : (M.codeF (M.compB bv wv (.loop c b))).length =
    (M.codeF (mgenB c 0)).length + M.lenBz + (M.codeF (M.compB bv wv b)).length + M.lenJmp := by
  rw [code_loopB]; simp only [List.length_append, M.len_bz, M.len_jmp]

theorem regionR_disj {N fp : Nat} {R W : List Region} (hL : M.Lay N fp R W) {b : Nat} (hb : b < R.length) :
    ∀ r ∈ AllR N fp R W, r ≠ R[b] → disjoint R[b] r := by
  intro r hr hne
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨b', hb', rfl⟩ := List.getElem_of_mem hr
      have hbb : b' ≠ b := fun e => hne (by subst e; rfl)
      exact pairwise_get hL.rp hb hb' (Ne.symm hbb)
    · exact hL.rw _ (List.getElem_mem hb) r hr
  · obtain ⟨j, hj, rfl⟩ := mem_slots hr
    have := hL.fr _ (List.getElem_mem hb); unfold disjoint at this ⊢; dsimp only at this ⊢; omega

theorem regionW_disj {N fp : Nat} {R W : List Region} (hL : M.Lay N fp R W) {b : Nat} (hb : b < W.length) :
    ∀ r ∈ AllR N fp R W, r ≠ W[b] → disjoint W[b] r := by
  intro r hr hne
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 hr with hr | hr
    · exact disj_symm (hL.rw r hr _ (List.getElem_mem hb))
    · obtain ⟨b', hb', rfl⟩ := List.getElem_of_mem hr
      have hbb : b' ≠ b := fun e => hne (by subst e; rfl)
      exact pairwise_get hL.wp hb hb' (Ne.symm hbb)
  · obtain ⟨j, hj, rfl⟩ := mem_slots hr
    have := hL.fw _ (List.getElem_mem hb); unfold disjoint at this ⊢; dsimp only at this ⊢; omega

theorem execB_ok {N fp : Nat} (hF : M.Frm N fp) (bv wv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N)
    (hwv : ∀ x ∈ wv, x < 8 + N) {R W : List Region} (hL : M.Lay N fp R W) :
    ∀ {p : BStmt} {σ σ' : BState}, BExec p σ σ' → M.wfB N bv wv p → ∀ {s : M.S} {pc : BitVec 64},
    M.At s pc (M.codeF (M.compB bv wv p)) →
    (∀ r ∈ AllR N fp R W, disjoint ⟨pc.toNat, 4 * (M.codeF (M.compB bv wv p)).length⟩ r) →
    M.RelB N fp bv wv R W σ s →
    M.runsTo s fun s' => M.Done s s' (next pc (M.codeF (M.compB bv wv p)).length) ∧
      Out (AllR N fp R W) (M.mem s) (M.mem s') ∧ M.RelB N fp bv wv R W σ' s'
  | _, σ, _, .assign (v := v) (e := e), hp, s, pc, hA, hcd, hrel => by
    simp only [compB, wfB, codeF_append, List.length_append] at hp hA hcd ⊢
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
    rw [← next_add]
    refine M.seq_run (M.genB_ok hF σ.env e 0 (by omega) hp.2.1 hA1 hrel.env) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    have hrel₁ := RelB.same M hrel m₁ d₁.keep fun i => k₁ _ (.inr (avar_ge i))
    refine M.runsTo_mono (M.setV_ok hF hL hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2) v₁ hrel₁) fun s₂ ⟨d₂, o₂, r₂⟩ =>
      ⟨d₂, (Out.of_eq m₁).trans o₂, r₂⟩
  | _, σ, _, .load (v := v) (b := b) (i := i) hb hi, hp, s, pc, hA, hcd, hrel => by
    simp only [compB, wfB, codeF_append, codeF_one, List.length_append] at hp hA hcd ⊢
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    rw [List.length_append, ← next_add] at hc3 ho3
    obtain ⟨hbR, ha, hram⟩ := M.addrB_ok hrel hL hb hi
    have hB : bytes (M.mem s) R[b].base R[b].len = σ.heap[b].map some := by
      rw [← getD_get _ hb]; exact hrel.rbytes b hbR
    have hbyte := get_of_bytes hB hi
    rw [← next_add, ← next_add]
    refine M.seq_run (M.genB_ok hF σ.env (addrB bv b i) 0 (by simp only [addrB, BExp.depth]; omega)
      (vlt_addrB hp6 hbv hp2) hA1 hrel.env) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    refine M.seq_run (M.law_lbu (v := σ.heap[b][(i.denote σ.env).toNat]) (rk_val (by omega)) (rk_val (by omega))
      (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2) (by rw [v₁, ha]; exact hram)
      (by rw [m₁, v₁, ha]; exact hbyte)) fun s₂ d₂ ⟨st₂, m₂⟩ => ?_
    have hrel₂ := RelB.same M hrel (m₂.trans m₁) (M.keep_trans d₁.keep d₂.keep) fun j => by
      rw [Core.Set1.other _ st₂ (avar_ne_rk0 j), k₁ _ (.inr (avar_ge j))]
    refine M.runsTo_mono (M.setV_ok hF hL hp3 hp4 hp5 (Core.Done.at _ d₂ (M.codeAt_mem (m₂.trans m₁) hc3) ho3)
      (Core.Set1.same _ st₂) hrel₂) fun s₃ ⟨d₃, o₃, r₃⟩ =>
      ⟨d₃, (Out.of_eq (m₂.trans m₁)).trans o₃, r₃⟩
  | _, σ, _, .store (b := b) (i := i) (e := e) hb hi, hp, s, pc, hA, hcd, hrel => by
    simp only [compB, wfB, codeF_append, codeF_one, List.length_append] at hp hA hcd ⊢
    obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hp
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    rw [List.length_append, ← next_add] at hc3 ho3
    obtain ⟨hbR, ha, hram⟩ := M.addrB_ok hrel hL hb hi
    have hil : (i.denote σ.env).toNat < R[b].len := by
      have := hrel.blen b hbR; rw [getD_get _ hb] at this; omega
    rw [← next_add, ← next_add]
    refine M.runsTo_trans (M.genB_ok hF σ.env (addrB bv b i) 0 (by simp only [addrB, BExp.depth]; omega)
      (vlt_addrB hp5 hbv hp3) hA1 hrel.env) fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    have hrel₁ := RelB.same M hrel m₁ d₁.keep fun j => k₁ _ (.inr (avar_ge j))
    refine M.runsTo_trans (M.genB_ok hF σ.env e 1 (by omega) hp4
      (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2) hrel₁.env) fun s₂ ⟨d₂, m₂, v₂, k₂⟩ => ?_
    have a₂ : M.get s₂ (rk 0) = (addrB bv b i).denote σ.env := by
      rw [k₂ _ (.inl (by rw [rk_val (by omega)]; omega)), v₁]
    refine M.runsTo_mono (M.law_sb (rk_val (by omega)) (rk_val (by omega))
      (Core.Done.at _ d₂ (M.codeAt_mem (m₂.trans m₁) hc3) ho3)
      (by rw [a₂, ha]; exact hL.wr _ (List.getElem_mem hbR) _ (Nat.le_add_right _ _) (by omega) s₂ d₂.ok))
      fun s₃ ⟨d₃, st₃, m₃⟩ => ⟨Core.Done.trans _ d₁ (Core.Done.trans _ d₂ d₃), ?_, ?_⟩
    · rw [a₂, ha, v₂, m₂, m₁] at m₃
      intro x hx
      rw [m₃]; unfold Mem.upd
      have := hx _ (memR (List.getElem_mem hbR))
      rw [ite_neg (by omega)]
    · rw [a₂, ha, v₂, m₂, m₁] at m₃
      have hout : ∀ a n, (a + n ≤ R[b].base ∨ R[b].base + R[b].len ≤ a) →
          bytes (M.mem s₃) a n = bytes (M.mem s) a n := fun a n h => by
        rw [m₃]; exact bytes_upd_out fun j hj => by omega
      have hk := M.keep_trans d₁.keep (M.keep_trans d₂.keep d₃.keep)
      refine ⟨⟨fun j => by rw [st₃ (avar j), k₂ _ (.inr (avar_ge j)), k₁ _ (.inr (avar_ge j)), hrel.env.reg],
          by rw [M.keep_fr hk, hrel.env.fr], fun j hj => ?_⟩,
        by rw [List.length_set, hrel.hlen], hrel.bvlen, hrel.base, fun b' hb' => ?_, fun b' hb' => ?_,
        hrel.whlen, hrel.wvlen, hrel.wbase, hrel.wblen, fun b' hb' => ?_⟩
      · rw [hout _ _ (by have := hL.fr _ (List.getElem_mem hbR); unfold disjoint at this; dsimp only at this; omega)]
        exact hrel.env.slot j hj
      · by_cases hbb : b' = b
        · subst hbb
          rw [getD_set_self _ _ hb, List.length_set, ← getD_get _ hb]; exact hrel.blen b' hb'
        · rw [getD_set_ne _ _ hbb]; exact hrel.blen b' hb'
      · by_cases hbb : b' = b
        · subst hbb
          rw [m₃, bytes_upd_in hil, hrel.rbytes b' hb', getD_set_self _ _ hb, map_set, getD_get _ hb]
        · have hd := pairwise_get hL.rp hb' hbR hbb
          unfold disjoint at hd
          rw [hout _ _ (by omega), hrel.rbytes b' hb', getD_set_ne _ _ hbb]
      · have hd := hL.rw _ (List.getElem_mem hbR) _ (List.getElem_mem hb')
        unfold disjoint at hd
        rw [hout _ _ (by omega)]; exact hrel.wbyts b' hb'
  | _, σ, _, .load64 (v := v) (b := b) (i := i) hb hi, hp, s, pc, hA, hcd, hrel => by
    simp only [compB, wfB, codeF_append, codeF_one, List.length_append] at hp hA hcd ⊢
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    rw [List.length_append, ← next_add] at hc3 ho3
    obtain ⟨hbW, ha, hram, hal, hlen⟩ := M.addrW_ok hrel hL hb hi
    have hwl := hrel.wblen b hbW
    rw [getD_get _ hb] at hwl
    have hB := hrel.wbyts b hbW
    rw [getD_get _ hb, ← hwl] at hB
    have hword := bytes_word hB hi
    rw [← next_add, ← next_add]
    refine M.seq_run (M.genB_ok hF σ.env (addrW wv b i) 0 (by simp only [addrW, BExp.depth]; omega)
      (vlt_addrW hp6 hwv hp2) hA1 hrel.env) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    refine M.seq_run (M.law_ld (v := σ.wheap[b][(i.denote σ.env).toNat]) (rk_val (by omega)) (rk_val (by omega))
      (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2) (by rw [v₁, ha]; exact hram) (by rw [v₁, ha]; exact hal)
      (by rw [m₁, v₁, ha]; exact hword)) fun s₂ d₂ ⟨st₂, m₂⟩ => ?_
    have hrel₂ := RelB.same M hrel (m₂.trans m₁) (M.keep_trans d₁.keep d₂.keep) fun j => by
      rw [Core.Set1.other _ st₂ (avar_ne_rk0 j), k₁ _ (.inr (avar_ge j))]
    refine M.runsTo_mono (M.setV_ok hF hL hp3 hp4 hp5 (Core.Done.at _ d₂ (M.codeAt_mem (m₂.trans m₁) hc3) ho3)
      (Core.Set1.same _ st₂) hrel₂) fun s₃ ⟨d₃, o₃, r₃⟩ =>
      ⟨d₃, (Out.of_eq (m₂.trans m₁)).trans o₃, r₃⟩
  | _, σ, _, .store64 (b := b) (i := i) (e := e) hb hi, hp, s, pc, hA, hcd, hrel => by
    simp only [compB, wfB, codeF_append, codeF_one, List.length_append] at hp hA hcd ⊢
    obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hp
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    rw [List.length_append, ← next_add] at hc3 ho3
    obtain ⟨hbW, ha, hram, hal, hlen⟩ := M.addrW_ok hrel hL hb hi
    have hwl := hrel.wblen b hbW
    rw [getD_get _ hb] at hwl
    rw [← next_add, ← next_add]
    refine M.runsTo_trans (M.genB_ok hF σ.env (addrW wv b i) 0 (by simp only [addrW, BExp.depth]; omega)
      (vlt_addrW hp5 hwv hp3) hA1 hrel.env) fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    have hrel₁ := RelB.same M hrel m₁ d₁.keep fun j => k₁ _ (.inr (avar_ge j))
    refine M.runsTo_trans (M.genB_ok hF σ.env e 1 (by omega) hp4
      (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2) hrel₁.env) fun s₂ ⟨d₂, m₂, v₂, k₂⟩ => ?_
    have a₂ : M.get s₂ (rk 0) = (addrW wv b i).denote σ.env := by
      rw [k₂ _ (.inl (by rw [rk_val (by omega)]; omega)), v₁]
    refine M.runsTo_mono (M.law_sd (rk_val (by omega)) (rk_val (by omega))
      (Core.Done.at _ d₂ (M.codeAt_mem (m₂.trans m₁) hc3) ho3) (by rw [a₂, ha]; exact hram)
      (by rw [a₂, ha]; exact hal))
      fun s₃ ⟨d₃, st₃, m₃⟩ => ⟨Core.Done.trans _ d₁ (Core.Done.trans _ d₂ d₃), ?_, ?_⟩
    · rw [a₂, ha, v₂, m₂, m₁] at m₃
      rw [m₃]
      exact Out.wr (memW (List.getElem_mem hbW)) (by omega) (by rw [length_le8]; omega)
    · rw [a₂, ha, v₂, m₂, m₁] at m₃
      have hout : ∀ a n, (a + n ≤ W[b].base ∨ W[b].base + W[b].len ≤ a) →
          bytes (M.mem s₃) a n = bytes (M.mem s) a n := fun a n h => by
        rw [m₃]; exact bytes_wr_out (by rw [length_le8]; omega)
      have hk := M.keep_trans d₁.keep (M.keep_trans d₂.keep d₃.keep)
      refine ⟨⟨fun j => by rw [st₃ (avar j), k₂ _ (.inr (avar_ge j)), k₁ _ (.inr (avar_ge j)), hrel.env.reg],
          by rw [M.keep_fr hk, hrel.env.fr], fun j hj => ?_⟩,
        hrel.hlen, hrel.bvlen, hrel.base, hrel.blen, fun b' hb' => ?_,
        by rw [List.length_set, hrel.whlen], hrel.wvlen, hrel.wbase, fun b' hb' => ?_, fun b' hb' => ?_⟩
      · rw [hout _ _ (by have := hL.fw _ (List.getElem_mem hbW); unfold disjoint at this; dsimp only at this; omega)]
        exact hrel.env.slot j hj
      · have hd := hL.rw _ (List.getElem_mem hb') _ (List.getElem_mem hbW)
        unfold disjoint at hd
        rw [hout _ _ (by omega)]; exact hrel.rbytes b' hb'
      · by_cases hbb : b' = b
        · subst hbb
          rw [getD_set_self _ _ hb, List.length_set, ← getD_get _ hb]; exact hrel.wblen b' hb'
        · rw [getD_set_ne _ _ hbb]; exact hrel.wblen b' hb'
      · by_cases hbb : b' = b
        · subst hbb
          have hB := hrel.wbyts b' hbW
          rw [getD_get _ hb, ← hwl] at hB
          rw [m₃, getD_set_self _ _ hb, ← hwl]
          exact bytes_word_set hB hi _
        · have hd := pairwise_get hL.wp hb' hbW hbb
          unfold disjoint at hd
          rw [hout _ _ (by omega), hrel.wbyts b' hb', getD_set_ne _ _ hbb]
  | _, σ, _, .seq (p := p) (q := q) hpx hqx, hp, s, pc, hA, hcd, hrel => by
    simp only [compB, wfB, codeF_append, List.length_append] at hp hA hcd ⊢
    have e := M.pc_toNat hA.codeOK (a := (M.codeF (M.compB bv wv p)).length) (by rw [List.length_append]; omega)
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
    have hcd₂ := Machine.disj_sub (p' := (next pc (M.codeF (M.compB bv wv p)).length).toNat)
      (n' := 4 * (M.codeF (M.compB bv wv q)).length) hcd (by rw [e]; omega) (by rw [e]; omega)
    rw [← next_add]
    refine M.runsTo_trans (execB_ok hF bv wv hbv hwv hL hpx hp.1 hA1 (Machine.disj_sub hcd (Nat.le_refl _) (by omega)) hrel)
      fun s₁ ⟨d₁, o₁, r₁⟩ => ?_
    exact M.runsTo_mono (execB_ok hF bv wv hbv hwv hL hqx hp.2 (Core.Done.at _ d₁ (M.codeAt_out hc2 ho2 hcd₂ o₁) ho2)
      hcd₂ r₁) fun s₂ ⟨d₂, o₂, r₂⟩ => ⟨Core.Done.trans _ d₁ d₂, o₁.trans o₂, r₂⟩
  | _, σ, _, .loopF (c := c) (b := body) hc0, hp, s, pc, hA, hcd, hrel => by
    obtain ⟨hp1, hpv, hp2, hp3, hp4⟩ := hp
    rw [code_loopB] at hA
    rw [len_loopB]
    obtain ⟨hA123, -, -⟩ := Core.At.split _ hA
    obtain ⟨hA12, -, -⟩ := Core.At.split _ hA123
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    refine M.seq_run (M.genB_ok hF σ.env c 0 (by omega) hpv hA1 hrel.env) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    refine M.runsTo_mono (M.law_bz (rk_val (by omega)) hp3 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2))
      fun s₂ ⟨d₂, st, m₂⟩ => ⟨?_, Out.of_eq (m₂.trans m₁),
        RelB.same M hrel (m₂.trans m₁) (M.keep_trans d₁.keep d₂.keep) fun j => by rw [st, k₁ _ (.inr (avar_ge j))]⟩
    rw [v₁, ite_pos hc0, next_add] at d₂
    rw [show (M.codeF (mgenB c 0)).length + M.lenBz + (M.codeF (M.compB bv wv body)).length + M.lenJmp =
      (M.codeF (mgenB c 0)).length + ((M.codeF (M.compB bv wv body)).length + M.lenBz + M.lenJmp) by omega]
    exact d₂
  | _, σ, σ₂, .loopT (c := c) (b := body) (σ₁ := σ₁) hc0 hb hl, hp, s, pc, hA, hcd, hrel => by
    have hp' := hp
    obtain ⟨hp1, hpv, hp2, hp3, hp4⟩ := hp'
    have hA0 := hA
    have hcd0 := hcd
    rw [code_loopB] at hA
    rw [len_loopB] at hcd
    have hok := hA0.codeOK
    rw [len_loopB] at hok
    obtain ⟨hA123, hc4, ho4⟩ := Core.At.split _ hA
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA123
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    simp only [List.length_append, M.len_bz] at hc3 ho3 hc4 ho4
    have e3 := M.pc_toNat hok (a := (M.codeF (mgenB c 0)).length + M.lenBz) (by omega)
    have e4 := M.pc_toNat hok (a := (M.codeF (mgenB c 0)).length + M.lenBz + (M.codeF (M.compB bv wv body)).length)
      (by omega)
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hpv hA1 hrel.env) fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hp3 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_neg hc0, M.len_bz, next_add] at d₂
    have m₂₀ := m₂.trans m₁
    have hrel₂ : M.RelB N fp bv wv R W σ s₂ :=
      RelB.same M hrel m₂₀ (M.keep_trans d₁.keep d₂.keep) fun j => by rw [st₂, k₁ _ (.inr (avar_ge j))]
    have hcd3 := Machine.disj_sub (p' := (next pc ((M.codeF (mgenB c 0)).length + M.lenBz)).toNat)
      (n' := 4 * (M.codeF (M.compB bv wv body)).length) hcd (by rw [e3]; omega) (by rw [e3]; omega)
    refine M.runsTo_trans (execB_ok hF bv wv hbv hwv hL hb hp2 (Core.Done.at _ d₂ (M.codeAt_mem m₂₀ hc3) ho3) hcd3 hrel₂)
      fun s₃ ⟨d₃, o₃, r₃⟩ => ?_
    rw [next_add] at d₃
    have o₃' : Out (AllR N fp R W) (M.mem s) (M.mem s₃) := (Out.of_eq m₂₀).trans o₃
    have hcd4 := Machine.disj_sub (p' := (next pc ((M.codeF (mgenB c 0)).length + M.lenBz +
      (M.codeF (M.compB bv wv body)).length)).toNat) (n' := 4 * (M.enc (.jmp ((M.codeF (mgenB c 0)).length + M.lenBz +
      (M.codeF (M.compB bv wv body)).length))).length) hcd (by rw [e4]; omega) (by rw [e4, M.len_jmp]; omega)
    refine M.runsTo_trans (M.law_jmp hp4 (Core.Done.at _ d₃ (M.codeAt_out hc4 ho4 hcd4 o₃') ho4))
      fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
    rw [next_jmp] at d₄
    have o₄ : Out (AllR N fp R W) (M.mem s) (M.mem s₄) := o₃'.trans (Out.of_eq m₄)
    refine M.runsTo_mono (execB_ok hF bv wv hbv hwv hL hl hp (Core.Done.at _ d₄ (M.codeAt_out hA0.code hA0.codeOK hcd0 o₄)
      hA0.codeOK) hcd0 (RelB.same M r₃ m₄ d₄.keep fun j => st₄ _)) fun s₅ ⟨d₅, o₅, r₅⟩ => ⟨?_, o₄.trans o₅, r₅⟩
    exact Core.Done.trans _ d₁ (Core.Done.trans _ d₂ (Core.Done.trans _ d₃ (Core.Done.trans _ d₄ d₅)))

/-- the heap part of `RelB` -/
structure HeapB (bv wv : List Nat) (R W : List Region) (σ : BState) (s : M.S) : Prop where
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  rbytes : ∀ b (hb : b < R.length), bytes (M.mem s) R[b].base R[b].len = (σ.heap[b]?.getD []).map some
  whlen : σ.wheap.length = W.length
  wvlen : wv.length = W.length
  wbase : ∀ b (hb : b < W.length), σ.env (wv.getD b 0) = BitVec.ofNat 64 W[b].base
  wblen : ∀ b (hb : b < W.length), 8 * (σ.wheap[b]?.getD []).length = W[b].len
  wbyts : ∀ b (hb : b < W.length), bytes (M.mem s) W[b].base W[b].len = (wbytes (σ.wheap[b]?.getD [])).map some

/-- every region of `A` lies inside one of `B`: `Out A` implies `Out B` -/
theorem Out.mono {A B : List Region} {m m' : Mem} (h : Out A m m')
    (hab : ∀ r ∈ A, ∃ r' ∈ B, r'.base ≤ r.base ∧ r.base + r.len ≤ r'.base + r'.len) : Out B m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hab r hr
    have := hx r' hr'; omega

theorem bytes_out {R : List Region} {m m' : Mem} (h : Out R m m') {a n : Nat}
    (hd : ∀ r ∈ R, disjoint ⟨a, n⟩ r) : bytes m' a n = bytes m a n :=
  bytes_congr fun j hj => h _ fun r hr => by have := hd r hr; unfold disjoint at this; dsimp only at this; omega

/-- **`BStmt` compiler correctness from the extended interface laws** (as a function with a frame of `N`
slots: `enter N`, body, `leave`, return to `ra`).  Slots start at `0`; the frame `F` is
`⟨frameAt s N, 8 (N + 1)⟩`.  The run returns to `ra` with `σ'` in the variable registers and the blocks,
memory outside the blocks and `F` unchanged, `ok` and the full frame `keep` (frame register included). -/
theorem compBF_ok (N : Nat) (bv wv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N) (hwv : ∀ x ∈ wv, x < 8 + N)
    {p : BStmt} (hp : M.wfB N bv wv p) {R W : List Region} {σ σ' : BState} (hex : BExec p σ σ')
    {s : M.S} {pc : BitVec 64} (hA : M.At s pc (M.codeF (M.compBF N bv wv p))) (hen : M.enterOK s N)
    (hL : M.Lay N (M.frameAt s N) R W)
    (hcd : ∀ r ∈ R ++ W ++ [⟨M.frameAt s N, 8 * (N + 1)⟩],
      disjoint ⟨pc.toNat, 4 * (M.codeF (M.compBF N bv wv p)).length⟩ r)
    (hreg : ∀ i : Fin 8, M.get s (avar i) = σ.env i.val) (hslot : ∀ j, j < N → σ.env (8 + j) = 0)
    (hheap : M.HeapB bv wv R W σ s) (hra : M.retOK (M.ra s)) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ (∀ i : Fin 8, M.get s' (avar i) = σ'.env i.val) ∧
      M.HeapB bv wv R W σ' s' ∧ Out (R ++ W ++ [⟨M.frameAt s N, 8 * (N + 1)⟩]) (M.mem s) (M.mem s') ∧
      M.ok s' ∧ M.keep s s' := by
  generalize hfp : M.frameAt s N = fp at hL hcd ⊢
  obtain ⟨hns, hram, hal⟩ := M.enterOK_frame hen
  rw [hfp] at hram hal
  have hF : M.Frm N fp := ⟨hram, hal, hns⟩
  simp only [compBF, codeF_append, codeF_one, codeF_two, List.length_append] at hA hcd
  obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA
  obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
  rw [List.length_append, ← next_add] at hc3 ho3
  have hok := hA.codeOK
  simp only [List.length_append] at hok
  have hFm : (⟨fp, 8 * (N + 1)⟩ : Region) ∈ R ++ W ++ [⟨fp, 8 * (N + 1)⟩] := List.mem_append_right _ (List.mem_singleton_self _)
  have e2 := M.pc_toNat hok (a := (M.encF (.f (.enter N))).length) (by omega)
  have e3 := M.pc_toNat hok (a := (M.encF (.f (.enter N))).length + (M.codeF (M.compB bv wv p)).length) (by omega)
  have hcdA : ∀ r ∈ R ++ W ++ [⟨fp, 8 * (N + 1)⟩], disjoint ⟨(next pc (M.encF (.f (.enter N))).length).toNat,
      4 * (M.codeF (M.compB bv wv p)).length⟩ r :=
    Machine.disj_sub hcd (by rw [e2]; omega) (by rw [e2]; omega)
  have hcdB : ∀ r ∈ R ++ W ++ [⟨fp, 8 * (N + 1)⟩], disjoint ⟨(next (next pc (M.encF (.f (.enter N))).length)
      (M.codeF (M.compB bv wv p)).length).toNat, 4 * (M.encF (.f .leave) ++ M.encF (.a .ret)).length⟩ r := by
    rw [next_add]; exact Machine.disj_sub hcd (by rw [e3]; omega) (by rw [e3, List.length_append]; omega)
  have hcdF := hcd _ hFm
  -- enter
  refine M.runsTo_trans (M.law_enter hen hA1 (by
    rw [hfp]; unfold disjoint at hcdF ⊢; dsimp only [encF] at hcdF ⊢; omega)) fun s₁ ⟨ok₁, kf₁, pc₁, fr₁, rg₁, o₁, sv₁, z₁⟩ => ?_
  rw [hfp] at fr₁ o₁ sv₁ z₁
  have hR1 : ∀ r ∈ R ++ W, disjoint ⟨fp, 8 * (N + 1)⟩ r := fun r hr => by
    rcases List.mem_append.1 hr with hr | hr; exact hL.fr r hr; exact hL.fw r hr
  have byR : ∀ r ∈ R ++ W, bytes (M.mem s₁) r.base r.len = bytes (M.mem s) r.base r.len := fun r hr =>
    bytes_out o₁ fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact disj_symm (hR1 r hr)
  have hrel₁ : M.RelB N fp bv wv R W σ s₁ := by
    refine ⟨⟨fun i => by rw [rg₁ _ (avar_ge i), hreg], fr₁, fun j hj => by rw [z₁ j hj, hslot j hj]⟩,
      hheap.hlen, hheap.bvlen, hheap.base, hheap.blen, fun b hb => ?_, hheap.whlen, hheap.wvlen, hheap.wbase,
      hheap.wblen, fun b hb => ?_⟩
    · rw [byR _ (List.mem_append_left _ (List.getElem_mem hb))]; exact hheap.rbytes b hb
    · rw [byR _ (List.mem_append_right _ (List.getElem_mem hb))]; exact hheap.wbyts b hb
  have hcd1 : ∀ r ∈ [(⟨fp, 8 * (N + 1)⟩ : Region)], disjoint ⟨(next pc (M.encF (.f (.enter N))).length).toNat,
      4 * (M.codeF (M.compB bv wv p)).length⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hcdA _ hFm
  have hA₁ : M.At s₁ (next pc (M.encF (.f (.enter N))).length) (M.codeF (M.compB bv wv p)) :=
    ⟨ok₁, pc₁, M.codeAt_out hc2 ho2 hcd1 o₁, ho2⟩
  have hcdS : ∀ r ∈ AllR N fp R W, disjoint ⟨(next pc (M.encF (.f (.enter N))).length).toNat,
      4 * (M.codeF (M.compB bv wv p)).length⟩ r := fun r hr => by
    rcases List.mem_append.1 hr with hr | hr
    · exact hcdA r (List.mem_append_left _ hr)
    · obtain ⟨j, hj, rfl⟩ := mem_slots hr
      have := hcdA _ hFm; unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  -- body
  refine M.runsTo_trans (M.execB_ok hF bv wv hbv hwv hL hex hp hA₁ hcdS hrel₁) fun s₂ ⟨d₂, o₂, r₂⟩ => ?_
  -- leave
  have hfr₂ : M.fr s₂ = BitVec.ofNat 64 fp := r₂.env.fr
  have hfrN := Frm.fr M hF hfr₂
  have hsv₂ : bytes (M.mem s₂) fp 8 = (le8 (M.fr s)).map some := by
    rw [← sv₁]; exact bytes_out o₂ fun r hr => by
      rcases List.mem_append.1 hr with hr | hr
      · have := hR1 r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega
      · obtain ⟨j, hj, rfl⟩ := mem_slots hr; unfold disjoint; dsimp only; omega
  have hoA : Out (R ++ W ++ [⟨fp, 8 * (N + 1)⟩]) (M.mem s₁) (M.mem s₂) := Out.mono o₂ fun r hr => by
    rcases List.mem_append.1 hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨j, hj, rfl⟩ := mem_slots hr
      exact ⟨_, hFm, by dsimp only; omega, by dsimp only; omega⟩
  have hoF : Out (R ++ W ++ [⟨fp, 8 * (N + 1)⟩]) (M.mem s) (M.mem s₁) := Out.mono o₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hFm, Nat.le_refl _, Nat.le_refl _⟩
  have hA₂ : M.At s₂ (next (next pc (M.encF (.f (.enter N))).length) (M.codeF (M.compB bv wv p)).length)
      (M.encF (.f .leave) ++ M.encF (.a .ret)) :=
    Core.Done.at _ d₂ (M.codeAt_out hc3 ho3 hcdB (hoF.trans hoA)) ho3
  obtain ⟨hA₂l, hc4, ho4⟩ := Core.At.split _ hA₂
  have hram0 : M.inRAM (M.fr s₂).toNat 8 := by
    rw [hfrN]; unfold Base.inRAM at hram ⊢; omega
  refine M.runsTo_trans (M.law_leave (w := M.fr s) hA₂l hram0 (by rw [hfrN]; exact hal) (by rw [hfrN]; exact hsv₂))
    fun s₃ ⟨ok₃, kf₃, pc₃, fr₃, st₃, m₃⟩ => ?_
  -- ret
  have kfs : M.keepF s s₃ := M.keepF_trans kf₁ (M.keepF_trans (M.keepF_of_keep d₂.keep) kf₃)
  have era : M.ra s₃ = M.ra s := M.keepF_ra kfs
  refine M.runsTo_mono (M.law_ret (by rw [era]; exact hra) ⟨ok₃, pc₃, M.codeAt_mem m₃ hc4, ho4⟩)
    fun s₄ ⟨d₄, st₄, m₄⟩ => ⟨by rw [← era]; exact d₄.hpc, fun i => by rw [st₄, st₃, r₂.env.reg], ?_, ?_, d₄.ok, ?_⟩
  · have m := m₄.trans m₃
    exact ⟨r₂.hlen, r₂.bvlen, r₂.base, r₂.blen, fun b hb => by rw [m]; exact r₂.rbytes b hb, r₂.whlen, r₂.wvlen,
      r₂.wbase, r₂.wblen, fun b hb => by rw [m]; exact r₂.wbyts b hb⟩
  · exact (hoF.trans hoA).trans (Out.of_eq (m₄.trans m₃))
  · exact M.keep_of_keepF (M.keepF_trans kfs (M.keepF_of_keep d₄.keep)) (by rw [M.keep_fr d₄.keep, fr₃])

end MachineF
end Proven.Mach
