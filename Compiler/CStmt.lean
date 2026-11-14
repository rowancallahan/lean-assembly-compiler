/- Middle layer, function calls: `CStmt` / `Fn` / `Prog` (`CLang.lean`) to abstract operations with calls
(`YOp`), and its correctness from the `MachineC` laws only (`execC_ok`), by induction on the source run.

Calling convention (abstract; RISC-V names in brackets):
* globals `0 .. 7` in `avar 0 .. 7` [`a0 .. a7`]: shared program state, never saved;
* locals in the frame: local `j` of the running function is slot `j`, the 8 bytes at `fr + 8 (j + 1)`
  (`fr` [`gp`] the frame register); cell 0 (`fr`) holds the saved return address;
* a call `res := f(args)`: the caller evaluates argument `j` into `r0` [`t0`] and stores it at
  `fr - 8 (n - j)`, which is slot `j` of the callee's frame (`n` = the callee's number of locals; the
  callee's other locals are stored as `0` the same way); then `call` (link register := return address);
* the callee: `enterC n` (`fr := fr - 8 (n + 1)`, cell 0 := link register), body, result into `r0`,
  `leaveC n` (link register := cell 0, `fr := fr + 8 (n + 1)`), `ret`;
* the caller stores `r0` into `res`.
Temporaries `r0 .. r6` are caller-saved (dead across statements); the frame register and the caller's
frame are preserved by the callee; the link register is not preserved by statements (saved in cell 0). -/
import Compiler.CLang
import Compiler.Call
import Compiler.BStmt

namespace Proven.Mach
open MachineF

/-- the number of locals of function `f` (0 if there is none) -/
def nlOf (P : Prog) (f : Nat) : Nat := match P[f]? with | some F => F.nlocals | none => 0

theorem nlOf_eq {P : Prog} {f : Nat} (hf : f < P.length) : nlOf P f = P[f].nlocals := by
  unfold nlOf; rw [List.getElem?_eq_getElem hf]

/-- the arguments, padded with zeros for the callee's other locals -/
def padArgs (n : Nat) (args : List BExp) : List BExp := args ++ List.replicate (n - args.length) (.const 0)

theorem padArgs_length {n : Nat} {args : List BExp} (h : args.length ≤ n) : (padArgs n args).length = n := by
  unfold padArgs; rw [List.length_append, List.length_replicate]; omega

theorem pad_wf {n m : Nat} {args : List BExp} (h : ∀ e ∈ args, e.depth < 7 ∧ e.vlt m) :
    ∀ e ∈ padArgs n args, e.depth < 7 ∧ e.vlt m := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact h e he
  · rw [(List.mem_replicate.1 he).2]; exact ⟨Nat.succ_pos _, trivial⟩

theorem pad_denote {n : Nat} {args : List BExp} (env : BEnv) {j : Nat} (hj : j < (padArgs n args).length) :
    ((padArgs n args)[j]).denote env = (args.map (·.denote env)).getD j 0 := by
  unfold padArgs at hj ⊢
  by_cases h : j < args.length
  · rw [List.getElem_append_left h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]; rfl
  · rw [List.getElem_append_right (by omega), List.getElem_replicate, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [List.length_map]; omega)]; rfl

/-- store the values of `es` into slots `j, j + 1, ..` of a callee with `n` slots -/
def argsC (n : Nat) : Nat → List BExp → List YOp
  | _, [] => []
  | j, e :: es => (mgenB e 0).map .x ++ [.c (.stA (n - j) (rk 0))] ++ argsC n (j + 1) es

/-- the words `ws` are the words `pos, pos + 1, ..` of `W` -/
def Sub (W : List (BitVec 32)) (pos : Nat) (ws : List (BitVec 32)) : Prop :=
  ∃ pre post, W = pre ++ ws ++ post ∧ pre.length = pos

theorem Sub.split {W : List (BitVec 32)} {pos : Nat} {a b : List (BitVec 32)} (h : Sub W pos (a ++ b)) :
    Sub W pos a ∧ Sub W (pos + a.length) b := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨⟨pre, b ++ post, by simp only [List.append_assoc], rfl⟩,
    ⟨pre ++ a, post, by simp only [List.append_assoc], List.length_append⟩⟩

theorem Sub.le {W : List (BitVec 32)} {pos : Nat} {ws : List (BitVec 32)} (h : Sub W pos ws) :
    pos + ws.length ≤ W.length := by
  obtain ⟨pre, post, rfl, rfl⟩ := h; simp only [List.length_append]; omega

theorem Sub.cast {W : List (BitVec 32)} {a b : Nat} {ws : List (BitVec 32)} (h : Sub W a ws) (e : a = b) :
    Sub W b ws := e ▸ h

/-- what a statement in the frame `(N, fp)` may write: the blocks, its slots, the stack below `fp` -/
def Wrt (N fp : Nat) (R Wr : List Region) (lo : Nat) : List Region := AllR N fp R Wr ++ [⟨lo, fp - lo⟩]
/-- the blocks and the stack below `fp` -/
def Low (R Wr : List Region) (lo fp : Nat) : List Region := R ++ Wr ++ [⟨lo, fp - lo⟩]

theorem out1 {a l b l' : Nat} {m m' : Mem} (h : Out [⟨a, l⟩] m m') (h1 : b ≤ a) (h2 : a + l ≤ b + l') :
    Out [⟨b, l'⟩] m m' :=
  Out.mono h fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, h1, h2⟩

theorem memLast {A : List Region} {r : Region} : r ∈ A ++ [r] := List.mem_append_right _ (List.mem_singleton_self _)

theorem wrt_G {N fp lo hi : Nat} {R Wr : List Region} {m m' : Mem} (h : Out (Wrt N fp R Wr lo) m m')
    (h1 : lo ≤ fp) (h2 : fp + 8 * (N + 1) ≤ hi) : Out (R ++ Wr ++ [⟨lo, hi - lo⟩]) m m' :=
  Out.mono h fun r hr => by
    unfold Wrt AllR at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · exact ⟨r, List.mem_append_left _ (List.mem_append_left _ hr), Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨j, hj, rfl⟩ := mem_slots hr
      exact ⟨_, memLast, by dsimp only; omega, by dsimp only; omega⟩
    · subst hr; exact ⟨_, memLast, by dsimp only; omega, by dsimp only; omega⟩

theorem low_G {fp lo hi : Nat} {R Wr : List Region} {m m' : Mem} (h : Out (Low R Wr lo fp) m m')
    (h1 : lo ≤ fp) (h2 : fp ≤ hi) : Out (R ++ Wr ++ [⟨lo, hi - lo⟩]) m m' :=
  Out.mono h fun r hr => by
    unfold Low at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | hr) | hr
    · exact ⟨r, List.mem_append_left _ (List.mem_append_left _ hr), Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), Nat.le_refl _, Nat.le_refl _⟩
    · subst hr; exact ⟨_, memLast, by dsimp only; omega, by dsimp only; omega⟩

theorem allR_wrt {N fp lo : Nat} {R Wr : List Region} {m m' : Mem} (h : Out (AllR N fp R Wr) m m') :
    Out (Wrt N fp R Wr lo) m m' :=
  Out.mono h fun r hr => ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩

theorem low_wrt {N fp lo : Nat} {R Wr : List Region} {m m' : Mem} (h : Out (Low R Wr lo fp) m m') :
    Out (Wrt N fp R Wr lo) m m' :=
  Out.mono h fun r hr => by
    unfold Low at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | hr) | hr
    · exact ⟨r, List.mem_append_left _ (memR hr), Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨r, List.mem_append_left _ (memW hr), Nat.le_refl _, Nat.le_refl _⟩
    · subst hr; exact ⟨_, memLast, Nat.le_refl _, Nat.le_refl _⟩

/-- the callee's writes are below the caller's frame -/
theorem wrt_low {N fp' fp lo : Nat} {R Wr : List Region} {m m' : Mem} (h : Out (Wrt N fp' R Wr lo) m m')
    (h1 : lo ≤ fp') (h2 : fp' + 8 * (N + 1) ≤ fp) : Out (Low R Wr lo fp) m m' :=
  Out.mono h fun r hr => by
    unfold Wrt AllR at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · exact ⟨r, List.mem_append_left _ (List.mem_append_left _ hr), Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨j, hj, rfl⟩ := mem_slots hr
      exact ⟨_, memLast, by dsimp only; omega, by dsimp only; omega⟩
    · subst hr; exact ⟨_, memLast, by dsimp only; omega, by dsimp only; omega⟩

theorem out_low {fp lo : Nat} {R Wr : List Region} {m m' : Mem} (h : Out [⟨lo, fp - lo⟩] m m') :
    Out (Low R Wr lo fp) m m' :=
  Out.mono h fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact ⟨_, memLast, Nat.le_refl _, Nat.le_refl _⟩

namespace MachineC
variable (M : MachineC) (P : Prog) (bv wv : List Nat) (off : Nat → Nat)

theorem codeC_two (a b : YOp) : M.codeC [a, b] = M.encY a ++ M.encY b := by
  show M.encY a ++ (M.encY b ++ []) = _; rw [List.append_nil]

/-- word length of `li r0, 0` -/
def lenLi : Nat := (M.enc (.li (rk 0) 0)).length

theorem lenLi_eq : (M.enc (.li (rk 0) 0)).length = M.lenLi := rfl

/-- word length of the argument code of a call to a function with `n` locals -/
def lenArgs (n : Nat) (args : List BExp) : Nat := (M.codeC (argsC n 0 (padArgs n args))).length

/-- word length of a statement's code -/
def lenC : CStmt → Nat
  | .base p => (M.codeF (M.compB bv wv p)).length
  | .seq p q => lenC p + lenC q
  | .ite c p q => (M.codeF (mgenB c 0)).length + M.lenBz + lenC p + (M.lenLi + M.lenBz) + lenC q
  | .loop c b => (M.codeF (mgenB c 0)).length + M.lenBz + lenC b + M.lenJmp
  | .call res f args => M.lenArgs (nlOf P f) args + M.lenCall + (M.codeF (setV res)).length

/-- the code of a statement placed at word `pos` of the program; `off f` = the word where `f` starts -/
def compC : Nat → CStmt → List YOp
  | _, .base p => (M.compB bv wv p).map .x
  | pos, .seq p q => compC pos p ++ compC (pos + M.lenC P bv wv p) q
  | pos, .ite c p q =>
      (mgenB c 0).map .x ++ [.x (.a (.bz (rk 0) (M.lenBz + M.lenC P bv wv p + (M.lenLi + M.lenBz))))] ++
      compC (pos + (M.codeF (mgenB c 0)).length + M.lenBz) p ++
      [.x (.a (.li (rk 0) 0)), .x (.a (.bz (rk 0) (M.lenBz + M.lenC P bv wv q)))] ++
      compC (pos + (M.codeF (mgenB c 0)).length + M.lenBz + M.lenC P bv wv p + (M.lenLi + M.lenBz)) q
  | pos, .loop c b =>
      (mgenB c 0).map .x ++ [.x (.a (.bz (rk 0) (M.lenC P bv wv b + M.lenBz + M.lenJmp)))] ++
      compC (pos + (M.codeF (mgenB c 0)).length + M.lenBz) b ++
      [.x (.a (.jmp ((M.codeF (mgenB c 0)).length + M.lenBz + M.lenC P bv wv b)))]
  | pos, .call res f args =>
      argsC (nlOf P f) 0 (padArgs (nlOf P f) args) ++
      [.c (.call ((off f : Int) - ((pos + M.lenArgs (nlOf P f) args : Nat) : Int)))] ++ (setV res).map .x

theorem len_compC : ∀ (p : CStmt) (pos : Nat), (M.codeC (M.compC P bv wv off pos p)).length = M.lenC P bv wv p
  | .base p, pos => by simp only [compC, lenC, codeC_map]
  | .seq p q, pos => by
    simp only [compC, lenC, codeC_append, List.length_append, len_compC p, len_compC q]
  | .ite c p q, pos => by
    simp only [compC, lenC, codeC_append, codeC_map, codeC_one, codeC_two, encY, MachineF.encF,
      List.length_append, len_compC p, len_compC q, M.len_bz, lenLi_eq]
  | .loop c b, pos => by
    simp only [compC, lenC, codeC_append, codeC_map, codeC_one, encY, MachineF.encF,
      List.length_append, len_compC b, M.len_bz, M.len_jmp]
  | .call res f args, pos => by
    simp only [compC, lenC, lenArgs, codeC_append, codeC_map, codeC_one, encY, List.length_append, M.len_call]

/-- well-formed statement in a function with `N` locals, placed at `pos` -/
def wfC (N : Nat) : Nat → CStmt → Prop
  | _, .base p => M.wfB N bv wv p
  | pos, .seq p q => wfC N pos p ∧ wfC N (pos + M.lenC P bv wv p) q
  | pos, .ite c p q => c.depth < 7 ∧ c.vlt (8 + N) ∧
      M.bzOK (M.lenBz + M.lenC P bv wv p + (M.lenLi + M.lenBz)) ∧ M.bzOK (M.lenBz + M.lenC P bv wv q) ∧
      wfC N (pos + (M.codeF (mgenB c 0)).length + M.lenBz) p ∧
      wfC N (pos + (M.codeF (mgenB c 0)).length + M.lenBz + M.lenC P bv wv p + (M.lenLi + M.lenBz)) q
  | pos, .loop c b => c.depth < 7 ∧ c.vlt (8 + N) ∧ M.bzOK (M.lenC P bv wv b + M.lenBz + M.lenJmp) ∧
      M.jmpOK ((M.codeF (mgenB c 0)).length + M.lenBz + M.lenC P bv wv b) ∧
      wfC N (pos + (M.codeF (mgenB c 0)).length + M.lenBz) b
  | pos, .call res f args => f < P.length ∧ args.length ≤ nlOf P f ∧ (∀ e ∈ args, e.depth < 7 ∧ e.vlt (8 + N)) ∧
      res < 8 + N ∧ res ∉ bv ∧ res ∉ wv ∧
      M.callOK ((off f : Int) - ((pos + M.lenArgs (nlOf P f) args : Nat) : Int))

/-- the code of a function placed at `pos` -/
def fnC (pos : Nat) (F : Fn) : List YOp :=
  [.c (.enterC F.nlocals)] ++ M.compC P bv wv off (pos + (M.encC (.enterC F.nlocals)).length) F.body ++
    (mgenB F.ret 0).map .x ++ [.c (.leaveC F.nlocals), .x (.a .ret)]

def lenF (F : Fn) : Nat :=
  (M.encC (.enterC F.nlocals)).length + M.lenC P bv wv F.body + (M.codeF (mgenB F.ret 0)).length +
    ((M.encC (.leaveC F.nlocals)).length + (M.enc .ret).length)

theorem len_fnC (pos : Nat) (F : Fn) : (M.codeC (M.fnC P bv wv off pos F)).length = M.lenF P bv wv F := by
  simp only [fnC, lenF, codeC_append, codeC_map, codeC_one, codeC_two, encY, MachineF.encF, List.length_append,
    len_compC]

def wfF (pos : Nat) (F : Fn) : Prop :=
  F.nlocals ≤ M.maxSlots ∧ F.ret.depth < 7 ∧ F.ret.vlt (8 + F.nlocals) ∧
    M.wfC P bv wv off F.nlocals (pos + (M.encC (.enterC F.nlocals)).length) F.body

/-- the static context of a run: the program's words `W` at `cb` (function `f` at word `off f`), the byte
blocks `R`, the word blocks `Wr`, the stack area `[lo, hi)`; all in RAM and pairwise disjoint. -/
structure Ctx (cb : BitVec 64) (W : List (BitVec 32)) (R Wr : List Region) (lo hi : Nat) : Prop where
  codeOK : M.codeOK cb W.length
  fns : ∀ f (hf : f < P.length), Sub W (off f) (M.codeC (M.fnC P bv wv off (off f) P[f]))
  wf : ∀ f (hf : f < P.length), M.wfF P bv wv off (off f) P[f]
  bvlt : ∀ x ∈ bv, x < 8
  wvlt : ∀ x ∈ wv, x < 8
  ram : ∀ r ∈ R, M.inRAM r.base r.len
  wram : ∀ r ∈ Wr, M.inRAM r.base r.len
  rp : R.Pairwise disjoint
  wp : Wr.Pairwise disjoint
  rw : ∀ r ∈ R, ∀ w ∈ Wr, disjoint r w
  wal : ∀ w ∈ Wr, w.base % 8 = 0
  lohi : lo ≤ hi
  stk : M.inRAM lo (hi - lo)
  sR : ∀ r ∈ R ++ Wr, disjoint ⟨lo, hi - lo⟩ r
  cd : ∀ r ∈ R ++ Wr ++ [⟨lo, hi - lo⟩], disjoint ⟨cb.toNat, 4 * W.length⟩ r

variable {P bv wv off}
variable {cb : BitVec 64} {W : List (BitVec 32)} {R Wr : List Region} {lo hi : Nat}

theorem pcIs_cast {s : M.S} {cb : BitVec 64} {a b : Nat} (h : M.pcIs s (next cb a)) (e : a = b) :
    M.pcIs s (next cb b) := e ▸ h

theorem done_cast {s s' : M.S} {cb : BitVec 64} {a b : Nat} (h : M.Done s s' (next cb a)) (e : a = b) :
    M.Done s s' (next cb b) := e ▸ h

theorem pcIs_jmp {s : M.S} {cb : BitVec 64} {X n pos : Nat} (h : M.pcIs s (next cb X - BitVec.ofNat 64 (4 * n)))
    (e : X = pos + n) : M.pcIs s (next cb pos) := by
  subst e; rwa [← next_add, next_jmp] at h

theorem kC {s s' : M.S} {pc : BitVec 64} (d : M.Done s s' pc) : M.keepC s s' :=
  M.keepC_of_keepF (M.keepF_of_keep d.keep)

theorem at_sub {cb : BitVec 64} {W ws : List (BitVec 32)} {pos : Nat} {s : M.S} (hok : M.codeOK cb W.length)
    (hc : M.codeAt s cb W) (hs : Sub W pos ws) (ho : M.ok s) (hpc : M.pcIs s (next cb pos)) :
    M.At s (next cb pos) ws := by
  obtain ⟨pre, post, rfl, rfl⟩ := hs
  have h1 := (M.codeAt_append).1 hc
  have h2 := (M.codeAt_append).1 h1.1
  rw [List.length_append, List.length_append] at hok
  have o1 := M.codeOK_append hok
  have o2 := M.codeOK_append o1.1
  exact ⟨ho, hpc, h2.2, o2.2⟩

theorem sub_disj {cb : BitVec 64} {W ws : List (BitVec 32)} {pos : Nat} {Rs : List Region}
    (hok : M.codeOK cb W.length) (hs : Sub W pos ws) (hd : ∀ r ∈ Rs, disjoint ⟨cb.toNat, 4 * W.length⟩ r) :
    ∀ r ∈ Rs, disjoint ⟨(next cb pos).toNat, 4 * ws.length⟩ r := by
  have hle := hs.le
  have e := M.pc_toNat hok (a := pos) (by omega)
  exact Machine.disj_sub hd (by rw [e]; omega) (by rw [e]; omega)

theorem lay (C : M.Ctx P bv wv off cb W R Wr lo hi) {N fp : Nat} (h1 : lo ≤ fp) (h2 : fp + 8 * (N + 1) ≤ hi) :
    M.Lay N fp R Wr :=
  ⟨C.ram, C.wram, C.rp, C.wp, C.rw,
    fun r hr => by
      have := C.sR r (List.mem_append_left _ hr); unfold disjoint at this ⊢; dsimp only at this ⊢; omega,
    fun r hr => by
      have := C.sR r (List.mem_append_right _ hr); unfold disjoint at this ⊢; dsimp only at this ⊢; omega,
    C.wal⟩

/-- the code is disjoint from every part of the stack area -/
theorem cd_in (C : M.Ctx P bv wv off cb W R Wr lo hi) {a l : Nat} (h1 : lo ≤ a) (h2 : a + l ≤ hi) :
    disjoint ⟨cb.toNat, 4 * W.length⟩ ⟨a, l⟩ := by
  have := C.cd _ memLast; unfold disjoint at this ⊢; dsimp only at this ⊢; omega

theorem cdAll (C : M.Ctx P bv wv off cb W R Wr lo hi) {N fp : Nat} (h1 : lo ≤ fp) (h2 : fp + 8 * (N + 1) ≤ hi) :
    ∀ r ∈ AllR N fp R Wr, disjoint ⟨cb.toNat, 4 * W.length⟩ r := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact C.cd r (List.mem_append_left _ hr)
  · obtain ⟨j, hj, rfl⟩ := mem_slots hr
    exact M.cd_in C (by omega) (by omega)

theorem codeAt_G (C : M.Ctx P bv wv off cb W R Wr lo hi) {s s' : M.S} (hc : M.codeAt s cb W)
    (o : Out (R ++ Wr ++ [⟨lo, hi - lo⟩]) (M.mem s) (M.mem s')) : M.codeAt s' cb W :=
  M.codeAt_out hc C.codeOK C.cd o

/-- the saved return address (cell 0) is not written by the body -/
theorem cell0 (C : M.Ctx P bv wv off cb W R Wr lo hi) {N fp : Nat} (h1 : lo ≤ fp) (h2 : fp + 8 * (N + 1) ≤ hi) :
    ∀ r ∈ Wrt N fp R Wr lo, disjoint ⟨fp, 8⟩ r := by
  intro r hr
  unfold Wrt AllR at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · have := C.sR r (List.mem_append_left _ hr); unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  · have := C.sR r (List.mem_append_right _ hr); unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  · obtain ⟨j, hj, rfl⟩ := mem_slots hr; unfold disjoint; dsimp only; omega
  · subst hr; unfold disjoint; dsimp only; omega

/-- the caller's slots are not written by a callee -/
theorem slot_low {N fp : Nat} (hL : M.Lay N fp R Wr) (h1 : lo ≤ fp) {j : Nat} (hj : j < N) :
    ∀ r ∈ Low R Wr lo fp, disjoint ⟨fp + 8 * (j + 1), 8⟩ r := by
  intro r hr
  unfold Low at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | hr) | hr
  · have := hL.fr r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  · have := hL.fw r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  · subst hr; unfold disjoint; dsimp only; omega

/-- the argument code: the values of `es` land in the 8-byte cells `fp - 8 (n - j), ..` below the frame -/
theorem args_ok (hok : M.codeOK cb W.length) {N fp : Nat} (hF : M.Frm N fp) (env : BEnv) (n : Nat)
    (hn : n ≤ M.maxSlots) (hlo : 8 * n ≤ fp) (hram : M.inRAM (fp - 8 * n) (8 * n))
    (hcd : disjoint ⟨cb.toNat, 4 * W.length⟩ ⟨fp - 8 * n, 8 * n⟩) :
    ∀ (es : List BExp) (j pos : Nat), j + es.length = n → (∀ e ∈ es, e.depth < 7 ∧ e.vlt (8 + N)) →
    Sub W pos (M.codeC (argsC n j es)) → ∀ {s : M.S}, M.codeAt s cb W → M.ok s → M.pcIs s (next cb pos) →
    M.EnvB N fp env s →
    M.runsTo s fun s' => M.Done s s' (next cb (pos + (M.codeC (argsC n j es)).length)) ∧
      (∀ i : Fin 8, M.get s' (avar i) = M.get s (avar i)) ∧
      Out [⟨fp - 8 * (n - j), 8 * (n - j)⟩] (M.mem s) (M.mem s') ∧
      ∀ i (hi : i < es.length), bytes (M.mem s') (fp - 8 * (n - (j + i))) 8 = (le8 (es[i].denote env)).map some
  | [], j, pos, _, _, _, s, _, ho, hpc, _ =>
    M.runsTo_of ⟨⟨ho, M.keep_refl s, hpc⟩, fun _ => rfl, Out.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | e :: es, j, pos, hj, hes, hsub, s, hc, ho, hpc, henv => by
    simp only [argsC, codeC_append, codeC_map, codeC_one, encY] at hsub ⊢
    obtain ⟨h12, h3⟩ := hsub.split
    obtain ⟨h1, h2⟩ := h12.split
    simp only [List.length_append] at h3 ⊢
    have hes0 := hes e List.mem_cons_self
    have hlen : j + (es.length + 1) = n := hj
    unfold Base.inRAM at hram
    refine M.runsTo_trans (M.genB_ok hF env e 0 (by omega) hes0.2 (M.at_sub hok hc h1 ho hpc) henv)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    have hfr₁ : M.fr s₁ = BitVec.ofNat 64 fp := by rw [M.keep_fr d₁.keep, henv.fr]
    have hfp := MachineF.Frm.fr M.toMachineF hF hfr₁
    have hc₁ := M.codeAt_mem m₁ hc
    refine M.runsTo_trans (M.law_stA (m := n - j) (v := rk 0) (rk_val (by omega)) (by omega) (by omega)
      (M.at_sub hok hc₁ h2 d₁.ok d₁.hpc) (by rw [hfp]; omega) (by rw [hfp]; unfold Base.inRAM; omega)
      (by rw [hfp]; exact hF.al)) fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [next_add] at d₂
    rw [hfp, v₁, m₁] at m₂
    have henv₂ : M.EnvB N fp env s₂ :=
      ⟨fun i => by rw [st₂, k₁ _ (.inr (avar_ge i)), henv.reg], by rw [M.keep_fr d₂.keep, hfr₁],
        fun j' hj' => by rw [m₂, bytes_wr_out (by rw [length_le8]; omega)]; exact henv.slot j' hj'⟩
    have ho₂ : Out [⟨fp - 8 * (n - j), 8 * (n - j)⟩] (M.mem s) (M.mem s₂) := by
      rw [m₂]; exact Out.wr (List.mem_singleton_self _) (by dsimp only; omega) (by rw [length_le8]; dsimp only; omega)
    have hc₂ : M.codeAt s₂ cb W := M.codeAt_out hc hok (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; unfold disjoint at hcd ⊢; dsimp only at hcd ⊢; omega) ho₂
    refine M.runsTo_mono (args_ok hok hF env n hn hlo hram hcd es (j + 1) _ (by omega)
      (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) (h3.cast (by omega)) hc₂ d₂.ok d₂.hpc henv₂)
      fun s₃ ⟨d₃, e₃, o₃, b₃⟩ => ⟨?_, ?_, ?_, ?_⟩
    · have d := Core.Done.trans _ d₁ (Core.Done.trans _ d₂ d₃)
      exact M.done_cast d (by omega)
    · intro i; rw [e₃, st₂, k₁ _ (.inr (avar_ge i))]
    · exact ho₂.trans (out1 o₃ (by omega) (by omega))
    · intro i hi
      cases i with
      | zero =>
        show bytes (M.mem s₃) (fp - 8 * (n - (j + 0))) 8 = (le8 (e.denote env)).map some
        rw [bytes_out o₃ (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; unfold disjoint; dsimp only; omega), m₂]
        have := bytes_wr_self (m := M.mem s) (a := fp - 8 * (n - j)) (l := le8 (e.denote env))
        rw [length_le8] at this; exact this
      | succ i =>
        have := b₃ i (by simp only [List.length_cons] at hi; omega)
        rw [show j + (i + 1) = j + 1 + i by omega]; exact this

/-- **Statements with calls: compiler correctness from the `MachineC` laws**, by induction on the source
run.  In a frame `(N, fp)` with at least `k` bytes of stack below it (`lo + k ≤ fp`), the code of `p` at
word `pos` runs to the word after it, with `σ'` in the globals, the frame slots and the blocks; it writes
only the blocks, its own slots and the stack below `fp` (so the caller's frames and the saved return
address are intact), and keeps everything else but the link register. -/
theorem execC_ok (C : M.Ctx P bv wv off cb W R Wr lo hi) :
    ∀ {k : Nat} {p : CStmt} {σ σ' : BState}, CExec P k p σ σ' → ∀ {N fp pos : Nat} {s : M.S},
    M.wfC P bv wv off N pos p → Sub W pos (M.codeC (M.compC P bv wv off pos p)) → M.Frm N fp →
    lo + k ≤ fp → fp + 8 * (N + 1) ≤ hi → M.codeAt s cb W → M.ok s → M.pcIs s (next cb pos) →
    M.RelB N fp bv wv R Wr σ s →
    M.runsTo s fun s' => M.ok s' ∧ M.keepC s s' ∧ M.pcIs s' (next cb (pos + M.lenC P bv wv p)) ∧
      Out (Wrt N fp R Wr lo) (M.mem s) (M.mem s') ∧ M.RelB N fp bv wv R Wr σ' s' := by
  intro k p σ σ' h
  induction h with
  | @base k p σ σ' hex =>
    intro N fp pos s hwf hsub hF hk hhi hc ho hpc hrel
    simp only [compC, codeC_map] at hsub
    have hL := M.lay C (N := N) (fp := fp) (by omega) hhi
    refine M.runsTo_mono (M.execB_ok hF bv wv (fun x hx => by have := C.bvlt x hx; omega)
      (fun x hx => by have := C.wvlt x hx; omega) hL hex hwf (M.at_sub C.codeOK hc hsub ho hpc)
      (M.sub_disj C.codeOK hsub (M.cdAll C (by omega) hhi)) hrel) fun s' ⟨d, o, r⟩ => ?_
    rw [next_add] at d
    exact ⟨d.ok, M.kC d, d.hpc, allR_wrt o, r⟩
  | @seq k p q σ σ₁ σ₂ _ _ ih₁ ih₂ =>
    intro N fp pos s hwf hsub hF hk hhi hc ho hpc hrel
    simp only [compC, codeC_append, wfC] at hsub hwf
    obtain ⟨h1, h2⟩ := hsub.split
    rw [len_compC] at h2
    refine M.runsTo_trans (ih₁ hwf.1 h1 hF hk hhi hc ho hpc hrel) fun s₁ ⟨ok₁, kc₁, pc₁, o₁, r₁⟩ => ?_
    have hc₁ := M.codeAt_G C hc (wrt_G o₁ (by omega) hhi)
    refine M.runsTo_mono (ih₂ hwf.2 h2 hF hk hhi hc₁ ok₁ pc₁ r₁) fun s₂ ⟨ok₂, kc₂, pc₂, o₂, r₂⟩ =>
      ⟨ok₂, M.keepC_trans kc₁ kc₂, M.pcIs_cast pc₂ (by simp only [lenC]; omega), o₁.trans o₂, r₂⟩
  | @iteT k c p q σ σ' hc0 _ ih =>
    intro N fp pos s hwf hsub hF hk hhi hc ho hpc hrel
    simp only [compC, codeC_append, codeC_map, codeC_one, codeC_two, encY, MachineF.encF, wfC] at hsub hwf
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6⟩ := hwf
    obtain ⟨h1234, h5⟩ := hsub.split
    obtain ⟨h123, h4⟩ := h1234.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    obtain ⟨h4a, h4b⟩ := h4.split
    simp only [List.length_append, M.len_bz, len_compC, lenLi_eq] at h2 h3 h4a h4b h5
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hw2 (M.at_sub C.codeOK hc h1 ho hpc) hrel.env)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    have hc₁ := M.codeAt_mem m₁ hc
    have hrel₁ := RelB.same M.toMachineF hrel m₁ d₁.keep fun i => k₁ _ (.inr (avar_ge i))
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hw3 (M.at_sub C.codeOK hc₁ h2 d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_neg hc0, M.len_bz, next_add] at d₂
    have hc₂ := M.codeAt_mem m₂ hc₁
    have hrel₂ := RelB.same M.toMachineF hrel₁ m₂ d₂.keep fun i => st₂ _
    refine M.runsTo_trans (ih hw5 (h3.cast (by omega)) hF hk hhi hc₂ d₂.ok (M.pcIs_cast d₂.hpc (by omega)) hrel₂)
      fun s₃ ⟨ok₃, kc₃, pc₃, o₃, r₃⟩ => ?_
    have hc₃ := M.codeAt_G C hc₂ (wrt_G o₃ (by omega) hhi)
    refine M.runsTo_trans (M.law_li (d := rk 0) (c := 0) (by rw [rk_val (by omega)]; omega)
      (M.at_sub C.codeOK hc₃ h4a ok₃ (M.pcIs_cast pc₃ (by omega)))) fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
    rw [next_add] at d₄
    refine M.runsTo_mono (M.law_bz (c := rk 0) (rk_val (by omega)) hw4
      (M.at_sub C.codeOK (M.codeAt_mem m₄ hc₃) h4b d₄.ok (M.pcIs_cast d₄.hpc (by rw [lenLi_eq]))))
      fun s₅ ⟨d₅, st₅, m₅⟩ => ?_
    rw [Core.Set1.same _ st₄, ite_pos rfl, next_add] at d₅
    refine ⟨d₅.ok, ?_, M.pcIs_cast d₅.hpc (by simp only [lenC]; omega),
      (Out.of_eq (m₂.trans m₁)).trans (o₃.trans (Out.of_eq (m₅.trans m₄))), ?_⟩
    · exact M.keepC_trans (M.kC d₁) (M.keepC_trans (M.kC d₂) (M.keepC_trans kc₃ (M.keepC_trans (M.kC d₄) (M.kC d₅))))
    · exact RelB.same M.toMachineF r₃ (m₅.trans m₄) (M.keep_trans d₄.keep d₅.keep) fun i => by
        rw [st₅, Core.Set1.other _ st₄ (avar_ne_rk0 i)]
  | @iteF k c p q σ σ' hc0 _ ih =>
    intro N fp pos s hwf hsub hF hk hhi hc ho hpc hrel
    simp only [compC, codeC_append, codeC_map, codeC_one, codeC_two, encY, MachineF.encF, wfC] at hsub hwf
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6⟩ := hwf
    obtain ⟨h1234, h5⟩ := hsub.split
    obtain ⟨h123, h4⟩ := h1234.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    simp only [List.length_append, M.len_bz, len_compC, lenLi_eq] at h2 h5
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hw2 (M.at_sub C.codeOK hc h1 ho hpc) hrel.env)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    have hc₁ := M.codeAt_mem m₁ hc
    have hrel₁ := RelB.same M.toMachineF hrel m₁ d₁.keep fun i => k₁ _ (.inr (avar_ge i))
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hw3 (M.at_sub C.codeOK hc₁ h2 d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_pos hc0, next_add] at d₂
    have hc₂ := M.codeAt_mem m₂ hc₁
    have hrel₂ := RelB.same M.toMachineF hrel₁ m₂ d₂.keep fun i => st₂ _
    refine M.runsTo_mono (ih hw6 (h5.cast (by omega)) hF hk hhi hc₂ d₂.ok (M.pcIs_cast d₂.hpc (by omega)) hrel₂)
      fun s₃ ⟨ok₃, kc₃, pc₃, o₃, r₃⟩ => ⟨ok₃, M.keepC_trans (M.kC d₁) (M.keepC_trans (M.kC d₂) kc₃),
        M.pcIs_cast pc₃ (by simp only [lenC]; omega), (Out.of_eq (m₂.trans m₁)).trans o₃, r₃⟩
  | @loopF k c b σ hc0 =>
    intro N fp pos s hwf hsub hF hk hhi hc ho hpc hrel
    simp only [compC, codeC_append, codeC_map, codeC_one, encY, MachineF.encF, wfC] at hsub hwf
    obtain ⟨hw1, hw2, hw3, hw4, hw5⟩ := hwf
    obtain ⟨h123, h4⟩ := hsub.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hw2 (M.at_sub C.codeOK hc h1 ho hpc) hrel.env)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    have hc₁ := M.codeAt_mem m₁ hc
    have hrel₁ := RelB.same M.toMachineF hrel m₁ d₁.keep fun i => k₁ _ (.inr (avar_ge i))
    refine M.runsTo_mono (M.law_bz (rk_val (by omega)) hw3 (M.at_sub C.codeOK hc₁ h2 d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_pos hc0, next_add] at d₂
    exact ⟨d₂.ok, M.keepC_trans (M.kC d₁) (M.kC d₂), M.pcIs_cast d₂.hpc (by simp only [lenC]; omega),
      Out.of_eq (m₂.trans m₁), RelB.same M.toMachineF hrel₁ m₂ d₂.keep fun i => st₂ _⟩
  | @loopT k c b σ σ₁ σ₂ hc0 _ _ ih₁ ih₂ =>
    intro N fp pos s hwf hsub hF hk hhi hc ho hpc hrel
    have hwf0 := hwf
    have hsub0 := hsub
    simp only [compC, codeC_append, codeC_map, codeC_one, encY, MachineF.encF, wfC] at hsub hwf
    obtain ⟨hw1, hw2, hw3, hw4, hw5⟩ := hwf
    obtain ⟨h123, h4⟩ := hsub.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    simp only [List.length_append, M.len_bz, len_compC] at h2 h3 h4
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hw2 (M.at_sub C.codeOK hc h1 ho hpc) hrel.env)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    have hc₁ := M.codeAt_mem m₁ hc
    have hrel₁ := RelB.same M.toMachineF hrel m₁ d₁.keep fun i => k₁ _ (.inr (avar_ge i))
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hw3 (M.at_sub C.codeOK hc₁ h2 d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_neg hc0, M.len_bz, next_add] at d₂
    have hc₂ := M.codeAt_mem m₂ hc₁
    have hrel₂ := RelB.same M.toMachineF hrel₁ m₂ d₂.keep fun i => st₂ _
    refine M.runsTo_trans (ih₁ hw5 (h3.cast (by omega)) hF hk hhi hc₂ d₂.ok (M.pcIs_cast d₂.hpc (by omega)) hrel₂)
      fun s₃ ⟨ok₃, kc₃, pc₃, o₃, r₃⟩ => ?_
    have hc₃ := M.codeAt_G C hc₂ (wrt_G o₃ (by omega) hhi)
    refine M.runsTo_trans (M.law_jmp hw4 (M.at_sub C.codeOK hc₃ h4 ok₃ (M.pcIs_cast pc₃ (by omega))))
      fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
    have pc₄ : M.pcIs s₄ (next cb pos) := M.pcIs_jmp d₄.hpc (by omega)
    refine M.runsTo_mono (ih₂ hwf0 hsub0 hF hk hhi (M.codeAt_mem m₄ hc₃) d₄.ok pc₄
      (RelB.same M.toMachineF r₃ m₄ d₄.keep fun i => st₄ _)) fun s₅ ⟨ok₅, kc₅, pc₅, o₅, r₅⟩ =>
      ⟨ok₅, M.keepC_trans (M.kC d₁) (M.keepC_trans (M.kC d₂) (M.keepC_trans kc₃ (M.keepC_trans (M.kC d₄) kc₅))),
        pc₅, (Out.of_eq (m₂.trans m₁)).trans (o₃.trans ((Out.of_eq m₄).trans o₅)), r₅⟩
  | @call k k' res f args σ σ₁ hf ha hk' _ ih =>
    intro N fp pos s hwf hsub hF hk hhi hc ho hpc hrel
    have enl := nlOf_eq hf
    simp only [compC, lenArgs, codeC_append, codeC_map, codeC_one, encY, wfC, enl] at hsub hwf
    obtain ⟨-, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hwf
    obtain ⟨hwN, hwr1, hwr2, hwb⟩ := C.wf f hf
    obtain ⟨h12, h3⟩ := hsub.split
    obtain ⟨h1, h2⟩ := h12.split
    simp only [List.length_append, M.len_call] at h3
    have hfrm : P[f].frame = 8 * (P[f].nlocals + 1) := rfl
    rw [hfrm] at hk'
    have hL := M.lay C (N := N) (fp := fp) (by omega) hhi
    have hstk := C.stk
    unfold Base.inRAM at hstk
    have hlohi := C.lohi
    have hal := hF.al
    have hfp := MachineF.Frm.fr M.toMachineF hF hrel.env.fr
    have hpad : (padArgs P[f].nlocals args).length = P[f].nlocals := padArgs_length hw2
    -- 1. the arguments
    refine M.runsTo_trans (M.args_ok C.codeOK hF σ.env P[f].nlocals hwN (by omega) (by unfold Base.inRAM; omega)
      (M.cd_in C (by omega) (by omega)) (padArgs P[f].nlocals args) 0 pos (by omega) (pad_wf hw3) h1 hc ho hpc
      hrel.env) fun s₁ ⟨d₁, e₁, o₁, b₁⟩ => ?_
    rw [Nat.sub_zero] at o₁
    have hc₁ : M.codeAt s₁ cb W := M.codeAt_out hc C.codeOK (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact M.cd_in C (by omega) (by omega)) o₁
    -- 2. the call
    refine M.runsTo_trans (M.law_call hw7 (M.at_sub C.codeOK hc₁ h2 d₁.ok d₁.hpc))
      fun s₂ ⟨ok₂, kc₂, pc₂, ra₂, fr₂, st₂, m₂⟩ => ?_
    rw [next_call] at pc₂
    have hfr₂ : (M.fr s₂).toNat = fp := by rw [fr₂, M.keep_fr d₁.keep]; exact hfp
    -- 3. the callee's prologue
    have hfn := C.fns f hf
    simp only [fnC, codeC_append, codeC_map, codeC_one, codeC_two, encY, MachineF.encF] at hfn
    obtain ⟨g123, g4⟩ := hfn.split
    obtain ⟨g12, g3⟩ := g123.split
    obtain ⟨g1, g2⟩ := g12.split
    obtain ⟨g4a, g4b⟩ := g4.split
    simp only [List.length_append, len_compC] at g3 g4a g4b
    refine M.runsTo_trans (M.law_enterC hwN (M.at_sub C.codeOK (M.codeAt_mem m₂ hc₁) g1 ok₂ pc₂)
      (by rw [hfr₂]; omega) (by rw [hfr₂]; unfold Base.inRAM; omega) (by rw [hfr₂]; exact hal))
      fun s₃ ⟨ok₃, kc₃, pc₃, fr₃, st₃, m₃⟩ => ?_
    rw [hfr₂] at fr₃ m₃
    rw [next_add] at pc₃
    have hF' : M.Frm P[f].nlocals (fp - 8 * (P[f].nlocals + 1)) :=
      ⟨by unfold Base.inRAM; omega, by omega, hwN⟩
    have o₃ : Out [⟨lo, fp - lo⟩] (M.mem s) (M.mem s₃) := by
      refine (out1 o₁ (by omega) (by omega)).trans ?_
      rw [m₃, m₂]
      exact Out.wr (List.mem_singleton_self _) (by dsimp only; omega) (by rw [length_le8]; dsimp only; omega)
    have hrel₃ : M.RelB P[f].nlocals (fp - 8 * (P[f].nlocals + 1)) bv wv R Wr
        ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩ s₃ := by
      have byR : ∀ r ∈ R ++ Wr, bytes (M.mem s₃) r.base r.len = bytes (M.mem s) r.base r.len := fun r hr =>
        bytes_out o₃ fun r' hr' => by
          rw [List.mem_singleton] at hr'; subst hr'
          have := C.sR r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega
      refine ⟨⟨fun i => ?_, fr₃, fun j hj => ?_⟩, hrel.hlen, hrel.bvlen, fun b hb => ?_, hrel.blen,
        fun b hb => ?_, hrel.whlen, hrel.wvlen, fun b hb => ?_, hrel.wblen, fun b hb => ?_⟩
      · rw [st₃, st₂, e₁, hrel.env.reg]
        show _ = if i.val < 8 then _ else _
        rw [ite_pos i.2]
      · have hb := b₁ j (by rw [hpad]; exact hj)
        rw [pad_denote] at hb
        rw [m₃, bytes_wr_out (by rw [length_le8]; omega), m₂,
          show fp - 8 * (P[f].nlocals + 1) + 8 * (j + 1) = fp - 8 * (P[f].nlocals - (0 + j)) by omega, hb]
        show _ = (le8 (if 8 + j < 8 then _ else (args.map _).getD (8 + j - 8) 0)).map some
        rw [ite_neg (by omega), Nat.add_sub_cancel_left]
      · show (if bv.getD b 0 < 8 then σ.env (bv.getD b 0) else _) = _
        rw [ite_pos (C.bvlt _ (getD_memN (hrel.bvlen ▸ hb)))]; exact hrel.base b hb
      · rw [byR _ (List.mem_append_left _ (List.getElem_mem hb))]; exact hrel.rbytes b hb
      · show (if wv.getD b 0 < 8 then σ.env (wv.getD b 0) else _) = _
        rw [ite_pos (C.wvlt _ (getD_memN (hrel.wvlen ▸ hb)))]; exact hrel.wbase b hb
      · rw [byR _ (List.mem_append_right _ (List.getElem_mem hb))]; exact hrel.wbyts b hb
    -- 4. the body
    have hc₃ : M.codeAt s₃ cb W := M.codeAt_out hc C.codeOK (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact M.cd_in C (Nat.le_refl _) (by omega)) o₃
    refine M.runsTo_trans (ih hwb g2 hF' (by omega) (by omega) hc₃ ok₃ pc₃ hrel₃)
      fun s₄ ⟨ok₄, kc₄, pc₄, o₄, r₄⟩ => ?_
    have hc₄ := M.codeAt_G C hc₃ (wrt_G o₄ (by omega) (by omega))
    -- 5. the result
    refine M.runsTo_trans (M.genB_ok hF' σ₁.env P[f].ret 0 (by omega) hwr2
      (M.at_sub C.codeOK hc₄ g3 ok₄ (M.pcIs_cast pc₄ (by omega))) r₄.env) fun s₅ ⟨d₅, m₅, v₅, k₅⟩ => ?_
    rw [next_add] at d₅
    -- 6. the epilogue
    have hfr₅ : (M.fr s₅).toNat = fp - 8 * (P[f].nlocals + 1) :=
      MachineF.Frm.fr M.toMachineF hF' (by rw [M.keep_fr d₅.keep, r₄.env.fr])
    have hsv : bytes (M.mem s₅) (fp - 8 * (P[f].nlocals + 1)) 8 = (le8 (M.ra s₂)).map some := by
      rw [m₅, bytes_out o₄ (M.cell0 C (by omega) (by omega)), m₃]
      have := bytes_wr_self (m := M.mem s₂) (a := fp - 8 * (P[f].nlocals + 1)) (l := le8 (M.ra s₂))
      rw [length_le8] at this; exact this
    refine M.runsTo_trans (M.law_leaveC (w := M.ra s₂) hwN
      (M.at_sub C.codeOK (M.codeAt_mem m₅ hc₄) g4a d₅.ok (M.pcIs_cast d₅.hpc (by omega)))
      (by rw [hfr₅]; exact hF'.ram) (by rw [hfr₅]; exact hF'.al) (by rw [hfr₅]; exact hsv))
      fun s₆ ⟨ok₆, kc₆, pc₆, ra₆, fr₆, st₆, m₆⟩ => ?_
    rw [next_add] at pc₆
    rw [hfr₅, Nat.sub_add_cancel (by omega)] at fr₆
    have hret : M.retOK (M.ra s₆) := by
      rw [ra₆, ra₂, next_add]
      apply M.retOK_al
      rw [M.pc_toNat C.codeOK (by have := h2.le; rw [M.len_call] at this; omega)]
      have := C.codeOK.1; omega
    refine M.runsTo_trans (M.law_ret hret (M.at_sub C.codeOK (M.codeAt_mem m₆ (M.codeAt_mem m₅ hc₄)) g4b ok₆
      (M.pcIs_cast pc₆ (by omega)))) fun s₇ ⟨d₇, st₇, m₇⟩ => ?_
    rw [ra₆, ra₂, next_add] at d₇
    -- 7. back in the caller
    have m₇₄ : M.mem s₇ = M.mem s₄ := by rw [m₇, m₆, m₅]
    have o₇ : Out (Low R Wr lo fp) (M.mem s) (M.mem s₇) := by
      rw [m₇₄]; exact (out_low o₃).trans (wrt_low o₄ (by omega) (by omega))
    have hrel₇ : M.RelB N fp bv wv R Wr ⟨retEnv σ.env σ₁.env, σ₁.heap, σ₁.wheap⟩ s₇ := by
      refine ⟨⟨fun i => ?_, ?_, fun j hj => ?_⟩, r₄.hlen, r₄.bvlen, fun b hb => ?_, r₄.blen,
        fun b hb => by rw [m₇₄]; exact r₄.rbytes b hb, r₄.whlen, r₄.wvlen, fun b hb => ?_, r₄.wblen,
        fun b hb => by rw [m₇₄]; exact r₄.wbyts b hb⟩
      · rw [st₇, st₆, k₅ _ (.inr (avar_ge i)), r₄.env.reg]
        show _ = if i.val < 8 then _ else _
        rw [ite_pos i.2]
      · rw [M.keep_fr d₇.keep, fr₆]
      · rw [bytes_out o₇ (M.slot_low hL (by omega) hj), hrel.env.slot j hj]
        show _ = (le8 (if 8 + j < 8 then _ else _)).map some
        rw [ite_neg (by omega)]
      · show (if bv.getD b 0 < 8 then σ₁.env (bv.getD b 0) else _) = _
        rw [ite_pos (C.bvlt _ (getD_memN (r₄.bvlen ▸ hb)))]; exact r₄.base b hb
      · show (if wv.getD b 0 < 8 then σ₁.env (wv.getD b 0) else _) = _
        rw [ite_pos (C.wvlt _ (getD_memN (r₄.wvlen ▸ hb)))]; exact r₄.wbase b hb
    -- 8. the result variable
    have hx : M.get s₇ (rk 0) = P[f].ret.denote σ₁.env := by rw [st₇, st₆, v₅]
    have hc₇ := M.codeAt_G C hc (low_G o₇ (by omega) (by omega))
    refine M.runsTo_mono (M.setV_ok hF hL hw4 hw5 hw6
      (M.at_sub C.codeOK hc₇ h3 d₇.ok (M.pcIs_cast d₇.hpc (by omega))) hx hrel₇) fun s₈ ⟨d₈, o₈, r₈⟩ => ?_
    rw [next_add] at d₈
    refine ⟨d₈.ok, ?_, M.pcIs_cast d₈.hpc (by simp only [lenC, lenArgs, enl]; omega),
      (low_wrt o₇).trans (allR_wrt o₈), r₈⟩
    exact M.keepC_trans (M.kC d₁) (M.keepC_trans kc₂ (M.keepC_trans kc₃ (M.keepC_trans kc₄
      (M.keepC_trans (M.kC d₅) (M.keepC_trans kc₆ (M.keepC_trans (M.kC d₇) (M.kC d₈)))))))

end MachineC
end Proven.Mach
