/- `compileX1`: the `XPipe` compiler in the `Implements1` convention (working space in the WORK block), on the
optimised back end (`compileBFO`, 8 slots, blocks input / work / output with bases `a0`, `a2`, `a3`).

    theorem compileX1_ok (h : compileX1 p = .ok code) :
        Implements1Raw code (XPipe.denote p) (XPipe.space1 p) (retLen := true)

`XPipe.space1 p n = 2 (n + XPipe.extra p) + 79`: the relocated output buffer and scratch block (`n + E` bytes
each, `Compiler/Front/PipeI.lean`), the 72-byte frame below `sp` (8 slots + the saved `gp`), 7 bytes of
alignment.  The result is written to exactly the first `|result|` output bytes; the output block needs only
`|result|` bytes, every other output byte is unchanged; `a1` = `|result|`. -/
import Nano.Base.Compiler.Front.PipeI
import Nano.Base.Riscv.Back.Implements1Opt
import Spec.Implements1

set_option linter.unusedVariables false

namespace Proven
open Mach.Riscv (bytesAt_take' abi_of_keep)

/-- from a run of a `BStmt` program on blocks `[input, work, output]` to `Implements1Raw` -/
theorem implements1_of_execB (N : Nat) (hN : N ≤ 16) {prog : BStmt} (hwf : prog.wf N [0, 2, 3])
    (wl space : Nat → Nat) (hsp : ∀ n, wl n + 8 * (N + 1) + 7 ≤ space n) {f : List UInt8 → List UInt8}
    (retLen : Bool)
    (hex : ∀ (xs : List UInt8) (wk out : List (BitVec 8)) (env : BEnv), env 1 = .ofNat 64 xs.length →
      xs.length ≤ 2 ^ 20 → wk.length = wl xs.length → (f xs).length ≤ out.length → out.length < 2 ^ 32 →
      ∃ σ' wk', BExec prog ⟨env, [tbs xs, wk, out]⟩ σ' ∧
        σ'.heap = [tbs xs, wk', tbs (f xs) ++ out.drop (f xs).length] ∧
        (retLen = true → σ'.env 1 = .ofNat 64 (f xs).length)) :
    Implements1Raw (compileBFO N [0, 2, 3] prog) f space (retLen := retLen) := by
  intro a s entry ra input output work
  dsimp only [encRaw]
  intro hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx hil hol hws hwal hram hdis hmapO hmapW
  have hin : ∀ r ∈ [input, output, work, (⟨entry.toNat, 4 * (compileBFO N [0, 2, 3] prog).length⟩ : Region)],
    r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rw' rc
  unfold disjoint at d12 d13 d14 d23 d24 d34
  dsimp only at d12 d13 d14 d23 d24 d34 ri ro rw' rc
  have hxl : (tbs a).length = a.length := by simp
  have hil' : input.len = a.length := hil
  have hol' : (f a).length ≤ output.len := by simpa using hol
  have hws' : space a.length ≤ work.len := hws
  have hsp' := hsp a.length
  -- the frame
  have hsp2 : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = work.base + work.len := by rw [hsp2]; exact toNat_ofNat' (by omega)
  have hfb : frameBase N (getX s 2) = (work.base + work.len) / 8 * 8 - 8 * (N + 1) := by
    unfold frameBase; rw [hspn]
  have hfb1 : work.base + wl a.length ≤ frameBase N (getX s 2) := by rw [hfb]; omega
  have hfb2 : frameBase N (getX s 2) + 8 * (N + 1) ≤ work.base + work.len := by rw [hfb]; omega
  have hf : FrOK N (frameBase N (getX s 2)) :=
    ⟨by rw [hfb]; omega, by omega, by omega, by unfold NS; omega⟩
  -- the initial heap
  obtain ⟨out0, hout0l, ho⟩ : ∃ out0 : List (BitVec 8), out0.length = output.len ∧
      bytesAt s output.base output.len = out0.map some :=
    ⟨_, by simp [bytesAt], bytesAt_hosted fun i hi => hmapO i hi⟩
  obtain ⟨wk0, hwl, hwb⟩ : ∃ wk0 : List (BitVec 8), wk0.length = wl a.length ∧
      bytesAt s work.base (wl a.length) = wk0.map some :=
    ⟨_, by simp [bytesAt], bytesAt_hosted fun i hi => hmapW i (by omega)⟩
  obtain ⟨σ', wk', hexec, hh, hrl⟩ := hex a wk0 out0 (envOf s)
    (by simp [envOf]; exact getX_of (h.x11.symm.trans h11) rfl) hmax hwl (by omega) (by omega)
  let R : List Region := [⟨input.base, a.length⟩, ⟨work.base, wl a.length⟩, ⟨output.base, output.len⟩]
  have hR : RegOK R := by
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> (unfold Region.inRAM; dsimp only; omega)
    · simp only [R, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; omega
  have hok : codeOK entry (compileBFO N [0, 2, 3] prog).length := ⟨hal, rc.1, rc.2⟩
  have hfd : ∀ r ∈ R, disjoint ⟨frameBase N (getX s 2), 8 * (N + 1)⟩ r := by
    intro r hr
    simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hcd : ∀ r ∈ (⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Region) :: R,
      disjoint ⟨entry.toNat, 4 * (compileBFO N [0, 2, 3] prog).length⟩ r := by
    intro r hr
    simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hheap : HeapRel [0, 2, 3] R ⟨envOf s, [tbs a, wk0, out0]⟩ s :=
    ⟨rfl, rfl, fun b hb => by
        obtain _ | _ | _ | b := b
        · simp [envOf]; exact getX_of (h.x10.symm.trans h10) rfl
        · simp [envOf]; exact getX_of (h.x12.symm.trans h12) rfl
        · simp [envOf]; exact getX_of (h.x13.symm.trans h13) rfl
        · simp [R] at hb; omega,
      fun b hb => by
        obtain _ | _ | _ | b := b
        · simp [R]
        · simpa [R] using hwl
        · simpa [R] using hout0l
        · simp [R] at hb; omega,
      fun b hb => by
        obtain _ | _ | _ | b := b
        · simpa [R, List.map_map, Function.comp_def] using hx
        · simpa [R] using hwb
        · simpa [R] using ho
        · simp [R] at hb; omega⟩
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (compileBFO_okK N [0, 2, 3] (by intro x hx; simp at hx; omega) hwf hR hexec h hpc
    (codeAt_of_codeBytes hok hcode) hok hf hfd hcd (fun i => by simp [envOf])
    (fun j hj => by simp only [envOf]; rw [dif_neg (by omega)]) hheap (by rw [hra']; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  have e0 := p3.bytes 0 (by simp [R]); have e2 := p3.bytes 2 (by simp [R])
  simp only [hh] at e0 e2
  have e0' : bytesAt s' input.base a.length = (tbs a).map some := by simpa [R] using e0
  have e2' : bytesAt s' output.base output.len = (tbs (f a) ++ out0.drop (f a).length).map some := by
    simpa [R] using e2
  refine ⟨by rw [p1, hra'], ?_, ?_, abi_of_keep h p5 p6, p5, fun hr => ?_⟩
  · rw [← bytesAt_take' s' output.base hol', e2', ← List.map_take,
      List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
    simp [List.map_map, tbs]
  · intro q hq
    have a2 := hq ⟨output.base, (f a).length⟩ (by simp); have a3 := hq work (by simp)
    dsimp only at a2
    by_cases hqi : input.base ≤ q ∧ q < input.base + input.len
    · have e0x : bytesAt s' input.base a.length = bytesAt s input.base a.length := by
        rw [e0', hx, List.map_map]; rfl
      have := congrArg (·[q - input.base]?) e0x
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - input.base < a.length by omega),
        Option.map_some, Option.some.injEq] at this
      rwa [Nat.add_sub_cancel' hqi.1] at this
    by_cases hqo : output.base ≤ q ∧ q < output.base + output.len
    · have e1x : (bytesAt s' output.base output.len)[q - output.base]? =
          (bytesAt s output.base output.len)[q - output.base]? := by
        rw [e2', ho, List.getElem?_map, List.getElem?_map, List.getElem?_append_right (by simp; omega),
          List.getElem?_drop]
        simp only [tbs, List.length_map]
        rw [show (f a).length + (q - output.base - (f a).length) = q - output.base by omega]
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - output.base < output.len by omega),
        Option.map_some, Option.some.injEq] at e1x
      rwa [Nat.add_sub_cancel' hqo.1] at e1x
    · apply p4 q
      intro r hr
      simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only
      · show q < frameBase N (getX s 2) ∨ frameBase N (getX s 2) + _ ≤ q; omega
      · omega
      · omega
      · omega
  · have := p2 ⟨1, by decide⟩
    rw [show getX s' (A8 ⟨1, by decide⟩) = getX s' 11 from rfl, hrl hr] at this
    rw [p5.x11, this]

/-! ## The compiler -/

def XPipe.space1 (p : XPipe) (n : Nat) : Nat := 2 * (n + XPipe.extra p) + 79

/-- **The `XPipe` compiler in the `Implements1` convention** (all pipes, sorts included) -/
def compileX1 (p : XPipe) : Except String (List (BitVec 32)) :=
  match XPipe.chkErr p with
  | some m => .error m
  | none =>
    if okR (XPipe.progB p) && decide (XPipe.extra p < 2 ^ 20) then
      match wfErrB 8 [0, 2, 3] (progI p) with
      | some m => .error m
      | none => .ok (compileBFO 8 [0, 2, 3] (progI p))
    else .error "compileX1: the program reads a2/a3/v15, or the appended constants are too long"

theorem compileX1_inv {p : XPipe} {code : List (BitVec 32)} (h : compileX1 p = .ok code) :
    (∀ st ∈ p, st.chk = none) ∧ okR (XPipe.progB p) = true ∧ XPipe.extra p < 2 ^ 20 ∧
      (progI p).wf 8 [0, 2, 3] ∧ code = compileBFO 8 [0, 2, 3] (progI p) := by
  unfold compileX1 at h
  cases hc : XPipe.chkErr p with
  | some m => simp [hc] at h
  | none =>
    simp only [hc] at h
    by_cases hk : (okR (XPipe.progB p) && decide (XPipe.extra p < 2 ^ 20)) = true
    · rw [if_pos hk] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      cases hw : wfErrB 8 [0, 2, 3] (progI p) with
      | some m => simp [hw] at h
      | none =>
        simp only [hw, Except.ok.injEq] at h
        exact ⟨XPipe.chkErr_none hc, hk.1, hk.2, (wfErrB_iff _ _ _).1 hw, h.symm⟩
    · rw [if_neg hk] at h; exact nomatch h

/-- **`compileX1` is correct**: the code implements the pipe's function in `Implements1` form, work space
`XPipe.space1 p n = 2 (n + XPipe.extra p) + 79`, result length in `a1` -/
theorem compileX1_ok {p : XPipe} {code : List (BitVec 32)} (h : compileX1 p = .ok code) :
    Implements1Raw code (XPipe.denote p) (XPipe.space1 p) (retLen := true) := by
  obtain ⟨hc, hR, hE, hwf, rfl⟩ := compileX1_inv h
  refine implements1_of_execB 8 (by omega) hwf (fun n => 2 * (n + XPipe.extra p)) (XPipe.space1 p)
    (fun n => by simp only [XPipe.space1]; omega) true ?_
  intro xs wk out env h1 hx hw ho hol
  obtain ⟨σ', wk', x, hh, h1'⟩ := progI_exec p hc hR hE xs wk out env h1 hx hw ho hol
  exact ⟨σ', wk', x, hh, fun _ => h1'⟩

/-- the encoded form: `f` with a result encoding `enc` that the pipe computes -/
theorem Implements1Raw.enc {β : Type} {encB : β → List UInt8} {f : List UInt8 → β} {g : List UInt8 → List UInt8}
    {code : List (BitVec 32)} {space : Nat → Nat} {maxLen : Nat} {retLen : Bool}
    (hg : ∀ xs, encB (f xs) = g xs) (h : Implements1Raw code g space maxLen retLen) :
    Implements1With encRaw encB code f space maxLen retLen := by
  have : (fun xs => encB (f xs)) = g := funext hg
  intro a s entry ra input output work
  have := h a s entry ra input output work
  simp only [encRaw, hg] at this ⊢
  exact this

end Proven
