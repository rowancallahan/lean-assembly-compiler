/- `Implements1` (`Spec/Implements1.lean`) for the list front end: the source-level form of
`implements_of_exec` (`Compiler/Front/PipeMachine.lean`) gives `Implements1Raw … (fun _ => 0)` whenever the
program needs no more output space than its result (pipe code uses the OUTPUT block as its work area, so a
pipe with `space n > |f x|` does not fit `Implements1` with the same code; `a2`, the work base, is only a
temporary for it).  `compileP_implements1`: every accepted `compileP` pipe with `Pipe.space ≤ Pipe.len`. -/
import Compiler.Front.PipeMachine
import Spec.Implements1
import Riscv.Back.Keep

set_option linter.unusedVariables false

namespace Proven

theorem implements1_of_exec {prog : AStmt} (hwf : prog.wf [0, 3]) {f : List UInt8 → List UInt8} {space : Nat → Nat}
    (hsl : ∀ xs : List UInt8, space xs.length ≤ (f xs).length)
    (hex : ∀ (xs : List UInt8) (out : List (BitVec 8)) (env : AEnv), env 1 = .ofNat 64 xs.length →
      xs.length < 2 ^ 32 → space xs.length ≤ out.length → out.length < 2 ^ 32 →
      ∃ σ' out', AExec prog ⟨env, [tbs xs, out]⟩ σ' ∧ σ'.heap = [tbs xs, out'] ∧ out'.length = out.length ∧
        out'.take (f xs).length = tbs (f xs)) :
    Implements1Raw (compileAF [0, 3] prog) f (fun _ => 0) := by
  intro x s entry ra input output work
  dsimp only [encRaw]
  intro hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx hil hol hws hwal hram hdis hmapO hmapW
  have hin : ∀ r ∈ [input, output, work, (⟨entry.toNat, 4 * (compileAF [0, 3] prog).length⟩ : Region)],
    r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rc
  unfold disjoint at d12 d14 d24
  dsimp only at d12 d14 d24 ri ro rc
  obtain ⟨L, hLe⟩ : ∃ L, L = space x.length := ⟨_, rfl⟩
  have hLf : L ≤ (f x).length := hLe ▸ hsl x
  have hmap : ∀ i < L, (s.mem[output.base + i]?).isSome := fun i hi => hmapO i (by omega)
  have hil' : input.len = x.length := hil
  have hol' : L ≤ output.len := by have : (f x).length ≤ output.len := hol; omega
  have hxl : (tbs x).length = x.length := by simp
  have hout0 : ((bytesAt s output.base L).map (·.getD 0)).length = L := by simp [bytesAt]
  have ho : bytesAt s output.base L = ((bytesAt s output.base L).map (·.getD 0)).map some := by
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [bytesAt, List.getElem_map, List.getElem_range, Function.comp]
    have := hmap i (by simpa [bytesAt] using h1)
    cases e : s.mem[output.base + i]? with
    | none => rw [e] at this; simp at this
    | some b => rfl
  generalize (bytesAt s output.base L).map (·.getD 0) = out0 at hout0 ho
  have hR : RegOK [⟨input.base, x.length⟩, ⟨output.base, L⟩] := by
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Region.inRAM; dsimp only; omega)
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; omega
  have hok : codeOK entry (compileAF [0, 3] prog).length := ⟨hal, rc.1, rc.2⟩
  have hcd : ∀ r ∈ [(⟨input.base, x.length⟩ : Region), ⟨output.base, L⟩],
      disjoint ⟨entry.toNat, 4 * (compileAF [0, 3] prog).length⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  obtain ⟨σ', out', hexec, hh, hlen, htk⟩ := hex x out0 (fun i => getX s (A8 i))
    (getX_of (h.x11.symm.trans h11) rfl) (by omega) (by rw [← hLe, hout0]; exact Nat.le_refl _) (by omega)
  have hrel : Rel [0, 3] [⟨input.base, x.length⟩, ⟨output.base, L⟩] ⟨fun i => getX s (A8 i), [tbs x, out0]⟩ s :=
    ⟨fun _ => rfl, rfl, rfl,
      fun b hb => by
        obtain _ | _ | b := b
        · exact getX_of (h.x10.symm.trans h10) rfl
        · exact getX_of (h.x13.symm.trans h13) rfl
        · simp at hb; omega,
      fun b hb => by
        obtain _ | _ | b := b
        · exact hxl
        · exact hout0
        · simp at hb; omega,
      fun b hb => by
        obtain _ | _ | b := b
        · simpa [tbs, List.map_map, Function.comp_def] using hx
        · exact ho
        · simp at hb; omega⟩
  refine runsTo_mono (Mach.Riscv.compileAF_okK [0, 3] hwf hR hexec h hpc (codeAt_of_codeBytes hok hcode) hok hcd hrel
    (by rw [hra']; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4, p5⟩
  have e1 := p2.bytes 1 (by simp)
  simp only [hh] at e1
  have e1' : bytesAt s' output.base L = out'.map some := by simpa using e1
  have hfl : (f x).length ≤ L := by
    have := congrArg List.length htk
    simp only [List.length_take, List.length_map] at this; omega
  refine ⟨by rw [p1, hra'], ?_, ?_, Mach.Riscv.abi_of_keep h p4 p5, p4, fun h => nomatch h⟩
  · rw [← bytesAt_take s' output.base hfl, e1', ← List.map_take, htk]; simp [tbs, List.map_map]
  · have e0 := p2.bytes 0 (by simp)
    simp only [hh] at e0
    have e0' : bytesAt s' input.base x.length = bytesAt s input.base x.length := by
      have := e0; simp at this
      rw [this, hx]; simp [tbs, List.map_map]
    intro a ha
    by_cases hqi : input.base ≤ a ∧ a < input.base + input.len
    · have := congrArg (·[a - input.base]?) e0'
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show a - input.base < x.length by omega),
        Option.map_some, Option.some.injEq] at this
      rwa [Nat.add_sub_cancel' hqi.1] at this
    · apply p3 a
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hoo := ha ⟨output.base, (f x).length⟩ (by simp)
      dsimp only at hoo
      rcases hr with rfl | rfl <;> (dsimp only; omega)


/-- every pipe accepted by `compileP` whose intermediate results are no longer than its result -/
theorem compileP_implements1 {p : Pipe} {code : List (BitVec 32)} (h : compileP p = .ok code)
    (hs : ∀ n, Pipe.space p n ≤ Pipe.len p n) : Implements1Raw code (Pipe.denote p) (fun _ => 0) := by
  obtain ⟨hc, hwf, rfl⟩ := compileP_inv h
  exact implements1_of_exec hwf (fun x => by rw [Pipe.denote_len]; exact hs _)
    fun xs out env h1 hx hsp hL => Pipe.prog_exec p hc xs out env h1 hx hsp hL

end Proven
