/- The NATIVE AArch64 target (`C/GenArm.lean`) as a general target (`GTarget`), over any machine `M` with permission
predicates `X` / `W`, and what remains to prove about it (M3), as ONE hypothesis bundle `NatLawsOK`:
* `natTarget M X W V`: registers `armReg`, scratch x16 / x17, permissions `PermOK` on the image's code bytes; the image
  relation `V Cj I` ("`I` is GenArm's image of the J program `Cj`": words, layout, anchors, dead temporaries) is a
  parameter, defined with the templates (M3).
* `NatLawsOK M X W V`: the image facts of `GTarget.Laws` (`entry`, `off_le`, `vis_link`, `vis_ret`, `live_ret`,
  `vis_err`: about `V` only, no machine) and the machine facts (`seg`, `addi_ok`, `ret_ok`).
* `natLaws`: `A64SemN M X W` + `NatLawsOK` give `(natTarget M X W V).Laws` (the calling convention, the RAM window,
  the layout and the loader's permissions are proved here, once).
Nothing here mentions a model: DeepMind and Sail only supply `A64SemN`. -/
import Nano.Run.GTarget
import Nano.Run.ArmNat
namespace JT
open Proven.Top SimW CallProbe

/-- **the native AArch64 target** with image relation `V` -/
def natTarget (M : Machine) (X W : M.State → Nat → Prop) (V : List J → Img → Prop) : GTarget where
  M := M
  reg := armReg
  scratch := armScratch
  lay K C I := JTarget.LayOK M I.code.length K ∧ V C I
  m0 s a := ((M.observe s).memory (UInt64.ofNat a)).map UInt8.toBitVec
  inv K _ I s := PermOK X W K I.code.length s
  valid := V
  loader := ArmLoader X W

/-- **what M3 proves about the native target**: the image facts and the machine facts of `GTarget.Laws` -/
structure NatLawsOK (M : Machine) (X W : M.State → Nat → Prop) (V : List J → Img → Prop) : Prop where
  entry : ∀ (C : List J) (I : Img), V C I → I.vis 0 ∧ I.off 0 = 0
  off_le : ∀ (C : List J) (I : Img), V C I → ∀ n, n ≤ C.length → I.vis n → I.off n ≤ I.code.length
  vis_link : ∀ (C : List J) (I : Img) (n : Nat) (off : Int), V C I → C[n]? = some (.jal 1 off) → I.vis (n + 1)
  vis_ret : ∀ (C : List J) (I : Img) (pc : Nat), V C I → C[pc]? = some (.jalr 0 1) → I.vis pc
  live_ret : ∀ (C : List J) (I : Img) (pc : Nat), V C I → C[pc]? = some (.jalr 0 1) → ∀ j, ¬ I.dead pc j
  vis_err : ∀ (C : List J) (I : Img) (pc : Nat) (imm : Int), V C I → C[pc]? = some (.addi 10 0 imm) →
    C[pc + 1]? = some (.addi 11 0 0) → I.vis pc ∧ I.vis (pc + 1) ∧ I.vis (pc + 2)
  seg : ∀ {K : LayW} {C : List J} {I : Img} {s0 : M.State} {a z : Nat × CallProbe.St} {s : M.State} {n : Nat},
    (natTarget M X W V).lay K C I → (natTarget M X W V).Rel K C I s0 a s → I.vis a.1 → SRunN K C (n + 1) a z →
    I.vis z.1 →
    ∃ m c s', m ≤ n ∧ SRunN K C (n - m) c z ∧ I.vis c.1 ∧ Runs M s s' ∧ (natTarget M X W V).Rel K C I s0 c s'
  addi_ok : ∀ {K : LayW} {C : List J} {I : Img} {s0 : M.State} {pc : Nat} {st : CallProbe.St} {s : M.State}
    {rd rs : Nat} {imm : Int}, (natTarget M X W V).lay K C I → (natTarget M X W V).Rel K C I s0 (pc, st) s →
    I.vis pc → I.vis (pc + 1) → C[pc]? = some (.addi rd rs imm) → rd < 32 → rs < 32 → -2048 ≤ imm → imm < 2048 →
    ∃ s', Runs M s s' ∧
      (natTarget M X W V).Rel K C I s0 (pc + 1, CallProbe.wr st rd (st.x rs + UInt64.ofInt imm)) s'
  ret_ok : ∀ {K : LayW} {C : List J} {I : Img} {s0 : M.State} {pc : Nat} {st : CallProbe.St} {s : M.State},
    (natTarget M X W V).lay K C I → (natTarget M X W V).Rel K C I s0 (pc, st) s → I.vis pc →
    C[pc]? = some (.jalr 0 1) → (st.x 1).toNat % 4 = 0 →
    ∃ s', Runs M s s' ∧ (M.observe s').programCounter = st.x 1 ∧
      (∀ r, (M.observe s').register r = (M.observe s).register r) ∧
      (M.observe s').memory = (M.observe s).memory ∧ M.configured s'

variable {M : Machine} {X W : M.State → Nat → Prop} {V : List J → Img → Prop}

/-- **the native target's laws**, from the abstract A64 steps and the bundle -/
theorem natLaws (S : A64SemN M X W) (H : NatLawsOK M X W V) : (natTarget M X W V).Laws where
  reg_map := by
    have hm : (natTarget M X W V).M.mapping = armMapping := S.map
    rw [hm]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  kept_map r hr := by
    have hr' : r ∈ armMapping.kept := by have := hr; show r ∈ armMapping.kept; rw [← S.map]; exact this
    exact Or.inr (kept_out r hr')
  ram := S.ram
  lay_init _ _ _ h hv := ⟨h, hv⟩
  m0_obs s a _ := by
    show (M.observe s).memory (UInt64.ofNat a) = (((M.observe s).memory (UInt64.ofNat a)).map UInt8.toBitVec).map _
    cases (M.observe s).memory (UInt64.ofNat a) <;> rfl
  inv_init K C I s call x sc hld _ hb _ hlo hhi hib hil hob hol := by
    obtain ⟨hx, hw⟩ := hld
    have hxl := sc.inputLength
    have hb' : K.base = (M.observe s).programCounter.toNat := hb
    show PermOK X W K I.code.length s
    refine ⟨fun a h1 h2 => hx a (by omega) (by omega), fun a ha => hw a ?_⟩
    unfold DataK at ha; unfold InBlocks; omega
  entry := H.entry
  off_le := H.off_le
  vis_link := H.vis_link
  vis_ret := H.vis_ret
  live_ret := H.live_ret
  vis_err := H.vis_err
  seg := H.seg
  addi_ok := H.addi_ok
  ret_ok := H.ret_ok

end JT
