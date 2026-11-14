/- Lowering: IR code over the abstract machine registers (`Code Reg`) to wide operations, and its
correctness from the `Wide` laws: an IR big-step execution is simulated by the machine.

One abstract register `sc` is the lowering's scratch (constants that have no immediate form); IR code
must not mention it (`wf`).  `when` is a forward branch over the body; a loop is laid out bottom-tested,
`jmp test; body; test: pre; br t body` (one branch per iteration). -/
import Compiler.Opt.IR

namespace Proven.Mach
open IR

namespace Wide
variable (M : Wide) (sc : Reg)

/-! ## The lowering -/

def lowIns : Ins Reg → List WOp
  | .set d (.r a) => [.mov d a]
  | .set d (.i c) => [.li d c]
  | .bin op d (.r a) (.r b) => [.bin op d a b]
  | .bin op d (.r a) (.i c) => if M.immOK op c = true then [.bini op d a c] else [.li sc c, .bin op d a sc]
  | .bin op d (.i c) (.r b) => [.li sc c, .bin op d sc b]
  | .bin op d (.i c₁) (.i c₂) => [.li d (op.eval c₁ c₂)]
  | .lbu d (.r a) off => [.lbu d a off]
  | .lbu _ (.i _) _ => []
  | .sb (.r v) (.r a) off => [.sb v a off]
  | .sb (.i c) (.r a) off => [.li sc c, .sb sc a off]
  | .sb _ (.i _) _ => []

/-- a test as (setup, condition, register, register or zero) -/
def lowT (t : Tst Reg) : List WOp × Cond × Reg × Option Reg :=
  match t.a, t.b with
  | .r a, .r b => ([], t.c, a, some b)
  | .r a, .i c => if c = 0 then ([], t.c, a, none) else ([.li sc c], t.c, a, some sc)
  | .i c, .r b => ([.li sc c], t.c, sc, some b)
  | .i c₁, .i c₂ => ([.li sc (if t.c.eval c₁ c₂ = true then 1 else 0)], .ne, sc, none)

def low : Code Reg → List WOp
  | .skip => []
  | .ins i => M.lowIns sc i
  | .seq a b => low a ++ low b
  | .when t body =>
      (lowT sc t.neg).1 ++ ([.br (lowT sc t.neg).2.1 (lowT sc t.neg).2.2.1 (lowT sc t.neg).2.2.2 false
        (M.lenBr + (M.wcode (low body)).length)] ++ low body)
  | .loop pre t body =>
      [.jmp false (M.lenJ + (M.wcode (low body)).length)] ++ (low body ++ (low pre ++ ((lowT sc t).1 ++
        [.br (lowT sc t).2.1 (lowT sc t).2.2.1 (lowT sc t).2.2.2 true
          ((M.wcode (low body)).length + (M.wcode (low pre)).length + (M.wcode (lowT sc t).1).length)])))
  | .loop2 p₁ t₁ p₂ t₂ body =>
      [.jmp false (M.lenJ + (M.wcode (low body)).length)] ++ (low body ++ (low p₁ ++ ((lowT sc t₁.neg).1 ++
        ([.br (lowT sc t₁.neg).2.1 (lowT sc t₁.neg).2.2.1 (lowT sc t₁.neg).2.2.2 false
            (M.lenBr + (M.wcode (low p₂)).length + (M.wcode (lowT sc t₂).1).length + M.lenBr)] ++
          (low p₂ ++ ((lowT sc t₂).1 ++
            [.br (lowT sc t₂).2.1 (lowT sc t₂).2.2.1 (lowT sc t₂).2.2.2 true
              ((M.wcode (low body)).length + (M.wcode (low p₁)).length + (M.wcode (lowT sc t₁.neg).1).length +
                M.lenBr + (M.wcode (low p₂)).length + (M.wcode (lowT sc t₂).1).length)]))))))

/-! ## Well-formedness: no scratch, supported operands, distances in range -/

def argOK : Arg Reg → Bool
  | .r x => decide (x ≠ sc)
  | .i _ => true

def legalIns : Ins Reg → Bool
  | .set d a => decide (d ≠ sc) && argOK sc a
  | .bin _ d a b => decide (d ≠ sc) && argOK sc a && argOK sc b
  | .lbu d (.r a) off => decide (d ≠ sc) && decide (a ≠ sc) && M.offOK off
  | .lbu _ (.i _) _ => false
  | .sb v (.r a) off => argOK sc v && decide (a ≠ sc) && M.offOK off
  | .sb _ (.i _) _ => false

def legalT (t : Tst Reg) : Bool := argOK sc t.a && argOK sc t.b

def wf : Code Reg → Bool
  | .skip => true
  | .ins i => M.legalIns sc i
  | .seq a b => wf a && wf b
  | .when t body => legalT sc t && wf body && M.brOK false (M.lenBr + (M.wcode (M.low sc body)).length)
  | .loop pre t body => legalT sc t && wf pre && wf body &&
      M.jOK false (M.lenJ + (M.wcode (M.low sc body)).length) &&
      M.brOK true ((M.wcode (M.low sc body)).length + (M.wcode (M.low sc pre)).length +
        (M.wcode (lowT sc t).1).length)
  | .loop2 p₁ t₁ p₂ t₂ body => legalT sc t₁ && legalT sc t₂ && (wf p₁ && wf p₂ && wf body) &&
      (M.jOK false (M.lenJ + (M.wcode (M.low sc body)).length) &&
       M.brOK false (M.lenBr + (M.wcode (M.low sc p₂)).length + (M.wcode (lowT sc t₂).1).length + M.lenBr) &&
       M.brOK true ((M.wcode (M.low sc body)).length + (M.wcode (M.low sc p₁)).length +
        (M.wcode (lowT sc t₁.neg).1).length + M.lenBr + (M.wcode (M.low sc p₂)).length +
        (M.wcode (lowT sc t₂).1).length))

/-! ## Simulation -/

variable (ram : Nat → Prop)

/-- machine state `s` represents IR state `σ` (the scratch register is free) -/
def Rel (s : M.S) (σ : St Reg) : Prop := (∀ r, r ≠ sc → M.get s r = σ.reg r) ∧ M.mem s = σ.mem

/-- memory changed only at `ram` addresses -/
def MF (s s' : M.S) : Prop := ∀ a, ¬ram a → M.mem s' a = M.mem s a

/-- the words `ws` sit at `pc`, in RAM, outside the writable addresses -/
structure Frag (s : M.S) (pc : BitVec 64) (ws : List (BitVec 32)) : Prop where
  code : M.codeAt s pc ws
  ok : M.codeOK pc ws.length
  nc : ∀ a, ram a → ¬(pc.toNat ≤ a ∧ a < pc.toNat + 4 * ws.length)

/-- run to `pc'`, establishing `Q` -/
def RunTo (s : M.S) (pc' : BitVec 64) (Q : M.S → Prop) : Prop :=
  M.runsTo s fun s' => M.Done s s' pc' ∧ M.MF ram s s' ∧ Q s'

variable {M sc ram}

theorem MF.refl (s : M.S) : M.MF ram s s := fun _ _ => rfl
theorem MF.of_eq {s s' : M.S} (h : M.mem s' = M.mem s) : M.MF ram s s' := fun a _ => by rw [h]
theorem MF.trans {s₁ s₂ s₃ : M.S} (h₁ : M.MF ram s₁ s₂) (h₂ : M.MF ram s₂ s₃) : M.MF ram s₁ s₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem RunTo.seq {s : M.S} {pc₁ pc₂ : BitVec 64} {P Q : M.S → Prop} (h₁ : M.RunTo ram s pc₁ P)
    (h₂ : ∀ s₁, M.Done s s₁ pc₁ → M.MF ram s s₁ → P s₁ → M.RunTo ram s₁ pc₂ Q) : M.RunTo ram s pc₂ Q :=
  M.runsTo_trans h₁ fun s₁ ⟨d₁, m₁, p₁⟩ => M.runsTo_mono (h₂ s₁ d₁ m₁ p₁) fun _ ⟨d₂, m₂, q⟩ =>
    ⟨Core.Done.trans _ d₁ d₂, MF.trans m₁ m₂, q⟩

theorem RunTo.mono {s : M.S} {pc' : BitVec 64} {P Q : M.S → Prop} (h : M.RunTo ram s pc' P)
    (hpq : ∀ s', M.Done s s' pc' → M.MF ram s s' → P s' → Q s') : M.RunTo ram s pc' Q :=
  M.runsTo_mono h fun s' ⟨d, m, p⟩ => ⟨d, m, hpq s' d m p⟩

theorem RunTo.here {s : M.S} {pc : BitVec 64} {Q : M.S → Prop} (hok : M.ok s) (hpc : M.pcIs s pc) (q : Q s) :
    M.RunTo ram s pc Q := M.runsTo_of ⟨Core.Done.refl _ hok hpc, MF.refl s, q⟩

theorem Frag.left {s : M.S} {pc : BitVec 64} {a b : List (BitVec 32)} (h : M.Frag ram s pc (a ++ b)) :
    M.Frag ram s pc a := by
  obtain ⟨hc, ho, hn⟩ := h
  rw [List.length_append] at ho hn
  exact ⟨((M.codeAt_append).1 hc).1, (M.codeOK_append ho).1, fun x hx h' => hn x hx ⟨h'.1, by omega⟩⟩

theorem Frag.right {s : M.S} {pc : BitVec 64} {a b : List (BitVec 32)} (h : M.Frag ram s pc (a ++ b)) :
    M.Frag ram s (next pc a.length) b := by
  obtain ⟨hc, ho, hn⟩ := h
  rw [List.length_append] at ho hn
  have e := M.pc_toNat ho (a := a.length) (by omega)
  exact ⟨((M.codeAt_append).1 hc).2, (M.codeOK_append ho).2, fun x hx h' => hn x hx (by rw [e] at h'; omega)⟩

/-- the code survives writes to `ram` addresses -/
theorem Frag.mf {s s' : M.S} {pc : BitVec 64} {ws : List (BitVec 32)} (h : M.Frag ram s pc ws)
    (m : M.MF ram s s') : M.Frag ram s' pc ws := by
  refine ⟨fun i hi => M.instrAt_frame (fun j hj => m _ fun hr => h.nc _ hr ?_) (h.code i hi), h.ok, h.nc⟩
  have e := M.pc_toNat h.ok (a := i) (by omega)
  simp only [next] at e
  rw [e]; omega

theorem Frag.at {s : M.S} {pc : BitVec 64} {ws : List (BitVec 32)} (h : M.Frag ram s pc ws) (hok : M.ok s)
    (hpc : M.pcIs s pc) : M.At s pc ws := ⟨hok, hpc, h.code, h.ok⟩

theorem Rel.set {s s' : M.S} {σ : St Reg} {d : Reg} {v : BitVec 64} (hr : M.Rel sc s σ) (st : M.Set1 s s' d v)
    (m : M.mem s' = M.mem s) : M.Rel sc s' ⟨upd σ.reg d v, σ.mem⟩ := by
  refine ⟨fun r hrs => ?_, m.trans hr.2⟩
  rw [st r]
  show (if r = d then v else M.get s r) = if r = d then v else σ.reg r
  by_cases h : r = d
  · rw [ite_pos h, ite_pos h]
  · rw [ite_neg h, ite_neg h]; exact hr.1 r hrs

theorem Rel.scr {s s' : M.S} {σ : St Reg} {v : BitVec 64} (hr : M.Rel sc s σ) (st : M.Set1 s s' sc v)
    (m : M.mem s' = M.mem s) : M.Rel sc s' σ :=
  ⟨fun r hrs => by rw [st r, ite_neg hrs]; exact hr.1 r hrs, m.trans hr.2⟩

theorem Rel.same {s s' : M.S} {σ : St Reg} (hr : M.Rel sc s σ) (st : M.Same s s') (m : M.mem s' = M.mem s) :
    M.Rel sc s' σ := ⟨fun r hrs => by rw [st r]; exact hr.1 r hrs, m.trans hr.2⟩

theorem argOK_r {x : Reg} (h : argOK sc (.r x) = true) : x ≠ sc := of_decide_eq_true h

theorem Rel.arg {s : M.S} {σ : St Reg} {x : Reg} (hr : M.Rel sc s σ) (h : argOK sc (.r x) = true) :
    M.get s x = σ.reg x := hr.1 x (argOK_r h)

theorem wcode2 (o₁ o₂ : WOp) : M.wcode [o₁, o₂] = M.wenc o₁ ++ M.wenc o₂ := by
  show M.wenc o₁ ++ (M.wenc o₂ ++ []) = _; rw [List.append_nil]

theorem and3 {a b c : Bool} (h : (a && b && c) = true) : a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem and2 {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- `li sc c` then continue -/
theorem li_sc {s : M.S} {pc : BitVec 64} {c : BitVec 64} {σ : St Reg} {rest : List (BitVec 32)}
    (hok : M.ok s) (hpc : M.pcIs s pc) (hf : M.Frag ram s pc (M.wenc (.li sc c) ++ rest)) (hr : M.Rel sc s σ) :
    M.RunTo ram s (next pc (M.wenc (.li sc c)).length) fun s' =>
      M.Rel sc s' σ ∧ M.get s' sc = c ∧ M.mem s' = M.mem s :=
  M.runsTo_mono (M.w_li (hf.left.at hok hpc)) fun _ ⟨d, st, m⟩ =>
    ⟨d, MF.of_eq m, hr.scr st m, Core.Set1.same _ st, m⟩

theorem lowIns_ok (hram : ∀ a, ram a → M.inRAM a 1) {i : Ins Reg} {σ σ' : St Reg} (hst : Step ram i σ σ')
    (hl : M.legalIns sc i = true) {s : M.S} {pc : BitVec 64} (hok : M.ok s) (hpc : M.pcIs s pc)
    (hf : M.Frag ram s pc (M.wcode (M.lowIns sc i))) (hr : M.Rel sc s σ) :
    M.RunTo ram s (next pc (M.wcode (M.lowIns sc i)).length) (M.Rel sc · σ') := by
  cases hst with
  | @set d a =>
    obtain ⟨hd, ha⟩ := and2 hl
    cases a with
    | r a =>
      simp only [lowIns, wcode_one] at hf ⊢
      refine M.runsTo_mono (M.w_mov (hf.at hok hpc)) fun s' ⟨dn, st, m⟩ => ⟨dn, MF.of_eq m, ?_⟩
      rw [hr.arg ha] at st; exact hr.set st m
    | i c =>
      simp only [lowIns, wcode_one] at hf ⊢
      exact M.runsTo_mono (M.w_li (hf.at hok hpc)) fun s' ⟨dn, st, m⟩ => ⟨dn, MF.of_eq m, hr.set st m⟩
  | @bin op d a b =>
    obtain ⟨hd, ha, hb⟩ := and3 hl
    cases a with
    | r a =>
      cases b with
      | r b =>
        simp only [lowIns, wcode_one] at hf ⊢
        refine M.runsTo_mono (M.w_bin (hf.at hok hpc)) fun s' ⟨dn, st, m⟩ => ⟨dn, MF.of_eq m, ?_⟩
        rw [hr.arg ha, hr.arg hb] at st; exact hr.set st m
      | i c =>
        simp only [lowIns] at hf ⊢
        by_cases hi : M.immOK op c = true
        · rw [ite_pos hi, wcode_one] at hf ⊢
          refine M.runsTo_mono (M.w_bini hi (hf.at hok hpc)) fun s' ⟨dn, st, m⟩ => ⟨dn, MF.of_eq m, ?_⟩
          rw [hr.arg ha] at st; exact hr.set st m
        · rw [ite_neg hi, wcode2] at hf ⊢
          rw [List.length_append, ← next_add]
          refine (li_sc hok hpc hf hr).seq fun s₁ d₁ m₁ ⟨r₁, v₁, _⟩ => ?_
          refine M.runsTo_mono (M.w_bin ((hf.right.mf m₁).at d₁.ok d₁.hpc)) fun s' ⟨dn, st, m⟩ =>
            ⟨dn, MF.of_eq m, ?_⟩
          rw [r₁.arg ha, v₁] at st; exact r₁.set st m
    | i c =>
      cases b with
      | r b =>
        simp only [lowIns] at hf ⊢
        rw [wcode2] at hf ⊢
        rw [List.length_append, ← next_add]
        refine (li_sc hok hpc hf hr).seq fun s₁ d₁ m₁ ⟨r₁, v₁, _⟩ => ?_
        refine M.runsTo_mono (M.w_bin ((hf.right.mf m₁).at d₁.ok d₁.hpc)) fun s' ⟨dn, st, m⟩ =>
          ⟨dn, MF.of_eq m, ?_⟩
        rw [r₁.arg hb, v₁] at st; exact r₁.set st m
      | i c₂ =>
        simp only [lowIns, wcode_one] at hf ⊢
        exact M.runsTo_mono (M.w_li (hf.at hok hpc)) fun s' ⟨dn, st, m⟩ => ⟨dn, MF.of_eq m, hr.set st m⟩
  | @lbu d a off _ v hra hv =>
    cases a with
    | i c => exact absurd hl (by simp only [legalIns]; exact Bool.false_ne_true)
    | r a =>
      obtain ⟨hd, ha, ho⟩ := and3 hl
      have ea : M.get s a = σ.reg a := hr.1 a (of_decide_eq_true ha)
      simp only [lowIns, wcode_one] at hf ⊢
      simp only [Arg.eval] at hra hv
      rw [← ea] at hra hv; rw [← hr.2] at hv
      exact M.runsTo_mono (M.w_lbu ho (hf.at hok hpc) (hram _ hra) hv) fun s' ⟨dn, st, m⟩ =>
        ⟨dn, MF.of_eq m, hr.set st m⟩
  | @sb v a off _ hra =>
    cases a with
    | i c => cases v <;> exact absurd hl (by simp only [legalIns]; exact Bool.false_ne_true)
    | r a =>
      have hmf : ∀ {s₁ s' : M.S} {x : BitVec 8}, M.mem s₁ = M.mem s → M.get s₁ a = σ.reg a →
          M.mem s' = (M.mem s₁).upd (M.get s₁ a + off).toNat x →
          M.MF ram s₁ s' ∧ M.mem s' = σ.mem.upd (σ.reg a + off).toNat x := fun {s₁ s' x} e₁ ea m => by
        refine ⟨fun y hy => ?_, by rw [m, e₁, ea, hr.2]⟩
        rw [m]; unfold Mem.upd
        rw [ite_neg]; intro e; subst e; rw [ea] at hy; exact hy hra
      cases v with
      | r v =>
        obtain ⟨hv, ha, ho⟩ := and3 hl
        have ea : M.get s a = σ.reg a := hr.1 a (of_decide_eq_true ha)
        simp only [lowIns, wcode_one] at hf ⊢
        simp only [Arg.eval] at hra ⊢
        refine M.runsTo_mono (M.w_sb ho (hf.at hok hpc) (hram _ (by rw [ea]; exact hra))) fun s' ⟨dn, st, m⟩ => ?_
        obtain ⟨mf, m'⟩ := hmf rfl ea m
        rw [hr.arg hv] at m'
        exact ⟨dn, mf, fun r hrs => by rw [st r]; exact hr.1 r hrs, m'⟩
      | i c =>
        obtain ⟨hv, ha, ho⟩ := and3 hl
        simp only [lowIns] at hf ⊢
        rw [wcode2] at hf ⊢
        rw [List.length_append, ← next_add]
        simp only [Arg.eval] at hra ⊢
        refine (li_sc hok hpc hf hr).seq fun s₁ d₁ m₁ ⟨r₁, v₁, e₁⟩ => ?_
        have ea : M.get s₁ a = σ.reg a := r₁.1 a (of_decide_eq_true ha)
        refine M.runsTo_mono (M.w_sb ho ((hf.right.mf m₁).at d₁.ok d₁.hpc) (hram _ (by rw [ea]; exact hra)))
          fun s' ⟨dn, st, m⟩ => ?_
        obtain ⟨mf, m'⟩ := hmf e₁ ea m
        rw [v₁] at m'
        exact ⟨dn, mf, fun r hrs => by rw [st r]; exact r₁.1 r hrs, m'⟩

theorem lowT_ok {t : Tst Reg} {σ : St Reg} (hl : legalT sc t = true) {s : M.S} {pc : BitVec 64}
    {rest : List (BitVec 32)} (hok : M.ok s) (hpc : M.pcIs s pc)
    (hf : M.Frag ram s pc (M.wcode (lowT sc t).1 ++ rest)) (hr : M.Rel sc s σ) :
    M.RunTo ram s (next pc (M.wcode (lowT sc t).1).length) fun s' =>
      M.Rel sc s' σ ∧ M.mem s' = M.mem s ∧
      (lowT sc t).2.1.eval (M.get s' (lowT sc t).2.2.1) (M.getO s' (lowT sc t).2.2.2) = t.eval σ.reg := by
  obtain ⟨c, a, b⟩ := t
  obtain ⟨ha, hb⟩ := and2 hl
  simp only at ha hb
  cases a with
  | r a =>
    cases b with
    | r b =>
      simp only [lowT, wcode, List.length_nil, next_zero] at hf ⊢
      exact RunTo.here hok hpc ⟨hr, rfl, by simp only [Tst.eval, Arg.eval, Base.getO]; rw [hr.arg ha, hr.arg hb]⟩
    | i c₀ =>
      by_cases h0 : c₀ = 0
      · simp only [lowT, ite_pos h0, wcode, List.length_nil, next_zero] at hf ⊢
        exact RunTo.here hok hpc ⟨hr, rfl, by simp only [Tst.eval, Arg.eval, Base.getO]; rw [hr.arg ha, h0]⟩
      · simp only [lowT, ite_neg h0, wcode_one] at hf ⊢
        refine (li_sc hok hpc hf hr).mono fun s' _ _ ⟨r₁, v₁, e₁⟩ => ⟨r₁, e₁, ?_⟩
        simp only [Tst.eval, Arg.eval, Base.getO]; rw [r₁.arg ha, v₁]
  | i c₁ =>
    cases b with
    | r b =>
      simp only [lowT, wcode_one] at hf ⊢
      refine (li_sc hok hpc hf hr).mono fun s' _ _ ⟨r₁, v₁, e₁⟩ => ⟨r₁, e₁, ?_⟩
      simp only [Tst.eval, Arg.eval, Base.getO]; rw [r₁.arg hb, v₁]
    | i c₂ =>
      simp only [lowT, wcode_one] at hf ⊢
      refine (li_sc hok hpc hf hr).mono fun s' _ _ ⟨r₁, v₁, e₁⟩ => ⟨r₁, e₁, ?_⟩
      simp only [Tst.eval, Arg.eval, Base.getO]; rw [v₁]
      cases h : c.eval c₁ c₂
      · rw [ite_neg Bool.false_ne_true]; rfl
      · rw [ite_pos rfl]; rfl

/-- the words of a lowered fragment -/
def W (M : Wide) (sc : Reg) (c : Code Reg) : List (BitVec 32) := M.wcode (M.low sc c)

/-- the test's branch operation -/
def brOp (M : Wide) (sc : Reg) (t : Tst Reg) (back : Bool) (n : Nat) : WOp :=
  .br (lowT sc t).2.1 (lowT sc t).2.2.1 (lowT sc t).2.2.2 back n

theorem W_seq (a b : Code Reg) : M.W sc (.seq a b) = M.W sc a ++ M.W sc b := M.wcode_append _ _

theorem W_when (t : Tst Reg) (body : Code Reg) : M.W sc (.when t body) = M.wcode (lowT sc t.neg).1 ++
    (M.wenc (M.brOp sc t.neg false (M.lenBr + (M.W sc body).length)) ++ M.W sc body) := by
  simp only [W, low, wcode_append, wcode_one, brOp]

theorem W_loop (pre : Code Reg) (t : Tst Reg) (body : Code Reg) : M.W sc (.loop pre t body) =
    M.wenc (.jmp false (M.lenJ + (M.W sc body).length)) ++ (M.W sc body ++ (M.W sc pre ++
      (M.wcode (lowT sc t).1 ++ M.wenc (M.brOp sc t true
        ((M.W sc body).length + (M.W sc pre).length + (M.wcode (lowT sc t).1).length))))) := by
  simp only [W, low, wcode_append, wcode_one, brOp]

theorem len_loop (pre : Code Reg) (t : Tst Reg) (body : Code Reg) : (M.W sc (.loop pre t body)).length =
    M.lenJ + (M.W sc body).length + (M.W sc pre).length + (M.wcode (lowT sc t).1).length + M.lenBr := by
  rw [W_loop]; simp only [List.length_append, M.len_j, brOp, M.len_br]; omega

theorem tgt_back (pc : BitVec 64) (a x b : Nat) (h : x = a + b) : tgt (next pc x) true b = next pc a := by
  subst h; simp only [tgt, ite_pos]; rw [← next_add, next_jmp]

theorem _root_.Proven.Mach.Base.Done.cast {B : Base} {s s' : B.S} {p q : BitVec 64} (d : B.Done s s' p) (h : p = q) :
    B.Done s s' q := h ▸ d

/-- a loop from its test: run `pre`, the test and the branch -/
theorem loop_test {pre : Code Reg} {t : Tst Reg} {body : Code Reg} {σ σ₁ : St Reg}
    (hwf : M.wf sc (.loop pre t body) = true)
    (ihpre : ∀ {s : M.S} {pc : BitVec 64}, M.ok s → M.pcIs s pc → M.Frag ram s pc (M.W sc pre) → M.Rel sc s σ →
      M.RunTo ram s (next pc (M.W sc pre).length) (M.Rel sc · σ₁))
    {s : M.S} {pc : BitVec 64} (hok : M.ok s) (hpc : M.pcIs s (next pc (M.lenJ + (M.W sc body).length)))
    (hf : M.Frag ram s pc (M.W sc (.loop pre t body))) (hr : M.Rel sc s σ) :
    M.RunTo ram s (if t.eval σ₁.reg = true then next pc M.lenJ else next pc (M.W sc (.loop pre t body)).length)
      (M.Rel sc · σ₁) := by
  simp only [wf] at hwf
  obtain ⟨hwf, hbr⟩ := and2 hwf
  obtain ⟨hwf, hj⟩ := and2 hwf
  obtain ⟨hlt, hwp, hwb⟩ := and3 hwf
  rw [len_loop]
  rw [W_loop] at hf
  have f1 := hf.right.right
  rw [M.len_j, next_add] at f1
  refine (ihpre hok hpc f1.left hr).seq fun s₁ d₁ m₁ r₁ => ?_
  refine (lowT_ok hlt d₁.ok d₁.hpc (f1.right.mf m₁) r₁).seq fun s₂ d₂ m₂ ⟨r₂, _, v₂⟩ => ?_
  have f3 := (f1.right.right.mf m₁).mf m₂
  refine M.runsTo_mono (M.w_br hbr (f3.at d₂.ok d₂.hpc)) fun s₃ ⟨d₃, st, m₃⟩ => ⟨?_, MF.of_eq m₃, r₂.same st m₃⟩
  rw [v₂] at d₃
  simp only [W, next_add] at d₃ ⊢
  by_cases ht : t.eval σ₁.reg = true
  · rw [ite_pos ht] at d₃ ⊢
    rw [tgt_back pc M.lenJ _ _ (by omega)] at d₃
    exact d₃
  · rw [ite_neg ht] at d₃ ⊢
    exact d₃.cast (congrArg (next pc) (by omega))

theorem tgt_fwd (pc : BitVec 64) (n : Nat) : tgt pc false n = next pc n := ite_neg Bool.false_ne_true

theorem Frag.cast {s : M.S} {p q : BitVec 64} {ws : List (BitVec 32)} (h : M.Frag ram s p ws) (e : p = q) :
    M.Frag ram s q ws := e ▸ h

theorem RunTo.cast {s : M.S} {p q : BitVec 64} {Q : M.S → Prop} (h : M.RunTo ram s p Q) (e : p = q) :
    M.RunTo ram s q Q := e ▸ h

theorem W_loop2 (p₁ : Code Reg) (t₁ : Tst Reg) (p₂ : Code Reg) (t₂ : Tst Reg) (body : Code Reg) :
    M.W sc (.loop2 p₁ t₁ p₂ t₂ body) =
    M.wenc (.jmp false (M.lenJ + (M.W sc body).length)) ++ (M.W sc body ++ (M.W sc p₁ ++
      (M.wcode (lowT sc t₁.neg).1 ++ (M.wenc (M.brOp sc t₁.neg false
          (M.lenBr + (M.W sc p₂).length + (M.wcode (lowT sc t₂).1).length + M.lenBr)) ++
        (M.W sc p₂ ++ (M.wcode (lowT sc t₂).1 ++ M.wenc (M.brOp sc t₂ true
          ((M.W sc body).length + (M.W sc p₁).length + (M.wcode (lowT sc t₁.neg).1).length + M.lenBr +
            (M.W sc p₂).length + (M.wcode (lowT sc t₂).1).length)))))))) := by
  simp only [W, low, wcode_append, wcode_one, brOp]

theorem len_loop2 (p₁ : Code Reg) (t₁ : Tst Reg) (p₂ : Code Reg) (t₂ : Tst Reg) (body : Code Reg) :
    (M.W sc (.loop2 p₁ t₁ p₂ t₂ body)).length =
    M.lenJ + (M.W sc body).length + (M.W sc p₁).length + (M.wcode (lowT sc t₁.neg).1).length + M.lenBr +
      (M.W sc p₂).length + (M.wcode (lowT sc t₂).1).length + M.lenBr := by
  rw [W_loop2]; simp only [List.length_append, M.len_j, brOp, M.len_br]; omega

theorem wf_loop2 {p₁ : Code Reg} {t₁ : Tst Reg} {p₂ : Code Reg} {t₂ : Tst Reg} {body : Code Reg}
    (h : M.wf sc (.loop2 p₁ t₁ p₂ t₂ body) = true) :
    (legalT sc t₁ = true ∧ legalT sc t₂ = true) ∧ (M.wf sc p₁ = true ∧ M.wf sc p₂ = true ∧ M.wf sc body = true) ∧
    M.jOK false (M.lenJ + (M.W sc body).length) = true ∧
    M.brOK false (M.lenBr + (M.W sc p₂).length + (M.wcode (lowT sc t₂).1).length + M.lenBr) = true ∧
    M.brOK true ((M.W sc body).length + (M.W sc p₁).length + (M.wcode (lowT sc t₁.neg).1).length + M.lenBr +
      (M.W sc p₂).length + (M.wcode (lowT sc t₂).1).length) = true := by
  simp only [wf] at h
  obtain ⟨h1, h2, h3⟩ := and3 h
  exact ⟨and2 h1, and3 h2, and3 h3⟩

/-- a two-test loop from its first test: `pre₁`, the test, the exit branch -/
theorem loop2_t1 {p₁ : Code Reg} {t₁ : Tst Reg} {p₂ : Code Reg} {t₂ : Tst Reg} {body : Code Reg} {σ σ₁ : St Reg}
    (hwf : M.wf sc (.loop2 p₁ t₁ p₂ t₂ body) = true)
    (ih₁ : ∀ {s : M.S} {pc : BitVec 64}, M.ok s → M.pcIs s pc → M.Frag ram s pc (M.W sc p₁) → M.Rel sc s σ →
      M.RunTo ram s (next pc (M.W sc p₁).length) (M.Rel sc · σ₁))
    {s : M.S} {pc : BitVec 64} (hok : M.ok s) (hpc : M.pcIs s (next pc (M.lenJ + (M.W sc body).length)))
    (hf : M.Frag ram s pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body))) (hr : M.Rel sc s σ) :
    M.RunTo ram s (if t₁.eval σ₁.reg = true then
        next pc (M.lenJ + (M.W sc body).length + (M.W sc p₁).length + (M.wcode (lowT sc t₁.neg).1).length + M.lenBr)
      else next pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body)).length) (M.Rel sc · σ₁) := by
  obtain ⟨⟨hl1, hl2⟩, ⟨hw1, hw2, hwb⟩, hj, hb1, hb2⟩ := wf_loop2 hwf
  rw [len_loop2]
  rw [W_loop2] at hf
  have f1 := hf.right.right
  rw [M.len_j, next_add] at f1
  refine (ih₁ hok hpc f1.left hr).seq fun s₁ d₁ m₁ r₁ => ?_
  refine (lowT_ok (t := t₁.neg) hl1 d₁.ok d₁.hpc (f1.right.mf m₁) r₁).seq fun s₂ d₂ m₂ ⟨r₂, _, v₂⟩ => ?_
  have f3 := (f1.right.right.left.mf m₁).mf m₂
  refine M.runsTo_mono (M.w_br hb1 (f3.at d₂.ok d₂.hpc)) fun s₃ ⟨d₃, st, m₃⟩ => ⟨?_, MF.of_eq m₃, r₂.same st m₃⟩
  rw [v₂, Tst.eval_neg] at d₃
  simp only [next_add, tgt_fwd] at d₃ ⊢
  cases ht : t₁.eval σ₁.reg
  · rw [ht] at d₃
    simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false] at d₃ ⊢
    exact d₃.cast (congrArg (next pc) (by omega))
  · rw [ht] at d₃
    simp only [Bool.not_true, ite_true, Bool.false_eq_true, ite_false] at d₃ ⊢
    exact d₃

/-- a two-test loop from its second test: `pre₂`, the test, the back branch -/
theorem loop2_t2 {p₁ : Code Reg} {t₁ : Tst Reg} {p₂ : Code Reg} {t₂ : Tst Reg} {body : Code Reg} {σ₁ σ₂ : St Reg}
    (hwf : M.wf sc (.loop2 p₁ t₁ p₂ t₂ body) = true)
    (ih₂ : ∀ {s : M.S} {pc : BitVec 64}, M.ok s → M.pcIs s pc → M.Frag ram s pc (M.W sc p₂) → M.Rel sc s σ₁ →
      M.RunTo ram s (next pc (M.W sc p₂).length) (M.Rel sc · σ₂))
    {s : M.S} {pc : BitVec 64} (hok : M.ok s)
    (hpc : M.pcIs s (next pc (M.lenJ + (M.W sc body).length + (M.W sc p₁).length +
      (M.wcode (lowT sc t₁.neg).1).length + M.lenBr)))
    (hf : M.Frag ram s pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body))) (hr : M.Rel sc s σ₁) :
    M.RunTo ram s (if t₂.eval σ₂.reg = true then next pc M.lenJ
      else next pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body)).length) (M.Rel sc · σ₂) := by
  obtain ⟨⟨hl1, hl2⟩, ⟨hw1, hw2, hwb⟩, hj, hb1, hb2⟩ := wf_loop2 hwf
  rw [len_loop2]
  rw [W_loop2] at hf
  have f1 := hf.right.right.right.right.right
  simp only [M.len_j, brOp, M.len_br, next_add] at f1
  replace f1 := f1.cast (q := next pc (M.lenJ + (M.W sc body).length + (M.W sc p₁).length +
      (M.wcode (lowT sc t₁.neg).1).length + M.lenBr)) (congrArg (next pc) (by omega))
  refine (ih₂ hok hpc f1.left hr).seq fun s₁ d₁ m₁ r₁ => ?_
  refine (lowT_ok hl2 d₁.ok d₁.hpc (f1.right.mf m₁) r₁).seq fun s₂ d₂ m₂ ⟨r₂, _, v₂⟩ => ?_
  have f3 := (f1.right.right.mf m₁).mf m₂
  refine M.runsTo_mono (M.w_br hb2 (f3.at d₂.ok d₂.hpc)) fun s₃ ⟨d₃, st, m₃⟩ => ⟨?_, MF.of_eq m₃, r₂.same st m₃⟩
  rw [v₂] at d₃
  simp only [next_add] at d₃ ⊢
  by_cases ht : t₂.eval σ₂.reg = true
  · rw [ite_pos ht] at d₃ ⊢
    rw [tgt_back pc M.lenJ _ _ (by omega)] at d₃
    exact d₃
  · rw [ite_neg ht] at d₃ ⊢
    exact d₃.cast (congrArg (next pc) (by omega))

/-- entering a loop at its head: jump to the test -/
theorem loop_enter {ws rest : List (BitVec 32)} {n : Nat} {Q : M.S → Prop} {σ : St Reg}
    (hW : ws = M.wenc (.jmp false n) ++ rest) (hj : M.jOK false n = true)
    (h2 : ∀ {s : M.S} {pc : BitVec 64}, M.ok s → M.pcIs s (next pc n) → M.Frag ram s pc ws → M.Rel sc s σ →
      M.RunTo ram s (next pc ws.length) Q)
    {s : M.S} {pc : BitVec 64} (hok : M.ok s) (hpc : M.pcIs s pc) (hf : M.Frag ram s pc ws) (hr : M.Rel sc s σ) :
    M.RunTo ram s (next pc ws.length) Q := by
  have fj := hf
  rw [hW] at fj
  refine RunTo.seq (P := fun s₁ => M.Rel sc s₁ σ) (M.runsTo_mono (M.w_jmp hj (fj.left.at hok hpc))
    fun s₁ ⟨d, st, m⟩ => ⟨d, MF.of_eq m, hr.same st m⟩) fun s₁ d₁ m₁ r₁ => ?_
  exact h2 d₁.ok (by have := d₁.hpc; rwa [tgt_fwd] at this) (hf.mf m₁) r₁

/-- **Lowering is correct**: an IR execution of `c` is simulated by the machine running `W c`.  The second
and third components are the same statement for a loop entered at its test. -/
theorem low_ok' (hram : ∀ a, ram a → M.inRAM a 1) : ∀ {c : Code Reg} {σ σ' : St Reg}, Exec ram c σ σ' →
    (M.wf sc c = true → ∀ {s : M.S} {pc : BitVec 64}, M.ok s → M.pcIs s pc → M.Frag ram s pc (M.W sc c) →
      M.Rel sc s σ → M.RunTo ram s (next pc (M.W sc c).length) (M.Rel sc · σ')) ∧
    (∀ pre t body, c = .loop pre t body → M.wf sc c = true → ∀ {s : M.S} {pc : BitVec 64}, M.ok s →
      M.pcIs s (next pc (M.lenJ + (M.W sc body).length)) → M.Frag ram s pc (M.W sc c) →
      M.Rel sc s σ → M.RunTo ram s (next pc (M.W sc c).length) (M.Rel sc · σ')) ∧
    (∀ p₁ t₁ p₂ t₂ body, c = .loop2 p₁ t₁ p₂ t₂ body → M.wf sc c = true → ∀ {s : M.S} {pc : BitVec 64}, M.ok s →
      M.pcIs s (next pc (M.lenJ + (M.W sc body).length)) → M.Frag ram s pc (M.W sc c) →
      M.Rel sc s σ → M.RunTo ram s (next pc (M.W sc c).length) (M.Rel sc · σ')) := by
  intro c σ σ' h
  have jl : ∀ {pre t body}, M.wf sc (.loop pre t body) = true → M.jOK false (M.lenJ + (M.W sc body).length) = true :=
    fun hwf => by simp only [wf] at hwf; exact (and2 (and2 hwf).1).2
  induction h with
  | skip => exact ⟨fun _ s pc hok hpc _ hr => by
      rw [show (M.W sc Code.skip).length = 0 from rfl, next_zero]; exact RunTo.here hok hpc hr,
      fun _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e)⟩
  | ins hst => exact ⟨fun hwf s pc hok hpc hf hr => lowIns_ok hram hst hwf hok hpc hf hr, fun _ _ _ e => (by cases e),
      fun _ _ _ _ _ e => (by cases e)⟩
  | @seq a b _ _ _ _ _ iha ihb =>
    refine ⟨fun hwf s pc hok hpc hf hr => ?_, fun _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e)⟩
    obtain ⟨wa, wb⟩ := and2 (show (M.wf sc a && M.wf sc b) = true from hwf)
    rw [W_seq] at hf ⊢
    rw [List.length_append, ← next_add]
    exact (iha.1 wa hok hpc hf.left hr).seq fun s₁ d₁ m₁ r₁ => ihb.1 wb d₁.ok d₁.hpc (hf.right.mf m₁) r₁
  | @whenT t body _ _ ht _ ih =>
    refine ⟨fun hwf s pc hok hpc hf hr => ?_, fun _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e)⟩
    obtain ⟨hlt, hwb, hbr⟩ := and3 (show (legalT sc t && M.wf sc body && _) = true from hwf)
    rw [W_when] at hf ⊢
    rw [List.length_append, List.length_append, brOp, M.len_br, ← next_add, ← next_add]
    refine (lowT_ok (t := t.neg) hlt hok hpc hf hr).seq fun s₁ d₁ m₁ ⟨r₁, _, v₁⟩ => ?_
    have f2 := hf.right.mf m₁
    refine RunTo.seq (P := fun s₂ => M.Rel sc s₂ _) (M.runsTo_mono (M.w_br hbr (f2.left.at d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st, m₂⟩ => ⟨d₂, MF.of_eq m₂, r₁.same st m₂⟩) fun s₂ d₂ m₂ r₂ => ?_
    rw [v₁, Tst.eval_neg, ht] at d₂
    have f3 := f2.right.mf m₂
    rw [brOp, M.len_br] at f3
    exact ih.1 hwb d₂.ok (by simpa only [Bool.not_true, ite_neg Bool.false_ne_true] using d₂.hpc) f3 r₂
  | @whenF t body _ ht =>
    refine ⟨fun hwf s pc hok hpc hf hr => ?_, fun _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e)⟩
    obtain ⟨hlt, hwb, hbr⟩ := and3 (show (legalT sc t && M.wf sc body && _) = true from hwf)
    rw [W_when] at hf ⊢
    rw [List.length_append, List.length_append, brOp, M.len_br, ← next_add]
    refine (lowT_ok (t := t.neg) hlt hok hpc hf hr).seq fun s₁ d₁ m₁ ⟨r₁, _, v₁⟩ => ?_
    have f2 := hf.right.mf m₁
    refine M.runsTo_mono (M.w_br hbr (f2.left.at d₁.ok d₁.hpc)) fun s₂ ⟨d₂, st, m₂⟩ =>
      ⟨?_, MF.of_eq m₂, r₁.same st m₂⟩
    rw [v₁, Tst.eval_neg, ht] at d₂
    simpa only [Bool.not_false, ite_pos, tgt, ite_neg Bool.false_ne_true] using d₂
  | @loopF pre t body σa σb _ ht ihpre =>
    have h2 : M.wf sc (.loop pre t body) = true → ∀ {s : M.S} {pc : BitVec 64}, M.ok s →
        M.pcIs s (next pc (M.lenJ + (M.W sc body).length)) → M.Frag ram s pc (M.W sc (.loop pre t body)) →
        M.Rel sc s σa → M.RunTo ram s (next pc (M.W sc (.loop pre t body)).length) (M.Rel sc · σb) := by
      intro hwf s pc hok hpc hf hr
      have hwf' := hwf
      simp only [wf] at hwf'
      have hwp := (and3 (and2 (and2 hwf').1).1).2.1
      have := loop_test hwf (ihpre.1 hwp) hok hpc hf hr
      rwa [ht, ite_neg Bool.false_ne_true] at this
    exact ⟨fun hwf => loop_enter (W_loop pre t body) (jl hwf) (h2 hwf), fun _ _ _ e => (by cases e; exact h2),
      fun _ _ _ _ _ e => (by cases e)⟩
  | @loopT pre t body σa σb σc σd _ ht _ _ ihpre ihb ihl =>
    have h2 : M.wf sc (.loop pre t body) = true → ∀ {s : M.S} {pc : BitVec 64}, M.ok s →
        M.pcIs s (next pc (M.lenJ + (M.W sc body).length)) → M.Frag ram s pc (M.W sc (.loop pre t body)) →
        M.Rel sc s σa → M.RunTo ram s (next pc (M.W sc (.loop pre t body)).length) (M.Rel sc · σd) := by
      intro hwf s pc hok hpc hf hr
      have hwf' := hwf
      simp only [wf] at hwf'
      obtain ⟨_, hwp, hwb⟩ := and3 (and2 (and2 hwf').1).1
      have := loop_test hwf (ihpre.1 hwp) hok hpc hf hr
      rw [ht, ite_pos rfl] at this
      refine this.seq fun s₁ d₁ m₁ r₁ => ?_
      have f1 := hf.mf m₁
      have fb := f1
      rw [W_loop] at fb
      have fb := fb.right.left
      rw [M.len_j] at fb
      refine (ihb.1 hwb d₁.ok d₁.hpc fb r₁).seq fun s₂ d₂ m₂ r₂ => ?_
      exact ihl.2.1 pre t body rfl hwf d₂.ok (by rw [← next_add]; exact d₂.hpc) (f1.mf m₂) r₂
    exact ⟨fun hwf => loop_enter (W_loop pre t body) (jl hwf) (h2 hwf), fun _ _ _ e => (by cases e; exact h2),
      fun _ _ _ _ _ e => (by cases e)⟩
  | @loop2A p₁ t₁ p₂ t₂ body σa σb _ ht ih₁ =>
    have h2 : M.wf sc (.loop2 p₁ t₁ p₂ t₂ body) = true → ∀ {s : M.S} {pc : BitVec 64}, M.ok s →
        M.pcIs s (next pc (M.lenJ + (M.W sc body).length)) → M.Frag ram s pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body)) →
        M.Rel sc s σa → M.RunTo ram s (next pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body)).length) (M.Rel sc · σb) := by
      intro hwf s pc hok hpc hf hr
      have := loop2_t1 hwf (ih₁.1 (wf_loop2 hwf).2.1.1) hok hpc hf hr
      rwa [ht, ite_neg Bool.false_ne_true] at this
    exact ⟨fun hwf => loop_enter (W_loop2 p₁ t₁ p₂ t₂ body) (wf_loop2 hwf).2.2.1 (h2 hwf),
      fun _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e; exact h2)⟩
  | @loop2B p₁ t₁ p₂ t₂ body σa σb σc _ ht₁ _ ht₂ ih₁ ih₂ =>
    have h2 : M.wf sc (.loop2 p₁ t₁ p₂ t₂ body) = true → ∀ {s : M.S} {pc : BitVec 64}, M.ok s →
        M.pcIs s (next pc (M.lenJ + (M.W sc body).length)) → M.Frag ram s pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body)) →
        M.Rel sc s σa → M.RunTo ram s (next pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body)).length) (M.Rel sc · σc) := by
      intro hwf s pc hok hpc hf hr
      have := loop2_t1 hwf (ih₁.1 (wf_loop2 hwf).2.1.1) hok hpc hf hr
      rw [ht₁, ite_pos rfl] at this
      refine this.seq fun s₁ d₁ m₁ r₁ => ?_
      have := loop2_t2 hwf (ih₂.1 (wf_loop2 hwf).2.1.2.1) d₁.ok d₁.hpc (hf.mf m₁) r₁
      rwa [ht₂, ite_neg Bool.false_ne_true] at this
    exact ⟨fun hwf => loop_enter (W_loop2 p₁ t₁ p₂ t₂ body) (wf_loop2 hwf).2.2.1 (h2 hwf),
      fun _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e; exact h2)⟩
  | @loop2T p₁ t₁ p₂ t₂ body σa σb σc σd σe _ ht₁ _ ht₂ _ _ ih₁ ih₂ ihb ihl =>
    have h2 : M.wf sc (.loop2 p₁ t₁ p₂ t₂ body) = true → ∀ {s : M.S} {pc : BitVec 64}, M.ok s →
        M.pcIs s (next pc (M.lenJ + (M.W sc body).length)) → M.Frag ram s pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body)) →
        M.Rel sc s σa → M.RunTo ram s (next pc (M.W sc (.loop2 p₁ t₁ p₂ t₂ body)).length) (M.Rel sc · σe) := by
      intro hwf s pc hok hpc hf hr
      have := loop2_t1 hwf (ih₁.1 (wf_loop2 hwf).2.1.1) hok hpc hf hr
      rw [ht₁, ite_pos rfl] at this
      refine this.seq fun s₁ d₁ m₁ r₁ => ?_
      have := loop2_t2 hwf (ih₂.1 (wf_loop2 hwf).2.1.2.1) d₁.ok d₁.hpc (hf.mf m₁) r₁
      rw [ht₂, ite_pos rfl] at this
      refine this.seq fun s₂ d₂ m₂ r₂ => ?_
      have f2 := (hf.mf m₁).mf m₂
      have fb := f2
      rw [W_loop2] at fb
      have fb := fb.right.left
      rw [M.len_j] at fb
      refine (ihb.1 (wf_loop2 hwf).2.1.2.2 d₂.ok d₂.hpc fb r₂).seq fun s₃ d₃ m₃ r₃ => ?_
      exact ihl.2.2 p₁ t₁ p₂ t₂ body rfl hwf d₃.ok (by rw [← next_add]; exact d₃.hpc) (f2.mf m₃) r₃
    exact ⟨fun hwf => loop_enter (W_loop2 p₁ t₁ p₂ t₂ body) (wf_loop2 hwf).2.2.1 (h2 hwf),
      fun _ _ _ e => (by cases e), fun _ _ _ _ _ e => (by cases e; exact h2)⟩

theorem low_ok (hram : ∀ a, ram a → M.inRAM a 1) {c : Code Reg} {σ σ' : St Reg} (hex : Exec ram c σ σ')
    (hwf : M.wf sc c = true) {s : M.S} {pc : BitVec 64} (hok : M.ok s) (hpc : M.pcIs s pc)
    (hf : M.Frag ram s pc (M.W sc c)) (hr : M.Rel sc s σ) :
    M.RunTo ram s (next pc (M.W sc c).length) (M.Rel sc · σ') := (low_ok' hram hex).1 hwf hok hpc hf hr

end Wide
end Proven.Mach
