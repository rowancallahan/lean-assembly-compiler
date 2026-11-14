/- The optimising byte-array compiler (`AStmt`: 8 variables, loads/stores into named blocks, `while`) over
any `Wide` target, and its correctness (`optA_ok`, the statement of `Machine.compAF_ok`).

Variables `v_i` live in `avar i` (as before), temporaries in `r0 .. r5`, scratch `r6`.  A load is
`add t, base, i; lbu v, 0(t)`; a store `add t, base, i; sb e, 0(t)` with `e` used in place when it is a
variable. -/
import Compiler.Opt.Fn
import Compiler.Opt.Sel
import Compiler.Arr

namespace Proven.Mach
open IR Sel

/-- IR code (virtual registers) of an array statement -/
def irA (bv : List (Fin 8)) : AStmt → Code Nat
  | .assign v e => into e v.val 0
  | .load v b i => .seq (into (addrE bv b i) (tk 0) 0) (.ins (.lbu v.val (.r (tk 0)) 0))
  | .store b i e => .seq (into (addrE bv b i) (tk 0) 0) (.seq (opnd e 1 (into e (tk 1) 1)).1
      (.ins (.sb (opnd e 1 (into e (tk 1) 1)).2.1 (.r (tk 0)) 0)))
  | .seq p q => .seq (irA bv p) (irA bv q)
  | .loop c body => loopCode c (irA bv body)

/-- block variables are never assigned, block numbers are in range (checked) -/
def okA (bv : List (Fin 8)) : AStmt → Bool
  | .assign v _ => decide (v ∉ bv)
  | .load v b _ => decide (v ∉ bv) && decide (b < bv.length)
  | .store b _ _ => decide (b < bv.length)
  | .seq p q => okA bv p && okA bv q
  | .loop _ body => okA bv body

/-- addresses inside the data regions -/
def ramR (R : List Region) (a : Nat) : Prop := ∃ r ∈ R, r.base ≤ a ∧ a < r.base + r.len

/-- the IR state represents `σ` -/
structure RelA (bv : List (Fin 8)) (R : List Region) (σ : AState) (τ : St Nat) : Prop where
  env : ∀ i : Fin 8, τ.reg i.val = σ.env i
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  bytes : ∀ b (hb : b < R.length), bytes τ.mem R[b].base R[b].len = (σ.heap[b]?.getD []).map some

theorem RelA.agree {bv R σ τ} (r : RelA bv R σ τ) (e : AExp) : Agree σ.env e τ := fun i _ => r.env i

theorem RelA.setVar {bv R σ τ} (r : RelA bv R σ τ) {τ' : St Nat} (hm : τ'.mem = τ.mem) {v : Fin 8}
    (hv : v ∉ bv) {x : BitVec 64} (hx : τ'.reg v.val = x)
    (hf : ∀ y, y ≠ v.val → y < 8 → τ'.reg y = τ.reg y) : RelA bv R ⟨σ.env.set v x, σ.heap⟩ τ' := by
  refine ⟨fun i => ?_, r.hlen, r.bvlen, fun b hb => ?_, r.blen, fun b hb => by rw [hm]; exact r.bytes b hb⟩
  · show _ = if i = v then x else σ.env i
    by_cases hi : i = v
    · rw [ite_pos hi, hi, hx]
    · rw [ite_neg hi, hf i.val (fun e => hi (Fin.ext e)) i.2, r.env]
  · have : bv.getD b 0 ≠ v := fun e => hv (e ▸ getD_mem bv (r.bvlen ▸ hb))
    show (if bv.getD b 0 = v then x else σ.env (bv.getD b 0)) = _
    rw [ite_neg this]; exact r.base b hb

theorem RelA.frame {bv R σ τ} (r : RelA bv R σ τ) {τ' : St Nat} (f : Frame 8 τ τ') : RelA bv R σ τ' :=
  ⟨fun i => (f.2 i.val i.2).trans (r.env i), r.hlen, r.bvlen, r.base, r.blen, fun b hb => by
    rw [f.1]; exact r.bytes b hb⟩

/-- the address of an in-bounds element -/
theorem RelA.addr {bv R σ τ} (r : RelA bv R σ τ) (hR : ∀ r ∈ R, r.base + r.len < 2 ^ 64) {b : Nat}
    (hb : b < σ.heap.length) {i : AExp} (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
    ∃ hbR : b < R.length, ((addrE bv b i).denote σ.env).toNat = R[b].base + (i.denote σ.env).toNat ∧
      (i.denote σ.env).toNat < R[b].len := by
  have hbR : b < R.length := r.hlen ▸ hb
  have hl := r.blen b hbR; rw [getD_get _ hb] at hl
  have := hR _ (List.getElem_mem hbR)
  refine ⟨hbR, ?_, by omega⟩
  show (σ.env (bv.getD b 0) + i.denote σ.env).toNat = _
  rw [r.base b hbR, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := R[b].base) (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- selection preserves the array-statement semantics -/
theorem irA_ok (bv : List (Fin 8)) {R : List Region} (hR : ∀ r ∈ R, r.base + r.len < 2 ^ 64)
    (hP : R.Pairwise disjoint) : ∀ {p : AStmt} {σ σ' : AState}, AExec p σ σ' → okA bv p = true →
    ∀ (τ : St Nat), RelA bv R σ τ → ∃ τ', IR.Exec (ramR R) (irA bv p) τ τ' ∧ RelA bv R σ' τ' := by
  intro p σ σ' h
  induction h with
  | @assign v e σ =>
    intro hp τ r
    obtain ⟨τ', hx, hv, hm, hf⟩ := into_ok (ram := ramR R) e v.val 0 τ (r.agree e)
    exact ⟨τ', hx, r.setVar hm (of_decide_eq_true hp) hv fun y hy h8 => hf y hy (by omega)⟩
  | @load v b i σ hb hi =>
    intro hp τ r
    obtain ⟨hv, _⟩ := Wide.and2 hp
    obtain ⟨hbR, ha, hil⟩ := r.addr hR hb hi
    obtain ⟨τ₁, x₁, v₁, m₁, f₁⟩ := into_ok (ram := ramR R) (addrE bv b i) (tk 0) 0 τ (r.agree _)
    have hB : bytes τ.mem R[b].base R[b].len = σ.heap[b].map some := by
      rw [← getD_get _ hb]; exact r.bytes b hbR
    have hbyte := get_of_bytes hB hi
    have ea : (τ₁.reg (tk 0) + 0).toNat = R[b].base + (i.denote σ.env).toNat := by
      rw [show τ₁.reg (tk 0) + 0 = τ₁.reg (tk 0) from BitVec.add_zero _, v₁, ha]
    refine ⟨_, .seq x₁ (.ins (.lbu (v := σ.heap[b][(i.denote σ.env).toNat]) ?_ ?_)), ?_⟩
    · show ramR R (τ₁.reg (tk 0) + 0).toNat
      rw [ea]; exact ⟨R[b], List.getElem_mem hbR, by omega, by omega⟩
    · show τ₁.mem (τ₁.reg (tk 0) + 0).toNat = _
      rw [ea, m₁]; exact hbyte
    · exact r.setVar (τ' := ⟨upd τ₁.reg v.val _, τ₁.mem⟩) m₁ (of_decide_eq_true hv) (upd_same _ _ _)
        fun y hy h8 => (upd_other _ _ hy).trans (f₁ y (by unfold tk; omega) (by omega))
  | @store b i e σ hb hi =>
    intro hp τ r
    obtain ⟨hbR, ha, hil⟩ := r.addr hR hb hi
    obtain ⟨τ₁, x₁, v₁, m₁, f₁⟩ := into_ok (ram := ramR R) (addrE bv b i) (tk 0) 0 τ (r.agree _)
    have g₁ : Agree σ.env e τ₁ := fun j _ => (f₁ j.val (by unfold tk; omega) (by omega)).trans (r.env j)
    obtain ⟨τ₂, x₂, v₂, f₂, _, _⟩ := opnd_ok (k := 1) (into_ok (ram := ramR R) e (tk 1) 1 τ₁ g₁) g₁
    have ea : (τ₂.reg (tk 0) + 0).toNat = R[b].base + (i.denote σ.env).toNat := by
      rw [show τ₂.reg (tk 0) + 0 = τ₂.reg (tk 0) from BitVec.add_zero _, f₂.2 (tk 0) (by unfold tk; omega), v₁, ha]
    refine ⟨_, .seq x₁ (.seq x₂ (.ins (.sb ?_))), ?_⟩
    · show ramR R (τ₂.reg (tk 0) + 0).toNat
      rw [ea]; exact ⟨R[b], List.getElem_mem hbR, by omega, by omega⟩
    · have hm : ∀ m, Mem.upd m ((Arg.r (tk 0)).eval τ₂.reg + 0).toNat = Mem.upd m (R[b].base + (i.denote σ.env).toNat) :=
        fun m => by show Mem.upd m (τ₂.reg (tk 0) + 0).toNat = _; rw [ea]
      refine ⟨fun j => (f₂.2 j.val (by omega)).trans ((f₁ j.val (by unfold tk; omega) (by omega)).trans (r.env j)),
        by rw [List.length_set, r.hlen], r.bvlen, r.base, fun b' hb' => ?_, fun b' hb' => ?_⟩
      · by_cases hbb : b' = b
        · subst hbb
          rw [getD_set_self _ _ hb, List.length_set, ← getD_get _ hb]; exact r.blen b' hb'
        · rw [getD_set_ne _ _ hbb]; exact r.blen b' hb'
      · show bytes (Mem.upd τ₂.mem _ _) _ _ = _
        rw [hm, v₂, f₂.1, m₁]
        by_cases hbb : b' = b
        · subst hbb
          rw [bytes_upd_in hil, r.bytes b' hb', getD_set_self _ _ hb, map_set, getD_get _ hb]
        · have hd := pairwise_get hP hb' hbR hbb
          unfold disjoint at hd
          rw [bytes_upd_out (fun j hj => by omega), r.bytes b' hb', getD_set_ne _ _ hbb]
  | seq _ _ iha ihb =>
    intro hp τ r
    obtain ⟨pa, pb⟩ := Wide.and2 hp
    obtain ⟨τ₁, x₁, r₁⟩ := iha pa τ r
    obtain ⟨τ₂, x₂, r₂⟩ := ihb pb τ₁ r₁
    exact ⟨τ₂, .seq x₁ x₂, r₂⟩
  | @loopF c body σ hc =>
    intro hp τ r
    obtain ⟨τ₁, x₁, f₁⟩ := loopCode_exit (ram := ramR R) (body := irA bv body) (r.agree c) hc
    exact ⟨τ₁, x₁, r.frame f₁⟩
  | @loopT c body σ _ _ hc _ _ ihb ihl =>
    intro hp τ r
    obtain ⟨τ₁, f₁, hx⟩ := loopCode_iter (ram := ramR R) (body := irA bv body) (r.agree c) hc
    obtain ⟨τ₂, x₂, r₂⟩ := ihb hp τ₁ (r.frame f₁)
    obtain ⟨τ₃, x₃, r₃⟩ := ihl hp τ₂ r₂
    exact ⟨τ₃, hx τ₂ τ₃ x₂ x₃, r₃⟩

/-- scratch register of the array pipeline -/
def scA : Reg := ⟨6, by decide⟩

/-- register assignment: variable `i ↦ avar i`, temporary `k` (virtual `8 + k`) `↦ r k` for `k < 6` -/
def fA (x : Nat) : Reg :=
  if h : x < 8 then avar ⟨x, h⟩ else if h : x < 14 then ⟨x - 8, by omega⟩ else scA

namespace Wide
variable (M : Wide)

/-- data regions: in RAM, pairwise disjoint -/
def RegOK (R : List Region) : Prop := (∀ r ∈ R, M.inRAM r.base r.len) ∧ R.Pairwise disjoint

/-- the machine state represents `σ` (as `Machine.Rel`) -/
structure RelW (bv : List (Fin 8)) (R : List Region) (σ : AState) (s : M.S) : Prop where
  env : ∀ i, M.get s (avar i) = σ.env i
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  bytes : ∀ b (hb : b < R.length), bytes (M.mem s) R[b].base R[b].len = (σ.heap[b]?.getD []).map some

/-- **The optimising array compiler** (as a function: run the statement, then return) -/
def optA (bv : List (Fin 8)) (p : AStmt) : Option (List (BitVec 32)) :=
  if okA bv p = true then M.fn scA fA [0, 1, 2, 3, 4, 5, 6, 7] (irA bv p) else none

/-- **Correctness of the optimising array compiler from the wide laws**; same conclusion as
`Machine.compAF_ok`. -/
theorem optA_ok (bv : List (Fin 8)) {p : AStmt} {ws : List (BitVec 32)} (hc : M.optA bv p = some ws)
    {R : List Region} (hR : M.RegOK R) {σ σ' : AState} (hex : AExec p σ σ') {s : M.S} {pc : BitVec 64}
    (hA : M.At s pc ws) (hcd : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * ws.length⟩ r) (hrel : M.RelW bv R σ s)
    (hra : M.retOK (M.ra s)) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ M.RelW bv R σ' s' ∧ Out R (M.mem s) (M.mem s') ∧ M.ok s' ∧
      M.keep s s' := by
  unfold optA at hc
  by_cases hk : okA bv p = true
  · rw [ite_pos hk] at hc
    have hlt := M.ramHi_lt
    have hR64 : ∀ r ∈ R, r.base + r.len < 2 ^ 64 := fun r hr => by
      have : r.base + r.len ≤ M.ramHi := (hR.1 r hr).2
      omega
    have fAv : ∀ i : Fin 8, fA i.val = avar i := by decide
    obtain ⟨τ', hx, r'⟩ := irA_ok bv hR64 hR.2 hex hk ⟨fun x => M.get s (fA x), M.mem s⟩
      ⟨fun i => (congrArg _ (fAv i)).trans (hrel.env i), hrel.hlen, hrel.bvlen, hrel.base, hrel.blen, hrel.bytes⟩
    have hram : ∀ a, ramR R a → M.inRAM a 1 := fun a ⟨r, hr, h1, h2⟩ => by
      have : M.ramLo ≤ r.base ∧ r.base + r.len ≤ M.ramHi := hR.1 r hr
      exact ⟨by omega, by omega⟩
    have hf : M.Frag (ramR R) s pc ws := ⟨hA.code, hA.codeOK, fun a ⟨r, hr, h1, h2⟩ h' => by
      have := hcd r hr; unfold disjoint at this; dsimp only at this; omega⟩
    refine M.runsTo_mono (fn_ok hram hc hA.ok hA.hpc hf hra hx) fun s' ⟨pc', v, o, m, k⟩ =>
      ⟨pc', ⟨fun i => ?_, r'.hlen, r'.bvlen, r'.base, r'.blen, fun b hb => by rw [m]; exact r'.bytes b hb⟩, ?_, o, k⟩
    · rw [← r'.env i, ← fAv i]
      exact v i.val (by revert i; decide) (by revert i; decide)
    · intro a ha
      rw [m]
      exact Exec.mem_out _ hx a fun ⟨r, hr, h1, h2⟩ => by have := ha r hr; omega
  · rw [ite_neg hk] at hc; exact nomatch hc

end Wide
end Proven.Mach
