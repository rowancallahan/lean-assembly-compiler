/- The simulation of a Lin run by the machine, with calls: the relation `Rel` (the top frame at an instruction of a
block, the machine at that instruction's code with the relation `MR` of the frame; the suspended frames below it
in memory, each at the code after its call, `Stk`), one step (`step_ok`) and the end of the run (`done_ok`). -/
import Compiler.Ir.EmitJump

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

section
variable {P : Prog Nat} {st : State Nat} {fr : Frame Nat} {rest : List (Frame Nat)} {F : Func Nat} {B : Block Nat}

theorem step_inst (hst : st.stack = fr :: rest) (hP : P.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    {i : Inst Nat} (hk : B.body[fr.pc]? = some i) (hi : ∀ ds g as, i ≠ .call ds g as) :
    step P st = match i.exec st.mem fr.regs with
      | some (g', m', e) => .next ⟨{ fr with pc := fr.pc + 1, regs := g' } :: rest, m', e ++ st.ev⟩
      | none => .stuck := by
  unfold step; rw [hst]; simp only [hP, hB, hk]
  cases i with
  | call ds g as => exact absurd rfl (hi ds g as)
  | _ => (rcases hx : Inst.exec _ _ _ with _ | ⟨g', m', e⟩) <;> simp only

theorem step_call (hst : st.stack = fr :: rest) (hP : P.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    {ds : List Nat} {g : FId} {as : List (Arg Nat)} (hk : B.body[fr.pc]? = some (.call ds g as)) {G : Func Nat}
    (hG : P.funcs[g]? = some G) (hl : as.length = G.params.length) :
    step P st = .next ⟨⟨g, G.entry, 0, setMany (fun _ => .w 0) G.params (as.map (Arg.eval fr.regs)), ds⟩ ::
            { fr with pc := fr.pc + 1 } :: rest, st.mem, .alloc (G.slots + 1) :: st.ev⟩ := by
  unfold step; rw [hst]; simp only [hP, hB, hk, hG, hl, if_true]

theorem step_call_inv (hst : st.stack = fr :: rest) (hP : P.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    {ds : List Nat} {g : FId} {as : List (Arg Nat)} (hk : B.body[fr.pc]? = some (.call ds g as)) {st' : State Nat}
    (h : step P st = .next st') : ∃ G, P.funcs[g]? = some G ∧ as.length = G.params.length ∧
      st' = ⟨⟨g, G.entry, 0, setMany (fun _ => .w 0) G.params (as.map (Arg.eval fr.regs)), ds⟩ ::
            { fr with pc := fr.pc + 1 } :: rest, st.mem, .alloc (G.slots + 1) :: st.ev⟩ := by
  unfold step at h; rw [hst] at h; simp only [hP, hB, hk] at h
  split at h
  · next G hG =>
    split at h
    · next hl => cases h; exact ⟨G, hG, hl, rfl⟩
    · exact nomatch h
  · exact nomatch h

theorem step_term (hst : st.stack = fr :: rest) (hP : P.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    (hk : B.body[fr.pc]? = none) : step P st = termStep F fr rest st.mem st.ev B.term := by
  unfold step; rw [hst]; simp only [hP, hB, hk]

end

theorem inUse_append_allocs : ∀ (E L : List MemEvent), Allocs E → inUse (E ++ L) = inUse E + inUse L
  | [], L, _ => by simp [inUse]
  | .alloc n :: E, L, h => by
    show inUse (E ++ L) + n = inUse E + n + inUse L
    rw [inUse_append_allocs E L fun e he => h e (List.mem_cons_of_mem _ he)]; omega
  | .free n :: E, _, h => by obtain ⟨_, e⟩ := h _ (List.mem_cons_self ..); exact nomatch e

/-- the code of a function of the program -/
structure CodeF {T : Target} (C : Ctx T) (Q : Prog Nat) (L : Lay) (f : FId) (F : Func Nat) : Prop where
  nsl : F.slots ≤ T.maxSlots
  big : 8 * (F.slots + 1) < 2 ^ 64
  p7 : F.params.length ≤ 7
  ps : ∀ p ∈ F.params, p < F.slots
  ent : ∃ B, F.blocks.lookup F.entry = some B
  pro : ∃ j rest, T.jTo ((Q.env L).fq f + T.len (Target.proF F.slots F)) (L.posF f F.entry) = some j ∧
    InW C.W ((Q.env L).fq f) (T.words (Target.proF F.slots F ++ j) ++ rest)
  blocks : ∀ l B, F.blocks.lookup l = some B → ∃ c ct,
    T.emitIs (Q.env L) F.slots L.ex (L.posF f l) B.body = some c ∧
    T.emitT F F.slots (L.posF f) (L.posF f l + T.len c) B.term = some ct ∧ InW C.W (L.posF f l) (T.words (c ++ ct))

/-- the code of the program: its functions, the exit, the stub's code after the call of `main` (at `qs`) -/
structure Code {T : Target} (C : Ctx T) (Q : Prog Nat) (L : Lay) (qs : Nat) : Prop where
  fn : ∀ f F, Q.funcs[f]? = some F → CodeF C Q L f F
  exit : ∃ rest, InW C.W L.ex (T.encO .exit ++ rest)
  stub : ∃ rest, InW C.W qs (T.words (Target.stub3) ++ rest)

namespace Ctx
variable {T : Target} (C : Ctx T)

/-- **the suspended frames** `fs` (innermost first) below a frame at `fbA` with `nA` slots, return address `svA`,
destination `dA`, function `gA`; `M` the memory above that frame (as it must stay); `bl` the block table -/
def Stk (Q : Prog Nat) (L : Lay) (qs : Nat) (bl : List (Nat × Nat × Bool)) :
    List (Frame Nat) → (Nat → Option (BitVec 8)) → Nat → Nat → BitVec 64 → List Nat → FId → Prop
  | [], M, fbA, nA, svA, dA, gA => fbA + 8 * (nA + 1) + 16 = C.T0 ∧ svA = next C.pc0 qs ∧ dA = [] ∧ gA = Q.main ∧
      bytes M (C.T0 - 8) 8 = (le8 (T.fr C.s0)).map some
  | c :: fs, M, fbA, nA, svA, dA, gA => ∃ (F : Func Nat) (B : Block Nat) (as : List (Arg Nat)) (qr : Nat)
      (cr ct : List EOp) (Mc : Nat → Option (BitVec 8)) (svc : BitVec 64),
      Q.funcs[c.f]? = some F ∧ F.blocks.lookup c.l = some B ∧ 1 ≤ c.pc ∧
      B.body[c.pc - 1]? = some (.call dA gA as) ∧ dA.length ≤ 7 ∧ (∀ d ∈ dA, d < F.slots) ∧
      nA = (Q.env L).fs gA ∧ svA = next C.pc0 qr ∧
      T.emitIs (Q.env L) F.slots L.ex (qr + T.len (Target.callPost nA dA)) (B.body.drop c.pc) = some cr ∧
      T.emitT F F.slots (L.posF c.f) (qr + T.len (Target.callPost nA dA) + T.len cr) B.term = some ct ∧
      InW C.W qr (T.words (Target.callPost nA dA ++ cr ++ ct)) ∧
      (C.fa F.slots (fbA + 8 * (nA + 1)) svc Mc).Snap ⟨[], [], [], bl⟩ c.regs M ∧ (∀ j, Valid bl (c.regs j)) ∧
      Stk Q L qs bl fs Mc (fbA + 8 * (nA + 1)) F.slots svc c.dst c.f

/-- the frame cells: the stub's two, then every frame -/
def base (Q : Prog Nat) : MemEvent := .alloc (((Q.funcs[Q.main]?).map (·.slots)).getD 0 + 3)

/-- **the relation** of a Lin state and a machine state -/
def Rel (Q : Prog Nat) (L : Lay) (qs : Nat) (st : State Nat) (s : T.S) : Prop :=
  ∃ (fr : Frame Nat) (below : List (Frame Nat)) (F : Func Nat) (B : Block Nat) (fb : Nat) (sv : BitVec 64)
    (M : Nat → Option (BitVec 8)) (q : Nat) (c ct : List EOp),
    st.stack = fr :: below ∧ Q.funcs[fr.f]? = some F ∧ F.blocks.lookup fr.l = some B ∧
    T.emitIs (Q.env L) F.slots L.ex q (B.body.drop fr.pc) = some c ∧
    T.emitT F F.slots (L.posF fr.f) (q + T.len c) B.term = some ct ∧ InW C.W q (T.words (c ++ ct)) ∧
    C.AtQ s q ∧ (C.fa F.slots fb sv M).MR st.mem fr.regs s ∧
    C.Stk Q L qs st.mem.blks below M fb F.slots sv fr.dst fr.f ∧
    inUse (st.ev ++ [base Q]) = st.mem.cells.length + (C.T0 - fb) / 8 ∧ peak (st.ev ++ [base Q]) ≤ C.wl / 8

/-- the end of a run: returned, and either the output is there or the flag (exactly when out of memory) -/
def Fin (Q : Prog Nat) (r : Result) (s' : T.S) : Prop :=
  T.ok s' ∧ T.pcIs s' (T.ra C.s0) ∧ C.Unch s' ∧
  ((peak (r.ev ++ [base Q]) ≤ C.wl / 8 ∧ T.get s' RIn = BitVec.ofNat 64 C.inA ∧
      ∀ i b, r.mem.out[i]? = some (some b) → T.mem s' (C.outA + i) = some b.toBitVec) ∨
    (C.wl / 8 < peak (r.ev ++ [base Q]) ∧ T.get s' RIn = BitVec.allOnes 64))

variable {C}

theorem retOK_at {q : Nat} {ws : List (BitVec 32)} (h : InW C.W q ws) : T.retOK (next C.pc0 q) := by
  obtain ⟨pre, post, e, hl⟩ := h
  have hq : q ≤ C.W.length := by rw [e]; simp [hl]
  apply T.retOK_al
  rw [T.toCore.pc_toNat C.codeOK hq]
  have := C.codeOK.1; omega


theorem fa_F0 {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).F0 = fb := rfl
theorem fa_nS {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).nS = n := rfl
theorem fa_sv {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).sv = v := rfl
theorem fa_hm {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).hm = M := rfl
theorem fa_T0 {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).T0 = C.T0 := rfl
theorem fa_wb {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).wb = C.wb := rfl
theorem fa_wl {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).wl = C.wl := rfl
theorem fa_W {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).W = C.W := rfl
theorem fa_pc0 {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).pc0 = C.pc0 := rfl
theorem fa_repr {n fb : Nat} {v : BitVec 64} {M : Nat → Option (BitVec 8)} : (C.fa n fb v M).repr = C.repr := rfl

theorem Snap.ext {C' : Ctx T} {bl : List (Nat × Nat × Bool)} {regs : Nat → Val} {M : Nat → Option (BitVec 8)}
    (h : C'.Snap ⟨[], [], [], bl⟩ regs M) (hv : ∀ j, Valid bl (regs j)) (X : List (Nat × Nat × Bool)) :
    C'.Snap ⟨[], [], [], bl ++ X⟩ regs M :=
  ⟨fun j hj => by have := h.slots j hj; simp only at this ⊢; rw [C'.repr_ext X (hv j)]; exact this, h.saved, h.above⟩

theorem Snap.blks {C' : Ctx T} {m : Mem} {regs : Nat → Val} {M : Nat → Option (BitVec 8)} :
    C'.Snap m regs M ↔ C'.Snap ⟨[], [], [], m.blks⟩ regs M :=
  ⟨fun h => ⟨h.slots, h.saved, h.above⟩, fun h => ⟨h.slots, h.saved, h.above⟩⟩

theorem Snap.congr {C' : Ctx T} {m : Mem} {regs : Nat → Val} {M M' : Nat → Option (BitVec 8)}
    (h : C'.Snap m regs M) (hfit : C'.F0 + 8 * (C'.nS + 1) ≤ C'.T0) (he : ∀ x, C'.F0 ≤ x → x < C'.T0 → M' x = M x) :
    C'.Snap m regs M' :=
  ⟨fun j hj => by rw [← h.slots j hj]; exact bytes_congr fun i hi => he _ (by omega) (by omega),
   by rw [← h.saved]; exact bytes_congr fun i hi => he _ (by omega) (by omega),
   fun x h1 h2 => by rw [he x (by omega) h2]; exact h.above x h1 h2⟩

theorem Stk.ext {Q : Prog Nat} {L : Lay} {qs : Nat} {bl : List (Nat × Nat × Bool)} (X : List (Nat × Nat × Bool)) :
    ∀ {fs : List (Frame Nat)} {M : Nat → Option (BitVec 8)} {fbA nA : Nat} {svA : BitVec 64} {dA : List Nat} {gA : FId},
    C.Stk Q L qs bl fs M fbA nA svA dA gA → C.Stk Q L qs (bl ++ X) fs M fbA nA svA dA gA
  | [], _, _, _, _, _, _, h => h
  | _ :: _, _, _, _, _, _, _, ⟨F, B, as, qr, cr, ct, Mc, svc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ =>
    ⟨F, B, as, qr, cr, ct, Mc, svc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12.ext h13 X,
      fun j => Valid.ext X (h13 j), Stk.ext X h14⟩

theorem Stk.fit {Q : Prog Nat} {L : Lay} {qs : Nat} {bl : List (Nat × Nat × Bool)} :
    ∀ {fs : List (Frame Nat)} {M : Nat → Option (BitVec 8)} {fbA nA : Nat} {svA : BitVec 64} {dA : List Nat} {gA : FId},
    C.Stk Q L qs bl fs M fbA nA svA dA gA → fbA + 8 * (nA + 1) + 16 ≤ C.T0
  | [], _, _, _, _, _, _, h => by have := h.1; omega
  | _ :: _, _, _, _, _, _, _, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h14⟩ => by
    have := Stk.fit h14; omega

theorem peak_cons_le {e : MemEvent} {L : List MemEvent} {W : Nat} (h1 : inUse (e :: L) ≤ W) (h2 : peak L ≤ W) :
    peak (e :: L) ≤ W := by
  show max (inUse (e :: L)) (peak L) ≤ W; omega

theorem exec_blks {m : Mem} {g : Nat → Val} {i : Inst Nat} {g' : Nat → Val} {m' : Mem} {e : List MemEvent}
    (h : i.exec m g = some (g', m', e)) (hi : ∀ p, i ≠ .free p) : ∃ X, m'.blks = m.blks ++ X := by
  cases i with
  | let_ d r => simp only [Inst.exec] at h; split at h <;> cases h; exact ⟨[], by simp⟩
  | ldb d p x => simp only [Inst.exec] at h; (repeat' split at h) <;> cases h <;> exact ⟨[], by simp⟩
  | stb v p x => simp only [Inst.exec] at h; split at h <;> cases h; exact ⟨[], by simp⟩
  | ld d p k => simp only [Inst.exec] at h; (repeat' split at h) <;> cases h <;> exact ⟨[], by simp⟩
  | st v p k => simp only [Inst.exec] at h; (repeat' split at h) <;> cases h <;> exact ⟨[], by simp⟩
  | alloc d n => simp only [Inst.exec] at h; split at h <;> cases h; exact ⟨_, rfl⟩
  | free p => exact absurd rfl (hi p)
  | call ds f as => exact nomatch h

end Ctx
end Proven.Ir
