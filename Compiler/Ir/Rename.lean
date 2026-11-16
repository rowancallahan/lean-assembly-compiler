/- The trivial allocation as a validated pass (`Testing/notes/IR_DESIGN.md` §2.4 pass 8 at its simplest): every
virtual register of `main` gets its own frame slot.  The choice `σ` (position in the list of `main`'s registers) is
untrusted; the check `injOn` (no two registers share a slot) and `noCall` make the renamed program simulate the
original step for step (`rename_sim`, a `Sim` of `Compiler/Ir/Sim.lean`), so runs and results are equal
(`rename_refines`). -/
import Compiler.Ir.Sim
import Compiler.Ir.Lin
import Compiler.Ir.EmitStep

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

/-- the registers of a function -/
def Func.locs (F : Func Nat) : List Nat := F.params ++ (F.blocks.map fun b => b.2.locs).flatten

/-- position in a list (untrusted choice of slots) -/
def idx : List Nat → Nat → Nat
  | [], _ => 0
  | v :: vs, x => if v = x then 0 else idx vs x + 1

/-- the list without repeats (untrusted) -/
def dedup (L : List Nat) : List Nat := L.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- distinct registers get distinct slots -/
def injOn (σ : Nat → Nat) (L : List Nat) : Bool := L.all fun x => L.all fun y => σ x != σ y || x == y

def Inst.isCall : Inst Nat → Bool
  | .call _ _ _ => true
  | _ => false

def noCall (F : Func Nat) : Bool := F.blocks.all fun b => b.2.body.all fun i => !i.isCall

def Func.rename (σ : Nat → Nat) (F : Func Nat) : Func Nat :=
  { F with params := F.params.map σ, blocks := F.blocks.map fun b => (b.1, b.2.map σ) }

def Prog.rename (σ : Nat → Nat) (P : Prog Nat) : Prog Nat := ⟨P.funcs.map (Func.rename σ), P.main⟩

/-- **the pass**: the renamed program, if the check passes -/
def alloc (P : Prog Nat) : Option (Prog Nat × (Nat → Nat)) :=
  match P.funcs[P.main]? with
  | some F =>
    let σ := idx (dedup F.locs)
    if injOn σ F.locs = true ∧ noCall F = true then some (P.rename σ, σ) else none
  | none => none

section
variable {σ : Nat → Nat} {L : List Nat}

theorem injOn_ok (h : injOn σ L = true) {x y : Nat} (hx : x ∈ L) (hy : y ∈ L) (e : σ x = σ y) : x = y := by
  have := List.all_eq_true.1 (List.all_eq_true.1 h x hx) y hy
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  exact this.resolve_left (fun h' => h' e)

/-- related registers: the renamed frame holds `regs x` in `σ x` for every register of `main` -/
def RelR (σ : Nat → Nat) (L : List Nat) (g g' : Nat → Val) : Prop := ∀ x ∈ L, g' (σ x) = g x

theorem RelR.upd {g g' : Nat → Val} (hσ : injOn σ L = true) (h : RelR σ L g g') {d : Nat} (hd : d ∈ L) (v : Val) :
    RelR σ L (Ir.upd g d v) (Ir.upd g' (σ d) v) := fun x hx => by
  by_cases e : x = d
  · subst e; simp [Ir.upd]
  · have : σ x ≠ σ d := fun e' => e (injOn_ok hσ hx hd e')
    simp only [Ir.upd, if_neg this, if_neg e]; exact h x hx

theorem RelR.setMany (hσ : injOn σ L = true) : ∀ {g g' : Nat → Val} (ps : List Nat) (vs : List Val),
    RelR σ L g g' → (∀ p ∈ ps, p ∈ L) → RelR σ L (Ir.setMany g ps vs) (Ir.setMany g' (ps.map σ) vs)
  | _, _, [], _, h, _ => h
  | _, _, _ :: _, [], h, _ => h
  | _, _, p :: ps, v :: vs, h, hp => RelR.setMany hσ ps vs (h.upd hσ (hp p (List.mem_cons_self ..)) v)
      fun q hq => hp q (List.mem_cons_of_mem _ hq)

theorem Arg.eval_map {g g' : Nat → Val} (h : RelR σ L g g') {a : Arg Nat} (ha : ∀ x ∈ a.locs, x ∈ L) :
    (a.map σ).eval g' = a.eval g := by
  cases a with
  | r x => exact h x (ha x (by simp [Arg.locs]))
  | i c => rfl

theorem Arg.word_map {g g' : Nat → Val} (h : RelR σ L g g') {a : Arg Nat} (ha : ∀ x ∈ a.locs, x ∈ L) :
    (a.map σ).word g' = a.word g := by
  unfold Arg.word; rw [Arg.eval_map h ha]

theorem Rhs.eval_map {g g' : Nat → Val} (h : RelR σ L g g') {m : Mem} {e : Rhs Nat}
    (he : ∀ x ∈ (Inst.let_ 0 e).locs.tail, x ∈ L) : (e.map σ).eval m g' = e.eval m g := by
  cases e with
  | arg a => simp only [Rhs.map, Rhs.eval, Arg.eval_map h (fun x hx => he x (by simpa [Inst.locs] using hx))]
  | op o a b =>
    simp only [Rhs.map, Rhs.eval, Arg.word_map h (a := a) (fun x hx => he x (by simp [Inst.locs, hx])),
      Arg.word_map h (a := b) (fun x hx => he x (by simp [Inst.locs, hx]))]
  | mop o a b =>
    simp only [Rhs.map, Rhs.eval, Arg.word_map h (a := a) (fun x hx => he x (by simp [Inst.locs, hx])),
      Arg.word_map h (a := b) (fun x hx => he x (by simp [Inst.locs, hx]))]
  | padd p i =>
    simp only [Rhs.map, Rhs.eval, h p (he p (by simp [Inst.locs])),
      Arg.word_map h (a := i) (fun x hx => he x (by simp [Inst.locs, hx]))]

/-- **one renamed instruction** does what the original does -/
theorem exec_map {g g' : Nat → Val} (hσ : injOn σ L = true) (h : RelR σ L g g') {i : Inst Nat}
    (hi : ∀ x ∈ i.locs, x ∈ L) {m : Mem} {g₁ : Nat → Val} {m₁ : Mem} {e : List MemEvent}
    (hx : i.exec m g = some (g₁, m₁, e)) :
    ∃ g₁', (i.map σ).exec m g' = some (g₁', m₁, e) ∧ RelR σ L g₁ g₁' := by
  cases i with
  | let_ d r =>
    have hd : d ∈ L := hi d (by cases r <;> simp [Inst.locs])
    have hr := Rhs.eval_map (m := m) (e := r) h (fun x hx => hi x (by cases r <;> simp_all [Inst.locs]))
    simp only [Inst.map, Inst.exec, hr] at hx ⊢
    split at hx
    · next v hv => cases hx; exact ⟨_, rfl, h.upd hσ hd v⟩
    · exact nomatch hx
  | ldb d p a =>
    have hd : d ∈ L := hi d (by simp [Inst.locs])
    have hp : g' (σ p) = g p := h p (hi p (by simp [Inst.locs]))
    have ha := Arg.word_map h (a := a) (fun x hx => hi x (by simp [Inst.locs, hx]))
    simp only [Inst.map, Inst.exec, hp, ha] at hx ⊢
    split at hx
    · next k e1 e2 =>
      (try simp only [e1, e2])
      split at hx
      · next b hb => cases hx; (try simp only [hb]); exact ⟨_, rfl, h.upd hσ hd _⟩
      · exact nomatch hx
    · next k e1 e2 =>
      (try simp only [e1, e2])
      split at hx
      · next b hb => cases hx; (try simp only [hb]); exact ⟨_, rfl, h.upd hσ hd _⟩
      · exact nomatch hx
    · exact nomatch hx
  | stb v p a =>
    have hp : g' (σ p) = g p := h p (hi p (by simp [Inst.locs]))
    have ha := Arg.word_map h (a := a) (fun x hx => hi x (by simp [Inst.locs, hx]))
    have hv := Arg.word_map h (a := v) (fun x hx => hi x (by simp [Inst.locs, hx]))
    simp only [Inst.map, Inst.exec, hp, ha, hv] at hx ⊢
    split at hx
    · next x k e1 e2 e3 => cases hx; (try simp only [e1, e2, e3]); exact ⟨_, rfl, h⟩
    · exact nomatch hx
  | ld d p k =>
    have hd : d ∈ L := hi d (by simp [Inst.locs])
    have hp : g' (σ p) = g p := h p (hi p (by simp [Inst.locs]))
    simp only [Inst.map, Inst.exec, hp] at hx ⊢
    split at hx
    · next b o e1 =>
      (try simp only [e1])
      split at hx
      · next a0 sz e2 =>
        (try simp only [e2])
        split at hx
        · next hlt =>
          (try simp only [hlt, if_true])
          split at hx
          · next v e3 => cases hx; (try simp only [e3]); exact ⟨_, rfl, h.upd hσ hd _⟩
          · exact nomatch hx
        · exact nomatch hx
      · exact nomatch hx
    · exact nomatch hx
  | st v p k =>
    have hp : g' (σ p) = g p := h p (hi p (by simp [Inst.locs]))
    have hv := Arg.eval_map h (a := v) (fun x hx => hi x (by simp [Inst.locs, hx]))
    simp only [Inst.map, Inst.exec, hp, hv] at hx ⊢
    split at hx
    · next b o e1 =>
      (try simp only [e1])
      split at hx
      · next a0 sz e2 =>
        (try simp only [e2])
        split at hx
        · next hlt => (try simp only [hlt, if_true]); cases hx; exact ⟨_, rfl, h⟩
        · exact nomatch hx
      · exact nomatch hx
    · exact nomatch hx
  | alloc d n =>
    have hd : d ∈ L := hi d (by simp [Inst.locs])
    have hn := Arg.word_map h (a := n) (fun x hx => hi x (by simp [Inst.locs, hx]))
    simp only [Inst.map, Inst.exec, hn] at hx ⊢
    split at hx
    · next c e1 => cases hx; (try simp only [e1]); exact ⟨_, rfl, h.upd hσ hd _⟩
    · exact nomatch hx
  | free p =>
    have hp : g' (σ p) = g p := h p (hi p (by simp [Inst.locs]))
    simp only [Inst.map, Inst.exec, hp] at hx ⊢
    split at hx
    · next k e1 =>
      (try simp only [e1])
      split at hx
      · next a0 sz e2 => cases hx; (try simp only [e2]); exact ⟨_, rfl, h⟩
      · exact nomatch hx
    · exact nomatch hx
  | call ds f as => exact nomatch hx

end

/-! ## The simulation -/

theorem lookup_rename (σ : Nat → Nat) : ∀ (bs : List (Lbl × Block Nat)) (l : Lbl),
    (bs.map fun b => (b.1, b.2.map σ)).lookup l = (bs.lookup l).map (Block.map σ)
  | [], _ => rfl
  | (l', B) :: bs, l => by
    simp only [List.map_cons, List.lookup_cons]
    split <;> simp_all [lookup_rename σ bs l]

theorem lookup_locs : ∀ {bs : List (Lbl × Block Nat)} {l : Lbl} {B : Block Nat}, bs.lookup l = some B →
    ∀ x ∈ B.locs, x ∈ (bs.map fun b => b.2.locs).flatten
  | [], _, _, h => nomatch h
  | (l', B') :: bs, l, B, h => by
    rw [List.lookup_cons] at h
    split at h
    · cases h; intro x hx; simp only [List.map_cons, List.flatten_cons]; exact List.mem_append_left _ hx
    · intro x hx; simp only [List.map_cons, List.flatten_cons]; exact List.mem_append_right _ (lookup_locs h x hx)

theorem lookup_mem : ∀ {bs : List (Lbl × Block Nat)} {l : Lbl} {B : Block Nat}, bs.lookup l = some B → (l, B) ∈ bs
  | [], _, _, h => nomatch h
  | (l', B') :: bs, l, B, h => by
    rw [List.lookup_cons] at h
    split at h
    · next e => cases h; simp at e; subst e; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem h)

variable {P : Prog Nat} {F : Func Nat} {σ : Nat → Nat}

/-- the relation of an original state and a renamed one -/
def RelS (P : Prog Nat) (σ : Nat → Nat) (L : List Nat) (st st' : State Nat) : Prop :=
  ∃ (l k : Nat) (g g' : Nat → Val), st.stack = [⟨P.main, l, k, g, []⟩] ∧ st'.stack = [⟨P.main, l, k, g', []⟩] ∧
    RelR σ L g g' ∧ st'.mem = st.mem ∧ st'.ev = st.ev

theorem rename_funcs (hP : P.funcs[P.main]? = some F) : (P.rename σ).funcs[P.main]? = some (F.rename σ) := by
  simp [Prog.rename, hP]

theorem jump_rename (hσ : injOn σ F.locs = true) {g g' : Nat → Val} (hR : RelR σ F.locs g g') {l k : Nat}
    {l' : Lbl} {vs : List Val} {fr₁ : Frame Nat} (h : jump F ⟨P.main, l, k, g, []⟩ l' vs = some fr₁) :
    ∃ g₁', jump (F.rename σ) ⟨P.main, l, k, g', []⟩ l' vs = some ⟨P.main, l', 0, g₁', []⟩ ∧
      RelR σ F.locs fr₁.regs g₁' ∧ fr₁ = ⟨P.main, l', 0, fr₁.regs, []⟩ := by
  obtain ⟨B, hB, hl, rfl⟩ := jump_inv h
  refine ⟨setMany g' (B.params.map σ) vs, ?_, RelR.setMany hσ _ _ hR fun p hp => ?_, rfl⟩
  · unfold jump
    rw [show (F.rename σ).blocks = F.blocks.map (fun b => (b.1, b.2.map σ)) from rfl, lookup_rename, hB]
    simp [Block.map, hl]
  · simp only [Func.locs]; exact List.mem_append_right _ (lookup_locs hB p (by simp [Block.locs, hp]))

theorem args_map {L : List Nat} {g g' : Nat → Val} (hR : RelR σ L g g') {as : List (Arg Nat)}
    (h : ∀ x ∈ (as.map Arg.locs).flatten, x ∈ L) :
    (as.map (Arg.map σ)).map (Arg.eval g') = as.map (Arg.eval g) := by
  rw [List.map_map]
  refine List.map_congr_left fun a ha => Arg.eval_map hR fun x hx => h x ?_
  exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, hx⟩

theorem term_rename (hσ : injOn σ F.locs = true) {g g' : Nat → Val} (hR : RelR σ F.locs g g') {l k : Nat}
    {m : Mem} {ev : List MemEvent} {t : Term Nat} (ht : ∀ x ∈ t.locs, x ∈ F.locs) :
    (∀ s', termStep F ⟨P.main, l, k, g, []⟩ [] m ev t = .next s' →
      ∃ s'', termStep (F.rename σ) ⟨P.main, l, k, g', []⟩ [] m ev (t.map σ) = .next s'' ∧
        RelS P σ F.locs s' s'') ∧
    (∀ r, termStep F ⟨P.main, l, k, g, []⟩ [] m ev t = .done r →
      termStep (F.rename σ) ⟨P.main, l, k, g', []⟩ [] m ev (t.map σ) = .done r) := by
  have nxt : ∀ {l' : Lbl} {vs : List Val} {fr₁ : Frame Nat}, jump F ⟨P.main, l, k, g, []⟩ l' vs = some fr₁ →
      ∃ fr₂, jump (F.rename σ) ⟨P.main, l, k, g', []⟩ l' vs = some fr₂ ∧
        RelS P σ F.locs ⟨[fr₁], m, ev⟩ ⟨[fr₂], m, ev⟩ := by
    intro l' vs fr₁ hj
    obtain ⟨g₁', hj', hR', e⟩ := jump_rename (P := P) hσ hR hj
    exact ⟨_, hj', l', 0, fr₁.regs, g₁', by rw [e], rfl, hR', rfl, rfl⟩
  cases t with
  | jmp l' as =>
    have ha := args_map hR (as := as) (by simpa [Term.locs] using ht)
    refine ⟨fun s' h => ?_, fun r h => ?_⟩
    · simp only [termStep, Term.map] at h ⊢; rw [ha]
      split at h
      · next fr₁ hj => cases h; obtain ⟨fr₂, hj', hr⟩ := nxt hj; rw [hj']; exact ⟨_, rfl, hr⟩
      · exact nomatch h
    · simp only [termStep] at h; split at h <;> exact nomatch h
  | br tt l₁ a₁ l₂ a₂ =>
    have h1 := args_map hR (as := a₁) (fun x hx => ht x (by simp [Term.locs, hx]))
    have h2 := args_map hR (as := a₂) (fun x hx => ht x (by simp [Term.locs, hx]))
    have hta := Arg.eval_map hR (a := tt.a) (fun x hx => ht x (by simp [Term.locs, hx]))
    have htb := Arg.eval_map hR (a := tt.b) (fun x hx => ht x (by simp [Term.locs, hx]))
    have htv : (tt.map σ).eval g' = tt.eval g := by simp only [Tst.eval, Tst.map, hta, htb]
    refine ⟨fun s' h => ?_, fun r h => ?_⟩
    · simp only [termStep, Term.map] at h ⊢; rw [htv, h1, h2]
      split at h
      · split at h
        · next fr₁ hj => cases h; obtain ⟨fr₂, hj', hr⟩ := nxt hj; rw [hj']; exact ⟨_, rfl, hr⟩
        · exact nomatch h
      · split at h
        · next fr₁ hj => cases h; obtain ⟨fr₂, hj', hr⟩ := nxt hj; rw [hj']; exact ⟨_, rfl, hr⟩
        · exact nomatch h
      · exact nomatch h
    · simp only [termStep] at h; (repeat' split at h) <;> exact nomatch h
  | switch x ls d =>
    have hx : g' (σ x) = g x := hR x (ht x (by simp [Term.locs]))
    refine ⟨fun s' h => ?_, fun r h => ?_⟩
    · simp only [termStep, Term.map] at h ⊢; rw [hx]
      split at h
      · split at h
        · next fr₁ hj => cases h; obtain ⟨fr₂, hj', hr⟩ := nxt hj; rw [hj']; exact ⟨_, rfl, hr⟩
        · exact nomatch h
      · exact nomatch h
    · simp only [termStep] at h; (repeat' split at h) <;> exact nomatch h
  | ret vs =>
    have hv := args_map hR (as := vs) (by simpa [Term.locs] using ht)
    refine ⟨fun s' h => (by simp only [termStep] at h; exact (nomatch h)), fun r h => ?_⟩
    simp only [termStep, Term.map] at h ⊢; rw [hv]; exact h

/-- **the renamed program simulates the original step for step** -/
def renameSim (hP : P.funcs[P.main]? = some F) (hσ : injOn σ F.locs = true) (hnc : noCall F = true) :
    Sim P (P.rename σ) where
  R := RelS P σ F.locs
  RR := Eq
  next := by
    intro st st' s' ⟨l, k, g, g', hst, hst', hR, hm, he⟩ hs
    unfold step at hs; rw [hst] at hs; simp only [hP] at hs
    cases hB : F.blocks.lookup l with
    | none => rw [hB] at hs; exact nomatch hs
    | some B =>
      rw [hB] at hs; simp only at hs
      have hBL : ∀ x ∈ B.locs, x ∈ F.locs := fun x hx => by
        simp only [Func.locs]; exact List.mem_append_right _ (lookup_locs hB x hx)
      have hB' : (F.rename σ).blocks.lookup l = some (B.map σ) := by
        rw [show (F.rename σ).blocks = F.blocks.map (fun b => (b.1, b.2.map σ)) from rfl, lookup_rename, hB]; rfl
      cases hk : B.body[k]? with
      | some i =>
        rw [hk] at hs
        have hnc' : i.isCall = false := by
          have := List.all_eq_true.1 (List.all_eq_true.1 hnc _ (lookup_mem hB)) i (List.mem_of_getElem? hk)
          simpa using this
        have hil : ∀ x ∈ i.locs, x ∈ F.locs := fun x hx => hBL x (by
          simp only [Block.locs, List.mem_append, List.mem_flatten, List.mem_map]
          exact .inl (.inr ⟨_, ⟨i, List.mem_of_getElem? hk, rfl⟩, hx⟩))
        have hk' : (B.map σ).body[k]? = some (i.map σ) := by simp [Block.map, hk]
        cases i with
        | call ds f as => simp [Inst.isCall] at hnc'
        | _ =>
          simp only at hs
          split at hs
          · next g₁ m₁ e₁ hx =>
            cases hs
            obtain ⟨g₁', hx', hR'⟩ := exec_map hσ hR hil hx
            refine ⟨1, ⟨[⟨P.main, l, k + 1, g₁', []⟩], m₁, e₁ ++ st'.ev⟩, ?_, l, k + 1, _, g₁', rfl, rfl, hR', rfl,
              by rw [he]⟩
            simp only [steps]
            unfold step; rw [hst']; simp only [rename_funcs hP, hB', hk', Inst.map]
            rw [hm]; simp only [Inst.map] at hx'; rw [hx']
          · exact nomatch hs
      | none =>
        rw [hk] at hs
        have hk' : (B.map σ).body[k]? = none := by simp [Block.map, hk]
        have hTL : ∀ x ∈ B.term.locs, x ∈ F.locs := fun x hx => hBL x (by simp [Block.locs, hx])
        have hstep' : step (P.rename σ) st' = termStep (F.rename σ) ⟨P.main, l, k, g', []⟩ [] st'.mem st'.ev
            (B.map σ).term := by
          unfold step; rw [hst']; simp only [rename_funcs hP, hB', hk']
        obtain ⟨s'', h1, h2⟩ := (term_rename (P := P) hσ hR hTL).1 s' hs
        refine ⟨1, s'', ?_, h2⟩
        simp only [steps]; rw [hstep', hm, he]; simp only [Block.map]; rw [h1]
  done := by
    intro st st' r ⟨l, k, g, g', hst, hst', hR, hm, he⟩ hs
    refine ⟨0, st', r, rfl, ?_, rfl⟩
    unfold step at hs; rw [hst] at hs; simp only [hP] at hs
    cases hB : F.blocks.lookup l with
    | none => rw [hB] at hs; exact nomatch hs
    | some B =>
      rw [hB] at hs; simp only at hs
      have hBL : ∀ x ∈ B.locs, x ∈ F.locs := fun x hx => by
        simp only [Func.locs]; exact List.mem_append_right _ (lookup_locs hB x hx)
      have hB' : (F.rename σ).blocks.lookup l = some (B.map σ) := by
        rw [show (F.rename σ).blocks = F.blocks.map (fun b => (b.1, b.2.map σ)) from rfl, lookup_rename, hB]; rfl
      cases hk : B.body[k]? with
      | some i =>
        rw [hk] at hs
        cases i with
        | call ds f as => simp only at hs; split at hs <;> (try split at hs) <;> exact nomatch hs
        | _ => simp only at hs; split at hs <;> exact nomatch hs
      | none =>
        rw [hk] at hs
        have hk' : (B.map σ).body[k]? = none := by simp [Block.map, hk]
        have hTL : ∀ x ∈ B.term.locs, x ∈ F.locs := fun x hx => hBL x (by simp [Block.locs, hx])
        unfold step; rw [hst']; simp only [rename_funcs hP, hB', hk']
        rw [hm, he]; simp only [Block.map]
        exact (term_rename (P := P) hσ hR hTL).2 r hs

end Proven.Ir

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc

theorem rename_init {P : Prog Nat} {F : Func Nat} {σ : Nat → Nat} (hP : P.funcs[P.main]? = some F)
    (hσ : injOn σ F.locs = true) (input : List UInt8) :
    RelS P σ F.locs (init P input) (init (P.rename σ) input) := by
  have h1 : init P input = ⟨[⟨P.main, F.entry, 0, setMany (fun _ => .w 0) F.params
      [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0], []⟩], Mem.init input, []⟩ := by unfold init; rw [hP]
  have h2 : init (P.rename σ) input = ⟨[⟨P.main, F.entry, 0, setMany (fun _ => .w 0) (F.params.map σ)
      [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0], []⟩], Mem.init input, []⟩ := by
    unfold init; rw [show (P.rename σ).main = P.main from rfl, rename_funcs hP]; rfl
  rw [h1, h2]
  exact ⟨F.entry, 0, _, _, rfl, rfl, RelR.setMany hσ _ _ (fun _ _ => rfl)
    (fun p hp => List.mem_append_left _ hp), rfl, rfl⟩

/-- **the pass preserves runs and results** -/
theorem alloc_runs {P Q : Prog Nat} {σ : Nat → Nat} (h : alloc P = some (Q, σ)) {input : List UInt8} {r : Result}
    (hr : Runs P (init P input) r) : Runs Q (init Q input) r := by
  unfold alloc at h
  split at h
  · next F hP =>
    simp only at h
    split at h
    · next hc =>
      cases h
      obtain ⟨r', h', e⟩ := (renameSim hP hc.1 hc.2).refines (rename_init hP hc.1 input) r hr
      subst e; exact h'
    · exact nomatch h
  · exact nomatch h

theorem alloc_main {P Q : Prog Nat} {σ : Nat → Nat} (h : alloc P = some (Q, σ)) : Q.main = P.main := by
  unfold alloc at h
  split at h
  · simp only at h; split at h
    · cases h; rfl
    · exact nomatch h
  · exact nomatch h

end Proven.Ir
