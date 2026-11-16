/- The trivial allocation as a validated pass (`Testing/notes/IR_DESIGN.md` §2.4 pass 8 at its simplest): every
virtual register of every function gets its own frame slot (`alloc`, `Compiler/Ir/Lin.lean`).  The choice (position
in the list of the function's registers) is untrusted; the check (every register in the list, distinct registers
of the list in distinct slots) makes the renamed program simulate the original step for step, frame by frame, with
calls (`renameSim`, a `Sim` of `Compiler/Ir/Sim.lean`), so runs give the same values and memory (`alloc_runs`).
Only the memory events differ: the renamed functions have their slot counts, so their frames have sizes. -/
import Compiler.Ir.Sim
import Compiler.Ir.Lin

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

section
variable {σ : Nat → Nat} {L : List Nat}

/-- distinct registers of `L` get distinct slots -/
def InjOn (σ : Nat → Nat) (L : List Nat) : Prop := ∀ x ∈ L, ∀ y ∈ L, σ x = σ y → x = y

theorem injOn_ok (h : InjOn σ L) {x y : Nat} (hx : x ∈ L) (hy : y ∈ L) (e : σ x = σ y) : x = y := h x hx y hy e

theorem injOn_of {D : List Nat} (h : injOn σ D = true) (hL : L.all (fun x => D.contains x) = true) : InjOn σ L :=
  fun x hx y hy e => by
    have hxD : x ∈ D := by simpa using List.all_eq_true.1 hL x hx
    have hyD : y ∈ D := by simpa using List.all_eq_true.1 hL y hy
    have := List.all_eq_true.1 (List.all_eq_true.1 h x hxD) y hyD
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
    exact this.resolve_left (fun h' => h' e)

/-- related registers: the renamed frame holds `regs x` in `σ x` for every register of `main` -/
def RelR (σ : Nat → Nat) (L : List Nat) (g g' : Nat → Val) : Prop := ∀ x ∈ L, g' (σ x) = g x

theorem RelR.upd {g g' : Nat → Val} (hσ : InjOn σ L) (h : RelR σ L g g') {d : Nat} (hd : d ∈ L) (v : Val) :
    RelR σ L (Ir.upd g d v) (Ir.upd g' (σ d) v) := fun x hx => by
  by_cases e : x = d
  · subst e; simp [Ir.upd]
  · have : σ x ≠ σ d := fun e' => e (injOn_ok hσ hx hd e')
    simp only [Ir.upd, if_neg this, if_neg e]; exact h x hx

theorem RelR.setMany (hσ : InjOn σ L) : ∀ {g g' : Nat → Val} (ps : List Nat) (vs : List Val),
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
theorem exec_map {g g' : Nat → Val} (hσ : InjOn σ L) (h : RelR σ L g g') {i : Inst Nat}
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

/-- the slot choice of a function -/
def Func.σ (F : Func Nat) : Nat → Nat := idx (dedup F.locs)

/-- the renamed function -/
def Func.ren (F : Func Nat) : Func Nat := { F.rename F.σ with slots := (dedup F.locs).length }

theorem alloc1_inv {F F' : Func Nat} (h : F.alloc1 = some F') : F' = F.ren ∧ InjOn F.σ F.locs := by
  unfold Func.alloc1 Func.allocD at h
  split at h
  · next hc => cases h; exact ⟨rfl, injOn_of hc.2 hc.1⟩
  · exact nomatch h

theorem mapM_inv {α β : Type} {f : α → Option β} : ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
    ∀ i : Nat, (∀ x, l[i]? = some x → ∃ y, f x = some y ∧ l'[i]? = some y) ∧ (l[i]? = none → l'[i]? = none)
  | [], l', h, i => by simp at h; subst h; simp
  | x :: xs, l', h, i => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some ys =>
        simp [hx, hxs] at h; subst h
        cases i with
        | zero => exact ⟨fun z hz => by simp at hz; subst hz; exact ⟨y, hx, rfl⟩, fun h => by simp at h⟩
        | succ i => simpa using mapM_inv hxs i

theorem alloc_inv {P Q : Prog Nat} (h : alloc P = some Q) : Q.main = P.main ∧
    ∀ f : FId, (∀ F : Func Nat, P.funcs[f]? = some F → Q.funcs[f]? = some F.ren ∧ InjOn F.σ F.locs) ∧
      (P.funcs[f]? = none → Q.funcs[f]? = none) := by
  unfold alloc at h
  cases hm : P.funcs.mapM Func.alloc1 with
  | none => rw [hm] at h; exact nomatch h
  | some fs =>
    rw [hm] at h; cases h
    refine ⟨rfl, fun f => ⟨fun F hF => ?_, (mapM_inv hm f).2⟩⟩
    obtain ⟨F', h1, h2⟩ := (mapM_inv hm f).1 F hF
    obtain ⟨rfl, hi⟩ := alloc1_inv h1
    exact ⟨h2, hi⟩

theorem locs_of_block {F : Func Nat} {l : Lbl} {B : Block Nat} (hB : F.blocks.lookup l = some B) :
    ∀ x ∈ B.locs, x ∈ F.locs := fun x hx => by
  simp only [Func.locs]; exact List.mem_append_right _ (lookup_locs hB x hx)

theorem ren_lookup {F : Func Nat} {l : Lbl} {B : Block Nat} (hB : F.blocks.lookup l = some B) :
    F.ren.blocks.lookup l = some (B.map F.σ) := by
  rw [show F.ren.blocks = F.blocks.map (fun b => (b.1, b.2.map F.σ)) from rfl, lookup_rename, hB]; rfl

theorem ren_lookup_none {F : Func Nat} {l : Lbl} (hB : F.blocks.lookup l = none) : F.ren.blocks.lookup l = none := by
  rw [show F.ren.blocks = F.blocks.map (fun b => (b.1, b.2.map F.σ)) from rfl, lookup_rename, hB]; rfl

variable {P Q : Prog Nat}

/-- related frames: same function, block, position; registers renamed -/
def RelF (P : Prog Nat) (fr fr' : Frame Nat) : Prop :=
  fr'.f = fr.f ∧ fr'.l = fr.l ∧ fr'.pc = fr.pc ∧ ∃ F, P.funcs[fr.f]? = some F ∧ RelR F.σ F.locs fr.regs fr'.regs

/-- related destinations: the caller's registers renamed -/
def RelD (P : Prog Nat) (fr fr' : Frame Nat) : List (Frame Nat) → Prop
  | [] => True
  | c :: _ => ∃ Fc, P.funcs[c.f]? = some Fc ∧ fr'.dst = fr.dst.map Fc.σ ∧ ∀ x ∈ fr.dst, x ∈ Fc.locs

def RelStk (P : Prog Nat) : List (Frame Nat) → List (Frame Nat) → Prop
  | [], [] => True
  | fr :: rest, fr' :: rest' => RelF P fr fr' ∧ RelD P fr fr' rest ∧ RelStk P rest rest'
  | _, _ => False

/-- the relation of an original state and a renamed one -/
def RelS (P : Prog Nat) (st st' : State Nat) : Prop := RelStk P st.stack st'.stack ∧ st'.mem = st.mem

theorem args_map {σ : Nat → Nat} {L : List Nat} {g g' : Nat → Val} (hR : RelR σ L g g') {as : List (Arg Nat)}
    (h : ∀ x ∈ (as.map Arg.locs).flatten, x ∈ L) :
    (as.map (Arg.map σ)).map (Arg.eval g') = as.map (Arg.eval g) := by
  rw [List.map_map]
  refine List.map_congr_left fun a ha => Arg.eval_map hR fun x hx => h x ?_
  exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, hx⟩

theorem RelR.zero (σ : Nat → Nat) (L : List Nat) : RelR σ L (fun _ => .w 0) (fun _ => .w 0) := fun _ _ => rfl


theorem jump_ren {F : Func Nat} (hσ : InjOn F.σ F.locs) {fr fr' : Frame Nat} {l : Lbl} {vs : List Val}
    {fr₁ : Frame Nat} (hR : RelR F.σ F.locs fr.regs fr'.regs) (h : jump F fr l vs = some fr₁) :
    ∃ g', jump F.ren fr' l vs = some { fr' with l := l, pc := 0, regs := g' } ∧
      fr₁ = { fr with l := l, pc := 0, regs := fr₁.regs } ∧ RelR F.σ F.locs fr₁.regs g' := by
  unfold jump at h
  split at h
  · next B hB =>
    split at h
    · next hl =>
      cases h
      refine ⟨setMany fr'.regs (B.params.map F.σ) vs, ?_, rfl, RelR.setMany hσ _ _ hR fun p hp =>
        locs_of_block hB p (by simp [Block.locs, hp])⟩
      unfold jump; rw [ren_lookup hB]; simp [Block.map, hl]
    · exact nomatch h
  · exact nomatch h

/-- a terminator other than `ret`, renamed -/
theorem term_ren {F : Func Nat} (hσ : InjOn F.σ F.locs) {fr fr' : Frame Nat} {rest rest' : List (Frame Nat)}
    {m : Mem} {ev ev' : List MemEvent} {t : Term Nat} (hR : RelR F.σ F.locs fr.regs fr'.regs)
    (ht : ∀ x ∈ t.locs, x ∈ F.locs) (hnr : ∀ vs, t ≠ .ret vs) {s : State Nat}
    (h : termStep F fr rest m ev t = .next s) :
    ∃ l g g', s = ⟨{ fr with l := l, pc := 0, regs := g } :: rest, m, ev⟩ ∧
      termStep F.ren fr' rest' m ev' (t.map F.σ) = .next ⟨{ fr' with l := l, pc := 0, regs := g' } :: rest', m, ev'⟩ ∧
      RelR F.σ F.locs g g' := by
  cases t with
  | jmp l' as =>
    have ha := args_map hR (as := as) (by simpa [Term.locs] using ht)
    simp only [termStep, Term.map] at h ⊢; rw [ha]
    split at h
    · next fr₁ hj => exact (by
          obtain ⟨g', hj', e, hR'⟩ := jump_ren hσ hR hj
          injection h with h
          exact ⟨_, fr₁.regs, g', by rw [← h, e], by rw [hj'], hR'⟩)
    · exact nomatch h
  | br tt l₁ a₁ l₂ a₂ =>
    have h1 := args_map hR (as := a₁) (fun x hx => ht x (by simp [Term.locs, hx]))
    have h2 := args_map hR (as := a₂) (fun x hx => ht x (by simp [Term.locs, hx]))
    have hta := Arg.eval_map hR (a := tt.a) (fun x hx => ht x (by simp [Term.locs, hx]))
    have htb := Arg.eval_map hR (a := tt.b) (fun x hx => ht x (by simp [Term.locs, hx]))
    have htv : (tt.map F.σ).eval fr'.regs = tt.eval fr.regs := by simp only [Tst.eval, Tst.map, hta, htb]
    simp only [termStep, Term.map] at h ⊢; rw [htv, h1, h2]
    split at h
    · split at h
      · next fr₁ hj => exact (by
          obtain ⟨g', hj', e, hR'⟩ := jump_ren hσ hR hj
          injection h with h
          exact ⟨_, fr₁.regs, g', by rw [← h, e], by rw [hj'], hR'⟩)
      · exact nomatch h
    · split at h
      · next fr₁ hj => exact (by
          obtain ⟨g', hj', e, hR'⟩ := jump_ren hσ hR hj
          injection h with h
          exact ⟨_, fr₁.regs, g', by rw [← h, e], by rw [hj'], hR'⟩)
      · exact nomatch h
    · exact nomatch h
  | switch x ls d =>
    have hx : fr'.regs (F.σ x) = fr.regs x := hR x (ht x (by simp [Term.locs]))
    simp only [termStep, Term.map] at h ⊢; rw [hx]
    split at h
    · split at h
      · next fr₁ hj => exact (by
          obtain ⟨g', hj', e, hR'⟩ := jump_ren hσ hR hj
          injection h with h
          exact ⟨_, fr₁.regs, g', by rw [← h, e], by rw [hj'], hR'⟩)
      · exact nomatch h
    · exact nomatch h
  | ret vs => exact absurd rfl (hnr vs)

theorem steps_one {Q : Prog Nat} {t t' : State Nat} (h : step Q t = .next t') : steps Q 1 t = some t' := by
  simp only [steps, h]

/-- **the renamed program simulates the original step for step** -/
def renameSim (hQ : alloc P = some Q) : Sim P Q where
  R := RelS P
  RR r r' := r'.vs = r.vs ∧ r'.mem = r.mem
  next := by
    intro st st' s' ⟨hstk, hm⟩ hs
    obtain ⟨hmain, hfun⟩ := alloc_inv hQ
    unfold step at hs
    rcases hst : st.stack with _ | ⟨fr, rest⟩
    · rw [hst] at hs; exact nomatch hs
    rcases hst' : st'.stack with _ | ⟨fr', rest'⟩
    · rw [hst, hst'] at hstk; exact absurd hstk (by simp [RelStk])
    rw [hst, hst'] at hstk
    obtain ⟨⟨hf, hl, hpc, F, hF, hR⟩, hD, hrest⟩ := hstk
    rw [hst] at hs; simp only [hF] at hs
    obtain ⟨hQF, hσ⟩ := (hfun fr.f).1 F hF
    cases hB : F.blocks.lookup fr.l with
    | none => rw [hB] at hs; exact nomatch hs
    | some B =>
    rw [hB] at hs; simp only at hs
    have hBL := locs_of_block hB
    have hQB : F.ren.blocks.lookup fr'.l = some (B.map F.σ) := by rw [hl]; exact ren_lookup hB
    cases hk : B.body[fr.pc]? with
    | some i =>
      have hil : ∀ x ∈ i.locs, x ∈ F.locs := fun x hx => hBL x (by
        simp only [Block.locs, List.mem_append, List.mem_flatten, List.mem_map]
        exact .inl (.inr ⟨_, ⟨i, List.mem_of_getElem? hk, rfl⟩, hx⟩))
      have hk' : (B.map F.σ).body[fr'.pc]? = some (i.map F.σ) := by rw [hpc]; simp [Block.map, hk]
      rw [hk] at hs
      cases i with
      | call ds g as =>
        simp only at hs
        cases hG : P.funcs[g]? with
        | none => rw [hG] at hs; exact nomatch hs
        | some G =>
        rw [hG] at hs; simp only at hs
        split at hs
        case isFalse => exact nomatch hs
        rename_i hlen
        cases hs
        obtain ⟨hQG, hσG⟩ := (hfun g).1 G hG
        have ha := args_map hR (as := as) (fun x hx => hil x (by simp [Inst.locs, hx]))
        refine ⟨1, ⟨⟨g, G.entry, 0, setMany (fun _ => .w 0) (G.params.map G.σ)
            ((as.map (Arg.map F.σ)).map (Arg.eval fr'.regs)), ds.map F.σ⟩ :: { fr' with pc := fr'.pc + 1 } :: rest',
            st'.mem, .alloc (G.ren.slots + 1) :: st'.ev⟩, steps_one ?_, ?_⟩
        · unfold step; rw [hst']; simp only [hf, hQF, hQB, hk', Inst.map, hQG]
          rw [if_pos (by simp [Func.ren, Func.rename, hlen])]; rfl
        · refine ⟨⟨⟨rfl, rfl, rfl, G, hG, ?_⟩, ⟨F, hF, rfl, fun x hx => hil x (by simp [Inst.locs, hx])⟩,
            ⟨by simpa using hf, by simpa using hl, by simpa using hpc, F, hF, hR⟩, hD, hrest⟩, ?_⟩
          · show RelR G.σ G.locs _ (setMany (fun _ => .w 0) (G.params.map G.σ) ((as.map (Arg.map F.σ)).map (Arg.eval fr'.regs)))
            rw [ha]
            exact RelR.setMany hσG _ _ (RelR.zero _ _) fun p hp => by simp only [Func.locs]; exact List.mem_append_left _ hp
          · exact hm
      | _ =>
        simp only at hs
        split at hs
        · next g₁ m₁ e₁ hx =>
          cases hs
          obtain ⟨g₁', hx', hR'⟩ := exec_map hσ hR hil (hm ▸ hx)
          refine ⟨1, ⟨{ fr' with pc := fr'.pc + 1, regs := g₁' } :: rest', m₁, e₁ ++ st'.ev⟩, steps_one ?_,
            ⟨⟨by simpa using hf, by simpa using hl, by simp [hpc], F, hF, hR'⟩, hD, hrest⟩, rfl⟩
          unfold step; rw [hst']; simp only [hf, hQF, hQB, hk']
          simp only [Inst.map] at hx' ⊢; rw [hx']
        · exact nomatch hs
    | none =>
      rw [hk] at hs
      have hk' : (B.map F.σ).body[fr'.pc]? = none := by rw [hpc]; simp [Block.map, hk]
      have hTL : ∀ x ∈ B.term.locs, x ∈ F.locs := fun x hx => hBL x (by simp [Block.locs, hx])
      have hQs : step Q st' = termStep F.ren fr' rest' st'.mem st'.ev (B.map F.σ).term := by
        unfold step; rw [hst']; simp only [hf, hQF, hQB, hk']
      cases ht : B.term with
      | ret vs =>
        rw [ht] at hs hTL
        cases rest with
        | nil => simp only [termStep] at hs; exact nomatch hs
        | cons c rest₂ =>
        cases rest' with
        | nil => simp [RelStk] at hrest
        | cons c' rest₂' =>
          obtain ⟨Fc, hFc, hdst, hdl⟩ := hD
          obtain ⟨⟨hcf, hcl, hcpc, Fc', hFc', hRc⟩, hDc, hrest₂⟩ := hrest
          rw [hFc] at hFc'; cases hFc'
          simp only [termStep] at hs
          split at hs
          case isFalse => exact nomatch hs
          rename_i hvl
          cases hs
          have hv := args_map hR (as := vs) (by simpa [Term.locs] using hTL)
          obtain ⟨-, hσc⟩ := (hfun c.f).1 Fc hFc
          refine ⟨1, ⟨{ c' with regs := setMany c'.regs fr'.dst ((vs.map (Arg.map F.σ)).map (Arg.eval fr'.regs)) } :: rest₂',
            st'.mem, .free (F.ren.slots + 1) :: st'.ev⟩, steps_one ?_, ⟨⟨⟨hcf, hcl, hcpc, Fc, hFc, ?_⟩, hDc, hrest₂⟩, hm⟩⟩
          · rw [hQs]; show termStep F.ren fr' _ st'.mem st'.ev (B.term.map F.σ) = _
            rw [ht]; simp only [termStep, Term.map]
            rw [if_pos (by simp [hdst, hvl])]
          · show RelR Fc.σ Fc.locs _ (setMany c'.regs fr'.dst ((vs.map (Arg.map F.σ)).map (Arg.eval fr'.regs)))
            rw [hv, hdst]; exact RelR.setMany hσc _ _ hRc hdl
      | _ =>
        rw [ht] at hs hTL
        obtain ⟨l', g, g', rfl, hQt, hR'⟩ := term_ren (rest' := rest') (ev' := st'.ev) hσ hR hTL
          (by intro vs h; cases h) (hm ▸ hs)
        refine ⟨1, ⟨{ fr' with l := l', pc := 0, regs := g' } :: rest', st'.mem, st'.ev⟩, steps_one ?_,
          ⟨⟨by simpa using hf, rfl, rfl, F, hF, hR'⟩, hD, hrest⟩, rfl⟩
        rw [hQs]; show termStep F.ren fr' _ st'.mem st'.ev (B.term.map F.σ) = _
        rw [ht]; exact hQt
  done := by
    intro st st' r ⟨hstk, hm⟩ hs
    obtain ⟨hmain, hfun⟩ := alloc_inv hQ
    unfold step at hs
    rcases hst : st.stack with _ | ⟨fr, rest⟩
    · rw [hst] at hs; exact nomatch hs
    rcases hst' : st'.stack with _ | ⟨fr', rest'⟩
    · rw [hst, hst'] at hstk; exact absurd hstk (by simp [RelStk])
    rw [hst, hst'] at hstk
    obtain ⟨⟨hf, hl, hpc, F, hF, hR⟩, hD, hrest⟩ := hstk
    rw [hst] at hs; simp only [hF] at hs
    obtain ⟨hQF, hσ⟩ := (hfun fr.f).1 F hF
    cases hB : F.blocks.lookup fr.l with
    | none => rw [hB] at hs; exact nomatch hs
    | some B =>
    rw [hB] at hs; simp only at hs
    have hQB : F.ren.blocks.lookup fr'.l = some (B.map F.σ) := by rw [hl]; exact ren_lookup hB
    have hBL := locs_of_block hB
    cases hk : B.body[fr.pc]? with
    | some i =>
      rw [hk] at hs
      cases i with
      | call ds g as => simp only at hs; split at hs <;> (try split at hs) <;> exact nomatch hs
      | _ => simp only at hs; split at hs <;> exact nomatch hs
    | none =>
      rw [hk] at hs
      have hk' : (B.map F.σ).body[fr'.pc]? = none := by rw [hpc]; simp [Block.map, hk]
      have hTL : ∀ x ∈ B.term.locs, x ∈ F.locs := fun x hx => hBL x (by simp [Block.locs, hx])
      cases ht : B.term with
      | ret vs =>
        rw [ht] at hs hTL
        cases rest with
        | cons c rest₂ => simp only [termStep] at hs; split at hs <;> exact nomatch hs
        | nil =>
        cases rest' with
        | cons => simp [RelStk] at hrest
        | nil =>
        simp only [termStep] at hs; cases hs
        have hv := args_map hR (as := vs) (by simpa [Term.locs] using hTL)
        refine ⟨0, st', ⟨(vs.map (Arg.map F.σ)).map (Arg.eval fr'.regs), st'.mem, st'.ev⟩, rfl, ?_, hv, hm⟩
        unfold step; rw [hst']; simp only [hf, hQF, hQB, hk']
        show termStep F.ren fr' [] st'.mem st'.ev (B.term.map F.σ) = _
        rw [ht]; rfl
      | _ => rw [ht] at hs; simp only [termStep] at hs; (repeat' split at hs) <;> exact nomatch hs

end Proven.Ir

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc

theorem rename_init {P Q : Prog Nat} (hQ : alloc P = some Q) (input : List UInt8) (hP : (P.funcs[P.main]?).isSome) :
    RelS P (init P input) (init Q input) := by
  obtain ⟨hmain, hfun⟩ := alloc_inv hQ
  cases hF : P.funcs[P.main]? with
  | none => rw [hF] at hP; exact nomatch hP
  | some F =>
  obtain ⟨hQF, hσ⟩ := (hfun P.main).1 F hF
  have h1 : init P input = ⟨[⟨P.main, F.entry, 0, setMany (fun _ => .w 0) F.params
      [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0], []⟩], Mem.init input, []⟩ := by unfold init; rw [hF]
  have h2 : init Q input = ⟨[⟨P.main, F.entry, 0, setMany (fun _ => .w 0) (F.params.map F.σ)
      [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0], []⟩], Mem.init input, []⟩ := by
    unfold init; rw [hmain, hQF]; rfl
  rw [h1, h2]
  exact ⟨⟨⟨rfl, rfl, rfl, F, hF, RelR.setMany hσ _ _ (RelR.zero _ _) fun p hp => List.mem_append_left _ hp⟩, trivial,
    trivial⟩, rfl⟩

/-- **the pass preserves runs**: the same returned values and memory -/
theorem alloc_runs {P Q : Prog Nat} (h : alloc P = some Q) {input : List UInt8} {r : Result}
    (hr : Runs P (init P input) r) : ∃ r', Runs Q (init Q input) r' ∧ r'.vs = r.vs ∧ r'.mem = r.mem := by
  cases hF : P.funcs[P.main]? with
  | none =>
    obtain ⟨n, hn⟩ := hr
    have : init P input = ⟨[], Mem.init input, []⟩ := by unfold init; rw [hF]
    rw [this] at hn
    cases n with
    | zero => exact nomatch hn
    | succ n => simp [run, step] at hn
  | some F =>
    exact (renameSim h).refines (rename_init h input (by rw [hF]; rfl)) r hr

theorem alloc_main {P Q : Prog Nat} (h : alloc P = some Q) : Q.main = P.main := (alloc_inv h).1

end Proven.Ir
