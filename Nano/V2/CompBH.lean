import Nano.V2.HeapN
/- nano v2 increment 5 (buffers): helpers of the buffer-aware expression proof (Nano/V2/CompB.lean): outcome
composition (`PB.after`, `PB.slide`), environment extension (`EnvB.push`, `EnvB.alias`), consumed regions. -/
namespace Nano.V2B

/-- the footprints of an extended environment -/
def consF (F : Rg) (Fs : Nat → Rg) : Nat → Rg
  | 0 => F
  | k + 1 => Fs k

theorem seq_assoc {c : Cfg} {a b d : SC} {s : St} {r : Res} (e : SC.Ex c (.seq a (.seq b d)) s r) :
    SC.Ex c (.seq (.seq a b) d) s r := by
  cases e with
  | seq e1 e2 =>
    cases e2 with
    | seq e3 e4 => exact .seq (.seq e1 e3) e4
    | seqJ e3 => exact .seqJ (.seq e1 e3)
  | seqJ e1 => exact .seqJ (.seqJ e1)

/-- an outcome of a later block, seen from an earlier state -/
theorem PB.after {c : Cfg} {s s1 : St} {h h1 : Nat} {L : List UInt64} {R1 R2 R : Rg} {τ : Ty} {v : Val} {r : Res}
    (k : KeepB s s1 h R1) (hh : h ≤ h1) (hR1 : ∀ y, y < h → R1 y → R y)
    (hR2 : ∀ y, R2 y → R y ∨ (h ≤ y ∧ y < h1)) (p : PB c s1 h1 L R2 τ v r) : PB c s h L R τ v r := by
  cases r with
  | jmp t _ => exact p
  | ok s' =>
    obtain ⟨h2, W, F, hh2, h82, hs2, hv, hF, k2⟩ := p
    refine ⟨h2, W, F, by omega, h82, hs2, hv, fun y hy => ?_, k.trans k2 hh fun y hy h' => ?_⟩
    · rcases hF y hy with h' | h'
      · rcases hR2 y h' with h'' | h''
        · exact .inl h''
        · exact .inr ⟨h''.1, by omega⟩
      · exact .inr ⟨by omega, h'.2⟩
    · rcases h' with h' | h'
      · exact hR1 y hy h'
      · rcases hR2 y h' with h'' | h''
        · exact h''
        · omega

/-- **slide** after a contracted block: its words move down over `W` -/
theorem PB.slide {c : Cfg} {a : SC} {s : St} {h : Nat} {L W : List UInt64} {R : Rg} {τ : Ty} {v : Val}
    (hc : c.Good) (hR : ∀ y, R y → y < h) (hk : τ.size ≤ 255) (hm : W.length ≤ 255)
    (hp : ∃ r, SC.Ex c a s r ∧ PB c s h (L ++ W) R τ v r) :
    ∃ r, SC.Ex c (.seq a (.ins (slide τ.size W.length))) s r ∧ PB c s h L R τ v r := by
  refine thenB (fun t _ ht => ht) hp ?_
  rintro s1 ⟨h1, Wv, F, hh1, h81, hs1, hv, hF, k1⟩
  have hl := hv.len
  obtain ⟨s2, e2, hs2, k2⟩ := slide_ok hc L W Wv s1 (by simpa using hs1) hm (by omega)
  refine ⟨.ok s2, .ins (by rw [← hl]; exact e2), h1, Wv, F, hh1, h81, hs2, ?_, hF, ?_⟩
  · refine hv.frame fun y hy => k2.heap y ?_
    rw [hs1.hp]; rcases hF y hy with h' | h'
    · have := hR y h'; omega
    · exact h'.2
  · exact k1.keep k2 (by rw [hs1.hp]; exact hh1)

/-- the stack grows: the environment's words stay where they are -/
theorem EnvB.ext {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d : List Nat} {Fs : Nat → Rg} (he : EnvB c s h L env vals d Fs) (M : List UInt64) :
    EnvB c s h (L ++ M) env vals d Fs where
  len := he.len
  slot := fun k τ p hk => by have := he.slot k τ p hk; simp; omega
  rep := fun k τ p hk hd => by rw [getD_append_take (he.slot k τ p hk)]; exact he.rep k τ p hk hd
  nb := he.nb
  low := he.low
  disj := he.disj
  inp := he.inp
  h8 := he.h8
  dl := he.dl

theorem lt_of_getElem? {α : Type} {l : List α} {k : Nat} {x : α} (h : l[k]? = some x) : k < l.length :=
  (List.getElem?_eq_some_iff.1 h).1

/-- a new live entry (a `let`/`split`-bound value) on top of the stack -/
theorem EnvB.push {c : Cfg} {s : St} {h : Nat} {L W : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d : List Nat} {Fs : Nat → Rg} {τ : Ty} {v : Val} {F : Rg}
    (he : EnvB c s h (L ++ W) env vals d Fs) (hv : VR c s τ v W F) (hlow : ∀ y, F y → y < h)
    (hdisj : ∀ k, k < env.length → fl d k ≠ 2 → Disj F (Fs k)) :
    EnvB c s h (L ++ W) ((τ, L.length) :: env) (v :: vals) (0 :: d) (consF F Fs) where
  len := by simp [he.len]
  slot := fun k τ' p hk => by
    cases k with
    | zero => simp at hk; obtain ⟨rfl, rfl⟩ := hk; simp [hv.len]
    | succ k => exact he.slot k τ' p (by simpa using hk)
  rep := fun k τ' p hk hd => by
    cases k with
    | zero =>
      simp at hk; obtain ⟨rfl, rfl⟩ := hk
      rw [List.drop_left, ← hv.len, List.take_length]; exact hv
    | succ k => exact he.rep k τ' p (by simpa using hk) hd
  nb := fun k τ' p hk hb => by
    cases k with
    | zero => rfl
    | succ k => exact he.nb k τ' p (by simpa using hk) hb
  low := fun k hk hd y hy => by
    cases k with
    | zero => exact hlow y hy
    | succ k => exact he.low k (by simpa using hk) hd y hy
  disj := fun k k' hne hk hk' h0 h2 => by
    cases k with
    | zero =>
      cases k' with
      | zero => exact absurd rfl hne
      | succ k' => exact hdisj k' (by simpa using hk') h2
    | succ k =>
      cases k' with
      | zero => exact fun y a b => hdisj k (by simpa using hk) (by simp [fl_cons_succ] at h0; omega) y b a
      | succ k' => exact he.disj k k' (by omega) (by simpa using hk) (by simpa using hk') h0 h2
  inp := he.inp
  h8 := he.h8
  dl := by simp [he.dl]

/-- a READ-ONLY alias of the buffer variable `j` on top of the stack (`let a := var j; b`, `b` read-only on both) -/
theorem EnvB.alias {c : Cfg} {s : St} {h : Nat} {L W : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d : List Nat} {Fs : Nat → Rg} {τ : Ty} {j p : Nat}
    (he : EnvB c s h (L ++ W) env vals d Fs) (hj : env[j]? = some (τ, p)) (hb : τ.hasBuf = true)
    (hW : W = ((L ++ W).drop p).take τ.size) (hd : fl d j ≠ 2) :
    EnvB c s h (L ++ W) ((τ, L.length) :: env) (vals.getD j (.wd 0) :: vals) (1 :: d.set j (max (fl d j) 1))
      (consF (Fs j) Fs) where
  len := by simp [he.len]
  slot := fun k τ' p' hk => by
    cases k with
    | zero =>
      simp at hk; obtain ⟨rfl, rfl⟩ := hk
      have := he.slot j _ p hj; have hl : W.length = τ.size := by
        have h2 := congrArg List.length hW; simp only [List.length_take, List.length_drop] at h2; omega
      simp [hl]
    | succ k => exact he.slot k τ' p' (by simpa using hk)
  rep := fun k τ' p' hk hd' => by
    cases k with
    | zero =>
      simp at hk; obtain ⟨rfl, rfl⟩ := hk
      have hl : W.length = τ.size := by
        have := he.slot j _ p hj
        have h2 := congrArg List.length hW; simp only [List.length_take, List.length_drop] at h2; omega
      rw [List.drop_left, ← hl, List.take_length]; rw [hW]
      exact he.rep j _ p hj hd
    | succ k =>
      have hk' : env[k]? = some (τ', p') := by simpa using hk
      refine he.rep k τ' p' hk' ?_
      simp only [fl_cons_succ, fl_set] at hd'
      split at hd'
      · next h' => obtain ⟨rfl, _⟩ := h'; exact hd
      · exact hd'
  nb := fun k τ' p' hk hb' => by
    cases k with
    | zero => simp at hk; obtain ⟨rfl, rfl⟩ := hk; rw [hb] at hb'; exact absurd hb' (by decide)
    | succ k =>
      have hk' : env[k]? = some (τ', p') := by simpa using hk
      simp only [fl_cons_succ, fl_set]
      split
      · next h' => obtain ⟨rfl, _⟩ := h'; rw [hj] at hk'; simp at hk'; rw [← hk'.1, hb] at hb'
                   exact absurd hb' (by decide)
      · exact he.nb k τ' p' hk' hb'
  low := fun k hk hd' y hy => by
    cases k with
    | zero => exact he.low j (lt_of_getElem? hj) hd y hy
    | succ k =>
      refine he.low k (by simpa using hk) ?_ y hy
      simp only [fl_cons_succ, fl_set] at hd'
      split at hd'
      · next h' => obtain ⟨rfl, _⟩ := h'; exact hd
      · exact hd'
  disj := fun k k' hne hk hk' h0 h2 => by
    cases k with
    | zero => simp [fl_cons_zero] at h0
    | succ k =>
      simp only [fl_cons_succ, fl_set] at h0
      split at h0
      · omega
      · next hkj =>
        have hkl : k < env.length := by simpa using hk
        have hkj' : k ≠ j := fun h' => hkj ⟨h', by rw [he.dl]; subst h'; exact hkl⟩
        cases k' with
        | zero => exact he.disj k j hkj' hkl (lt_of_getElem? hj) h0 hd
        | succ k' =>
          refine he.disj k k' (by omega) hkl (by simpa using hk') h0 ?_
          simp only [fl_cons_succ, fl_set] at h2
          split at h2
          · next h' => obtain ⟨rfl, _⟩ := h'; exact hd
          · exact h2
  inp := he.inp
  h8 := he.h8
  dl := by simp [he.dl]

/-! ## consumed regions -/

theorem RgC.mono {n : Nat} {d d' D D' : List Nat} {Fs : Nat → Rg}
    (hm : ∀ k, k < n → fl d k = 0 → fl d' k = 2 → fl D k = 0 ∧ fl D' k = 2) {y : Nat} (hy : RgC n d d' Fs y) :
    RgC n D D' Fs y := by
  obtain ⟨k, hk, a, b, f⟩ := hy; obtain ⟨a', b'⟩ := hm k hk a b; exact ⟨k, hk, a', b', f⟩

/-- the region consumed by a block in an environment extended by one entry -/
theorem RgC.cons {n : Nat} {a : Nat} {d d'' : List Nat} {F : Rg} {Fs : Nat → Rg} {y : Nat}
    (hy : RgC (n + 1) (a :: d) d'' (consF F Fs) y) : F y ∨ RgC n d d''.tail Fs y := by
  obtain ⟨k, hk, a0, b0, f⟩ := hy
  cases k with
  | zero => exact .inl f
  | succ k => exact .inr ⟨k, by omega, a0, by rw [fl_tail]; exact b0, f⟩

theorem RgC.cons2 {n : Nat} {a b : Nat} {d d'' : List Nat} {F1 F2 : Rg} {Fs : Nat → Rg} {y : Nat}
    (hy : RgC (n + 1 + 1) (a :: b :: d) d'' (consF F2 (consF F1 Fs)) y) :
    F2 y ∨ F1 y ∨ RgC n d (d''.drop 2) Fs y := by
  obtain ⟨k, hk, a0, b0, f⟩ := hy
  match k, hk, a0, b0, f with
  | 0, _, _, _, f => exact .inl f
  | 1, _, _, _, f => exact .inr (.inl f)
  | k + 2, hk, a0, b0, f => exact .inr (.inr ⟨k, by omega, a0, by rw [fl_drop2]; exact b0, f⟩)

/-- the alias entry and `j` are read-only: the body consumes neither -/
theorem RgC.alias {n : Nat} {d d'' : List Nat} {Fs : Nat → Rg} {j : Nat} (hj : j < d.length) {y : Nat}
    (hy : RgC (n + 1) (1 :: d.set j (max (fl d j) 1)) d'' (consF (Fs j) Fs) y) :
    RgC n d (d''.tail.set j (fl d j)) Fs y := by
  obtain ⟨k, hk, a0, b0, f⟩ := hy
  cases k with
  | zero => simp [fl_cons_zero] at a0
  | succ k =>
    simp only [fl_cons_succ, fl_set] at a0
    split at a0
    · omega
    · next hkj =>
      have hkj' : k ≠ j := fun h' => hkj ⟨h', hj⟩
      refine ⟨k, by omega, a0, ?_, f⟩
      rw [fl_set, if_neg (fun h' => hkj' h'.1), fl_tail]; exact b0

/-! ## loops -/

theorem fl_killAll : ∀ {d : List Nat} {tys : List Ty}, d.length = tys.length → ∀ k,
    fl (killAll tys d) k = if (tys.getD k .w).hasBuf then max (fl d k) 1 else fl d k
  | [], [], _, k => by simp [killAll, fl, Ty.hasBuf]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: d, τ :: tys, h, k => by
    cases k with
    | zero => simp [killAll, fl]
    | succ k =>
      have := fl_killAll (d := d) (tys := tys) (by simpa using h) k
      simp only [killAll, fl] at this ⊢; simpa using this

theorem killAll_length {d : List Nat} {tys : List Ty} (h : d.length = tys.length) :
    (killAll tys d).length = d.length := by simp [killAll, h]

/-- inside a loop body every outer buffer is at most read-only -/
theorem EnvB.kill_all {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d : List Nat} {Fs : Nat → Rg} (he : EnvB c s h L env vals d Fs) :
    EnvB c s h L env vals (killAll (env.map (·.1)) d) Fs := by
  have hl : d.length = (env.map (·.1)).length := by simp [he.dl]
  have hk := fl_killAll hl
  have nd : ∀ k, fl (killAll (env.map (·.1)) d) k ≠ 2 → fl d k ≠ 2 := by
    intro k; rw [hk]; split <;> omega
  exact {
    len := he.len, slot := he.slot, inp := he.inp, h8 := he.h8
    rep := fun k τ p hk' hd => he.rep k τ p hk' (nd k hd)
    nb := fun k τ p hk' hb => by
      rw [hk, show (env.map (·.1)).getD k .w = τ by simp [List.getD_eq_getElem?_getD, hk'], hb]
      exact he.nb k τ p hk' hb
    low := fun k hk' hd => he.low k hk' (nd k hd)
    disj := fun k k' hne hk1 hk2 h0 h2 => by
      refine he.disj k k' hne hk1 hk2 ?_ (nd k' h2)
      rw [hk] at h0; split at h0 <;> omega
    dl := by rw [killAll_length hl, he.dl] }

/-- a loop body's consumed region lies inside the state's footprint -/
theorem RgC.body {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d dz : List Nat} {Fs : Nat → Rg} {Fst : Rg} (he : EnvB c s h L env vals d Fs) {y : Nat}
    (hy : RgC (env.length + 1) (0 :: killAll (env.map (·.1)) d) dz (consF Fst Fs) y) : Fst y := by
  obtain ⟨k, hk, a0, _, f⟩ := hy
  cases k with
  | zero => exact f
  | succ k =>
    have hl : d.length = (env.map (·.1)).length := by simp [he.dl]
    simp only [fl_cons_succ, fl_killAll hl] at a0
    have hk' : k < env.length := by omega
    obtain ⟨⟨τ, p⟩, hkp⟩ : ∃ e, env[k]? = some e := ⟨env[k], by simp [hk']⟩
    have hτ : (env.map (·.1)).getD k .w = τ := by simp [List.getD_eq_getElem?_getD, hkp]
    rw [hτ] at a0
    split at a0
    · omega
    · rename_i hb
      exact absurd f ((he.rep k τ p hkp (by omega)).nobuf (by simpa using hb) y)

/-- an outcome seen from an earlier state -/
theorem OB.after {c : Cfg} {s s1 s' : St} {h h1 : Nat} {L : List UInt64} {R1 R2 R : Rg} {τ : Ty} {v : Val}
    (k : KeepB s s1 h R1) (hh : h ≤ h1) (hR1 : ∀ y, y < h → R1 y → R y)
    (hR2 : ∀ y, R2 y → R y ∨ (h ≤ y ∧ y < h1)) (p : OB c s1 h1 L R2 τ v s') : OB c s h L R τ v s' :=
  PB.after (r := .ok s') k hh hR1 hR2 p

/-- a loop-body tail's outcome: `ret r` (jump to EXIT, `r` on `L`), `next v` (jump to HEAD, `v` on `L ++ [w]`), or an
abort -/
def TB (c : Cfg) (s : St) (h : Nat) (L : List UInt64) (w : UInt64) (R : Rg) (σ ρ : Ty) : Val ⊕ Val → Res → Prop
  | _, .ok _ => False
  | o, .jmp t s' => t = .oom ∨ t = .cap ∨ match o with
    | .inl r => t = .exit ∧ OB c s h L R ρ r s'
    | .inr v => t = .head ∧ OB c s h (L ++ [w]) R σ v s'

theorem TB.after {c : Cfg} {s s1 : St} {h h1 : Nat} {L : List UInt64} {w : UInt64} {R1 R2 R : Rg} {σ ρ : Ty}
    {o : Val ⊕ Val} {r : Res} (k : KeepB s s1 h R1) (hh : h ≤ h1) (hR1 : ∀ y, y < h → R1 y → R y)
    (hR2 : ∀ y, R2 y → R y ∨ (h ≤ y ∧ y < h1)) (p : TB c s1 h1 L w R2 σ ρ o r) : TB c s h L w R σ ρ o r := by
  cases r with
  | ok _ => exact p.elim
  | jmp t s' =>
    rcases p with h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl h')
    · right; right
      cases o with
      | inl _ => exact ⟨h'.1, h'.2.after k hh hR1 hR2⟩
      | inr _ => exact ⟨h'.1, h'.2.after k hh hR1 hR2⟩

end Nano.V2B
