import Nano.V2.Buf
import Nano.V2.Own
/- nano v2 increment 5 (buffers), proof layer: the HEAP invariant for `cE` with buffers (after
Testing/notes/NANO_V2_SKELETONS6.lean `Round6.MultiBuffer`: footprints, `SameOutside`, `Owned`).
* `VR c s τ v W F`: the value `v : τ` is the words `W` (stack) plus, for each buffer, a `BufRep` in memory; `F` is
  EXACTLY the union of its buffers' footprints, pairwise disjoint.
* `EnvB`: every non-dead variable is represented (footprint `Fs k`, below the heap top); a LIVE (flag 0) variable's
  footprint is disjoint from every other non-dead one (read-only aliases may share).
* `KeepB s s' h R`: memory below the old heap top `h` changes only inside the region `R` (the footprints of the
  buffers CONSUMED by the block, `RgC`).
* `PB`: a block's outcome: the value pushed, heap top grown, its footprint inside `R` ∪ the new heap; or an abort. -/
namespace Nano.V2B

/-- a region of byte addresses -/
abbrev Rg := Nat → Prop

def blk (a cap : Nat) : Rg := fun y => a ≤ y ∧ y < foot a cap
def Disj (F G : Rg) : Prop := ∀ y, F y → G y → False

theorem BufRep.frame {c : Cfg} {s s' : St} {a cap : Nat} {l : List UInt64} (hr : BufRep c s a cap l)
    (hm : ∀ y, blk a cap y → s'.w y = s.w y) : BufRep c s' a cap l where
  al := hr.al
  lo := hr.lo
  cap_lt := hr.cap_lt
  len_le := hr.len_le
  hd := by rw [hm a ⟨Nat.le_refl _, by unfold foot; omega⟩]; exact hr.hd
  hc := by rw [hm (a + 8) ⟨by omega, by unfold foot; omega⟩]; exact hr.hc
  el := fun i hi => by
    rw [hm _ ⟨by omega, by have := hr.len_le; unfold foot; omega⟩]; exact hr.el i hi

/-- value representation -/
def VR (c : Cfg) (s : St) : Ty → Val → List UInt64 → Rg → Prop
  | .w, .wd x, W, F => W = [x] ∧ ∀ y, ¬ F y
  | .buf, .bf l, W, F => ∃ a cap, W = [UInt64.ofNat a] ∧ BufRep c s a cap l ∧ ∀ y, F y ↔ blk a cap y
  | .prod τ σ, .pr u v, W, F => ∃ W1 W2 F1 F2, W = W1 ++ W2 ∧ VR c s τ u W1 F1 ∧ VR c s σ v W2 F2 ∧
      Disj F1 F2 ∧ ∀ y, F y ↔ F1 y ∨ F2 y
  | _, _, _, _ => False

theorem VR.len {c : Cfg} {s : St} : ∀ {τ : Ty} {v : Val} {W : List UInt64} {F : Rg}, VR c s τ v W F → W.length = τ.size
  | .w, .wd _, _, _, ⟨h, _⟩ => by subst h; rfl
  | .buf, .bf _, _, _, ⟨_, _, h, _⟩ => by subst h; rfl
  | .prod _ _, .pr _ _, _, _, ⟨_, _, _, _, h, h1, h2, _⟩ => by subst h; simp [Ty.size, h1.len, h2.len]
  | .w, .bf _, _, _, h | .w, .pr _ _, _, _, h | .buf, .wd _, _, _, h | .buf, .pr _ _, _, _, h
  | .prod _ _, .wd _, _, _, h | .prod _ _, .bf _, _, _, h => h.elim

theorem VR.frame {c : Cfg} {s s' : St} : ∀ {τ : Ty} {v : Val} {W : List UInt64} {F : Rg}, VR c s τ v W F →
    (∀ y, F y → s'.w y = s.w y) → VR c s' τ v W F
  | .w, .wd _, _, _, h, _ => h
  | .buf, .bf _, _, _, ⟨a, cap, h1, h2, h3⟩, hm => ⟨a, cap, h1, h2.frame fun y hy => hm y ((h3 y).2 hy), h3⟩
  | .prod _ _, .pr _ _, _, _, ⟨W1, W2, F1, F2, h, h1, h2, hd, hF⟩, hm =>
    ⟨W1, W2, F1, F2, h, h1.frame fun y hy => hm y ((hF y).2 (.inl hy)),
      h2.frame fun y hy => hm y ((hF y).2 (.inr hy)), hd, hF⟩
  | .w, .bf _, _, _, h, _ | .w, .pr _ _, _, _, h, _ | .buf, .wd _, _, _, h, _ | .buf, .pr _ _, _, _, h, _
  | .prod _ _, .wd _, _, _, h, _ | .prod _ _, .bf _, _, _, h, _ => h.elim

theorem VR.nobuf {c : Cfg} {s : St} : ∀ {τ : Ty} {v : Val} {W : List UInt64} {F : Rg}, τ.hasBuf = false →
    VR c s τ v W F → ∀ y, ¬ F y
  | .w, .wd _, _, _, _, ⟨_, h⟩ => h
  | .prod _ _, .pr _ _, _, _, hb, ⟨_, _, _, _, _, h1, h2, _, hF⟩ => by
    simp only [Ty.hasBuf, Bool.or_eq_false_iff] at hb
    intro y hy; rcases (hF y).1 hy with h | h
    · exact h1.nobuf hb.1 y h
    · exact h2.nobuf hb.2 y h
  | .buf, .bf _, _, _, hb, _ => by simp [Ty.hasBuf] at hb
  | .w, .bf _, _, _, _, h | .w, .pr _ _, _, _, _, h | .buf, .wd _, _, _, _, h | .buf, .pr _ _, _, _, _, h
  | .prod _ _, .wd _, _, _, _, h | .prod _ _, .bf _, _, _, _, h => h.elim

theorem VR.wd {c : Cfg} {s : St} {v : Val} {W : List UInt64} {F : Rg} (h : VR c s .w v W F) :
    v = .wd v.word ∧ W = [v.word] ∧ ∀ y, ¬ F y := by
  cases v with
  | wd x => exact ⟨rfl, h.1, h.2⟩
  | bf _ => exact h.elim
  | pr _ _ => exact h.elim

theorem VR.ofw {c : Cfg} {s : St} (x : UInt64) : VR c s .w (.wd x) [x] (fun _ => False) := ⟨rfl, fun _ h => h⟩

/-- the memory frame of a block: below the old heap top `h`, only `R` changes -/
structure KeepB (s s' : St) (h : Nat) (R : Rg) : Prop where
  ib : s'.get 28 = s.get 28
  il : s'.get 29 = s.get 29
  heap : ∀ a < h, ¬ R a → s'.w a = s.w a
  o : s'.o = s.o

theorem Keep.toB {s s' : St} {h : Nat} (k : Keep s s') (hh : (s.get 30).toNat = h) (R : Rg) : KeepB s s' h R :=
  ⟨k.ib, k.il, fun a ha _ => k.heap a (hh ▸ ha), k.o⟩

theorem KeepB.trans {s1 s2 s3 : St} {h h2 : Nat} {R1 R2 R : Rg} (k1 : KeepB s1 s2 h R1) (k2 : KeepB s2 s3 h2 R2)
    (hh : h ≤ h2) (hR : ∀ y, y < h → R1 y ∨ R2 y → R y) : KeepB s1 s3 h R :=
  ⟨k2.ib.trans k1.ib, k2.il.trans k1.il, fun a ha hn =>
    (k2.heap a (by omega) fun h' => hn (hR a ha (.inr h'))).trans (k1.heap a ha fun h' => hn (hR a ha (.inl h'))),
    k2.o.trans k1.o⟩

theorem KeepB.mono {s s' : St} {h : Nat} {R R' : Rg} (k : KeepB s s' h R) (hR : ∀ y, y < h → R y → R' y) :
    KeepB s s' h R' := ⟨k.ib, k.il, fun a ha hn => k.heap a ha fun h' => hn (hR a ha h'), k.o⟩

theorem KeepB.keep {s1 s2 s3 : St} {h : Nat} {R : Rg} (k1 : KeepB s1 s2 h R) (k2 : Keep s2 s3)
    (hh : h ≤ (s2.get 30).toNat) : KeepB s1 s3 h R :=
  k1.trans (k2.toB rfl (fun _ => False)) hh fun _ _ h => h.elim (fun h => h) False.elim

theorem InpRep.keepB {c : Cfg} {s s' : St} {h : Nat} {R : Rg} (hi : InpRep c s) (k : KeepB s s' h R) : InpRep c s' :=
  ⟨k.ib ▸ hi.ib, k.il ▸ hi.il, hi.fit⟩

/-- a block's successful outcome: `v : τ` pushed (words `W`), the heap grown to `h'`, `v`'s buffers inside the
consumed region `R` or the new heap -/
def OB (c : Cfg) (s : St) (h : Nat) (L : List UInt64) (R : Rg) (τ : Ty) (v : Val) (s' : St) : Prop :=
  ∃ h' W F, h ≤ h' ∧ h' % 8 = 0 ∧ Stk c s' h' (L ++ W) ∧ VR c s' τ v W F ∧ (∀ y, F y → R y ∨ (h ≤ y ∧ y < h')) ∧
    KeepB s s' h R

/-- a block's outcome: `OB`, or an abort (out of memory / capacity) -/
def PB (c : Cfg) (s : St) (h : Nat) (L : List UInt64) (R : Rg) (τ : Ty) (v : Val) : Res → Prop
  | .ok s' => OB c s h L R τ v s'
  | .jmp t _ => t = .oom ∨ t = .cap

/-! ## flags (`Ex.lv`): 0 live, 1 read-only, 2 dead -/

def fl (d : List Nat) (k : Nat) : Nat := d.getD k 0

/-- what one checked block does to the flags: a live BUFFER variable may die, nothing else changes -/
def Step (tys : List Ty) (d d' : List Nat) : Prop :=
  ∀ k, fl d' k = fl d k ∨ (fl d k = 0 ∧ fl d' k = 2 ∧ (tys.getD k .w).hasBuf = true)

theorem Step.refl (tys : List Ty) (d : List Nat) : Step tys d d := fun _ => .inl rfl
theorem Step.trans {tys : List Ty} {d1 d2 d3 : List Nat} (h1 : Step tys d1 d2) (h2 : Step tys d2 d3) :
    Step tys d1 d3 := by
  intro k
  rcases h1 k with a | ⟨a1, a2, a3⟩ <;> rcases h2 k with b | ⟨b1, b2, b3⟩
  · exact .inl (b.trans a)
  · exact .inr ⟨a ▸ b1, b2, b3⟩
  · exact .inr ⟨a1, b ▸ a2, a3⟩
  · omega

/-- the footprints of the variables a block consumed (live before, dead after) -/
def RgC (n : Nat) (d d' : List Nat) (Fs : Nat → Rg) : Rg :=
  fun y => ∃ k < n, fl d k = 0 ∧ fl d' k = 2 ∧ Fs k y

/-- the environment: entry `k` = `(τ, p)` (the words at absolute slot `p` of the stack `L`), value `vals[k]`, flag
`d[k]`, footprint `Fs k` -/
structure EnvB (c : Cfg) (s : St) (h : Nat) (L : List UInt64) (env : List (Ty × Nat)) (vals : List Val)
    (d : List Nat) (Fs : Nat → Rg) : Prop where
  len : vals.length = env.length
  slot : ∀ (k : Nat) (τ : Ty) (p : Nat), env[k]? = some (τ, p) → p + τ.size ≤ L.length
  rep : ∀ (k : Nat) (τ : Ty) (p : Nat), env[k]? = some (τ, p) → fl d k ≠ 2 →
    VR c s τ (vals.getD k (.wd 0)) ((L.drop p).take τ.size) (Fs k)
  nb : ∀ (k : Nat) (τ : Ty) (p : Nat), env[k]? = some (τ, p) → τ.hasBuf = false → fl d k = 0
  low : ∀ k : Nat, k < env.length → fl d k ≠ 2 → ∀ y, Fs k y → y < h
  disj : ∀ k k' : Nat, k ≠ k' → k < env.length → k' < env.length → fl d k = 0 → fl d k' ≠ 2 → Disj (Fs k) (Fs k')
  inp : InpRep c s
  h8 : h % 8 = 0
  dl : d.length = env.length

theorem RgC.low {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d d' : List Nat} {Fs : Nat → Rg} (he : EnvB c s h L env vals d Fs) {y : Nat} (hy : RgC env.length d d' Fs y) :
    y < h := by
  obtain ⟨k, hk, h0, _, hF⟩ := hy; exact he.low k hk (by omega) y hF

/-- two consecutive blocks consume disjoint regions -/
theorem RgC.disj {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d d1 d2 : List Nat} {Fs : Nat → Rg} (he : EnvB c s h L env vals d Fs) (st : Step (env.map (·.1)) d d1)
    {y : Nat} (h1 : RgC env.length d d1 Fs y) (h2 : RgC env.length d1 d2 Fs y) : False := by
  obtain ⟨k1, hk1, a1, b1, f1⟩ := h1
  obtain ⟨k2, hk2, a2, _, f2⟩ := h2
  have hne : k1 ≠ k2 := by rintro rfl; omega
  have : fl d k2 = 0 := by rcases st k2 with h | ⟨h, _⟩ <;> omega
  exact he.disj k1 k2 hne hk1 hk2 a1 (by omega) y f1 f2

theorem RgC.trans {n : Nat} {tys : List Ty} {d d1 d2 : List Nat} {Fs : Nat → Rg} (st1 : Step tys d d1)
    (st2 : Step tys d1 d2) {y : Nat} (hy : RgC n d d1 Fs y ∨ RgC n d1 d2 Fs y) : RgC n d d2 Fs y := by
  rcases hy with ⟨k, hk, a, b, f⟩ | ⟨k, hk, a, b, f⟩
  · refine ⟨k, hk, a, ?_, f⟩; rcases st2 k with h | ⟨h, _⟩ <;> omega
  · refine ⟨k, hk, ?_, b, f⟩; rcases st1 k with h | ⟨h, _⟩ <;> omega

theorem getD_append_take {L M : List UInt64} {p n : Nat} (h : p + n ≤ L.length) :
    ((L ++ M).drop p).take n = (L.drop p).take n := by
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- the environment after a block that consumed `RgC d d1`, grew the heap and pushed `M` -/
theorem EnvB.after {c : Cfg} {s s1 : St} {h h1 : Nat} {L M : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d d1 : List Nat} {Fs : Nat → Rg} (he : EnvB c s h L env vals d Fs) (st : Step (env.map (·.1)) d d1)
    (hl : d1.length = d.length) (k : KeepB s s1 h (RgC env.length d d1 Fs)) (hh : h ≤ h1) (h8 : h1 % 8 = 0) :
    EnvB c s1 h1 (L ++ M) env vals d1 Fs where
  len := he.len
  slot := fun k τ p hk => by have := he.slot k τ p hk; simp; omega
  rep := fun j τ p hj hd => by
    have hd0 : fl d j ≠ 2 := by rcases st j with h | ⟨h, _⟩ <;> omega
    rw [getD_append_take (he.slot j τ p hj)]
    refine (he.rep j τ p hj hd0).frame fun y hy => k.heap y (he.low j ?_ hd0 y hy) ?_
    · exact (List.getElem?_eq_some_iff.1 hj).1
    · rintro ⟨k', hk', a, b, f⟩
      have hne : k' ≠ j := by rintro rfl; omega
      exact he.disj k' j hne hk' (List.getElem?_eq_some_iff.1 hj).1 a hd0 y f hy
  nb := fun j τ p hj hb => by
    have := he.nb j τ p hj hb
    rcases st j with h | ⟨_, _, h⟩
    · omega
    · simp [List.getD_eq_getElem?_getD, List.getElem?_map, hj] at h; rw [hb] at h; exact absurd h (by decide)
  low := fun j hj hd y hy => by
    have : fl d j ≠ 2 := by rcases st j with h | ⟨h, _⟩ <;> omega
    have := he.low j hj this y hy; omega
  disj := fun j j' hne hj hj' h0 h2 => by
    have a : fl d j = 0 := by rcases st j with h | ⟨h, _⟩ <;> omega
    have b : fl d j' ≠ 2 := by rcases st j' with h | ⟨h, _⟩ <;> omega
    exact he.disj j j' hne hj hj' a b
  inp := he.inp.keepB k
  h8 := h8
  dl := hl.trans he.dl

/-- a value produced by the first of two blocks survives the second -/
theorem VR.across {c : Cfg} {s s1 s2 : St} {h h1 : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d d1 d2 : List Nat} {Fs : Nat → Rg} {τ : Ty} {v : Val} {W : List UInt64} {F : Rg}
    (he : EnvB c s h L env vals d Fs) (st : Step (env.map (·.1)) d d1) (hv : VR c s1 τ v W F)
    (hF : ∀ y, F y → RgC env.length d d1 Fs y ∨ (h ≤ y ∧ y < h1))
    (k : KeepB s1 s2 h1 (RgC env.length d1 d2 Fs)) (hh : h ≤ h1) : VR c s2 τ v W F := by
  refine hv.frame fun y hy => k.heap y ?_ ?_
  · rcases hF y hy with h' | h'
    · have := h'.low he; omega
    · exact h'.2
  · intro h2
    rcases hF y hy with h' | h'
    · exact RgC.disj he st h' h2
    · obtain ⟨k2, hk2, a2, _, f2⟩ := h2
      have : fl d k2 = 0 := by rcases st k2 with h | ⟨h, _⟩ <;> omega
      have := he.low k2 hk2 (by omega) y f2; omega

end Nano.V2B
