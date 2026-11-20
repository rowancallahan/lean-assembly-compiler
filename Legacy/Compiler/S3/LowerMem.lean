/- The lowering of S3 is correct, part 1: how a value lives in RTL memory (`Rep`), memory growth (`Grow`), the
environment relation (`EnvR`), and the big-step meaning (`SC.Ex`) of the small pieces of code (field loads,
constructor allocation, the tag dispatch). -/
import Legacy.Compiler.S3.Lower
import Legacy.Compiler.Ir.IndLowMem

namespace Proven.S3
open Proven.Ir Proven.Ir.IndLow Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

/-! ## values in memory -/

mutual
/-- **`a` is the value `v` in memory `m`**: a word, or a pointer to a live block `[j, fields...]` -/
def Rep (m : Ir.Mem) : V → Val → Prop
  | .w x, a => a = .w x
  | .c j fs, a => ∃ b c0, a = .p b 0 ∧ m.blk b = some (c0, fs.length + 1) ∧
      m.cells[c0]? = some (some (.w (BitVec.ofNat 64 j))) ∧ RepL m fs (c0 + 1)
/-- the cells from `c` hold the values `vs` -/
def RepL (m : Ir.Mem) : List V → Nat → Prop
  | [], _ => True
  | v :: vs, c => (∃ x, m.cells[c]? = some (some x) ∧ Rep m v x) ∧ RepL m vs (c + 1)
end

mutual
theorem Rep.mono {m m' : Ir.Mem} (h : MLe m m') : ∀ (v : V) (a : Val), Rep m v a → Rep m' v a
  | .w _, _, r => r
  | .c _ fs, _, r => by
    obtain ⟨b, c0, e, hb, hc, hl⟩ := r
    exact ⟨b, c0, e, h.2.1 _ _ _ hb, h.2.2 _ _ hc, RepL.mono h fs _ hl⟩
theorem RepL.mono {m m' : Ir.Mem} (h : MLe m m') : ∀ (vs : List V) (c : Nat), RepL m vs c → RepL m' vs c
  | [], _, _ => trivial
  | v :: vs, c, ⟨⟨x, hx, hr⟩, hl⟩ => ⟨⟨x, h.2.2 _ _ hx, Rep.mono h v x hr⟩, RepL.mono h vs (c + 1) hl⟩
end

theorem RepL.get {m : Ir.Mem} : ∀ {vs : List V} {c : Nat}, RepL m vs c → ∀ k (hk : k < vs.length),
    ∃ x, m.cells[c + k]? = some (some x) ∧ Rep m vs[k] x
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | v :: vs, c, ⟨h0, hl⟩, k, hk => by
    cases k with
    | zero => simpa using h0
    | succ k =>
      obtain ⟨x, hx, hr⟩ := RepL.get hl k (by simp at hk; omega)
      exact ⟨x, by rw [show c + (k + 1) = c + 1 + k by omega]; exact hx, by simpa using hr⟩

theorem RepL.of_get {m : Ir.Mem} : ∀ {vs : List V} {c : Nat}, (∀ k (hk : k < vs.length),
    ∃ x, m.cells[c + k]? = some (some x) ∧ Rep m vs[k] x) → RepL m vs c
  | [], _, _ => trivial
  | v :: vs, c, h => ⟨h 0 (by simp), RepL.of_get fun k hk => by
      obtain ⟨x, hx, hr⟩ := h (k + 1) (by simp; omega)
      exact ⟨x, by rw [show c + 1 + k = c + (k + 1) by omega]; exact hx, by simpa using hr⟩⟩

/-- memory grows and the output is untouched -/
def Grow (m m' : Ir.Mem) : Prop := MLe m m' ∧ m'.out = m.out

theorem Grow.refl (m : Ir.Mem) : Grow m m := ⟨MLe.refl m, rfl⟩
theorem Grow.trans {m₁ m₂ m₃ : Ir.Mem} (a : Grow m₁ m₂) (b : Grow m₂ m₃) : Grow m₁ m₃ :=
  ⟨a.1.trans b.1, b.2.trans a.2⟩

/-! ## environments -/

/-- the registers `ρ` hold the values `env` -/
def EnvR (m : Ir.Mem) (env : List V) (ρ : List VReg) (g : VReg → Val) : Prop :=
  env.length = ρ.length ∧ ∀ i (h₁ : i < env.length) (h₂ : i < ρ.length), Rep m env[i] (g ρ[i])

theorem EnvR.get {m : Ir.Mem} {env : List V} {ρ : List VReg} {g : VReg → Val} (h : EnvR m env ρ g) {i : Nat} {v : V}
    (hv : env[i]? = some v) : Rep m v (g (ρ.getD i 0)) ∧ ρ.getD i 0 ∈ ρ := by
  have hi : i < env.length := by
    rcases Nat.lt_or_ge i env.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hv; exact nomatch hv
  have hi' : i < ρ.length := h.1 ▸ hi
  rw [List.getElem?_eq_getElem hi] at hv
  cases hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  exact ⟨h.2 i hi hi', List.getElem_mem hi'⟩

theorem EnvR.mono {m m' : Ir.Mem} {env : List V} {ρ : List VReg} {g g' : VReg → Val} (h : EnvR m env ρ g)
    (hm : MLe m m') (hg : ∀ r ∈ ρ, g' r = g r) : EnvR m' env ρ g' :=
  ⟨h.1, fun i h₁ h₂ => by rw [hg _ (List.getElem_mem h₂)]; exact Rep.mono hm _ _ (h.2 i h₁ h₂)⟩

theorem EnvR.cons {m : Ir.Mem} {env : List V} {ρ : List VReg} {g : VReg → Val} (h : EnvR m env ρ g) {v : V} {r : VReg}
    (hv : Rep m v (g r)) : EnvR m (v :: env) (r :: ρ) g :=
  ⟨by simp [h.1], fun i h₁ h₂ => by
    cases i with
    | zero => exact hv
    | succ i => exact h.2 i (by simp at h₁; omega) (by simp at h₂; omega)⟩

theorem EnvR.append {m : Ir.Mem} {env : List V} {ρ : List VReg} {g : VReg → Val} (h : EnvR m env ρ g) {fs : List V}
    {rs : List VReg} (hl : fs.length = rs.length) (hf : ∀ k (h₁ : k < fs.length) (h₂ : k < rs.length), Rep m fs[k] (g rs[k])) :
    EnvR m (fs ++ env) (rs ++ ρ) g :=
  ⟨by simp [h.1, hl], fun i h₁ h₂ => by
    rcases Nat.lt_or_ge i fs.length with hi | hi
    · rw [List.getElem_append_left hi, List.getElem_append_left (hl ▸ hi)]; exact hf i hi (hl ▸ hi)
    · rw [List.getElem_append_right hi, List.getElem_append_right (hl ▸ hi)]
      simp only [hl]
      exact h.2 _ (by simp at h₁; omega) (by simp at h₂; omega)⟩

theorem Vars.get_length {Γ : List Ty} : ∀ {ts : List Ty} (xs : Vars Γ ts), xs.idxs.length = ts.length
  | _, .nil => rfl
  | _, .cons _ xs => by simp [Vars.idxs, Vars.get_length xs]

theorem mapM_get : ∀ {is : List Nat} {env vs : List V}, is.mapM (env[·]?) = some vs →
    vs.length = is.length ∧ ∀ k (h₁ : k < vs.length) (h₂ : k < is.length), env[is[k]]? = some vs[k]
  | [], env, vs, h => by simp at h; subst h; simp
  | i :: is, env, vs, h => by
    rw [List.mapM_cons] at h
    cases hi : env[i]? with
    | none => simp [hi] at h
    | some v =>
      cases hr : is.mapM (env[·]?) with
      | none => simp [hi, hr] at h
      | some ws =>
        simp [hi, hr] at h; subst h
        obtain ⟨hl, hg⟩ := mapM_get hr
        refine ⟨by simp [hl], fun k h₁ h₂ => ?_⟩
        cases k with
        | zero => simpa using hi
        | succ k => simpa using hg k (by simp at h₁; omega) (by simp at h₂; omega)

/-- the values of variables, read from their registers -/
theorem vars_rep {m : Ir.Mem} {env : List V} {ρ : List VReg} {g : VReg → Val} (h : EnvR m env ρ g) {is : List Nat}
    {vs : List V} (hv : is.mapM (env[·]?) = some vs) :
    vs.length = is.length ∧ ∀ k (h₁ : k < vs.length) (h₂ : k < is.length), Rep m vs[k] (g (ρ.getD is[k] 0)) ∧
      ρ.getD is[k] 0 ∈ ρ := by
  obtain ⟨hl, hg⟩ := mapM_get hv
  exact ⟨hl, fun k h₁ h₂ => h.get (hg k h₁ h₂)⟩

/-! ## registers -/

theorem setMany_nodup : ∀ (xs : List VReg) (vals : List Val) (g : VReg → Val), xs.Nodup → xs.length = vals.length →
    ∀ i (h₁ : i < xs.length) (h₂ : i < vals.length), setMany g xs vals xs[i] = vals[i]
  | [], _, _, _, _, i, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | x :: xs, [], _, _, hl, _, _, _ => by simp at hl
  | x :: xs, v :: vals, g, hn, hl, i, h₁, h₂ => by
    simp only [setMany]
    have hn' := List.nodup_cons.1 hn
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      have : ∀ (ys : List VReg) (ws : List Val) (g' : VReg → Val), x ∉ ys → g' x = v → setMany g' ys ws x = v := by
        intro ys
        induction ys with
        | nil => intro ws g' _ h; cases ws <;> simpa [setMany] using h
        | cons y ys ih =>
          intro ws g' hy h
          cases ws with
          | nil => simpa [setMany] using h
          | cons w ws =>
            simp only [setMany]
            refine ih ws _ (fun h' => hy (List.mem_cons_of_mem _ h')) ?_
            simp only [List.mem_cons, not_or] at hy
            rw [upd_ne _ _ hy.1]; exact h
      exact this xs vals _ hn'.1 (upd_same _ _ _)
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact setMany_nodup xs vals _ hn'.2 (by simpa using hl) i (by simp at h₁; omega) (by simp at h₂; omega)

/-! ## small pieces of code -/

section
variable {Q : Ir.Prog VReg}

theorem ex_op {g : VReg → Val} (m : Ir.Mem) (o : Op) (d : VReg) (a b : Arg VReg) {x y : BitVec 64}
    (ha : a.eval g = .w x) (hb : b.eval g = .w y) :
    SC.Ex Q (opK o d a b) g m (upd g d (.w (o.eval x y))) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, Rhs.eval, Arg.word, ha, hb])

theorem ex_mop {g : VReg → Val} (m : Ir.Mem) (o : MOp) (d a b : VReg) {x y : BitVec 64} (ha : g a = .w x)
    (hb : g b = .w y) : SC.Ex Q (.i (.let_ d (.mop o (.r a) (.r b)))) g m (upd g d (.w (o.eval x y))) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, Rhs.eval, Arg.word, Arg.eval, ha, hb])

/-- `ldFs`: the fields into consecutive registers -/
theorem ex_ldFs {m : Ir.Mem} {g : VReg → Val} {x : Nat} {b c0 : Nat} {fs : List V} (hx : g x = .p b 0)
    (hb : m.blk b = some (c0, fs.length + 1)) (hl : RepL m fs (c0 + 1)) (base : Nat) (hxb : x < base) :
    ∀ k, k ≤ fs.length → ∃ g', SC.Ex Q (ldFs x base k) g m g' m ∧ (∀ r, r < base → g' r = g r) ∧
      ∀ i (h : i < k) (h' : i < fs.length), Rep m fs[i] (g' (base + i))
  | 0, _ => ⟨g, .nop, fun _ _ => rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    obtain ⟨g1, x1, f1, r1⟩ := ex_ldFs hx hb hl base hxb k (by omega)
    obtain ⟨y, hy, hr⟩ := hl.get k (by omega)
    have hx1 : g1 x = .p b 0 := by rw [f1 x hxb, hx]
    refine ⟨upd g1 (base + k) y, .seq x1 (.i (e := []) (fun _ _ _ h => nomatch h) ?ex), fun r hr => ?fr, fun i hi => ?fi⟩
    case ex =>
      simp only [Inst.exec, hx1, hb]
      rw [if_pos (by omega), show c0 + 0 + (k + 1) = c0 + 1 + k by omega, hy]
    case fr => rw [upd_ne _ _ (show r ≠ base + k by omega), f1 r hr]
    case fi =>
      intro hi'
      rcases Nat.lt_or_ge i k with h' | h'
      · rw [upd_ne _ _ (show base + i ≠ base + k by omega)]; exact r1 i h' hi'
      · have : i = k := by omega
        subst this; rw [upd_same]; exact hr

/-- the memory with a fresh block of cells `cs` -/
def _root_.Proven.Ir.Mem.withBlk (m : Ir.Mem) (cs : List (Option Val)) : Ir.Mem :=
  { m with cells := m.cells ++ cs, blks := m.blks ++ [(m.cells.length, cs.length, true)] }

theorem withBlk_blk (m : Ir.Mem) (cs : List (Option Val)) :
    (m.withBlk cs).blk (m.blks.length + 2) = some (m.cells.length, cs.length) := by
  simp [Ir.Mem.withBlk, Ir.Mem.blk]

theorem withBlk_grow (m : Ir.Mem) (cs : List (Option Val)) : Grow m (m.withBlk cs) := by
  refine ⟨⟨rfl, fun b c0 sz h => ?_, fun i v h => ?_⟩, rfl⟩
  · match b, h with
    | k + 2, h =>
      simp only [Ir.Mem.blk] at h ⊢
      have hk : k < m.blks.length := by
        rcases Nat.lt_or_ge k m.blks.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at h; exact nomatch h
      simp only [Ir.Mem.withBlk]
      rw [List.getElem?_append_left hk]; exact h
  · have hi : i < m.cells.length := by
      rcases Nat.lt_or_ge i m.cells.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at h; exact nomatch h
    simp only [Ir.Mem.withBlk]
    rw [List.getElem?_append_left hi]; exact h

theorem ex_st_blk {g : VReg → Val} (m : Ir.Mem) (cs : List (Option Val)) (d : VReg) (hd : g d = .p (m.blks.length + 2) 0)
    (a : Arg VReg) (k : Nat) (hk : k < cs.length) :
    SC.Ex Q (.i (.st a d k)) g (m.withBlk cs) g (m.withBlk (cs.set k (some (a.eval g)))) :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by
    simp only [Inst.exec, hd, withBlk_blk, Nat.zero_add, if_pos hk]
    simp [Ir.Mem.withBlk, List.set_append_right _ _ (Nat.le_add_right m.cells.length k)])

theorem ex_stFs {g : VReg → Val} (m : Ir.Mem) (d : VReg) (hd : g d = .p (m.blks.length + 2) 0) :
    ∀ (rs : List VReg) (k : Nat) (cs : List (Option Val)), k + rs.length ≤ cs.length →
      SC.Ex Q (stFs d k rs) g (m.withBlk cs) g
        (m.withBlk (cs.take k ++ rs.map (fun r => some (g r)) ++ cs.drop (k + rs.length)))
  | [], k, cs, _ => by simpa [stFs] using SC.Ex.nop
  | r :: rs, k, cs, hk => by
    simp only [stFs]
    have h1 := ex_st_blk (Q := Q) m cs d hd (.r r) k (by simp at hk; omega)
    have h2 := ex_stFs m d hd rs (k + 1) (cs.set k (some (g r))) (by simp at hk ⊢; omega)
    refine .seq h1 ?_
    have e : (cs.set k (some (g r))).take (k + 1) ++ rs.map (fun r => some (g r)) ++
        (cs.set k (some (g r))).drop (k + 1 + rs.length) =
        cs.take k ++ (r :: rs).map (fun r => some (g r)) ++ cs.drop (k + (r :: rs).length) := by
      have hkl : k < cs.length := by simp at hk; omega
      rw [List.drop_set, if_pos (by omega), List.take_add_one, List.getElem?_set_self hkl,
        List.take_set_of_le (Nat.le_refl k)]
      simp [show k + 1 + rs.length = k + (rs.length + 1) by omega]
    rw [← e]; simpa only [Arg.eval] using h2

/-- the tag dispatch picks arm `j` -/
theorem ex_chain {t : Nat} {g : VReg → Val} {m : Ir.Mem} {g' : VReg → Val} {m' : Ir.Mem} :
    ∀ (L : List SC) (k j : Nat) (hj : j < L.length), g t = .w (BitVec.ofNat 64 (k + j)) →
      (∀ i, i < j → BitVec.ofNat 64 (k + i) ≠ BitVec.ofNat 64 (k + j)) → SC.Ex Q L[j] g m g' m' →
      SC.Ex Q (chain t k L) g m g' m'
  | [], _, _, hj, _, _, _ => absurd hj (Nat.not_lt_zero _)
  | [a], k, j, hj, _, _, hx => by
    have : j = 0 := by simp at hj; omega
    subst this; simpa [chain] using hx
  | a :: b :: L, k, j, hj, ht, hne, hx => by
    simp only [chain]
    cases j with
    | zero =>
      refine .iteT ?_ (by simpa using hx)
      simp [Tst.eval, Arg.eval, ht, Cond.eval]
    | succ j =>
      refine .iteF ?_ (ex_chain (b :: L) (k + 1) j (by simp at hj ⊢; omega)
        (by rw [ht]; congr 2; omega) (fun i hi => by
          have := hne (i + 1) (by omega); rwa [show k + (i + 1) = k + 1 + i by omega,
            show k + (j + 1) = k + 1 + j by omega] at this) (by simpa using hx))
      have := hne 0 (by omega)
      simp only [Nat.add_zero] at this
      simp [Tst.eval, Arg.eval, ht, Cond.eval, Ne.symm this]

end

end Proven.S3
