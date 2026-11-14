/- Source-level correctness of the `Pipe` translation: running `Pipe.prog p` on the heap
`[input, output]` terminates with `p.denote input` at the start of the output block (`Pipe.prog_exec`). -/
import Compiler.Front.Pipe

set_option linter.unusedVariables false

namespace Proven

/-! ## Bytes and words -/

theorem zx_toNat (u : UInt8) : (zx u).toNat = u.toNat := by
  have := u.toBitVec.isLt
  simp only [zx, BitVec.toNat_setWidth, UInt8.toNat_toBitVec] at *; omega

theorem zx_setWidth (u : UInt8) : (zx u).setWidth 8 = u.toBitVec := setWidth_setWidth8 _

theorem zx_inj {a b : UInt8} : zx a = zx b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have := congrArg BitVec.toNat h; rw [zx_toNat, zx_toNat] at this; exact UInt8.toNat_inj.mp this

theorem zx_lt (a b : UInt8) : zx a < zx b ↔ a < b := by
  rw [BitVec.lt_def, zx_toNat, zx_toNat, UInt8.lt_iff_toNat_lt]

theorem zx_add (a b : UInt8) : (zx a + zx b) &&& 255#64 = zx (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_add, zx_toNat, zx_toNat, zx_toNat, UInt8.toNat_add,
    show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := a.toNat_lt; have := b.toNat_lt; omega

theorem zx_sub (a b : UInt8) : (zx a - zx b) &&& 255#64 = zx (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_sub, zx_toNat, zx_toNat, zx_toNat, UInt8.toNat_sub,
    show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := a.toNat_lt; have := b.toNat_lt; omega

theorem zx_and (a b : UInt8) : zx a &&& zx b = zx (a &&& b) := by simp [zx, BitVec.setWidth_and]
theorem zx_or (a b : UInt8) : zx a ||| zx b = zx (a ||| b) := by simp [zx, BitVec.setWidth_or]
theorem zx_xor (a b : UInt8) : zx a ^^^ zx b = zx (a ^^^ b) := by simp [zx, BitVec.setWidth_xor]

theorem ite01 (p : Prop) [Decidable p] : ((if p then 1 else 0 : BitVec 64) = 0) ↔ ¬p := by
  by_cases h : p <;> simp [h]

/-- `e.tr` computes `zx (e.denote a x)` exactly -/
theorem ByteExp.tr_ok (a x : UInt8) (env : AEnv) (h6 : env 6 = zx x) :
    ∀ e : ByteExp, (e.noAcc = true ∨ env 5 = zx a) → e.tr.denote env = zx (e.denote a x)
  | .x, _ => h6
  | .acc, h => by simpa [ByteExp.noAcc] using h
  | .lit c, _ => rfl
  | .bin op p q, h => by
    have h' : (p.noAcc = true ∨ env 5 = zx a) ∧ (q.noAcc = true ∨ env 5 = zx a) := by
      rcases h with h | h
      · simp only [ByteExp.noAcc, Bool.and_eq_true] at h; exact ⟨.inl h.1, .inl h.2⟩
      · exact ⟨.inr h, .inr h⟩
    have ip := ByteExp.tr_ok a x env h6 p h'.1; have iq := ByteExp.tr_ok a x env h6 q h'.2
    cases op <;> simp only [ByteExp.tr, mask8, AExp.denote, Op.eval, ip, iq, ByteExp.denote, BOp.eval]
    · exact zx_add _ _
    · exact zx_sub _ _
    · exact zx_and _ _
    · exact zx_or _ _
    · exact zx_xor _ _
  | .ite c p q t e, h => by
    have h' : (p.noAcc = true ∨ env 5 = zx a) ∧ (q.noAcc = true ∨ env 5 = zx a) ∧
        (t.noAcc = true ∨ env 5 = zx a) ∧ (e.noAcc = true ∨ env 5 = zx a) := by
      rcases h with h | h
      · simp only [ByteExp.noAcc, Bool.and_eq_true] at h; exact ⟨.inl h.1.1.1, .inl h.1.1.2, .inl h.1.2, .inl h.2⟩
      · exact ⟨.inr h, .inr h, .inr h, .inr h⟩
    have ip := ByteExp.tr_ok a x env h6 p h'.1; have iq := ByteExp.tr_ok a x env h6 q h'.2.1
    have it := ByteExp.tr_ok a x env h6 t h'.2.2.1; have ie := ByteExp.tr_ok a x env h6 e h'.2.2.2
    cases c <;> simp only [ByteExp.tr, AExp.denote, Op.eval, ip, iq, it, ie, ByteExp.denote, ite01, zx_lt, zx_inj]
    · by_cases hc : p.denote a x < q.denote a x <;> simp [hc]
    · by_cases hc : p.denote a x ≤ q.denote a x
      · simp [hc, UInt8.not_lt.mpr hc]
      · simp [hc, UInt8.not_le.mp hc]
    · by_cases hc : p.denote a x = q.denote a x <;> simp [hc]
    · by_cases hc : p.denote a x = q.denote a x <;> simp [hc]

theorem WExp.tr_ok (a : BitVec 64) (x : UInt8) (env : AEnv) (h5 : env 5 = a) (h6 : env 6 = zx x) :
    ∀ w : WExp, w.tr.denote env = w.denote a x
  | .acc => h5
  | .x => h6
  | .const c => rfl
  | .bin op p q => by simp only [WExp.tr, AExp.denote, WExp.denote, WExp.tr_ok a x env h5 h6 p, WExp.tr_ok a x env h5 h6 q]
  | .ite c p q => by
    simp only [WExp.tr, AExp.denote, WExp.denote, WExp.tr_ok a x env h5 h6 p, WExp.tr_ok a x env h5 h6 q,
      WExp.tr_ok a x env h5 h6 c]

/-! ## Statement lists -/

def ExecL : List AStmt → AState → AState → Prop
  | [], σ, σ' => σ' = σ
  | a :: r, σ, σ' => ∃ σ₁, AExec a σ σ₁ ∧ ExecL r σ₁ σ'

theorem ExecL.append : ∀ {a b : List AStmt} {σ σ₁ σ₂ : AState}, ExecL a σ σ₁ → ExecL b σ₁ σ₂ → ExecL (a ++ b) σ σ₂
  | [], _, _, _, _, h1, h2 => by cases h1; exact h2
  | _ :: _, _, _, _, _, ⟨τ, h, h1⟩, h2 => ⟨τ, h, ExecL.append h1 h2⟩

theorem ExecL.foldl : ∀ {l : List AStmt} {a : AStmt} {σ σ₁ σ' : AState}, AExec a σ σ₁ → ExecL l σ₁ σ' →
    AExec (l.foldl .seq a) σ σ'
  | [], _, _, _, _, h, h1 => by cases h1; exact h
  | b :: l, a, _, _, _, h, ⟨τ, hb, h1⟩ => ExecL.foldl (l := l) (a := .seq a b) (.seq h hb) h1

theorem ExecL.one {a : AStmt} {σ σ' : AState} (h : AExec a σ σ') : ExecL [a] σ σ' := ⟨σ', h, rfl⟩

theorem ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := toNat_ofNat_lt h

/-- `for a2 in [0, m)`, `m` in `a_c`: `P 0` before, each iteration takes `P i` to `P (i+1)` -/
theorem loopV_exec {c : Fin 8} (hc : c ≠ 2) {body : AStmt} {m : Nat} (hm : m < 2 ^ 64) (P : Nat → AState → Prop)
    (step : ∀ i τ, i < m → P i τ → τ.env 2 = .ofNat 64 i → τ.env c = .ofNat 64 m →
      ∃ τ', AExec body τ τ' ∧ τ'.env 2 = .ofNat 64 i ∧ τ'.env c = .ofNat 64 m ∧
        P (i + 1) ⟨τ'.env.set 2 (.ofNat 64 (i + 1)), τ'.heap⟩)
    (σ : AState) (hcm : σ.env c = .ofNat 64 m) (h0 : P 0 ⟨σ.env.set 2 0, σ.heap⟩) :
    ∃ σ', AExec (loopV c body) σ σ' ∧ P m σ' ∧ σ'.env c = .ofNat 64 m := by
  obtain ⟨σ', hl, hq⟩ := AExec.loop_inv (c := .bin .ult (.var 2) (.var c))
    (b := .seq body (.assign 2 (.bin .add (.var 2) (.const 1))))
    (fun τ => ∃ i, i ≤ m ∧ τ.env 2 = .ofNat 64 i ∧ τ.env c = .ofNat 64 m ∧ P i τ)
    (fun τ => P m τ ∧ τ.env c = .ofNat 64 m) (fun τ => m - (τ.env 2).toNat)
    (fun τ ⟨i, hi, h2, h1, hP⟩ hcond => by
      simp only [AExp.denote, ult_ne, h2, h1, ofNat_toNat_lt hm, ofNat_toNat_lt (show i < 2 ^ 64 by omega)] at hcond
      obtain ⟨τ', hb, h2', h1', hP'⟩ := step i τ hcond hP h2 h1
      have e : τ'.env 2 + 1 = .ofNat 64 (i + 1) := by rw [h2', BitVec.ofNat_add]; rfl
      refine ⟨_, .seq hb (AExec.assign' rfl), ⟨i + 1, hcond, ?_, ?_, ?_⟩, ?_⟩
      · simp only [AEnv.set, AExp.denote, Op.eval, if_true]; exact e
      · simp only [AEnv.set, if_neg hc]; exact h1'
      · simp only [AExp.denote, Op.eval, e]; exact hP'
      · simp only [AEnv.set, AExp.denote, Op.eval, e, if_true, h2, ofNat_toNat_lt (show i < 2 ^ 64 by omega),
          ofNat_toNat_lt (show i + 1 < 2 ^ 64 by omega)]; omega)
    (fun τ ⟨i, hi, h2, h1, hP⟩ hcond => by
      have : ¬ i < m := fun hlt => (ult_ne (a := τ.env 2) (b := τ.env c)).2
        (by rw [h2, h1, ofNat_toNat_lt hm, ofNat_toNat_lt (show i < 2 ^ 64 by omega)]; exact hlt) hcond
      have : i = m := by omega
      subst this; exact ⟨hP, h1⟩)
    ⟨σ.env.set 2 0, σ.heap⟩ ⟨0, Nat.zero_le _, by simp [AEnv.set], by simp only [AEnv.set, if_neg hc]; exact hcm, h0⟩
  exact ⟨σ', .seq (AExec.assign' rfl) hl, hq⟩

/-! ## Views -/

abbrev tbs (l : List UInt8) : List (BitVec 8) := l.map (·.toBitVec)

def dirL (rev : Bool) (l : List UInt8) : List UInt8 := if rev then l.reverse else l
def applyAll (fs : List (UInt8 → UInt8)) (x : UInt8) : UInt8 := fs.foldl (fun x f => f x) x
/-- `g` computes `f` on the element in `a6` -/
def ExactG (g : AExp) (f : UInt8 → UInt8) : Prop := ∀ (env : AEnv) (x : UInt8), env 6 = zx x → g.denote env = zx (f x)

/-- block index of view element `i` -/
def idxN (rev : Bool) (s m i : Nat) : Nat := if rev then s + m - 1 - i else s + i

theorem view_get {B : List UInt8} {s m i : Nat} (rev : Bool) (hb : s + m ≤ B.length) (hi : i < m) :
    (dirL rev ((B.drop s).take m))[i]? = B[idxN rev s m i]? := by
  have hl : ((B.drop s).take m).length = m := by simp; omega
  cases rev <;> simp only [dirL, idxN, Bool.false_eq_true, if_false, if_true]
  · rw [List.getElem?_take, if_pos hi, List.getElem?_drop]
  · rw [List.getElem?_reverse (by omega), hl, List.getElem?_take, if_pos (by omega), List.getElem?_drop]
    congr 1; omega

theorem view_len {B : List UInt8} {s m : Nat} (rev : Bool) (hb : s + m ≤ B.length) :
    (dirL rev ((B.drop s).take m)).length = m := by
  cases rev <;> simp [dirL] <;> omega

theorem vIdx_val {env : AEnv} {s m i : Nat} (rev : Bool) (h4 : (env 4).toNat = s) (h1 : (env 1).toNat = m)
    (h2 : env 2 = .ofNat 64 i) (hi : i < m) (hb : s + m < 2 ^ 63) :
    ((vIdx rev).denote env).toNat = idxN rev s m i := by
  have e2 : (env 2).toNat = i := by rw [h2]; exact ofNat_toNat_lt (by omega)
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  cases rev <;> simp only [vIdx, idxN, Bool.false_eq_true, if_false, if_true, AExp.denote, Op.eval]
  · rw [BitVec.toNat_add, h4, e2]; omega
  · rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add, h4, h1, e2, e1]; omega

inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a b l₁ l₂} : R a b → All2 R l₁ l₂ → All2 R (a :: l₁) (b :: l₂)

/-- the state/list relation maintained between stages -/
structure Inv (L : Nat) (cs : CS) (xs cur : List UInt8) (σ : AState) (out : List UInt8)
    (fs : List (UInt8 → UInt8)) : Prop where
  heap : σ.heap = [tbs xs, tbs out]
  olen : out.length = L
  fsok : All2 ExactG cs.gs fs
  bound : (σ.env 4).toNat + (σ.env 1).toNat ≤ (if cs.onOut then out else xs).length
  cur : cur = (dirL cs.rev (((if cs.onOut then out else xs).drop (σ.env 4).toNat).take (σ.env 1).toNat)).map
    (applyAll fs)
  s0 : cs.s0 = true → σ.env 4 = 0

def InvE (L : Nat) (cs : CS) (xs cur : List UInt8) (σ : AState) : Prop := ∃ out fs, Inv L cs xs cur σ out fs

theorem Inv.len {L cs xs cur σ out fs} (h : Inv L cs xs cur σ out fs) : cur.length = (σ.env 1).toNat := by
  rw [h.cur, List.length_map, view_len _ h.bound]

theorem set_set (env : AEnv) (v : Fin 8) (a b : BitVec 64) : (env.set v a).set v b = env.set v b := by
  funext i; simp only [AEnv.set]; split <;> rfl

theorem fetchG_exec {gs : List AExp} {fs : List (UInt8 → UInt8)} (hf : All2 ExactG gs fs) :
    ∀ {p : AStmt} {τ τ₁ : AState} {y : UInt8}, AExec p τ τ₁ → τ₁.heap = τ.heap → τ₁.env = τ.env.set 6 (zx y) →
    ∃ τ', AExec (fetchG p gs) τ τ' ∧ τ'.heap = τ.heap ∧ τ'.env = τ.env.set 6 (zx (applyAll fs y)) := by
  induction hf with
  | nil => intro p τ τ₁ y h hh he; exact ⟨τ₁, h, hh, he⟩
  | cons hg _ ih =>
    intro p τ τ₁ y h hh he
    refine ih (y := _) (.seq h .assign) hh ?_
    show (τ₁.env.set 6 _) = _
    rw [he, set_set, hg _ y (by simp [AEnv.set])]

/-- `fetch`: `a6 := zx (pending maps (block[t]))` where `t` is the value of the index expression -/
theorem fetch_exec {cs : CS} {fs : List (UInt8 → UInt8)} (hf : All2 ExactG cs.gs fs)
    {env : AEnv} {xs o : List UInt8} {t : Nat} (ht : ((vIdx cs.rev).denote env).toNat = t)
    (hlt : t < (if cs.onOut then o else xs).length) :
    ∃ τ', AExec (fetch cs) ⟨env, [tbs xs, tbs o]⟩ τ' ∧ τ'.heap = [tbs xs, tbs o] ∧
      τ'.env = env.set 6 (zx (applyAll fs ((if cs.onOut then o else xs)[t]))) := by
  subst ht
  obtain ⟨onOut, rev, s0, gs⟩ := cs
  cases onOut <;> simp only [if_true, Bool.false_eq_true, if_false] at hlt ⊢
  · refine fetchG_exec hf (τ := ⟨env, [tbs xs, tbs o]⟩) (y := _) (.load (b := 0) (by simp) (by simpa using hlt)) rfl ?_
    simp [zx]
  · refine fetchG_exec hf (τ := ⟨env, [tbs xs, tbs o]⟩) (y := _) (.load (b := 1) (by simp) (by simpa using hlt)) rfl ?_
    simp [zx]

/-! ## Materialization loop -/

theorem getElem?_some_of {l : List UInt8} {i : Nat} (h : i < l.length) : l[i]? = some l[i] := List.getElem?_eq_getElem h

theorem heap_set1 (a : List (BitVec 8)) (o : List UInt8) (i : Nat) (u : UInt8) :
    ([a, tbs o] : Heap).set 1 ((tbs o).set i u.toBitVec) = [a, tbs (o.set i u)] := by
  simp [List.map_set]

/-- the loop writing the view to `out[0..m)`; in place (view on the output block) only forwards -/
theorem matLoop_exec {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} {out : List UInt8}
    {fs : List (UInt8 → UInt8)} (hI : Inv L cs xs cur σ out fs) (hrev : cs.onOut = true → cs.rev = false)
    (hsp : cur.length ≤ L) (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ' out', AExec (loopV 1 (.seq (fetch cs) (.store 1 (.var 2) (.var 6)))) σ σ' ∧
      σ'.heap = [tbs xs, tbs out'] ∧ out'.length = L ∧ out'.take cur.length = cur ∧ σ'.env 1 = σ.env 1 := by
  obtain ⟨env, heap⟩ := σ
  have hh := hI.heap; dsimp only at hh; subst hh
  have hlen := hI.len; dsimp only at hlen
  have hbd := hI.bound; dsimp only at hbd
  have hcur := hI.cur; dsimp only at hcur
  have hol0 := hI.olen
  generalize hs : (env 4).toNat = s at *
  generalize hm : (env 1).toNat = m at *
  have hBl : (if cs.onOut then out else xs).length < 2 ^ 32 := by split <;> omega
  obtain ⟨σ', hex, ⟨h4, o, hho, hol, hpre, -⟩, h1⟩ := loopV_exec (c := 1) (by decide) (m := m) (by omega)
    (fun i τ => τ.env 4 = env 4 ∧ ∃ o : List UInt8, τ.heap = [tbs xs, tbs o] ∧ o.length = L ∧
      (∀ k, k < i → o[k]? = cur[k]?) ∧
      (∀ j, i ≤ j → j < m → (if cs.onOut then o else xs)[idxN cs.rev s m j]? =
        (if cs.onOut then out else xs)[idxN cs.rev s m j]?))
    (fun i ⟨env', heap'⟩ hi ⟨h4, o, hho, hol, hpre, hsrc⟩ h2 h1 => by
      dsimp only at h4 hho h2 h1; subst hho
      have ht := vIdx_val cs.rev (env := env') (s := s) (m := m) (by rw [h4]; exact hs) (by rw [h1]; exact ofNat_toNat_lt (by omega))
        h2 hi (by omega)
      have hsi := hsrc i (Nat.le_refl _) hi
      have hidx : idxN cs.rev s m i < s + m := by unfold idxN; split <;> omega
      have hlt : idxN cs.rev s m i < (if cs.onOut then o else xs).length := by
        have : (if cs.onOut then o else xs).length = (if cs.onOut then out else xs).length := by split <;> omega
        omega
      have hci : cur[i]? = some (applyAll fs ((if cs.onOut then o else xs)[idxN cs.rev s m i])) := by
        rw [hcur, List.getElem?_map, view_get _ hbd hi, ← hsi, getElem?_some_of hlt]; rfl
      obtain ⟨⟨env'', heap''⟩, hf, hfh, hfe⟩ := fetch_exec hI.fsok ht hlt
      dsimp only at hfh hfe; subst hfh hfe
      generalize applyAll fs ((if cs.onOut then o else xs)[idxN cs.rev s m i]) = u at *
      have hio : i < o.length := by omega
      have e2 : ((AExp.var 2).denote (env'.set 6 (zx u))).toNat = i := by
        simp only [AExp.denote, AEnv.set, Fin.reduceEq, if_false, h2]; exact ofNat_toNat_lt (by omega)
      refine ⟨_, .seq hf (AExec.store (b := 1) (i := .var 2) (e := .var 6) (σ := ⟨env'.set 6 (zx u), [tbs xs, tbs o]⟩)
        (by simp) (by rw [e2]; simpa using hio)), ?_, ?_, ?_, ?_⟩
      · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h2
      · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h1
      · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h4
      · refine ⟨o.set i u, ?_, by simpa using hol, fun k hk => ?_, fun j hj hjm => ?_⟩
        · simp only [e2]
          simp only [AExp.denote, AEnv.set, if_true, zx_setWidth, List.getElem_cons_succ, List.getElem_cons_zero]
          exact heap_set1 _ _ _ _
        · by_cases hki : k = i
          · subst hki; rw [List.getElem?_set_self hio, hci]
          · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hpre k (by omega)
        · have := hsrc j (by omega) hjm
          cases hO : cs.onOut
          · simp
          · simp only [hO, if_true] at this ⊢
            rw [hrev hO] at this ⊢
            simp only [idxN, Bool.false_eq_true, if_false] at this ⊢
            rw [List.getElem?_set_ne (by omega)]; exact this)
    ⟨env, [tbs xs, tbs out]⟩ (by rw [← hm]; simp) ⟨by simp [AEnv.set], out, rfl, hol0, fun k hk => absurd hk (by omega),
      fun j _ _ => rfl⟩
  refine ⟨σ', o, hex, hho, hol, ?_, ?_⟩
  · apply List.ext_getElem?; intro k
    rw [List.getElem?_take]
    split
    · exact hpre k (by omega)
    · exact (List.getElem?_eq_none (by omega)).symm
  · rw [h1]; simp [← hm]

/-! ## In-place reversal of the window -/

theorem rev_exec {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} {out : List UInt8}
    {fs : List (UInt8 → UInt8)} (hI : Inv L cs xs cur σ out fs) (hO : cs.onOut = true) (hR : cs.rev = true)
    (hL : L < 2 ^ 32) :
    ∃ σ' out', ExecL revC σ σ' ∧ Inv L { cs with rev := false } xs cur σ' out' fs := by
  obtain ⟨env, heap⟩ := σ
  have hh := hI.heap; dsimp only at hh; subst hh
  have hbd := hI.bound; simp only [hO, if_true] at hbd
  have hcur := hI.cur; simp only [hO, hR, if_true] at hcur
  have hol0 := hI.olen
  generalize hs : (env 4).toNat = s at *
  generalize hm : (env 1).toNat = m at *
  have h7 : (env.set 7 ((AExp.bin .lshr (.var 1) (.const 1)).denote env)) 7 = .ofNat 64 (m / 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [AEnv.set, if_true, AExp.denote, Op.eval, BitVec.toNat_ushiftRight, hm]
    rw [ofNat_toNat_lt (by omega)]; rfl
  obtain ⟨σ', hex, ⟨h4, h1, o, hho, hol, hall⟩, -⟩ := loopV_exec (c := 7) (by decide) (m := m / 2) (by omega)
    (body := .seq (.load 5 1 (vIdx false)) (.seq (.load 6 1 (vIdx true))
      (.seq (.store 1 (vIdx false) (.var 6)) (.store 1 (vIdx true) (.var 5)))))
    (fun i τ => τ.env 4 = env 4 ∧ τ.env 1 = env 1 ∧ ∃ o : List UInt8, τ.heap = [tbs xs, tbs o] ∧ o.length = L ∧
      ∀ k, o[k]? = if s ≤ k ∧ k < s + m ∧ (k - s < i ∨ m - i ≤ k - s) then out[s + m - 1 - (k - s)]? else out[k]?)
    (fun i ⟨env', heap'⟩ hi ⟨h4, h1, o, hho, hol, hall⟩ h2 h7 => by
      dsimp only at h4 h1 hho h2 h7; subst hho
      have him : i < m := by omega
      have hp := vIdx_val false (env := env') (s := s) (m := m) (by rw [h4]; exact hs) (by rw [h1]; exact hm) h2 him (by omega)
      have hq := vIdx_val true (env := env') (s := s) (m := m) (by rw [h4]; exact hs) (by rw [h1]; exact hm) h2 him (by omega)
      simp only [idxN, Bool.false_eq_true, if_false, if_true] at hp hq
      have hpl : s + i < o.length := by omega
      have hql : s + m - 1 - i < o.length := by omega
      have hop : o[s + i]? = out[s + i]? := by rw [hall, if_neg (by omega)]
      have hoq : o[s + m - 1 - i]? = out[s + m - 1 - i]? := by rw [hall, if_neg (by omega)]
      -- the four statements
      let e1 : AEnv := env'.set 5 (zx o[s + i])
      let e2 : AEnv := e1.set 6 (zx o[s + m - 1 - i])
      have hp1 : ((vIdx false).denote e2).toNat = s + i := by
        have := vIdx_val false (env := e2) (s := s) (m := m) (i := i) (by simp [e2, e1, AEnv.set, h4, hs])
          (by simp [e2, e1, AEnv.set, h1, hm]) (by simp [e2, e1, AEnv.set, h2]) him (by omega)
        simpa [idxN] using this
      have hq1 : ((vIdx true).denote e1).toNat = s + m - 1 - i := by
        have := vIdx_val true (env := e1) (s := s) (m := m) (i := i) (by simp [e1, AEnv.set, h4, hs])
          (by simp [e1, AEnv.set, h1, hm]) (by simp [e1, AEnv.set, h2]) him (by omega)
        simpa [idxN] using this
      have hq2 : ((vIdx true).denote e2).toNat = s + m - 1 - i := by
        have := vIdx_val true (env := e2) (s := s) (m := m) (i := i) (by simp [e2, e1, AEnv.set, h4, hs])
          (by simp [e2, e1, AEnv.set, h1, hm]) (by simp [e2, e1, AEnv.set, h2]) him (by omega)
        simpa [idxN] using this
      have x1 : AExec (.load 5 1 (vIdx false)) ⟨env', [tbs xs, tbs o]⟩ ⟨e1, [tbs xs, tbs o]⟩ := by
        have := AExec.load (v := 5) (b := 1) (i := vIdx false) (σ := ⟨env', [tbs xs, tbs o]⟩) (by simp)
          (by rw [hp]; simpa using hpl)
        simpa [hp, e1, zx] using this
      have x2 : AExec (.load 6 1 (vIdx true)) ⟨e1, [tbs xs, tbs o]⟩ ⟨e2, [tbs xs, tbs o]⟩ := by
        have := AExec.load (v := 6) (b := 1) (i := vIdx true) (σ := ⟨e1, [tbs xs, tbs o]⟩) (by simp)
          (by rw [hq1]; simpa using hql)
        simpa [hq1, e2, zx] using this
      have x3 : AExec (.store 1 (vIdx false) (.var 6)) ⟨e2, [tbs xs, tbs o]⟩
          ⟨e2, [tbs xs, tbs (o.set (s + i) o[s + m - 1 - i])]⟩ := by
        have := AExec.store (b := 1) (i := vIdx false) (e := .var 6) (σ := ⟨e2, [tbs xs, tbs o]⟩) (by simp)
          (by rw [hp1]; simpa using hpl)
        simp only [hp1, List.getElem_cons_succ, List.getElem_cons_zero] at this
        rw [show ((AExp.var 6).denote e2).setWidth 8 = (o[s + m - 1 - i]).toBitVec from by
          simp [AExp.denote, e2, AEnv.set, zx_setWidth], heap_set1] at this
        exact this
      have x4 : AExec (.store 1 (vIdx true) (.var 5)) ⟨e2, [tbs xs, tbs (o.set (s + i) o[s + m - 1 - i])]⟩
          ⟨e2, [tbs xs, tbs ((o.set (s + i) o[s + m - 1 - i]).set (s + m - 1 - i) o[s + i])]⟩ := by
        have := AExec.store (b := 1) (i := vIdx true) (e := .var 5)
          (σ := ⟨e2, [tbs xs, tbs (o.set (s + i) o[s + m - 1 - i])]⟩) (by simp) (by rw [hq2]; simpa using hql)
        simp only [hq2, List.getElem_cons_succ, List.getElem_cons_zero] at this
        rw [show ((AExp.var 5).denote e2).setWidth 8 = (o[s + i]).toBitVec from by
          simp [AExp.denote, e2, e1, AEnv.set, zx_setWidth], heap_set1] at this
        exact this
      refine ⟨_, .seq x1 (.seq x2 (.seq x3 x4)), by simp [e2, e1, AEnv.set, h2], by simp [e2, e1, AEnv.set, h7],
        by simp [e2, e1, AEnv.set, h4], by simp [e2, e1, AEnv.set, h1], _, rfl, by simpa using hol, fun k => ?_⟩
      by_cases hkq : k = s + m - 1 - i
      · subst hkq
        rw [List.getElem?_set_self (by simpa using hql), if_pos (by omega), ← getElem?_some_of hpl, hop]
        congr 1; omega
      · rw [List.getElem?_set_ne (Ne.symm hkq)]
        by_cases hkp : k = s + i
        · subst hkp
          rw [List.getElem?_set_self hpl, if_pos (by omega), ← getElem?_some_of hql, hoq]
          congr 1; omega
        · rw [List.getElem?_set_ne (Ne.symm hkp), hall k]
          split <;> split <;> first | rfl | (exfalso; omega))
    ⟨env.set 7 ((AExp.bin .lshr (.var 1) (.const 1)).denote env), [tbs xs, tbs out]⟩ h7
    ⟨by simp [AEnv.set], by simp [AEnv.set], out, rfl, hol0, fun k => by rw [if_neg (by omega)]⟩
  obtain ⟨env₁, heap₁⟩ := σ'
  dsimp only at h4 h1 hho; subst hho
  have key : (o.drop s).take m = ((out.drop s).take m).reverse := by
    apply List.ext_getElem?; intro j
    by_cases hj : j < m
    · have a := view_get (B := o) false (s := s) (m := m) (by omega) hj
      have b := view_get (B := out) true (s := s) (m := m) (by omega) hj
      simp only [dirL, idxN, Bool.false_eq_true, if_false, if_true] at a b
      rw [a, b, hall]
      split
      · congr 1; omega
      · congr 1; omega
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  refine ⟨_, o, ⟨_, AExec.assign' rfl, ExecL.one hex⟩, ⟨rfl, hol, hI.fsok, ?_, ?_, fun h => ?_⟩⟩
  · simp only [hO, if_true, h4, h1, hs, hm]; omega
  · simp only [hO, if_true, h4, h1, hs, hm, dirL, Bool.false_eq_true, if_false, key]; exact hcur
  · show env₁ 4 = 0; rw [h4]; exact hI.s0 h

/-! ## Fold loop and accumulator bytes -/

theorem foldLoop_exec {α : Type} (enc : α → BitVec 64) (F : α → UInt8 → α) (S : AExp)
    (hS : ∀ (env : AEnv) (a : α) (x : UInt8), env 5 = enc a → env 6 = zx x → S.denote env = enc (F a x))
    {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} {out : List UInt8} {fs : List (UInt8 → UInt8)}
    (hI : Inv L cs xs cur σ out fs) (init : α) (h5 : σ.env 5 = enc init) (hx : xs.length < 2 ^ 32)
    (hL : L < 2 ^ 32) :
    ∃ σ', AExec (loopV 1 (.seq (fetch cs) (.assign 5 S))) σ σ' ∧ σ'.heap = σ.heap ∧
      σ'.env 5 = enc (cur.foldl F init) := by
  obtain ⟨env, heap⟩ := σ
  have hh := hI.heap; dsimp only at hh h5 ⊢; subst hh
  have hlen := hI.len; dsimp only at hlen
  have hbd := hI.bound; dsimp only at hbd
  have hcur := hI.cur; dsimp only at hcur
  have hol0 := hI.olen
  generalize hs : (env 4).toNat = s at *
  generalize hm : (env 1).toNat = m at *
  have hBl : (if cs.onOut then out else xs).length < 2 ^ 32 := by split <;> omega
  obtain ⟨σ', hex, ⟨h4, hho, hacc⟩, h1⟩ := loopV_exec (c := 1) (by decide) (m := m) (by omega)
    (fun i τ => τ.env 4 = env 4 ∧ τ.heap = [tbs xs, tbs out] ∧ τ.env 5 = enc ((cur.take i).foldl F init))
    (fun i ⟨env', heap'⟩ hi ⟨h4, hho, hacc⟩ h2 h1 => by
      dsimp only at h4 hho h2 h1 hacc; subst hho
      have ht := vIdx_val cs.rev (env := env') (s := s) (m := m) (by rw [h4]; exact hs) (by rw [h1]; exact ofNat_toNat_lt (by omega))
        h2 hi (by omega)
      have hlt : idxN cs.rev s m i < (if cs.onOut then out else xs).length := by
        have : idxN cs.rev s m i < s + m := by unfold idxN; split <;> omega
        omega
      have hci : cur[i]? = some (applyAll fs ((if cs.onOut then out else xs)[idxN cs.rev s m i])) := by
        rw [hcur, List.getElem?_map, view_get _ hbd hi, getElem?_some_of hlt]; rfl
      obtain ⟨⟨env'', heap''⟩, hf, hfh, hfe⟩ := fetch_exec hI.fsok ht hlt
      dsimp only at hfh hfe; subst hfh hfe
      generalize applyAll fs ((if cs.onOut then out else xs)[idxN cs.rev s m i]) = u at *
      refine ⟨_, .seq hf (AExec.assign (v := 5) (e := S) (σ := ⟨env'.set 6 (zx u), [tbs xs, tbs out]⟩)),
        ?_, ?_, ?_, rfl, ?_⟩
      · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h2
      · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h1
      · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h4
      · simp only [AEnv.set, Fin.reduceEq, if_false, if_true]
        rw [hS _ _ u (by simp only [AEnv.set, Fin.reduceEq, if_false]; exact hacc) (by simp [AEnv.set]),
          List.take_add_one, List.foldl_append, hci]; rfl)
    ⟨env, [tbs xs, tbs out]⟩ (by rw [← hm]; simp) ⟨by simp [AEnv.set], rfl, by simpa [AEnv.set] using h5⟩
  refine ⟨σ', hex, hho, ?_⟩
  rw [hacc, List.take_of_length_le (by omega)]

theorem leBytes_get (A : BitVec 64) {k i : Nat} (h : i < k) : (leBytes A k)[i]? = some ⟨(A >>> (8 * i)).setWidth 8⟩ := by
  simp [leBytes, h]

theorem emit_exec {L k : Nat} {xs out : List UInt8} {env : AEnv} (hol : out.length = L) (hk : k ≤ 8) (hkL : k ≤ L) :
    ∃ σ' out', ExecL (emitC k) ⟨env, [tbs xs, tbs out]⟩ σ' ∧ σ'.heap = [tbs xs, tbs out'] ∧ out'.length = L ∧
      out'.take k = leBytes (env 5) k ∧ σ'.env 1 = .ofNat 64 k ∧ σ'.env 4 = 0 := by
  obtain ⟨σ', hex, ⟨h5, o, hho, hol', hpre⟩, h1⟩ := loopV_exec (c := 1) (by decide) (m := k) (by omega)
    (body := .store 1 (.var 2) (.bin .lshr (.var 5) (.bin .shl (.var 2) (.const 3))))
    (fun i τ => τ.env 5 = env 5 ∧ ∃ o : List UInt8, τ.heap = [tbs xs, tbs o] ∧ o.length = L ∧
      ∀ j, j < i → o[j]? = (leBytes (env 5) k)[j]?)
    (fun i ⟨env', heap'⟩ hi ⟨h5, o, hho, hol', hpre⟩ h2 h1 => by
      dsimp only at h5 hho h2 h1; subst hho
      have e2 : ((AExp.var 2).denote env').toNat = i := by
        simp only [AExp.denote, h2]; exact ofNat_toNat_lt (by omega)
      have hio : i < o.length := by omega
      have hv : ((AExp.bin .lshr (.var 5) (.bin .shl (.var 2) (.const 3))).denote env').setWidth 8 =
          (⟨(env 5 >>> (8 * i)).setWidth 8⟩ : UInt8).toBitVec := by
        simp only [AExp.denote, Op.eval, h2, h5]
        have : ((BitVec.ofNat 64 i <<< ((3 : BitVec 64).toNat % 64)).toNat % 64) = 8 * i := by
          rw [show (3 : BitVec 64).toNat % 64 = 3 from rfl, BitVec.toNat_shiftLeft, ofNat_toNat_lt (by omega),
            Nat.shiftLeft_eq]; omega
        rw [this]
      have := AExec.store (b := 1) (i := .var 2) (e := .bin .lshr (.var 5) (.bin .shl (.var 2) (.const 3)))
        (σ := ⟨env', [tbs xs, tbs o]⟩) (by simp) (by rw [e2]; simpa using hio)
      simp only [e2, List.getElem_cons_succ, List.getElem_cons_zero] at this
      rw [hv, heap_set1] at this
      refine ⟨_, this, h2, h1, h5, _, rfl, by simpa using hol', fun j hj => ?_⟩
      by_cases hji : j = i
      · subst hji; rw [List.getElem?_set_self hio, leBytes_get _ hi]
      · rw [List.getElem?_set_ne (Ne.symm hji)]; exact hpre j (by omega))
    ⟨env.set 1 (.ofNat 64 k), [tbs xs, tbs out]⟩ (by simp [AEnv.set])
    ⟨by simp [AEnv.set], out, rfl, hol, fun j hj => absurd hj (by omega)⟩
  refine ⟨_, o, ⟨_, AExec.assign' rfl, _, hex, ExecL.one (AExec.assign' rfl)⟩, hho, hol', ?_, ?_, ?_⟩
  · apply List.ext_getElem?; intro j
    rw [List.getElem?_take]
    split
    · exact hpre j (by omega)
    · exact (List.getElem?_eq_none (by simp [leBytes]; omega)).symm
  · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h1
  · simp [AEnv.set, AExp.denote]

/-! ## Frame: a program run on longer blocks -/

/-- `H'` is `H` with `J b` appended to block `b` -/
def Ext (J : Nat → List (BitVec 8)) (H H' : Heap) : Prop :=
  H'.length = H.length ∧ ∀ b (h : b < H.length) (h' : b < H'.length), H'[b] = H[b] ++ J b

theorem AExec.frame {J : Nat → List (BitVec 8)} {p : AStmt} {σ σ' : AState} (h : AExec p σ σ') :
    ∀ {H' : Heap}, Ext J σ.heap H' → ∃ K', AExec p ⟨σ.env, H'⟩ ⟨σ'.env, K'⟩ ∧ Ext J σ'.heap K' := by
  induction h with
  | assign => intro H' hE; exact ⟨H', .assign, hE⟩
  | @load v b i σ hb hi =>
    intro H' hE
    have hb' : b < H'.length := hE.1 ▸ hb
    have e := hE.2 b hb hb'
    have hi' : (i.denote σ.env).toNat < H'[b].length := by rw [e, List.length_append]; omega
    have key : H'[b][(i.denote σ.env).toNat] = σ.heap[b][(i.denote σ.env).toNat] := by
      simp [e, List.getElem_append_left hi]
    have := AExec.load (v := v) (b := b) (i := i) (σ := ⟨σ.env, H'⟩) hb' hi'
    dsimp only at this; rw [key] at this
    exact ⟨H', this, hE⟩
  | @store b i e σ hb hi =>
    intro H' hE
    have hb' : b < H'.length := hE.1 ▸ hb
    have eb := hE.2 b hb hb'
    have hi' : (i.denote σ.env).toNat < H'[b].length := by rw [eb, List.length_append]; omega
    refine ⟨_, AExec.store (b := b) (i := i) (e := e) (σ := ⟨σ.env, H'⟩) hb' hi', by simp [hE.1], fun b' h h' => ?_⟩
    simp only [List.length_set] at h h'
    simp only [List.getElem_set]
    by_cases hbb : b = b'
    · subst hbb; simp only [if_true, eb]; exact List.set_append_left _ _ hi
    · simp only [if_neg hbb]; exact hE.2 b' h h'
  | seq _ _ ih1 ih2 =>
    intro H' hE
    obtain ⟨K₁, x1, hE₁⟩ := ih1 hE
    obtain ⟨K₂, x2, hE₂⟩ := ih2 hE₁
    exact ⟨K₂, .seq x1 x2, hE₂⟩
  | loopF hc => intro H' hE; exact ⟨H', .loopF hc, hE⟩
  | loopT hc _ _ ih1 ih2 =>
    intro H' hE
    obtain ⟨K₁, x1, hE₁⟩ := ih1 hE
    obtain ⟨K₂, x2, hE₂⟩ := ih2 hE₁
    exact ⟨K₂, .loopT hc x1 x2, hE₂⟩

/-! ## Stages -/

theorem applyAll_nil : applyAll [] = id := rfl

theorem All2.snoc {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} (h : All2 R l₁ l₂) {a : α} {b : β}
    (hab : R a b) : All2 R (l₁ ++ [a]) (l₂ ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons h _ ih => exact .cons h ih

theorem clean_eq {cs : CS} (h : cs.clean = true) : cs = csClean := by
  obtain ⟨a, b, c, d⟩ := cs
  simp only [CS.clean, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; rfl

/-- a clean view: the list is the first `m` output bytes -/
theorem Inv.clean {L xs cur σ out fs} (h : Inv L csClean xs cur σ out fs) :
    fs = [] ∧ σ.env 4 = 0 ∧ cur = out.take (σ.env 1).toNat ∧ (σ.env 1).toNat ≤ L := by
  have hf := h.fsok; simp only [csClean] at hf; cases hf
  have h4 := h.s0 rfl
  have hb := h.bound; have hc := h.cur
  simp [csClean, h4, dirL, applyAll_nil] at hb hc
  exact ⟨rfl, h4, hc, h.olen ▸ hb⟩

theorem Inv.ofClean {L xs cur out} {env : AEnv} (hol : out.length = L) (h4 : env 4 = 0)
    (hc : out.take (env 1).toNat = cur) (hm : (env 1).toNat ≤ L) :
    Inv L csClean xs cur ⟨env, [tbs xs, tbs out]⟩ out [] :=
  ⟨rfl, hol, .nil, by simp [csClean, h4]; omega, by simp [csClean, h4, dirL, applyAll_nil, hc], fun _ => h4⟩

theorem mat_exec {L : Nat} {xs : List UInt8} (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) {cs : CS}
    {cur : List UInt8} {σ : AState} (hI : InvE L cs xs cur σ) (hsp : cs.clean = true ∨ cur.length ≤ L) :
    ∃ σ', ExecL (mat cs) σ σ' ∧ InvE L csClean xs cur σ' := by
  by_cases hcl : cs.clean = true
  · refine ⟨σ, by simp [mat, hcl, ExecL], ?_⟩
    rw [← clean_eq hcl]; exact hI
  have hsp : cur.length ≤ L := hsp.resolve_left hcl
  obtain ⟨out, fs, hI⟩ := hI
  simp only [mat, hcl, Bool.false_eq_true, if_false]
  -- optional in-place reversal
  obtain ⟨σ₁, out₁, hex₁, hI₁, hrev⟩ : ∃ σ₁ out₁, ExecL (if (cs.onOut && cs.rev) = true then revC else []) σ σ₁ ∧
      Inv L { cs with rev := cs.rev && !cs.onOut } xs cur σ₁ out₁ fs ∧ (cs.onOut = true → (cs.rev && !cs.onOut) = false) := by
    by_cases hOR : (cs.onOut && cs.rev) = true
    · simp only [Bool.and_eq_true] at hOR
      obtain ⟨σ₁, out₁, hex, hI₁⟩ := rev_exec hI hOR.1 hOR.2 hL
      refine ⟨σ₁, out₁, by simpa [hOR.1, hOR.2] using hex, by simpa [hOR.1, hOR.2] using hI₁, by simp [hOR.1]⟩
    · refine ⟨σ, out, by simp [hOR, ExecL], ?_, by intro h; simp [h]⟩
      have : ({ cs with rev := cs.rev && !cs.onOut } : CS) = cs := by
        obtain ⟨a, b, c, d⟩ := cs; cases a <;> cases b <;> simp_all
      rw [this]; exact hI
  obtain ⟨σ₂, out₂, hex₂, hh₂, hol₂, htk, h1⟩ := matLoop_exec hI₁ hrev hsp hx hL
  have hlen := hI₁.len
  obtain ⟨env₂, heap₂⟩ := σ₂
  dsimp only at hh₂ h1; subst hh₂
  refine ⟨_, ExecL.append hex₁ ⟨_, hex₂, ExecL.one (AExec.assign' rfl)⟩, out₂, [], ?_⟩
  refine Inv.ofClean hol₂ (by simp [AEnv.set, AExp.denote]) ?_ ?_
  · simp only [AEnv.set, Fin.reduceEq, if_false, h1, ← hlen]; exact htk
  · simp only [AEnv.set, Fin.reduceEq, if_false, h1, ← hlen]; exact hsp

theorem tbs_append (a b : List UInt8) : tbs (a ++ b) = tbs a ++ tbs b := List.map_append

theorem sort_exec {L : Nat} {xs cur : List UInt8} {σ : AState} {out : List UInt8} {fs : List (UInt8 → UInt8)}
    (hI : Inv L csClean xs cur σ out fs) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL [insProg, .assign 4 (.const 0)] σ σ' ∧ InvE L csClean xs (cur.mergeSort leU) σ' := by
  obtain ⟨rfl, h4, hcur, hm⟩ := hI.clean
  have hol := hI.olen
  obtain ⟨env, heap⟩ := σ
  have hh := hI.heap; dsimp only at hh h4 hcur hm; subst hh
  generalize hmm : (env 1).toNat = m at *
  have hlen : cur.length = m := by rw [hcur, List.length_take]; omega
  have hout : out = cur ++ out.drop m := by rw [hcur, List.take_append_drop]
  obtain ⟨σ₁, hex, arr, hh₁, hp, hsrt⟩ := ins_exec (tbs xs) (tbs cur) ⟨env, [tbs xs, tbs cur]⟩ rfl
    (by simp [hlen, ← hmm]) (by simp [hlen]; omega)
  obtain ⟨K', hexK, hE⟩ := hex.frame (J := fun b => if b = 1 then tbs (out.drop m) else [])
    (H' := [tbs xs, tbs out]) ⟨rfl, fun b h h' => by
      obtain _ | _ | b := b
      · simp
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, if_true]; rw [← tbs_append, ← hout]
      · simp at h; omega⟩
  have harr : arr = tbs (cur.mergeSort leU) := by
    rw [tbs, mergeSort_toBitVec]
    exact sorted_perm_eq hsrt (sorted_mergeSort _) (hp.trans (List.mergeSort_perm _ leB).symm)
  have hK : K' = [tbs xs, tbs (cur.mergeSort leU ++ out.drop m)] := by
    obtain ⟨hl, hg⟩ := hE
    rw [hh₁] at hl hg
    obtain _ | ⟨a, _ | ⟨b, _ | _⟩⟩ := K' <;> simp at hl
    have g0 := hg 0 (by simp) (by simp); have g1 := hg 1 (by simp) (by simp)
    simp at g0 g1; rw [g0, g1, harr]; simp [tbs, List.map_drop]
  subst hK
  have k1 : σ₁.env 1 = env 1 := hex.env_keep (v := 1) (by decide)
  refine ⟨_, ⟨_, hexK, ExecL.one (AExec.assign' rfl)⟩, _, [], Inv.ofClean ?_ (by simp [AEnv.set, AExp.denote]) ?_ ?_⟩
  · simp [List.length_mergeSort, hlen, hol]; omega
  · simp only [AEnv.set, Fin.reduceEq, if_false, k1, hmm]
    exact List.take_left' (by simp [List.length_mergeSort, hlen])
  · simp only [AEnv.set, Fin.reduceEq, if_false, k1, hmm]; exact hm

theorem minN_val {env : AEnv} {n : Nat} (hn : n < 2 ^ 64) : ((minN n).denote env).toNat = min n (env 1).toNat := by
  simp only [minN, AExp.denote, Op.eval]
  by_cases h : BitVec.ofNat 64 n < env 1
  · have h' := h; rw [BitVec.lt_def, ofNat_toNat_lt hn] at h'
    simp [h, ofNat_toNat_lt hn]; omega
  · have h' := h; rw [BitVec.lt_def, ofNat_toNat_lt hn] at h'
    simp [h]; omega

theorem Inv.set {L cs xs cur out fs} {env : AEnv} {heap : Heap} (h : Inv L cs xs cur ⟨env, heap⟩ out fs) (v : Fin 8)
    (a : BitVec 64) (h1 : v ≠ 1) (h4 : v ≠ 4) : Inv L cs xs cur ⟨env.set v a, heap⟩ out fs := by
  have e1 : env.set v a 1 = env 1 := by simp [AEnv.set, Ne.symm h1]
  have e4 : env.set v a 4 = env 4 := by simp [AEnv.set, Ne.symm h4]
  exact ⟨h.heap, h.olen, h.fsok, by dsimp only; rw [e1, e4]; exact h.bound, by dsimp only; rw [e1, e4]; exact h.cur,
    fun hs => by dsimp only; rw [e4]; exact h.s0 hs⟩

theorem win_len {B : List UInt8} {s m : Nat} (hb : s + m ≤ B.length) : ((B.drop s).take m).length = m := by
  simp; omega

theorem fold_exec {α : Type} (enc : α → BitVec 64) (F : α → UInt8 → α) (S : AExp)
    (hS : ∀ (env : AEnv) (a : α) (x : UInt8), env 5 = enc a → env 6 = zx x → S.denote env = enc (F a x))
    {L : Nat} {cs : CS} {xs cur : List UInt8} {σ : AState} (hI : InvE L cs xs cur σ) (init : α) {k : Nat}
    (hk : k ≤ 8) (hkL : k ≤ L) (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∃ σ', ExecL (foldC cs S (enc init) k) σ σ' ∧
      InvE L csClean xs (leBytes (enc (cur.foldl F init)) k) σ' := by
  obtain ⟨out, fs, hI⟩ := hI
  obtain ⟨env, heap⟩ := σ
  have hI₁ := hI.set 5 (enc init) (by decide) (by decide)
  obtain ⟨⟨env₂, heap₂⟩, hex₂, hh₂, h5⟩ := foldLoop_exec enc F S hS hI₁ init (by simp [AEnv.set]) hx hL
  have hh := hI.heap; dsimp only at hh hh₂ h5; subst hh; subst hh₂
  obtain ⟨⟨env₃, heap₃⟩, out', hex₃, hh₃, hol₃, htk, h1, h4⟩ := emit_exec (xs := xs) (env := env₂) hI.olen hk hkL
  dsimp only at hh₃ h1 h4; subst hh₃
  have e1 : (env₃ 1).toNat = k := by rw [h1]; exact ofNat_toNat_lt (by omega)
  exact ⟨_, ⟨_, AExec.assign' rfl, _, hex₂, hex₃⟩, out', [],
    Inv.ofClean hol₃ h4 (by rw [e1, htk, h5]) (by rw [e1]; exact hkL)⟩

theorem Stage.denote_len (st : Stage) (l : List UInt8) : (st.denote l).length = st.len l.length := by
  cases st <;> simp [Stage.denote, Stage.len, leBytes, List.length_mergeSort]

theorem stage_exec {L : Nat} {xs : List UInt8} (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) (st : Stage) {cs : CS}
    {cur : List UInt8} {σ : AState} (hc : st.chk = none) (hI : InvE L cs xs cur σ)
    (hsp : st.space cs cur.length ≤ L) :
    ∃ σ', ExecL (stageC st cs).1 σ σ' ∧ InvE L (stageC st cs).2 xs (st.denote cur) σ' := by
  cases st with
  | map e =>
    obtain ⟨out, fs, hI⟩ := hI
    have hna : e.noAcc = true := by
      simp only [Stage.chk] at hc; by_cases h : e.noAcc = true
      · exact h
      · simp [h] at hc
    refine ⟨σ, rfl, out, fs ++ [fun x => e.denote 0 x], hI.heap, hI.olen,
      hI.fsok.snoc fun env x h6 => ByteExp.tr_ok 0 x env h6 e (.inl hna), hI.bound, ?_, hI.s0⟩
    simp only [Stage.denote, stageC]
    rw [hI.cur, List.map_map]
    congr 1; funext x; simp [applyAll, List.foldl_append]
  | reverse =>
    obtain ⟨out, fs, hI⟩ := hI
    refine ⟨σ, rfl, out, fs, hI.heap, hI.olen, hI.fsok, hI.bound, ?_, hI.s0⟩
    simp only [Stage.denote, stageC]
    rw [hI.cur, ← List.map_reverse]
    obtain ⟨a, b, c, d⟩ := cs
    cases b <;> simp [dirL] <;> rfl
  | sort =>
    obtain ⟨σ₁, hex₁, out₁, fs₁, hI₁⟩ := mat_exec hx hL hI (by
      simp only [Stage.space] at hsp
      by_cases h : cs.clean = true
      · exact .inl h
      · simp only [h, Bool.false_eq_true, if_false] at hsp; exact .inr hsp)
    obtain ⟨σ₂, hex₂, hI₂⟩ := sort_exec hI₁ hL
    exact ⟨σ₂, ExecL.append hex₁ hex₂, hI₂⟩
  | fold e i =>
    obtain ⟨σ', hex, hI'⟩ := fold_exec zx (fun a x => e.denote a x) e.tr
      (fun env a x h5 h6 => ByteExp.tr_ok a x env h6 e (.inr h5)) hI i (k := 1) (by omega) hsp hx hL
    refine ⟨σ', hex, ?_⟩
    have : leBytes (zx (cur.foldl (fun a x => e.denote a x) i)) 1 = [cur.foldl (fun a x => e.denote a x) i] := by
      simp [leBytes, zx_setWidth]
    rw [this] at hI'; exact hI'
  | foldW w i =>
    exact fold_exec id (fun a x => w.denote a x) w.tr (fun env a x h5 h6 => WExp.tr_ok a x env h5 h6 w) hI i
      (k := 8) (by omega) hsp hx hL
  | take n =>
    obtain ⟨out, fs, hI⟩ := hI
    obtain ⟨env, heap⟩ := σ
    have hn : n < 2 ^ 64 := by
      simp only [Stage.chk] at hc; by_cases h : n < 2 ^ 64
      · exact h
      · simp [h] at hc
    have hbd := hI.bound; have hcur := hI.cur; dsimp only at hbd hcur
    have hk := minN_val (env := env) hn
    have hset : ∀ a, (minN n).denote (env.set 4 a) = (minN n).denote env := fun a => by
      simp [minN, AExp.denote, AEnv.set]
    have hBl : (if cs.onOut then out else xs).length < 2 ^ 32 := by have := hI.olen; split <;> omega
    generalize hB : (if cs.onOut then out else xs) = B at *
    generalize hs : (env 4).toNat = s at *
    generalize hm : (env 1).toNat = m at *
    cases hr : cs.rev
    · simp only [stageC, hr, Bool.false_eq_true, if_false]
      refine ⟨_, ExecL.one (AExec.assign' rfl), out, fs, hI.heap, hI.olen, hI.fsok, ?_, ?_, ?_⟩
      · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hB, hs, hk]; omega
      · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hB, hs, hk, hr, Stage.denote]
        rw [hcur, hr]; simp only [dirL, Bool.false_eq_true, if_false]
        rw [← List.map_take, List.take_take]
      · intro h; simp only [AEnv.set, Fin.reduceEq, if_false]; exact hI.s0 h
    · simp only [stageC, hr, if_true]
      have e4 : (env 4 + (env 1 - (minN n).denote env)).toNat = s + (m - min n m) := by
        rw [BitVec.toNat_add, BitVec.toNat_sub, hk, hs, hm]; omega
      refine ⟨_, ⟨_, AExec.assign' rfl, ExecL.one (AExec.assign' rfl)⟩, out, fs, hI.heap, hI.olen, hI.fsok, ?_, ?_, ?_⟩
      · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hB, AExp.denote, Op.eval, hset, e4, hk]
        omega
      · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hB, AExp.denote, Op.eval, Stage.denote, hset, e4, hk]
        rw [hcur, hr]; simp only [dirL, if_true]
        rw [← List.map_take, List.take_reverse, win_len hbd, List.drop_take, List.drop_drop,
          show m - n = m - min n m from by omega, show m - (m - min n m) = min n m from by omega]
      · intro h; simp at h
  | drop n =>
    obtain ⟨out, fs, hI⟩ := hI
    obtain ⟨env, heap⟩ := σ
    have hn : n < 2 ^ 64 := by
      simp only [Stage.chk] at hc; by_cases h : n < 2 ^ 64
      · exact h
      · simp [h] at hc
    have hbd := hI.bound; have hcur := hI.cur; dsimp only at hbd hcur
    have hk := minN_val (env := env) hn
    have hset : ∀ a, (minN n).denote (env.set 4 a) = (minN n).denote env := fun a => by
      simp [minN, AExp.denote, AEnv.set]
    have hBl : (if cs.onOut then out else xs).length < 2 ^ 32 := by have := hI.olen; split <;> omega
    generalize hB : (if cs.onOut then out else xs) = B at *
    generalize hs : (env 4).toNat = s at *
    generalize hm : (env 1).toNat = m at *
    have e1 : (env 1 - (minN n).denote env).toNat = m - min n m := by
      rw [BitVec.toNat_sub, hk, hm]; omega
    cases hr : cs.rev
    · simp only [stageC, hr, Bool.false_eq_true, if_false]
      have e4 : (env 4 + (minN n).denote env).toNat = s + min n m := by
        rw [BitVec.toNat_add, hk, hs]; omega
      refine ⟨_, ⟨_, AExec.assign' rfl, ExecL.one (AExec.assign' rfl)⟩, out, fs, hI.heap, hI.olen, hI.fsok, ?_, ?_, ?_⟩
      · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hB, AExp.denote, Op.eval, hset, e4, e1]; omega
      · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hB, AExp.denote, Op.eval, Stage.denote, hset, e4, e1]
        rw [hcur, hr]; simp only [dirL, Bool.false_eq_true, if_false]
        rw [← List.map_drop]; congr 1
        rw [← List.drop_drop, ← List.drop_take]
        rcases Nat.le_total n m with h | h
        · rw [Nat.min_eq_left h]
        · rw [Nat.min_eq_right h, List.drop_of_length_le (by rw [win_len hbd]; exact h),
            List.drop_of_length_le (by rw [win_len hbd]; exact Nat.le_refl _)]
      · intro h; simp at h
    · simp only [stageC, hr, if_true]
      refine ⟨_, ExecL.one (AExec.assign' rfl), out, fs, hI.heap, hI.olen, hI.fsok, ?_, ?_, ?_⟩
      · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hB, hs, AExp.denote, Op.eval, e1]; omega
      · simp only [AEnv.set, Fin.reduceEq, if_false, if_true, hB, hs, AExp.denote, Op.eval, e1, hr, Stage.denote]
        rw [hcur, hr]; simp only [dirL, if_true]
        rw [← List.map_drop, List.drop_reverse, win_len hbd, List.take_take]
        congr 3; omega
      · intro h; simp only [AEnv.set, Fin.reduceEq, if_false]; exact hI.s0 h

/-! ## Whole pipes -/

theorem stmts_exec {L : Nat} {xs : List UInt8} (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) :
    ∀ (p : Pipe) {cs : CS} {cur : List UInt8} {σ : AState}, (∀ st ∈ p, st.chk = none) → InvE L cs xs cur σ →
    Pipe.need p cs cur.length ≤ L → ∃ σ', ExecL (stmts p cs) σ σ' ∧ InvE L csClean xs (Pipe.denote p cur) σ'
  | [], cs, cur, σ, _, hI, hsp => by
    refine mat_exec hx hL hI ?_
    simp only [Pipe.need] at hsp
    by_cases h : cs.clean = true
    · exact .inl h
    · simp only [h, Bool.false_eq_true, if_false] at hsp; exact .inr hsp
  | st :: r, cs, cur, σ, hc, hI, hsp => by
    simp only [Pipe.need] at hsp
    obtain ⟨σ₁, hex₁, hI₁⟩ := stage_exec hx hL st (hc st (List.mem_cons_self ..)) hI (by omega)
    obtain ⟨σ₂, hex₂, hI₂⟩ := stmts_exec hx hL r (fun s hs => hc s (List.mem_cons_of_mem _ hs)) hI₁
      (by rw [Stage.denote_len]; omega)
    exact ⟨σ₂, ExecL.append hex₁ hex₂, hI₂⟩

theorem Pipe.denote_len (p : Pipe) (l : List UInt8) : (Pipe.denote p l).length = Pipe.len p l.length := by
  induction p generalizing l with
  | nil => rfl
  | cons st r ih => simp only [Pipe.denote, Pipe.len, List.foldl_cons] at ih ⊢; rw [ih, Stage.denote_len]

/-- **Source-level correctness of the pipe translation.**  On the heap `[input, out]` with `a1 = |input|`
and an output block of at least `p.space |input|` bytes, `p.prog` terminates (all accesses in bounds), the
input block is unchanged and the output block starts with `p.denote input`. -/
theorem Pipe.prog_exec (p : Pipe) (hc : ∀ st ∈ p, st.chk = none) (xs : List UInt8) (out : List (BitVec 8))
    (env : AEnv) (h1 : env 1 = .ofNat 64 xs.length) (hx : xs.length < 2 ^ 32)
    (hsp : Pipe.space p xs.length ≤ out.length) (hL : out.length < 2 ^ 32) :
    ∃ σ' out', AExec (Pipe.prog p) ⟨env, [tbs xs, out]⟩ σ' ∧ σ'.heap = [tbs xs, out'] ∧
      out'.length = out.length ∧ out'.take (Pipe.denote p xs).length = tbs (Pipe.denote p xs) := by
  have ho : out = tbs (out.map fun b => ⟨b⟩) := by simp [tbs, List.map_map, Function.comp_def]
  generalize out.map (fun b => (⟨b⟩ : UInt8)) = o at ho; subst ho
  have e1 : (env 1).toNat = xs.length := by rw [h1]; exact ofNat_toNat_lt (by omega)
  have hI0 : InvE (tbs o).length cs0 xs xs ⟨env.set 4 0, [tbs xs, tbs o]⟩ :=
    ⟨o, [], rfl, by simp, .nil, by simp [cs0, AEnv.set, e1], by simp [cs0, AEnv.set, e1, dirL, applyAll_nil],
      fun _ => by simp [AEnv.set]⟩
  obtain ⟨⟨env', heap'⟩, hex, out', fs, hI⟩ := stmts_exec hx hL p hc hI0 hsp
  obtain ⟨rfl, h4, hcur, hm⟩ := hI.clean
  have hh := hI.heap; dsimp only at hh hcur; subst hh
  refine ⟨_, tbs out', ExecL.foldl (AExec.assign' rfl) hex, rfl, by simpa using hI.olen, ?_⟩
  have : (Pipe.denote p xs).length = (env' 1).toNat := hI.len
  rw [this, hcur]; simp [tbs]

end Proven
