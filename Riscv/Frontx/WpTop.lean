/- Paged dynamic arrays (NOTES section 30), part 10: results and the whole program.

`outLoopP`: the bytes of an array result (input view or paged work array) to the output block. -/
import Riscv.Frontx.WpProg
import Riscv.Frontx.WaImpl

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj rB wrO wrO_length wrO_append wrO_nil)

/-- a load of element `i` of the array `a` at `l` (input view or pages), index in `d` -/
theorem ldLoc_ok {k : AK} (a : k.T) (l : PLoc) (X O : List (BitVec 8)) (W : W64) (env : Mach.BEnv) (d i : Nat)
    (hinp : l.inp = true → InpAt X k a) (hpt : l.inp = false → ArrAt W (env l.pt).toNat (words k a))
    (hW : W.length < 2 ^ 32) (hs32 : AK.size k a < 2 ^ 32) (hlt : l.pt < d) (hd : env d = rN i) (hi : i < AK.size k a) :
    ∃ env', Mach.BExec (ldP l d) ⟨env, [X, O], [W]⟩ ⟨env', [X, O], [W]⟩ ∧ env' d = AK.w k a i ∧
      (∀ j, j ≠ d → j ≠ d + 1 → env' j = env j) := by
  unfold ldP
  split
  · rename_i hin
    obtain ⟨hl, hj⟩ := hinp hin
    have h := hj i hi
    have hiB : i < X.length := by
      rcases Nat.lt_or_ge i X.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at h; simp at h
    rw [List.getElem?_eq_getElem hiB] at h
    have e := Option.some.inj h
    have hdi : ((Mach.BExp.var d).denote env).toNat = i := by
      simp only [Mach.BExp.denote, hd]; exact rN_toNat (by omega)
    have := Mach.BExec.load (v := d) (b := 0) (i := .var d) (σ := ⟨env, [X, O], [W]⟩) (by simp)
      (by simp only [List.getElem_cons_zero, hdi]; exact hiB)
    simp only [List.getElem_cons_zero, hdi, e] at this
    exact ⟨_, this, set_eq, fun j h1 _ => set_ne h1⟩
  · rename_i hin
    have hin' : l.inp = false := by simpa using hin
    have hA := hpt hin'
    have hpt' : env l.pt = rN (env l.pt).toNat := by simp [rN]
    have hsz : i < (words k a).length := by rw [words_length]; exact hi
    obtain ⟨x, hx, e⟩ := getEl_ok hA [X, O] env l.pt d ⟨by omega, by omega⟩ hpt' i hd hsz hW
    rw [words_get k _ hi] at hx
    refine ⟨_, e, by simp only [set_eq]; exact (Option.some.inj hx).symm, fun j h1 h2 => ?_⟩
    simp only [set_ne h1, set_ne h2]

/-- `j := 0; q := 0; while j < size { x := a[j]; out[q ..] := bytes of x; j := j + 1; q := q + width }` -/
def outLoopP (l : PLoc) (w d : Nat) : MS :=
  .seq (.assign d (.const 0)) (.seq (.assign (d + 1) (.const 0)) (.loop (.bin .ult (.var d) (.var l.v))
    (.seq (.assign (d + 2) (.var d)) (.seq (ldP l (d + 2))
      (.seq (storeV (d + 2) (d + 1) 0 0 (w - 1))
        (.seq (.assign d (.bin .add (.var d) (.const 1))) (.assign (d + 1) (.bin .add (.var (d + 1)) (.const (BitVec.ofNat 64 w))))))))))

set_option maxHeartbeats 4000000 in
theorem outLoopP_iter {k : AK} (a : k.T) (l : PLoc) (d : Nat) (X O0 : List (BitVec 8)) (W : W64) (p0 : BitVec 64)
    (hinp : l.inp = true → InpAt X k a) (hpt : l.inp = false → ArrAt W p0.toNat (words k a))
    (hW : W.length < 2 ^ 32) (hd : l.v < d ∧ l.pt < d)
    (hcap : k.el.width * AK.size k a ≤ O0.length) (hO : O0.length < 2 ^ 32) (h32 : AK.size k a < 2 ^ 32) :
    ∀ (m j : Nat) (env : Mach.BEnv), AK.size k a - j = m → j ≤ AK.size k a → env d = rN j →
      env (d + 1) = rN (k.el.width * j) → env l.v = rN (AK.size k a) → env l.pt = p0 →
      ∃ env', Mach.BExec (.loop (.bin .ult (.var d) (.var l.v))
        (.seq (.assign (d + 2) (.var d)) (.seq (ldP l (d + 2))
          (.seq (storeV (d + 2) (d + 1) 0 0 (k.el.width - 1))
            (.seq (.assign d (.bin .add (.var d) (.const 1)))
              (.assign (d + 1) (.bin .add (.var (d + 1)) (.const (BitVec.ofNat 64 k.el.width)))))))))
        ⟨env, [X, wrO O0 0 ((List.range j).flatMap fun i => leN k.el.width (AK.w k a i).toNat)], [W]⟩
        ⟨env', [X, wrO O0 0 (encArr k a)], [W]⟩ ∧ env' (d + 1) = rN (encArr k a).length ∧
        ∀ i, i < d → env' i = env i
  | 0, j, env, hm, hj, h0, h1, hs, hp => by
    have hjn : j = AK.size k a := by omega
    subst hjn
    refine ⟨env, .loopF ?_, ?_, fun _ _ => rfl⟩
    · simp only [Mach.BExp.denote, Op.eval, h0, hs]; simp
    · rw [h1]; unfold encArr; rw [encPre_length]
  | m + 1, j, env, hm, hj, h0, h1, hs, hp => by
    have hjn : j < AK.size k a := by omega
    have hw := Ty.width_pos k.el
    let O1 := wrO O0 0 ((List.range j).flatMap fun i => leN k.el.width (AK.w k a i).toNat)
    have hpre := encPre_length k a j
    have hO1 : O1.length = O0.length := wrO_length _ _ _ (by rw [hpre]; have := Nat.mul_le_mul_left k.el.width (show j ≤ AK.size k a by omega); omega)
    have hlt : (Mach.BExp.bin .ult (.var d) (.var l.v)).denote env ≠ 0 := by
      simp only [Mach.BExp.denote, Op.eval, h0, hs]
      rw [if_pos (by simp only [rN_lt (by omega : j < 2 ^ 64) (by omega : AK.size k a < 2 ^ 64)]; exact hjn)]; decide
    let env0 := env.set (d + 2) ((Mach.BExp.var d).denote env)
    have h0' : env0 (d + 2) = rN j := by simp only [env0, set_eq, Mach.BExp.denote]; exact h0
    have hp0 : env0 l.pt = p0 := by simp only [env0, set_ne (show l.pt ≠ d + 2 by omega)]; exact hp
    obtain ⟨env1, hl1, hv1, hk1⟩ := ldLoc_ok a l X O1 W env0 (d + 2) j hinp
      (fun h => by rw [hp0]; exact hpt h) hW h32 (by omega) h0' hjn
    have hst := storeV_exec (d + 2) (d + 1) (AK.w k a j) X [W] (k.el.width - 1) 0 0 O1 env1 (k.el.width * j) hv1
      (by rw [hk1 _ (by omega) (by omega)]; simp only [env0, set_ne (show d + 1 ≠ d + 2 by omega)]; exact h1)
      (by rw [hO1]; have := Nat.mul_le_mul_left k.el.width (show j + 1 ≤ AK.size k a by omega); simp [Nat.mul_succ] at this; omega)
      (by rw [hO1]; exact hO) (by omega)
    rw [show k.el.width - 1 + 1 = k.el.width by omega, Nat.pow_zero, Nat.div_one] at hst
    simp only [Nat.add_zero] at hst
    have hO2 : wrO O1 (k.el.width * j) (leN k.el.width (AK.w k a j).toNat) =
        wrO O0 0 ((List.range (j + 1)).flatMap fun i => leN k.el.width (AK.w k a i).toNat) := by
      rw [encPre_succ, wrO_append _ _ _ _ (by rw [hpre]; have := Nat.mul_le_mul_left k.el.width (show j ≤ AK.size k a by omega); omega), hpre, Nat.zero_add]
    rw [hO2] at hst
    have hk1' : ∀ q, q < d + 2 → env1 q = env q := fun q hq => by
      rw [hk1 q (by omega) (by omega)]; simp only [env0, set_ne (show q ≠ d + 2 by omega)]
    let env2 := env1.set d ((Mach.BExp.bin .add (.var d) (.const 1)).denote env1)
    let env3 := env2.set (d + 1) ((Mach.BExp.bin .add (.var (d + 1)) (.const (BitVec.ofNat 64 k.el.width))).denote env2)
    obtain ⟨env', e', h1', k'⟩ := outLoopP_iter a l d X O0 W p0 hinp hpt hW hd hcap hO h32 m (j + 1) env3 (by omega) (by omega)
      (by simp only [env3, env2, set_ne (show d ≠ d + 1 by omega), set_eq, Mach.BExp.denote, Op.eval,
          hk1' d (by omega), h0, rN_add]; rfl)
      (by simp only [env3, env2, set_eq, Mach.BExp.denote, Op.eval, set_ne (show d + 1 ≠ d by omega),
          hk1' (d + 1) (by omega), h1]
          rw [show k.el.width * (j + 1) = k.el.width * j + k.el.width from Nat.mul_succ _ _, rN_add]; rfl)
      (by simp only [env3, env2, set_ne (show l.v ≠ d + 1 by omega), set_ne (show l.v ≠ d by omega),
          hk1' l.v (by omega)]; exact hs)
      (by simp only [env3, env2, set_ne (show l.pt ≠ d + 1 by omega), set_ne (show l.pt ≠ d by omega),
          hk1' l.pt (by omega)]; exact hp)
    refine ⟨env', .loopT hlt (.seq .assign (.seq hl1 (.seq hst (.seq .assign .assign)))) e', h1', fun i hi => ?_⟩
    rw [k' i hi]
    simp only [env3, env2, set_ne (show i ≠ d + 1 by omega), set_ne (show i ≠ d by omega), hk1' i (by omega)]

/-! ## The whole program -/

def inLocP : PLoc := ⟨1, true, 0⟩

/-- an empty pool: nothing bumped, no free page, no failed request (`vCap` is set before) -/
def poolInit : MS :=
  .seq (.assign vBump (.const 0)) (.seq (.assign vFh (.const NIL)) (.assign vOk (.const 1)))

theorem envOK_input (xs : ByteArray) (env : Mach.BEnv) (out : List (BitVec 8)) (W : W64)
    (h1 : env 1 = BitVec.ofNat 64 xs.data.toList.length) (h32 : xs.size < 2 ^ 32) (hW : W.length < 2 ^ 32) :
    EnvOK [.ar .ba] [inLocP] (xs, ()) ⟨env, [xs.data.toList.map (·.toBitVec), out], [W]⟩ := by
  refine ⟨⟨⟨?_, h32, fun _ => ?_, fun h => nomatch h⟩, trivial⟩, by simp, W, rfl, hW, ?_⟩
  · show env 1 = _; rw [h1]; simp [AK.size, rN]
  · show InpAt _ .ba xs
    refine ⟨?_, fun j hj => ?_⟩
    · simp [AK.size]
    · simp only [List.getD_cons_zero, List.getElem?_map, Array.getElem?_toList, Option.map_map]
      rw [show xs.data[j]? = some xs.data[j] from Array.getElem?_eq_getElem hj]
      simp only [Option.map_some, AK.w, AK.el, AK.get, Ty.rep]
      rw [getElem!_pos xs j hj]; rfl
  · intro a ha; simp [arrsP, inLocP] at ha

theorem pool_empty (C : Nat) (env : Mach.BEnv) (W : W64) (hC : C * P ≤ W.length) (hW : W.length < 2 ^ 32)
    (hcap : env vCap = rN (C * P)) (h5 : env vBump = 0) (h6 : env vFh = NIL) :
    Store C env W [] := by
  refine ⟨⟨0, [], hcap, by rw [h5]; rfl, ?_, rfl, Nat.zero_le _, hC, hW, ?_⟩, fun a ha => nomatch ha⟩
  · rw [h6]; rfl
  · simp [owned, below]

theorem poolInit_ok (env : Mach.BEnv) (H : Heap) (W : W64) :
    Mach.BExec poolInit ⟨env, H, [W]⟩
      ⟨((env.set vBump 0).set vFh NIL).set vOk 1, H, [W]⟩ := .seq .assign (.seq .assign .assign)

/-- the pool, then the program: either it ends with its result and its page events within `C` pages, or `vOk = 0`
exactly when the events exceed `C` pages -/
theorem wholeCore (C : Nat) {R : Sl} (p : Pg [.ar .ba] R) (xs : ByteArray) (env : Mach.BEnv)
    (out : List (BitVec 8)) (W : W64) (y : R.T) (E : List MemEvent)
    (h1 : env 1 = BitVec.ofNat 64 xs.data.toList.length) (h32 : xs.size < 2 ^ 32) (hW : W.length < 2 ^ 32)
    (hC : C * P ≤ W.length) (hcap : env vCap = rN (C * P))
    (hwf : p.wfP [inLocP] 9 = true) (hg : p.GoodE [inLocP] 9 (xs, ()) y E) :
    ∃ σ' W', Mach.BExec (.seq poolInit (p.compP [inLocP] 9).1) ⟨env, [xs.data.toList.map (·.toBitVec), out], [W]⟩ σ' ∧
      σ'.heap = [xs.data.toList.map (·.toBitVec), out] ∧ σ'.wheap = [W'] ∧
      ((σ'.env vOk = 1 ∧ ResP σ' W' R (p.compP [inLocP] 9).2 y ∧ (p.compP [inLocP] 9).2.v ≠ 8 ∧
          (p.compP [inLocP] 9).2.pt ≠ 8 ∧ W'.length < 2 ^ 32 ∧ pk 0 E ≤ C) ∨
        (σ'.env vOk = 0 ∧ C < pk 0 E)) := by
  let H := [xs.data.toList.map (·.toBitVec), out]
  let env1 := ((env.set vBump 0).set vFh NIL).set vOk 1
  have e1 := poolInit_ok env H W
  have hk : ∀ j, j ≠ vBump → j ≠ vFh → j ≠ vOk → env1 j = env j := fun j a b c => by
    simp only [env1, set_ne c, set_ne b, set_ne a]
  have hcap1 : env1 vCap = rN (C * P) := by
    rw [hk _ (by decide) (by decide) (by decide)]; exact hcap
  have hS : Store C env1 W ([] ++ arrsP [.ar .ba] [inLocP] (xs, ()) env1) := by
    simpa [arrsP, inLocP] using pool_empty C env1 W hC hW hcap1 (by simp only [env1, set_ne (show vBump ≠ vOk by decide),
      set_ne (show vBump ≠ vFh by decide), set_eq]) (by simp only [env1, set_ne (show vFh ≠ vOk by decide), set_eq])
  have hE : EnvOK [.ar .ba] [inLocP] (xs, ()) ⟨env1, H, [W]⟩ := by
    have := envOK_input xs env1 out W (by rw [hk 1 (by decide) (by decide) (by decide)]; exact h1) h32 hW
    exact this
  obtain ⟨σ', W', e2, h2, w2, o2⟩ := Pg.compP_ok C p [inLocP] (xs, ()) env1 H W 9 [] y E hE
    (fun l hl => by simp [inLocP] at hl; subst hl; simp)
    (by omega) (fun l hl => by simp [inLocP] at hl; subst hl; decide)
    (by simpa using hS) (by simp only [env1, set_eq]) hwf hg
  refine ⟨σ', W', .seq e1 e2, h2, w2, ?_⟩
  simpa [arrsP, inLocP, pageCount] using o2

end Proven.WA
