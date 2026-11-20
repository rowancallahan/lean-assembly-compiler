/- Paged dynamic arrays (NOTES section 30), part 10: results and the whole program.

`outLoopP`: the bytes of an array result (input view or paged work array) to the output block. -/
import Legacy.Riscv.Frontx.WpProg
import Legacy.Riscv.Frontx.WaImpl

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc Proven.Mach.Riscv
open Proven.Frontx (Res rN rN_toNat rN_lt rN_add rN_inj rB wrO wrO_length wrO_append wrO_nil wrO_take wrO_drop)

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

/-- a scalar result: the program, its result's bytes (only while no page request failed), `a1 := -1` when one did -/
def wholeS {t : Ty} (p : Pg [.ar .ba] (.sc t)) (k : Nat) : MS :=
  .seq (.seq poolInit (p.compP [inLocP] 9).1) (.seq (.assign 8 (.var vOk))
    (.seq (when 8 (.seq (.assign 4 (.var (p.compP [inLocP] 9).2.v)) (store8 k)))
      (.assign 1 (.ite (.var vOk) (.var 1) (.const NIL)))))

theorem wholeS_ok (C : Nat) {t : Ty} {β : Type} [Res β] (f : ByteArray → β) (p : Pg [.ar .ba] (.sc t))
    (cv : t.T → β) (hcv : ∀ y, Res.repr (cv y) = t.rep y) (xs : ByteArray) (env : Mach.BEnv)
    (out : List (BitVec 8)) (W : W64) (y : t.T) (E : List MemEvent)
    (h1 : env 1 = BitVec.ofNat 64 xs.data.toList.length) (h32 : xs.size < 2 ^ 32) (hW : W.length < 2 ^ 32)
    (hC : C * P ≤ W.length) (hcap : env vCap = rN (C * P))
    (hwf : p.wfP [inLocP] 9 = true) (hg : p.GoodE [inLocP] 9 (xs, ()) y E) (hy : cv y = f xs)
    (hout : (Res.enc (f xs)).length ≤ out.length) :
    ∃ σ' out', Mach.BExec (wholeS p (Res.k β)) ⟨env, [xs.data.toList.map (·.toBitVec), out], [W]⟩ σ' ∧
      σ'.heap = [xs.data.toList.map (·.toBitVec), out'] ∧
      ((pk 0 E ≤ C ∧ out'.take (Res.enc (f xs)).length = (Res.enc (f xs)).map (·.toBitVec) ∧
          out'.drop (Res.enc (f xs)).length = out.drop (Res.enc (f xs)).length ∧ σ'.env vOk = 1) ∨
        (C < pk 0 E ∧ σ'.env 1 = NIL ∧ out' = out ∧ σ'.env vOk = 0)) := by
  obtain ⟨σ1, W1, e1, h1', w1, o1⟩ := wholeCore C p xs env out W y E h1 h32 hW hC hcap hwf hg
  have hlen : (Res.enc (f xs)).length = Res.k β + 1 := by
    have := congrArg List.length (Res.henc (f xs)); simpa using this
  obtain ⟨env1, H1, Ws1⟩ := σ1
  simp only at h1' w1; subst h1' w1
  let Hh : Heap := [xs.data.toList.map (·.toBitVec), out]
  rcases o1 with ⟨ok1, r1, n1, p1, wl1, pk1⟩ | ⟨ok1, pk1⟩
  · have ok1' : env1 vOk = 1 := ok1
    have g1 : Mach.BExec (.assign 8 (.var vOk)) ⟨env1, Hh, [W1]⟩ ⟨env1.set 8 1, Hh, [W1]⟩ := by
      have := Mach.BExec.assign (v := 8) (e := .var vOk) (σ := ⟨env1, [xs.data.toList.map (·.toBitVec), out], [W1]⟩)
      simp only [Mach.BExp.denote, ok1'] at this; exact this
    let σ2 : Mach.BState := ⟨(env1.set 8 1).set 4 ((Mach.BExp.var (p.compP [inLocP] 9).2.v).denote (env1.set 8 1)), Hh, [W1]⟩
    have h4 : σ2.env 4 = Res.repr (f xs) := by
      simp only [σ2, set_eq, Mach.BExp.denote, set_ne (show (p.compP [inLocP] 9).2.v ≠ 8 from n1)]
      rw [← hy, hcv]; exact r1
    obtain ⟨out', hst, hl', hb', hu⟩ := store8_exec (Res.repr (f xs)) (Res.k β) (Res.hk (β := β)) σ2 _ out rfl h4
      (by omega) rfl
    have e2 := when_true (c := 8) (σ := ⟨env1.set 8 1, Hh, [W1]⟩) (by simp only [set_eq]; decide) (.seq .assign hst)
    refine ⟨_, out', .seq e1 (.seq g1 (.seq e2 .assign)), rfl, .inl ⟨pk1, ?_, ?_, ?_⟩⟩
    · rw [hlen]
      apply List.ext_getElem?; intro i
      rw [Res.henc]
      by_cases hi : i < Res.k β + 1
      · rw [List.getElem?_take_of_lt hi, hb' i (by omega), List.getElem?_map, List.getElem?_range hi]; rfl
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    · rw [hlen]
      exact List.ext_getElem? fun i => by rw [List.getElem?_drop, List.getElem?_drop]; exact hu _ (by omega)
    · simp only [σ2, set_ne (show vOk ≠ 1 by decide), set_ne (show vOk ≠ 4 by decide),
        set_ne (show vOk ≠ 8 by decide), ok1']; done
  · have ok1' : env1 vOk = 0 := ok1
    have g1 : Mach.BExec (.assign 8 (.var vOk)) ⟨env1, Hh, [W1]⟩ ⟨env1.set 8 0, Hh, [W1]⟩ := by
      have := Mach.BExec.assign (v := 8) (e := .var vOk) (σ := ⟨env1, [xs.data.toList.map (·.toBitVec), out], [W1]⟩)
      simp only [Mach.BExp.denote, ok1'] at this; exact this
    have e2 := when_false (c := 8) (S := (Mach.BStmt.seq (.assign 4 (.var (p.compP [inLocP] 9).2.v)) (store8 (Res.k β))))
      (σ := ⟨env1.set 8 0, [xs.data.toList.map (·.toBitVec), out], [W1]⟩) (by simp only [set_eq])
    refine ⟨_, out, .seq e1 (.seq g1 (.seq e2 .assign)), rfl, .inr ⟨pk1, ?_, rfl, ?_⟩⟩
    · simp only [Mach.BExp.denote, set_eq, set_ne (show 1 ≠ 8 by decide), set_ne (show vOk ≠ 8 by decide), ok1']
      simp
    · simp only [set_ne (show vOk ≠ 1 by decide), set_ne (show vOk ≠ 8 by decide), ok1']

/-- an array result: the program, the elements' bytes (only while no page request failed), their number in `a1`,
`a1 := -1` when a request failed -/
def wholeA {k : AK} (p : Pg [.ar .ba] (.ar k)) (ob : Nat) : MS :=
  .seq (.seq poolInit (p.compP [inLocP] 9).1) (.seq (.assign 8 (.var vOk))
    (.seq (when 8 (.seq (outLoopP (p.compP [inLocP] 9).2 k.el.width ob) (.assign 1 (.var (ob + 1)))))
      (.assign 1 (.ite (.var vOk) (.var 1) (.const NIL)))))

set_option maxHeartbeats 4000000 in
theorem wholeA_ok (C : Nat) {k : AK} (p : Pg [.ar .ba] (.ar k)) (ob : Nat) (xs : ByteArray) (env : Mach.BEnv)
    (out : List (BitVec 8)) (W : W64) (y : k.T) (E : List MemEvent)
    (hob : 9 ≤ ob ∧ (p.compP [inLocP] 9).2.v < ob ∧ (p.compP [inLocP] 9).2.pt < ob)
    (h1 : env 1 = BitVec.ofNat 64 xs.data.toList.length) (h32 : xs.size < 2 ^ 32) (hW : W.length < 2 ^ 32)
    (hC : C * P ≤ W.length) (hcap : env vCap = rN (C * P))
    (hwf : p.wfP [inLocP] 9 = true) (hg : p.GoodE [inLocP] 9 (xs, ()) y E)
    (hout : (encArr k y).length ≤ out.length) (hol : out.length < 2 ^ 32) :
    ∃ σ' out', Mach.BExec (wholeA p ob) ⟨env, [xs.data.toList.map (·.toBitVec), out], [W]⟩ σ' ∧
      σ'.heap = [xs.data.toList.map (·.toBitVec), out'] ∧
      ((pk 0 E ≤ C ∧ out'.take (encArr k y).length = (encArr k y).map (·.toBitVec) ∧
          out'.drop (encArr k y).length = out.drop (encArr k y).length ∧ σ'.env 1 = rN (encArr k y).length ∧
          σ'.env vOk = 1) ∨
        (C < pk 0 E ∧ σ'.env 1 = NIL ∧ out' = out ∧ σ'.env vOk = 0)) := by
  obtain ⟨σ1, W1, e1, h1', w1, o1⟩ := wholeCore C p xs env out W y E h1 h32 hW hC hcap hwf hg
  obtain ⟨env1, H1, Ws1⟩ := σ1
  simp only at h1' w1; subst h1' w1
  let Hh : Heap := [xs.data.toList.map (·.toBitVec), out]
  rcases o1 with ⟨ok1, r1, n1, p1, wl1, pk1⟩ | ⟨ok1, pk1⟩
  · have ok1' : env1 vOk = 1 := ok1
    have g1 : Mach.BExec (.assign 8 (.var vOk)) ⟨env1, Hh, [W1]⟩ ⟨env1.set 8 1, Hh, [W1]⟩ := by
      have := Mach.BExec.assign (v := 8) (e := .var vOk) (σ := ⟨env1, [xs.data.toList.map (·.toBitVec), out], [W1]⟩)
      simp only [Mach.BExp.denote, ok1'] at this; exact this
    obtain ⟨hsr, hat⟩ := r1
    obtain ⟨hv, hs32, hinp, hpg⟩ := hsr
    unfold wholeA
    generalize hl : (p.compP [inLocP] 9).2 = l at hv hinp hpg hat hob n1 p1 ⊢
    simp only [Hh, List.getD_cons_zero] at hinp
    have hcap2 : k.el.width * AK.size k y ≤ out.length := by
      have := encPre_length k y (AK.size k y); unfold encArr at hout; omega
    let env2 := ((env1.set 8 1).set ob 0).set (ob + 1) 0
    have hk2 : ∀ j, j ≠ ob → j ≠ ob + 1 → env2 j = env1 j ∨ j = 8 := fun j a b => by
      simp only [env2, set_ne b, set_ne a]
      by_cases h8 : j = 8
      · exact Or.inr h8
      · exact Or.inl (set_ne h8)
    have hk2' : ∀ j, j ≠ ob → j ≠ ob + 1 → j ≠ 8 → env2 j = env1 j := fun j a b c => by
      simp only [env2, set_ne b, set_ne a, set_ne c]
    obtain ⟨env', e3, hq, hk⟩ := outLoopP_iter y l ob (xs.data.toList.map (·.toBitVec)) out W1 (env1 l.pt) hinp
      (fun h => by have := hat h; exact this) wl1 ⟨hob.2.1, hob.2.2⟩ hcap2 hol hs32 _ 0 env2 rfl (Nat.zero_le _)
      (by simp only [env2, set_ne (show ob ≠ ob + 1 by omega), set_eq]; rfl)
      (by simp only [env2, set_eq]; rfl)
      (by rw [hk2' l.v (by omega) (by omega) n1]; exact hv)
      (by rw [hk2' l.pt (by omega) (by omega) p1])
    simp only [List.range_zero, List.flatMap_nil, wrO_nil] at e3
    have e2 : Mach.BExec (outLoopP l k.el.width ob) ⟨env1.set 8 1, Hh, [W1]⟩
        ⟨env', [xs.data.toList.map (·.toBitVec), wrO out 0 (encArr k y)], [W1]⟩ :=
      .seq .assign (.seq .assign e3)
    have e4 := when_true (c := 8) (S := .seq (outLoopP l k.el.width ob) (.assign 1 (.var (ob + 1))))
      (σ := ⟨env1.set 8 1, Hh, [W1]⟩) (by simp only [set_eq]; decide) (.seq e2 .assign)
    refine ⟨_, wrO out 0 (encArr k y), .seq e1 (.seq g1 (.seq e4 .assign)), rfl,
      .inl ⟨pk1, wrO_take _ _ hout, wrO_drop _ _, ?_, ?_⟩⟩
    · simp only [Mach.BExp.denote, set_eq, set_ne (show 1 ≠ 8 by decide), set_ne (show vOk ≠ 8 by decide),
        set_ne (show vOk ≠ 1 by decide), Op.eval]
      rw [hk vOk (by have := hob.1; simp only [vOk]; omega), hk2' vOk (by have := hob.1; simp only [vOk]; omega)
        (by have := hob.1; simp only [vOk]; omega) (by decide), ok1', if_neg (by decide), hq]
    · simp only [set_ne (show vOk ≠ 1 by decide), set_ne (show vOk ≠ 8 by decide)]
      rw [hk vOk (by have := hob.1; simp only [vOk]; omega), hk2' vOk (by have := hob.1; simp only [vOk]; omega)
        (by have := hob.1; simp only [vOk]; omega) (by decide), ok1']
  · have ok1' : env1 vOk = 0 := ok1
    have g1 : Mach.BExec (.assign 8 (.var vOk)) ⟨env1, Hh, [W1]⟩ ⟨env1.set 8 0, Hh, [W1]⟩ := by
      have := Mach.BExec.assign (v := 8) (e := .var vOk) (σ := ⟨env1, [xs.data.toList.map (·.toBitVec), out], [W1]⟩)
      simp only [Mach.BExp.denote, ok1'] at this; exact this
    have e2 := when_false (c := 8) (S := (Mach.BStmt.seq (outLoopP (p.compP [inLocP] 9).2 k.el.width ob) (.assign 1 (.var (ob + 1)))))
      (σ := ⟨env1.set 8 0, [xs.data.toList.map (·.toBitVec), out], [W1]⟩) (by simp only [set_eq])
    refine ⟨_, out, .seq e1 (.seq g1 (.seq e2 .assign)), rfl, .inr ⟨pk1, ?_, rfl, ?_⟩⟩
    · simp only [Mach.BExp.denote, set_eq, set_ne (show 1 ≠ 8 by decide), set_ne (show vOk ≠ 8 by decide), ok1']
      simp
    · simp only [set_ne (show vOk ≠ 1 by decide), set_ne (show vOk ≠ 8 by decide), ok1']

/-- the pool size from the work block: `cap := ((sp - a2) >> 13 - 1) << 10` words (one page of `8 P = 8192` bytes
is left for the frame) -/
def capCode : MS :=
  .assign vCap (.bin .shl (.bin .sub (.bin .lshr (.bin .sub (.var 4) (.var 2)) (.const 13)) (.const 1)) (.const 10))

theorem capCode_ok (env : Mach.BEnv) (H : Heap) (W : List (List (BitVec 64))) (b L : Nat)
    (h2 : env 2 = BitVec.ofNat 64 b) (h4 : env 4 = BitVec.ofNat 64 (b + L)) (hL : 8192 ≤ L)
    (hb : b + L ≤ 2 ^ 32) :
    Mach.BExec capCode ⟨env, H, W⟩ ⟨env.set vCap (rN ((L / 8192 - 1) * P)), H, W⟩ := by
  have hv : (Mach.BExp.bin .shl (.bin .sub (.bin .lshr (.bin .sub (.var 4) (.var 2)) (.const 13)) (.const 1)) (.const 10)).denote env = rN ((L / 8192 - 1) * P) := by
    simp only [Mach.BExp.denote, h2, h4, Op.eval]
    apply BitVec.eq_of_toNat_eq
    have e1 : (BitVec.ofNat 64 (b + L) - BitVec.ofNat 64 b).toNat = L := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have h13 : (13 : BitVec 64).toNat = 13 := rfl
    have h10 : (10 : BitVec 64).toNat = 10 := rfl
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have e2' : ((BitVec.ofNat 64 (b + L) - BitVec.ofNat 64 b) >>> ((13 : BitVec 64).toNat % 64)).toNat = L / 8192 := by
      rw [BitVec.toNat_ushiftRight, e1, h13]; simp [Nat.shiftRight_eq_div_pow]
    have e3 : (((BitVec.ofNat 64 (b + L) - BitVec.ofNat 64 b) >>> ((13 : BitVec 64).toNat % 64)) - 1).toNat = L / 8192 - 1 := by
      rw [BitVec.toNat_sub, e2', h1]; omega
    rw [BitVec.toNat_shiftLeft, e3, h10, Nat.shiftLeft_eq]
    simp only [rN, BitVec.toNat_ofNat, P]
  have := Mach.BExec.assign (v := vCap) (e := .bin .shl (.bin .sub (.bin .lshr (.bin .sub (.var 4) (.var 2)) (.const 13)) (.const 1)) (.const 10)) (σ := ⟨env, H, W⟩)
  rw [hv] at this
  exact this

end Proven.WA
