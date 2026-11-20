/- Nano/V2Self/Proof/Tests/SelfInPath: step C towards `Nonempty SelfIn`: on the EMPTY input the meaning of C's source
does not report `cap`.  The 169 push-free defs are exact by `SelfInQuiet.quiet` + the certificate; the 13 defs on the
empty-input path that contain or reach a push are evaluated by hand below (`X<i>`). -/
import Nano.V2Self.Proof.Tests.SelfInQuiet
import Nano.V2Self.Proof.Cert.All

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Cert.CapFree
open NanoMain ParSpec

theorem allOk_take (inp : List UInt8) (κ : Nat) (specs : List (Fn → Prop)) : ∀ (p : List DefA) (k n : Nat),
    AllOk inp κ specs k p → AllOk inp κ specs k (p.take n)
  | [], k, n, _ => by simp [AllOk]
  | d :: p, k, 0, _ => by simp [AllOk]
  | d :: p, k, n + 1, h => ⟨h.1, allOk_take inp κ specs p (k + 1) n h.2⟩

/-- the certificate for the prefix of length `j` -/
theorem good (j : Nat) (hj : j ≤ PC.all.length) : Good (specs []) (Pre [] j) j := by
  have h := means_all [] κC (specs []) (PC.all.take j) [] 0 ⟨rfl, by simp⟩ (allOk_take _ _ _ _ _ _ (all_ok [] (by decide)))
  simpa [Pre, Nat.min_eq_left hj] using h

theorem exact {α : Type} {r : Except Stop α} {v : α} (h : Ref r v) (hn : r ≠ .error .cap) : r = .ok v := h.resolve_left hn

/-- a callee's meaning, as `ev` sees it in def `j` (`cal i j d rfl` with `d` the named def) -/
theorem cal (i j : Nat) (d : DefA) (hd : PC.all[i]? = some d) (hij : i < j := by decide) (hj : j ≤ PC.all.length := by decide) :
    (Pre [] j)[i]? = some (F [] i d) := by
  have h := pre_get [] hij hj
  rw [List.getElem?_eq_getElem (by omega)] at hd
  cases hd; exact h

/-! the push-free callees used on the path, exact -/
theorem X8 (p : UInt64) : F [] 8 PC.d8 [.w p] = .ok [.w (C.s4 [] p)] :=
  exact (ok_8 [] _ (by decide) (good 8 (by decide)) p) (quiet [] 8 (by decide) (by decide) _)
theorem X181 : F [] 181 PC.d181 [] = .ok [.w C.g_999] :=
  exact (ok_181 [] _ (by decide) (good 181 (by decide))) (quiet [] 181 (by decide) (by decide) _)

/-! the path.  Each def is first evaluated over ABSTRACT callees (`g<i>`: a list `ms` and functions `G…` with their
lookup and value as hypotheses), then instantiated (`X<i>`).  With the concrete callee in the goal the kernel, checking
`simp`'s definitional steps, may unfold it and run a 184,384-step loop. -/

/-- one step of a fuel loop at the fuel literal C uses (stated so that `simp` never unrolls a loop by itself) -/
theorem loopRun_big (fz fs : List W → Out) (env : List W) :
    loopRun fz fs 16777216 env = (do
      let env1 ← setSlots env 0 [.w (UInt64.ofNat 16777215)]
      match ← fs env1 with
      | .inl v => pure v
      | .inr st => loopRun fz fs 16777215 (← setSlots env1 1 st)) := rfl
theorem loopRun_big2 (fz fs : List W → Out) (env : List W) :
    loopRun fz fs 16777215 env = (do
      let env1 ← setSlots env 0 [.w (UInt64.ofNat 16777214)]
      match ← fs env1 with
      | .inl v => pure v
      | .inr st => loopRun fz fs 16777214 (← setSlots env1 1 st)) := rfl

theorem g13 (ms : List Fn) (G8 : Fn) (h8 : ms[8]? = some G8) (e8 : G8 [.w 0] = .ok [.w 91]) :
    defMean [] κC ms PC.d13 [.w 16777216, .w 0, .b []] = .ok [.b []] := by
  simp only [defMean, PC.d13, ev]
  simp [loopRun_big, PC.z13, PC.s13, ev, evL, NanoMain.val, prim, setSlots, h8, e8, bind, Except.bind, pure, Except.pure]
theorem X13 : F [] 13 PC.d13 [.w 16777216, .w 0, .b []] = .ok [.b []] :=
  g13 _ _ (cal 8 13 PC.d8 rfl) (by rw [X8]; exact congrArg (fun x => Except.ok [W.w x]) (by decide))

theorem g14 (ms : List Fn) (G13 : Fn) (h13 : ms[13]? = some G13) (e13 : G13 [.w 16777216, .w 0, .b []] = .ok [.b []]) :
    defMean [] κC ms PC.d14 [] = .ok [.b []] := by
  simp only [defMean, PC.d14]
  simp [PC.b14, ev, evL, NanoMain.val, prim, h13, e13, bind, Except.bind, pure, Except.pure]
theorem X14 : F [] 14 PC.d14 [] = .ok [.b []] := g14 _ _ (cal 13 14 PC.d13 rfl) X13

/-- a loop that pushes one 0 per step: `n` pushes, below the capacity -/
theorem push_loop {fz fs : List W → Out} (hz : ∀ w l, fz [.w w, .b l] = .ok (.inl [.b l]))
    (hs : ∀ w l, l.length < κC → fs [.w w, .b l] = .ok (.inr [.b (l ++ [0])])) :
    ∀ (n : Nat) (l : List UInt64) (w0 : UInt64), l.length + n < κC →
      loopRun fz fs n [.w w0, .b l] = .ok [.b (l ++ List.replicate n 0)]
  | 0, l, w0, _ => by simp [loopRun, hz, NanoMain.val]
  | n + 1, l, w0, h => by
    have ih := push_loop hz hs n (l ++ [0]) (UInt64.ofNat n) (by simp; omega)
    simp only [List.append_assoc, List.singleton_append, ← List.replicate_succ] at ih
    simp [loopRun, setSlots, hs _ l (by omega), ih, bind, Except.bind]

/-- the parser's initial heap: 184,384 zero words (never unfolded below) -/
def H0 : List UInt64 := List.replicate 184384 0
theorem H0_eq : H0 = [] ++ List.replicate 184384 0 := (List.nil_append _).symm
theorem H0_len : H0.length = 184384 := List.length_replicate
theorem H0_get (i : Nat) : H0[i]?.getD 0 = 0 := by
  unfold H0; rw [List.getElem?_replicate]; split <;> rfl
attribute [irreducible] H0

/-- a loop def's meaning from its loop run (no `simp` over the fuel literal) -/
theorem defMean_loop_ok {ms : List Fn} {d : DefA} {z s : Nd} {w0 : UInt64} {rest v : List W} (hb : d.body = .loop z s)
    (hlen : (W.w w0 :: rest).length = d.npw) (hk : d.npw ≤ d.nslots) (hv : v.length = d.nres)
    (hr : loopRun (fun e => ev ⟨[], κC, ms⟩ z e) (fun e => ev ⟨[], κC, ms⟩ s e) w0.toNat
      (W.w w0 :: (rest ++ List.replicate (d.nslots - d.npw) (.w 0))) = .ok v) :
    defMean [] κC ms d (W.w w0 :: rest) = .ok v := by
  unfold defMean
  rw [if_pos ⟨hlen, hk⟩, hb]
  simp only [List.cons_append, ev, hr, NanoMain.val, bind, Except.bind, pure, Except.pure, hv, if_true]

theorem X15 : F [] 15 PC.d15 [.w 184384, .b []] = .ok [.b H0] := by
  have h := push_loop (fz := fun e => ev ⟨[], κC, Pre [] 15⟩ PC.z15 e) (fs := fun e => ev ⟨[], κC, Pre [] 15⟩ PC.s15 e)
    (fun w l => by simp [PC.z15, ev]) (fun w l hl => by
      simp [PC.s15, ev, evL, NanoMain.val, prim, push, hl, bind, Except.bind, pure, Except.pure]) 184384 [] 184384 (by decide)
  rw [← H0_eq] at h
  exact defMean_loop_ok (z := PC.z15) (s := PC.s15) rfl rfl (by decide) rfl h

theorem g31 (ms : List Fn) (G15 : Fn) (r : List UInt64) (h15 : ms[15]? = some G15)
    (e15 : G15 [.w 184384, .b []] = .ok [.b r]) : defMean [] κC ms PC.d31 [.b []] = .ok [.b r] := by
  simp only [defMean, PC.d31]
  simp [PC.b31, ev, evL, NanoMain.val, h15, e15, bind, Except.bind, pure, Except.pure]
theorem X31 : F [] 31 PC.d31 [.b []] = .ok [.b H0] := g31 _ _ _ (cal 15 31 PC.d15 rfl) X15

theorem X38 (h : List UInt64) : F [] 38 PC.d38 [.w 16777216, .b [], .w 0, .b h] = .ok [.b h] := by
  simp only [F, defMean, PC.d38, ev]
  simp [loopRun_big, PC.z38, PC.s38, ev, evL, NanoMain.val, prim, setSlots, bind, Except.bind, pure, Except.pure]

theorem X160 : F [] 160 PC.d160 [.b []] = .ok [.b []] := by
  simp only [F, defMean, PC.d160]
  simp [PC.b160, ev, evL, NanoMain.val, prim, setSlots, bind, Except.bind, pure, Except.pure]

theorem X231 (u : UInt64) : F [] 231 PC.d231 [.b [], .w u] = .ok [.b []] := by
  simp only [F, defMean, PC.d231]
  simp [PC.b231, ev, evL, NanoMain.val, prim, bind, Except.bind, pure, Except.pure]

theorem g232 (ms : List Fn) (G181 G231 : Fn) (u : UInt64) (h181 : ms[181]? = some G181) (h231 : ms[231]? = some G231)
    (e181 : G181 [] = .ok [.w u]) (e231 : G231 [.b [], .w u] = .ok [.b []]) :
    defMean [] κC ms PC.d232 [.b []] = .ok [.b []] := by
  simp only [defMean, PC.d232]
  simp [PC.b232, ev, evL, NanoMain.val, h181, h231, e181, e231, bind, Except.bind, pure, Except.pure]
theorem X232 : F [] 232 PC.d232 [.b []] = .ok [.b []] :=
  g232 _ _ _ _ (cal 181 232 PC.d181 rfl) (cal 231 232 PC.d231 rfl) X181 (X231 _)

/-! ### the parser on no tokens -/
theorem X16 : F [] 16 PC.d16 [] = .ok [.w C.d1] :=
  exact (ok_16 [] _ (by decide) (good 16 (by decide))) (quiet [] 16 (by decide) (by decide) _)
theorem X26 : F [] 26 PC.d26 [] = .ok [.w C.d11] :=
  exact (ok_26 [] _ (by decide) (good 26 (by decide))) (quiet [] 26 (by decide) (by decide) _)
theorem X56 (h : List UInt64) (c a b : UInt64) : F [] 56 PC.d56 [.b h, .w c, .w a, .w b] = .ok [.b (C.v1 h c a b)] :=
  exact (ok_56 [] _ (by decide) (good 56 (by decide)) h c a b) (quiet [] 56 (by decide) (by decide) _)
theorem X95 (h : List UInt64) (a b : UInt64) : F [] 95 PC.d95 [.b h, .w a, .w b] = .ok [.b (C.v127 h a b)] :=
  exact (ok_95 [] _ (by decide) (good 95 (by decide)) h a b) (quiet [] 95 (by decide) (by decide) _)

/-- a plain def's meaning from its body's value -/
theorem defMean_plain_ok {ms : List Fn} {d : DefA} {e : Nd} {ps v : List W} (hb : d.body = e) (hlen : ps.length = d.npw)
    (hk : d.npw ≤ d.nslots) (hv : v.length = d.nres)
    (hr : ev ⟨[], κC, ms⟩ e (ps ++ List.replicate (d.nslots - d.npw) (.w 0)) = .ok (.inl v)) : defMean [] κC ms d ps = .ok v := by
  unfold defMean
  rw [if_pos ⟨hlen, hk⟩, hb]
  simp only [hr, NanoMain.val, bind, Except.bind, pure, Except.pure, hv, if_true]

/-- an `==` test that fails / succeeds: step into the branch without looking at the other one -/
theorem ev_ite_ne {cx : Ctx} {a b t e : Nd} {env : List W} {x y : UInt64} (ha : ev cx a env = .ok (.inl [.w x]))
    (hb : ev cx b env = .ok (.inl [.w y])) (hxy : x ≠ y) : ev cx (.ite 1 a b t e) env = ev cx e env := by
  simp [ev, ha, hb, hxy, NanoMain.val, bind, Except.bind]
theorem ev_ite_eq {cx : Ctx} {a b t e : Nd} {env : List W} {x y : UInt64} (ha : ev cx a env = .ok (.inl [.w x]))
    (hb : ev cx b env = .ok (.inl [.w y])) (hxy : x = y) : ev cx (.ite 1 a b t e) env = ev cx t env := by
  simp [ev, ha, hb, hxy, NanoMain.val, bind, Except.bind]
theorem ev_const (cx : Ctx) (c : UInt64) (env : List W) : ev cx (.const c) env = .ok (.inl [.w c]) := by simp [ev]

/-- the dispatcher at task 60 calls `v127` (id 95) -/
theorem g117 (ms : List Fn) (G95 : Fn) (V : List UInt64 → UInt64 → UInt64 → List UInt64) (h95 : ms[95]? = some G95)
    (e95 : ∀ h a b, G95 [.b h, .w a, .w b] = .ok [.b (V h a b)]) (h : List UInt64) (a b : UInt64) :
    defMean [] κC ms PC.d117 [.b h, .w 60, .w a, .w b] = .ok [.b (V h a b)] := by
  have hc : ev ⟨[], κC, ms⟩ (.loc 1 1) [.b h, .w 60, .w a, .w b] = .ok (.inl [.w 60]) := by simp [ev]
  refine defMean_plain_ok (e := PC.b117) rfl rfl (by decide) rfl ?_
  show ev _ PC.b117 [.b h, .w 60, .w a, .w b] = _
  unfold PC.b117
  repeat rw [ev_ite_ne hc (ev_const _ _ _) (by decide)]
  rw [ev_ite_eq hc (ev_const _ _ _) rfl]
  simp [ev, evL, NanoMain.val, h95, e95, bind, Except.bind, pure, Except.pure]

/-- the task loop: one task (60) is pending; after it the status is not 1, so the loop returns -/
theorem g118 (ms : List Fn) (G16 G117 : Fn) (V : List UInt64 → UInt64 → UInt64 → List UInt64) (h16 : ms[16]? = some G16)
    (h117 : ms[117]? = some G117) (e16 : G16 [] = .ok [.w 64])
    (e117 : ∀ h a b, G117 [.b h, .w 60, .w a, .w b] = .ok [.b (V h a b)]) (h : List UInt64)
    (h0 : h[0]?.getD 0 = 1) (h5 : h[5]?.getD 0 = 1) (h64 : h[64]?.getD 0 = 60) (h65 : h[65]?.getD 0 = 0)
    (h66 : h[66]?.getD 0 = 0) (hR : (V (h.set 5 0) 0 0)[0]?.getD 0 ≠ 1) :
    defMean [] κC ms PC.d118 [.w 16777216, .b h] = .ok [.b (V (h.set 5 0) 0 0)] := by
  refine defMean_loop_ok (z := PC.z118) (s := PC.s118) rfl rfl (by decide) rfl ?_
  show loopRun _ _ 16777216 _ = _
  rw [loopRun_big]
  simp [loopRun_big2, PC.z118, PC.s118, PC.d118, ev, evL, NanoMain.val, prim, binop, setSlots, h16, h117, e16, e117, h0, h5, h64,
    h65, h66, hR, bind, Except.bind, pure, Except.pure]

/-- `v99` on no tokens: whatever task 60 answers, no def was parsed (cell 12 is 0), so the result is empty -/
theorem g120 (ms : List Fn) (G26 G31 G38 G56 G118 : Fn) (V1 : List UInt64 → UInt64 → UInt64 → UInt64 → List UInt64)
    (Z R : List UInt64) (hZ : Z.length = 184384)
    (h26 : ms[26]? = some G26) (h31 : ms[31]? = some G31) (h38 : ms[38]? = some G38) (h56 : ms[56]? = some G56)
    (h118 : ms[118]? = some G118) (e26 : G26 [] = .ok [.w 184384]) (e31 : G31 [.b []] = .ok [.b Z])
    (e38 : G38 [.w 16777216, .b [], .w 0, .b Z] = .ok [.b Z])
    (e56 : ∀ h c a b, G56 [.b h, .w c, .w a, .w b] = .ok [.b (V1 h c a b)])
    (e118 : G118 [.w 16777216, .b (V1 ((Z.set 7 0).set 0 1 ++ [0, 2]) 60 0 0)] = .ok [.b R])
    (hR12 : R[12]?.getD 0 = 0) : defMean [] κC ms PC.d120 [.b [], .w 1] = .ok [.b []] := by
  refine defMean_plain_ok (e := PC.b120) rfl rfl (by decide) rfl ?_
  simp [PC.b120, PC.d120, ev, evL, NanoMain.val, prim, binop, push, setSlots, κC, h26, h31, h38, h56, h118, e26, e31, e38, e56,
    e118, hR12, hZ, bind, Except.bind, pure, Except.pure]

/-! Lean facts about the heap the task loop starts from -/
theorem bget_eq (h : List UInt64) (i : UInt64) : bget h i = h[i.toNat]?.getD 0 := by simp [bget]

/-- the heap after `v99`'s set-up, before the first task is pushed -/
def HA : List UInt64 := (H0.set 7 0).set 0 1 ++ [0, 2]
theorem HA_len : HA.length = 184386 := by simp [HA, H0_len]
theorem HA_0 : HA[0]?.getD 0 = 1 := by
  simp [HA, List.getElem?_append, H0_len, List.getElem?_set]
theorem HA_z (i : Nat) (h1 : 0 < i) (h2 : i < 184384) : HA[i]?.getD 0 = 0 := by
  have := H0_get i
  simp only [HA, List.getElem?_append, List.length_set, H0_len, h2, if_true, List.getElem?_set]
  split
  · omega
  · split
    · split <;> rfl
    · exact this

/-- the heap with task 60 pushed -/
theorem H5_eq : C.v1 HA 60 0 0 = (((HA.set 64 60).set 65 0).set 66 0).set 5 1 := by
  have a5 : bget HA 5 = 0 := by rw [bget_eq]; exact HA_z 5 (by decide) (by decide)
  have dj : C.d1 + 3 * (0 : UInt64) = 64 := by decide
  have g5 : (((HA.set 64 60).set 65 0).set 66 0)[5]?.getD 0 = 0 := by
    simp only [List.getElem?_set, List.length_set, HA_len]
    simpa using HA_z 5 (by decide) (by decide)
  unfold C.v1
  rw [a5, if_pos (by decide)]
  simp only [dj]
  have e1 : (64 : UInt64) + 1 = 65 := by decide
  have e2 : (64 : UInt64) + 2 = 66 := by decide
  simp only [e1, e2, bget_eq, bset]
  show ((((HA.set 64 60).set 65 0).set 66 0).set 5 ((((HA.set 64 60).set 65 0).set 66 0)[5]?.getD 0 + 1)) = _
  rw [g5]; rfl

/-- the heap task 60 runs on (the loop has popped the task) -/
def HT : List UInt64 := ((((HA.set 64 60).set 65 0).set 66 0).set 5 1).set 5 0
theorem HT_len : HT.length = 184386 := by simp [HT, HA_len]
theorem H5_0 : (C.v1 HA 60 0 0)[0]?.getD 0 = 1 := by
  rw [H5_eq]; simp only [List.getElem?_set, List.length_set, HA_len]; simpa using HA_0
theorem H5_5 : (C.v1 HA 60 0 0)[5]?.getD 0 = 1 := by
  rw [H5_eq]; simp [List.getElem?_set, HA_len]
theorem H5_64 : (C.v1 HA 60 0 0)[64]?.getD 0 = 60 := by
  rw [H5_eq]; simp [List.getElem?_set, HA_len]
theorem H5_65 : (C.v1 HA 60 0 0)[65]?.getD 0 = 0 := by
  rw [H5_eq]; simp [List.getElem?_set, HA_len]
theorem H5_66 : (C.v1 HA 60 0 0)[66]?.getD 0 = 0 := by
  rw [H5_eq]; simp [List.getElem?_set, HA_len]
theorem HT_z (i : Nat) (h1 : 0 < i) (h2 : i < 64) : HT[i]?.getD 0 = 0 := by
  have := HA_z i h1 (by omega)
  simp only [HT, List.getElem?_set, List.length_set, HA_len]
  repeat' split
  all_goals first | rfl | omega | exact this

/-- task 60 leaves status 0 or 2 when the cursor is at the end (cells 3 and 7 agree) -/
theorem v127_cases (h : List UInt64) (a b : UInt64) (e : bget h 3 = bget h 7) :
    C.v127 h a b = bset h 0 0 ∨ C.v127 h a b = bset h 0 2 := by
  unfold C.v127
  split
  · exact Or.inl rfl
  · rw [if_pos (by rw [e]; exact beq_self_eq_true _)]; exact Or.inr rfl

theorem R_facts : (C.v127 ((C.v1 HA 60 0 0).set 5 0) 0 0)[0]?.getD 0 ≠ 1 ∧ (C.v127 ((C.v1 HA 60 0 0).set 5 0) 0 0)[12]?.getD 0 = 0 := by
  have eT : (C.v1 HA 60 0 0).set 5 0 = HT := by rw [H5_eq]; rfl
  rw [eT]
  have e37 : bget HT 3 = bget HT 7 := by
    rw [bget_eq, bget_eq]; exact (HT_z 3 (by decide) (by decide)).trans (HT_z 7 (by decide) (by decide)).symm
  have h12 := HT_z 12 (by decide) (by decide)
  have hl := HT_len
  rcases v127_cases HT 0 0 e37 with h | h <;> rw [h] <;> simp [bset, hl] <;> simpa [hl] using h12

end Cert.CapFree
