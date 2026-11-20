/- Nano/V2Self/Proof/Tests/SelfInWitness: step C towards `Nonempty SelfIn`: on the EMPTY input the meaning of C's source
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

end Cert.CapFree
