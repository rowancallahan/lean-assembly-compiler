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

/-! the path -/
/-- one step of a fuel loop at the fuel literal C uses (stated so that `simp` never unrolls a loop by itself) -/
theorem loopRun_big (fz fs : List W → Out) (env : List W) :
    loopRun fz fs 16777216 env = (do
      let env1 ← setSlots env 0 [.w (UInt64.ofNat 16777215)]
      match ← fs env1 with
      | .inl v => pure v
      | .inr st => loopRun fz fs 16777215 (← setSlots env1 1 st)) := rfl

theorem X13 : F [] 13 PC.d13 [.w 16777216, .w 0, .b []] = .ok [.b []] := by
  have s4 : C.s4 [] 0 = 91 := by decide
  simp only [F, defMean, PC.d13, ev]
  simp [loopRun_big, PC.z13, PC.s13, ev, evL, NanoMain.val, prim, setSlots, cal 8 13 PC.d8 rfl, X8, s4, bind, Except.bind, pure, Except.pure]

theorem X14 : F [] 14 PC.d14 [] = .ok [.b []] := by
  simp only [F, defMean, PC.d14]
  simp [PC.b14, ev, evL, NanoMain.val, prim, cal 13 14 PC.d13 rfl, X13, bind, Except.bind, pure, Except.pure]

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

/-- the parser's initial heap: 184,384 zero words (kept folded: `simp` must not expand it) -/
def H0 : List UInt64 := List.replicate 184384 0

theorem X15 : F [] 15 PC.d15 [.w 184384, .b []] = .ok [.b H0] := by
  have h : loopRun (fun e => ev ⟨[], κC, Pre [] 15⟩ PC.z15 e) (fun e => ev ⟨[], κC, Pre [] 15⟩ PC.s15 e) 184384 [.w 184384, .b []]
      = .ok [.b H0] :=
    push_loop (fun w l => by simp [PC.z15, ev]) (fun w l hl => by
      simp [PC.s15, ev, evL, NanoMain.val, prim, push, hl, bind, Except.bind, pure, Except.pure]) 184384 [] 184384 (by decide)
  simp only [F, defMean, PC.d15, ev]
  simp [h, NanoMain.val, H0, bind, Except.bind, pure, Except.pure, -List.reduceReplicate]

theorem X31 : F [] 31 PC.d31 [.b []] = .ok [.b H0] := by
  simp only [F, defMean, PC.d31]
  simp [PC.b31, ev, evL, NanoMain.val, cal 15 31 PC.d15 rfl, X15, bind, Except.bind, pure, Except.pure]

theorem X38 (h : List UInt64) : F [] 38 PC.d38 [.w 16777216, .b [], .w 0, .b h] = .ok [.b h] := by
  simp only [F, defMean, PC.d38, ev]
  simp [loopRun_big, PC.z38, PC.s38, ev, evL, NanoMain.val, prim, setSlots, bind, Except.bind, pure, Except.pure]

theorem X160 : F [] 160 PC.d160 [.b []] = .ok [.b []] := by
  simp only [F, defMean, PC.d160]
  simp [PC.b160, ev, evL, NanoMain.val, prim, setSlots, bind, Except.bind, pure, Except.pure]

theorem X231 (u : UInt64) : F [] 231 PC.d231 [.b [], .w u] = .ok [.b []] := by
  simp only [F, defMean, PC.d231]
  simp [PC.b231, ev, evL, NanoMain.val, prim, setSlots, bind, Except.bind, pure, Except.pure]

theorem X232 : F [] 232 PC.d232 [.b []] = .ok [.b []] := by
  simp only [F, defMean, PC.d232]
  simp [PC.b232, ev, evL, NanoMain.val, cal 181 232 PC.d181 rfl, cal 231 232 PC.d231 rfl, X181, X231, bind, Except.bind, pure, Except.pure]

end Cert.CapFree
