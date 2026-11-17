/- A stage compiled by the paged front end (`wp_compile`, result `Array UInt8`) as a linker stage (branch
`nano-closeB`): `pg_stage` turns `PgProg.Good` plus the Lean function's runs (`GoodE`) and a bound `B` on the page
peak of every run into `Implements1With … (fun _ => 8192 * (B + 1)) maxIn true` (via `body_ok`, `Nano.Link.of_pg`). -/
import Nano.LinkPg
import Riscv.Frontx.WpCmd

set_option linter.unusedVariables false

namespace Nano.Link
open Proven Proven.Mach.Riscv Proven.WA

theorem encArr_u8 (a : Array UInt8) : encArr (.arr .u8) a = a.toList := by
  have hw : ∀ j, leN (AK.el (.arr .u8)).width (AK.w (.arr .u8) a j).toNat = [a[j]!] := by
    intro j
    simp only [AK.el, Ty.width, leN, AK.w, Ty.rep, AK.get, Proven.Frontx.r8]
    simp
  have hf : ∀ l : List Nat, l.flatMap (fun j => [a[j]!]) = l.map (fun j => a[j]!) := by
    intro l; induction l <;> simp_all
  unfold encArr
  simp only [hw, AK.size, hf]
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    exact getElem!_pos a j (by simpa using h2)

/-- changing the function on the inputs the theorem speaks about -/
theorem pg_congr {α β β' : Type} {encA : α → List UInt8} {encB : β → List UInt8} {encB' : β' → List UInt8}
    {code : List (BitVec 32)} {f : α → β} {f' : α → β'} {Lmin : Nat} {fits : α → Nat → Prop} {maxLen : Nat}
    {rl : Bool} (h : Implements1Pg encA encB code f Lmin fits maxLen rl)
    (he : ∀ a, (encA a).length ≤ maxLen → encB (f a) = encB' (f' a)) :
    Implements1Pg encA encB' code f' Lmin fits maxLen rl := by
  intro a s entry ra input output work
  dsimp only
  intro hx
  have := h a s entry ra input output work hx
  rw [he a hx] at this
  exact this

/-- **a paged stage with an `Array UInt8` result is a linker stage** -/
theorem pg_stage (p : Pg [.ar .ba] (.ar (.arr .u8))) (m : Nat) (c : Option (List (Nat × Nat) × List Nat))
    (hg : (⟨.ar (.arr .u8), p, m, c⟩ : PgProg).Good) (f : ByteArray → Array UInt8)
    (hf : ∀ xs : ByteArray, xs.size ≤ m → ∃ E, p.GoodE [inLocP] 9 (xs, ()) (f xs) E) (B : Nat)
    (hB : ∀ xs : ByteArray, xs.size ≤ m → ∀ y E, p.GoodE [inLocP] 9 (xs, ()) y E → pk 0 E ≤ B) :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (PgProg.body ⟨.ar (.arr .u8), p, m, c⟩)
      (fun xs => (f xs).toList) (fun _ => 8192 * (B + 1)) m true := by
  have ht := PgProg.good_total hg
  have h1 := (body_ok hg).toPg
  have h2 : Implements1Pg (fun xs : ByteArray => xs.data.toList) (fun l => l) (PgProg.body ⟨.ar (.arr .u8), p, m, c⟩)
      (fun xs => (f xs).toList) 8192 (PgProg.fitsM ⟨.ar (.arr .u8), p, m, c⟩) m true := by
    refine pg_congr h1 fun xs hx => ?_
    have hs : xs.size ≤ m := by simpa using hx
    have hr := PgProg.res_spec ht xs hs
    obtain ⟨E, hE⟩ := hf xs hs
    have := Pg.den_det _ _ _ _ (Pg.goodE_den _ _ _ _ _ _ hr) (Pg.goodE_den _ _ _ _ _ _ hE)
    show encArr (.arr .u8) _ = _
    rw [encArr_u8]
    exact congrArg Array.toList this
  refine of_pg h2 _ fun xs L hx hL => ⟨by omega, ?_⟩
  have hs : xs.size ≤ m := by simpa using hx
  rw [PgProg.fitsM_iff]
  have := hB xs hs _ _ (PgProg.res_spec ht xs hs)
  have : B + 1 ≤ L / 8192 := by
    apply (Nat.le_div_iff_mul_le (by decide)).2; simp only at hL; omega
  exact Nat.le_trans (Nat.succ_le_succ ‹_›) this

end Nano.Link
