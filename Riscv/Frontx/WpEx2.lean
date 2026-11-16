/- Paged arrays (NOTES section 30), part 13: an LZ77 copy that reads the array it writes (the shape of lean-zip's
`copyLoopGo`: `out := out.push out[out.size - distance]`), after a prefix taken with `ByteArray.extract`. -/
import Riscv.Frontx.WpEx

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven.WA.PgEx
open Proven Proven.WP Proven.Top.Alloc Proven.Mach.Riscv

/-- the distance, from the first byte -/
def lzD (xs : ByteArray) : Nat := (xs[0]!.toNat &&& 7) + 1

/-- copy `xs.size` bytes from `lzD xs` back -/
def lzGo (xs : ByteArray) (i : Nat) (out : ByteArray) : ByteArray :=
  if i < xs.size then lzGo xs (i + 1) (out.push out[out.size - lzD xs]!) else out
termination_by xs.size - i

def lzE (xs : ByteArray) : ByteArray := lzGo xs 0 (xs.extract 0 16)

def lzDist : E ([.ar .ba, .sc .nat] ++ [.ar .ba]) .nat :=
  .bin .add (.bin .and (.cast .nat (.getB (.tl (.tl .hd)) (.lit .nat 0) true)) (.lit .nat 7)) (.lit .nat 1)

def lzBody : T ([.ar .ba, .sc .nat] ++ [.ar .ba]) [.ar .ba, .sc .nat] (.ar .ba) :=
  .ite (.cmp .lt (.var (.tl .hd)) (.size (.tl (.tl .hd))))
    (.call (.cons (.push (.var .hd) (.getB .hd (.bin .sub (.size .hd) lzDist) true))
      (.cons (.bin .add (.var (.tl .hd)) (.lit .nat 1)) .nil)))
    (.ret (.var .hd))

def lzPg : Pg [.ar .ba] (.ar .ba) :=
  .loop [.ar .ba, .sc .nat] lzBody (.cons (.extract (.hd) (.lit .nat 0) (.lit .nat 16)) (.cons (.lit .nat 0) .nil))
    (.ret (.var .hd))

theorem lzPg_wf : lzPg.wfP [inLocP] 9 = true := by decide +kernel
theorem lz_N : pgNA lzPg ≤ NS := by decide +kernel
theorem lz_ob : (lzPg.compP [inLocP] 9).2.v < outBaseP lzPg ∧ (lzPg.compP [inLocP] 9).2.pt < outBaseP lzPg := by
  decide +kernel
theorem lz_wfB : rvF.wfB (pgNA lzPg) [0, 3] [2] (pgProgA lzPg) := by decide +kernel

theorem lzBody_out (xs : ByteArray) (out : ByteArray) (i : Nat) :
    lzBody.out (Vals.app (out, (i, ())) (xs, ())) =
      if i < xs.size then .inl (out.push out[out.size - lzD xs]!, (i + 1, ())) else .inr out := by
  simp [lzBody, lzDist, T.out, E.den, A.den, Args.den, Vals.app, Mem.get, AK.size, AK.get, AK.push, Op2.den, Cmp.den,
    Arg.den, AK.el, lzD, WA.cast]

theorem lz_runs (xs : ByteArray) (m0 : Nat) : ∀ (m i : Nat) (out : ByteArray), xs.size - i = m → out.size = m0 + i →
    i ≤ xs.size → RunsE lzBody (xs, ()) (out, (i, ())) (lzGo xs i out) (pushFrom (m0 + i) m)
  | 0, i, out, hm, hs, hi => by
    have hn : ¬ i < xs.size := by omega
    rw [lzGo, if_neg hn]
    exact .ret (by rw [lzBody_out, if_neg hn])
  | m + 1, i, out, hm, hs, hi => by
    have hl : i < xs.size := by omega
    have ho := lzBody_out xs out i
    rw [if_pos hl] at ho
    have ih := lz_runs xs m0 m (i + 1) (out.push out[out.size - lzD xs]!) (by omega) (by simp [hs]; omega) (by omega)
    have := RunsE.call (b := lzBody) (c := (xs, ())) (s := (out, (i, ()))) ho ih
    rw [lzGo, if_pos hl]
    have hev : lzBody.evs (Vals.app (out, (i, ())) (xs, ())) = pushEv (m0 + i) := by
      simp [pushEv, lzBody, T.evs, Args.evs, A.evs, A.den, E.den, Cmp.den, Vals.app, Mem.get, AK.size, hs, hl]
    rw [hev] at this
    exact this

/-- the page events of `lzE`: the prefix (table and pages), then the pushes after it -/
def lzEv (xs : ByteArray) : List MemEvent :=
  (.alloc 1 :: pushEvs (min 16 xs.size)) ++ (pushFrom (min 16 xs.size) xs.size ++ [])

theorem lzPg_good (xs : ByteArray) (h : xs.size ≤ P * P - 16) :
    lzPg.GoodE [inLocP] 9 (xs, ()) (lzE xs) (lzEv xs) ∧ pk 0 (lzEv xs) = 1 + npages (min 16 xs.size + xs.size) := by
  have hP : P * P = 2 ^ 20 := by decide
  rw [hP] at h
  have hm0 : (xs.extract 0 16).size = min 16 xs.size := by simp [ByteArray.size_extract]
  unfold lzEv
  refine ⟨?_, ?_⟩
  · simp only [lzPg, Pg.GoodE, Inis.okP, Ini.okP, F.okP, E.ok, and_true, true_and]
    refine ⟨⟨by simp [E.den], by simp [E.den], by simp [E.den, Mem.get]; rw [hP]; exact Nat.le_trans (Nat.min_le_left _ _) (by decide)⟩, lzGo xs 0 (xs.extract 0 16), fun s => s.1.size = min 16 xs.size + s.2.1 ∧
      s.2.1 ≤ xs.size, pushFrom (min 16 xs.size) xs.size, [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Inis.den, Ini.den, F.den, E.den, Mem.get, ByteArray.size_extract]
    · intro s hPs
      obtain ⟨out, i, u⟩ := s
      change ByteArray at out
      change Nat at i
      obtain ⟨hs, hi⟩ := hPs
      simp only at hs hi
      simp only [Vals.app, lzBody, T.okP]
      simp [E.ok, Args.okP, A.okP, E.den, A.den, Cmp.den, Op2.exact, Op2.side, Ty.small, Mem.get, AK.size, lzDist,
        Op2.den, WA.cast, AK.get, AK.el]
      have hd : xs[0]!.toNat &&& 7 ≤ 7 := Nat.and_le_right
      have hi2 : i ≤ xs.size := hi
      have hs2 : out.size = min 16 xs.size + i := hs
      simp only [hP]
      refine ⟨⟨by omega, by omega⟩, fun hl => ⟨⟨⟨by omega, ?_⟩, ?_⟩, by omega⟩⟩
      · omega
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
    · intro s s' hPs hout
      obtain ⟨out, i, u⟩ := s
      obtain ⟨out', i', u'⟩ := s'
      change ByteArray at out out'
      change Nat at i i'
      obtain ⟨hs, hi⟩ := hPs
      simp only at hs hi
      rw [lzBody_out] at hout
      split at hout
      · simp at hout
        obtain ⟨h1, h2⟩ := hout
        subst h1 h2
        rename_i hl
        have hl2 : i < xs.size := hl
        have hs2 : out.size = min 16 xs.size + i := hs
        refine ⟨by show (ByteArray.push out _).size = min 16 xs.size + (i + 1); simp [hs2]; omega,
          by show i + 1 ≤ xs.size; omega⟩
      · simp at hout
    · simpa [Inis.den, Ini.den, F.den, E.den, Mem.get] using lz_runs xs (min 16 xs.size) xs.size 0 (xs.extract 0 16)
        (by omega) (by simp [ByteArray.size_extract]) (by omega)
    · simp [Pg.GoodE, A.den, Mem.get, lzE]
    · simp [Inis.evsP, Ini.evsP, F.evsP, E.den, Mem.get]
  · have hn := (pk_allocs ((.alloc 1 :: pushEvs (min 16 xs.size)) ++ (pushFrom (min 16 xs.size) xs.size ++ [])) 0 (by
      intro e he
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, pushEvs] at he
      rcases he with (rfl | he) | he
      · exact ⟨1, rfl⟩
      · exact pushFrom_allocs 0 _ e he
      · exact pushFrom_allocs _ _ e he)).1
    rw [hn]
    simp only [List.cons_append, List.append_nil, finE_append, finE, stepE, pushEvs, finE_pushFrom]
    have := Nat.min_le_left 16 xs.size
    unfold npages P
    omega

def lzFits (xs : ByteArray) (L : Nat) : Prop := 2 + npages (min 16 xs.size + xs.size) ≤ L / 8192

/-- **the LZ77 copy (an array read while it grows) ⇒ `Implements1Pg`** -/
theorem lz_implements : Implements1Pg (fun xs : ByteArray => xs.data.toList) (encArr .ba) (pgCodeA lzPg) lzE
    8192 lzFits (2 ^ 20 - 16) (retLen := true) :=
  implements1_pgA (k := .ba) lzE lzPg lz_N lz_ob lzPg_wf lz_wfB lzFits (2 ^ 20 - 16) fun xs hx => by
    obtain ⟨hg, hpk⟩ := lzPg_good xs (by unfold P; omega)
    exact ⟨lzEv xs, hg, fun L _ => by unfold lzFits; omega⟩

end Proven.WA.PgEx
