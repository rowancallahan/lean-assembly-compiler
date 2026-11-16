/- Paged arrays (NOTES section 30), part 12: example programs with their `Implements1Pg` theorems. -/
import Riscv.Frontx.WpImpl

set_option linter.unusedVariables false

namespace Proven.WA.PgEx
open Proven Proven.WP Proven.Top.Alloc Proven.Mach.Riscv

/-- bytes plus one, pushed one at a time -/
def copyGo (xs : ByteArray) (i : Nat) (out : ByteArray) : ByteArray :=
  if i < xs.size then copyGo xs (i + 1) (out.push (xs[i]! + 1)) else out
termination_by xs.size - i

def copyE (xs : ByteArray) : ByteArray := copyGo xs 0 ByteArray.empty

/-- the loop body over state `(out, i)`, then `xs` -/
def copyBody : T ([.ar .ba, .sc .nat] ++ [.ar .ba]) [.ar .ba, .sc .nat] (.ar .ba) :=
  .ite (.cmp .lt (.var (.tl .hd)) (.size (.tl (.tl .hd))))
    (.call (.cons (.push (.var .hd) (.bin .add (.getB (.tl (.tl .hd)) (.var (.tl .hd)) true) (.lit .u8 1)))
      (.cons (.bin .add (.var (.tl .hd)) (.lit .nat 1)) .nil)))
    (.ret (.var .hd))

def copyPg : Pg [.ar .ba] (.ar .ba) :=
  .loop [.ar .ba, .sc .nat] copyBody (.cons .empty (.cons (.lit .nat 0) .nil)) (.ret (.var .hd))



theorem copyPg_wf : copyPg.wfP [inLocP] 9 = true := by decide +kernel

/-- all events are allocations: the peak is the final count -/
theorem pk_allocs : ∀ (E : List MemEvent) (u : Nat), (∀ e ∈ E, ∃ n, e = .alloc n) → pk u E = finE u E ∧ u ≤ finE u E
  | [], u, _ => ⟨rfl, Nat.le_refl _⟩
  | e :: es, u, h => by
    obtain ⟨n, rfl⟩ := h e (by simp)
    obtain ⟨h1, h2⟩ := pk_allocs es (stepE u (.alloc n)) (fun e he => h e (by simp [he]))
    simp only [pk, finE, stepE] at h1 h2 ⊢
    exact ⟨by rw [h1]; omega, by omega⟩

theorem pushFrom_allocs : ∀ (j m : Nat), ∀ e ∈ pushFrom j m, ∃ n, e = .alloc n
  | j, 0, e, he => by simp [pushFrom] at he
  | j, m + 1, e, he => by
    simp only [pushFrom, List.mem_append] at he
    rcases he with he | he
    · unfold pushEv at he; split at he
      · simp at he; exact ⟨1, he⟩
      · simp at he
    · exact pushFrom_allocs (j + 1) m e he

theorem copyBody_out (xs : ByteArray) (out : ByteArray) (i : Nat) :
    copyBody.out (Vals.app (out, (i, ())) (xs, ())) =
      if i < xs.size then .inl (out.push (xs[i]! + 1), (i + 1, ())) else .inr out := by
  simp [copyBody, T.out, E.den, A.den, Args.den, Vals.app, Mem.get, AK.size, AK.get, AK.push, Op2.den, Cmp.den, Arg.den, AK.el,
    Ty.T]

/-- the loop runs from `(out, i)` with `out.size = i` and its events are the pushes -/
theorem copy_runs (xs : ByteArray) : ∀ (m i : Nat) (out : ByteArray), xs.size - i = m → out.size = i → i ≤ xs.size →
    RunsE copyBody (xs, ()) (out, (i, ())) (copyGo xs i out) (pushFrom i m)
  | 0, i, out, hm, hs, hi => by
    have hn : ¬ i < xs.size := by omega
    rw [copyGo, if_neg hn]
    exact .ret (by rw [copyBody_out, if_neg hn])
  | m + 1, i, out, hm, hs, hi => by
    have hl : i < xs.size := by omega
    have ho := copyBody_out xs out i
    rw [if_pos hl] at ho
    have ih := copy_runs xs m (i + 1) (out.push (xs[i]! + 1)) (by omega) (by simp [hs]) (by omega)
    have := RunsE.call (b := copyBody) (c := (xs, ())) (s := (out, (i, ()))) ho ih
    rw [copyGo, if_pos hl]
    have hev : copyBody.evs (Vals.app (out, (i, ())) (xs, ())) = pushEv i := by
      simp [pushEv, copyBody, T.evs, Args.evs, A.evs, A.den, E.den, Cmp.den, Vals.app, Mem.get, AK.size, hs, hl]
    rw [hev] at this
    exact this

/-- the page events of `copyE`: the page table, then a page at every `P`-th push -/
def copyEv (xs : ByteArray) : List MemEvent := [.alloc 1] ++ (pushFrom 0 xs.size ++ [])

theorem copyPg_good (xs : ByteArray) (h : xs.size ≤ P * P) :
    copyPg.GoodE [inLocP] 9 (xs, ()) (copyE xs) (copyEv xs) ∧ pk 0 (copyEv xs) = 1 + npages xs.size := by
  have hP : P * P = 2 ^ 20 := by decide
  unfold copyEv
  refine ⟨?_, ?_⟩
  · simp only [copyPg, Pg.GoodE, Inis.okP, Ini.okP, F.okP, E.ok, and_true, true_and]
    refine ⟨copyGo xs 0 ByteArray.empty, fun s => s.1.size = s.2.1 ∧ s.2.1 ≤ xs.size, pushFrom 0 xs.size, [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Inis.den, Ini.den, F.den, E.den]
    · intro s hPs
      obtain ⟨out, i, u⟩ := s
      change ByteArray at out
      change Nat at i
      obtain ⟨hs, hi⟩ := hPs
      simp only at hs hi
      simp only [Vals.app, copyBody, T.okP]
      simp [E.ok, Args.okP, A.okP, E.den, A.den, Cmp.den, Op2.exact, Op2.side, Ty.small, Mem.get, AK.size]
      have hi2 : i ≤ xs.size := hi
      have hs2 : out.size = i := hs
      omega
    · intro s s' hPs hout
      obtain ⟨out, i, u⟩ := s
      obtain ⟨out', i', u'⟩ := s'
      change ByteArray at out out'
      change Nat at i i'
      obtain ⟨hs, hi⟩ := hPs
      simp only at hs hi
      rw [copyBody_out] at hout
      split at hout
      · simp at hout
        obtain ⟨h1, h2⟩ := hout
        subst h1 h2
        rename_i hl
        have hl2 : i < xs.size := hl
        refine ⟨by show (ByteArray.push out _).size = i + 1; simp [hs], by show i + 1 ≤ xs.size; omega⟩
      · simp at hout
    · simpa [Inis.den, Ini.den, F.den, E.den] using copy_runs xs xs.size 0 ByteArray.empty (by omega) (by simp) (by omega)
    · simp [Pg.GoodE, A.den, Mem.get, copyE]
    · simp [Inis.evsP, Ini.evsP, F.evsP]
  · have hn := (pk_allocs ([.alloc 1] ++ (pushFrom 0 xs.size ++ [])) 0 (by
      intro e he
      simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · exact ⟨1, rfl⟩
      · exact pushFrom_allocs 0 _ e he)).1
    rw [hn]
    simp only [List.singleton_append, List.append_nil, finE, stepE, finE_pushFrom]
    simp [npages, P]

theorem copy_N : pgNA copyPg ≤ NS := by decide +kernel
theorem copy_ob : (copyPg.compP [inLocP] 9).2.v < outBaseP copyPg ∧ (copyPg.compP [inLocP] 9).2.pt < outBaseP copyPg := by
  decide +kernel
theorem copy_wfB : rvF.wfB (pgNA copyPg) [0, 3] [2] (pgProgA copyPg) := by decide +kernel

/-- the pages `copyE` needs: a page table, its data pages (and one page for the frame) -/
def copyFits (xs : ByteArray) (L : Nat) : Prop := 2 + npages xs.size ≤ L / 8192

/-- **`copyE` (a `ByteArray` grown by pushes) ⇒ `Implements1Pg`** -/
theorem copy_implements : Implements1Pg (fun xs : ByteArray => xs.data.toList) (encArr .ba) (pgCodeA copyPg) copyE
    8192 copyFits (retLen := true) :=
  implements1_pgA (k := .ba) copyE copyPg copy_N copy_ob copyPg_wf copy_wfB copyFits (2 ^ 20) fun xs hx => by
    obtain ⟨hg, hpk⟩ := copyPg_good xs (by unfold P; omega)
    exact ⟨copyEv xs, hg, fun L _ => by unfold copyFits; omega⟩

end Proven.WA.PgEx
