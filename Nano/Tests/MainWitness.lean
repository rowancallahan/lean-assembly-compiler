/- Nano/Tests/MainWitness: NON-VACUITY of `NanoMain.compiler_correct`, per stage, kernel-checked (`decide +kernel`).
For three small sources: the lexer run `C.s10 x = ts`, ParSpec's acceptance `refParse ts = some p` with `serialize p = a`,
O's acceptance `C.o41 a = a` with `LinearK p` (explicit slot kinds `Ks`), and Gen's acceptance `C.g41 x a ≠ []`.  So
`OwnStage`'s and `GenStage`'s premises hold with non-empty code, and `mC x ≠ []` follows from the
single parser run `C.y16 ts = a` (checked natively, NOT in the kernel: Par1's fixed layout puts the tokens at word 184,384,
and one kernel `bget` at that index alone costs 28 s / 5.5 GB; see Testing/notes/NANO_V2_MAIN.md). -/
import Nano.Main.Sem
import Nano.Lexer.DsSound
namespace NanoMain.Witness
open ParSpec

/-- what each witness shows -/
def Acc (x : List UInt8) (ts a : List UInt64) : Prop :=
  DsSpec.LexesD x ts ∧
  (∃ p, ParsesProgram ts p ∧ serialize p = a ∧ LinearK p ∧ C.o41 (serialize p) = serialize p ∧ C.g41 x (serialize p) ≠ []) ∧
  (C.y16 ts = a → mC x ≠ [])

theorem stages (x : List UInt8) (ts a : List UInt64) (Ks : List (List Nat)) (hx : x.length < 2 ^ 32) (hl : C.s10 x = ts)
    (hd : C.t10 ts = ts) (hlen : ts.length < 2 ^ 24)
    (hp : (refParse ts).map (fun p => (serialize p, OwnSpec.progOk [] [] Ks p)) = some (a, true))
    (hK : (Ks.all fun K => K.all (· ≤ 2)) = true) (hu : (C.u10 a == a) = true) (ho : (C.o41 a == a) = true)
    (hg : (C.g41 x a).isEmpty = false) : Acc x ts a := by
  have hne : C.g41 x a ≠ [] := by intro e; simp [e] at hg
  have hoa : C.o41 a = a := by simpa using ho
  have hua : C.u10 a = a := by simpa using hu
  obtain ⟨p, hp1, hp2⟩ := Option.map_eq_some_iff.1 hp
  simp only [Prod.mk.injEq] at hp2
  obtain ⟨hp2, hpo⟩ := hp2
  have hts : ts ≠ [] := by rintro rfl; simp [refParse_nil] at hp1
  have hlin : LinearK p := ⟨Ks, hpo, fun K hK' k hk => by
    simp only [List.all_eq_true, decide_eq_true_eq] at hK; exact hK K hK' k hk⟩
  refine ⟨?_, ⟨p, hp1, hp2, hlin, hp2 ▸ hoa, hp2 ▸ hne⟩, fun hy => ?_⟩
  · exact ⟨ts, LexSpec.s10_sound x hx ts hl hts, by
      have := DsSpec.t10_sound ts (by omega) (by rw [hd]; exact hts); rwa [hd] at this⟩
  · simp only [mC, hl, hd, hy, hua, hoa]; exact hne

set_option maxRecDepth 100000

/-- `def m (x : List UInt8) : List UInt8 := []` -/
def x1 : List UInt8 := "def m (x : List UInt8) : List UInt8 := []".toUTF8.toList
def t1 : List UInt64 := [1, 14, 1, 109, 0, 6, 14, 1, 120, 0, 8, 37, 38, 7, 8, 37, 38, 9, 30, 31]
def a1 : List UInt64 := [2, 20, 0, 0, 0, 0, 1, 9, 5, 21]
theorem w1 : Acc x1 t1 a1 := stages x1 t1 a1 [[]] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel)

/-- ParSpec's ex1: two defs, BIN/CONST, prims RD/PUT/BNEW, a call -/
def x2 : List UInt8 := ex1.toUTF8.toList
def a2 : List UInt64 := [2, 20, 0, 2, 2, 0, 1, 3, 1, 2, 0, 1, 3, 3, 2, 1, 1, 1, 3, 21, 20, 1, 0, 0, 0, 1, 9, 4, 9, 5, 8, 0, 2, 9, 2, 1, 0, 1, 2, 21]
theorem w2 : Acc x2 (C.s10 x2) a2 := stages x2 (C.s10 x2) a2 [[0, 0], []] (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- ParSpec's ex3: a fuel loop with CONTINUE, `len'`, `len` -/
def x3 : List UInt8 := ex3.toUTF8.toList
def a3 : List UInt64 := [2, 20, 0, 2, 2, 1, 1, 10, 2, 1, 1, 4, 2, 2, 1, 1, 9, 3, 11, 3, 1, 2, 1, 1, 1, 1, 2, 1, 1, 21, 20, 1, 0, 0, 0, 1, 9, 4, 9, 5, 8, 0, 2, 9, 1, 1, 0, 21]
theorem w3 : Acc x3 (C.s10 x3) a3 := stages x3 (C.s10 x3) a3 [[0, 0], []] (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- the meaning is not trivial either: ex1 on input [5] is `put [] (5 + 2 * 3)`, ex3 on 4 bytes is `put [] 4` -/
theorem sem2 : (refParse (C.s10 x2)).map (fun p => (Sem κC p [5]).toOption) = some (some [11]) := by decide +kernel
theorem sem3 : (refParse (C.s10 x3)).map (fun p => (Sem κC p [1, 2, 3, 4]).toOption) = some (some [4]) := by decide +kernel

end NanoMain.Witness
