/- Nano/Parser/ParInvInit: the loaded heap `v1 (entryHeap ts) 60 0 0` represents ParRun's initial configuration (parser lead).
`tokAt_of_tokL`: a heap whose token region holds `ts` reads `TokL ts toks` as `TokAt h 0 toks`. -/
import Nano.Parser.ParInvTop
import Nano.Lexer.ParTokWF
import Nano.Parser.ParInvState
namespace ParInv
open C BufL ParSpec ParRun

theorem tn24 {p : Nat} (hp : p < 2 ^ 64) : p.toUInt64.toNat = p := by simp; omega

theorem tu_add (p k : Nat) (hp : p + k < 2 ^ 64) : p.toUInt64 + k.toUInt64 = (p + k).toUInt64 := by
  apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, tn24 (by omega), tn24 (by omega), tn24 hp]; omega

theorem flat2_len : ∀ nm : List UInt64, (nm.flatMap (fun c => [1, c])).length = 2 * nm.length
  | [] => rfl
  | c :: t => by rw [List.flatMap_cons, List.length_append, flat2_len t]; simp; omega

section
variable {h ts : Buf} (hc : ∀ i, i < ts.length → bget h (d11 + i.toUInt64) = ts.getD i 0) (hts : ts.length < 2 ^ 24)
include hc hts

omit hts in
theorem cellAt {p : Nat} {l : List UInt64} (hd : ts.drop p = l) {i : Nat} (hi : i < l.length) :
    bget h (d11 + (p + i).toUInt64) = l.getD i 0 := by
  have hl : l.length = ts.length - p := by rw [← hd]; simp
  rw [hc (p + i) (by omega), ← hd]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem nameSeq_of {r : List UInt64} : ∀ (nm : List UInt64) (q : Nat), ts.drop q = nm.flatMap (fun c => [1, c]) ++ 0 :: r →
    NameSeq h q.toUInt64 nm
  | [], q, hd => by
    have := cellAt hc hd (i := 0) (by simp)
    simpa [NameSeq] using this
  | c :: t, q, hd => by
    have l0 := cellAt hc hd (i := 0) (by simp)
    have l1 := cellAt hc hd (i := 1) (by simp)
    have hl : ts.length - q = 2 + (t.flatMap (fun c => [1, c])).length + 1 + r.length := by
      have := congrArg List.length hd; simp at this ⊢; omega
    have hd2 : ts.drop (q + 2) = t.flatMap (fun c => [1, c]) ++ 0 :: r := by
      rw [← List.drop_drop, hd]; simp
    refine ⟨by simpa using l0, ?_, ?_⟩
    · rw [UInt64.add_assoc, show q.toUInt64 + 1 = (q + 1).toUInt64 from tu_add q 1 (by omega)]; simpa using l1
    · rw [show q.toUInt64 + 2 = (q + 2).toUInt64 from tu_add q 2 (by omega)]; exact nameSeq_of t (q + 2) hd2

theorem tokAt_of (h7 : bget h 7 = ts.length.toUInt64) {r : List UInt64} {toks : List Tok} (ht : TokL r toks) :
    ∀ p, p ≤ ts.length → ts.drop p = r → TokAt h p.toUInt64 toks := by
  induction ht with
  | nil =>
    intro p hp hd
    have : ts.length ≤ p := by have := congrArg List.length hd; simp at this; omega
    exact .nil (by rw [h7]; congr 1; omega)
  | @kw r toks t h5 h14 hok _ ih =>
    intro p hp hd
    have hl := congrArg List.length hd; simp at hl
    have hd1 : ts.drop (p + 1) = r := by rw [← List.drop_drop, hd]; simp
    have c0 := cellAt hc hd (i := 0) (by simp)
    refine .kw t ?_ (by simpa using c0) h5 h14 hok ?_
    · rw [h7]; apply UInt64.lt_iff_toNat_lt.mpr; rw [tn24 (by omega), tn24 (by omega)]; omega
    · rw [show p.toUInt64 + 1 = (p + 1).toUInt64 from tu_add p 1 (by omega)]; exact ih (p + 1) (by omega) hd1
  | @num r toks bs hb8 hbs _ ih =>
    intro p hp hd
    have hl := congrArg List.length hd; simp [hb8] at hl
    have hd9 : ts.drop (p + 9) = r := by rw [← List.drop_drop, hd]; simp [hb8]
    have c0 := cellAt hc hd (i := 0) (by simp)
    refine .num bs ?_ (by simpa using c0) hb8 ?_ hbs ?_
    · rw [h7]; apply UInt64.lt_iff_toNat_lt.mpr; rw [tn24 (by omega), tn24 (by omega)]; omega
    · intro i hi
      have ci := cellAt hc hd (i := 1 + i) (by simp [hb8]; omega)
      rw [show p.toUInt64 + 1 + i.toUInt64 = (p + (1 + i)).toUInt64 by
        rw [UInt64.add_assoc, show (1 : UInt64) + i.toUInt64 = (1 + i).toUInt64 from tu_add 1 i (by omega)]
        exact tu_add p (1 + i) (by omega), ci]
      simp only [List.getD_eq_getElem?_getD, List.cons_append]
      rw [Nat.add_comm 1 i, List.getElem?_cons_succ, List.getElem?_append_left (by omega)]
    · rw [show p.toUInt64 + 9 = (p + 9).toUInt64 from tu_add p 9 (by omega)]; exact ih (p + 9) (by omega) hd9
  | @id r toks nm hne _ ih =>
    intro p hp hd
    have hfl := flat2_len nm
    have hl := congrArg List.length hd; simp only [List.length_drop, List.length_cons, List.length_append, hfl] at hl
    have hd1 : ts.drop (p + 1) = nm.flatMap (fun c => [1, c]) ++ 0 :: r := by rw [← List.drop_drop, hd]; simp
    have hdr : ts.drop (p + 2 + 2 * nm.length) = r := by
      rw [show p + 2 + 2 * nm.length = (p + 1) + 2 * nm.length + 1 by omega, ← List.drop_drop, ← List.drop_drop, hd1,
        List.drop_left' hfl]
      rfl
    have c0 := cellAt hc hd (i := 0) (by simp)
    refine .id nm ⟨by simpa using c0, ?_, ?_⟩ ?_
    · rw [show p.toUInt64 + 1 = (p + 1).toUInt64 from tu_add p 1 (by omega)]; exact nameSeq_of hc hts nm (p + 1) hd1
    · rw [h7, tn24 (by omega), tn24 (by omega)]; omega
    · rw [show p.toUInt64 + 2 + 2 * nm.length.toUInt64 = (p + 2 + 2 * nm.length).toUInt64 by
        apply UInt64.toNat_inj.mp; simp <;> omega]
      exact ih _ (by omega) hdr

end

/-! ## the loaded heap -/
def entryBase (ts : Buf) : Buf := List.replicate 185408 0 ++ ts ++ [0, 2]

theorem entryBase_len (ts : Buf) : (entryBase ts).length = 185410 + ts.length := by
  simp only [entryBase, List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega

theorem entry_eq (ts : Buf) : entryHeap ts = ((entryBase ts).set 7 (bsize ts)).set 0 1 := by
  unfold entryHeap entryBase
  have hz : (List.replicate 185408 (0 : UInt64)).length = 185408 := List.length_replicate
  generalize List.replicate 185408 (0 : UInt64) = Z at hz ⊢
  simp only [bpush, bset, show (7 : UInt64).toNat = 7 from rfl, show (0 : UInt64).toNat = 0 from rfl]
  have e1 : ∀ W : Buf, ((Z ++ W).set 7 (bsize ts)).set 0 1 = (Z.set 7 (bsize ts)).set 0 1 ++ W := by
    intro W; rw [List.set_append_left _ _ (by omega), List.set_append_left _ _ (by simp; omega)]
  rw [e1, List.append_assoc Z, e1]; simp

theorem base_lo (ts : Buf) (i : Nat) (hi : i < 185408) : (entryBase ts).getD i 0 = 0 := by
  unfold entryBase
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_replicate]; exact hi),
    List.getElem?_replicate, if_pos hi]
  rfl

theorem base_tok (ts : Buf) (i : Nat) : (entryBase ts).getD (185408 + i) 0 = (ts ++ [0, 2]).getD i 0 := by
  unfold entryBase
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [List.length_replicate]; exact Nat.le_add_right _ _), List.length_replicate,
    Nat.add_sub_cancel_left]

theorem entry_cells (ts : Buf) : (v1 (entryHeap ts) 60 0 0).length = 185410 + ts.length ∧
    ∀ i : UInt64, bget (v1 (entryHeap ts) 60 0 0) i =
      if i.toNat = 0 ∨ i.toNat = 5 then 1 else if i.toNat = 7 then bsize ts else if i.toNat = 64 then 60 else bget (entryBase ts) i := by
  have hl := entryBase_len ts
  have b5 : bget (entryBase ts) 5 = 0 := base_lo ts 5 (by decide)
  have b65 : bget (entryBase ts) 65 = 0 := base_lo ts 65 (by decide)
  have b66 : bget (entryBase ts) 66 = 0 := base_lo ts 66 (by decide)
  rw [entry_eq]
  generalize entryBase ts = B at hl b5 b65 b66 ⊢
  have e : (B.set 7 (bsize ts)).set 0 1 = bset (bset B 7 (bsize ts)) 0 1 := rfl
  rw [e]
  have h5 : bget (bset (bset B 7 (bsize ts)) 0 1) 5 = 0 := by
    rw [bget_bset, bget_bset]; simpa using b5
  simp only [v1, h5, show (0 : UInt64) < d12 from by decide, if_true]
  refine ⟨by simp only [length_bset]; omega, fun i => ?_⟩
  simp only [bget_bset, length_bset, hl, d1]
  have c5 : i.toNat = 5 → bget B i = 0 := fun h => by rw [show i = 5 from UInt64.toNat_inj.mp h]; exact b5
  have c65 : i.toNat = 65 → bget B i = 0 := fun h => by rw [show i = 65 from UInt64.toNat_inj.mp h]; exact b65
  have c66 : i.toNat = 66 → bget B i = 0 := fun h => by rw [show i = 66 from UInt64.toNat_inj.mp h]; exact b66
  clear e h5
  have J : ∀ k, (k = i.toNat) ↔ (i.toNat = k) := fun k => ⟨Eq.symm, Eq.symm⟩
  have L : ∀ k, k < 67 → (k < 185410 + ts.length) = True := fun k hk => eq_true (by omega)
  by_cases i0 : i.toNat = 0 <;> by_cases i5 : i.toNat = 5 <;> by_cases i7 : i.toNat = 7 <;> by_cases i64 : i.toNat = 64 <;>
    by_cases i65 : i.toNat = 65 <;> by_cases i66 : i.toNat = 66 <;> (try omega) <;>
    simp [i0, i5, i7, i64, i65, i66, L, b5, c65, c66, J]

theorem init_lo (ts : Buf) (i : UInt64) (h1 : i.toNat < 185408) (h0 : i.toNat ≠ 0) (h5 : i.toNat ≠ 5) (h7 : i.toNat ≠ 7)
    (h64 : i.toNat ≠ 64) : bget (v1 (entryHeap ts) 60 0 0) i = 0 := by
  rw [(entry_cells ts).2]; simp only [h0, h5, h7, h64, false_or, if_false]; exact base_lo ts _ h1

theorem init_tok (ts : Buf) (hts : ts.length < 2 ^ 24) (i : Nat) (hi : i < ts.length + 2) :
    bget (v1 (entryHeap ts) 60 0 0) (d11 + i.toUInt64) = (ts ++ [0, 2]).getD i 0 := by
  have e : (d11 + i.toUInt64).toNat = 185408 + i := by rw [d11a _ (by simp; omega)]; simp; omega
  rw [(entry_cells ts).2, e]
  simp only [show ¬(185408 + i = 0 ∨ 185408 + i = 5) by omega, show 185408 + i ≠ 7 by omega, show 185408 + i ≠ 64 by omega,
    if_false]
  simp only [bget, e]; exact base_tok ts i

theorem rowZero_init (ts : Buf) (j : Nat) (hj : j < 512) : RowZero (v1 (entryHeap ts) 60 0 0) j := by
  intro k hk
  have e : (d7 + 8 * j.toUInt64 + k).toNat = 147520 + 8 * j + k.toNat := by
    simp [UInt64.toNat_add, UInt64.toNat_mul, d7v]; omega
  exact init_lo ts _ (by omega) (by omega) (by omega) (by omega) (by omega)

/-- **the initial configuration**: the loaded heap with task 60 represents `ParRun.init toks` with stack `[.defs]` -/
theorem rep_init (ts : Buf) (toks : List Tok) (hT : TokL ts toks) (hts : ts.length < 2 ^ 24) :
    Rep (v1 (entryHeap ts) 60 0 0) ts (ParRun.init toks) [.defs] := by
  obtain ⟨hlen, E⟩ := entry_cells ts
  generalize hH : v1 (entryHeap ts) 60 0 0 = H at hlen E
  have lo := fun i h1 h0 h5 h7 h64 => hH ▸ init_lo ts i h1 h0 h5 h7 h64
  have tk := fun i hi => hH ▸ init_tok ts hts i hi
  have rz := fun j hj => hH ▸ rowZero_init ts j hj
  have z : ∀ c : UInt64, c.toNat < 185408 → c.toNat ≠ 0 → c.toNat ≠ 5 → c.toNat ≠ 7 → c.toNat ≠ 64 → bget H c = 0 := lo
  have h0 : bget H 0 = 1 := by rw [E]; rfl
  have h5 : bget H 5 = 1 := by rw [E]; rfl
  have h7 : bget H 7 = ts.length.toUInt64 := by rw [E]; rfl
  have h64 : bget H 64 = 60 := by rw [E]; rfl
  have hc : ∀ i, i < ts.length → bget H (d11 + i.toUInt64) = ts.getD i 0 := by
    intro i hi; rw [tk i (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have s0 : bget H (d11 + ts.length.toUInt64) = 0 := by rw [tk _ (by omega)]; simp [List.getD_eq_getElem?_getD]
  have s2 : bget H (d11 + ts.length.toUInt64 + 1) = 2 := by
    have hl1 : ts.length + 1 < 2 ^ 64 := by omega
    have e1 : ts.length.toUInt64 + 1 = (ts.length + 1).toUInt64 := tu_add ts.length 1 hl1
    rw [UInt64.add_assoc, e1, tk (ts.length + 1) (by omega)]
    simp [List.getD_eq_getElem?_getD]
  have c : ∀ c : UInt64, c.toNat < 185408 → c.toNat ≠ 0 → c.toNat ≠ 5 → c.toNat ≠ 7 → c.toNat ≠ 64 → (bget H c).toNat = 0 :=
    fun c a b d e f => by rw [z c a b d e f]; rfl
  have h3 : bget H 3 = 0 := z 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨⟨hc, s0, s2, h7⟩, hts, by rw [h0]; rfl, ?_, z 11 (by decide) (by decide) (by decide) (by decide) (by decide),
    ⟨c 4 (by decide) (by decide) (by decide) (by decide) (by decide), by simp [ParRun.init], fun i hi => by simp [ParRun.init] at hi⟩,
    ?_, ?_, fun s hs => by simp [ParRun.init] at hs, fun x hx => by simp [ParRun.init] at hx,
    z 30 (by decide) (by decide) (by decide) (by decide) (by decide), z 32 (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, ?_⟩
  · rw [h3]; exact tokAt_of hc hts h7 hT 0 (Nat.zero_le _) rfl
  · -- DefsRep (between defs)
    have row0 : ∀ j, j < 512 → RowZero H j := rz
    refine ⟨c 12 (by decide) (by decide) (by decide) (by decide) (by decide), by simp [ParRun.init],
      by rw [c 27 (by decide) (by decide) (by decide) (by decide) (by decide)]; decide, fun j hj => by simp [ParRun.init] at hj, ?_,
      fun j _ hj => row0 j hj, ?_, ?_, ?_⟩
    · simp only [inDefF, List.all_cons, List.all_nil, Frame.isDefs, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
      exact fun _ => row0 0 (by decide)
    · intro i _ hi
      apply z
      all_goals (simp [UInt64.toNat_add, d7v]; omega)
    · refine ⟨by rw [c 26 (by decide) (by decide) (by decide) (by decide) (by decide)]; decide, fun k _ hk => ?_,
        fun k hk => by rw [c 26 (by decide) (by decide) (by decide) (by decide) (by decide)] at hk; omega⟩
      have e : (d7 + 8192 + 3 * k.toUInt64).toNat = 155712 + 3 * k := by
        have : (3 * k.toUInt64).toNat = 3 * k := by
          rw [UInt64.toNat_mul, show (3 : UInt64).toNat = 3 from rfl, tn24 (by omega)]; exact Nat.mod_eq_of_lt (by omega)
        rw [UInt64.toNat_add, this, d7v]; simp; omega
      apply z <;> omega
    · exact hashRep_nil (fun i a b => z i (by omega) (by omega) (by omega) (by omega) (by omega))
  · -- ArenaRep
    refine ⟨c 9 (by decide) (by decide) (by decide) (by decide) (by decide), by simp [ParRun.init],
      c 8 (by decide) (by decide) (by decide) (by decide) (by decide), by simp [ParRun.init], fun _ => [], ?_, ?_, ?_, ?_⟩ <;>
      simp [ParRun.init]
  · -- OutRep
    refine ⟨by simp [ParRun.init]; omega, ?_⟩
    have e2 : (d11 + (ts.length + 1).toUInt64).toNat = 185408 + ts.length + 1 := by rw [d11a _ (by simp; omega)]; simp; omega
    have g := tk (ts.length + 1) (by omega)
    simp only [bget, e2] at g
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_drop]
    cases k with
    | zero =>
      have hk : 185408 + ts.length + 1 < H.length := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at g
      rw [List.getElem?_eq_getElem hk, g]; simp [ParRun.init]
    | succ k =>
      rw [List.getElem?_eq_none (by omega)]; simp [ParRun.init]
  · -- TasksRep
    refine ⟨c 5 |> fun _ => by rw [h5]; rfl, by decide, fun k hk => ?_⟩
    simp at hk; subst hk
    refine ⟨?_, trivial⟩
    simp only [taskAt, List.length_cons, List.length_nil]
    rw [show d1 + 3 * (Nat.toUInt64 (1 - 1 - 0)) = 64 from by decide, h64]; rfl
