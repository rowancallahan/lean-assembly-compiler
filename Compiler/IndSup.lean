/- The worst-case cell count of an inductive-path program over all inputs of `n` bytes (`cellsSup`), for the
space bound of programs whose allocation is not bounded by a fixed number of cells per input node (several
functions: a call of a later function may allocate in proportion to a computed value).  Source level, no model.

`C.dec` decodes the byte format `C.enc` (`dec_enc`); `cellsSup … n` is the largest `Pg.al` over the decodings
of all `256 ^ n` byte strings of length `n` (a definition, never computed), so every input of `n` bytes
allocates at most `cellsSup … n` cells (`al_le_cellsSup`). -/
import Compiler.IndMain

namespace Proven.Mach.Ind

/-- decode the fields of a shape into `(x, l, r)` -/
def decFlds (d : List UInt8 → Option (C × List UInt8)) : List Fld → BitVec 64 × C × C → List UInt8 →
    Option ((BitVec 64 × C × C) × List UInt8)
  | [], acc, L => some (acc, L)
  | .x :: fs, (_, l, r), L => decFlds d fs (BitVec.ofNat 64 (unle (L.take 8)), l, r) (L.drop 8)
  | .b :: fs, (_, l, r), L => decFlds d fs (BitVec.ofNat 64 (unle (L.take 1)), l, r) (L.drop 1)
  | .l :: fs, (x, _, r), L => match d L with
    | some (v, L') => decFlds d fs (x, v, r) L'
    | none => none
  | .r :: fs, (x, l, _), L => match d L with
    | some (v, L') => decFlds d fs (x, l, v) L'
    | none => none

/-- decode one value (fuel: the depth) -/
def C.dec (sh : Shape) : Nat → List UInt8 → Option (C × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, b :: L => match decFlds (C.dec sh n) (sh.getD b.toNat []) (0, .z, .z) L with
    | some ((x, l, r), L') => some (.c b.toNat x l r, L')
    | none => none

theorem x_dec (x : BitVec 64) (R : List UInt8) : BitVec.ofNat 64 (unle ((leN 8 x.toNat ++ R).take 8)) = x := by
  rw [List.take_append_of_le_length (by simp [leN_length]), List.take_of_length_le (by simp [leN_length]),
    unle_leN, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
theorem x_dec0 (x : BitVec 64) : BitVec.ofNat 64 (unle ((leN 8 x.toNat).take 8)) = x := by
  have := x_dec x []; simpa using this
theorem x_drop (x : BitVec 64) (R : List UInt8) : (leN 8 x.toNat ++ R).drop 8 = R := by
  rw [List.drop_append_of_le_length (by simp [leN_length]), List.drop_of_length_le (by simp [leN_length]),
    List.nil_append]

theorem b_dec (x : BitVec 64) (hx : x.toNat < 256) (R : List UInt8) :
    BitVec.ofNat 64 (unle (((leN 8 x.toNat).take 1 ++ R).take 1)) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [leN, unle, Nat.mod_eq_of_lt hx]
theorem b_drop (x : BitVec 64) (R : List UInt8) : ((leN 8 x.toNat).take 1 ++ R).drop 1 = R := by
  simp [leN]

theorem decFlds_ok (d : List UInt8 → Option (C × List UInt8)) (x : BitVec 64) (l r : C) (el er : List UInt8)
    (hl : ∀ R, d (el ++ R) = some (l, R)) (hr : ∀ R, d (er ++ R) = some (r, R)) :
    ∀ (fs : List Fld) (x0 : BitVec 64) (l0 r0 : C) (R : List UInt8),
      (Fld.b ∈ fs → x.toNat < 256) →
      decFlds d fs (x0, l0, r0) (fs.flatMap (encF x el er) ++ R) =
        some ((if Fld.x ∈ fs ∨ Fld.b ∈ fs then x else x0, if Fld.l ∈ fs then l else l0,
          if Fld.r ∈ fs then r else r0), R)
  | [], x0, l0, r0, R, _ => by simp [decFlds]
  | .x :: fs, x0, l0, r0, R, hb => by
    simp only [List.flatMap_cons, encF, List.append_assoc, decFlds, x_dec, x_drop]
    rw [decFlds_ok d x l r el er hl hr fs x l0 r0 R (fun m => hb (List.mem_cons_of_mem _ m))]
    simp
  | .b :: fs, x0, l0, r0, R, hb => by
    simp only [List.flatMap_cons, encF, List.append_assoc, decFlds, b_dec x (hb (by simp)), b_drop]
    rw [decFlds_ok d x l r el er hl hr fs x l0 r0 R (fun m => hb (List.mem_cons_of_mem _ m))]
    simp
  | .l :: fs, x0, l0, r0, R, hb => by
    simp only [List.flatMap_cons, encF, List.append_assoc, decFlds, hl]
    rw [decFlds_ok d x l r el er hl hr fs x0 l r0 R (fun m => hb (List.mem_cons_of_mem _ m))]
    simp
  | .r :: fs, x0, l0, r0, R, hb => by
    simp only [List.flatMap_cons, encF, List.append_assoc, decFlds, hr]
    rw [decFlds_ok d x l r el er hl hr fs x0 l0 r R (fun m => hb (List.mem_cons_of_mem _ m))]
    simp

theorem dec_enc (sh : Shape) (hsh : sh.length < 255) :
    ∀ (v : C), v.wf sh → ∀ n, v.depth < n → ∀ R, C.dec sh n (v.enc sh ++ R) = some (v, R)
  | .z, h => absurd h id
  | .c t x l r, ⟨ht, hx, hl, hr⟩ => by
    intro n hn R
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [C.depth] at hn
    have htb : (UInt8.ofNat t).toNat = t := by simp [UInt8.toNat_ofNat]; omega
    have okl : ∀ R, C.dec sh m (C.enc sh l ++ R) = some (l, R) ∨ Fld.l ∉ sh.getD t [] := by
      intro R; by_cases ml : Fld.l ∈ sh.getD t []
      · rw [if_pos ml] at hl; exact .inl (dec_enc sh hsh l hl m (by omega) R)
      · exact .inr ml
    have okr : ∀ R, C.dec sh m (C.enc sh r ++ R) = some (r, R) ∨ Fld.r ∉ sh.getD t [] := by
      intro R; by_cases mr : Fld.r ∈ sh.getD t []
      · rw [if_pos mr] at hr; exact .inl (dec_enc sh hsh r hr m (by omega) R)
      · exact .inr mr
    -- the fields of the shape decode to `x`, `l`, `r` (absent ones are `0` / `z`)
    have key : ∀ (fs : List Fld), (∀ f ∈ fs, f ∈ sh.getD t []) → ∀ (x0 : BitVec 64) (l0 r0 : C) (R : List UInt8),
        decFlds (C.dec sh m) fs (x0, l0, r0) (fs.flatMap (encF x (l.enc sh) (r.enc sh)) ++ R) =
          some ((if Fld.x ∈ fs ∨ Fld.b ∈ fs then x else x0, if Fld.l ∈ fs then l else l0,
            if Fld.r ∈ fs then r else r0), R) := by
      intro fs
      induction fs with
      | nil => intro _ x0 l0 r0 R; simp [decFlds]
      | cons f fs ih =>
        intro hsub x0 l0 r0 R
        have hsub' : ∀ f ∈ fs, f ∈ sh.getD t [] := fun f hf => hsub f (List.mem_cons_of_mem _ hf)
        cases f with
        | x =>
          simp only [List.flatMap_cons, encF, List.append_assoc, decFlds, x_dec, x_drop]
          rw [ih hsub']; simp
        | b =>
          have hm := hsub .b (by simp)
          simp only [List.flatMap_cons, encF, List.append_assoc, decFlds, b_dec x (hx.2 hm), b_drop]
          rw [ih hsub']; simp
        | l =>
          have hm := hsub .l (by simp)
          have e : ∀ R, C.dec sh m (C.enc sh l ++ R) = some (l, R) := fun R => (okl R).resolve_right (by simpa using hm)
          simp only [List.flatMap_cons, encF, List.append_assoc, decFlds, e]
          rw [ih hsub']; simp
        | r =>
          have hm := hsub .r (by simp)
          have e : ∀ R, C.dec sh m (C.enc sh r ++ R) = some (r, R) := fun R => (okr R).resolve_right (by simpa using hm)
          simp only [List.flatMap_cons, encF, List.append_assoc, decFlds, e]
          rw [ih hsub']; simp
    have k := key (sh.getD t []) (fun f hf => hf) 0 .z .z R
    simp only [C.enc, List.cons_append, C.dec, htb, k]
    congr 3
    · split
      · rfl
      · next h => exact (hx.1 (fun a => h (.inl a)) (fun a => h (.inr a))).symm
    · split
      · rfl
      · next h => rw [if_neg h] at hl; exact hl.symm
    · split
      · rfl
      · next h => rw [if_neg h] at hr; exact hr.symm

/-- decode the input of a program: the first value, the second (if `b` is an input), the word (if `ain`) -/
def decIn (sh : Shape) (bi : BIn) (ain : Bool) (L : List UInt8) : Option (C × C × BitVec 64) :=
  match C.dec sh (L.length + 1) L with
  | none => none
  | some (v₁, L₁) =>
    match (if bi = .inp then C.dec sh (L.length + 1) L₁ else some (.z, L₁)) with
    | none => none
    | some (v₂, L₂) => some (v₁, v₂, if ain then BitVec.ofNat 64 (unle (L₂.take 8)) else 0)

theorem decIn_ok (sh : Shape) (hsh : sh.length < 255) (bi : BIn) (ain : Bool) (v₁ v₂ : C) (a : BitVec 64)
    (h1 : v₁.wf sh) (h2 : bi = .inp → v₂.wf sh) :
    decIn sh bi ain (inBytesA sh bi ain v₁ v₂ a) = some (v₁, (if bi = .inp then v₂ else .z), if ain then a else 0) := by
  have n1 := nodes_le sh v₁ h1
  unfold decIn
  have hl : (inBytesA sh bi ain v₁ v₂ a).length = (inBytes sh bi v₁ v₂).length + (if ain then 8 else 0) := by
    cases ain <;> simp [inBytesA, leN_length]
  cases bi with
  | inp =>
    have n2 := nodes_le sh v₂ (h2 rfl)
    have e : inBytesA sh .inp ain v₁ v₂ a = v₁.enc sh ++ (v₂.enc sh ++ if ain then leN 8 a.toNat else []) := by
      simp [inBytesA, inBytes]
    have hl' : (inBytes sh .inp v₁ v₂).length = (v₁.enc sh).length + (v₂.enc sh).length := by simp [inBytes]
    rw [e, dec_enc sh hsh v₁ h1 _ (by simp; omega)]
    simp only [if_true]
    rw [dec_enc sh hsh v₂ (h2 rfl) _ (by simp; omega)]
    cases ain <;> simp [x_dec0]
  | ctor t =>
    have e : inBytesA sh (.ctor t) ain v₁ v₂ a = v₁.enc sh ++ (if ain then leN 8 a.toNat else []) := by
      simp [inBytesA, inBytes]
    rw [e, dec_enc sh hsh v₁ h1 _ (by simp; omega)]
    cases ain <;> simp [x_dec0]
  | none =>
    have e : inBytesA sh .none ain v₁ v₂ a = v₁.enc sh ++ (if ain then leN 8 a.toNat else []) := by
      simp [inBytesA, inBytes]
    rw [e, dec_enc sh hsh v₁ h1 _ (by simp; omega)]
    cases ain <;> simp [x_dec0]

/-- all byte strings of length `n` -/
def allBytes : Nat → List (List UInt8)
  | 0 => [[]]
  | n + 1 => (allBytes n).flatMap fun L => (List.range 256).map fun b => UInt8.ofNat b :: L

theorem mem_allBytes : ∀ L : List UInt8, L ∈ allBytes L.length
  | [] => by simp [allBytes]
  | b :: L => by
    simp only [allBytes, List.length_cons, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨L, mem_allBytes L, b.toNat, b.toNat_lt, by simp⟩

theorem le_foldr_max {α : Type} (F : α → Nat) : ∀ (xs : List α) (a : α), a ∈ xs → F a ≤ (xs.map F).foldr max 0
  | [], _, h => absurd h (by simp)
  | y :: ys, a, h => by
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max F ys a h) (Nat.le_max_right _ _)

/-- **The worst-case cell count** of the program `pg` (entry word `a0`, or the input's word when `ain`) over all
inputs of `n` bytes -/
def cellsSup {rk : Kd} (sh : Shape) (pg : Pg rk) (bi : BIn) (ain : Bool) (a0 : BitVec 64) (n : Nat) : Nat :=
  ((allBytes n).map fun L => match decIn sh bi ain L with
    | some (v₁, v₂, a) => pg.al v₁ (if ain then a else a0) (bi.val v₂)
    | none => 0).foldr max 0

theorem al_le_cellsSup {rk : Kd} (sh : Shape) (hsh : sh.length < 255) (pg : Pg rk) (bi : BIn) (ain : Bool)
    (a0 : BitVec 64) (v₁ v₂ : C) (a : BitVec 64) (h1 : v₁.wf sh) (h2 : bi = .inp → v₂.wf sh) :
    pg.al v₁ (if ain then a else a0) (bi.val v₂) ≤
      cellsSup sh pg bi ain a0 (inBytesA sh bi ain v₁ v₂ a).length := by
  have := le_foldr_max (fun L => match decIn sh bi ain L with
    | some (v₁, v₂, a) => pg.al v₁ (if ain then a else a0) (bi.val v₂)
    | none => 0) _ _ (mem_allBytes (inBytesA sh bi ain v₁ v₂ a))
  unfold cellsSup
  refine Nat.le_trans ?_ this
  simp only [decIn_ok sh hsh bi ain v₁ v₂ a h1 h2]
  cases bi <;> cases ain <;> simp [BIn.val]

end Proven.Mach.Ind
