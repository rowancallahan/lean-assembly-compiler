import Nano.Base.V2.Sem
/- nano v2 small backend, proof layer 3: the FLAT code `SC.flat` (Nano/V2/Gen.lean) on a pc-level machine.
`pstep` executes the instruction at index `pc` of the code list (branches/jumps by their byte offsets); a big-step
run of structured code (`SC.Ex`, Nano/V2/Sem.lean) is a pc-level run of its flattening: fall-through ends at
`pos + len`, a jump ends at its label (loop head/exit, the abort stubs). -/
namespace Nano.V2B

/-- the target of a byte offset from instruction `pc` -/
def jt (pc : Nat) (off : Int) : Nat := ((pc : Int) + off / 4).toNat

/-- one pc-level step; `none`: halted (`ret`) or stuck -/
def pstep (c : Cfg) (C : List I) (p : Nat × St) : Option (Nat × St) :=
  match C[p.1]? with
  | some (.br k r1 r2 off) => some (if k.eval (p.2.get r1) (p.2.get r2) then jt p.1 off else p.1 + 1, p.2)
  | some (.jal off) => some (jt p.1 off, p.2)
  | some i => (i.run c p.2).map (p.1 + 1, ·)
  | none => none

inductive PStar (c : Cfg) (C : List I) : Nat × St → Nat × St → Prop
  | refl (p : Nat × St) : PStar c C p p
  | step {p q r : Nat × St} : pstep c C p = some q → PStar c C q r → PStar c C p r

theorem PStar.trans {c : Cfg} {C : List I} {p q r : Nat × St} (h1 : PStar c C p q) (h2 : PStar c C q r) :
    PStar c C p r := by
  induction h1 with
  | refl => exact h2
  | step e _ ih => exact .step e (ih h2)

/-- the list `l` sits at index `pos` of `C` -/
def At (C : List I) (pos : Nat) (l : List I) : Prop := ∀ i, i < l.length → C[pos + i]? = l[i]?

theorem At.left {C : List I} {pos : Nat} {a b : List I} (h : At C pos (a ++ b)) : At C pos a := fun i hi => by
  have := h i (by simp; omega); rw [this, List.getElem?_append_left hi]

theorem At.right {C : List I} {pos : Nat} {a b : List I} (h : At C pos (a ++ b)) : At C (pos + a.length) b :=
  fun i hi => by
    have := h (a.length + i) (by simp; omega)
    rw [show pos + a.length + i = pos + (a.length + i) by omega, this, List.getElem?_append_right (by omega)]
    simp

theorem At.get {C : List I} {pos : Nat} {l : List I} (h : At C pos l) {i : Nat} {x : I} (hx : l[i]? = some x) :
    C[pos + i]? = some x := by rw [h i (List.getElem?_eq_some_iff.1 hx).1, hx]

theorem jt_toff (a b : Nat) : jt a (toff a b) = b := by
  unfold jt toff
  rw [show (4 * ((b : Int) - a)) / 4 = (b : Int) - a by omega]; omega

/-- a straight instruction steps by `I.run` -/
theorem pstep_straight {c : Cfg} {C : List I} {pc : Nat} {i : I} {s s' : St} (hC : C[pc]? = some i)
    (h : i.run c s = some s') : pstep c C (pc, s) = some (pc + 1, s') := by
  unfold pstep
  cases i <;> simp_all [I.run]

theorem runL_star {c : Cfg} {C : List I} : ∀ (l : List I) (pos : Nat) (s s' : St), At C pos l →
    runL c l s = some s' → PStar c C (pos, s) (pos + l.length, s')
  | [], pos, s, s', _, h => by simp only [runL, Option.some.injEq] at h; subst h; exact .refl _
  | i :: l, pos, s, s', hA, h => by
    simp only [runL] at h
    cases hi : i.run c s with
    | none => rw [hi] at h; simp at h
    | some s1 =>
      rw [hi] at h; simp only [Option.bind_some] at h
      have e := pstep_straight (hA.get (i := 0) (by simp)) hi
      have := runL_star l (pos + 1) s1 s' (fun j hj => by
        have := hA (j + 1) (by simp; omega); rw [show pos + 1 + j = pos + (j + 1) by omega, this]; simp) h
      exact .step (by simpa using e) (by simpa [Nat.add_assoc, Nat.add_comm 1] using this)

theorem SC.flat_len (om cp : Nat) : ∀ (sc : SC) (pos hd ex : Nat), (sc.flat om cp pos hd ex).length = sc.len
  | .ins l, _, _, _ => rfl
  | .seq a b, pos, hd, ex => by simp [SC.flat, SC.len, SC.flat_len om cp a, SC.flat_len om cp b]
  | .ite _ _ _ t e, pos, hd, ex => by simp [SC.flat, SC.len, SC.flat_len om cp t, SC.flat_len om cp e]; omega
  | .loop test dec z body, pos, hd, ex => by
    simp [SC.flat, SC.len, SC.flat_len om cp z, SC.flat_len om cp body]; omega
  | .jmp _, _, _, _ => rfl

/-- the label of a jump target -/
def Tg.at (om cp hd ex : Nat) : Tg → Nat
  | .head => hd | .exit => ex | .oom => om | .cap => cp

/-- **layer 3**: a structured run is a pc-level run of the flattened code -/
def FlatPost (c : Cfg) (C : List I) (om cp hd ex : Nat) (pos : Nat) (sc : SC) (s : St) : Res → Prop
  | .ok s' => PStar c C (pos, s) (pos + sc.len, s')
  | .jmp t s' => PStar c C (pos, s) (t.at om cp hd ex, s')

theorem At.congr {C : List I} {pos pos' : Nat} {l : List I} (h : At C pos l) (e : pos = pos') : At C pos' l := e ▸ h

theorem At.getAt {C : List I} {pos : Nat} {l : List I} (h : At C pos l) {i : Nat} {x : I} (hx : l[i]? = some x)
    (q : Nat) (hq : pos + i = q) : C[q]? = some x := hq ▸ h.get hx

/-- the pieces of a flattened loop at `pos` -/
theorem At.loop {C : List I} {om cp pos hd ex : Nat} {test dec : List I} {z body : SC}
    (hA : At C pos ((SC.loop test dec z body).flat om cp pos hd ex)) :
    let pb := pos + test.length + 2 + dec.length
    let pz := pb + body.len
    let pex := pz + z.len
    At C pos test ∧ C[pos + test.length]? = some (.br .bne 5 0 8) ∧
      C[pos + test.length + 1]? = some (.jal (toff (pos + test.length + 1) pz)) ∧
      At C (pos + test.length + 2) dec ∧ At C pb (body.flat om cp pb pos pex) ∧ At C pz (z.flat om cp pz pos pex) := by
  intro pb pz pex
  simp only [SC.flat] at hA
  exact ⟨hA.left.left.left.left, hA.left.left.left.right.getAt (i := 0) rfl _ rfl,
    hA.left.left.left.right.getAt (i := 1) rfl _ (by omega),
    hA.left.left.right.congr (by simp; omega), hA.left.right.congr (by simp; omega),
    hA.right.congr (by simp [SC.flat_len]; omega)⟩

theorem loop_len (test dec : List I) (z body : SC) :
    (SC.loop test dec z body).len = test.length + 2 + dec.length + body.len + z.len := rfl

theorem get0 (s : St) : s.get 0 = 0 := rfl

/-- the loop test: fuel 0 goes to ZERO, else through the decrement to the body -/
theorem loop_head {c : Cfg} {C : List I} {om cp pos hd ex : Nat} {test dec : List I} {z body : SC} {s s1 : St}
    (hA : At C pos ((SC.loop test dec z body).flat om cp pos hd ex)) (h1 : runL c test s = some s1) :
    (s1.get 5 = 0 → PStar c C (pos, s) (pos + test.length + 2 + dec.length + body.len, s1)) ∧
    (∀ s2, s1.get 5 ≠ 0 → runL c dec s1 = some s2 → PStar c C (pos, s) (pos + test.length + 2 + dec.length, s2)) := by
  obtain ⟨hT, hB, hJ, hD, -, -⟩ := hA.loop
  have e1 := runL_star test pos s s1 hT h1
  refine ⟨fun h0 => e1.trans (.step (q := (pos + test.length + 1, s1)) ?_ (.step ?_ (.refl _))), fun s2 h0 h2 =>
    e1.trans (.step (q := (pos + test.length + 2, s1)) ?_ (runL_star dec _ s1 s2 hD h2))⟩
  · have hc : BOp.eval .bne (s1.get 5) (s1.get 0) = false := by rw [h0, get0]; rfl
    unfold pstep; simp only [hB, hc]; rfl
  · unfold pstep; simp only [hJ, jt_toff]
  · have hc : BOp.eval .bne (s1.get 5) (s1.get 0) = true := by
      simp only [BOp.eval, get0, bne_iff_ne, ne_eq]; exact h0
    unfold pstep; simp only [hB, hc, if_true]; congr 2

theorem flat_ok {c : Cfg} {C : List I} {om cp : Nat} {sc : SC} {s : St} {r : Res} (e : SC.Ex c sc s r) :
    ∀ pos hd ex, At C pos (sc.flat om cp pos hd ex) → FlatPost c C om cp hd ex pos sc s r := by
  induction e with
  | @ins l s s' h => intro pos hd ex hA; exact runL_star _ pos _ _ hA h
  | @seq a b s s1 r e1 e2 ih1 ih2 =>
    intro pos hd ex hA
    simp only [SC.flat] at hA
    have h1 := ih1 pos hd ex hA.left
    have h2 := ih2 (pos + a.len) hd ex (hA.right.congr (by rw [SC.flat_len]))
    cases r with
    | ok s2 => exact h1.trans (by simpa [FlatPost, SC.len, Nat.add_assoc] using h2)
    | jmp t s2 => exact h1.trans h2
  | @seqJ a b s t s1 e1 ih => intro pos hd ex hA; simp only [SC.flat] at hA; exact ih pos hd ex hA.left
  | @iteT k r1 r2 t e s r hc e1 ih =>
    intro pos hd ex hA
    simp only [SC.flat] at hA
    have hb : C[pos]? = some (.br k r1 r2 8) := hA.left.left.left.getAt (i := 0) rfl _ rfl
    have e0 : pstep c C (pos, s) = some (pos + 2, s) := by
      unfold pstep; simp only [hb, hc, if_true]; congr 2
    have h2 := ih (pos + 2) hd ex (hA.left.left.right.congr (by simp))
    cases r with
    | jmp t' s' => exact .step e0 h2
    | ok s' =>
      have hj : C[pos + 2 + t.len]? = some (.jal (toff (pos + 2 + t.len) (pos + 2 + t.len + 1 + e.len))) :=
        hA.left.right.getAt (i := 0) rfl _ (by simp [SC.flat_len]; omega)
      refine .step e0 (h2.trans (.step (q := (pos + 2 + t.len + 1 + e.len, s')) ?_ ?_))
      · unfold pstep; simp only [hj, jt_toff]
      · show PStar c C _ (pos + (2 + t.len + 1 + e.len), s')
        rw [show pos + (2 + t.len + 1 + e.len) = pos + 2 + t.len + 1 + e.len by omega]; exact .refl _
  | @iteF k r1 r2 t e s r hc e1 ih =>
    intro pos hd ex hA
    simp only [SC.flat] at hA
    have hb : C[pos]? = some (.br k r1 r2 8) := hA.left.left.left.getAt (i := 0) rfl _ rfl
    have hj : C[pos + 1]? = some (.jal (toff (pos + 1) (pos + 2 + t.len + 1))) :=
      hA.left.left.left.getAt (i := 1) rfl _ rfl
    have e0 : pstep c C (pos, s) = some (pos + 1, s) := by unfold pstep; simp only [hb, hc]; rfl
    have e2 : pstep c C (pos + 1, s) = some (pos + 2 + t.len + 1, s) := by unfold pstep; simp only [hj, jt_toff]
    have h2 := ih _ hd ex (hA.right.congr (by simp [SC.flat_len]; omega))
    cases r with
    | jmp t' s' => exact .step e0 (.step e2 h2)
    | ok s' =>
      refine .step e0 (.step e2 ?_)
      show PStar c C _ (pos + (2 + t.len + 1 + e.len), s')
      rw [show pos + (2 + t.len + 1 + e.len) = pos + 2 + t.len + 1 + e.len by omega]; exact h2
  | @jmp t s =>
    intro pos hd ex hA
    have hj : C[pos]? = some (.jal (toff pos (t.at om cp hd ex))) :=
      hA.getAt (i := 0) (by cases t <;> rfl) _ (by simp)
    exact .step (by unfold pstep; simp only [hj, jt_toff]) (.refl _)
  | @loopZ test dec z body s s1 s2 h1 h0 ez ih =>
    intro pos hd ex hA
    have hz := ih _ pos _ hA.loop.2.2.2.2.2
    exact ((loop_head hA h1).1 h0).trans (by simpa [FlatPost, loop_len, Nat.add_assoc] using hz)
  | @loopZX test dec z body s s1 s2 h1 h0 ez ih =>
    intro pos hd ex hA
    have hz := ih _ pos _ hA.loop.2.2.2.2.2
    exact ((loop_head hA h1).1 h0).trans (by simpa [FlatPost, Tg.at, loop_len, Nat.add_assoc] using hz)
  | @loopZA test dec z body s s1 t s2 h1 h0 ez ht ih =>
    intro pos hd ex hA
    have hz := ih _ pos _ hA.loop.2.2.2.2.2
    rcases ht with rfl | rfl <;> exact ((loop_head hA h1).1 h0).trans hz
  | @loopX test dec z body s s1 s2 s3 h1 h0 h2 eb ih =>
    intro pos hd ex hA
    have hb := ih _ pos _ hA.loop.2.2.2.2.1
    exact ((loop_head hA h1).2 s2 h0 h2).trans (by simpa [FlatPost, Tg.at, loop_len, Nat.add_assoc] using hb)
  | @loopA test dec z body s s1 s2 t s3 h1 h0 h2 eb ht ih =>
    intro pos hd ex hA
    have hb := ih _ pos _ hA.loop.2.2.2.2.1
    rcases ht with rfl | rfl <;> exact ((loop_head hA h1).2 s2 h0 h2).trans hb
  | @loopH test dec z body s s1 s2 s3 r h1 h0 h2 eb el ihb ihl =>
    intro pos hd ex hA
    have hb : PStar c C (_, s2) (pos, s3) := ihb _ pos _ hA.loop.2.2.2.2.1
    have hl := ihl pos hd ex hA
    have e1 := ((loop_head hA h1).2 s2 h0 h2).trans hb
    cases r with
    | ok s4 => exact e1.trans hl
    | jmp t s4 => exact e1.trans hl

/-! ## bytes of a word (used by the Sail layer) -/

theorem or8 (a b : Nat) (hb : b < 2 ^ 8) : a <<< 8 ||| b = a * 256 + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

theorem cat8_extract (w : BitVec 64) :
    w.extractLsb' (8 * 7) 8 ++ w.extractLsb' (8 * 6) 8 ++ w.extractLsb' (8 * 5) 8 ++ w.extractLsb' (8 * 4) 8 ++
      w.extractLsb' (8 * 3) 8 ++ w.extractLsb' (8 * 2) 8 ++ w.extractLsb' (8 * 1) 8 ++ w.extractLsb' (8 * 0) 8 = w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  repeat rw [or8 _ _ (Nat.mod_lt _ (by decide))]
  have := w.isLt; omega

end Nano.V2B
