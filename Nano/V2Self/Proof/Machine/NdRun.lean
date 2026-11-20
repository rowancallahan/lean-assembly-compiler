/- Machine bridge (Opus box E): **the node theorem** — by induction on the AST node, the J template of every node
satisfies the heap contract for its machine-level semantics: `runV` (value mode, `EVHw`), `runT` (tail mode, `EVHt`),
`runL` (operand sequences).  Side conditions `OkV` / `OkT` / `OkL`: widths (Gen's g53 pass) and scoping (the parser's
slot discipline); callees satisfy `DefX` (call-graph order, discharged def by def). -/
import Nano.V2Self.Proof.Machine.NdSem
namespace Templates
open CallProbe ParSpec

/-- operand count of a prim -/
def arity (pn : Nat) : Nat := if pn = 1 ∨ pn = 3 ∨ pn = 5 then 0 else if pn = 2 ∨ pn = 6 then 1 else if pn = 8 then 3 else 2

mutual
def OkV (K : SC) : Nd → Prop
  | .const _ => True
  | .loc s w => s + w ≤ K.nl
  | .bin _ a b => OkV K a ∧ OkV K b ∧ wd K a = 1 ∧ wd K b = 1 ∧ (∀ k, rd b k → ¬ wr K.p a k)
  | .ite _ a b t e => OkV K a ∧ OkV K b ∧ OkV K t ∧ OkV K e ∧ wd K a = 1 ∧ wd K b = 1 ∧ wd K e = wd K t ∧
      (∀ k, rd b k → ¬ wr K.p a k) ∧ (∀ k, rd t k → ¬ (wr K.p a k ∨ wr K.p b k)) ∧
      (∀ k, rd e k → ¬ (wr K.p a k ∨ wr K.p b k))
  | .letE s w v b => OkV K v ∧ OkV K b ∧ wd K v = w ∧ s + w ≤ K.nl ∧
      (∀ k, rd b k → ¬ (s ≤ k ∧ k < s + w) → ¬ wr K.p v k)
  | .pair cs => OkL K cs
  | .call id as => OkL K as ∧ id < K.nd ∧ wdL K as = K.npwOf id
  | .prim pn as => OkL K as ∧ wdL K as = arity pn ∧ ((pn = 1 ∨ pn = 3 ∨ pn = 5) → as = [])
  | .loop z s => OkT K z K.q ∧ OkT K s K.q ∧ 1 ≤ K.p ∧ K.p ≤ K.nl ∧
      (∀ k, (wr K.p z k ∨ wr K.p s k) → K.p ≤ k) ∧ (∀ k, (rd z k ∨ rd s k) → ¬ (wr K.p z k ∨ wr K.p s k))
  | .cont _ => False
/-- tail mode with exit width w -/
def OkT (K : SC) : Nd → Nat → Prop
  | .ite _ a b t e, w => OkV K a ∧ OkV K b ∧ OkT K t w ∧ OkT K e w ∧ wd K a = 1 ∧ wd K b = 1 ∧
      (∀ k, rd b k → ¬ wr K.p a k) ∧ (∀ k, rd t k → ¬ (wr K.p a k ∨ wr K.p b k)) ∧
      (∀ k, rd e k → ¬ (wr K.p a k ∨ wr K.p b k))
  | .letE s w' v b, w => OkV K v ∧ OkT K b w ∧ wd K v = w' ∧ s + w' ≤ K.nl ∧
      (∀ k, rd b k → ¬ (s ≤ k ∧ k < s + w') → ¬ wr K.p v k)
  | .cont e, _ => OkV K e ∧ wd K e = K.p - 1 ∧ 1 ≤ K.p ∧ K.p ≤ K.nl
  | e, w => OkV K e ∧ wd K e = w
def OkL (K : SC) : List Nd → Prop
  | [] => True
  | c :: cs => OkV K c ∧ OkL K cs ∧ (∀ k, rdL cs k → ¬ wr K.p c k)
end

/-- the global facts the node theorem uses -/
structure RunCx (K : SC) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64) : Prop where
  ig : IGOK K.hb E0 IG
  e62 : E0 < 2 ^ 62
  cb : ∀ s, IG s → s.b + s.w * C.length < 2 ^ 64
  p20 : K.p < 2 ^ 20
  inp : InpOK IG c28 K.c29 K.inp
  defs : ∀ id, id < K.nd → DefX C (K.T id) (K.npwOf id) (K.nresOf id) IG K.hb E0 (K.fs id)

theorem RunCx.hI {K C IG E0 c28} (h : RunCx K C IG E0 c28) : InvOKH K.hb K.p (IGp IG E0 K.p) := invOKH_IGp h.ig K.p

theorem RunCx.inpP {K C IG E0 c28} (h : RunCx K C IG E0 c28) : InpOK (IGp IG E0 K.p) c28 K.c29 K.inp :=
  fun s hs => h.inp s hs.1

theorem At.mid {C : List J} {h : Nat} {l1 l2 l3 : List J} (hC : At C h (l1 ++ l2 ++ l3)) :
    At C h l1 ∧ At C (h + l1.length) l2 ∧ At C (h + l1.length + l2.length) l3 := by
  refine ⟨hC.left.left, hC.left.right, ?_⟩
  have := hC.right; simpa [Nat.add_assoc] using this

theorem At.cast {C : List J} {a b : Nat} {l : List J} (h : At C a l) (e : a = b) : At C b l := e ▸ h

theorem At.one {C : List J} {a : Nat} {x : J} (h : At C a [x]) : C[a]? = some x := by
  have := h 0 (by simp); simpa using this

section run
variable {K : SC} {C : List J} {IG : St → Prop} {E0 : Nat} {c28 : UInt64}

mutual
theorem runV (X : RunCx K C IG E0 c28) : ∀ (e : Nd) (h : Nat), OkV K e → At C h (tm K e h) →
    EVHw C h (lnV K e) K.p K.nl (IGp IG E0 K.p) K.hb (rd e) (wr K.p e) (wd K e) (sv K e)
  | .const v, h, _, hC => by
    simp only [tm, lnV, rd, wr, wd, sv] at hC ⊢; exact constX X.hI hC
  | .loc s w, h, hok, hC => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV] at hok hC ⊢; exact localX X.hI X.p20 w s h hok hC
  | .bin op a b, h, hok, hC => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV] at hok hC ⊢
    obtain ⟨oa, ob, wa, wb, sc⟩ := hok
    obtain ⟨ca, cb, cu⟩ := At.mid hC
    rw [tm_len] at cb cu; rw [tm_len] at cu
    have hA := (runV X a h oa ca).wid wa
    have hB := (runV X b _ ob cb).wid wb
    have hP := (pairX hA hB sc).wid (show 1 + 1 = 2 from rfl)
    exact fin2X X.hI hP (fin2_alu (by rwa [← Nat.add_assoc]))
  | .ite c a b t e, h, hok, hC => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV] at hok hC ⊢
    obtain ⟨oa, ob, ot, oe, wa, wb, we, sb, st', se⟩ := hok
    have cA := hC.left.left.left.left.left
    have cB := hC.left.left.left.left.right
    have cH := hC.left.left.left.right
    have cT := hC.left.left.right
    have cJ := At.one hC.left.right
    have cE := hC.right
    simp only [List.length_append, tm_len, ifHeadG, List.length_cons, List.length_nil] at cB cH cT cJ cE
    have hA := (runV X a h oa cA).wid wa
    have hB := (runV X b _ ob cB).wid wb
    have hP := (pairX hA hB sb).wid (show 1 + 1 = 2 from rfl)
    have hT := runV X t _ ot (At.cast cT (show _ = h + lnV K a + lnV K b + 5 by omega))
    have hE := (runV X e _ oe (At.cast cE (show _ = h + lnV K a + lnV K b + 6 + lnV K t by omega))).wid we
    rw [show h + lnV K a + lnV K b + 5 = h + (lnV K a + lnV K b) + 5 by omega] at hT
    rw [show h + lnV K a + lnV K b + 6 + lnV K t = h + (lnV K a + lnV K b) + 6 + lnV K t by omega] at hE
    exact ifX X.hI hP (At.cast cH (by omega)) hT (by rw [← cJ]; congr 1; omega) hE st' se
  | .letE s w v b, h, hok, hC => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV] at hok hC ⊢
    obtain ⟨ov, ob, wv, hk0, sc⟩ := hok
    obtain ⟨cv, cs, cb⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cb
    have hv := (runV X v h ov cv).wid wv
    have hb := runV X b _ ob cb
    exact letX X.hI hv cs hb hk0 sc
  | .pair cs, h, hok, hC => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV] at hok hC ⊢; exact runL X cs h hok hC
  | .call id as, h, hok, hC => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV] at hok hC ⊢
    obtain ⟨oa, hid, wa⟩ := hok
    have hA := (runL X as h oa hC.left).wid wa
    have hj := At.one hC.right
    rw [tmL_len] at hj
    have hlt : h + lnL K as < C.length := by
      rcases Nat.lt_or_ge (h + lnL K as) C.length with q | q
      · exact q
      · rw [List.getElem?_eq_none q] at hj; simp at hj
    exact callX X.ig hA hj (by omega) (X.defs id hid) X.e62
      (fun s hs => by
        have := X.cb s hs; have := Nat.mul_le_mul_left s.w (show h + lnL K as + 1 ≤ C.length by omega); omega)
  | .prim pn as, h, hok, hC => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV] at hok hC ⊢
    obtain ⟨oa, wa, h0⟩ := hok
    have hP := runL X as h oa hC.left
    have hU := hC.right
    rw [tmL_len] at hU
    unfold primT at hU; unfold primLen
    unfold arity at wa
    by_cases p13 : pn = 1 ∨ pn = 3
    · have := h0 (p13.elim Or.inl (fun q => Or.inr (Or.inl q))); subst this
      simp only [p13, if_true] at hU ⊢
      simp only [lnL, rdL, wrL]
      exact (lenX (R := fun _ => False) (W := fun _ => False) X.hI (fun s hs => (X.inpP s hs).2.1) (by simpa [lnL] using hU)).mono (fun _ q => q.elim) (fun _ q => q.elim)
    simp only [p13, if_false] at hU ⊢
    by_cases p5 : pn = 5
    · have := h0 (Or.inr (Or.inr p5)); subst this
      simp only [p5, if_true] at hU ⊢
      simp only [lnL, rdL, wrL]
      refine ((bnewX (R := fun _ => False) (W := fun _ => False) X.hI (by simpa [lnL] using hU)).mono (fun _ q => q.elim) (fun _ q => q.elim)).len ?_
      simp [bnewT_len]
    simp only [p5, if_false] at hU ⊢
    have n135 : ¬ (pn = 1 ∨ pn = 3 ∨ pn = 5) := by omega
    simp only [n135, if_false] at wa
    by_cases p26 : pn = 2 ∨ pn = 6
    · simp only [p26, if_true] at wa ⊢
      unfold primF1
      by_cases p2 : pn = 2
      · simp only [p2, if_true] at hU ⊢
        exact fin1X X.hI (hP.wid wa) (fin1_rd hU X.inpP)
      · have p6 : pn = 6 := by omega
        simp only [p6, if_true] at hU ⊢
        exact fin1X X.hI (hP.wid wa) (fin1_bsize hU)
    simp only [p26, if_false] at wa ⊢
    have n2 : pn ≠ 2 := by omega
    have n6 : pn ≠ 6 := by omega
    simp only [n2, n6, if_false] at hU ⊢
    by_cases p8 : pn = 8
    · simp only [p8, if_true] at wa hU ⊢
      exact fin3X X.hI (hP.wid wa) (fin3_bset hU)
    simp only [p8, if_false] at wa hU ⊢
    unfold primF2
    by_cases p7 : pn = 7
    · simp only [p7, if_true] at hU ⊢
      exact fin2X X.hI (hP.wid wa) (fin2_bget hU)
    · simp only [p7, if_false] at hU ⊢
      exact fin2X X.hI (hP.wid wa) (fin2_bpush hU)
  | .loop z s, h, hok, hC => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV] at hok hC ⊢
    obtain ⟨oz, os, hp, hpn, hWp, hsc⟩ := hok
    have cH := hC.left.left.left
    have cZ := hC.left.left.right
    have cD := hC.left.right
    have cS := hC.right
    simp only [List.length_append, tmT_len, loopHead, loopDec, List.length_cons, List.length_nil] at cZ cD cS
    have hZ := runT X z _ _ _ _ oz (At.cast cZ (show _ = h + 3 by omega))
    have hS := runT X s _ _ _ _ os (At.cast cS (show _ = h + 3 + lnT K z + 2 by omega))
    exact (loopX X.hI cH (At.cast cD (by omega)) hZ hS hp hpn hWp hsc).mono (fun _ q => q)
      (fun k q => by rcases q with q | q | q <;> simp_all)
  | .cont _, _, hok, _ => by simp only [OkV] at hok
termination_by e => 2 * sizeOf e
theorem runT (X : RunCx K C IG E0 c28) : ∀ (e : Nd) (h Xt Hd w : Nat), OkT K e w → At C h (tmT K e h Xt Hd) →
    EVHt C h K.p K.nl (IGp IG E0 K.p) K.hb (rd e) (wr K.p e) w Xt Hd (st K e)
  | .ite c a b t e, h, Xt, Hd, w, hok, hC => by
    simp only [tmT, rd, wr, st, OkT] at hok hC ⊢
    obtain ⟨oa, ob, ot, oe, wa, wb, sb, st', se⟩ := hok
    have cA := hC.left.left.left.left.left
    have cB := hC.left.left.left.left.right
    have cH := hC.left.left.left.right
    have cT := hC.left.left.right
    have cE := hC.right
    simp only [List.length_append, tm_len, tmT_len, ifHeadG, List.length_cons, List.length_nil] at cB cH cT cE
    have hA := (runV X a h oa cA).wid wa
    have hB := (runV X b _ ob cB).wid wb
    have hP := (pairX hA hB sb).wid (show 1 + 1 = 2 from rfl)
    have hT := runT X t _ Xt Hd w ot (At.cast cT (show _ = h + lnV K a + lnV K b + 5 by omega))
    have hE := runT X e _ Xt Hd w oe (At.cast cE (show _ = h + lnV K a + lnV K b + 6 + lnT K t by omega))
    rw [show h + lnV K a + lnV K b + 5 = h + (lnV K a + lnV K b) + 5 by omega] at hT
    rw [show h + lnV K a + lnV K b + 6 + lnT K t = h + (lnV K a + lnV K b) + 6 + lnT K t by omega] at hE
    exact ifT X.hI hP (At.cast cH (by omega)) hT hE st' se
  | .letE s w' v b, h, Xt, Hd, w, hok, hC => by
    simp only [tmT, rd, wr, st, OkT] at hok hC ⊢
    obtain ⟨ov, ob, wv, hk0, sc⟩ := hok
    obtain ⟨cv, cs, cb⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cb
    exact letT X.hI ((runV X v h ov cv).wid wv) cs (runT X b _ Xt Hd w ob cb) hk0 sc
  | .cont e, h, Xt, Hd, w, hok, hC => by
    simp only [tmT, rd, wr, st, OkT] at hok hC ⊢
    obtain ⟨oe, we, hp, hpn⟩ := hok
    obtain ⟨ce, cs, cj⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cj
    exact contT X.hI ((runV X e h oe ce).wid we) cs (At.one cj) hp hpn
  | .const v, h, Xt, Hd, w, hok, hC => by
    simp only [tmT, rd, wr, st, OkT] at hok hC ⊢; exact valT ((runV X _ h hok.1 hC.left).wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj)
  | .loc s' w', h, Xt, Hd, w, hok, hC => by
    simp only [tmT, rd, wr, st, OkT] at hok hC ⊢; exact valT ((runV X _ h hok.1 hC.left).wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj)
  | .bin op a b, h, Xt, Hd, w, hok, hC => by
    simp only [tmT, st, OkT] at hok hC ⊢; exact valT ((runV X _ h hok.1 hC.left).wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj)
  | .pair cs, h, Xt, Hd, w, hok, hC => by
    simp only [tmT, st, OkT] at hok hC ⊢; exact valT ((runV X _ h hok.1 hC.left).wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj)
  | .call id as, h, Xt, Hd, w, hok, hC => by
    simp only [tmT, st, OkT] at hok hC ⊢; exact valT ((runV X _ h hok.1 hC.left).wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj)
  | .prim pn as, h, Xt, Hd, w, hok, hC => by
    simp only [tmT, st, OkT] at hok hC ⊢; exact valT ((runV X _ h hok.1 hC.left).wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj)
  | .loop z s, h, Xt, Hd, w, hok, hC => by
    simp only [tmT, st, OkT] at hok hC ⊢; exact valT ((runV X _ h hok.1 hC.left).wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj)
termination_by e => 2 * sizeOf e + 1
theorem runL (X : RunCx K C IG E0 c28) : ∀ (cs : List Nd) (h : Nat), OkL K cs → At C h (tmL K cs h) →
    EVHw C h (lnL K cs) K.p K.nl (IGp IG E0 K.p) K.hb (rdL cs) (wrL K.p cs) (wdL K cs) (svL K cs)
  | [], h, _, _ => by
    simp only [lnL, rdL, wrL, wdL, svL]; exact nilX.mono (fun _ h => h.elim) (fun _ h => h.elim)
  | c :: cs, h, hok, hC => by
    simp only [tmL, lnL, rdL, wrL, wdL, svL, OkL] at hok hC ⊢
    obtain ⟨oc, ocs, sc⟩ := hok
    have h1 := runV X c h oc hC.left
    have h2 := runL X cs (h + lnV K c) ocs (by have := hC.right; rwa [tm_len] at this)
    exact pairX h1 h2 sc
termination_by cs => 2 * sizeOf cs
end

end run

end Templates
