/- Nano/V2Self/Proof/Parser/ParRunExprMain: the expression refinement, assembled from per-family lemmas (box B). -/
import Nano.V2Self.Proof.Parser.ParRunExprInv
namespace ParRun
open ParSpec

/-- a primary (`prim md`, not at `if` / `let` unless md = 2) ↔ `pApp f cx (md == 1)` -/
def PrimSpec (n : Nat) : Prop := ∀ md ks st fin cx, StarN n (.prim md :: ks, st) ([], fin) → CxRel st cx → CxNN st →
  (md = 2 ∨ ((∀ r, st.toks ≠ .k 32 :: r) ∧ (∀ r, st.toks ≠ .k 2 :: r))) →
  ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ (v.toNd.tailCont = true → v.pend = true) ∧
      ∀ f, 4 * st.toks.length + 2 ≤ f → pApp f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx))

theorem prim_two_ifs {ks st fin n} (h : StarN n (.prim 2 :: ks, st) ([], fin)) :
    (∀ r, st.toks ≠ .k 32 :: r) ∧ (∀ r, st.toks ≠ .k 2 :: r) := by
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
    obtain ⟨k, st1, hs, _⟩ := h.head
    constructor <;> intro r hr <;> simp [stepF, hr] at hs

theorem bin_of {n : Nat} (hP : ∀ n' < n, PrimSpec n') (hL : ∀ n' < n, LoopSpec n') : BinSpec n := by
  classical
  intro m ks st fin cx h hc hnn
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  rw [expr_eq] at hs; simp at hs; obtain ⟨rfl, rfl⟩ := hs
  simp only [List.cons_append, List.nil_append] at h1
  obtain ⟨a, st1, n1, hn1, hp1, hlt1, h2, hna, hspa⟩ := hP n (by omega) 2 _ _ fin cx h1 hc hnn (Or.inl rfl)
  let ta : Ty := if hva : VT (rows st) a then Classical.choose (hspa hva) else .bot
  have hta : VT (rows st1) a → TyRel a ta ∧ PT a := fun hva => by
    have hr : rows st1 = rows st := by simp [rows, hp1.defs, hp1.cur]
    rw [hr] at hva
    simp only [ta, dif_pos hva]; exact ⟨(Classical.choose_spec (hspa hva)).1, (Classical.choose_spec (hspa hva)).2.1⟩
  obtain ⟨v, st', n', hn', hp, hsub, hrun, hstop, hnv, hspec⟩ :=
    hL n1 (by omega) m ks st1 fin cx a st.vals ta h2 hp1.vals (CxRel.transport hc hp1.binds hp1.defs hp1.cur hp1.arm)
      (CxNN.transport hnn hp1.binds hp1.defs hp1.cur) hna hta
  have hr : rows st1 = rows st := by simp [rows, hp1.defs, hp1.cur]
  refine ⟨v, st', n', by omega, ⟨hp.vals, by rw [hp.binds, hp1.binds], by rw [hp.defs, hp1.defs], by rw [hp.cur, hp1.cur],
    by rw [hp.arm, hp1.arm], by rw [hp.all, hp1.all], by have := hp.toks; omega, by have := hp.nx; have := hp1.nx; omega, by rw [hp.out, hp1.out]⟩,
    by have := hp.toks; omega, hrun, hstop, hnv, fun hvt => ?_⟩
  rw [hr] at hspec
  obtain ⟨ty, hty, hpt, hf⟩ := hspec hvt
  have hva : VT (rows st) a := fun u hu => hvt u (hsub u hu)
  refine ⟨ty, hty, hpt, fun f hf' => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hpa := (Classical.choose_spec (hspa hva)).2.2 g (by omega)
  simp only [show (2 == 1) = false from rfl] at hpa
  rw [pBin.eq_def]; simp only
  rw [hpa]; simp only [Option.bind_some]
  have := hf g (by omega)
  simp only [ta, dif_pos hva] at this
  exact this


/-- a full expression (`expr 0 md`, md < 2) ↔ `pExpr f cx (md == 1)` -/
def ExprSpec (n : Nat) : Prop := ∀ md ks st fin cx, md < 2 → StarN n (.expr 0 md :: ks, st) ([], fin) → CxRel st cx → CxNN st →
  ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ Stop 0 st'.toks ∧
    ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
      ∀ f, 4 * st.toks.length + 4 ≤ f → pExpr f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx))

theorem pExpr_other {f cx tl ts nx} (h32 : ∀ r, ts ≠ .k 32 :: r) (h2 : ∀ r, ts ≠ .k 2 :: r) :
    pExpr (f + 1) cx tl ts nx = pBin f cx tl 0 ts nx := by
  rw [pExpr.eq_def]; simp only
  split <;> first | exact (h2 _ rfl).elim | exact (h32 _ rfl).elim | rfl | simp_all

/-- `expr 0 md` at a token that is neither `if` nor `let`: the primary, then the operator loop at precedence 0 -/
theorem expr_other {n : Nat} (hP : ∀ n' < n, PrimSpec n') (hL : ∀ n' < n, LoopSpec n') {md ks st fin cx} (hmd : md < 2)
    (h : StarN n (.expr 0 md :: ks, st) ([], fin)) (hc : CxRel st cx) (hnn : CxNN st)
    (h32 : ∀ r, st.toks ≠ .k 32 :: r) (h2 : ∀ r, st.toks ≠ .k 2 :: r) :
    ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ Stop 0 st'.toks ∧
    ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
      ∀ f, 4 * st.toks.length + 4 ≤ f → pExpr f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx)) := by
  classical
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  rw [expr_eq] at hs; simp at hs; obtain ⟨rfl, rfl⟩ := hs
  simp only [List.cons_append, List.nil_append] at h1
  obtain ⟨a, st1, n1, hn1, hp1, hlt1, h2', hna, hspa⟩ := hP n (by omega) md _ _ fin cx h1 hc hnn (Or.inr ⟨h32, h2⟩)
  let ta : Ty := if hva : VT (rows st) a then Classical.choose (hspa hva) else .bot
  have hr : rows st1 = rows st := by simp [rows, hp1.defs, hp1.cur]
  have hta : VT (rows st1) a → TyRel a ta ∧ PT a := fun hva => by
    rw [hr] at hva
    simp only [ta, dif_pos hva]; exact ⟨(Classical.choose_spec (hspa hva)).1, (Classical.choose_spec (hspa hva)).2.1⟩
  -- the first step of the loop decides whether an operator follows
  obtain ⟨v, st', n', hn', hp, hsub, hrun, hstop, hnv, hspec⟩ :=
    hL n1 (by omega) 0 ks st1 fin cx a st.vals ta h2' hp1.vals (CxRel.transport hc hp1.binds hp1.defs hp1.cur hp1.arm)
      (CxNN.transport hnn hp1.binds hp1.defs hp1.cur) hna hta
  refine ⟨v, st', n', by omega, ⟨hp.vals, by rw [hp.binds, hp1.binds], by rw [hp.defs, hp1.defs], by rw [hp.cur, hp1.cur],
    by rw [hp.arm, hp1.arm], by rw [hp.all, hp1.all], by have := hp.toks; omega, by have := hp.nx; have := hp1.nx; omega, by rw [hp.out, hp1.out]⟩,
    by have := hp.toks; omega, hrun, hstop, hnv, fun hvt => ?_⟩
  rw [hr] at hspec
  obtain ⟨ty, hty, hpt, hf⟩ := hspec hvt
  have hva : VT (rows st) a := fun u hu => hvt u (hsub u hu)
  refine ⟨ty, hty, hpt, fun f hf' => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have hpa := (Classical.choose_spec (hspa hva)).2.2 g (by omega)
  have hloop := hf g (by omega)
  simp only [ta, dif_pos hva] at hloop
  rw [pExpr_other h32 h2, pBin.eq_def]; simp only
  rw [hpa]; simp only [Option.bind_some]
  -- with the tail flag on and an operator next, ParSpec re-parses the primary with the flag off
  split
  · rename_i t rest hmd1 hrt
    split
    · rename_i hop
      -- the loop's first step tested that `a` is not pending
      have hpend : a.pend = false := by
        match n1, h2' with
        | 0, h2' => exact absurd h2'.zero_nil.1 (by simp)
        | n1 + 1, h2' =>
          obtain ⟨k, st2, hs2, _⟩ := h2'.head
          rcases binLoop_inv hs2 with ⟨_, _, hlt⟩ | ⟨t', r', op, p, top, rest', ht', _, _, hv', hpend, _⟩
          · obtain ⟨opp, hop'⟩ := Option.isSome_iff_exists.mp hop
            exact absurd (hlt t rest opp.1 opp.2 hrt hop') (by omega)
          · rw [hp1.vals] at hv'; injection hv' with hv'; rw [hv']; exact hpend
      have htc : a.toNd.tailCont = false := by
        cases hc' : a.toNd.tailCont
        · rfl
        · have := (Classical.choose_spec (hspa hva)).2.1 hc'; rw [hpend] at this; cases this
      have hmd : md = 1 := by simpa using hmd1
      subst hmd
      have hpf := (tl_down g).2.2.1 _ _ _ _ hpa htc
      rw [hpf]; simp only [Option.bind_some]; exact hloop
    · exact hloop
  · exact hloop


/-- v209 on a bin / ite / let / loop / cont node: no input-local child -/
theorem nodeOK_noInp {ds : List DefR} {t a b : Nat} {sh : Option Sh} {p : Bool} {ks : List RN}
    (ht : t ≠ 6 ∧ t ≠ 8 ∧ t ≠ 9) (h : nodeOK ds (.mk t a b sh p ks) = true) : ∀ k ∈ ks, k.isInp = false := by
  intro k hk
  cases hki : k.isInp
  · rfl
  · exfalso
    have hm : (ks.filter RN.isInp).length ≠ 0 := by
      intro h0; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0; have := h0 k hk; simp [hki] at this
    simp only [nodeOK, RN.kids, RN.tag, Bool.and_eq_true] at h
    obtain ⟨h1, _⟩ := h
    simp only [hm, decide_false, if_false, ht.1, ht.2.1, ht.2.2, Bool.false_eq_true] at h1

theorem VT.self {ds : List DefR} {v : RN} (h : VT ds v) : nodeOK ds v = true := h v (self_mem_nodes v)

theorem iteNode_toNd {c : Nat} {sh : Option Sh} {p : Bool} {a b t e : RN}
    (ha : a.isInp = false) (hb : b.isInp = false) (ht : t.isInp = false) (he : e.isInp = false) :
    (RN.mk 4 c 0 sh p [a, b, t, e]).toNd = .ite c a.toNd b.toNd t.toNd e.toNd := by
  rw [RN.toNd_mk]; simp [RN.toNdL_cons, RN.toNdL, ha, hb, ht, he]

theorem bm_eq (tl : Bool) : (bm tl == 1) = tl := by cases tl <;> rfl

/-- the join of the branch types, when neither branch is the input and the branch shapes agree -/
theorem join_rel {t e : RN} {tt te : Ty} (htt : TyRel t tt) (hte : TyRel e te) (hti : tt ≠ .inp) (hei : te ≠ .inp)
    (hsh : t.sh = e.sh) {c : Nat} :
    ∃ ty, tt.join te = some ty ∧ TyRel (RN.mk 4 c 0 e.sh (t.pend || e.pend) [a, b, t, e]) ty := by
  cases tt with
  | inp => exact absurd rfl hti
  | bot =>
    refine ⟨te, by cases te <;> rfl, ?_⟩
    cases te with
    | s s => exact ⟨hte.1, by simp [RN.isInp, RN.tag], by simp [RN.tag]⟩
    | lit => exact ⟨hte.1, rfl⟩
    | inp => exact absurd rfl hei
    | bot => simp [TyRel, RN.pend]; exact Or.inr hte
  | lit =>
    cases te with
    | s s =>
      have hs : s = .uw := by rw [htt.1, hte.1] at hsh; cases hsh; rfl
      subst hs; exact ⟨.s .uw, rfl, hte.1, by simp [RN.isInp, RN.tag], by simp [RN.tag]⟩
    | lit => exact ⟨.lit, rfl, hte.1, rfl⟩
    | inp => exact absurd rfl hei
    | bot => exact ⟨.lit, rfl, by rw [← hsh]; exact htt.1, rfl⟩
  | s s =>
    cases te with
    | s s' =>
      have hs : s = s' := by rw [htt.1, hte.1] at hsh; cases hsh; rfl
      subst hs; exact ⟨.s s, by simp [Ty.join], hte.1, by simp [RN.isInp, RN.tag], by simp [RN.tag]⟩
    | lit =>
      have hs : s = .uw := by rw [htt.1, hte.1] at hsh; cases hsh; rfl
      subst hs; exact ⟨.s .uw, rfl, hte.1, by simp [RN.isInp, RN.tag], by simp [RN.tag]⟩
    | inp => exact absurd rfl hei
    | bot => exact ⟨.s s, by cases s <;> rfl, by rw [← hsh]; exact htt.1, by simp [RN.isInp, RN.tag], by simp [RN.tag]⟩


theorem binLoop_stop0 {ks st fin n} (h : StarN (n + 1) (.binLoop 0 :: ks, st) ([], fin)) (hs : Stop 0 st.toks) :
    StarN n (ks, st) ([], fin) := by
  obtain ⟨k, st1, hs1, h1⟩ := h.head
  rcases binLoop_inv hs1 with ⟨rfl, rfl, _⟩ | ⟨t, r, op, p, _, _, ht, hop, _⟩
  · exact h1
  · exact absurd (hs t r op p ht hop) (by omega)

theorem pExpr_if {f cx tl r nx} : pExpr (f + 1) cx tl (.k 32 :: r) nx =
    (pBin f cx false 0 r nx).bind fun (a, ta, r1, nx1) =>
      match isU ta, r1 with
      | true, .k c :: r2 =>
        if c = 23 ∨ c = 20 then
          (pBin f cx false 0 r2 nx1).bind fun (b, tb, r3, nx2) =>
            match isU tb, r3 with
            | true, .k 33 :: r4 =>
              (pExpr f cx tl r4 nx2).bind fun (t, tt, r5, nx3) =>
                match r5 with
                | .k 34 :: r6 =>
                  (pExpr f cx tl r6 nx3).bind fun (e, te, r7, nx4) =>
                    (tt.join te).map fun ty => (.ite (if c = 23 then 1 else 2) a b t e, ty, r7, nx4)
                | _ => none
            | _, _ => none
        else none
      | _, _ => none := by
  simp only [pExpr]; rfl


/-- `rows` only reads `defs` and `cur` -/
theorem Post.rowsEq {st st' : St} {b : List RN} {v : RN} (h : Post st st' b v) : ParRun.rows st' = ParRun.rows st := by
  unfold ParRun.rows; rw [h.defs, h.cur]

theorem expr_if {n : Nat} (hB : ∀ n' < n, BinSpec n') (hE : ∀ n' < n, ExprSpec n') {md ks st fin cx r} (hmd : md < 2)
    (h : StarN n (.expr 0 md :: ks, st) ([], fin)) (hc : CxRel st cx) (hnn : CxNN st) (ht : st.toks = .k 32 :: r) :
    ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ Stop 0 st'.toks ∧
    ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
      ∀ f, 4 * st.toks.length + 4 ≤ f → pExpr f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx)) := by
  classical
  -- expr 0 md, then the primary sees `if`
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  rw [expr_eq] at hs; simp at hs; obtain ⟨rfl, rfl⟩ := hs
  match n, h1 with
  | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
  | n + 1, h1 =>
  obtain ⟨k, st2, hs2, h2⟩ := h1.head
  have hpc := prim_inv hs2
  cases hpc with
  | ifs _ ht' =>
    rw [ht] at ht'; injection ht' with _ hr; subst hr
    simp only [List.cons_append, List.nil_append] at h2
    -- condition A
    obtain ⟨a, stA, nA, hnA, hpA, hltA, hA, _, _, hspA⟩ := hB n (by omega) 0 _ _ fin cx h2 (CxRel.transport hc rfl rfl rfl rfl)
      (CxNN.transport hnn rfl rfl rfl)
    match nA, hA with
    | 0, hA => exact absurd hA.zero_nil.1 (by simp)
    | nA + 1, hA =>
    obtain ⟨k3, stA', hs3, hA'⟩ := hA.head
    obtain ⟨c, r2, hcr, rfl, rfl⟩ := ifCmp_inv hs3
    simp only [List.cons_append, List.nil_append] at hA'
    -- condition B
    obtain ⟨b, stB, nB, hnB, hpB, hltB, hBr, _, _, hspB⟩ :=
      hB nA (by omega) 0 _ _ fin cx hA' (CxRel.transport hc (by simp [hpA.binds]) (by simp [hpA.defs]) (by simp [hpA.cur]) (by simp [hpA.arm]))
        (CxNN.transport hnn (by simp [hpA.binds]) (by simp [hpA.defs]) (by simp [hpA.cur]))
    match nB, hBr with
    | 0, hBr => exact absurd hBr.zero_nil.1 (by simp)
    | nB + 1, hBr =>
    obtain ⟨k4, stB', hs4, hB'⟩ := hBr.head
    obtain ⟨r4, hr4, rfl, rfl⟩ := ifThen_inv hs4
    simp only [List.cons_append, List.nil_append] at hB'
    -- then branch
    obtain ⟨t, stT, nT, hnT, hpT, hltT, hT, _, _, hspT⟩ :=
      hE nB (by omega) (bm (md == 1)) _ _ fin cx (by cases md == 1 <;> simp [bm]) hB'
        (CxRel.transport hc (by simp [hpB.binds, hpA.binds]) (by simp [hpB.defs, hpA.defs]) (by simp [hpB.cur, hpA.cur]) (by simp [hpB.arm, hpA.arm]))
        (CxNN.transport hnn (by simp [hpB.binds, hpA.binds]) (by simp [hpB.defs, hpA.defs]) (by simp [hpB.cur, hpA.cur]))
    match nT, hT with
    | 0, hT => exact absurd hT.zero_nil.1 (by simp)
    | nT + 1, hT =>
    obtain ⟨k5, stT', hs5, hT'⟩ := hT.head
    obtain ⟨r6, hr6, rfl, rfl⟩ := ifElse_inv hs5
    simp only [List.nil_append] at hT'
    -- else branch
    obtain ⟨e, stE, nE, hnE, hpE, hltE, hEr, hstopE, hnE', hspE⟩ :=
      hE nT (by omega) (bm (md == 1)) _ _ fin cx (by cases md == 1 <;> simp [bm]) hT'
        (CxRel.transport hc (by simp [hpT.binds, hpB.binds, hpA.binds]) (by simp [hpT.defs, hpB.defs, hpA.defs]) (by simp [hpT.cur, hpB.cur, hpA.cur]) (by simp [hpT.arm, hpB.arm, hpA.arm]))
        (CxNN.transport hnn (by simp [hpT.binds, hpB.binds, hpA.binds]) (by simp [hpT.defs, hpB.defs, hpA.defs])
          (by simp [hpT.cur, hpB.cur, hpA.cur]))
    match nE, hEr with
    | 0, hEr => exact absurd hEr.zero_nil.1 (by simp)
    | nE + 1, hEr =>
    obtain ⟨k6, stI, hs6, hI⟩ := hEr.head
    obtain ⟨e', t', b', a', rest, hv6, hau, hbu, htsh, rfl, hstI⟩ := mkIte_inv hs6
    rw [hpE.vals] at hv6; simp only at hv6
    rw [hpT.vals, hpB.vals, hpA.vals] at hv6
    simp only [List.cons.injEq] at hv6
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hv6
    simp only [List.nil_append] at hI
    -- the operator loop after the `if` stops at once (the else branch consumed all operators)
    match nE, hI with
    | 0, hI => exact absurd hI.zero_nil.1 (by simp)
    | nE + 1, hI =>
    have hI' := binLoop_stop0 hI (by rw [hstI]; exact hstopE)
    have hsI : stI.toks = stE.toks := by rw [hstI]
    have l1 : r2.length + 1 = stA.toks.length := by rcases hcr with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
    have l2 : r4.length + 1 = stB.toks.length := by simp [hr4]
    have l3 : r6.length + 1 = stT.toks.length := by simp [hr6]
    have l0 : st.toks.length = r.length + 1 := by simp [ht]
    simp only at hltA hltB hltT hltE
    refine ⟨_, stI, nE, by omega, ⟨by rw [hstI], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hstI]; simp [hpE.out, hpT.out, hpB.out, hpA.out]⟩, ?_, hI', by rw [hsI]; exact hstopE,
      by simpa [RN.sh] using hnE', fun hvt => ?_⟩
    · rw [hstI]; simp [hpE.binds, hpT.binds, hpB.binds, hpA.binds]
    · rw [hstI]; simp [hpE.defs, hpT.defs, hpB.defs, hpA.defs]
    · rw [hstI]; simp [hpE.cur, hpT.cur, hpB.cur, hpA.cur]
    · rw [hstI]; simp [hpE.arm, hpT.arm, hpB.arm, hpA.arm]
    · rw [hstI]; simp [hpE.all, hpT.all, hpB.all, hpA.all]
    · rw [hsI]; omega
    · rw [hstI]; have := hpE.nx; have := hpT.nx; have := hpB.nx; have := hpA.nx; simp at *; omega
    · rw [hsI]; omega
    -- the spec side
    have hok := hvt.self
    have hni := nodeOK_noInp (by decide) hok
    have hna := hni a (by simp); have hnb := hni b (by simp); have hnt := hni t (by simp); have hne := hni e (by simp)
    have key : ∀ x : St, x.defs = st.defs → x.cur = st.cur → rows x = rows st := fun x hd hcu => by
      unfold ParRun.rows; rw [hd, hcu]
    have dA := hpA.defs; have cA := hpA.cur; have dB := hpB.defs; have cB := hpB.cur
    have dT := hpT.defs; have cT := hpT.cur
    simp only at dA cA dB cB dT cT
    obtain ⟨ta, hta, _, hfA⟩ := hspA (by have := hvt.kid (k := a) (by simp); simpa [ParRun.rows] using this)
    obtain ⟨tb, htb, _, hfB⟩ := hspB (by have := hvt.kid (k := b) (by simp); simpa [ParRun.rows, dA, cA] using this)
    obtain ⟨tt, htt, hptt, hfT⟩ := hspT (by have := hvt.kid (k := t) (by simp); simpa [ParRun.rows, dB, cB, dA, cA] using this)
    obtain ⟨te, hte, hpte, hfE⟩ := hspE (by have := hvt.kid (k := e) (by simp); simpa [ParRun.rows, dT, cT, dB, cB, dA, cA] using this)
    have hti : tt ≠ .inp := by rintro rfl; rw [htt.1] at hnt; cases hnt
    have hei : te ≠ .inp := by rintro rfl; rw [hte.1] at hne; cases hne
    obtain ⟨ty, hjoin, hty⟩ := join_rel (a := a) (b := b) (c := c) htt hte hti hei htsh
    refine ⟨ty, hty, ?_, fun f hf => ?_⟩
    · intro hc'
      rw [iteNode_toNd hna hnb hnt hne] at hc'
      simp only [Nd.tailCont, Bool.or_eq_true] at hc'
      simp only [RN.pend, Bool.or_eq_true]
      rcases hc' with hc' | hc'
      · exact Or.inl (hptt hc')
      · exact Or.inr (hpte hc')
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have pA := hfA g (by simp; omega)
    have pB := hfB g (by simp; omega)
    have pT := hfT g (by simp; omega)
    have pE := hfE g (by simp; omega)
    rw [bm_eq] at pT pE
    simp only at pA pB pT pE
    have hnbA : ta ≠ .bot := (nobot g).2.1 _ _ _ _ _ pA
    have hnbB : tb ≠ .bot := (nobot g).2.1 _ _ _ _ _ pB
    have huA : isU ta = true := by
      cases ta with
      | s s => rw [hta.1] at hau; cases hau; rfl
      | lit => rfl
      | inp => rw [hta.2] at hau; cases hau
      | bot => exact absurd rfl hnbA
    have huB : isU tb = true := by
      cases tb with
      | s s => rw [htb.1] at hbu; cases hbu; rfl
      | lit => rfl
      | inp => rw [htb.2] at hbu; cases hbu
      | bot => exact absurd rfl hnbB
    rw [ht, pExpr_if, pA]; simp only [Option.bind_some, huA]
    rcases hcr with ⟨hcA, rfl⟩ | ⟨hcA, rfl⟩
    · rw [hcA]; simp only [show (23 = 23 ∨ 23 = 20) from Or.inl rfl, if_true]
      rw [pB]; simp only [Option.bind_some, huB, hr4]
      rw [pT]; simp only [Option.bind_some, hr6]
      rw [pE]; simp only [Option.bind_some, hjoin, Option.map_some, iteNode_toNd hna hnb hnt hne, hsI]
      simp [hstI]
    · rw [hcA]; simp only [show (20 = 23 ∨ 20 = 20) from Or.inr rfl, if_true]
      rw [pB]; simp only [Option.bind_some, huB, hr4]
      rw [pT]; simp only [Option.bind_some, hr6]
      rw [pE]; simp only [Option.bind_some, hjoin, Option.map_some, iteNode_toNd hna hnb hnt hne, hsI]
      simp [hstI]
  | lets _ ht' => rw [ht] at ht'; cases ht'
  | leaf hl _ => cases hl <;> simp_all
  | paren ht' => rw [ht] at ht'; cases ht'
  | self ht' => rw [ht] at ht'; cases ht'
  | call ht' => rw [ht] at ht'; cases ht'
  | primTok ht' h1 h2 => rw [ht] at ht'; injection ht' with ht'; injection ht' with ht'; omega


theorem findB_push (bs : List Bd) (bd : Bd) (y : List Nat) :
    findB (bs ++ [bd]) y = if bd.name == y then some bd else findB bs y := by
  unfold findB; simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.find?_cons]
  split <;> simp_all

theorem findEnv_cons (env : List (List Nat × Nat × Ps)) (x : List Nat) (slot : Nat) (p : Ps) (y : List Nat) :
    findEnv ((x, slot, p) :: env) y = if x == y then some (slot, p) else findEnv env y := by
  unfold findEnv; simp only [List.find?_cons]; split <;> simp_all

/-- a typed, non-input, non-Nat binding extends the context relation -/
theorem CxRel.push {st st' : St} {cx : Cx} {x : List Nat} {slot : Nat} {s : Sh} (hc : CxRel st cx) (hs : s ≠ .nt)
    (hb : st'.binds = st.binds ++ [⟨x, slot, some s, false⟩]) (hd : st'.defs = st.defs)
    (hcu : st'.cur = st.cur) (har : st'.arm = st.arm) :
    CxRel st' { cx with env := (x, slot, .sh s) :: cx.env } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  have hps : bdPs ⟨x, slot, some s, false⟩ = some (.sh s) := by
    unfold bdPs; cases s <;> simp_all
  refine ⟨?_, ?_, ?_, by rw [hd]; exact h4, by rw [hd]; exact h5, h6, by rw [hcu, har]; exact h7⟩
  · intro y bd hy; rw [hb, findB_push] at hy; split at hy
    · cases hy; rfl
    · exact h1 y bd hy
  · intro y bd hy hi; rw [hb, findB_push] at hy; split at hy
    · cases hy; cases hi
    · exact h2 y bd hy hi
  · intro y
    rw [hb, findB_push, findEnv_cons]
    by_cases hxy : x = y
    · subst hxy; simp [hps]
    · have : (x == y) = false := by simpa using hxy
      simp only [this, Bool.false_eq_true, if_false]; exact h3 y

theorem CxNN.push {st st' : St} {bd : Bd} (h : CxNN st) (hbd : ShNN bd.sh) (hb : st'.binds = st.binds ++ [bd])
    (hd : st'.defs = st.defs) (hcu : st'.cur = st.cur) : CxNN st' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun b hm => ?_, by unfold ParRun.rows at *; rw [hd, hcu]; exact h2⟩
  rw [hb] at hm; rcases List.mem_append.mp hm with hm | hm
  · exact h1 b hm
  · simp at hm; subst hm; exact hbd


theorem pExpr_let {f cx tl x r nx} : pExpr (f + 1) cx tl (.k 2 :: .id x :: .k 9 :: r) nx =
    (pExpr f cx false r nx).bind fun (v, tv, r1, nx1) =>
      match tyShape tv, r1 with
      | some s, .k 13 :: r2 =>
        (pExpr f { cx with env := (x, nx1, .sh s) :: cx.env } tl r2 (nx1 + s.width)).map fun (b, tb, r3, nx3) =>
          (.letE nx1 s.width v b, tb, r3, nx3)
      | _, _ => none := by
  simp only [pExpr]; rfl

theorem letNode_toNd {s w : Nat} {sh : Option Sh} {p : Bool} {v b : RN} (hv : v.isInp = false) (hb : b.isInp = false) :
    (RN.mk 5 s w sh p [v, b]).toNd = .letE s w v.toNd b.toNd := by
  rw [RN.toNd_mk]; simp [RN.toNdL_cons, RN.toNdL, hv, hb]

/-- the value of a `let` has a storable ParSpec shape equal to its machine shape -/
theorem let_shape {v : RN} {tv : Ty} {s : Sh} (hrel : TyRel v tv) (hsh : v.sh = some s) (hnn : s.nnt = true) (hnt : s ≠ .nt)
    (hb : tv ≠ .bot) (hi : tv ≠ .inp) : tyShape tv = some s := by
  cases tv with
  | s s' => rw [hrel.1] at hsh; cases hsh; simp [tyShape, Sh.hasN_of_nnt hnn hnt]
  | lit => rw [hrel.1] at hsh; cases hsh; rfl
  | inp => exact absurd rfl hi
  | bot => exact absurd rfl hb

theorem body_rel {t a w : Nat} {sh : Option Sh} {p : Bool} {kids : List RN} {b : RN} {tb : Ty}
    (hrel : TyRel b tb) (hsh : sh = b.sh) (hp : p = b.pend) (hi : tb ≠ .inp) (ht : t ≠ 1 ∧ t ≠ 2) :
    TyRel (RN.mk t a w sh p kids) tb := by
  subst hsh hp
  cases tb with
  | s s => exact ⟨hrel.1, by simp [RN.isInp, RN.tag, ht.2], by simp [RN.tag, ht.1]⟩
  | lit => exact ⟨hrel.1, by simp [RN.isInp, RN.tag, ht.2]⟩
  | inp => exact absurd rfl hi
  | bot => exact hrel


theorem expr_let {n : Nat} (hE : ∀ n' < n, ExprSpec n') {md ks st fin cx x r} (hmd : md < 2)
    (h : StarN n (.expr 0 md :: ks, st) ([], fin)) (hc : CxRel st cx) (hnn : CxNN st) (ht : st.toks = .k 2 :: .id x :: .k 9 :: r) :
    ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ Stop 0 st'.toks ∧
    ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
      ∀ f, 4 * st.toks.length + 4 ≤ f → pExpr f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx)) := by
  classical
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  rw [expr_eq] at hs; simp at hs; obtain ⟨rfl, rfl⟩ := hs
  match n, h1 with
  | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
  | n + 1, h1 =>
  obtain ⟨k, st2, hs2, h2⟩ := h1.head
  have hpc := prim_inv hs2
  cases hpc with
  | lets _ ht' =>
    rw [ht] at ht'; injection ht' with _ hr; subst hr
    simp only [List.cons_append, List.nil_append] at h2
    match n, h2 with
    | 0, h2 => exact absurd h2.zero_nil.1 (by simp)
    | n + 1, h2 =>
    obtain ⟨k3, st3, hs3, h3⟩ := h2.head
    rcases letStart_inv hs3 with ⟨x', r', hx, rfl, rfl⟩ | ⟨r', hx, _, _⟩
    · simp only at hx; injection hx with hx1 hx2; injection hx1 with hx1; subst hx1; injection hx2 with _ hx2; subst hx2
      simp only [List.cons_append, List.nil_append] at h3
      -- the value
      obtain ⟨v, stV, nV, hnV, hpV, hltV, hV, _, hnvV, hspV⟩ :=
        hE n (by omega) 0 _ _ fin cx (by omega) h3 (CxRel.transport hc rfl rfl rfl rfl) (CxNN.transport hnn rfl rfl rfl)
      match nV, hV with
      | 0, hV => exact absurd hV.zero_nil.1 (by simp)
      | nV + 1, hV =>
      obtain ⟨k4, st4, hs4, h4⟩ := hV.head
      obtain ⟨r2, v', rest, hr2, hv4, hnt, rfl, rfl⟩ := letSemi_inv hs4
      rw [hpV.vals] at hv4; injection hv4 with hv4 hrest; subst hv4 hrest
      simp only [List.cons_append, List.nil_append] at h4
      obtain ⟨s, hsv, hsnn⟩ := hnvV
      have hsnt : s ≠ .nt := by rintro rfl; exact hnt hsv
      -- the body, in the extended context
      have hcB : CxRel { stV with toks := r2, nx := stV.nx + cw v.sh, binds := stV.binds ++ [⟨x, stV.nx, v.sh, false⟩] }
          { cx with env := (x, stV.nx, .sh s) :: cx.env } :=
        CxRel.push (CxRel.transport (st' := stV) hc (by rw [hpV.binds]) (by rw [hpV.defs]) (by rw [hpV.cur]) (by rw [hpV.arm])) hsnt (by simp [hsv]) rfl rfl rfl
      have hnB : CxNN { stV with toks := r2, nx := stV.nx + cw v.sh, binds := stV.binds ++ [⟨x, stV.nx, v.sh, false⟩] } :=
        CxNN.push (CxNN.transport (st' := stV) hnn hpV.binds hpV.defs hpV.cur) ⟨s, hsv, hsnn⟩ rfl rfl rfl
      obtain ⟨b, stB, nB, hnB', hpB, hltB, hB, hstopB, hnvB, hspB⟩ :=
        hE nV (by omega) (bm (md == 1)) _ _ fin _ (by cases md == 1 <;> simp [bm]) h4 hcB hnB
      match nB, hB with
      | 0, hB => exact absurd hB.zero_nil.1 (by simp)
      | nB + 1, hB =>
      obtain ⟨k5, stL, hs5, hL⟩ := hB.head
      obtain ⟨body, v'', rest, hv5, rfl, hstL⟩ := letEnd_inv hs5
      rw [hpB.vals] at hv5; simp only [List.cons.injEq] at hv5; obtain ⟨rfl, hv5⟩ := hv5
      rw [hpV.vals] at hv5; simp only [List.cons.injEq] at hv5; obtain ⟨rfl, rfl⟩ := hv5
      simp only [List.nil_append] at hL
      match nB, hL with
      | 0, hL => exact absurd hL.zero_nil.1 (by simp)
      | nB + 1, hL =>
      have hL' := binLoop_stop0 hL (by rw [hstL]; exact hstopB)
      have hsL : stL.toks = stB.toks := by rw [hstL]
      have l0 : st.toks.length = r.length + 3 := by simp [ht]
      have l1 : r2.length + 1 = stV.toks.length := by simp [hr2]
      simp only at hltV hltB
      have hbB := hpB.binds; simp only at hbB
      refine ⟨_, stL, nB, by omega, ⟨by rw [hstL], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hstL]; simp [hpB.out, hpV.out]⟩, by rw [hsL]; omega, hL', by rw [hsL]; exact hstopB,
        by simpa [RN.sh] using hnvB, fun hvt => ?_⟩
      · rw [hstL]; simp only; rw [hbB, hpV.binds]; simp
      · rw [hstL]; simp [hpB.defs, hpV.defs]
      · rw [hstL]; simp [hpB.cur, hpV.cur]
      · rw [hstL]; simp [hpB.arm, hpV.arm]
      · rw [hstL]; simp [hpB.all, hpV.all]
      · rw [hsL]; omega
      · rw [hstL]; have := hpB.nx; have := hpV.nx; simp at *; omega
      -- the spec side
      have hok := hvt.self
      have hni := nodeOK_noInp (by decide) hok
      have hnv := hni v (by simp); have hnb := hni b (by simp)
      have dV := hpV.defs; have cV := hpV.cur; have dB := hpB.defs; have cB := hpB.cur
      simp only at dV cV dB cB
      obtain ⟨tv, htv, _, hfV⟩ := hspV (by have := hvt.kid (k := v) (by simp); simpa [ParRun.rows] using this)
      obtain ⟨tb, htb, hptb, hfB⟩ := hspB (by have := hvt.kid (k := b) (by simp); simpa [ParRun.rows, dV, cV] using this)
      have hbi : tb ≠ .inp := by rintro rfl; rw [htb.1] at hnb; cases hnb
      refine ⟨tb, body_rel htb rfl rfl hbi (by decide), ?_, fun f hf => ?_⟩
      · intro hc'; rw [letNode_toNd hnv hnb] at hc'; simp only [Nd.tailCont] at hc'; exact hptb hc'
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have pV := hfV g (by simp; omega)
      have pB := hfB g (by simp; omega)
      rw [bm_eq] at pB
      simp only [show (0 == 1) = false from rfl] at pV pB
      have hvb : tv ≠ .bot := (nobot g).1 _ _ _ _ pV
      have hvi : tv ≠ .inp := by rintro rfl; rw [htv.1] at hnv; cases hnv
      have hshape := let_shape htv hsv hsnn hsnt hvb hvi
      rw [ht, pExpr_let, pV]; simp only [Option.bind_some, hshape, hr2]
      rw [hsv] at pB; simp only [cw] at pB
      rw [pB]; simp only [Option.map_some, letNode_toNd hnv hnb, hsL, hsv, cw]
      simp [hstL]
    · simp at hx
  | ifs _ ht' => rw [ht] at ht'; cases ht'
  | leaf hl _ => cases hl <;> simp_all
  | paren ht' => rw [ht] at ht'; cases ht'
  | self ht' => rw [ht] at ht'; cases ht'
  | call ht' => rw [ht] at ht'; cases ht'
  | primTok ht' h1 h2 => rw [ht] at ht'; injection ht' with ht'; injection ht' with ht'; omega


theorem pExpr_letpair {f cx tl x y r nx} :
    pExpr (f + 1) cx tl (.k 2 :: .k 6 :: .id x :: .k 15 :: .id y :: .k 7 :: .k 9 :: r) nx =
    (pExpr f cx false r nx).bind fun (v, tv, r1, nx1) =>
      match tyShape tv, r1 with
      | some (.p l rr), .k 13 :: r2 =>
        (pExpr f { cx with env := (y, nx1 + l.width, .sh rr) :: (x, nx1, .sh l) :: cx.env } tl r2 (nx1 + l.width + rr.width)).map
          fun (b, tb, r3, nx3) => (.letE nx1 (l.width + rr.width) v b, tb, r3, nx3)
      | _, _ => none := by
  simp only [pExpr]; rfl

theorem expr_letpair {n : Nat} (hE : ∀ n' < n, ExprSpec n') {md ks st fin cx x y r} (hmd : md < 2)
    (h : StarN n (.expr 0 md :: ks, st) ([], fin)) (hc : CxRel st cx) (hnn : CxNN st)
    (ht : st.toks = .k 2 :: .k 6 :: .id x :: .k 15 :: .id y :: .k 7 :: .k 9 :: r) :
    ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ Stop 0 st'.toks ∧
    ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
      ∀ f, 4 * st.toks.length + 4 ≤ f → pExpr f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx)) := by
  classical
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  rw [expr_eq] at hs; simp at hs; obtain ⟨rfl, rfl⟩ := hs
  match n, h1 with
  | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
  | n + 1, h1 =>
  obtain ⟨k, st2, hs2, h2⟩ := h1.head
  have hpc := prim_inv hs2
  cases hpc with
  | lets _ ht' =>
    rw [ht] at ht'; injection ht' with _ hr; subst hr
    simp only [List.cons_append, List.nil_append] at h2
    match n, h2 with
    | 0, h2 => exact absurd h2.zero_nil.1 (by simp)
    | n + 1, h2 =>
    obtain ⟨k3, st3, hs3, h3⟩ := h2.head
    rcases letStart_inv hs3 with ⟨x', r', hx, _, _⟩ | ⟨r', hx, rfl, rfl⟩
    · simp at hx
    simp only at hx; injection hx with _ hx; subst hx
    simp only [List.cons_append, List.nil_append] at h3
    match n, h3 with
    | 0, h3 => exact absurd h3.zero_nil.1 (by simp)
    | n + 1, h3 =>
    obtain ⟨k4, st4, hs4, h4⟩ := h3.head
    obtain ⟨x', r4, hx4, rfl, rfl⟩ := letPairX_inv hs4
    simp only [List.cons.injEq, Tok.id.injEq, true_and] at hx4; obtain ⟨rfl, rfl⟩ := hx4
    simp only [List.cons_append, List.nil_append] at h4
    match n, h4 with
    | 0, h4 => exact absurd h4.zero_nil.1 (by simp)
    | n + 1, h4 =>
    obtain ⟨k5, st5, hs5, h5⟩ := h4.head
    obtain ⟨y', r5, hy5, rfl, rfl⟩ := letPairY_inv hs5
    simp only [List.cons.injEq, Tok.id.injEq, true_and] at hy5; obtain ⟨rfl, rfl⟩ := hy5
    simp only [List.cons_append, List.nil_append] at h5
    -- the value
    obtain ⟨v, stV, nV, hnV, hpV, hltV, hV, _, hnvV, hspV⟩ :=
      hE n (by omega) 0 _ _ fin cx (by omega) h5 (CxRel.transport hc rfl rfl rfl rfl) (CxNN.transport hnn rfl rfl rfl)
    match nV, hV with
    | 0, hV => exact absurd hV.zero_nil.1 (by simp)
    | nV + 1, hV =>
    obtain ⟨k6, st6, hs6, h6⟩ := hV.head
    rw [stash_eq] at hs6; simp at hs6; obtain ⟨rfl, rfl⟩ := hs6
    simp only [List.nil_append] at h6
    match nV, h6 with
    | 0, h6 => exact absurd h6.zero_nil.1 (by simp)
    | nV + 1, h6 =>
    obtain ⟨k7, st7, hs7, h7⟩ := h6.head
    obtain ⟨r2, v', rest, l, rr, x', hr2, hv7, hx', hsv, rfl, rfl⟩ := letPairSemi_inv hs7
    simp only [Option.some.injEq] at hv7 hr2 hx'; subst hx'
    rw [hpV.vals] at hv7; injection hv7 with hv7 hrest; subst hv7 hrest
    simp only [List.cons_append, List.nil_append] at h7
    obtain ⟨s, hsv', hsnn⟩ := hnvV
    rw [hsv] at hsv'; cases hsv'
    simp only [Sh.nnt, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsnn
    obtain ⟨⟨⟨hl, hrr⟩, hlnn⟩, hrnn⟩ := hsnn
    -- the body, in the context extended by both components
    have hc1 : CxRel { stV with binds := stV.binds ++ [⟨x, stV.nx, some l, false⟩] } { cx with env := (x, stV.nx, .sh l) :: cx.env } :=
      CxRel.push (CxRel.transport (st' := stV) hc (by rw [hpV.binds]) (by rw [hpV.defs]) (by rw [hpV.cur]) (by rw [hpV.arm])) hl rfl rfl rfl rfl
    have hcB := CxRel.push (x := y) (slot := stV.nx + l.width) hc1 hrr
      (st' := { stV with toks := r2, nx := stV.nx + cw v.sh, stash := some x, binds := stV.binds ++ [⟨x, stV.nx, some l, false⟩, ⟨y, stV.nx + l.width, some rr, false⟩] }) (by simp) rfl rfl rfl
    have hn1 : CxNN { stV with binds := stV.binds ++ [⟨x, stV.nx, some l, false⟩] } :=
      CxNN.push (CxNN.transport (st' := stV) hnn hpV.binds hpV.defs hpV.cur) ⟨l, rfl, hlnn⟩ rfl rfl rfl
    have hnB := CxNN.push (bd := ⟨y, stV.nx + l.width, some rr, false⟩) hn1 ⟨rr, rfl, hrnn⟩
      (st' := { stV with toks := r2, nx := stV.nx + cw v.sh, stash := some x, binds := stV.binds ++ [⟨x, stV.nx, some l, false⟩, ⟨y, stV.nx + l.width, some rr, false⟩] }) (by simp) rfl rfl
    obtain ⟨b, stB, nB, hnB', hpB, hltB, hB, hstopB, hnvB, hspB⟩ :=
      hE nV (by omega) (bm (md == 1)) _ _ fin _ (by cases md == 1 <;> simp [bm]) h7 hcB hnB
    match nB, hB with
    | 0, hB => exact absurd hB.zero_nil.1 (by simp)
    | nB + 1, hB =>
    obtain ⟨k8, stL, hs8, hL⟩ := hB.head
    obtain ⟨body, v'', rest, hv8, rfl, hstL⟩ := letEnd_inv hs8
    rw [hpB.vals] at hv8; simp only [List.cons.injEq] at hv8; obtain ⟨rfl, hv8⟩ := hv8
    rw [hpV.vals] at hv8; simp only [List.cons.injEq] at hv8; obtain ⟨rfl, rfl⟩ := hv8
    simp only [List.nil_append] at hL
    match nB, hL with
    | 0, hL => exact absurd hL.zero_nil.1 (by simp)
    | nB + 1, hL =>
    have hL' := binLoop_stop0 hL (by rw [hstL]; exact hstopB)
    have hsL : stL.toks = stB.toks := by rw [hstL]
    have l0 : st.toks.length = r.length + 7 := by simp [ht]
    have l1 : r2.length + 1 = stV.toks.length := by simp [hr2]
    simp only at hltV hltB
    have hbB := hpB.binds; simp only at hbB
    refine ⟨_, stL, nB, by omega, ⟨by rw [hstL], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hstL]; simp [hpB.out, hpV.out]⟩, by rw [hsL]; omega, hL', by rw [hsL]; exact hstopB,
      by simpa [RN.sh] using hnvB, fun hvt => ?_⟩
    · rw [hstL]; simp only; rw [hbB, hpV.binds]; simp
    · rw [hstL]; simp [hpB.defs, hpV.defs]
    · rw [hstL]; simp [hpB.cur, hpV.cur]
    · rw [hstL]; simp [hpB.arm, hpV.arm]
    · rw [hstL]; simp [hpB.all, hpV.all]
    · rw [hsL]; omega
    · rw [hstL]; have := hpB.nx; have := hpV.nx; simp at *; omega
    have hok := hvt.self
    have hni := nodeOK_noInp (by decide) hok
    have hnv := hni v (by simp); have hnb := hni b (by simp)
    have dV := hpV.defs; have cV := hpV.cur
    simp only at dV cV
    obtain ⟨tv, htv, _, hfV⟩ := hspV (by have := hvt.kid (k := v) (by simp); simpa [ParRun.rows] using this)
    obtain ⟨tb, htb, hptb, hfB⟩ := hspB (by have := hvt.kid (k := b) (by simp); simpa [ParRun.rows, dV, cV] using this)
    have hbi : tb ≠ .inp := by rintro rfl; rw [htb.1] at hnb; cases hnb
    refine ⟨tb, body_rel htb rfl rfl hbi (by decide), ?_, fun f hf => ?_⟩
    · intro hc'; rw [letNode_toNd hnv hnb] at hc'; simp only [Nd.tailCont] at hc'; exact hptb hc'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have pV := hfV g (by simp; omega)
    have pB := hfB g (by simp; omega)
    rw [bm_eq] at pB
    simp only [show (0 == 1) = false from rfl] at pV pB
    have hvb : tv ≠ .bot := (nobot g).1 _ _ _ _ pV
    have hvi : tv ≠ .inp := by rintro rfl; rw [htv.1] at hnv; cases hnv
    have hnnt : (Sh.p l rr).nnt = true := by simp [Sh.nnt, hl, hrr, hlnn, hrnn]
    have hshape := let_shape htv hsv hnnt (by simp) hvb hvi
    rw [ht, pExpr_letpair, pV]; simp only [Option.bind_some, hshape, hr2]
    rw [hsv] at pB; simp only [cw, Sh.width, Nat.add_assoc] at pB
    simp only [Nat.add_assoc]
    rw [pB]; simp only [Option.map_some, letNode_toNd hnv hnb, hsL, hsv, cw, Sh.width]
    simp [hstL, Nat.add_assoc]
  | ifs _ ht' => rw [ht] at ht'; cases ht'
  | leaf hl _ => cases hl <;> simp_all
  | paren ht' => rw [ht] at ht'; cases ht'
  | self ht' => rw [ht] at ht'; cases ht'
  | call ht' => rw [ht] at ht'; cases ht'
  | primTok ht' h1 h2 => rw [ht] at ht'; injection ht' with ht'; injection ht' with ht'; omega


/-- a run through `let` reaches one of the two let forms -/
theorem let_forms {n md ks st fin r} (h : StarN n (.expr 0 md :: ks, st) ([], fin)) (ht : st.toks = .k 2 :: r) :
    (∃ x r', r = .id x :: .k 9 :: r') ∨ (∃ x y r', r = .k 6 :: .id x :: .k 15 :: .id y :: .k 7 :: .k 9 :: r') := by
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  rw [expr_eq] at hs; simp at hs; obtain ⟨rfl, rfl⟩ := hs
  match n, h1 with
  | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
  | n + 1, h1 =>
  obtain ⟨k, st2, hs2, h2⟩ := h1.head
  cases prim_inv hs2 with
  | lets _ ht' =>
    rw [ht] at ht'; injection ht' with _ hr; subst hr
    match n, h2 with
    | 0, h2 => exact absurd h2.zero_nil.1 (by simp)
    | n + 1, h2 =>
    obtain ⟨k3, st3, hs3, h3⟩ := h2.head
    rcases letStart_inv hs3 with ⟨x, r', hx, _, _⟩ | ⟨r', hx, rfl, rfl⟩
    · exact Or.inl ⟨x, r', hx⟩
    simp only [List.cons_append, List.nil_append] at h3
    match n, h3 with
    | 0, h3 => exact absurd h3.zero_nil.1 (by simp)
    | n + 1, h3 =>
    obtain ⟨k4, st4, hs4, h4⟩ := h3.head
    obtain ⟨x, r4, hx4, rfl, rfl⟩ := letPairX_inv hs4
    simp only [List.cons_append, List.nil_append] at h4
    match n, h4 with
    | 0, h4 => exact absurd h4.zero_nil.1 (by simp)
    | n + 1, h4 =>
    obtain ⟨k5, st5, hs5, _⟩ := h4.head
    obtain ⟨y, r5, hy5, _, _⟩ := letPairY_inv hs5
    simp only at hx hx4 hy5
    exact Or.inr ⟨x, y, r5, by rw [hx, hx4, hy5]⟩
  | ifs _ ht' => rw [ht] at ht'; cases ht'
  | leaf hl _ => cases hl <;> simp_all
  | paren ht' => rw [ht] at ht'; cases ht'
  | self ht' => rw [ht] at ht'; cases ht'
  | call ht' => rw [ht] at ht'; cases ht'
  | primTok ht' h1 h2 => rw [ht] at ht'; injection ht' with ht'; injection ht' with ht'; omega

theorem expr_sound {n : Nat} (hB : ∀ n' < n, BinSpec n') (hE : ∀ n' < n, ExprSpec n') (hP : ∀ n' < n, PrimSpec n')
    (hL : ∀ n' < n, LoopSpec n') : ExprSpec n := by
  intro md ks st fin cx hmd h hc hnn
  by_cases h32 : ∃ r, st.toks = .k 32 :: r
  · obtain ⟨r, ht⟩ := h32; exact expr_if hB hE hmd h hc hnn ht
  by_cases h2 : ∃ r, st.toks = .k 2 :: r
  · obtain ⟨r, ht⟩ := h2
    rcases let_forms h ht with ⟨x, r', rfl⟩ | ⟨x, y, r', rfl⟩
    · exact expr_let hE hmd h hc hnn ht
    · exact expr_letpair hE hmd h hc hnn ht
  exact expr_other hP hL hmd h hc hnn (fun r h' => h32 ⟨r, h'⟩) (fun r h' => h2 ⟨r, h'⟩)

end ParRun
