/- nano stage 2, layer A: the simulation lemmas (one per parse function, by induction on the fuel). -/
import Nano.ParseBProof

namespace Nano.PB
open Nano Nano.U

/-- what a parse result means for the machine -/
def Out (o : Option (Ex × List Tok)) (ok : Ex → List Tok → Prop) (bad : Prop) : Prop :=
  match o with
  | some (e, r) => ok e r
  | none => bad

def PE (f : Nat) : Prop := ∀ (ts : List Tok) out d scN scD mds K cg cf na, scN.length = scD.length →
  Out (pExpr f scN (dsOf mds) ts)
    (fun e r => Reach (.expr f) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩
      .ret ⟨r, out ++ serUE scD d e, d + 1, scN.zip scD, mds, K, cg, cf, na⟩)
    (Fails (.expr f) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩)

def PM (f : Nat) : Prop := ∀ (ts : List Tok) out d scN scD mds K cg cf na, scN.length = scD.length →
  Out (pMul f scN (dsOf mds) ts)
    (fun e r => Reach (.mul f) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩
      .ret ⟨r, out ++ serUE scD d e, d + 1, scN.zip scD, mds, K, cg, cf, na⟩)
    (Fails (.mul f) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩)

def PP (f : Nat) : Prop := ∀ (ts : List Tok) out d scN scD mds K cg cf na, scN.length = scD.length →
  Out (pApp f scN (dsOf mds) ts)
    (fun e r => Reach (.app f) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩
      .ret ⟨r, out ++ serUE scD d e, d + 1, scN.zip scD, mds, K, cg, cf, na⟩)
    (Fails (.app f) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩)

def PO (f : Nat) : Prop := ∀ (ts : List Tok) out d scN scD mds K cg cf na, scN.length = scD.length →
  Out (pAtom f scN (dsOf mds) ts)
    (fun e r => Reach (.atom f) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩
      .ret ⟨r, out ++ serUE scD d e, d + 1, scN.zip scD, mds, K, cg, cf, na⟩)
    (Fails (.atom f) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩)

/-- `acc` (at depth `d`) already emitted after `o` -/
def PA (f : Nat) : Prop := ∀ (ts : List Tok) o acc d scN scD mds K cg cf na, scN.length = scD.length →
  Out (pAdd f scN (dsOf mds) acc ts)
    (fun e r => Reach (.add f) ⟨ts, o ++ serUE scD d acc, d + 1, scN.zip scD, mds, K, cg, cf, na⟩
      .ret ⟨r, o ++ serUE scD d e, d + 1, scN.zip scD, mds, K, cg, cf, na⟩)
    (Fails (.add f) ⟨ts, o ++ serUE scD d acc, d + 1, scN.zip scD, mds, K, cg, cf, na⟩)

def PT (f : Nat) : Prop := ∀ (ts : List Tok) o acc d scN scD mds K cg cf na, scN.length = scD.length →
  Out (pMulT f scN (dsOf mds) acc ts)
    (fun e r => Reach (.mulT f) ⟨ts, o ++ serUE scD d acc, d + 1, scN.zip scD, mds, K, cg, cf, na⟩
      .ret ⟨r, o ++ serUE scD d e, d + 1, scN.zip scD, mds, K, cg, cf, na⟩)
    (Fails (.mulT f) ⟨ts, o ++ serUE scD d acc, d + 1, scN.zip scD, mds, K, cg, cf, na⟩)

def PG (f : Nat) : Prop := ∀ (k : Nat) (ts : List Tok) out d scN scD mds K cg cf na, scN.length = scD.length →
  Out (pArgs f scN (dsOf mds) k ts)
    (fun as r => cnt as = k ∧ Reach (.args f k) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩
      .ret ⟨r, out ++ serUA scD d as, d + k, scN.zip scD, mds, K, cg, cf, na⟩)
    (Fails (.args f k) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩)

theorem Out.imp {o : Option (Ex × List Tok)} {ok1 ok2 : Ex → List Tok → Prop} {bad1 bad2 : Prop}
    (hok : ∀ e r, ok1 e r → ok2 e r) (hbad : bad1 → bad2) (h : Out o ok1 bad1) : Out o ok2 bad2 := by
  cases o with
  | none => exact hbad h
  | some er => exact hok er.1 er.2 h

theorem PE_succ (f : Nat) (IE : PE f) (IM : PM f) (IA : PA f) : PE (f + 1) := by
  intro ts out d scN scD mds K cg cf na hlen
  have hst := step_expr f ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩
  rw [pExpr_succ]
  cases hl : letV ts with
  | some xt =>
    obtain ⟨x, ts'⟩ := xt
    simp only [hl] at hst ⊢
    have h1 := IE ts' out d scN scD mds (.letV f x :: K) cg cf na hlen
    cases hv : pExpr f scN (dsOf mds) ts' with
    | none => rw [hv] at h1; exact Fails.stepT hst h1
    | some vr =>
      obtain ⟨v, r⟩ := vr
      rw [hv] at h1
      have hbad : (∀ r', r ≠ Tok.semi :: r') → Fails (.expr (f + 1)) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩ := by
        intro hr
        refine Fails.stepT hst (h1.fails (Fails.one ?_))
        simp only [step, retF]
        all_goals split
        all_goals first | rfl | (rename_i r' h; exact absurd h (hr r'))
      rcases r with _ | ⟨t, r'⟩
      · exact hbad (fun _ h => by cases h)
      cases t
      case semi =>
        have h2 := IE r' (out ++ serUE scD d v) (d + 1) (x :: scN) (d :: scD) mds (.letB :: K) cg cf na
          (by simp [hlen])
        cases hb : pExpr f (x :: scN) (dsOf mds) r' with
        | none =>
          rw [hb] at h2
          simp only [Out, hb]
          exact Fails.stepT hst (h1.fails (Fails.stepT (by simp only [step, retF]; rfl) h2))
        | some br =>
          obtain ⟨b, r2⟩ := br
          rw [hb] at h2
          simp only [Out, hb]
          refine Reach.stepT hst (h1.trans (Reach.stepT (by simp only [step, retF]; rfl) (h2.trans ?_)))
          refine Reach.congr (Reach.one (by simp only [step, retF]; rfl)) ?_
          simp [serUE, List.append_assoc]
      all_goals exact hbad (fun _ h => by cases h)
  | none =>
    simp only [hl] at hst ⊢
    have h1 := IM ts out d scN scD mds (.exprAdd f :: K) cg cf na hlen
    cases hm : pMul f scN (dsOf mds) ts with
    | none => rw [hm] at h1; exact Fails.stepT hst h1
    | some er =>
      obtain ⟨e, r⟩ := er
      rw [hm] at h1
      have h2 := IA r out e d scN scD mds K cg cf na hlen
      simp only [Out]
      refine Out.imp (fun e2 r2 h => Reach.stepT hst (h1.trans (Reach.stepT (by simp only [step]; rfl) h)))
        (fun h => Fails.stepT hst (h1.fails (Fails.stepT (by simp only [step]; rfl) h))) h2

theorem PA_succ (f : Nat) (IM : PM f) (IA : PA f) : PA (f + 1) := by
  intro ts o acc d scN scD mds K cg cf na hlen
  have hst := step_add f ⟨ts, o ++ serUE scD d acc, d + 1, scN.zip scD, mds, K, cg, cf, na⟩
  rw [pAdd_succ]
  cases hl : addV ts with
  | none => simp only [hl] at hst ⊢; simp only [Out]; exact Reach.one hst
  | some mt =>
    obtain ⟨m, ts'⟩ := mt
    simp only [hl] at hst ⊢
    have h1 := IM ts' (o ++ serUE scD d acc) (d + 1) scN scD mds (.addOp f (opB m) :: K) cg cf na hlen
    cases hm : pMul f scN (dsOf mds) ts' with
    | none => rw [hm] at h1; simp only [Out]; exact Fails.stepT hst h1
    | some er =>
      obtain ⟨e, r⟩ := er
      rw [hm] at h1
      have h2 := IA r o (opE m acc e) d scN scD mds K cg cf na hlen
      have hs : step .ret ⟨r, (o ++ serUE scD d acc) ++ serUE scD (d + 1) e, d + 1 + 1, scN.zip scD, mds,
          .addOp f (opB m) :: K, cg, cf, na⟩ =
          .go (.add f) ⟨r, o ++ serUE scD d (opE m acc e), d + 1, scN.zip scD, mds, K, cg, cf, na⟩ := by
        cases m <;> simp [step, retF, opE, opB, serUE, List.append_assoc]
      simp only [Out]
      exact Out.imp (fun _ _ h => Reach.stepT hst (h1.trans (Reach.stepT hs h)))
        (fun h => Fails.stepT hst (h1.fails (Fails.stepT hs h))) h2

theorem PT_succ (f : Nat) (IP : PP f) (IT : PT f) : PT (f + 1) := by
  intro ts o acc d scN scD mds K cg cf na hlen
  have hst := step_mulT f ⟨ts, o ++ serUE scD d acc, d + 1, scN.zip scD, mds, K, cg, cf, na⟩
  rw [pMulT_succ]
  cases hl : starV ts with
  | none => simp only [hl] at hst ⊢; simp only [Out]; exact Reach.one hst
  | some ts' =>
    simp only [hl] at hst ⊢
    have h1 := IP ts' (o ++ serUE scD d acc) (d + 1) scN scD mds (.mulOp f :: K) cg cf na hlen
    cases hm : pApp f scN (dsOf mds) ts' with
    | none => rw [hm] at h1; simp only [Out]; exact Fails.stepT hst h1
    | some er =>
      obtain ⟨e, r⟩ := er
      rw [hm] at h1
      have h2 := IT r o (Ex.mul acc e) d scN scD mds K cg cf na hlen
      have hs : step .ret ⟨r, (o ++ serUE scD d acc) ++ serUE scD (d + 1) e, d + 1 + 1, scN.zip scD, mds,
          .mulOp f :: K, cg, cf, na⟩ =
          .go (.mulT f) ⟨r, o ++ serUE scD d (Ex.mul acc e), d + 1, scN.zip scD, mds, K, cg, cf, na⟩ := by
        simp [step, retF, serUE, List.append_assoc]
      simp only [Out]
      exact Out.imp (fun _ _ h => Reach.stepT hst (h1.trans (Reach.stepT hs h)))
        (fun h => Fails.stepT hst (h1.fails (Fails.stepT hs h))) h2

theorem PM_succ (f : Nat) (IP : PP f) (IT : PT f) : PM (f + 1) := by
  intro ts out d scN scD mds K cg cf na hlen
  have hst : step (.mul (f + 1)) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩ =
      .go (.app f) ⟨ts, out, d, scN.zip scD, mds, .mulT f :: K, cg, cf, na⟩ := rfl
  simp only [pMul]
  have h1 := IP ts out d scN scD mds (.mulT f :: K) cg cf na hlen
  cases hm : pApp f scN (dsOf mds) ts with
  | none => rw [hm] at h1; simp only [Out]; exact Fails.stepT hst h1
  | some er =>
    obtain ⟨e, r⟩ := er
    rw [hm] at h1
    have h2 := IT r out e d scN scD mds K cg cf na hlen
    have hs : step .ret ⟨r, out ++ serUE scD d e, d + 1, scN.zip scD, mds, .mulT f :: K, cg, cf, na⟩ =
        .go (.mulT f) ⟨r, out ++ serUE scD d e, d + 1, scN.zip scD, mds, K, cg, cf, na⟩ := rfl
    simp only [Out]
    exact Out.imp (fun _ _ h => Reach.stepT hst (h1.trans (Reach.stepT hs h)))
      (fun h => Fails.stepT hst (h1.fails (Fails.stepT hs h))) h2

theorem PG_succ (f : Nat) (IO : PO f) (IG : PG f) : PG (f + 1) := by
  intro k ts out d scN scD mds K cg cf na hlen
  cases k with
  | zero =>
    simp only [pArgs, Out]
    refine ⟨rfl, Reach.congr (Reach.one rfl) ?_⟩
    simp [serUA]
  | succ k =>
    have hst : step (.args (f + 1) (k + 1)) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩ =
        .go (.atom f) ⟨ts, out, d, scN.zip scD, mds, .args f k :: K, cg, cf, na⟩ := rfl
    simp only [pArgs]
    have h1 := IO ts out d scN scD mds (.args f k :: K) cg cf na hlen
    cases hm : pAtom f scN (dsOf mds) ts with
    | none => rw [hm] at h1; simp only [Out]; exact Fails.stepT hst h1
    | some er =>
      obtain ⟨e, r⟩ := er
      rw [hm] at h1
      have h2 := IG k r (out ++ serUE scD d e) (d + 1) scN scD mds K cg cf na hlen
      have hs : step .ret ⟨r, out ++ serUE scD d e, d + 1, scN.zip scD, mds, .args f k :: K, cg, cf, na⟩ =
          .go (.args f k) ⟨r, out ++ serUE scD d e, d + 1, scN.zip scD, mds, K, cg, cf, na⟩ := rfl
      cases hg : pArgs f scN (dsOf mds) k r with
      | none => rw [hg] at h2; simp only [Out, hg]; exact Fails.stepT hst (h1.fails (Fails.stepT hs h2))
      | some er2 =>
        obtain ⟨es, r2⟩ := er2
        rw [hg] at h2
        obtain ⟨hc, h2⟩ := h2
        simp only [Out, hg]
        refine ⟨by simp [cnt, hc], Reach.stepT hst (h1.trans (Reach.stepT hs (h2.congr ?_)))⟩
        simp [serUA, List.append_assoc]; omega

theorem var_eq (scN : List (List UInt8)) (scD : List Nat) (g : List UInt8) (i : Nat) (hlen : scN.length = scD.length)
    (hi : idx g scN 0 = some i) (d : Nat) :
    lookS g (scN.zip scD) = some (scD.getD i 0) ∧ serUE scD d (Ex.var i) = sVar d (scD.getD i 0) := by
  rw [lookS_zip g scN scD 0 hlen, hi]
  exact ⟨by simp, rfl⟩

theorem call_eq (scD : List Nat) (d j : Nat) (as : Ex) :
    serUE scD d (Ex.call (Ex.var j) as) = serUA scD d as ++ sCall j (cnt as) := by
  simp [serUE, sCall, List.append_assoc]

theorem PP_succ (f : Nat) (IG : PG f) (IO : PO f) : PP (f + 1) := by
  intro ts out d scN scD mds K cg cf na hlen
  have hst := step_app f ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩
  rw [pApp_succ]
  have hoth : step (.app (f + 1)) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩ =
      .go (.atom f) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩ →
      Out (pAtom f scN (dsOf mds) ts)
        (fun e r => Reach (.app (f + 1)) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩
          .ret ⟨r, out ++ serUE scD d e, d + 1, scN.zip scD, mds, K, cg, cf, na⟩)
        (Fails (.app (f + 1)) ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩) := fun h =>
    Out.imp (fun _ _ h2 => Reach.stepT h h2) (fun h2 => Fails.stepT h h2) (IO ts out d scN scD mds K cg cf na hlen)
  cases hv : appV ts with
  | name g ts' =>
    simp only [hv] at hst ⊢
    cases hi : idx g scN 0 with
    | some i =>
      obtain ⟨hl, he⟩ := var_eq scN scD g i hlen hi d
      simp only [hl] at hst
      simp only [Out]; rw [he]; exact Reach.one hst
    | none =>
      have hl : lookS g (scN.zip scD) = none := by rw [lookS_zip g scN scD 0 hlen, hi]; rfl
      simp only [hl] at hst
      rw [findDef_dsOf]
      cases hf : findD g mds with
      | none => simp only [hf] at hst; simp only [Out, Option.map]; exact Fails.one hst
      | some kj =>
        obtain ⟨k, j⟩ := kj
        simp only [hf] at hst
        simp only [Option.map]
        have h1 := IG k ts' out d scN scD mds (.call j k :: K) cg cf na hlen
        cases ha : pArgs f scN (dsOf mds) k ts' with
        | none => rw [ha] at h1; simp only [Out]; exact Fails.stepT hst h1
        | some er =>
          obtain ⟨as, r⟩ := er
          rw [ha] at h1
          obtain ⟨hc, h1⟩ := h1
          simp only [Out]
          refine Reach.stepT hst (h1.trans (Reach.congr (Reach.one rfl) ?_))
          rw [call_eq, hc]; simp [List.append_assoc]; omega
  | neg n ts' =>
    simp only [hv] at hst ⊢; simp only [Out]; exact Reach.one hst
  | lp ts' => simp only [hv] at hst ⊢; exact hoth hst
  | num n ts' => simp only [hv] at hst ⊢; exact hoth hst
  | other => simp only [hv] at hst ⊢; exact hoth hst

theorem PO_succ (f : Nat) (IE : PE f) : PO (f + 1) := by
  intro ts out d scN scD mds K cg cf na hlen
  have hst := step_atom f ⟨ts, out, d, scN.zip scD, mds, K, cg, cf, na⟩
  rw [pAtom_succ]
  cases hv : appV ts with
  | num n => simp only [hv] at hst ⊢; simp only [Out]; exact Reach.one hst
  | name g ts' =>
    simp only [hv] at hst ⊢
    cases hi : idx g scN 0 with
    | some i =>
      obtain ⟨hl, he⟩ := var_eq scN scD g i hlen hi d
      simp only [hl] at hst
      simp only [Out]; rw [he]; exact Reach.one hst
    | none =>
      have hl : lookS g (scN.zip scD) = none := by rw [lookS_zip g scN scD 0 hlen, hi]; rfl
      simp only [hl] at hst
      rw [findDef_dsOf]
      cases hf : findD g mds with
      | none => simp only [hf] at hst; simp only [Out, Option.map]; exact Fails.one hst
      | some kj =>
        obtain ⟨k, j⟩ := kj
        simp only [hf] at hst
        cases k with
        | zero =>
          simp only [Option.map, Out]
          refine Reach.congr (Reach.one hst) ?_
          rw [call_eq]; simp [serUA, cnt]
        | succ k => simp only [Option.map, Out]; exact Fails.one hst
  | lp ts' =>
    simp only [hv] at hst ⊢
    have h1 := IE ts' out d scN scD mds (.paren :: K) cg cf na hlen
    cases he : pExpr f scN (dsOf mds) ts' with
    | none => rw [he] at h1; simp only [Out]; exact Fails.stepT hst h1
    | some er =>
      obtain ⟨e, r⟩ := er
      rw [he] at h1
      rcases r with _ | ⟨t, r'⟩
      · simp only [Out]; exact Fails.stepT hst (h1.fails (Fails.one rfl))
      cases t
      case rp =>
        simp only [Out]; exact Reach.stepT hst (h1.trans (Reach.one rfl))
      all_goals simp only [Out]; exact Fails.stepT hst (h1.fails (Fails.one rfl))
  | neg n ts' => simp only [hv] at hst ⊢; simp only [Out]; exact Fails.one hst
  | other => simp only [hv] at hst ⊢; simp only [Out]; exact Fails.one hst

/-- **the simulation**: every parse function, every fuel -/
theorem sim : ∀ f, PE f ∧ PA f ∧ PM f ∧ PT f ∧ PP f ∧ PG f ∧ PO f
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [PE, PA, PM, PT, PP, PG, PO]; intros) <;>
      simp only [pExpr, pAdd, pMul, pMulT, pApp, pArgs, pAtom, Out] <;> exact Fails.one rfl
  | f + 1 => by
    obtain ⟨IE, IA, IM, IT, IP, IG, IO⟩ := sim f
    exact ⟨PE_succ f IE IM IA, PA_succ f IM IA, PM_succ f IP IT, PT_succ f IP IT, PP_succ f IG IO, PG_succ f IO IG,
      PO_succ f IE⟩

end Nano.PB
