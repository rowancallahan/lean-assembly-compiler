/- Nano/V2Self/Proof/OwnWF: well-formedness of parser outputs for the ownership-stage proof (box C, for O).
(1) `NdAr`: every PRIM node has its arity (`OwnP.primAr`) — a context-free fuel induction over ParSpec's expression parser
    (`Nd.ser` has no argument count for PRIM, so this is what makes the serialization readable).
(2) `TyN → WFN`: the slot / width / call-id bounds of `OwnP.WFN` follow from D's kinding (`MainTy.TyN`, every slot read or
    written lies below Γ.length = nslots) once `nslots < 2^20` and the def count is < 2^64.  The parser does NOT bound nslots
    (nested pair lets double widths), so `nslots < 2^20` is a hypothesis (Gen gives nslots < 251).
(3) `parsed_wfp : ParsesProgram ts p → Bnd p → WFP p`. -/
import Nano.V2Self.Proof.OwnP26
import Nano.V2Self.Proof.MainTyP
namespace OwnWF
open ParSpec OwnP OwnSpec NanoMain

mutual
/-- every PRIM node has the arity of its primitive -/
def NdAr : Nd → Prop
  | .const _ => True
  | .loc _ _ => True
  | .bin _ a b => NdAr a ∧ NdAr b
  | .ite _ a b t e => NdAr a ∧ NdAr b ∧ NdAr t ∧ NdAr e
  | .letE _ _ v b => NdAr v ∧ NdAr b
  | .pair cs => NdArL cs
  | .call _ as => NdArL as
  | .prim p as => primAr p as ∧ NdArL as
  | .loop z s => NdAr z ∧ NdAr s
  | .cont e => NdAr e
def NdArL : List Nd → Prop
  | [] => True
  | n :: r => NdAr n ∧ NdArL r
end

theorem ndArL_iff : ∀ cs : List Nd, NdArL cs ↔ ∀ c ∈ cs, NdAr c
  | [] => by simp [NdArL]
  | c :: r => by simp [NdArL, ndArL_iff r]

theorem dropInp_mem (ps : List Ps) (xs : List Nd) (x : Nd) (h : x ∈ dropInp ps xs) : x ∈ xs := by
  simp only [dropInp, List.mem_filterMap] at h
  obtain ⟨⟨p, a⟩, hm, he⟩ := h
  have := (List.of_mem_zip hm).2
  cases p <;> simp at he <;> subst he <;> exact this

def notInp : Ps → Bool | .inp => false | _ => true

theorem dropInp_len : ∀ (ps : List Ps) (xs : List Nd), xs.length = ps.length → (dropInp ps xs).length = (ps.filter notInp).length
  | [], [], _ => rfl
  | p :: ps, x :: xs, h => by
    have ih := dropInp_len ps xs (by simpa using h)
    simp only [dropInp, List.zip_cons_cons, List.filterMap_cons] at ih ⊢
    cases p <;> simp [notInp, ih]

theorem ar_dropInp {xs : List Nd} (h : ∀ x ∈ xs, NdAr x) (ps : List Ps) : NdArL (dropInp ps xs) :=
  (ndArL_iff _).2 fun x hx => h x (dropInp_mem ps xs x hx)

theorem ar_mkPairFlat {cs : List Nd} (h : NdArL cs) : NdAr (mkPairFlat cs) := by
  unfold mkPairFlat; split
  · simpa [NdArL] using h
  · simpa [NdAr] using h

/-- the prim table: the non-input arguments are exactly `dsP pid` many -/
theorem prim_arity {t pid : Nat} {ps : List Ps} {rs : Sh} (h : primSig t = some (pid, ps, rs)) (xs : List Nd)
    (hl : xs.length = ps.length) : primAr pid (dropInp ps xs) := by
  intro _ _
  rw [dropInp_len ps xs hl]
  unfold primSig at h
  split at h <;> (try cases h) <;> rfl

/-! ## (1) the parser emits `NdAr` nodes -/
def QE (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pExpr f cx tl ts nx = some (e, ty, r, nx') → NdAr e
def QB (f : Nat) : Prop := ∀ cx tl minp ts nx e ty r nx', pBin f cx tl minp ts nx = some (e, ty, r, nx') → NdAr e
def QL (f : Nat) : Prop := ∀ cx minp a ta ts nx e ty r nx', pLoop f cx minp a ta ts nx = some (e, ty, r, nx') → NdAr a → NdAr e
def QA (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pApp f cx tl ts nx = some (e, ty, r, nx') → NdAr e
def QC (f : Nat) : Prop := ∀ cx n ts nx e ty r nx', pCallDef f cx n ts nx = some (e, ty, r, nx') → NdAr e
def QG (f : Nat) : Prop := ∀ cx ps ts nx as r nx', pArgs f cx ps ts nx = some (as, r, nx') →
  as.length = ps.length ∧ ∀ x ∈ as, NdAr x.1
def QT (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pAtom f cx tl ts nx = some (e, ty, r, nx') → NdAr e
def QU (f : Nat) : Prop := ∀ cx ts nx e sh r nx', pTup f cx ts nx = some (e, sh, r, nx') → NdAr e

theorem qE_step (f : Nat) (hB : ∀ g ≤ f, QB g) (hE : ∀ g ≤ f, QE g) : QE (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pExpr at h
  split at h
  · cases h
  · obtain ⟨⟨v, tv, r1, nx1⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · obtain ⟨⟨b, tb, r3, nx3⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, -, -⟩ := he
      exact ⟨hE _ (by omega) _ _ _ _ _ _ _ _ hv, hE _ (by omega) _ _ _ _ _ _ _ _ hb⟩
    · cases h
  · obtain ⟨⟨v, tv, r1, nx1⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · obtain ⟨⟨b, tb, r3, nx3⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, -, -⟩ := he
      exact ⟨hE _ (by omega) _ _ _ _ _ _ _ _ hv, hE _ (by omega) _ _ _ _ _ _ _ _ hb⟩
    · cases h
  · obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · split at h
      · obtain ⟨⟨b, tb, r3, nx2⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
        simp only at h
        split at h
        · obtain ⟨⟨t, tt, r5, nx3⟩, ht, h⟩ := Option.bind_eq_some_iff.1 h
          simp only at h
          split at h
          · obtain ⟨⟨el, te, r7, nx4⟩, hel, h⟩ := Option.bind_eq_some_iff.1 h
            obtain ⟨ty', _, he⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, -, -⟩ := he
            exact ⟨hB _ (by omega) _ _ _ _ _ _ _ _ _ ha, hB _ (by omega) _ _ _ _ _ _ _ _ _ hb,
              hE _ (by omega) _ _ _ _ _ _ _ _ ht, hE _ (by omega) _ _ _ _ _ _ _ _ hel⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · exact hB _ (by omega) _ _ _ _ _ _ _ _ _ h

theorem qB_step (f : Nat) (hA : ∀ g ≤ f, QA g) (hL : ∀ g ≤ f, QL g) : QB (f + 1) := by
  intro cx tl minp ts nx e ty r nx' h
  unfold pBin at h
  obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
  have na := hA _ (by omega) _ _ _ _ _ _ _ _ ha
  simp only at h
  split at h
  · split at h
    · obtain ⟨⟨a', ta', r', nx''⟩, ha', h⟩ := Option.bind_eq_some_iff.1 h
      exact hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h (hA _ (by omega) _ _ _ _ _ _ _ _ ha')
    · exact hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h na
  · exact hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h na

theorem qL_step (f : Nat) (hB : ∀ g ≤ f, QB g) (hL : ∀ g ≤ f, QL g) : QL (f + 1) := by
  intro cx minp a ta ts nx e ty r nx' h na
  unfold pLoop at h
  split at h
  · split at h
    · split at h
      · cases h; exact na
      · split at h
        · split at h
          · split at h
            · exact hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h ⟨na, trivial⟩
            · cases h
          · obtain ⟨⟨b, tb, r', nx''⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
            simp only at h
            split at h
            · exact hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h ⟨na, hB _ (by omega) _ _ _ _ _ _ _ _ _ hb⟩
            · cases h
        · cases h
    · cases h; exact na
  · cases h; exact na

theorem qC_step (f : Nat) (hG : ∀ g ≤ f, QG g) : QC (f + 1) := by
  intro cx n ts nx e ty r nx' h
  unfold pCallDef at h
  split at h
  · obtain ⟨⟨as, r1, nx1⟩, hg, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, -, -⟩ := he
    obtain ⟨_, hm⟩ := hG _ (by omega) _ _ _ _ _ _ _ hg
    exact ar_dropInp (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hm y hy) _
  · cases h

theorem qG_step (f : Nat) (hT : ∀ g ≤ f, QT g) (hG : ∀ g ≤ f, QG g) : QG (f + 1) := by
  intro cx ps ts nx as r nx' h
  unfold pArgs at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, fun _ h => by simp at h⟩
  · obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · obtain ⟨⟨as', r2, nx2⟩, hg, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, -⟩ := he
      obtain ⟨hl, hm⟩ := hG _ (by omega) _ _ _ _ _ _ _ hg
      refine ⟨by simp [hl], fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hT _ (by omega) _ _ _ _ _ _ _ _ ha
      · exact hm x hx
    · cases h

theorem qA_step (f : Nat) (hT : ∀ g ≤ f, QT g) (hG : ∀ g ≤ f, QG g) (hC : ∀ g ≤ f, QC g) : QA (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pApp at h
  split at h
  · cases h
  · split at h
    · rename_i pid ps rs hps
      obtain ⟨⟨as, r1, nx1⟩, hg, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, -, -⟩ := he
      obtain ⟨hl, hm⟩ := hG _ (by omega) _ _ _ _ _ _ _ hg
      exact ⟨prim_arity hps _ (by simp [hl]), ar_dropInp (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hm y hy) _⟩
    · exact hT _ (by omega) _ _ _ _ _ _ _ _ h
  · repeat' (first | (cases h; done) | split at h)
    all_goals first
      | exact hT _ (by omega) _ _ _ _ _ _ _ _ h
      | exact hC _ (by omega) _ _ _ _ _ _ _ _ h
      | (obtain ⟨⟨as, r2, nx2⟩, hg, h⟩ := Option.bind_eq_some_iff.1 h
         obtain ⟨_, hm⟩ := hG _ (by omega) _ _ _ _ _ _ _ hg
         simp only at h
         split at h
         · cases h
         · cases h
           exact ar_mkPairFlat (ar_dropInp (fun x hx => by
             obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hm y hy) _))
  · exact hT _ (by omega) _ _ _ _ _ _ _ _ h

theorem qU_step (f : Nat) (hE : ∀ g ≤ f, QE g) (hU : ∀ g ≤ f, QU g) : QU (f + 1) := by
  intro cx ts nx e sh r nx' h
  unfold pTup at h
  split at h
  · cases h
  · obtain ⟨⟨e1, t, r1, nx1⟩, he1, h⟩ := Option.bind_eq_some_iff.1 h
    have n1 := hE _ (by omega) _ _ _ _ _ _ _ _ he1
    simp only at h
    split at h
    · cases h; exact n1
    · obtain ⟨⟨rest, sr, r3, nx3⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, -, -⟩ := he
      exact ⟨n1, hU _ (by omega) _ _ _ _ _ _ _ hr, trivial⟩
    · cases h
  · cases h

theorem qT_step (f : Nat) (hE : ∀ g ≤ f, QE g) (hU : ∀ g ≤ f, QU g) : QT (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pAtom at h
  split at h
  · cases h
  · cases h; trivial
  · cases h; exact ⟨fun _ _ => rfl, trivial⟩
  · cases h; exact ⟨fun _ _ => rfl, trivial⟩
  · split at h
    · cases h; trivial
    · cases h; trivial
    · cases h
    · split at h
      · split at h
        · cases h; trivial
        · cases h
      · cases h
  · obtain ⟨⟨e1, t, r1, nx1⟩, he1, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · cases h; exact hE _ (by omega) _ _ _ _ _ _ _ _ he1
    · obtain ⟨⟨e2, t2, r2, nx2⟩, he2, h⟩ := Option.bind_eq_some_iff.1 h
      simp only at h
      split at h
      · obtain ⟨⟨tl', st, r3, nx3⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, -, -⟩ := he
        exact ⟨hE _ (by omega) _ _ _ _ _ _ _ _ he2, hU _ (by omega) _ _ _ _ _ _ _ hr, trivial⟩
      · cases h
    · cases h
  · cases h

theorem q_all : ∀ f, ∀ g ≤ f, QE g ∧ QB g ∧ QL g ∧ QA g ∧ QC g ∧ QG g ∧ QT g ∧ QU g := by
  have base : QE 0 ∧ QB 0 ∧ QL 0 ∧ QA 0 ∧ QC 0 ∧ QG 0 ∧ QT 0 ∧ QU 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ _ _ h; simp [pExpr] at h
    · intro _ _ _ _ _ _ _ _ _ h; simp [pBin] at h
    · intro _ _ _ _ _ _ _ _ _ _ h; simp [pLoop] at h
    · intro _ _ _ _ _ _ _ _ h; simp [pApp] at h
    · intro _ _ _ _ _ _ _ _ h; simp [pCallDef] at h
    · intro _ _ _ _ _ _ _ h; simp [pArgs] at h
    · intro _ _ _ _ _ _ _ _ h; simp [pAtom] at h
    · intro _ _ _ _ _ _ _ h; simp [pTup] at h
  intro f
  induction f with
  | zero => intro g hg; rw [Nat.le_zero.1 hg]; exact base
  | succ f ih =>
    intro g hg
    rcases Nat.lt_or_eq_of_le hg with hg | rfl
    · exact ih g (by omega)
    · have pE := fun g h => (ih g h).1; have pB := fun g h => (ih g h).2.1; have pL := fun g h => (ih g h).2.2.1
      have pA := fun g h => (ih g h).2.2.2.1; have pC := fun g h => (ih g h).2.2.2.2.1
      have pG := fun g h => (ih g h).2.2.2.2.2.1; have pT := fun g h => (ih g h).2.2.2.2.2.2.1
      have pU := fun g h => (ih g h).2.2.2.2.2.2.2
      exact ⟨qE_step f pB pE, qB_step f pA pL, qL_step f pB pL, qA_step f pT pG pC, qC_step f pG, qG_step f pT pG,
        qT_step f pE pU, qU_step f pE pU⟩

theorem pExpr_ar {f cx tl ts nx e ty r nx'} (h : pExpr f cx tl ts nx = some (e, ty, r, nx')) : NdAr e :=
  (q_all f f (Nat.le_refl _)).1 _ _ _ _ _ _ _ _ h

theorem pDef_ar {fuel defs ts di da r} (h : pDef fuel defs ts = some (di, da, r)) : NdAr da.body := by
  unfold pDef at h
  repeat' (first
    | (cases h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h
       first
       | exact ⟨pExpr_ar (by assumption), pExpr_ar (by assumption)⟩
       | exact pExpr_ar (by assumption))
    | split at h
    | (simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists] at h
       repeat (obtain ⟨_, h⟩ := h)))

theorem pDefs_ar (fuel : Nat) : ∀ (f : Nat) (defs : List DefI) (ts : List Tok) (ds : List DefI) (as : List DefA),
    pDefs fuel f defs ts = some (ds, as) → ∀ a ∈ as, NdAr a.body
  | 0, _, _, _, _, h => by simp [pDefs] at h
  | f + 1, defs, ts, ds, as, h => by
    unfold pDefs at h
    split at h
    · cases h
    · cases h; intro a ha; simp at ha
    · rename_i f0 heq _
      obtain rfl : f = f0 := by omega
      obtain ⟨⟨di, da, r⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨ds', as'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact pDef_ar hd
      · exact pDefs_ar fuel f _ _ _ _ hr a ha

theorem refParse_ar {ts : List UInt64} {p : List DefA} (h : refParse ts = some p) : ∀ d ∈ p, NdAr d.body := by
  unfold refParse at h
  obtain ⟨toks, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨ds, as⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
  simp only at h
  split at h
  · split at h
    · cases h; exact pDefs_ar _ _ _ _ _ _ hd
    · cases h
  · cases h

end OwnWF
