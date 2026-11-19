/- Opus box E: parsed bodies have Gen's prim operand counts (`PAr`), by induction over the parser functions. -/
import Nano.V2Self.Proof.DBNode
namespace Templates
open ParSpec

def QE (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pExpr f cx tl ts nx = some (e, ty, r, nx') → PAr e
def QB (f : Nat) : Prop := ∀ cx tl minp ts nx e ty r nx', pBin f cx tl minp ts nx = some (e, ty, r, nx') → PAr e
def QL (f : Nat) : Prop := ∀ cx minp a ta ts nx e ty r nx', PAr a → pLoop f cx minp a ta ts nx = some (e, ty, r, nx') → PAr e
def QA (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pApp f cx tl ts nx = some (e, ty, r, nx') → PAr e
def QC (f : Nat) : Prop := ∀ cx n ts nx e ty r nx', pCallDef f cx n ts nx = some (e, ty, r, nx') → PAr e
def QG (f : Nat) : Prop := ∀ cx ps ts nx as r nx', pArgs f cx ps ts nx = some (as, r, nx') →
  as.length = ps.length ∧ ∀ a ∈ as, PAr a.1
def QT (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pAtom f cx tl ts nx = some (e, ty, r, nx') → PAr e
def QU (f : Nat) : Prop := ∀ cx ts nx e sh r nx', pTup f cx ts nx = some (e, sh, r, nx') → PAr e

theorem parL_iff : ∀ l : List Nd, PArL l ↔ ∀ x ∈ l, PAr x
  | [] => by simp [PArL]
  | c :: l => by simp [PArL, parL_iff l]

/-- the operands Gen reads: the non-input parameters -/
def nI (ps : List Ps) : Nat := (ps.filter fun p => match p with | .inp => false | _ => true).length

theorem dropInp_len : ∀ (ps : List Ps) (xs : List Nd), xs.length = ps.length → (dropInp ps xs).length = nI ps
  | [], [], _ => rfl
  | p :: ps, x :: xs, h => by
    have ih := dropInp_len ps xs (by simpa using h)
    unfold dropInp nI at *
    cases p <;> simp [List.filterMap_cons, List.filter_cons, ih]

theorem dropInp_mem : ∀ (ps : List Ps) (xs : List Nd) x, x ∈ dropInp ps xs → x ∈ xs := by
  intro ps xs x h
  unfold dropInp at h
  obtain ⟨⟨p, a⟩, hm, he⟩ := List.mem_filterMap.1 h
  have := (List.of_mem_zip hm).2
  cases p <;> simp at he <;> subst he <;> exact this

theorem primSig_nI {t pid ps rs} (h : primSig t = some (pid, ps, rs)) : nI ps = (C.g33 pid.toUInt64).toNat := by
  unfold primSig at h; split at h <;> cases h <;> decide

theorem mkPairFlat_par (cs : List Nd) (h : ∀ x ∈ cs, PAr x) : PAr (mkPairFlat cs) := by
  match cs with
  | [c] => exact h c (by simp)
  | [] => simp [mkPairFlat, PAr, PArL]
  | a :: b :: l => simp only [mkPairFlat, PAr]; exact (parL_iff _).2 h

theorem qE_step (f : Nat) (hB : QB f) (hE : QE f) : QE (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pExpr at h
  split at h
  · cases h
  · rename_i cx tl nx _ _ _ _ _ f0 x r0 heq
    simp at heq; subst heq
    obtain ⟨⟨v, tv, r1, nx1⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · obtain ⟨⟨b, tb, r3, nx3⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      exact ⟨hE _ _ _ _ _ _ _ _ hv, hE _ _ _ _ _ _ _ _ hb⟩
    · cases h
  · rename_i cx tl nx _ _ _ _ _ f0 x y r0 heq
    simp at heq; subst heq
    obtain ⟨⟨v, tv, r1, nx1⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · obtain ⟨⟨b, tb, r3, nx3⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      exact ⟨hE _ _ _ _ _ _ _ _ hv, hE _ _ _ _ _ _ _ _ hb⟩
    · cases h
  · rename_i cx tl nx _ _ _ _ _ f0 r0 heq
    simp at heq; subst heq
    obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
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
            obtain ⟨ty', hj, he⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
            exact ⟨hB _ _ _ _ _ _ _ _ _ ha, hB _ _ _ _ _ _ _ _ _ hb, hE _ _ _ _ _ _ _ _ ht, hE _ _ _ _ _ _ _ _ hel⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · rename_i cx tl ts nx _ _ _ _ _ f0 heq _ _ _
    simp at heq; subst heq
    exact hB _ _ _ _ _ _ _ _ _ h

theorem qB_step (f : Nat) (hA : QA f) (hL : QL f) : QB (f + 1) := by
  intro cx tl minp ts nx e ty r nx' h
  unfold pBin at h
  obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
  simp only at h
  have t1 := hA _ _ _ _ _ _ _ _ ha
  split at h
  · split at h
    · obtain ⟨⟨a', ta', r1', nx1'⟩, ha', h⟩ := Option.bind_eq_some_iff.1 h
      exact hL _ _ _ _ _ _ _ _ _ _ (hA _ _ _ _ _ _ _ _ ha') h
    · exact hL _ _ _ _ _ _ _ _ _ _ t1 h
  · exact hL _ _ _ _ _ _ _ _ _ _ t1 h

theorem qL_step (f : Nat) (hB : QB f) (hL : QL f) : QL (f + 1) := by
  intro cx minp a ta ts nx e ty r nx' ha h
  unfold pLoop at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ha
      · split at h
        · split at h
          · split at h
            · exact hL _ _ _ _ _ _ _ _ _ _ (by simp only [PAr]; exact ⟨ha, trivial⟩) h
            · cases h
          · obtain ⟨⟨b, tb, r', nx2⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
            simp only at h
            split at h
            · exact hL _ _ _ _ _ _ _ _ _ _ (by simp only [PAr]; exact ⟨ha, hB _ _ _ _ _ _ _ _ _ hb⟩) h
            · cases h
        · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ha
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ha

theorem qC_step (f : Nat) (hG : QG f) : QC (f + 1) := by
  intro cx n ts nx e ty r nx' h
  unfold pCallDef at h
  split at h
  · obtain ⟨⟨as, r1, nx1⟩, ha, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨-, t1⟩ := hG _ _ _ _ _ _ _ ha
    exact (parL_iff _).2 fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (dropInp_mem _ _ _ hx); exact t1 y hy
  · cases h

theorem qG_step (f : Nat) (hT : QT f) (hG : QG f) : QG (f + 1) := by
  intro cx ps ts nx as r nx' h
  unfold pArgs at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp⟩
  · rename_i f0 p ps0 heq
    simp at heq; subst heq
    obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · obtain ⟨⟨as0, r2, nx2⟩, has, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨hl2, t2⟩ := hG _ _ _ _ _ _ _ has
      refine ⟨by simp [hl2], ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hT _ _ _ _ _ _ _ _ ha
      · exact t2 x hx
    · cases h

theorem qA_step (f : Nat) (hT : QT f) (hG : QG f) (hC : QC f) : QA (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pApp at h
  split at h
  · cases h
  · rename_i f0 t r0 heq
    simp at heq; subst heq
    split at h
    · rename_i pid ps rs hp
      obtain ⟨⟨as, r1, nx1⟩, ha, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨hl1, t1⟩ := hG _ _ _ _ _ _ _ ha
      refine ⟨?_, (parL_iff _).2 fun x hx => ?_⟩
      · rw [dropInp_len _ _ (by simpa using hl1), primSig_nI hp]
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (dropInp_mem _ _ _ hx); exact t1 y hy
    · exact hT _ _ _ _ _ _ _ _ h
  · rename_i cx tl nx _ _ _ _ _ f0 n r0 heq
    simp at heq; subst heq
    split at h
    · exact hT _ _ _ _ _ _ _ _ h
    · split at h
      · split at h
        · split at h
          · split at h
            · split at h
              · obtain ⟨⟨as, r2, nx2⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
                simp only at h
                split at h
                · cases h
                · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  obtain ⟨-, t1⟩ := hG _ _ _ _ _ _ _ ha
                  exact mkPairFlat_par _ fun x hx => by
                    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (dropInp_mem _ _ _ hx); exact t1 y hy
              · cases h
            · cases h
          · cases h
        · exact hC _ _ _ _ _ _ _ _ h
      · exact hC _ _ _ _ _ _ _ _ h
  · rename_i cx tl ts nx _ _ _ _ _ f0 heq _ _
    simp at heq; subst heq
    exact hT _ _ _ _ _ _ _ _ h

theorem qT_step (f : Nat) (hE : QE f) (hU : QU f) : QT (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pAtom at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; trivial
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨rfl, trivial⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨rfl, trivial⟩
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; trivial
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; trivial
    · cases h
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; trivial
        · cases h
      · cases h
  · rename_i cx tl nx _ _ _ _ _ f0 r0 heq
    simp at heq; subst heq
    obtain ⟨⟨e1, t1, r1, nx1⟩, he1, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact hE _ _ _ _ _ _ _ _ he1
    · obtain ⟨⟨e2, t2, r2, nx2⟩, he2, h⟩ := Option.bind_eq_some_iff.1 h
      simp only at h
      split at h
      · obtain ⟨⟨rest, st, r3, nx3⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        exact ⟨hE _ _ _ _ _ _ _ _ he2, hU _ _ _ _ _ _ _ hr, trivial⟩
      · cases h
    · cases h
  · cases h

theorem qU_step (f : Nat) (hE : QE f) (hU : QU f) : QU (f + 1) := by
  intro cx ts nx e sh r nx' h
  unfold pTup at h
  split at h
  · cases h
  · rename_i cx nx _ _ _ _ f0 r0 heq
    simp at heq; subst heq
    obtain ⟨⟨e1, t1, r1, nx1⟩, he1, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact hE _ _ _ _ _ _ _ _ he1
    · obtain ⟨⟨rest, sr, r3, nx3⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      exact ⟨hE _ _ _ _ _ _ _ _ he1, hU _ _ _ _ _ _ _ hr, trivial⟩
    · cases h
  · cases h

theorem q_all : ∀ f, QE f ∧ QB f ∧ QL f ∧ QA f ∧ QC f ∧ QG f ∧ QT f ∧ QU f
  | 0 => by
    refine ⟨fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ _ _ h => ?_,
      fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ h => ?_,
      fun _ _ _ _ _ _ _ h => ?_⟩
    · rw [pExpr.eq_1] at h; cases h
    · rw [pBin.eq_1] at h; cases h
    · rw [pLoop.eq_1] at h; cases h
    · rw [pApp.eq_1] at h; cases h
    · rw [pCallDef.eq_1] at h; cases h
    · rw [pArgs.eq_1] at h; cases h
    · rw [pAtom.eq_1] at h; cases h
    · rw [pTup.eq_1] at h; cases h
  | f + 1 => by
    obtain ⟨hE, hB, hL, hA, hC, hG, hT, hU⟩ := q_all f
    exact ⟨qE_step f hB hE, qB_step f hA hL, qL_step f hB hL, qA_step f hT hG hC, qC_step f hG, qG_step f hT hG,
      qT_step f hE hU, qU_step f hE hU⟩

theorem pDef_par (fuel : Nat) (defs : List DefI) (ts : List Tok) (di : DefI) (da : DefA) (r : List Tok)
    (h : pDef fuel defs ts = some (di, da, r)) : PAr da.body ∧ da.kind ≤ 1 ∧ da.id = defs.length := by
  obtain ⟨hE, -⟩ := q_all fuel
  unfold pDef at h
  split at h
  · split at h
    · cases h
    · split at h
      · obtain ⟨⟨tys, r1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
        simp only at h
        split at h
        · split at h
          · cases h
          · split at h
            · obtain ⟨⟨zn, r3⟩, hz, h⟩ := Option.bind_eq_some_iff.1 h
              simp only at h
              split at h
              · cases h
              · obtain ⟨envZ, hZ, h⟩ := Option.bind_eq_some_iff.1 h
                obtain ⟨⟨z, tz, r4, nx1⟩, hpz, h⟩ := Option.bind_eq_some_iff.1 h
                simp only at h
                split at h
                · cases h
                · split at h
                  · obtain ⟨⟨sn, r6⟩, hs, h⟩ := Option.bind_eq_some_iff.1 h
                    simp only at h
                    split at h
                    · cases h
                    · obtain ⟨envS, hS, h⟩ := Option.bind_eq_some_iff.1 h
                      obtain ⟨⟨sb, ts', r7, nx2⟩, hps, h⟩ := Option.bind_eq_some_iff.1 h
                      simp only at h
                      split at h
                      · split at h
                        · cases h
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        exact ⟨⟨hE _ _ _ _ _ _ _ _ hpz, hE _ _ _ _ _ _ _ _ hps⟩, Nat.le_refl 1, rfl⟩
                      · cases h
                  · cases h
            · cases h
        · cases h
      · obtain ⟨⟨groups, r1⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
        simp only at h
        split at h
        · obtain ⟨⟨resT, r3⟩, ht, h⟩ := Option.bind_eq_some_iff.1 h
          simp only at h
          split at h
          · split at h
            · cases h
            · obtain ⟨⟨b, tb, r5, nx⟩, hpe, h⟩ := Option.bind_eq_some_iff.1 h
              simp only at h
              split at h
              · cases h
              · split at h
                · cases h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact ⟨hE _ _ _ _ _ _ _ _ hpe, Nat.zero_le 1, rfl⟩
          · cases h
        · cases h
  · cases h

theorem pDefs_par (fuel : Nat) : ∀ (f : Nat) (defs : List DefI) (ts : List Tok) (ds : List DefI) (as : List DefA),
    pDefs fuel f defs ts = some (ds, as) → ∀ (i : Nat) (d : DefA), as[i]? = some d → PAr d.body ∧ d.kind ≤ 1 ∧ d.id = defs.length + i
  | 0, _, _, _, _, h => by simp [pDefs] at h
  | f + 1, defs, [], ds, as, h => by
    simp [pDefs] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | f + 1, defs, t :: ts, ds, as, h => by
    simp only [pDefs] at h
    obtain ⟨⟨di, da, r⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨ds', as'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    intro i d hi
    cases i with
    | zero => simp at hi; subst hi; simpa using pDef_par fuel defs _ di _ r hd
    | succ i =>
      have := pDefs_par fuel f (defs ++ [di]) r ds' as' hr i d (by simpa using hi)
      simp at this; refine ⟨this.1, this.2.1, by omega⟩

theorem parsed_par {ts : List UInt64} {p : List DefA} (h : ParsesProgram ts p) :
    ∀ (i : Nat) (d : DefA), p[i]? = some d → PAr d.body ∧ d.kind ≤ 1 ∧ d.id = i := by
  unfold ParsesProgram refParse at h
  obtain ⟨toks, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨ds, as⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
  simp only at h
  split at h
  · split at h
    · cases h
      intro i d hi
      simpa using pDefs_par _ _ _ _ _ _ hd i d hi
    · cases h
  · cases h

end Templates
