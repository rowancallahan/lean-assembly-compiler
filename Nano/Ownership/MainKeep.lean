/- Nano/Ownership/MainKeep: static facts of O's walk — it kills only owned (kind 1) slots, and its tagged entries name
their slot's kind.  Used for the read-only slots' liveness (`R2`) and for the IF branch not taken. -/
import Nano.SelfHost.Bridge.MainBridge3
import Nano.SelfHost.Bridge.MainOk

namespace NanoMain
open Templates

/-- flags `F'` kill no slot of kind ≠ 1 that `F` had live -/
def Keep (Kk : List Nat) (F F' : List Bool) : Prop :=
  ∀ s, Kk.getD s 0 ≠ 1 → OwnSpec.dead F' s = true → OwnSpec.dead F s = true

/-- tagged entries carry their slot's kind -/
def TagsOK (Kk : List Nat) (es : List Nat) : Prop := ∀ x ∈ es, 4 ≤ x → x % 4 = Kk.getD (x / 4 - 1) 0

/-- O's def result kinds are plain -/
def RsW (oc : OwnSpec.Cx) : Prop := ∀ R ∈ oc.rs, ∀ x ∈ R, x ≤ 1

/-- every read-only slot is live -/
def R2 (Kk : List Nat) (F : List Bool) : Prop := ∀ s, Kk.getD s 0 = 2 → OwnSpec.dead F s = false

theorem Keep.refl (Kk : List Nat) (F : List Bool) : Keep Kk F F := fun _ _ h => h
theorem Keep.trans {Kk : List Nat} {F F1 F2 : List Bool} (h1 : Keep Kk F F1) (h2 : Keep Kk F1 F2) : Keep Kk F F2 :=
  fun s k h => h1 s k (h2 s k h)
theorem R2.keep {Kk : List Nat} {F F1 : List Bool} (h : R2 Kk F) (k : Keep Kk F F1) : R2 Kk F1 := fun s hs => by
  cases hd : OwnSpec.dead F1 s
  · rfl
  · have := k s (by omega) hd; rw [h s hs] at this; cases this

theorem tags_plain {Kk : List Nat} {es : List Nat} (h : ∀ x ∈ es, x < 4) : TagsOK Kk es := fun x hx h4 => by
  have := h x hx; omega
theorem tags_append {Kk : List Nat} {a b : List Nat} (ha : TagsOK Kk a) (hb : TagsOK Kk b) : TagsOK Kk (a ++ b) :=
  fun x hx => by rcases List.mem_append.1 hx with h | h; exact ha x h; exact hb x h

theorem dead_orF (a b : List Bool) (s : Nat) :
    OwnSpec.dead (OwnSpec.orF a b) s = (OwnSpec.dead a s || OwnSpec.dead b s) := by
  simp only [OwnSpec.dead, OwnSpec.orF, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  cases ha : a[s]? <;> cases hb : b[s]? <;> simp

theorem keep_orF {Kk : List Nat} {F a b : List Bool} (ha : Keep Kk F a) (hb : Keep Kk F b) : Keep Kk F (OwnSpec.orF a b) :=
  fun s k h => by
    rw [dead_orF] at h
    cases h1 : OwnSpec.dead a s
    · rw [h1] at h; exact hb s k (by simpa using h)
    · exact ha s k h1

theorem consume_keep {Kk : List Nat} {F F1 : List Bool} {k : Nat} (h : OwnSpec.consume1 F k = some F1)
    (hk : Kk.getD k 0 = 1) : Keep Kk F F1 := fun s ks hd => by
  obtain ⟨-, -, -, e⟩ := consume_spec h
  have : s ≠ k := fun q => by subst q; exact ks hk
  rw [e s this] at hd; exact hd

theorem tr_keep {Kk : List Nat} : ∀ (F F1 : List Bool) (es es1 : List Nat), TagsOK Kk es →
    OwnSpec.tr F es = some (F1, es1) → Keep Kk F F1 ∧ ∀ x ∈ es1, x < 4
  | F, F1, [], es1, _, h => by
    simp only [OwnSpec.tr, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨Keep.refl _ _, by simp⟩
  | F, F1, e :: es, es1, ht, h => by
    have ht' : TagsOK Kk es := fun x hx => ht x (by simp [hx])
    simp only [OwnSpec.tr] at h
    split at h
    · split at h
      · obtain ⟨⟨F2, es2⟩, h2, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨k, l⟩ := tr_keep _ _ _ _ ht' h2
        exact ⟨k, fun x hx => by rcases List.mem_cons.1 hx with rfl | hx; omega; exact l x hx⟩
      · cases h
    · split at h
      · obtain ⟨⟨F2, es2⟩, h2, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨k, l⟩ := tr_keep _ _ _ _ ht' h2
        exact ⟨k, fun x hx => by rcases List.mem_cons.1 hx with rfl | hx; omega; exact l x hx⟩
      · split at h
        · rename_i h4 _ h1
          obtain ⟨Fh, hc, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨⟨F2, es2⟩, h2, he⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
          obtain ⟨k, l⟩ := tr_keep _ _ _ _ ht' h2
          have := ht e (by simp) (by omega)
          exact ⟨(consume_keep hc (by omega)).trans k,
            fun x hx => by rcases List.mem_cons.1 hx with rfl | hx; omega; exact l x hx⟩
        · cases h

theorem finC_keep {Kk : List Nat} {ds : Option (List Nat)} : ∀ (F F2 : List Bool) (o : Nat) (es : List Nat), TagsOK Kk es →
    OwnSpec.finC ds F o es = some F2 → Keep Kk F F2
  | F, F2, _, [], _, h => by simp only [OwnSpec.finC, Option.some.injEq] at h; subst h; exact Keep.refl _ _
  | F, F2, o, e :: es, ht, h => by
    have ht' : TagsOK Kk es := fun x hx => ht x (by simp [hx])
    simp only [OwnSpec.finC] at h
    split at h
    · rename_i hc
      simp only [OwnSpec.own, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨F1, h1, h⟩ := Option.bind_eq_some_iff.1 h
      have := ht e (by simp) hc.1.1
      exact (consume_keep h1 (by omega)).trans (finC_keep _ _ _ _ ht' h)
    · exact finC_keep _ _ _ _ ht' h

theorem fin_keep {Kk : List Nat} {ds : Option (List Nat)} {F F2 : List Bool} {es es2 : List Nat} (ht : TagsOK Kk es)
    (h : OwnSpec.fin ds F es = some (F2, es2)) : Keep Kk F F2 ∧ ∀ x ∈ es2, x < 4 := by
  have key : ∀ F3, OwnSpec.finC ds F 0 es = some F3 →
      (if OwnSpec.finB ds F3 0 es = true then some (F3, OwnSpec.strip es) else none) = some (F2, es2) →
      Keep Kk F F2 ∧ ∀ x ∈ es2, x < 4 := by
    intro F3 h3 h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨finC_keep _ _ _ _ ht h3, fun x hx => ?_⟩
      simp only [OwnSpec.strip, List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx
      split <;> omega
    · simp at h
  cases ds with
  | none =>
    simp only [OwnSpec.fin, if_true, Option.bind_eq_some_iff] at h
    obtain ⟨F3, h3, h⟩ := h; exact key F3 h3 h
  | some l =>
    simp only [OwnSpec.fin, Option.bind_eq_some_iff] at h
    split at h
    · obtain ⟨F3, h3, h⟩ := Option.bind_eq_some_iff.1 h; exact key F3 h3 h
    · simp at h

theorem two_keep {Kk : List Nat} {a0 b0 y : List Bool × List Nat} (ha : TagsOK Kk a0.2) (hb : TagsOK Kk b0.2)
    (h : OwnSpec.two a0 b0 = some y) : Keep Kk b0.1 y.1 := by
  unfold OwnSpec.two at h
  split at h
  · exact (fin_keep (tags_append ha hb) h).1
  · cases h

theorem zip_max_lt : ∀ (a b : List Nat), (∀ x ∈ a, x < 4) → (∀ x ∈ b, x < 4) → ∀ x ∈ List.zipWith max a b, x < 4
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | x :: a, y :: b, ha, hb => by
    intro z hz
    simp only [List.zipWith_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · have := ha x (by simp); have := hb y (by simp); omega
    · exact zip_max_lt a b (fun z h => ha z (by simp [h])) (fun z h => hb z (by simp [h])) z hz

theorem join_plain {a b k : List Nat} (ha : ∀ x ∈ a, x < 4) (hb : ∀ x ∈ b, x < 4) (h : OwnSpec.join a b = some k) :
    ∀ x ∈ k, x < 4 := by
  unfold OwnSpec.join at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact hb
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact ha
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact zip_max_lt a b ha hb
      · cases h

theorem locE_tags {Kk : List Nat} (hK2 : ∀ s, Kk.getD s 0 ≤ 2) (s w : Nat) : TagsOK Kk (OwnSpec.locE Kk s w) := by
  intro x hx _
  simp only [OwnSpec.locE, List.mem_map] at hx; obtain ⟨j, -, rfl⟩ := hx
  have := hK2 (s + j)
  rw [show (Kk.getD (s + j) 0 + 4 * (s + j + 1)) / 4 - 1 = s + j by omega]; omega

mutual
theorem chk_keep {oc : OwnSpec.Cx} {D : List Sig} (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (hW : RsW oc) :
    ∀ {Γ S e ks}, TyN D Γ S e ks → S = none → ∀ F F' es, OwnSpec.chk oc e F = some (F', es) →
      Keep oc.K F F' ∧ TagsOK oc.K es
  | _, _, _, _, .const, _, F, F', es, h => by
    simp only [OwnSpec.chk, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨Keep.refl _ _, tags_plain (by simp)⟩
  | _, _, _, _, .loc _, _, F, F', es, h => by
    simp only [OwnSpec.chk] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨Keep.refl _ _, locE_tags hK2 _ _⟩
    · cases h
  | _, _, _, _, .bin _ _ ta tb, _, F, F', es, h => by
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a0, ha, b0, hb, y, hy, he⟩ := h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨ka, ta'⟩ := chk_keep hK2 hW ta rfl _ _ _ ha
    obtain ⟨kb, tb'⟩ := chk_keep hK2 hW tb rfl _ _ _ hb
    exact ⟨(ka.trans kb).trans (two_keep ta' tb' hy), tags_plain (by simp)⟩
  | _, _, _, _, .ite _ ta tb tt te, hS, F, F', es, h => by
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a0, ha, b0, hb, y, hy, t0, h1, t1, h2, e0, h3, e1, h4, k, hj, hk⟩ := h
    simp only [Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨ka, ta'⟩ := chk_keep hK2 hW ta rfl _ _ _ ha
    obtain ⟨kb, tb'⟩ := chk_keep hK2 hW tb rfl _ _ _ hb
    have ky := (ka.trans kb).trans (two_keep ta' tb' hy)
    obtain ⟨kt, tt'⟩ := chk_keep hK2 hW tt hS _ _ _ h1
    obtain ⟨ke, te'⟩ := chk_keep hK2 hW te hS _ _ _ h3
    obtain ⟨kt1, lt1⟩ := tr_keep _ _ _ _ tt' h2
    obtain ⟨ke1, le1⟩ := tr_keep _ _ _ _ te' h4
    exact ⟨keep_orF (ky.trans (kt.trans kt1)) (ky.trans (ke.trans ke1)), tags_plain (join_plain lt1 le1 hj)⟩
  | _, _, _, _, .letE tv _ _ _ tb, hS, F, F', es, h => by
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at h
    obtain ⟨v0, hv, v1, hv1, h⟩ := h
    split at h
    · obtain ⟨b0, hb0, hb1⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨kv, tv'⟩ := chk_keep hK2 hW tv rfl _ _ _ hv
      obtain ⟨kv1, -⟩ := tr_keep _ _ _ _ tv' hv1
      obtain ⟨kb, tb'⟩ := chk_keep hK2 hW tb hS _ _ _ hb0
      obtain ⟨kb1, lb1⟩ := tr_keep _ _ _ _ tb' hb1
      exact ⟨((kv.trans kv1).trans kb).trans kb1, tags_plain lb1⟩
    · cases h
  | _, _, _, _, .pair hl, _, F, F', es, h => by
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at h
    obtain ⟨⟨x1, x2⟩, hx, hf⟩ := h
    obtain ⟨k1, t1⟩ := lstA_keep hK2 hW hl _ _ _ _ _ hx (fun _ h => by simp at h)
    obtain ⟨k2, l2⟩ := fin_keep t1 hf
    exact ⟨k1.trans k2, tags_plain l2⟩
  | _, _, _, _, .call hl _, _, F, F', es, h => by
    simp only [OwnSpec.chk] at h
    split at h
    · rename_i P R hP hRr
      obtain ⟨⟨x1, x2⟩, hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨k1, t1⟩ := lstA_keep hK2 hW hl _ _ _ _ _ hx (fun _ h => by simp at h)
      exact ⟨k1.trans (fin_keep t1 hy).1, tags_plain fun x hx => by have := hW R (List.mem_of_getElem? hRr) x hx; omega⟩
    · cases h
  | _, _, _, _, .prim hl _ _, _, F, F', es, h => by
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨x1, x2⟩, hx, y, hy, he⟩ := h; simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨k1, t1⟩ := lstA_keep hK2 hW hl _ _ _ _ _ hx (fun _ h => by simp at h)
    refine ⟨k1.trans (fin_keep t1 hy).1, tags_plain ?_⟩
    simp only [List.mem_singleton]; intro x hx; subst hx; unfold OwnSpec.rk; split <;> omega
  | _, _, _, _, .cont _, hS, _, _, _, _ => by cases hS
theorem lstA_keep {oc : OwnSpec.Cx} {D : List Sig} (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (hW : RsW oc) :
    ∀ {Γ cs ks}, TyL D Γ cs ks → ∀ ds F es0 F' es', OwnSpec.lstA oc cs ds F es0 = some (F', es') → TagsOK oc.K es0 →
      Keep oc.K F F' ∧ TagsOK oc.K es'
  | _, _, _, .nil, ds, F, es0, F', es', h, h0 => by
    simp only [OwnSpec.lstA, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨Keep.refl _ _, h0⟩
  | _, _, _, .cons hn hr, ds, F, es0, F', es', h, h0 => by
    simp only [OwnSpec.lstA, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h
    · obtain ⟨k1, t1⟩ := chk_keep hK2 hW hn rfl _ _ _ hx
      obtain ⟨k2, t2⟩ := lstA_keep hK2 hW hr _ _ _ _ _ h (tags_append h0 t1)
      exact ⟨k1.trans k2, t2⟩
    · cases h
end

end NanoMain
