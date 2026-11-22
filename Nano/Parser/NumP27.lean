/- Nano/Parser/NumP27: the late-slot check (`NumSpec.lateOk`): `u73` marks the late slots of a body's lets, `u74` checks
the shifts' left operands; both scan the serialization node by node (`u77`). -/
import Nano.Parser.NumP26
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem nodes_succ (k : Nat) (e : Nd) : NumSpec.nodes (k + 1) e = e :: (kids e).flatMap (NumSpec.nodes k) := by
  cases e <;> rfl

/-- one node: its header is skipped, its children join the pending nodes -/
theorem u77_node {np : Nat} {x : Buf} {e : Nd} {r : Buf} {i k : Nat} (hx : x.drop i = e.ser ++ r) (hnb : NB np e)
    (hl : x.length < 2 ^ 64) (hk : k + 1 + (kids e).length < 2 ^ 64) :
    u77 x (u i) (u (k + 1)) = (u (i + (hdr e).length), u (k + (kids e).length)) := by
  have hil := drop_len hx (ser_pos e)
  unfold u77
  rw [ser_hdr e, List.append_assoc] at hx
  have hil2 : i + (hdr e).length ≤ x.length := by
    have := drop_len hx (hdr_pos e); omega
  have r0 := rd hx (k := 0) (by have := hdr_pos e; omega) (by have := hdr_pos e; omega)
  rw [Nat.add_zero] at r0
  rw [r0]
  have hsub' : u (k + 1) - u 1 = u k := by rw [u_sub (by omega) (by omega)]; rfl
  have ha : ∀ m : Nat, u i + (OfNat.ofNat m : UInt64) = u (i + m) := fun m => by rw [lit, u_add]
  cases e with
  | const v => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | loc s w => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | bin op a b => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | ite c a b t el => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | letE s w v b => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | pair cs =>
    have r1 := rd hx (k := 1) (by simp [hdr]) (by simp [hdr] at hil2; omega)
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at r1
    simp only [hdr, kids, List.getD_cons_zero]; simp; rw [ha 1, r1]; simp only [lit, u_add, hsub', and_self]
  | call id as =>
    have r2 := rd hx (k := 2) (by simp [hdr]) (by simp [hdr] at hil2; omega)
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at r2
    simp only [hdr, kids, List.getD_cons_zero]; simp; rw [ha 2, r2]; simp only [lit, u_add, hsub', and_self]
  | prim pn as =>
    have r1 := rd hx (k := 1) (by simp [hdr]) (by simp [hdr] at hil2; omega)
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at r1
    obtain ⟨hp, hpa, -⟩ := hnb
    have hg : g33 (u pn) = u as.length := by
      rw [hpa]; simp only [toU]; unfold u; simp
    simp only [hdr, kids, List.getD_cons_zero]; simp; rw [ha 1, r1, hg]; simp only [lit, u_add, hsub', and_self]
  | loop z s => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | cont e => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]

/-- the check at one node: a shift's left slot is unmarked -/
def SC74 (F : Buf) : Nd → Prop
  | .bin op (.loc s _) _ => NumSpec.isShift op = true → F.getD s 0 = 0
  | _ => True

/-- the facts about the pending nodes that a scan's step needs -/
theorem scan_step {np : Nat} {x : Buf} {e : Nd} {es : List Nd} {r : Buf} {i : Nat}
    (hx : x.drop i = serL (e :: es) ++ r) (hnb : ∀ c ∈ e :: es, NB np c) (hl : x.length < 2 ^ 23) :
    x.drop i = e.ser ++ (serL es ++ r) ∧ x.drop (i + (hdr e).length) = serL (kids e ++ es) ++ r ∧
      (∀ c ∈ kids e ++ es, NB np c) ∧ es.length + 1 + (kids e).length < 2 ^ 64 ∧ i + e.ser.length ≤ x.length := by
  have hx' : x.drop i = e.ser ++ (serL es ++ r) := by rw [hx]; simp [serL]
  have hil := drop_len hx (by simp [serL]; have := ser_pos e; omega)
  have h1 := len_le_serL (kids e ++ es)
  rw [serL_append] at h1
  have h2 := ser_len_kids e
  simp only [serL, List.length_append] at hil h1
  refine ⟨hx', ?_, ?_, by omega, by omega⟩
  · rw [serL_append, List.append_assoc]; apply drop_shift; rw [hx', ser_hdr e]; simp
  · intro c hc; rcases List.mem_append.1 hc with hc | hc
    · exact nb_kids (hnb e (by simp)) c hc
    · exact hnb c (by simp [hc])

/-- from the nodes of the kids and the node itself to the nodes of the node -/
theorem nodes_all {P : Nd → Prop} {e : Nd} {es : List Nd} (he : P e)
    (hk : ∀ e' ∈ kids e ++ es, ∀ k, ∀ c ∈ NumSpec.nodes k e', P c) :
    ∀ e' ∈ e :: es, ∀ k, ∀ c ∈ NumSpec.nodes k e', P c := by
  intro e' he' k c hc
  rcases List.mem_cons.1 he' with rfl | he'
  · cases k with
    | zero => simp [NumSpec.nodes] at hc
    | succ k =>
      rw [nodes_succ] at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact he
      · obtain ⟨c', hc', hc⟩ := List.mem_flatMap.1 hc
        exact hk c' (by simp [hc']) k c hc
  · exact hk e' (by simp [he']) k c hc

theorem u74_ok {np : Nat} {x F : Buf} (hl : x.length < 2 ^ 23) : ∀ (n : Nat) (es : List Nd) (r : Buf) (i : Nat),
    x.drop i = serL es ++ r → (∀ e ∈ es, NB np e) →
    u74 n x F (u i) (u es.length) = 1 → ∀ e ∈ es, ∀ k, ∀ c ∈ NumSpec.nodes k e, SC74 F c
  | 0, _, _, _, _, _, h => by simp [u74] at h
  | n + 1, [], r, i, _, _, _ => by simp
  | n + 1, e :: es, r, i, hx, hnb, h => by
    obtain ⟨hx', hx2, hnb2, hk, hil⟩ := scan_step hx hnb hl
    have hne : (u (es.length + 1) == 0) = false := by rw [u0, ueq (by omega) (by omega)]; simp
    rw [List.length_cons] at h
    simp only [u74] at h
    rw [if_neg (kne hne), u77_node hx' (hnb e (by simp)) (by omega) hk] at h
    dsimp only at h
    have ih := u74_ok (F := F) hl n (kids e ++ es) r _ hx2 hnb2
    rw [List.length_append, Nat.add_comm (kids e).length] at ih
    have hrd : ∀ m, m < e.ser.length → bget x (u i + u m) = e.ser.getD m 0 := by
      intro m hm; rw [uadd, rd hx' hm (by omega)]
    rw [u34_ok hx' (by omega) (hnb e (by simp))] at h
    have hgo : u74 n x F (u (i + (hdr e).length)) (u (es.length + (kids e).length)) = 1 → SC74 F e →
        ∀ e' ∈ e :: es, ∀ k, ∀ c ∈ NumSpec.nodes k e', SC74 F c := fun h1 h2 => nodes_all h2 (ih h1)
    cases e with
    | bin op a b =>
      cases hsh : NumSpec.isShift op
      · simp only [shN, hsh, w2, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false] at h
        refine hgo h ?_
        cases a <;> simp [SC74, hsh]
      · simp only [shN, hsh, w2, show ((1 : UInt64) == 1) = true from rfl, if_true] at h
        have h2 : bget x (u i + 2) = (hdr a).getD 0 0 := by
          rw [show (2 : UInt64) = u 2 from rfl, hrd 2 (by simp [Nd.ser]; have := ser_pos a; omega)]
          simp only [Nd.ser, List.getD_cons_succ]; rw [ser_hdr]; have := hdr_pos a
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 0 < (hdr a).length by omega)]
        rw [h2] at h
        cases a with
        | loc s w =>
          simp only [hdr, List.getD_cons_zero, show ((2 : UInt64) == 2) = true from rfl, if_true] at h
          have h3 : bget x (u i + 3) = u s := by
            rw [show (3 : UInt64) = u 3 from rfl, hrd 3 (by simp [Nd.ser])]; simp [Nd.ser, toU]
          have hnb0 := hnb (.bin op (.loc s w) b) (by simp); simp only [NB] at hnb0
          rw [h3, bget_u _ (by omega)] at h
          by_cases h0 : F.getD s 0 = 0
          · rw [if_pos (by rw [h0]; rfl)] at h; exact hgo h (fun _ => h0)
          · rw [if_neg (by simpa using h0)] at h; exact absurd h (by decide)
        | _ => simp only [hdr, List.getD_cons_zero] at h; rw [if_neg (by decide)] at h; exact hgo h trivial
    | _ => simp only [shN, w2, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false] at h
           exact hgo h trivial

/-! ## marking -/
/-- F' keeps F's length and its marks -/
def Mk (F F' : Buf) : Prop := F'.length = F.length ∧ ∀ p, F.getD p 0 ≠ 0 → F'.getD p 0 ≠ 0

theorem Mk.rfl' (F : Buf) : Mk F F := ⟨rfl, fun _ h => h⟩
theorem Mk.trans {F F' F'' : Buf} (h1 : Mk F F') (h2 : Mk F' F'') : Mk F F'' :=
  ⟨by rw [h2.1, h1.1], fun p h => h2.2 p (h1.2 p h)⟩

theorem mk_set (F : Buf) (j : UInt64) : Mk F (bset F j 1) := by
  refine ⟨by simp [bset], fun p h => ?_⟩
  simp only [bset, getD_set]
  split
  · exact (by decide : (1 : UInt64) ≠ 0)
  · exact h

theorem u78_mono : ∀ (n : Nat) (F : Buf) (s j k : UInt64), Mk F (u78 n F s j k).1
  | 0, F, _, _, _ => Mk.rfl' F
  | n + 1, F, s, j, k => by
    simp only [u78]
    split
    · split
      · exact (mk_set F _).trans (u78_mono n _ s _ k)
      · exact Mk.rfl' F
    · exact Mk.rfl' F

theorem u78_ok : ∀ (n : Nat) (F : Buf) (s j k : Nat), s + k < 2 ^ 62 → F.length < 2 ^ 62 →
    (u78 n F (u s) (u j) (u k)).2 = 1 → ∀ m, j ≤ m → m < k → (u78 n F (u s) (u j) (u k)).1.getD (s + m) 0 ≠ 0
  | 0, _, _, _, _, _, _, h => by simp [u78] at h
  | n + 1, F, s, j, k, hs, hF, h => by
    intro m hjm hmk
    simp only [u78] at h ⊢
    have hc : u j < u k := by rw [ult (by omega) (by omega)]; omega
    rw [if_pos hc] at h ⊢
    by_cases h2 : s + j < F.length
    · have hc2 : u s + u j < bsize F := by rw [uadd, bsize_u, ult (by omega) (by omega)]; exact h2
      rw [if_pos hc2] at h ⊢
      have e1 : u j + 1 = u (j + 1) := by rw [u1, uadd]
      rw [e1] at h ⊢
      have hF' : (bset F (u s + u j) 1).length = F.length := by simp [bset]
      by_cases hm : m = j
      · subst hm
        apply (u78_mono n _ (u s) _ (u k)).2
        rw [uadd, bset_u _ (by omega), getD_set, if_pos ⟨rfl, h2⟩]; decide
      · exact u78_ok n _ s (j + 1) k hs (by omega) h m (by omega) hmk
    · have hc2 : ¬ (u s + u j < bsize F) := by rw [uadd, bsize_u, ult (by omega) (by omega)]; exact h2
      rw [if_neg hc2] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

theorem u76_mono {x : Buf} : ∀ (n : Nat) (F w : Buf) (q s j k : UInt64), Mk F (u76 n x F w q s j k).1
  | 0, F, _, _, _, _, _ => Mk.rfl' F
  | n + 1, F, w, q, s, j, k => by
    simp only [u76]
    split
    · try dsimp only
      split
      · exact Mk.rfl' F
      · split
        · exact Mk.rfl' F
        · split
          · generalize hU : u78 16777216 F s j (j + 1) = U
            obtain ⟨F1, ok⟩ := U
            have hm := u78_mono 16777216 F s j (j + 1); rw [hU] at hm
            dsimp only
            split
            · exact hm.trans (u76_mono n _ _ _ s _ k)
            · exact hm
          · exact u76_mono n _ _ _ s _ k
    · exact Mk.rfl' F

theorem u76_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) (f0 s : Nat) :
    ∀ (n : Nat) (cs : List Nd) (F w : Buf) (q j : Nat) (r : Buf), x.drop q = serL cs ++ r →
    (∀ c ∈ cs, NB np c ∧ c.ser.length ≤ f0) → 0 < q → w.length < 2 ^ 62 → F.length < 2 ^ 62 →
    s + j + cs.length < 2 ^ 62 →
    (u76 n x F w (u q) (u s) (u j) (u (j + cs.length))).2.2 = 1 →
    (∀ ci ∈ (cs.zipIdx j).filter (fun ci => NumSpec.spineLet f0 ci.1),
        (u76 n x F w (u q) (u s) (u j) (u (j + cs.length))).1.getD (s + ci.2) 0 ≠ 0) ∧
      (u76 n x F w (u q) (u s) (u j) (u (j + cs.length))).2.1.length < 2 ^ 62
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [u76] at h
  | n + 1, [], F, w, q, j, r, _, _, _, hw, _, _, _ => by
    have : ¬ (u j < u (j + ([] : List Nd).length)) := by rw [ult (by simp; omega) (by simp; omega)]; simp
    simp only [u76]; rw [if_neg this]; exact ⟨by simp, hw⟩
  | n + 1, c :: cs, F, w, q, j, r, hx, hcs, hq, hw, hF, hsj, h => by
    obtain ⟨hnc, hfc⟩ := hcs c (by simp)
    have hx' : x.drop q = c.ser ++ (serL cs ++ r) := by rw [hx]; simp [serL]
    have hx2 := drop_shift hx'
    have hcl := drop_len hx' (ser_pos c)
    simp only [List.length_cons] at hsj h ⊢
    have hc : u j < u (j + (cs.length + 1)) := by rw [ult (by omega) (by omega)]; omega
    simp only [u76] at h ⊢
    rw [if_pos hc] at h ⊢
    obtain ⟨hw1, h17⟩ := u17_ok hl hx' hfc hnc hq hw
    generalize u17 x w (u q) = V at hw1 h17 h ⊢
    obtain ⟨w1, hh⟩ := V
    dsimp only at hw1 h17 h ⊢
    rcases h17 with h2 | hsl
    · subst h2; rw [if_pos (keq rfl)] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
    subst hsl
    rw [if_neg (kne (w2_ne2 _))] at h ⊢
    rcases u15_ok (by omega) hx' hnc with h15 | ⟨h15, -⟩
    · rw [h15, if_pos (keq rfl)] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
    have hne : (u (q + c.ser.length) == 0) = false := by
      rw [u0, ueq (by omega) (by omega)]; exact decide_eq_false (by omega)
    rw [h15, if_neg (kne hne)] at h ⊢
    have e1 : u j + 1 = u (j + 1) := by rw [u1, uadd]
    have e2 : u (j + (cs.length + 1)) = u (j + 1 + cs.length) := by congr 1; omega
    rw [e2] at h ⊢
    have hzip : (c :: cs).zipIdx j = (c, j) :: cs.zipIdx (j + 1) := by simp [List.zipIdx_cons]
    rw [hzip, e1]
    rw [e1] at h
    cases hsp : NumSpec.spineLet f0 c
    · simp only [hsp, w2, Bool.false_eq_true, if_false, show ((0 : UInt64) == 1) = false from rfl] at h ⊢
      have ih := u76_ok hl f0 s n cs F w1 (q + c.ser.length) (j + 1) r hx2 (fun c' h' => hcs c' (by simp [h']))
        (by omega) hw1 hF (by omega) h
      refine ⟨fun ci hci => ?_, ih.2⟩
      simp only [List.filter_cons, hsp] at hci
      exact ih.1 ci hci
    · simp only [hsp, w2, if_true, show ((1 : UInt64) == 1) = true from rfl] at h ⊢
      have h78 := u78_ok 16777216 F s j (j + 1) (by omega) hF
      have hm78 := u78_mono 16777216 F (u s) (u j) (u (j + 1))
      generalize u78 16777216 F (u s) (u j) (u (j + 1)) = M at h78 hm78 h ⊢
      obtain ⟨F1, ok⟩ := M
      dsimp only at h78 hm78 h ⊢
      by_cases hok : ok = 1
      · subst hok
        rw [if_pos (keq rfl)] at h ⊢
        have ih := u76_ok hl f0 s n cs F1 w1 (q + c.ser.length) (j + 1) r hx2 (fun c' h' => hcs c' (by simp [h']))
          (by omega) hw1 (by rw [hm78.1]; exact hF) (by omega) h
        refine ⟨fun ci hci => ?_, ih.2⟩
        simp only [List.filter_cons, hsp, if_true, List.mem_cons] at hci
        rcases hci with rfl | hci
        · exact (u76_mono n F1 w1 _ (u s) _ _).2 _ (h78 rfl j (by omega) (by omega))
        · exact ih.1 ci hci
      · rw [if_neg (by simpa using hok)] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

theorem u75_mono {x : Buf} (F w : Buf) (q s wd : UInt64) : Mk F (u75 x F w q s wd).1 := by
  unfold u75
  split
  · exact u76_mono _ _ _ _ _ _ _
  · generalize u17 x w q = V
    obtain ⟨w1, h⟩ := V
    dsimp only
    split
    · exact Mk.rfl' F
    · split
      · have := u78_mono 16777216 F s 0 wd
        generalize u78 16777216 F s 0 wd = M at this
        obtain ⟨F1, ok⟩ := M
        exact this
      · exact Mk.rfl' F

/-- `u75`: the late slots of `let s := v` -/
theorem u75_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) (f0 : Nat) {v : Nd} {q : Nat} {r : Buf} {s wd : Nat}
    (bd : Nd) (hx : x.drop q = v.ser ++ r) (hnb : NB np v) (hf : v.ser.length ≤ f0) (hq : 0 < q) {F w : Buf}
    (hw : w.length < 2 ^ 62) (hF : F.length < 2 ^ 62) (hs : s < 2 ^ 32) (hwd : wd < 2 ^ 32) :
    (u75 x F w (u q) (u s) (u wd)).2.2 = 1 →
      (∀ p ∈ NumSpec.late f0 (.letE s wd v bd), (u75 x F w (u q) (u s) (u wd)).1.getD p 0 ≠ 0) ∧
      (u75 x F w (u q) (u s) (u wd)).2.1.length < 2 ^ 62 := by
  have hcl := drop_len hx (ser_pos v)
  unfold u75
  rw [tag_rd hx (by omega)]
  cases v with
  | pair cs =>
    simp only [hdr, List.getD_cons_zero, show ((6 : UInt64) == 6) = true from rfl, if_true]
    simp only [NB] at hnb
    obtain ⟨hcsl, hcs⟩ := hnb
    have h1 : bget x (u q + 1) = u cs.length := by
      rw [tag1_rd hx (by omega) (by simp [hdr])]; simp [hdr]
    have hx2 : x.drop (q + 2) = serL cs ++ r := by
      have h0 : x.drop q = [6, u cs.length] ++ (serL cs ++ r) := by rw [hx]; simp [Nd.ser, toU]
      simpa using drop_shift h0
    rw [h1, show u q + 2 = u (q + 2) by rw [u2, uadd]]
    have hf' : (serL cs).length + 2 ≤ f0 := by simp [Nd.ser] at hf; omega
    intro h
    have := u76_ok hl f0 s 16777216 cs F w (q + 2) 0 r hx2
      (fun c hc => ⟨(nbl_iff cs).1 hcs c hc, by have := mem_serL_len hc; omega⟩) (by omega) hw hF (by omega)
      (by rw [Nat.zero_add]; exact h)
    rw [Nat.zero_add] at this
    refine ⟨fun p hp => ?_, this.2⟩
    simp only [NumSpec.late, List.mem_map] at hp
    obtain ⟨ci, hci, rfl⟩ := hp
    exact this.1 ci (by simpa using hci)
  | _ =>
    simp only [hdr, List.getD_cons_zero]
    rw [if_neg (by decide)]
    obtain ⟨hw1, h17⟩ := u17_ok hl hx hf hnb hq hw
    generalize u17 x w (u q) = V at hw1 h17 ⊢
    obtain ⟨w1, hh⟩ := V
    dsimp only at hw1 h17 ⊢
    rcases h17 with h2 | hsl
    · subst h2; rw [if_pos (keq rfl)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
    subst hsl
    rw [if_neg (kne (w2_ne2 _))]
    cases hsp : NumSpec.spineLet f0 _
    · simp only [w2, Bool.false_eq_true, if_false, show ((0 : UInt64) == 1) = false from rfl]
      intro _; refine ⟨fun p hp => ?_, hw1⟩
      simp [NumSpec.late, hsp] at hp
    · simp only [w2, if_true, show ((1 : UInt64) == 1) = true from rfl]
      have h78 := u78_ok 16777216 F s 0 wd (by omega) hF
      rw [show u 0 = (0 : UInt64) from rfl] at h78
      generalize u78 16777216 F (u s) 0 (u wd) = M at h78 ⊢
      obtain ⟨F1, ok⟩ := M
      dsimp only at h78 ⊢
      intro h
      refine ⟨fun p hp => ?_, hw1⟩
      simp only [NumSpec.late, hsp, if_true, List.mem_map, List.mem_range] at hp
      obtain ⟨m, hm, rfl⟩ := hp
      exact h78 h m (Nat.zero_le _) hm

theorem u73_mono {x : Buf} : ∀ (n : Nat) (F w : Buf) (i k : UInt64), Mk F (u73 n x F w i k).1
  | 0, F, _, _, _ => Mk.rfl' F
  | n + 1, F, w, i, k => by
    simp only [u73]
    split
    · exact Mk.rfl' F
    · have hE : Mk F (if bget x i == 5 then u75 x F w (i + 3) (bget x (i + 1)) (bget x (i + 2)) else (F, (w, 1))).1 := by
        split
        · exact u75_mono _ _ _ _ _
        · exact Mk.rfl' F
      generalize (if bget x i == 5 then u75 x F w (i + 3) (bget x (i + 1)) (bget x (i + 2)) else (F, (w, 1))) = E at hE
      obtain ⟨F1, w1, ok⟩ := E
      dsimp only at hE ⊢
      split
      · exact hE.trans (u73_mono n _ _ _ _)
      · exact hE

theorem u73_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) (f0 : Nat) :
    ∀ (n : Nat) (es : List Nd) (r : Buf) (i : Nat) (F w : Buf),
    x.drop i = serL es ++ r → (∀ e ∈ es, NB np e ∧ e.ser.length ≤ f0) → 0 < i → w.length < 2 ^ 62 →
    F.length < 2 ^ 62 → (u73 n x F w (u i) (u es.length)).2.2 = 1 →
    (∀ e ∈ es, ∀ k, ∀ c ∈ NumSpec.nodes k e, ∀ p ∈ NumSpec.late f0 c, (u73 n x F w (u i) (u es.length)).1.getD p 0 ≠ 0) ∧
      (u73 n x F w (u i) (u es.length)).2.1.length < 2 ^ 62
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [u73] at h
  | n + 1, [], r, i, F, w, _, _, _, hw, _, _ => by simp [u73, show u 0 = 0 from rfl, hw]
  | n + 1, e :: es, r, i, F, w, hx, hnb, hi, hw, hF, h => by
    obtain ⟨hx', hx2, hnb2, hk, hil⟩ := scan_step hx (fun c hc => (hnb c hc).1) hl
    have hne : (u (es.length + 1) == 0) = false := by rw [u0, ueq (by omega) (by omega)]; simp
    have hrd : ∀ m, m < e.ser.length → bget x (u i + u m) = e.ser.getD m 0 := by
      intro m hm; rw [uadd, rd hx' hm (by omega)]
    rw [List.length_cons] at h ⊢
    simp only [u73] at h ⊢
    rw [if_neg (kne hne), u77_node hx' (hnb e (by simp)).1 (by omega) hk] at h ⊢
    have hnb3 : ∀ c ∈ kids e ++ es, NB np c ∧ c.ser.length ≤ f0 := by
      intro c hc; refine ⟨hnb2 c hc, ?_⟩
      rcases List.mem_append.1 hc with hc | hc
      · have := kid_len hc; have := (hnb e (by simp)).2; omega
      · exact (hnb c (by simp [hc])).2
    -- the step at e
    have hE : ∀ E : Buf × (Buf × UInt64),
        (if bget x (u i) == 5 then u75 x F w (u i + 3) (bget x (u i + 1)) (bget x (u i + 2)) else (F, (w, 1))) = E →
        E.2.2 = 1 → (∀ p ∈ NumSpec.late f0 e, E.1.getD p 0 ≠ 0) ∧ E.2.1.length < 2 ^ 62 ∧ Mk F E.1 := by
      intro E hE1 hok
      have hmk : Mk F E.1 := by
        rw [← hE1]; split
        · exact u75_mono _ _ _ _ _
        · exact Mk.rfl' F
      refine ⟨?_, ?_, hmk⟩ <;> rw [← hE1] at hok ⊢ <;> rw [tag_rd hx' (by omega)] at hok ⊢
      all_goals
        cases e with
        | letE s wd v bd =>
          have hnbe := (hnb (.letE s wd v bd) (by simp)).1
          have hfe := (hnb (.letE s wd v bd) (by simp)).2
          simp only [NB] at hnbe
          obtain ⟨hs, hwd, hnv, -⟩ := hnbe
          have h1 : bget x (u i + 1) = u s := by rw [show (1 : UInt64) = u 1 from rfl, hrd 1 (by simp [Nd.ser])]; simp [Nd.ser, toU]
          have h2 : bget x (u i + 2) = u wd := by rw [show (2 : UInt64) = u 2 from rfl, hrd 2 (by simp [Nd.ser])]; simp [Nd.ser, toU]
          have hx3 : x.drop (i + 3) = v.ser ++ (bd.ser ++ (serL es ++ r)) := by
            have h0 : x.drop i = [5, u s, u wd] ++ (v.ser ++ (bd.ser ++ (serL es ++ r))) := by rw [hx']; simp [Nd.ser, toU]
            simpa using drop_shift h0
          simp only [hdr, List.getD_cons_zero, show ((5 : UInt64) == 5) = true from rfl, if_true, h1, h2,
            show u i + 3 = u (i + 3) by rw [u3, uadd]] at hok ⊢
          have := u75_ok hl f0 bd hx3 hnv (by simp [Nd.ser] at hfe; omega) (by omega) hw hF hs hwd hok
          first | exact this.1 | exact this.2
        | _ =>
          simp only [hdr, List.getD_cons_zero] at hok ⊢
          rw [if_neg (by decide)] at hok ⊢
          first | (intro p hp; simp [NumSpec.late] at hp) | exact hw
    generalize hE1 : (if bget x (u i) == 5 then u75 x F w (u i + 3) (bget x (u i + 1)) (bget x (u i + 2)) else (F, (w, 1))) = E
      at h ⊢
    obtain ⟨F1, w1, ok⟩ := E
    dsimp only at h ⊢
    by_cases hok : ok = 1
    · subst hok
      rw [if_pos (keq rfl)] at h ⊢
      obtain ⟨he1, hw1, hmk⟩ := hE _ hE1 rfl
      simp only at he1 hw1 hmk
      have ih := u73_ok hl f0 n (kids e ++ es) r _ F1 w1 hx2 hnb3 (by omega) hw1 (by rw [hmk.1]; exact hF)
      rw [List.length_append, Nat.add_comm (kids e).length] at ih
      have ih' := ih h
      refine ⟨nodes_all (P := fun c => ∀ p ∈ NumSpec.late f0 c,
        (u73 n x F1 w1 (u (i + (hdr e).length)) (u (es.length + (kids e).length))).1.getD p 0 ≠ 0)
        (fun p hp => (u73_mono n F1 w1 _ _).2 p (he1 p hp)) ih'.1, ih'.2⟩
    · rw [if_neg (by simpa using hok)] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

/-- **the late-slot check**: both scans of a body accept only if `lateOk` holds -/
theorem late_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) {e : Nd} {r : Buf} {i : Nat}
    (hx : x.drop i = e.ser ++ r) (hnb : NB np e) (hf : e.ser.length ≤ 2 ^ 24) (hi : 0 < i) {F w : Buf}
    (hw : w.length < 2 ^ 62) (hF : F.length < 2 ^ 62) :
    (u73 16777216 x F w (u i) 1).2.2 = 1 → u74 16777216 x (u73 16777216 x F w (u i) 1).1 (u i) 1 = 1 →
      NumSpec.lateOk (2 ^ 24) e = true := by
  intro h1 h2
  have hx' : x.drop i = serL [e] ++ r := by simpa [serL] using hx
  have m := u73_ok (np := np) hl (2 ^ 24) 16777216 [e] r i F w hx' (by simpa using ⟨hnb, hf⟩) hi hw hF h1
  have c := u74_ok (np := np) (F := (u73 16777216 x F w (u i) 1).1) hl 16777216 [e] r i hx' (by simpa using hnb) h2
  unfold NumSpec.lateOk
  rw [List.all_eq_true]
  intro n hn
  have hc := c e (by simp) _ n hn
  generalize hP : (NumSpec.nodes (2 ^ 24) e).flatMap (NumSpec.late (2 ^ 24)) = P
  have hP' : ∀ p ∈ P, (u73 16777216 x F w (u i) 1).1.getD p 0 ≠ 0 := by
    rw [← hP]; intro p hp
    obtain ⟨c', hc', hp⟩ := List.mem_flatMap.1 hp
    exact m.1 e (by simp) _ c' hc' p hp
  revert hc
  match n with
  | .bin op (.loc s _) _ =>
    intro hc
    dsimp only
    cases hs : NumSpec.isShift op
    · simp
    · cases hm : P.contains s
      · simp
      · exfalso; exact hP' s (by simpa using hm) (hc hs)
  | .const _ => intro _; rfl
  | .loc _ _ => intro _; rfl
  | .bin _ (.const _) _ => intro _; rfl
  | .bin _ (.bin _ _ _) _ => intro _; rfl
  | .bin _ (.ite _ _ _ _ _) _ => intro _; rfl
  | .bin _ (.letE _ _ _ _) _ => intro _; rfl
  | .bin _ (.pair _) _ => intro _; rfl
  | .bin _ (.call _ _) _ => intro _; rfl
  | .bin _ (.prim _ _) _ => intro _; rfl
  | .bin _ (.loop _ _) _ => intro _; rfl
  | .bin _ (.cont _) _ => intro _; rfl
  | .ite _ _ _ _ _ => intro _; rfl
  | .letE _ _ _ _ => intro _; rfl
  | .pair _ => intro _; rfl
  | .call _ _ => intro _; rfl
  | .prim _ _ => intro _; rfl
  | .loop _ _ => intro _; rfl
  | .cont _ => intro _; rfl

end NumP
