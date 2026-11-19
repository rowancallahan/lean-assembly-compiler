/- Machine bridge (Opus box E): every template instruction is `GoodX` (registers < 32, immediates in range), so
Gen's words for the defs are the Sail layer's words (`encG_encJX`).  Needs the slot bounds (ScV, nl < 251, p ≤ nl)
and the BIN op range (Gen checks it in CG; here a hypothesis `OpV`). -/
import Nano.V2Self.Proof.Machine.SimXB
import Nano.V2Self.Proof.Machine.NoW
namespace Templates
open CallProbe ParSpec

def GL (l : List J) : Prop := ∀ i ∈ l, GoodX i

theorem GL.app {a b : List J} (ha : GL a) (hb : GL b) : GL (a ++ b) := by
  intro i hi; rcases List.mem_append.mp hi with h | h; exact ha i h; exact hb i h

theorem GL.nil : GL [] := fun _ h => absurd h (by simp)

theorem slotOff_rng {p nl k : Nat} (hk : k < nl) (hnl : nl < 251) (hp : p ≤ nl) :
    -2048 ≤ slotOff p k ∧ slotOff p k < 2048 := by
  unfold slotOff; split <;> omega

theorem offOf_rng {p nl k : Nat} (hk : k < nl) (hnl : nl < 251) (hp : p ≤ nl) :
    -2048 ≤ offOf p k ∧ offOf p k < 2048 := by
  unfold offOf; split <;> omega

theorem liB_good (d v : Nat) (hd : d < 32) : ∀ k, k ≤ 8 → GL (liB d v k)
  | 0, _ => GL.nil
  | k + 1, hk => by
    refine GL.app (liB_good d v hd k (by omega)) ?_
    intro i hi; simp [liJ] at hi
    have : (v / 2 ^ (56 - 8 * k)) % 256 < 256 := Nat.mod_lt _ (by decide)
    rcases hi with rfl | rfl <;> simp [GoodX, GoodW, hd] <;> omega

theorem liT_good (d : Nat) (v : UInt64) (hd : d < 32) : GL (liT d v) := by
  unfold liT; split
  · intro i hi; simp at hi; subst hi; simp [GoodX, GoodW, hd]; omega
  · intro i hi; simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · simp [GoodX, GoodW, hd]
    · exact liB_good d v.toNat hd 8 (by omega) i hi

theorem push_good (r : Nat) (o : Int) (hr : r < 32) : GL (push r o) := by
  intro i hi; simp [push] at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp [GoodX, GoodW, hr]

theorem popN_good (p nl k0 : Nat) (hnl : nl < 251) (hp : p ≤ nl) : ∀ w, k0 + w ≤ nl → GL (popN p k0 w)
  | 0, _ => GL.nil
  | w + 1, h => by
    refine GL.app ?_ (popN_good p nl k0 hnl hp w (by omega))
    have := slotOff_rng (p := p) (k := k0 + w) (by omega) hnl hp
    intro i hi; simp [popSlot] at hi; rcases hi with rfl | rfl | rfl <;> simp [GoodX, GoodW] <;> omega

theorem localT_good (tgt p nl : Nat) (hnl : nl < 251) (hp : p ≤ nl) : ∀ k q w, k + w ≤ nl → GL (localT tgt p k q w)
  | _, _, 0, _ => GL.nil
  | k, q, w + 1, h => by
    refine GL.app (GL.app ?_ (push_good 5 _ (by omega))) (localT_good tgt p nl hnl hp (k + 1) (q + 5) w (by omega))
    have := offOf_rng (p := p) (k := k) (by omega) hnl hp
    intro i hi; simp at hi; subst hi; simp [GoodX, GoodW]; omega

theorem copy_good (p q : Nat) (hp : p < 251) (hq : q < 251) : ∀ k, k ≤ q → GL (copy p q k)
  | 0, _ => GL.nil
  | k + 1, h => by
    refine GL.app (copy_good p q hp hq k (by omega)) ?_
    intro i hi; simp [copyJ] at hi; rcases hi with rfl | rfl <;> simp [GoodX, GoodW] <;> omega

theorem lst_good {l : List J} (h : ∀ i ∈ l, GoodX i) : GL l := h

theorem bnewT_good (tgt q κ : Nat) : GL (bnewT tgt q κ) := by
  unfold bnewT
  refine GL.app (by intro i hi; simp at hi; subst hi; simp [GoodX, GoodW]) (GL.app (liT_good 6 _ (by omega))
    (GL.app (by intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp [GoodX, GoodW])
    (GL.app (liT_good 7 _ (by omega)) (GL.app (by intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;>
      simp [GoodX, GoodW]) (push_good 5 _ (by omega))))))

theorem primT_good (K : SC) (pn q : Nat) : GL (primT K pn q) := by
  unfold primT
  repeat' split
  all_goals first
    | exact push_good _ _ (by omega)
    | exact bnewT_good _ _ _
    | (intro i hi; simp [rdT, bsizeT, bgetT, bsetT, bpushT] at hi
       rcases hi with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [GoodX, GoodW])
    | (intro i hi; simp [rdT, bsizeT, bgetT, bsetT, bpushT] at hi
       rcases hi with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [GoodX, GoodW])
    | (intro i hi; simp [rdT, bsizeT, bgetT, bsetT, bpushT] at hi
       rcases hi with h | h | h | h | h | h | h | h | h <;> subst h <;> simp [GoodX, GoodW])
    | (intro i hi; simp [rdT, bsizeT, bgetT, bsetT, bpushT] at hi
       rcases hi with h | h | h | h | h | h <;> subst h <;> simp [GoodX, GoodW])
    | (intro i hi; simp [rdT, bsizeT, bgetT, bsetT, bpushT] at hi
       rcases hi with h | h | h <;> subst h <;> simp [GoodX, GoodW])


theorem ifHeadG_good (c lt : Nat) : GL (ifHeadG c lt) := by
  intro i hi; simp [ifHeadG] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> first | (simp [GoodX, GoodW]; done) | (unfold cmpJ; split <;> simp [GoodX, GoodW])

theorem jal0_good (o : Int) : GL [.jal 0 o] := by intro i hi; simp at hi; subst hi; simp [GoodX, GoodW]

mutual
theorem tm_good (K : SC) (hnl : K.nl < 251) (hp : K.p ≤ K.nl) :
    ∀ (e : Nd) (h : Nat), ScV K e → OpV e → GL (tm K e h)
  | .const v, h, _, _ => by
    simp only [tm, constT, pushA]; exact GL.app (liT_good 5 v (by omega)) (push_good 5 _ (by omega))
  | .loc s w, h, sc, _ => by
    simp only [tm]; simp only [ScV] at sc; exact localT_good 1 K.p K.nl hnl hp s h w sc
  | .bin op a b, h, sc, op' => by
    simp only [ScV] at sc; simp only [OpV] at op'
    simp only [tm]
    refine GL.app (GL.app (tm_good K hnl hp a _ sc.1 op'.2.2.1) (tm_good K hnl hp b _ sc.2.1 op'.2.2.2)) ?_
    intro i hi; simp [binT] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [GoodX, GoodW] <;> omega
  | .ite c a b t e, h, sc, op' => by
    simp only [ScV] at sc; simp only [OpV] at op'
    simp only [tm]
    exact GL.app (GL.app (GL.app (GL.app (GL.app (tm_good K hnl hp a _ sc.1 op'.1) (tm_good K hnl hp b _ sc.2.1 op'.2.1))
      (ifHeadG_good _ _)) (tm_good K hnl hp t _ sc.2.2.1 op'.2.2.1)) (jal0_good _)) (tm_good K hnl hp e _ sc.2.2.2.1 op'.2.2.2)
  | .letE s w v b, h, sc, op' => by
    simp only [ScV] at sc; simp only [OpV] at op'
    simp only [tm]
    exact GL.app (GL.app (tm_good K hnl hp v _ sc.1 op'.1) (popN_good K.p K.nl s hnl hp w sc.2.2.1))
      (tm_good K hnl hp b _ sc.2.1 op'.2)
  | .pair cs, h, sc, op' => by
    simp only [ScV] at sc; simp only [OpV] at op'
    simp only [tm]; exact tmL_good K hnl hp cs h sc op'
  | .call id as, h, sc, op' => by
    simp only [ScV] at sc; simp only [OpV] at op'
    simp only [tm]; exact GL.app (tmL_good K hnl hp as h sc.1 op') (by intro i hi; simp at hi; subst hi; simp [GoodX, GoodW])
  | .prim pn as, h, sc, op' => by
    simp only [ScV] at sc; simp only [OpV] at op'
    simp only [tm]; exact GL.app (tmL_good K hnl hp as h sc op') (primT_good K pn _)
  | .loop z s, h, sc, op' => by
    simp only [ScV] at sc; simp only [OpV] at op'
    have r0 := slotOff_rng (p := K.p) (k := 0) (by omega) hnl hp
    simp only [tm]
    refine GL.app (GL.app (GL.app ?_ (tmT_good K hnl hp z _ _ _ sc.1 op'.1)) ?_) (tmT_good K hnl hp s _ _ _ sc.2.1 op'.2)
    · intro i hi; simp [loopHead] at hi; rcases hi with rfl | rfl | rfl <;> simp [GoodX, GoodW] <;> omega
    · intro i hi; simp [loopDec] at hi; rcases hi with rfl | rfl <;> simp [GoodX, GoodW] <;> omega
  | .cont _, h, sc, _ => by simp only [ScV] at sc
theorem tmT_good (K : SC) (hnl : K.nl < 251) (hp : K.p ≤ K.nl) :
    ∀ (e : Nd) (h X Hd : Nat), ScT K e → OpV e → GL (tmT K e h X Hd)
  | .ite c a b t e, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [OpV] at op'
    simp only [tmT]
    exact GL.app (GL.app (GL.app (GL.app (GL.app (tm_good K hnl hp a _ sc.1 op'.1) (tm_good K hnl hp b _ sc.2.1 op'.2.1))
      (ifHeadG_good _ _)) (tmT_good K hnl hp t _ _ _ sc.2.2.1 op'.2.2.1)) (jal0_good _))
      (tmT_good K hnl hp e _ _ _ sc.2.2.2.1 op'.2.2.2)
  | .letE s w v b, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [OpV] at op'
    simp only [tmT]
    exact GL.app (GL.app (tm_good K hnl hp v _ sc.1 op'.1) (popN_good K.p K.nl s hnl hp w sc.2.2.1))
      (tmT_good K hnl hp b _ _ _ sc.2.1 op'.2)
  | .cont e, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [OpV] at op'
    simp only [tmT]
    exact GL.app (GL.app (tm_good K hnl hp e _ sc.1 op') (popN_good K.p K.nl 1 hnl hp _ (by omega))) (jal0_good _)
  | .const v, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [tmT]; exact GL.app (tm_good K hnl hp _ _ sc op') (jal0_good _)
  | .loc s w, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [tmT]; exact GL.app (tm_good K hnl hp _ _ sc op') (jal0_good _)
  | .bin o a b, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [tmT]; exact GL.app (tm_good K hnl hp _ _ sc op') (jal0_good _)
  | .pair cs, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [tmT]; exact GL.app (tm_good K hnl hp _ _ sc op') (jal0_good _)
  | .call n as, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [tmT]; exact GL.app (tm_good K hnl hp _ _ sc op') (jal0_good _)
  | .prim pn as, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [tmT]; exact GL.app (tm_good K hnl hp _ _ sc op') (jal0_good _)
  | .loop z s, h, X, Hd, sc, op' => by
    simp only [ScT] at sc; simp only [tmT]; exact GL.app (tm_good K hnl hp _ _ sc op') (jal0_good _)
theorem tmL_good (K : SC) (hnl : K.nl < 251) (hp : K.p ≤ K.nl) :
    ∀ (cs : List Nd) (h : Nat), ScL K cs → OpL cs → GL (tmL K cs h)
  | [], h, _, _ => by simp only [tmL]; exact GL.nil
  | c :: cs, h, sc, op' => by
    simp only [ScL] at sc; simp only [OpL] at op'
    simp only [tmL]; exact GL.app (tm_good K hnl hp c h sc.1 op'.1) (tmL_good K hnl hp cs _ sc.2.1 op'.2)
end

theorem defT_good (S : SC) (e : Nd) (f q : Nat) (hnl : S.nl < 251) (hp : S.p ≤ S.nl) (hq : q < 251)
    (sc : ScV S e) (op' : OpV e) : GL (defT S e f q) := by
  unfold defT proA epi pushA
  refine GL.app (GL.app (GL.app (push_good 1 _ (by omega)) (GL.app (push_good 8 _ (by omega)) ?_))
    (tm_good S hnl hp e _ sc op')) (GL.app ?_ (GL.app (copy_good S.p q (by omega) hq q (Nat.le_refl _)) ?_))
  · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl <;> simp [GoodX, GoodW] <;> omega
  · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp [GoodX, GoodW]
  · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> simp [GoodX, GoodW] <;> omega

theorem defsJ_good (P : PC) (ds : List DefA) (N : Nat) (hok : ∀ k, k < N → (dA ds k).nslots < 251 ∧
    (dA ds k).npw ≤ (dA ds k).nslots ∧ (dA ds k).nres < 251 ∧ ScV (scAt P ds k) (dA ds k).body ∧ OpV (dA ds k).body) :
    ∀ k n, k + n ≤ N → GL (defsJ P ds k n)
  | _, 0, _ => GL.nil
  | k, n + 1, hk => by
    simp only [defsJ]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hok k (by omega)
    exact GL.app (defT_good _ _ _ _ h1 h2 h3 h4 h5) (defsJ_good P ds N hok (k + 1) n (by omega))

/-- Gen's words for a GoodX program are the Sail layer's words -/
theorem words_encJX {C : List J} (h : GL C) : (C.map encG).map UInt64.toNat = C.map SimW.encJX := by
  rw [List.map_map]; apply List.map_congr_left; intro i hi; exact encG_encJX i (h i hi)

/-- the whole program C = stubs ++ defs ++ start code is GoodX -/
theorem prog_good (P : PC) (ds : List DefA) (S w n : Nat) (hok : ∀ k, k < n → (dA ds k).nslots < 251 ∧
    (dA ds k).npw ≤ (dA ds k).nslots ∧ (dA ds k).nres < 251 ∧ ScV (scAt P ds k) (dA ds k).body ∧ OpV (dA ds k).body) :
    GL (stubJ S ++ defsJ P ds 0 n ++ startJ S w) :=
  GL.app (GL.app (stubJ_good S) (defsJ_good P ds n hok 0 n (by omega))) (startJ_good S w)

end Templates
