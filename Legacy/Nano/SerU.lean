/- nano: the non-inlined program as a micro-op stream (`serU`) and the byte-level inliner `inlB` (integration,
nano-int).  `serU u`: per def (oldest first) the body's micro-ops (as `Nano.serE`, but a call is the arguments, then
`[14, j / 256] [15, j % 256]` for the callee's number `j`, then the usual `[9, arity]`), closed by `[13, arity]`.
`inlB` copies micro-ops, replaces a `[14, h] [15, l]` pair by the (already inlined) body code of def `256 h + l`, and
at the end wraps the last def as a program.  **`inlB_serU : WF u → inlB (serU u) = ser (inlineProg u)`**.
The reason copying is right: the code of a body does not depend on the stack depth of the call site (`serE_shift`). -/
import Legacy.Nano.Ser
import Legacy.Nano.ElabU

namespace Nano.U
open Nano

/-! ## scoped expressions -/

mutual
/-- an inlined expression with every variable among the `n` in scope -/
def WS : Ex → Nat → Bool
  | .num _, _ => true
  | .var i, n => decide (i < n)
  | .add a b, n => WS a n && WS b n
  | .sub a b, n => WS a n && WS b n
  | .mul a b, n => WS a n && WS b n
  | .let_ v b, n => WS v n && WS b (n + 1)
  | .call b as, n => WSA as n && WS b (cnt as)
  | .anil, _ => false
  | .acons _ _, _ => false
def WSA : Ex → Nat → Bool
  | .acons e r, n => WS e n && WSA r n
  | .anil, _ => true
  | _, _ => false
end

mutual
/-- a non-inlined expression: scoped, calls to existing defs (`ar`: arities, oldest first) with the right number of
arguments -/
def WU (ar : List Nat) : Ex → Nat → Bool
  | .num _, _ => true
  | .var i, n => decide (i < n)
  | .add a b, n => WU ar a n && WU ar b n
  | .sub a b, n => WU ar a n && WU ar b n
  | .mul a b, n => WU ar a n && WU ar b n
  | .let_ v b, n => WU ar v n && WU ar b (n + 1)
  | .call (.var j) as, n => WUA ar as n && decide (ar[j]? = some (cnt as)) && decide (j < 65536)
  | .call _ _, _ => false
  | .anil, _ => false
  | .acons _ _, _ => false
def WUA (ar : List Nat) : Ex → Nat → Bool
  | .acons e r, n => WU ar e n && WUA ar r n
  | .anil, _ => true
  | _, _ => false
end

/-! ## the stream -/

mutual
def serUE : List Nat → Nat → Ex → List UInt8
  | _, _, .num n => sLi n ++ mo 3 0
  | sc, d, .var i => mo 7 (d - 1 - sc.getD i 0).toUInt8 ++ mo 3 0
  | sc, d, .add a b => serUE sc d a ++ serUE sc (d + 1) b ++ mo 8 24
  | sc, d, .sub a b => serUE sc d a ++ serUE sc (d + 1) b ++ mo 8 32
  | sc, d, .mul a b => serUE sc d a ++ serUE sc (d + 1) b ++ mo 8 40
  | sc, d, .let_ v b => serUE sc d v ++ serUE (d :: sc) (d + 1) b ++ mo 9 1
  | sc, d, .call (.var j) as =>
    serUA sc d as ++ mo 14 (j / 256).toUInt8 ++ mo 15 (j % 256).toUInt8 ++ mo 9 (cnt as).toUInt8
  | _, _, _ => []
def serUA : List Nat → Nat → Ex → List UInt8
  | sc, d, .acons e r => serUE sc d e ++ serUA sc (d + 1) r
  | _, _, _ => []
end

/-- one def: its body, then `[13, arity]` -/
def serUD (d : Nat × Ex) : List UInt8 := serUE (mkSc d.1 0) d.1 d.2 ++ mo 13 d.1.toUInt8

/-- **the non-inlined program as bytes** (defs given newest first, emitted oldest first) -/
def serU : List (Nat × Ex) → List UInt8
  | [] => []
  | d :: older => serU older ++ serUD d

/-! ## the inliner on bytes -/

/-- the program around the entry's body code -/
def wrap (k : Nat) (body : List UInt8) : List UInt8 := mo 0 0 ++ serPro k ++ body ++ mo 7 0 ++ sWr ++ mo 12 0

/-- `tab`: the body code of the defs so far; `cur`: the code of the def being read; `hi`: the high byte of a
callee number; `k`, `last`: the last closed def -/
def inlGo : List UInt8 → List (List UInt8) → List UInt8 → Nat → Nat → List UInt8 → List UInt8
  | m :: x :: rest, tab, cur, hi, k, last =>
    if m = 13 then inlGo rest (tab ++ [cur]) [] hi x.toNat cur
    else if m = 14 then inlGo rest tab cur x.toNat k last
    else if m = 15 then inlGo rest tab (cur ++ tab.getD (hi * 256 + x.toNat) []) hi k last
    else inlGo rest tab (cur ++ [m, x]) hi k last
  | _, _, _, _, k, last => wrap k last

/-- **the inliner** -/
def inlB (xs : List UInt8) : List UInt8 := inlGo xs [] [] 0 0 []

/-! ## steps of `inlGo` -/

theorem inlGo_mo (m x : UInt8) (h13 : m ≠ 13) (h14 : m ≠ 14) (h15 : m ≠ 15) (rest : List UInt8)
    (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat) (last : List UInt8) :
    inlGo (mo m x ++ rest) tab cur hi k last = inlGo rest tab (cur ++ mo m x) hi k last := by
  show inlGo (m :: x :: rest) tab cur hi k last = _
  rw [inlGo, if_neg h13, if_neg h14, if_neg h15]; rfl

theorem inlGo_call (h l : UInt8) (rest : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat)
    (last : List UInt8) :
    inlGo (mo 14 h ++ (mo 15 l ++ rest)) tab cur hi k last =
      inlGo rest tab (cur ++ tab.getD (h.toNat * 256 + l.toNat) []) h.toNat k last := by
  show inlGo (14 :: h :: 15 :: l :: rest) tab cur hi k last = _
  rw [inlGo, if_neg (by decide), if_pos rfl, inlGo, if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem inlGo_def (x : UInt8) (rest : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat)
    (last : List UInt8) :
    inlGo (mo 13 x ++ rest) tab cur hi k last = inlGo rest (tab ++ [cur]) [] hi x.toNat cur := by
  show inlGo (13 :: x :: rest) tab cur hi k last = _
  rw [inlGo, if_pos rfl]

theorem inlGo_sLi (n : UInt64) (rest : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat)
    (last : List UInt8) : inlGo (sLi n ++ rest) tab cur hi k last = inlGo rest tab (cur ++ sLi n) hi k last := by
  simp only [sLi, List.append_assoc]
  repeat rw [inlGo_mo _ _ (by decide) (by decide) (by decide)]
  simp only [List.append_assoc]

/-! ## the code of a body does not depend on the depth of the call site -/

theorem mkSc_shift : ∀ (k d : Nat), (mkSc k 0).map (· + d) = mkSc k d
  | 0, _ => rfl
  | k + 1, d => by simp only [mkSc, List.map_cons, mkSc_shift k d]; congr 1; omega

theorem mkSc_length : ∀ (k d : Nat), (mkSc k d).length = k
  | 0, _ => rfl
  | k + 1, d => by simp [mkSc, mkSc_length k d]

mutual
theorem serE_shift : ∀ (e : Ex) (sc : List Nat) (d δ : Nat), WS e sc.length = true →
    serE (sc.map (· + δ)) (d + δ) e = serE sc d e
  | .num n, sc, d, δ, _ => by simp only [serE]
  | .var i, sc, d, δ, h => by
    simp only [WS, decide_eq_true_eq] at h
    simp only [serE]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
    simp only [Option.map_some, Option.getD_some]
    congr 3; omega
  | .add a b, sc, d, δ, h => by
    simp only [WS, Bool.and_eq_true] at h
    simp only [serE, serE_shift a sc d δ h.1]
    rw [show d + δ + 1 = d + 1 + δ by omega, serE_shift b sc (d + 1) δ h.2]
  | .sub a b, sc, d, δ, h => by
    simp only [WS, Bool.and_eq_true] at h
    simp only [serE, serE_shift a sc d δ h.1]
    rw [show d + δ + 1 = d + 1 + δ by omega, serE_shift b sc (d + 1) δ h.2]
  | .mul a b, sc, d, δ, h => by
    simp only [WS, Bool.and_eq_true] at h
    simp only [serE, serE_shift a sc d δ h.1]
    rw [show d + δ + 1 = d + 1 + δ by omega, serE_shift b sc (d + 1) δ h.2]
  | .let_ v b, sc, d, δ, h => by
    simp only [WS, Bool.and_eq_true] at h
    simp only [serE, serE_shift v sc d δ h.1]
    have := serE_shift b (d :: sc) (d + 1) δ (by simpa using h.2)
    simp only [List.map_cons] at this
    rw [show d + δ + 1 = d + 1 + δ by omega, this]
  | .call b as, sc, d, δ, h => by
    simp only [WS, Bool.and_eq_true] at h
    simp only [serE, serA_shift as sc d δ h.1]
    have h1 := serE_shift b (mkSc (cnt as) 0) (cnt as) (d + δ) (by rw [mkSc_length]; exact h.2)
    have h2 := serE_shift b (mkSc (cnt as) 0) (cnt as) d (by rw [mkSc_length]; exact h.2)
    rw [mkSc_shift] at h1 h2
    rw [show d + δ + cnt as = cnt as + (d + δ) by omega, h1, show d + cnt as = cnt as + d by omega, h2]
  | .anil, sc, d, δ, h => by simp [WS] at h
  | .acons _ _, sc, d, δ, h => by simp [WS] at h
theorem serA_shift : ∀ (e : Ex) (sc : List Nat) (d δ : Nat), WSA e sc.length = true →
    serA (sc.map (· + δ)) (d + δ) e = serA sc d e
  | .acons e r, sc, d, δ, h => by
    simp only [WSA, Bool.and_eq_true] at h
    simp only [serA, serE_shift e sc d δ h.1]
    rw [show d + δ + 1 = d + 1 + δ by omega, serA_shift r sc (d + 1) δ h.2]
  | .anil, sc, d, δ, _ => by simp only [serA]
  | .num _, _, _, _, h | .var _, _, _, _, h | .add _ _, _, _, _, h | .sub _ _, _, _, _, h | .mul _ _, _, _, _, h
  | .let_ _ _, _, _, _, h | .call _ _, _, _, _, h => by simp [WSA] at h
end

/-- the code of a body with `k` parameters, at any call-site depth -/
theorem body_code (b : Ex) (k d : Nat) (h : WS b k = true) :
    serE (mkSc k d) (d + k) b = serE (mkSc k 0) k b := by
  have := serE_shift b (mkSc k 0) k d (by rw [mkSc_length]; exact h)
  rw [mkSc_shift] at this
  rw [show d + k = k + d by omega, this]

/-! ## an expression's micro-ops through the inliner -/

theorem cnt_sub (σ : Nat → Ex) : ∀ e : Ex, cnt (sub σ e) = cnt e
  | .acons e r => by simp only [sub, cnt, cnt_sub σ r]
  | .num _ | .var _ | .add _ _ | .sub _ _ | .mul _ _ | .let_ _ _ | .call _ _ | .anil => by simp only [sub, cnt]

theorem idx_bytes {j : Nat} (h : j < 65536) : (j / 256).toUInt8.toNat * 256 + (j % 256).toUInt8.toNat = j := by
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega

mutual
theorem WS_sub (ar : List Nat) (σ : Nat → Ex) (hσ : ∀ j k, ar[j]? = some k → WS (σ j) k = true) :
    ∀ (e : Ex) (n : Nat), WU ar e n = true → WS (sub σ e) n = true
  | .num _, _, _ => by simp only [sub, WS]
  | .var i, n, h => by simpa only [sub, WS, WU] using h
  | .add a b, n, h => by
    simp only [WU, Bool.and_eq_true] at h
    simp only [sub, WS, Bool.and_eq_true]; exact ⟨WS_sub ar σ hσ a n h.1, WS_sub ar σ hσ b n h.2⟩
  | .sub a b, n, h => by
    simp only [WU, Bool.and_eq_true] at h
    simp only [sub, WS, Bool.and_eq_true]; exact ⟨WS_sub ar σ hσ a n h.1, WS_sub ar σ hσ b n h.2⟩
  | .mul a b, n, h => by
    simp only [WU, Bool.and_eq_true] at h
    simp only [sub, WS, Bool.and_eq_true]; exact ⟨WS_sub ar σ hσ a n h.1, WS_sub ar σ hσ b n h.2⟩
  | .let_ v b, n, h => by
    simp only [WU, Bool.and_eq_true] at h
    simp only [sub, WS, Bool.and_eq_true]; exact ⟨WS_sub ar σ hσ v n h.1, WS_sub ar σ hσ b (n + 1) h.2⟩
  | .call (.var j) as, n, h => by
    simp only [WU, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [sub, mkB, WS, Bool.and_eq_true, cnt_sub]
    exact ⟨WSA_sub ar σ hσ as n h.1.1, hσ j _ h.1.2⟩
  | .call (.num _) _, _, h | .call (.add _ _) _, _, h | .call (.sub _ _) _, _, h | .call (.mul _ _) _, _, h
  | .call (.let_ _ _) _, _, h | .call (.call _ _) _, _, h | .call .anil _, _, h | .call (.acons _ _) _, _, h
  | .anil, _, h | .acons _ _, _, h => by simp [WU] at h
theorem WSA_sub (ar : List Nat) (σ : Nat → Ex) (hσ : ∀ j k, ar[j]? = some k → WS (σ j) k = true) :
    ∀ (e : Ex) (n : Nat), WUA ar e n = true → WSA (sub σ e) n = true
  | .acons e r, n, h => by
    simp only [WUA, Bool.and_eq_true] at h
    simp only [sub, WSA, Bool.and_eq_true]; exact ⟨WS_sub ar σ hσ e n h.1, WSA_sub ar σ hσ r n h.2⟩
  | .anil, _, _ => by simp only [sub, WSA]
  | .num _, _, h | .var _, _, h | .add _ _, _, h | .sub _ _, _, h | .mul _ _, _, h | .let_ _ _, _, h
  | .call _ _, _, h => by simp [WUA] at h
end

mutual
theorem chunkE (ar : List Nat) (σ : Nat → Ex) (tab : List (List UInt8))
    (ht : ∀ j k, ar[j]? = some k → tab.getD j [] = serE (mkSc k 0) k (σ j) ∧ WS (σ j) k = true) :
    ∀ (e : Ex) (n : Nat) (sc : List Nat) (d hi : Nat), WU ar e n = true → ∃ hi', ∀ rest cur k last,
      inlGo (serUE sc d e ++ rest) tab cur hi k last = inlGo rest tab (cur ++ serE sc d (sub σ e)) hi' k last
  | .num x, n, sc, d, hi, _ => ⟨hi, fun rest cur k last => by
      simp only [serUE, serE, sub, List.append_assoc]
      rw [inlGo_sLi, inlGo_mo _ _ (by decide) (by decide) (by decide)]; simp only [List.append_assoc]⟩
  | .var i, n, sc, d, hi, _ => ⟨hi, fun rest cur k last => by
      simp only [serUE, serE, sub, List.append_assoc]
      rw [inlGo_mo _ _ (by decide) (by decide) (by decide), inlGo_mo _ _ (by decide) (by decide) (by decide)]
      simp only [List.append_assoc]⟩
  | .add a b, n, sc, d, hi, h => by
    simp only [WU, Bool.and_eq_true] at h
    obtain ⟨h1, e1⟩ := chunkE ar σ tab ht a n sc d hi h.1
    obtain ⟨h2, e2⟩ := chunkE ar σ tab ht b n sc (d + 1) h1 h.2
    refine ⟨h2, fun rest cur k last => ?_⟩
    simp only [serUE, serE, sub, List.append_assoc]
    rw [e1, e2, inlGo_mo _ _ (by decide) (by decide) (by decide)]; simp only [List.append_assoc]
  | .sub a b, n, sc, d, hi, h => by
    simp only [WU, Bool.and_eq_true] at h
    obtain ⟨h1, e1⟩ := chunkE ar σ tab ht a n sc d hi h.1
    obtain ⟨h2, e2⟩ := chunkE ar σ tab ht b n sc (d + 1) h1 h.2
    refine ⟨h2, fun rest cur k last => ?_⟩
    simp only [serUE, serE, sub, List.append_assoc]
    rw [e1, e2, inlGo_mo _ _ (by decide) (by decide) (by decide)]; simp only [List.append_assoc]
  | .mul a b, n, sc, d, hi, h => by
    simp only [WU, Bool.and_eq_true] at h
    obtain ⟨h1, e1⟩ := chunkE ar σ tab ht a n sc d hi h.1
    obtain ⟨h2, e2⟩ := chunkE ar σ tab ht b n sc (d + 1) h1 h.2
    refine ⟨h2, fun rest cur k last => ?_⟩
    simp only [serUE, serE, sub, List.append_assoc]
    rw [e1, e2, inlGo_mo _ _ (by decide) (by decide) (by decide)]; simp only [List.append_assoc]
  | .let_ v b, n, sc, d, hi, h => by
    simp only [WU, Bool.and_eq_true] at h
    obtain ⟨h1, e1⟩ := chunkE ar σ tab ht v n sc d hi h.1
    obtain ⟨h2, e2⟩ := chunkE ar σ tab ht b (n + 1) (d :: sc) (d + 1) h1 h.2
    refine ⟨h2, fun rest cur k last => ?_⟩
    simp only [serUE, serE, sub, List.append_assoc]
    rw [e1, e2, inlGo_mo _ _ (by decide) (by decide) (by decide)]; simp only [List.append_assoc]
  | .call (.var j) as, n, sc, d, hi, h => by
    simp only [WU, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hwa, har⟩, hj⟩ := h
    obtain ⟨h1, e1⟩ := chunkA ar σ tab ht as n sc d hi hwa
    obtain ⟨htab, hws⟩ := ht j _ har
    refine ⟨(j / 256).toUInt8.toNat, fun rest cur k last => ?_⟩
    simp only [serUE, serE, sub, mkB, List.append_assoc, cnt_sub]
    rw [e1, inlGo_call, idx_bytes hj, htab, inlGo_mo _ _ (by decide) (by decide) (by decide), body_code _ _ _ hws]
    simp only [List.append_assoc]
  | .call (.num _) _, _, _, _, _, h | .call (.add _ _) _, _, _, _, _, h | .call (.sub _ _) _, _, _, _, _, h
  | .call (.mul _ _) _, _, _, _, _, h | .call (.let_ _ _) _, _, _, _, _, h | .call (.call _ _) _, _, _, _, _, h
  | .call .anil _, _, _, _, _, h | .call (.acons _ _) _, _, _, _, _, h
  | .anil, _, _, _, _, h | .acons _ _, _, _, _, _, h => by simp [WU] at h
theorem chunkA (ar : List Nat) (σ : Nat → Ex) (tab : List (List UInt8))
    (ht : ∀ j k, ar[j]? = some k → tab.getD j [] = serE (mkSc k 0) k (σ j) ∧ WS (σ j) k = true) :
    ∀ (e : Ex) (n : Nat) (sc : List Nat) (d hi : Nat), WUA ar e n = true → ∃ hi', ∀ rest cur k last,
      inlGo (serUA sc d e ++ rest) tab cur hi k last = inlGo rest tab (cur ++ serA sc d (sub σ e)) hi' k last
  | .acons e r, n, sc, d, hi, h => by
    simp only [WUA, Bool.and_eq_true] at h
    obtain ⟨h1, e1⟩ := chunkE ar σ tab ht e n sc d hi h.1
    obtain ⟨h2, e2⟩ := chunkA ar σ tab ht r n sc (d + 1) h1 h.2
    refine ⟨h2, fun rest cur k last => ?_⟩
    simp only [serUA, serA, sub, List.append_assoc]
    rw [e1, e2]; simp only [List.append_assoc]
  | .anil, _, _, _, hi, _ => ⟨hi, fun rest cur k last => by simp only [serUA, serA, sub, List.nil_append, List.append_nil]⟩
  | .num _, _, _, _, _, h | .var _, _, _, _, _, h | .add _ _, _, _, _, _, h | .sub _ _, _, _, _, _, h
  | .mul _ _, _, _, _, _, h | .let_ _ _, _, _, _, _, h | .call _ _, _, _, _, _, h => by simp [WUA] at h
end

/-! ## programs -/

/-- arities, oldest first, of defs given newest first -/
def arities : List (Nat × Ex) → List Nat
  | [] => []
  | d :: older => arities older ++ [d.1]

/-- the inlined body code of every def, oldest first -/
def codes : List (Nat × Ex) → List (List UInt8)
  | [] => []
  | (k, e) :: older => codes older ++ [serE (mkSc k 0) k (sub (σof (realBodies older)) e)]

/-- well-formed non-inlined program: bodies scoped in their parameters, calls to earlier defs with the right number
of arguments, fewer than 65536 callees, arities below 256 -/
def WF : List (Nat × Ex) → Bool
  | [] => true
  | (k, e) :: older => WF older && WU (arities older) e k && decide (k < 256)

theorem length_arities : ∀ u : List (Nat × Ex), (arities u).length = u.length
  | [] => rfl
  | _ :: older => by simp [arities, length_arities older]

theorem length_codes : ∀ u : List (Nat × Ex), (codes u).length = u.length
  | [] => rfl
  | (_, _) :: older => by simp [codes, length_codes older]

/-- the table the inliner has built is the code of the inlined bodies, and they are scoped -/
theorem inv : ∀ u : List (Nat × Ex), WF u = true → ∀ j k, (arities u)[j]? = some k →
    (codes u).getD j [] = serE (mkSc k 0) k (σof (realBodies u) j) ∧ WS (σof (realBodies u) j) k = true
  | [], _, j, k, h => by simp [arities] at h
  | (k0, e0) :: older, hw, j, k, h => by
    simp only [WF, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨hwo, hwu⟩, _⟩ := hw
    have ih := inv older hwo
    have la := length_arities older; have lc := length_codes older; have lr := length_realBodies older
    simp only [arities, codes, realBodies, σof] at h ⊢
    by_cases hj : j < older.length
    · rw [List.getElem?_append_left (by omega)] at h
      have := ih j k h
      simp only [σof] at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD (l := realBodies older ++ _), List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      exact this
    · rw [List.getElem?_append_right (by omega)] at h
      have hj' : j = older.length := by
        rcases Nat.lt_or_ge (j - (arities older).length) 1 with h1 | h1
        · omega
        · rw [List.getElem?_eq_none (by simpa using h1)] at h; cases h
      subst hj'
      simp only [la, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        List.getD_eq_getElem?_getD (l := realBodies older ++ _), List.getElem?_append_right (by omega)]
      simp only [lc, lr, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, true_and]
      exact WS_sub (arities older) (σof (realBodies older)) (fun j k h => (ih j k h).2) e0 k0 hwu

/-- the last closed def after reading a program -/
def lastK : List (Nat × Ex) → Nat → Nat
  | [], k0 => k0
  | d :: _, _ => d.1
def lastC : List (Nat × Ex) → List UInt8 → List UInt8
  | [], l0 => l0
  | (k, e) :: older, _ => serE (mkSc k 0) k (sub (σof (realBodies older)) e)

/-- the inliner on a whole program stream -/
theorem run : ∀ u : List (Nat × Ex), WF u = true → ∀ (rest : List UInt8) (hi k0 : Nat) (last0 : List UInt8),
    ∃ hi', inlGo (serU u ++ rest) [] [] hi k0 last0 = inlGo rest (codes u) [] hi' (lastK u k0) (lastC u last0)
  | [], _, rest, hi, k0, last0 => ⟨hi, rfl⟩
  | (k, e) :: older, hw, rest, hi, k0, last0 => by
    have hw' := hw
    simp only [WF, Bool.and_eq_true, decide_eq_true_eq] at hw'
    obtain ⟨⟨hwo, hwu⟩, hk⟩ := hw'
    obtain ⟨h1, e1⟩ := run older hwo (serUD (k, e) ++ rest) hi k0 last0
    obtain ⟨h2, e2⟩ := chunkE (arities older) (σof (realBodies older)) (codes older) (inv older hwo) e k
      (mkSc k 0) k h1 hwu
    refine ⟨h2, ?_⟩
    simp only [serU, List.append_assoc]
    rw [e1]
    simp only [serUD, List.append_assoc]
    rw [e2, inlGo_def]
    have hk8 : k.toUInt8.toNat = k := by simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega
    simp only [hk8, List.nil_append, codes, lastK, lastC]

/-- **inlining on bytes**: the inliner turns the non-inlined stream into the micro-op stream of the inlined program -/
theorem inlB_serU (u : List (Nat × Ex)) (hw : WF u = true) (hne : u ≠ []) : inlB (serU u) = ser (inlineProg u) := by
  obtain ⟨hi', e⟩ := run u hw [] 0 0 []
  rw [List.append_nil] at e
  unfold inlB; rw [e]
  match u, hne with
  | (k, b) :: older, _ => simp only [inlGo, lastK, lastC, inlineProg, wrap, ser]

/-- the whole chain in Lean: the spec's code is the expander after the inliner after the non-inlined stream -/
theorem genR_chain (xs : List UInt8) (p : Prog) (u : List (Nat × Ex)) (hu : nanoElabU xs = some u)
    (hp : nanoElab xs = some p) (hw : WF u = true) (hne : u ≠ []) : mexp (inlB (serU u)) = genR p := by
  rw [nanoElab_eq, hu] at hp
  cases hp
  rw [inlB_serU u hw hne, mexp_ser]

end Nano.U
