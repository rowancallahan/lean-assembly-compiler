/- Nano/V2Self/Proof/Parser/ParRunFlat: Layer 2, the FLATTEN tasks (codes 81 / 82, v142 / v143).  `RN.words n` = the words v142/v143 emit for
the arena tree `n` (input locals skipped everywhere, the first child of rd/len/len' skipped, a CONTINUE state tuple with one
non-input component flattened away).  `flat_run`: the frame `flat n` always runs to its continuation with `out ++ n.words`. -/
import Nano.V2Self.Proof.Parser.ParRunStar
namespace ParRun
open ParSpec

/-- header words of a node (v142), given the number of input-local children `ni` -/
def hdr (t a b nk ni : Nat) : List UInt64 :=
  [t.toUInt64] ++ (if t = 6 then [(nk - ni).toUInt64] else if t < 10 then [a.toUInt64] else []) ++
    (if t = 2 ∨ t = 5 then [b.toUInt64] else if t = 8 then [(b - ni).toUInt64] else [])

mutual
def RN.words : RN → List UInt64
  | .mk t a b _ _ ks =>
    let ni := (ks.filter RN.isInp).length
    if t = 6 ∧ ks.length - ni = 1 then RN.wordsL ks else
    hdr t a b ks.length ni ++
      (if t = 9 ∧ a < 4 then (match ks with | [] => [] | _ :: r => RN.wordsL r) else RN.wordsL ks)
def RN.wordsL : List RN → List UInt64
  | [] => []
  | n :: r => (if n.isInp then [] else RN.words n) ++ RN.wordsL r
end

theorem Star.one {f fs st k st'} (h : stepF f st = some (k, st')) : Star (f :: fs, st) (k ++ fs, st') :=
  .step (stepS_some.mpr ⟨k, st', h, rfl⟩) (.refl _)

theorem RN.words_mk (t a b : Nat) (sh : Option Sh) (p : Bool) (ks : List RN) : RN.words (.mk t a b sh p ks) =
    if t = 6 ∧ ks.length - (ks.filter RN.isInp).length = 1 then RN.wordsL ks else
    hdr t a b ks.length (ks.filter RN.isInp).length ++
      (if t = 9 ∧ a < 4 then (match ks with | [] => [] | _ :: r => RN.wordsL r) else RN.wordsL ks) := by
  rw [RN.words.eq_def]

theorem RN.wordsL_cons (n : RN) (r : List RN) : RN.wordsL (n :: r) = (if n.isInp then [] else RN.words n) ++ RN.wordsL r := by
  rw [RN.wordsL]

theorem RN.tail_words {ks : List RN} :
    (match ks with | [] => [] | _ :: r => RN.wordsL r) = RN.wordsL ks.tail := by
  cases ks <;> rfl

mutual
theorem flat_run (n : RN) (ks : List Frame) (st : St) :
    Star (.flat n :: ks, st) (ks, { st with out := st.out ++ n.words }) := by
  match n with
  | .mk t a b sh p kd =>
    by_cases h6 : t = 6 ∧ kd.length - (kd.filter RN.isInp).length = 1
    · have hs : stepF (.flat (.mk t a b sh p kd)) st = some ([.flatL kd], st) := by
        simp only [stepF, RN.kids, RN.tag]; rw [if_pos h6]
      refine (Star.one hs).trans ?_
      rw [RN.words_mk, if_pos h6]
      exact flatL_run kd ks st
    · have hs : stepF (.flat (.mk t a b sh p kd)) st =
          some ([.flatL (if t = 9 ∧ a < 4 then kd.tail else kd)], { st with out := st.out ++ hdr t a b kd.length (kd.filter RN.isInp).length }) := by
        simp only [stepF, RN.kids, RN.tag, RN.a, RN.b]; rw [if_neg h6]; simp [hdr]
      refine (Star.one hs).trans ?_
      rw [RN.words_mk, if_neg h6, RN.tail_words]
      by_cases hp : t = 9 ∧ a < 4
      · simp only [if_pos hp]
        match kd with
        | [] => simpa using flatL_run [] ks { st with out := st.out ++ hdr t a b 0 0 }
        | k0 :: r => simpa using flatL_run r ks { st with out := st.out ++ hdr t a b (k0 :: r).length ((k0 :: r).filter RN.isInp).length }
      · simp only [if_neg hp]
        simpa using flatL_run kd ks { st with out := st.out ++ hdr t a b kd.length (kd.filter RN.isInp).length }
theorem flatL_run (ns : List RN) (ks : List Frame) (st : St) :
    Star (.flatL ns :: ks, st) (ks, { st with out := st.out ++ RN.wordsL ns }) := by
  match ns with
  | [] =>
    have hs : stepF (.flatL []) st = some ([], st) := rfl
    simpa [RN.wordsL] using Star.one (fs := ks) hs
  | n :: r =>
    by_cases hi : n.isInp
    · have hs : stepF (.flatL (n :: r)) st = some ([.flatL r], st) := by simp [stepF, hi]
      refine (Star.one hs).trans ?_
      rw [RN.wordsL_cons, if_pos hi, List.nil_append]; exact flatL_run r ks st
    · have hs : stepF (.flatL (n :: r)) st = some ([.flat n, .flatL r], st) := by simp [stepF, hi]
      refine (Star.one hs).trans ?_
      refine (flat_run n (.flatL r :: ks) st).trans ?_
      rw [RN.wordsL_cons, if_neg hi, ← List.append_assoc]; exact flatL_run r ks { st with out := st.out ++ n.words }
end

/-! ## decoding the arena tree as a ParSpec node -/
mutual
/-- `RN` → `Nd` exactly as the flattener reads it (input locals dropped, rd/len/len' lose their first child, a one-component state tuple is its component) -/
def RN.toNd : RN → Nd
  | .mk t a b _ _ ks =>
    let cs := if t = 9 ∧ a < 4 then (match ks with | [] => [] | _ :: r => RN.toNdL r) else RN.toNdL ks
    if t = 1 then .const a.toUInt64
    else if t = 2 then .loc a b
    else if t = 3 then (match cs with | [x, y] => .bin a x y | _ => .pair [])
    else if t = 4 then (match cs with | [x, y, u, v] => .ite a x y u v | _ => .pair [])
    else if t = 5 then (match cs with | [x, y] => .letE a b x y | _ => .pair [])
    else if t = 6 then (match cs with | [x] => x | _ => .pair cs)
    else if t = 8 then .call a cs
    else if t = 9 then .prim a cs
    else if t = 10 then (match cs with | [x, y] => .loop x y | _ => .pair [])
    else (match cs with | [x] => .cont x | _ => .pair [])
def RN.toNdL : List RN → List Nd
  | [] => []
  | n :: r => if n.isInp then RN.toNdL r else RN.toNd n :: RN.toNdL r
end

mutual
/-- the shape facts the flattener relies on (all guaranteed by the handlers that build the nodes) -/
def RN.ok : RN → Bool
  | .mk t a b _ _ ks =>
    let nc := ks.length - (ks.filter RN.isInp).length
    RN.okL ks &&
    (if t = 1 ∨ t = 2 then ks.isEmpty
     else if t = 3 ∨ t = 5 ∨ t = 10 then nc = 2 && (ks.filter RN.isInp).isEmpty
     else if t = 4 then nc = 4 && (ks.filter RN.isInp).isEmpty
     else if t = 11 then nc = 1 && (ks.filter RN.isInp).isEmpty
     else if t = 8 then b = ks.length
     else if t = 9 then (if a < 4 then (match ks with | k :: _ => k.isInp | [] => false) else true)
     else t = 6)
def RN.okL : List RN → Bool
  | [] => true
  | n :: r => RN.ok n && RN.okL r
end

theorem RN.toNd_mk (t a b : Nat) (sh : Option Sh) (p : Bool) (ks : List RN) : RN.toNd (.mk t a b sh p ks) =
    let cs := if t = 9 ∧ a < 4 then (match ks with | [] => [] | _ :: r => RN.toNdL r) else RN.toNdL ks
    if t = 1 then .const a.toUInt64
    else if t = 2 then .loc a b
    else if t = 3 then (match cs with | [x, y] => .bin a x y | _ => .pair [])
    else if t = 4 then (match cs with | [x, y, u, v] => .ite a x y u v | _ => .pair [])
    else if t = 5 then (match cs with | [x, y] => .letE a b x y | _ => .pair [])
    else if t = 6 then (match cs with | [x] => x | _ => .pair cs)
    else if t = 8 then .call a cs
    else if t = 9 then .prim a cs
    else if t = 10 then (match cs with | [x, y] => .loop x y | _ => .pair [])
    else (match cs with | [x] => .cont x | _ => .pair []) := by
  rw [RN.toNd.eq_def]

theorem RN.toNdL_cons (n : RN) (r : List RN) : RN.toNdL (n :: r) = if n.isInp then RN.toNdL r else RN.toNd n :: RN.toNdL r := by
  rw [RN.toNdL.eq_def]

theorem RN.ok_mk (t a b : Nat) (sh : Option Sh) (p : Bool) (ks : List RN) : RN.ok (.mk t a b sh p ks) =
    (RN.okL ks &&
    (if t = 1 ∨ t = 2 then ks.isEmpty
     else if t = 3 ∨ t = 5 ∨ t = 10 then ks.length - (ks.filter RN.isInp).length = 2 && (ks.filter RN.isInp).isEmpty
     else if t = 4 then ks.length - (ks.filter RN.isInp).length = 4 && (ks.filter RN.isInp).isEmpty
     else if t = 11 then ks.length - (ks.filter RN.isInp).length = 1 && (ks.filter RN.isInp).isEmpty
     else if t = 8 then b = ks.length
     else if t = 9 then (if a < 4 then (match ks with | k :: _ => k.isInp | [] => false) else true)
     else t = 6)) := by
  rw [RN.ok.eq_def]

theorem RN.okL_cons (n : RN) (r : List RN) : RN.okL (n :: r) = (RN.ok n && RN.okL r) := by
  rw [RN.okL.eq_def]

theorem RN.toNdL_length (ks : List RN) : (RN.toNdL ks).length = ks.length - (ks.filter RN.isInp).length := by
  induction ks with
  | nil => rfl
  | cons n r ih =>
    rw [RN.toNdL_cons]
    have hle : (r.filter RN.isInp).length ≤ r.length := List.length_filter_le _ _
    by_cases h : n.isInp <;> simp [h, ih, List.filter_cons] <;> omega

mutual
theorem RN.words_eq (n : RN) (h : n.ok) : n.words = (n.toNd).ser := by
  match n with
  | .mk t a b sh p ks =>
    rw [RN.ok_mk] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hk, h⟩ := h
    have hL := RN.wordsL_eq ks hk
    have hlen := RN.toNdL_length ks
    rw [RN.words_mk, RN.toNd_mk]
    by_cases h1 : t = 1
    · subst h1; simp at h; subst h; simp [hdr, Nd.ser, RN.wordsL]
    by_cases h2 : t = 2
    · subst h2; simp at h; subst h; simp [hdr, Nd.ser, RN.wordsL]
    by_cases h6 : t = 6
    · subst h6
      simp only [true_and, show ¬ (6 = 9 ∧ a < 4) by omega, if_false, if_true, show (6:Nat) ≠ 1 by omega, show (6:Nat) ≠ 2 by omega,
        show (6:Nat) ≠ 3 by omega, show (6:Nat) ≠ 4 by omega, show (6:Nat) ≠ 5 by omega]
      split
      · next hc =>
        rw [hL]
        obtain ⟨x, hx⟩ : ∃ x, RN.toNdL ks = [x] := List.length_eq_one_iff.mp (by omega)
        rw [hx]; simp [serL]
      · next hc =>
        rw [hL]
        split
        · next x hx => rw [hx] at hlen; simp at hlen; omega
        · simp [hdr, Nd.ser, hlen]
    by_cases h9 : t = 9
    · subst h9
      simp only [show ¬ ((9:Nat) = 6 ∧ _) by omega, if_false, true_and, show (9:Nat) ≠ 1 by omega, show (9:Nat) ≠ 2 by omega,
        show (9:Nat) ≠ 3 by omega, show (9:Nat) ≠ 4 by omega, show (9:Nat) ≠ 5 by omega, show (9:Nat) ≠ 6 by omega,
        show (9:Nat) ≠ 8 by omega, if_true]
      by_cases ha : a < 4
      · simp only [ha, if_true]
        match ks, hk with
        | [], _ => simp [hdr, Nd.ser, RN.wordsL, RN.toNdL, serL]
        | k :: r, hk =>
          rw [RN.okL_cons, Bool.and_eq_true] at hk
          simp [hdr, Nd.ser, RN.wordsL_eq r hk.2]
      · simp only [ha, if_false]; rw [hL]; simp [hdr, Nd.ser]
    have h69 : ¬ (t = 6 ∧ ks.length - (ks.filter RN.isInp).length = 1) := fun hc => h6 hc.1
    have h9' : ¬ (t = 9 ∧ a < 4) := fun hc => h9 hc.1
    simp only [h69, h9', if_false, h1, h2, h6, h9]
    rw [hL]
    have hni : ∀ m, ks.length - (ks.filter RN.isInp).length = m → (RN.toNdL ks).length = m := by
      intro m hm; omega
    have h12 : ¬ (t = 1 ∨ t = 2) := by omega
    by_cases h3 : t = 3 ∨ t = 5 ∨ t = 10
    · simp only [if_neg h12, if_pos h3, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨x, y, hxy⟩ : ∃ x y, RN.toNdL ks = [x, y] := by
        match hc : RN.toNdL ks, hni 2 h.1 with
        | [x, y], _ => exact ⟨x, y, rfl⟩
      rw [hxy]
      rcases h3 with rfl | rfl | rfl <;> simp [hdr, Nd.ser, serL]
    by_cases h4 : t = 4
    · simp only [if_neg h12, if_neg h3, if_pos h4, Bool.and_eq_true, decide_eq_true_eq] at h
      subst h4
      obtain ⟨x, y, u, v, hxy⟩ : ∃ x y u v, RN.toNdL ks = [x, y, u, v] := by
        match hc : RN.toNdL ks, hni 4 h.1 with
        | [x, y, u, v], _ => exact ⟨x, y, u, v, rfl⟩
      rw [hxy]; simp [hdr, Nd.ser, serL]
    by_cases h11 : t = 11
    · simp only [if_neg h12, if_neg h3, if_neg h4, if_pos h11, Bool.and_eq_true, decide_eq_true_eq] at h
      subst h11
      obtain ⟨x, hx⟩ : ∃ x, RN.toNdL ks = [x] := by
        match hc : RN.toNdL ks, hni 1 h.1 with
        | [x], _ => exact ⟨x, rfl⟩
      rw [hx]; simp [hdr, Nd.ser, serL]
    by_cases h8 : t = 8
    · simp only [if_neg h12, if_neg h3, if_neg h4, if_neg h11, if_pos h8, decide_eq_true_eq] at h
      subst h8
      simp [hdr, Nd.ser, h, hlen]
    simp only [if_neg h12, if_neg h3, if_neg h4, if_neg h11, if_neg h8, if_neg h9, decide_eq_true_eq] at h
    exact absurd h h6
theorem RN.wordsL_eq (ks : List RN) (h : RN.okL ks) : RN.wordsL ks = serL (RN.toNdL ks) := by
  match ks with
  | [] => rw [RN.wordsL, RN.toNdL]; rfl
  | n :: r =>
    rw [RN.okL_cons, Bool.and_eq_true] at h
    rw [RN.wordsL_cons, RN.toNdL_cons, RN.wordsL_eq r h.2]
    by_cases hi : n.isInp
    · simp [hi]
    · simp [hi, serL, RN.words_eq n h.1]
end

end ParRun
