/- Nano/V2Self/Proof/ParTree: the FLATTEN of Par1 (tasks 81/82, `v142`/`v143`) on Layer-2 arena trees `ParRun.RN`, pure part (parser lead).
* `emit n` / `emitL ns` : the words the frames `.flat n` / `.flatL ns` append to `out` (big-step form of `stepF`): input-local children are
  skipped, PRIM 1..3 drop their first child, CALL writes `b - #input children`, a PAIR with exactly one visible child is elided.
* `flat_run` / `flatL_run` : `Star ([.flat n], st) ([], { st with out := st.out ++ emit n })` (with `Star.det`: the only run).
* `toNd` : the `ParSpec.Nd` a raw tree stands for (`dropInp` / `mkPairFlat` made explicit).
* `ok`   : child counts as the node builders produce them, no input local directly under a fixed-arity node (what `v209` leaves).
* `emit_ser : ok n → emit n = (toNd n).ser`. -/
import Nano.V2Self.Proof.ParRunStar
namespace ParRun
open ParSpec

/-- number of input-local children (`v205`) -/
def cntInp (ks : List RN) : Nat := (ks.filter RN.isInp).length

mutual
/-- the words `.flat n` appends, children included (preorder) -/
def emit : RN → List UInt64
  | .mk t a b _ _ ks =>
    if t = 6 ∧ ks.length - cntInp ks = 1 then emitL ks
    else
      [t.toUInt64] ++ (if t = 6 then [(ks.length - cntInp ks).toUInt64] else if t < 10 then [a.toUInt64] else []) ++
        (if t = 2 ∨ t = 5 then [b.toUInt64] else if t = 8 then [(b - cntInp ks).toUInt64] else []) ++
        (if t = 9 ∧ a < 4 then emitT ks else emitL ks)
/-- children: input locals are skipped -/
def emitL : List RN → List UInt64
  | [] => []
  | k :: r => (if k.isInp then [] else emit k) ++ emitL r
/-- children of PRIM 1..3: the first one (the input) is dropped unconditionally -/
def emitT : List RN → List UInt64
  | [] => []
  | _ :: r => emitL r
end

theorem emitT_tail (ks : List RN) : emitT ks = emitL ks.tail := by
  cases ks <;> simp [emitT, emitL]

/-! ## the flatten frames compute `emit` -/
theorem star_one {c d e} (h : stepS c = some d) (r : Star d e) : Star c e := .step h r

mutual
theorem flat_run : ∀ (n : RN) (st : St), Star ([.flat n], st) ([], { st with out := st.out ++ emit n })
  | .mk t a b s p ks, st => by
    by_cases h6 : t = 6 ∧ ks.length - cntInp ks = 1
    · have hs : stepS ([.flat (.mk t a b s p ks)], st) = some ([.flatL ks], st) := by
        simp [stepS, stepF, RN.kids, RN.tag, cntInp] at h6 ⊢
        simp [h6]
      have he : emit (.mk t a b s p ks) = emitL ks := by
        unfold emit; rw [if_pos h6]
      rw [he]
      exact star_one hs (flatL_run ks st)
    · have he : emit (.mk t a b s p ks) = [t.toUInt64] ++ (if t = 6 then [(ks.length - cntInp ks).toUInt64] else if t < 10 then [a.toUInt64] else []) ++
          (if t = 2 ∨ t = 5 then [b.toUInt64] else if t = 8 then [(b - cntInp ks).toUInt64] else []) ++ emitL (if t = 9 ∧ a < 4 then ks.tail else ks) := by
        unfold emit; rw [if_neg h6]
        by_cases h9 : t = 9 ∧ a < 4
        · rw [if_pos h9, if_pos h9, emitT_tail]
        · rw [if_neg h9, if_neg h9]
      generalize hw : [t.toUInt64] ++ (if t = 6 then [(ks.length - cntInp ks).toUInt64] else if t < 10 then [a.toUInt64] else []) ++
          (if t = 2 ∨ t = 5 then [b.toUInt64] else if t = 8 then [(b - cntInp ks).toUInt64] else []) = w at he
      have hs : stepS ([.flat (.mk t a b s p ks)], st) =
          some ([.flatL (if t = 9 ∧ a < 4 then ks.tail else ks)], { st with out := st.out ++ w }) := by
        have h6' : ¬ (t = 6 ∧ ks.length - (List.filter RN.isInp ks).length = 1) := h6
        simp only [stepS, stepF, RN.kids, RN.tag, RN.a, RN.b, h6', if_false, Option.map_some, List.append_nil, ← hw, cntInp]
      rw [he, ← List.append_assoc]
      by_cases h9 : t = 9 ∧ a < 4
      · rw [if_pos h9] at hs ⊢
        exact star_one hs (flatT_run ks _)
      · rw [if_neg h9] at hs ⊢
        exact star_one hs (flatL_run ks _)
theorem flatL_run : ∀ (ns : List RN) (st : St), Star ([.flatL ns], st) ([], { st with out := st.out ++ emitL ns })
  | [], st => by
    have hs : stepS ([.flatL []], st) = some ([], st) := by simp [stepS, stepF]
    simpa [emitL] using star_one hs (.refl _)
  | k :: r, st => by
    by_cases hk : k.isInp
    · have hs : stepS ([.flatL (k :: r)], st) = some ([.flatL r], st) := by simp [stepS, stepF, hk]
      have := star_one hs (flatL_run r st)
      simpa [emitL, hk] using this
    · have hs : stepS ([.flatL (k :: r)], st) = some ([.flat k, .flatL r], st) := by simp [stepS, stepF, hk]
      have r1 := (flat_run k st).append [.flatL r]
      have r2 := flatL_run r { st with out := st.out ++ emit k }
      have := star_one hs (r1.trans r2)
      simpa [emitL, hk, List.append_assoc] using this
theorem flatT_run : ∀ (ns : List RN) (st : St), Star ([.flatL ns.tail], st) ([], { st with out := st.out ++ emitL ns.tail })
  | [], st => flatL_run [] st
  | _ :: r, st => flatL_run r st
end

/-! ## raw trees as spec nodes -/
mutual
/-- the spec node of a raw tree -/
def toNd : RN → Nd
  | .mk t a b _ _ ks =>
    if t = 1 then .const a.toUInt64
    else if t = 2 then .loc a b
    else if t = 3 then (match ks with | [x, y] => .bin a (toNd x) (toNd y) | _ => .const 0)
    else if t = 4 then (match ks with | [x, y, u, v] => .ite a (toNd x) (toNd y) (toNd u) (toNd v) | _ => .const 0)
    else if t = 5 then (match ks with | [v, e] => .letE a b (toNd v) (toNd e) | _ => .const 0)
    else if t = 6 then mkPairFlat (toNdL ks)
    else if t = 8 then .call a (toNdL ks)
    else if t = 9 then .prim a (if a < 4 then toNdT ks else toNdL ks)
    else if t = 10 then (match ks with | [z, s] => .loop (toNd z) (toNd s) | _ => .const 0)
    else (match ks with | [e] => .cont (toNd e) | _ => .const 0)
/-- variadic children: input locals dropped (`dropInp`) -/
def toNdL : List RN → List Nd
  | [] => []
  | k :: r => if k.isInp then toNdL r else toNd k :: toNdL r
def toNdT : List RN → List Nd
  | [] => []
  | _ :: r => toNdL r
end

mutual
/-- emittable trees: the child counts the node builders produce, and no input local directly under a fixed-arity node -/
def ok : RN → Bool
  | .mk t a b _ _ ks =>
    if t = 1 ∨ t = 2 then ks.isEmpty
    else if t = 3 ∨ t = 5 ∨ t = 10 then ks.length == 2 && okF ks
    else if t = 4 then ks.length == 4 && okF ks
    else if t = 11 then ks.length == 1 && okF ks
    else if t = 6 then okL ks
    else if t = 8 then b == ks.length && okL ks
    else if t = 9 then (if a < 4 then okT ks else okL ks)
    else false
/-- fixed-arity children: none is the input local -/
def okF : List RN → Bool
  | [] => true
  | k :: r => !k.isInp && ok k && okF r
/-- variadic children: input locals are allowed (and skipped) -/
def okL : List RN → Bool
  | [] => true
  | k :: r => (k.isInp || ok k) && okL r
/-- PRIM 1..3: a first child exists (it is dropped) -/
def okT : List RN → Bool
  | [] => false
  | _ :: r => okL r
end

/-- the visible children are the non-input ones -/
theorem vis_len (ks : List RN) : (toNdL ks).length = ks.length - cntInp ks ∧ cntInp ks ≤ ks.length := by
  induction ks with
  | nil => simp [toNdL, cntInp]
  | cons k r ih =>
    unfold cntInp at ih ⊢
    by_cases hk : k.isInp <;> simp [toNdL, hk, List.filter] <;> omega

mutual
theorem emit_ser : ∀ n : RN, ok n = true → emit n = (toNd n).ser
  | .mk t a b s p ks => by
    intro h
    unfold ok at h
    unfold emit toNd
    by_cases h1 : t = 1
    · subst h1; simp at h; subst h; simp [emitL, Nd.ser]
    by_cases h2 : t = 2
    · subst h2; simp at h; subst h; simp [emitL, Nd.ser]
    by_cases h3 : t = 3
    · subst h3
      simp at h
      match ks, h with
      | [x, y], h =>
        simp [okF] at h
        simp [emitL, h.1.1, h.2.1, emit_ser x h.1.2, emit_ser y h.2.2, Nd.ser]
    by_cases h4 : t = 4
    · subst h4
      simp at h
      match ks, h with
      | [x, y, u, v], h =>
        simp [okF] at h
        simp [emitL, h.1.1, h.2.1.1, h.2.2.1.1, h.2.2.2.1, emit_ser x h.1.2, emit_ser y h.2.1.2, emit_ser u h.2.2.1.2,
          emit_ser v h.2.2.2.2, Nd.ser]
    by_cases h5 : t = 5
    · subst h5
      simp at h
      match ks, h with
      | [x, y], h =>
        simp [okF] at h
        simp [emitL, h.1.1, h.2.1, emit_ser x h.1.2, emit_ser y h.2.2, Nd.ser]
    by_cases h6 : t = 6
    · subst h6
      simp at h
      have hv := (vis_len ks).1
      have hs := emitL_ser ks h
      simp only [true_and, if_true, ← hv, hs]
      match he : toNdL ks with
      | [] => simp [mkPairFlat, Nd.ser, serL]
      | [c] => simp [mkPairFlat, serL]
      | c :: d :: r => simp [mkPairFlat, Nd.ser]
    by_cases h8 : t = 8
    · subst h8
      simp at h
      have hv := (vis_len ks).1
      have hs := emitL_ser ks h.2
      simp [h.1, ← hv, hs, Nd.ser]
    by_cases h9 : t = 9
    · subst h9
      simp at h
      by_cases hx : a < 4
      · simp [hx] at h
        simp [hx, emitT_ser ks h, Nd.ser]
      · simp [hx] at h
        simp [hx, emitL_ser ks h, Nd.ser]
    by_cases h10 : t = 10
    · subst h10
      simp at h
      match ks, h with
      | [x, y], h =>
        simp [okF] at h
        simp [emitL, h.1.1, h.2.1, emit_ser x h.1.2, emit_ser y h.2.2, Nd.ser]
    by_cases h11 : t = 11
    · subst h11
      simp at h
      match ks, h with
      | [x], h =>
        simp [okF] at h
        simp [emitL, h.1, emit_ser x h.2, Nd.ser]
    simp [h1, h2, h3, h4, h5, h6, h8, h9, h10, h11] at h
theorem emitL_ser : ∀ ks : List RN, okL ks = true → emitL ks = serL (toNdL ks)
  | [] => by intro _; simp [emitL, toNdL, serL]
  | k :: r => by
    intro h
    simp [okL] at h
    by_cases hk : k.isInp
    · simp [emitL, toNdL, hk, emitL_ser r h.2]
    · simp [hk] at h
      simp [emitL, toNdL, hk, serL, emit_ser k h.1, emitL_ser r h.2]
theorem emitT_ser : ∀ ks : List RN, okT ks = true → emitT ks = serL (toNdT ks)
  | [] => by intro h; simp [okT] at h
  | _ :: r => by intro h; simp [okT] at h; simp [emitT, toNdT, emitL_ser r h]
end

end ParRun
