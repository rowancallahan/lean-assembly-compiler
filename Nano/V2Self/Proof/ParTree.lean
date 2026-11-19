/- Nano/V2Self/Proof/ParTree: RAW arena trees of the parser (Par1) and the pure flatten function.  No heap, no machine (parser lead).
* `RNd` is exactly the 8-word node record of the arena (tag, payload 1, payload 2, shape CODE, pending bit) with its children in chain order.
  The machine-side state of the proof (operand stack, Layer 2 `St`) holds `RNd`s, not `ParSpec.Nd`s: Par1 validates late (`v209`/`v210` at the
  next def boundary), so the arena legally holds trees with no spec counterpart, and it keeps children the IR does not have.
* `isInp` : the width-0 INPUT LOCAL as the machine tests it (tag 2, payload 2 = 0; `v205`, `v143`, `v141`).
* `emit`  : the words tasks 81/82 (`v142`/`v143`) push for a tree: input-local children are skipped, PRIM 1..3 drop their first child,
  CALL writes `p2 - #input children`, a PAIR with exactly one visible child is elided.
* `erase` : the `ParSpec.Nd` a raw tree stands for (`dropInp` / `mkPairFlat` made explicit).
* `ok`    : child counts as the node builders produce them, no input local under a fixed-arity node (what `v209` leaves).
* `emit_ser : ok t → emit t = (erase t).ser`. -/
import Nano.V2Self.Proof.ParSpec
namespace ParInv
open ParSpec

inductive RNd where
  | mk (tag p1 p2 sh pend : UInt64) (kids : List RNd)

namespace RNd
def tag : RNd → UInt64 | mk t _ _ _ _ _ => t
def p1 : RNd → UInt64 | mk _ x _ _ _ _ => x
def p2 : RNd → UInt64 | mk _ _ y _ _ _ => y
def sh : RNd → UInt64 | mk _ _ _ w _ _ => w
def pend : RNd → UInt64 | mk _ _ _ _ p _ => p
def kids : RNd → List RNd | mk _ _ _ _ _ ks => ks

/-- the INPUT LOCAL as every machine test reads it: tag 2 (LOCAL) with payload 2 (width) = 0 -/
def isInp (t : RNd) : Bool := t.tag == 2 && t.p2 == 0
end RNd

/-- number of input-local children (`v205`) -/
def cntInp (ks : List RNd) : Nat := (ks.filter RNd.isInp).length

mutual
/-- the words `v142` (task 81) and its child loop `v143` (task 82) push for a tree, in preorder -/
def emit : RNd → List UInt64
  | .mk t x y _ _ ks =>
    let n : UInt64 := ks.length.toUInt64
    let c : UInt64 := (cntInp ks).toUInt64
    if t == 6 && n - c == 1 then emitL ks
    else
      t :: ((if t == 6 then [n - c] else if t < 10 then [x] else []) ++
            (if t == 2 || t == 5 then [y] else if t == 8 then [y - c] else []) ++
            (if t == 9 && x < 4 then emitT ks else emitL ks))
/-- children: input locals are skipped -/
def emitL : List RNd → List UInt64
  | [] => []
  | k :: r => (if k.isInp then [] else emit k) ++ emitL r
/-- children of PRIM 1..3: the first one (the input) is dropped unconditionally -/
def emitT : List RNd → List UInt64
  | [] => []
  | _ :: r => emitL r
end

mutual
/-- the spec node of a raw tree -/
def erase : RNd → Nd
  | .mk t x y _ _ ks =>
    if t == 1 then .const x
    else if t == 2 then .loc x.toNat y.toNat
    else if t == 3 then (match ks with | [a, b] => .bin x.toNat (erase a) (erase b) | _ => .const 0)
    else if t == 4 then (match ks with | [a, b, c, d] => .ite x.toNat (erase a) (erase b) (erase c) (erase d) | _ => .const 0)
    else if t == 5 then (match ks with | [v, b] => .letE x.toNat y.toNat (erase v) (erase b) | _ => .const 0)
    else if t == 6 then mkPairFlat (eraseL ks)
    else if t == 8 then .call x.toNat (eraseL ks)
    else if t == 9 then .prim x.toNat (if x < 4 then eraseT ks else eraseL ks)
    else if t == 10 then (match ks with | [z, s] => .loop (erase z) (erase s) | _ => .const 0)
    else (match ks with | [e] => .cont (erase e) | _ => .const 0)
def eraseL : List RNd → List Nd
  | [] => []
  | k :: r => if k.isInp then eraseL r else erase k :: eraseL r
def eraseT : List RNd → List Nd
  | [] => []
  | _ :: r => eraseL r
end

mutual
/-- emittable trees: the child counts the node builders produce, and no input local directly under a fixed-arity node -/
def ok : RNd → Bool
  | .mk t x y _ _ ks =>
    if t == 1 || t == 2 then ks.isEmpty
    else if t == 3 || t == 5 || t == 10 then ks.length == 2 && okF ks
    else if t == 4 then ks.length == 4 && okF ks
    else if t == 11 then ks.length == 1 && okF ks
    else if t == 6 then decide (ks.length < 2 ^ 64) && okL ks
    else if t == 8 then decide (ks.length < 2 ^ 64) && y == ks.length.toUInt64 && okL ks
    else if t == 9 then (if x < 4 then okT ks else okL ks)
    else false
/-- fixed-arity children: none is the input local -/
def okF : List RNd → Bool
  | [] => true
  | k :: r => !k.isInp && ok k && okF r
/-- variadic children: input locals are allowed (and skipped) -/
def okL : List RNd → Bool
  | [] => true
  | k :: r => (k.isInp || ok k) && okL r
/-- PRIM 1..3: a first child exists (it is dropped) -/
def okT : List RNd → Bool
  | [] => false
  | _ :: r => okL r
end

/-- fixed-arity children, erased one by one -/
def eraseF : List RNd → List Nd
  | [] => []
  | k :: r => erase k :: eraseF r

theorem toU64_toNat (x : UInt64) : x.toNat.toUInt64 = x := by
  apply UInt64.toNat_inj.mp; simp [Nat.toUInt64]

/-- `n - c` on words is the number of visible children -/
theorem vis_len (ks : List RNd) (hl : ks.length < 2 ^ 64) :
    ks.length.toUInt64 - (cntInp ks).toUInt64 = (eraseL ks).length.toUInt64 := by
  have key : ∀ ks : List RNd, (eraseL ks).length + cntInp ks = ks.length := by
    intro ks
    induction ks with
    | nil => simp [eraseL, cntInp]
    | cons k r ih =>
      unfold cntInp at ih ⊢
      by_cases hk : k.isInp <;> simp [eraseL, hk, List.filter] <;> omega
  have h1 := key ks
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp [Nat.toUInt64]; omega)]
  simp [Nat.toUInt64]; omega

mutual
theorem emit_ser : ∀ t : RNd, ok t = true → emit t = (erase t).ser
  | .mk t x y w p ks => by
    intro h
    unfold ok at h
    unfold emit erase
    by_cases h1 : t = 1
    · subst h1; simp at h; subst h; simp [emitL, Nd.ser]
    by_cases h2 : t = 2
    · subst h2; simp at h; subst h; simp [emitL, Nd.ser]
    by_cases h3 : t = 3
    · subst h3
      simp at h
      match ks, h with
      | [a, b], h =>
        simp [okF] at h
        simp [emitL, h.1.1, h.2.1, emit_ser a h.1.2, emit_ser b h.2.2, Nd.ser]
    by_cases h4 : t = 4
    · subst h4
      simp at h
      match ks, h with
      | [a, b, c, d], h =>
        simp [okF] at h
        simp [emitL, h.1.1, h.2.1.1, h.2.2.1.1, h.2.2.2.1, emit_ser a h.1.2, emit_ser b h.2.1.2, emit_ser c h.2.2.1.2,
          emit_ser d h.2.2.2.2, Nd.ser]
    by_cases h5 : t = 5
    · subst h5
      simp at h
      match ks, h with
      | [a, b], h =>
        simp [okF] at h
        simp [emitL, h.1.1, h.2.1, emit_ser a h.1.2, emit_ser b h.2.2, Nd.ser]
    by_cases h6 : t = 6
    · subst h6
      simp at h
      have hv := vis_len ks h.1
      have hs := emitL_ser ks h.2
      simp only [beq_self_eq_true, Bool.true_and, if_true, hv, hs]
      have hlen : (eraseL ks).length < 2 ^ 64 := by
        have : ∀ ks : List RNd, (eraseL ks).length ≤ ks.length := by
          intro ks; induction ks with
          | nil => simp [eraseL]
          | cons k r ih => by_cases hk : k.isInp <;> simp [eraseL, hk] <;> omega
        have := this ks; omega
      match he : eraseL ks with
      | [] => simp [mkPairFlat, Nd.ser, serL]
      | [c] => simp [mkPairFlat, serL]
      | c :: d :: r =>
        have : ¬ ((c :: d :: r).length.toUInt64 = 1) := by
          intro e
          have e2 := congrArg UInt64.toNat e
          rw [he] at hlen
          simp [Nat.toUInt64] at e2 hlen
          omega
        simp at this
        simp [mkPairFlat, Nd.ser]
        intro e; exact absurd e this
    by_cases h8 : t = 8
    · subst h8
      simp at h
      have hv := vis_len ks h.1.1
      have hs := emitL_ser ks h.2
      simp [h.1.2, hv, hs, Nd.ser]
    by_cases h9 : t = 9
    · subst h9
      simp at h
      by_cases hx : x < 4
      · simp [hx] at h
        simp [hx, emitT_ser ks h, Nd.ser]
      · simp [hx] at h
        simp [hx, emitL_ser ks h, Nd.ser]
    by_cases h10 : t = 10
    · subst h10
      simp at h
      match ks, h with
      | [a, b], h =>
        simp [okF] at h
        simp [emitL, h.1.1, h.2.1, emit_ser a h.1.2, emit_ser b h.2.2, Nd.ser]
    by_cases h11 : t = 11
    · subst h11
      simp at h
      match ks, h with
      | [a], h =>
        simp [okF] at h
        simp [emitL, h.1, emit_ser a h.2, Nd.ser]
    simp [h1, h2, h3, h4, h5, h6, h8, h9, h10, h11] at h
theorem emitL_ser : ∀ ks : List RNd, okL ks = true → emitL ks = serL (eraseL ks)
  | [] => by intro _; simp [emitL, eraseL, serL]
  | k :: r => by
    intro h
    simp [okL] at h
    by_cases hk : k.isInp
    · simp [emitL, eraseL, hk, emitL_ser r h.2]
    · simp [hk] at h
      simp [emitL, eraseL, hk, serL, emit_ser k h.1, emitL_ser r h.2]
theorem emitT_ser : ∀ ks : List RNd, okT ks = true → emitT ks = serL (eraseT ks)
  | [] => by intro h; simp [okT] at h
  | _ :: r => by intro h; simp [okT] at h; simp [emitT, eraseT, emitL_ser r h]
end

end ParInv
