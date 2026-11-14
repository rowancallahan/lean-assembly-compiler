/- Arithmetic expression trees and their byte format (prefix encoding).  Part of the input format of the
spec, like `Spec/Encode.lean`.  Pure Lean, no machine model.

Format: a leaf is the tag byte `0` followed by its value byte; a node is its operator's tag byte
(`1` add, `2` sub, `3` xor) followed by the encoding of the left, then of the right subtree. -/
import Spec.Encode

namespace Proven

inductive TOp where
  | add | sub | xor

def TOp.tag : TOp → UInt8
  | .add => 1 | .sub => 2 | .xor => 3

def TOp.eval : TOp → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .xor, a, b => a ^^^ b

inductive Tree where
  | leaf (v : UInt8)
  | node (op : TOp) (l r : Tree)

/-- the value of a tree in 64-bit words (the reference of the tree evaluator) -/
def Tree.eval : Tree → BitVec 64
  | .leaf v => BitVec.ofNat 64 v.toNat
  | .node op l r => op.eval l.eval r.eval

/-- nesting depth of nodes (a leaf has depth 0) -/
def Tree.depth : Tree → Nat
  | .leaf _ => 0
  | .node _ l r => 1 + max l.depth r.depth

def Tree.enc : Tree → List UInt8
  | .leaf v => [0, v]
  | .node op l r => op.tag :: (l.enc ++ r.enc)

def TOp.ofTag (t : UInt8) : Option TOp :=
  if t = 1 then some .add else if t = 2 then some .sub else if t = 3 then some .xor else none

/-- decode one tree off the front, with fuel (the number of bytes is always enough) -/
def Tree.decF : Nat → List UInt8 → Option (Tree × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, t :: bs =>
    if t = 0 then
      match bs with
      | v :: r => some (.leaf v, r)
      | [] => none
    else
      match TOp.ofTag t with
      | none => none
      | some op => (Tree.decF f bs).bind fun (l, r₁) => (Tree.decF f r₁).map fun (r, r₂) => (.node op l r, r₂)

theorem Tree.decF_enc : ∀ (t : Tree) (f : Nat) (rest : List UInt8), t.enc.length ≤ f →
    Tree.decF f (t.enc ++ rest) = some (t, rest)
  | .leaf v, f + 1, rest, _ => by simp [Tree.enc, Tree.decF]
  | .leaf v, 0, rest, h => by simp [Tree.enc] at h
  | .node op l r, 0, rest, h => by simp [Tree.enc] at h
  | .node op l r, f + 1, rest, h => by
    have hl : l.enc.length ≤ f := by simp [Tree.enc] at h; omega
    have hr : r.enc.length ≤ f := by simp [Tree.enc] at h; omega
    have e1 := Tree.decF_enc l f (r.enc ++ rest) hl
    have e2 := Tree.decF_enc r f rest hr
    cases op <;> simp [Tree.enc, Tree.decF, TOp.tag, TOp.ofTag, List.append_assoc, e1, e2]

instance : Bytes Tree where
  enc := Tree.enc
  dec bs := Tree.decF bs.length bs
  dec_enc t rest := Tree.decF_enc t _ rest (by simp)

/-- the depth is bounded by the size of the encoding -/
theorem Tree.depth_le : ∀ t : Tree, t.depth + 2 ≤ t.enc.length
  | .leaf _ => by simp [Tree.depth, Tree.enc]
  | .node _ l r => by
    have := Tree.depth_le l; have := Tree.depth_le r
    simp [Tree.depth, Tree.enc]; omega

example : enc (Tree.node .add (.leaf 2) (.node .xor (.leaf 5) (.leaf 1))) = [1, 0, 2, 3, 0, 5, 0, 1] := rfl
example : (decAll (α := Tree) [1, 0, 2, 3, 0, 5, 0, 1]).map Tree.eval = some 6 := by decide

end Proven
