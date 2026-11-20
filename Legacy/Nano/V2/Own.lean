import Nano.Base.V2.Lang
/- nano v2: the OWNERSHIP checker (`Ex.lv`), moved from Nano/V2/Front.lean so the back-end proofs can use it
(Nano/V2/CompB.lean: accepted programs satisfy the discipline the buffer proof assumes). -/
namespace Nano.V2B

/-! ## ownership: a buffer-holding variable occurs at most once -/
def Ty.hasBuf : Ty → Bool
  | .w => false | .buf => true | .prod a b => a.hasBuf || b.hasBuf

/- READ-ONLY use of variable `k`: only borrows (`size (var k)`, `get (var k) _`) and read-only aliases
`let a := var k; b` (with `b` read-only on `a`); loop bodies are closed (no outer use) -/
mutual
def Ex.ro (k : Nat) : Ex → Bool
  | .var i => i != k
  | .size (.var _) => true
  | .get (.var _) j => j.ro k
  | .let_ (.var i) b => if i = k then b.ro 0 && b.ro (k + 1) else b.ro (k + 1)
  | .bin _ a b | .pair a b | .get a b | .push a b => a.ro k && b.ro k
  | .set a b c => a.ro k && b.ro k && c.ro k
  | .size a | .fst a | .snd a | .iget a => a.ro k
  | .ite _ a b t e => a.ro k && b.ro k && t.ro k && e.ro k
  | .let_ v b => v.ro k && b.ro (k + 1)
  | .split e b => e.ro k && b.ro (k + 2)
  | .loop f i z t => f.ro k && i.ro k && z.ro (k + 1) && t.ro (k + 1)
  | _ => true
def Tl.ro (k : Nat) : Tl → Bool
  | .ret e | .next e => e.ro k
  | .ite _ a b t e => a.ro k && b.ro k && t.ro k && e.ro k
  | .let_ v b => v.ro k && b.ro (k + 1)
  | .split e b => e.ro k && b.ro (k + 2)
end

/-- OWNERSHIP (affine, Astra r3 §4): walking in evaluation order, a buffer-holding variable is CONSUMED by every use
except a BORROW (`size (var i)`, `get (var i) _`, and the buffer of `set`/`push` while their other arguments run);
a dead variable may not be used again; `if` branches start from the same state and the most restrictive state
continues; loop bodies may use no outer buffer.  READ-ONLY ALIAS: `let a := var j; b` with `b` read-only on `a`
(`Ex.ro`) does not consume `j`; during `b` both are READ-ONLY (borrows only).  This is how an inlined helper
borrows a `Buf` parameter.  Flags (de Bruijn): 0 live, 1 read-only, 2 dead. -/
def dead (d : List Nat) (i : Nat) : Bool := d.getD i 0 == 2
def live (d : List Nat) (i : Nat) : Bool := d.getD i 0 == 0
def kill (env : List Ty) (d : List Nat) (i : Nat) : List Nat :=
  if (env.getD i .w).hasBuf then d.set i 2 else d
/-- inside a loop body every outer buffer is at most read-only -/
def killAll (env : List Ty) (d : List Nat) : List Nat :=
  (d.zip env).map fun (x, τ) => if τ.hasBuf then max x 1 else x
def orL (a b : List Nat) : List Nat := (a.zip b).map fun (x, y) => max x y
/-- consuming a variable: allowed only if live (a read-only buffer may not be moved) -/
def use (env : List Ty) (d : List Nat) (i : Nat) : Option (List Nat) :=
  if (env.getD i .w).hasBuf then (if live d i then some (kill env d i) else none) else some d

mutual
def Ex.lv : List Ty → List Nat → Ex → Option (List Nat)
  | env, d, .var i => use env d i
  | _, d, .size (.var i) => if dead d i then none else some d
  | env, d, .get (.var i) j => if dead d i then none else
      -- `i`'s address is pushed before `j` runs: `j` may not consume (mutate in place) `i`
      match j.lv env d with
      | some d1 => if dead d1 i then none else some d1
      | none => none
  | env, d, .set (.var i) j x => if live d i then
      match j.lv env d with
      | some d1 => match x.lv env d1 with
        | some d2 => use env d2 i
        | none => none
      | none => none
    else none
  | env, d, .push (.var i) x => if live d i then
      match x.lv env d with
      | some d2 => use env d2 i
      | none => none
    else none
  | env, d, .let_ (.var j) b => match env[j]? with
    | some τ =>
      if τ.hasBuf && b.ro 0 then
        -- read-only alias: `j` and the alias are read-only during `b`, `j` keeps its state afterwards
        if dead d j then none else
        let dj := d.getD j 0
        (b.lv (τ :: env) (1 :: d.set j (max dj 1))).map fun d' => (d'.tail).set j dj
      else
        match use env d j with
        | some d1 => (b.lv (τ :: env) (0 :: d1)).map List.tail
        | none => none
    | none => none
  | env, d, .bin _ a b | env, d, .pair a b | env, d, .get a b | env, d, .push a b =>
      match a.lv env d with
      | some d1 => b.lv env d1
      | none => none
  | env, d, .set a b c =>
      match a.lv env d with
      | some d1 => match b.lv env d1 with
        | some d2 => c.lv env d2
        | none => none
      | none => none
  | env, d, .size a | env, d, .fst a | env, d, .snd a | env, d, .iget a => a.lv env d
  | env, d, .ite _ a b t e =>
      match a.lv env d with
      | some d1 => match b.lv env d1 with
        | some d2 => match t.lv env d2, e.lv env d2 with
          | some x, some y => some (orL x y)
          | _, _ => none
        | none => none
      | none => none
  | env, d, .let_ v b => match tyOf env v, v.lv env d with
    | some τ, some d1 => (b.lv (τ :: env) (0 :: d1)).map List.tail
    | _, _ => none
  | env, d, .split e b => match tyOf env e, e.lv env d with
    | some (.prod τ σ), some d1 => (b.lv (σ :: τ :: env) (0 :: 0 :: d1)).map (·.drop 2)
    | _, _ => none
  | env, d, .loop f i z t => match tyOf env i with
    | some σ =>
      match f.lv env d with
      | some d1 => match i.lv env d1 with
        | some d2 =>
          let da := 0 :: killAll env d2
          if (z.lv (σ :: env) da).isSome && (t.lvT (σ :: env) da).isSome then some d2 else none
        | none => none
      | none => none
    | none => none
  | _, d, _ => some d
def Tl.lvT : List Ty → List Nat → Tl → Option (List Nat)
  | env, d, .ret e | env, d, .next e => e.lv env d
  | env, d, .ite _ a b t e =>
      match a.lv env d with
      | some d1 => match b.lv env d1 with
        | some d2 => match t.lvT env d2, e.lvT env d2 with
          | some x, some y => some (orL x y)
          | _, _ => none
        | none => none
      | none => none
  | env, d, .let_ (.var j) b => match env[j]? with
    | some τ =>
      if τ.hasBuf && b.ro 0 then
        if dead d j then none else
        let dj := d.getD j 0
        (b.lvT (τ :: env) (1 :: d.set j (max dj 1))).map fun d' => (d'.tail).set j dj
      else
        match use env d j with
        | some d1 => (b.lvT (τ :: env) (0 :: d1)).map List.tail
        | none => none
    | none => none
  | env, d, .let_ v b => match tyOf env v, v.lv env d with
    | some τ, some d1 => (b.lvT (τ :: env) (0 :: d1)).map List.tail
    | _, _ => none
  | env, d, .split e b => match tyOf env e, e.lv env d with
    | some (.prod τ σ), some d1 => (b.lvT (σ :: τ :: env) (0 :: 0 :: d1)).map (·.drop 2)
    | _, _ => none
end

end Nano.V2B
