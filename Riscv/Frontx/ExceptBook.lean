/- Round 7: the `Option` / `Except` examples of "Functional Programming in Lean", chapter 5 (Monads), verbatim
(github.com/leanprover/fp-lean @ 0abeea5, `examples/Examples/Monads.lean:18-135, 163-300`; anchors, `#eval`s and
the `String` list `ediblePlants` dropped).  Lists are views of the input (`frontx_view`, `α := UInt8`); results
`Option (α × α)` etc. are a tag byte and the payload, `Except String _` a tag byte (`0` = error, the message is
not kept) and the payload. -/
import Riscv.Frontx.Impl1
import Riscv.Frontx.PairExamples

namespace Monads.Option
variable {α : Type}

def first (xs : List α) : Option α :=
  xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)

def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)

def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)

namespace M
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)

namespace ExplicitParens
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))
end ExplicitParens

infixl:55 " ~~> " => andThen

def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)

def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)
end M

end Monads.Option

namespace Monads.Err

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

def first (xs : List α) : Except String α :=
  get xs 0

def firstThird (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      Except.ok (first, third)

def firstThirdFifth (xs : List α) : Except String (α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        Except.ok (first, third, fifth)

def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        match get xs 6 with
        | Except.error msg => Except.error msg
        | Except.ok seventh =>
          Except.ok (first, third, fifth, seventh)

def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x

namespace AndThen
def firstThird' (xs : List α) : Except String (α × α) :=
  andThen (get xs 0) fun first  =>
  andThen (get xs 2) fun third =>
  Except.ok (first, third)
end AndThen

infixl:55 " ~~> " => andThen

def ok (x : α) : Except ε α := Except.ok x

def fail (err : ε) : Except ε α := Except.error err

namespace Eff
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x
end Eff

namespace WithInfix
def firstThird (xs : List α) : Except String (α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  ok (first, third)

def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)
end WithInfix

end Monads.Err

namespace Proven.Frontx.ExcBook
open Proven Proven.Frontx

frontx_view Monads.Option.firstThird
frontx_compile Monads.Option.firstThird.view from Monads.Option.firstThird.view.eq measure fun _ _ => 0
frontx_view Monads.Option.firstThirdFifth
frontx_compile Monads.Option.firstThirdFifth.view from Monads.Option.firstThirdFifth.view.eq measure fun _ _ => 0
frontx_view Monads.Option.firstThirdFifthSeventh
frontx_compile Monads.Option.firstThirdFifthSeventh.view from Monads.Option.firstThirdFifthSeventh.view.eq measure fun _ _ => 0
frontx_view Monads.Option.M.firstThird
frontx_compile Monads.Option.M.firstThird.view from Monads.Option.M.firstThird.view.eq measure fun _ _ => 0
frontx_view Monads.Option.M.ExplicitParens.firstThird
frontx_compile Monads.Option.M.ExplicitParens.firstThird.view from Monads.Option.M.ExplicitParens.firstThird.view.eq measure fun _ _ => 0
frontx_view Monads.Option.M.firstThirdInfix
frontx_compile Monads.Option.M.firstThirdInfix.view from Monads.Option.M.firstThirdInfix.view.eq measure fun _ _ => 0
frontx_view Monads.Err.first
frontx_compile Monads.Err.first.view from Monads.Err.first.view.eq measure fun _ _ => 0
frontx_view Monads.Err.firstThird
frontx_compile Monads.Err.firstThird.view from Monads.Err.firstThird.view.eq measure fun _ _ => 0
frontx_view Monads.Err.firstThirdFifth
frontx_compile Monads.Err.firstThirdFifth.view from Monads.Err.firstThirdFifth.view.eq measure fun _ _ => 0
frontx_view Monads.Err.AndThen.firstThird'
frontx_compile Monads.Err.AndThen.firstThird'.view from Monads.Err.AndThen.firstThird'.view.eq measure fun _ _ => 0
frontx_view Monads.Err.WithInfix.firstThird
frontx_compile Monads.Err.WithInfix.firstThird.view from Monads.Err.WithInfix.firstThird.view.eq measure fun _ _ => 0

frontx_view Monads.Option.M.firstThirdFifthSeventh
frontx_compile Monads.Option.M.firstThirdFifthSeventh.view from Monads.Option.M.firstThirdFifthSeventh.view.eq measure fun _ _ => 0
frontx_view Monads.Err.firstThirdFifthSeventh
frontx_compile Monads.Err.firstThirdFifthSeventh.view from Monads.Err.firstThirdFifthSeventh.view.eq measure fun _ _ => 0
frontx_view Monads.Err.WithInfix.firstThirdFifthSeventh
frontx_compile Monads.Err.WithInfix.firstThirdFifthSeventh.view from Monads.Err.WithInfix.firstThirdFifthSeventh.view.eq measure fun _ _ => 0

/-! Entry points (glue): the list is the whole input. -/
def optFirstThirdE (xs : ByteArray) : Option (UInt8 × UInt8) := Monads.Option.firstThird.view xs 0
frontx_entry optFirstThirdE
frontx_implements_bytes optFirstThirdE
def optMFirstThirdE (xs : ByteArray) : Option (UInt8 × UInt8) := Monads.Option.M.firstThird.view xs 0
frontx_entry optMFirstThirdE
frontx_implements_bytes optMFirstThirdE
def optParensFirstThirdE (xs : ByteArray) : Option (UInt8 × UInt8) := Monads.Option.M.ExplicitParens.firstThird.view xs 0
frontx_entry optParensFirstThirdE
frontx_implements_bytes optParensFirstThirdE
def optInfixFirstThirdE (xs : ByteArray) : Option (UInt8 × UInt8) := Monads.Option.M.firstThirdInfix.view xs 0
frontx_entry optInfixFirstThirdE
frontx_implements_bytes optInfixFirstThirdE
def errFirstE (xs : ByteArray) : Except String UInt8 := Monads.Err.first.view xs 0
frontx_entry errFirstE
frontx_implements_bytes errFirstE
def errFirstThirdE (xs : ByteArray) : Except String (UInt8 × UInt8) := Monads.Err.firstThird.view xs 0
frontx_entry errFirstThirdE
frontx_implements_bytes errFirstThirdE
def errAndThenFirstThirdE (xs : ByteArray) : Except String (UInt8 × UInt8) := Monads.Err.AndThen.firstThird'.view xs 0
frontx_entry errAndThenFirstThirdE
frontx_implements_bytes errAndThenFirstThirdE
def errInfixFirstThirdE (xs : ByteArray) : Except String (UInt8 × UInt8) := Monads.Err.WithInfix.firstThird.view xs 0
frontx_entry errInfixFirstThirdE
frontx_implements_bytes errInfixFirstThirdE

end Proven.Frontx.ExcBook
