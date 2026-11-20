/- An UNTRUSTED register allocator for the liveness checker (`Live.lean`): interference from the same
liveness as `chk`, greedy colouring (most constrained first, move partners preferred).  Nothing here is
proved; its result is checked by `allocOK` (`Fn.lean`) inside the proved compilers. -/
import Nano.Base.Compiler.Opt.Live

namespace Proven.Mach.IR

/-- interference edges (and move pairs) of `c` with `L` live after it -/
def igIns (i : Ins Nat) (L : List Nat) : List (Nat × Nat) :=
  match i.dst with
  | some d => (L.filter fun x => x != d && i.mv != some x).map fun x => (d, x)
  | none => []

def mvIns (i : Ins Nat) : List (Nat × Nat) :=
  match i.dst, i.mv with
  | some d, some a => [(d, a)]
  | _, _ => []

def ig : Code Nat → List Nat → List (Nat × Nat) × List (Nat × Nat)
  | .skip, _ => ([], [])
  | .ins i, L => (igIns i L, mvIns i)
  | .seq a b, L => let A := ig a (lv b L); let B := ig b L; (A.1 ++ B.1, A.2 ++ B.2)
  | .when _ b, L => ig b L
  | .loop p t b, L =>
    let I := lvIter (lv p) (lv b) L t.regs 10 L
    let B := ig b I; let P := ig p (t.regs ++ lunion (lv b I) L); (B.1 ++ P.1, B.2 ++ P.2)
  | .loop2 p₁ t₁ p₂ t₂ b, L =>
    let I := lvIter2 (lv p₁) (lv p₂) (lv b) L t₁.regs t₂.regs 10 L
    let B := ig b I
    let L₂ := t₂.regs ++ lunion (lv b I) L
    let P₂ := ig p₂ L₂
    let P₁ := ig p₁ (t₁.regs ++ lunion (lv p₂ L₂) L)
    (B.1 ++ P₂.1 ++ P₁.1, B.2 ++ P₂.2 ++ P₁.2)

/-- greedy colouring.  `pin x`: a fixed register; `cols`: the registers free for the others (in order of
preference); `weight x`: higher is coloured earlier.  `none` when some register gets no colour. -/
def color (c : Code Nat) (out : List Nat) (pin : Nat → Option Reg) (cols : List Reg) (weight : Nat → Nat) :
    Option (Nat → Reg) :=
  let (E, Mv) := ig c out
  let nodes := (c.regs ++ out).eraseDups.filter fun x => (pin x).isNone
  let nbr := fun x => (E.filterMap fun (a, b) => if a = x then some b else if b = x then some a else none).eraseDups
  let deg := fun x => (nbr x).length
  let order := nodes.mergeSort fun a b => weight b < weight a || (weight b == weight a && deg b ≤ deg a)
  let step := fun (acc : Option (List (Nat × Reg))) (x : Nat) =>
    acc.bind fun asg =>
      let colOf := fun y => match pin y with | some r => some r | none => asg.lookup y
      let used := (nbr x).filterMap colOf
      let free := cols.filter fun r => !used.contains r
      let pref := (Mv.filterMap fun (a, b) => if a = x then colOf b else if b = x then colOf a else none).filter
        fun r => free.contains r
      match pref ++ free with
      | r :: _ => some ((x, r) :: asg)
      | [] => none
  (order.foldl step (some [])).map fun asg x => match pin x with | some r => r | none => (asg.lookup x).getD ⟨6, by decide⟩

/-- the nodes `color` leaves without a register (greedy, continuing past failures; untrusted, for spill choice) -/
def uncol (c : Code Nat) (out : List Nat) (pin : Nat → Option Reg) (cols : List Reg) (weight : Nat → Nat) :
    List Nat :=
  let (E, Mv) := ig c out
  let nodes := (c.regs ++ out).eraseDups.filter fun x => (pin x).isNone
  let nbr := fun x => (E.filterMap fun (a, b) => if a = x then some b else if b = x then some a else none).eraseDups
  let deg := fun x => (nbr x).length
  let order := nodes.mergeSort fun a b => weight b < weight a || (weight b == weight a && deg b ≤ deg a)
  let step := fun (acc : List (Nat × Reg) × List Nat) (x : Nat) =>
    let colOf := fun y => match pin y with | some r => some r | none => acc.1.lookup y
    let used := (nbr x).filterMap colOf
    let free := cols.filter fun r => !used.contains r
    let pref := (Mv.filterMap fun (a, b) => if a = x then colOf b else if b = x then colOf a else none).filter
      fun r => free.contains r
    match pref ++ free with
    | r :: _ => ((x, r) :: acc.1, acc.2)
    | [] => (acc.1, x :: acc.2)
  (order.foldl step ([], [])).2

end Proven.Mach.IR
