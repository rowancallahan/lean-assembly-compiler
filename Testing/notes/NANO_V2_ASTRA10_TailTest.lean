namespace TailTest
inductive E where
  | val
  | self (good : Bool) (state : E)
  | group (x : E)
  | strict (a b : E)
  | bind (v body : E)
  | cond (a b yes no : E)
  deriving Repr

def ok (tail : Bool) : E → Bool
  | .val => true
  | .self good s => tail && good && ok false s
  | .group x => ok tail x
  | .strict a b => ok false a && ok false b
  | .bind v b => ok false v && ok tail b
  | .cond a b y n => ok false a && ok false b && ok tail y && ok tail n

def mix (s : UInt64) := s * 6364136223846793005 + 1442695040888963407

def gen : Nat → UInt64 → E
  | 0, s => if s % 3 == 0 then .self true .val else .val
  | n+1, s =>
    let a := mix s
    let b := mix a
    match (a / 65536 % 6).toNat with
    | 0 => .group (gen n b)
    | 1 => .self (b % 5 != 0) (gen n b)
    | 2 => .bind (gen n a) (gen n b)
    | 3 => .strict (gen n a) (gen n b)
    | 4 => .cond .val .val (gen n a) (gen n b)
    | _ => .cond (gen n b) .val .val .val
end TailTest
#eval (List.range 200).filter (fun i => TailTest.ok true (TailTest.gen 5 (TailTest.mix i.toUInt64))) |>.length
