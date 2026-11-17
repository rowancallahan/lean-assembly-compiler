import Nano.V2.Gen
/- nano v2 first example (round 2 §7): byte copy, through the small backend.
`copy fuel s := match fuel with | 0 => fail 1 | n+1 => if i ≥ size then ok else if full then fail 2 else
copy n (i+1, push out input[i])`; state s = (i, out). -/
namespace Nano.V2

/-- the typed AST of the byte copy, with fuel `F` and output capacity `C` -/
def copyProg (F C : Nat) : Prog where
  main := .loop (.lit F.toUInt64) (.pair (.lit 0) (.mk C))
    (.split (.var 0) (.pair (.lit 1) (.var 0)))
    (.split (.var 0)
      (.ite .ge (.var 1) .isize (.ret (.pair (.lit 0) (.var 0)))
        (.ite .lt (.size (.var 0)) (.lit C.toUInt64)
          (.next (.pair (.bin .add (.var 1) (.lit 1)) (.push (.var 0) (.iget (.var 1)))))
          (.ret (.pair (.lit 2) (.var 0))))))

/-- the same function as ordinary Lean (the source the front end would accept) -/
def copyStep (C : Nat) (inp : Array UInt64) (s : UInt64 × Array UInt64) :
    Sum (UInt64 × Array UInt64) (UInt64 × Array UInt64) :=
  let (i, out) := s
  if inp.size.toUInt64 ≤ i then .inl (0, out)
  else if out.size.toUInt64 < C.toUInt64 then .inr (i + 1, out.push inp[i.toNat]!)
  else .inl (2, out)

def copyRun (C : Nat) (inp : Array UInt64) : Nat → UInt64 × Array UInt64 → UInt64 × Array UInt64
  | 0, (_, out) => (1, out)
  | n + 1, s => match copyStep C inp s with
    | .inl r => r
    | .inr s' => copyRun C inp n s'

def copyLean (F C : Nat) (input : List UInt8) : Except UInt64 (List UInt8) :=
  let r := copyRun C (input.map (·.toUInt64)).toArray (F.toUInt64.toNat) (0, Array.mkEmpty C)
  if r.1 = 0 then .ok (r.2.toList.map (·.toUInt8)) else .error r.1

end Nano.V2
