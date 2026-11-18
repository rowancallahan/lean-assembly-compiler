import Nano.V2Self.C.Lex2
import Nano.V2Self.C.Par1
/- Astra-12 regression programs through the real lexer and the folded parser (Par1).  VALID programs must be accepted (non-empty), NEGATIVE ones rejected.
run (small layout recommended): LEAN_PATH=/tmp/o_small:/tmp/o lean --run Testing/nano/v2self/par1_test.lean -/
def prog (l : List String) : String := "\n".intercalate l ++ "\n"
def valid : List (String × String) := [
  ("pair-build", "def f (x : UInt64) : UInt64 × UInt64 := (x, x)\n"),
  ("pair-destructure", "def f (x : UInt64 × UInt64) : UInt64 := let (a, b) := x; b\n"),
  ("main-put", "def m (x : List UInt8) : List UInt8 := put [] (rd x 0)\n"),
  ("call-bytes", prog ["def f (x : List UInt8) (a : UInt64) : List UInt8 := put [] (rd x a)", "def m (x : List UInt8) : List UInt8 := f x 1"]),
  ("prim-bsize", "def f (x : Buf) : UInt64 := bsize (bpush x 1)\n"),
  ("loop-plain", prog ["def f : Nat → UInt64 → UInt64", "  | 0, s => s", "  | n + 1, s => f n s"]),
  ("loop-let", prog ["def f : Nat → UInt64 → UInt64", "  | 0, s => s", "  | n + 1, s => let x := s; f n x"]),
  ("loop-input", prog ["def f : Nat → List UInt8 → UInt64 → UInt64", "  | 0, x, s => s", "  | n + 1, x, s => f n x (s + rd x s)"]),
  ("call-loop-main", prog ["def f : Nat → List UInt8 → UInt64 → UInt64", "  | 0, x, s => s", "  | n + 1, x, s => f n x (s + rd x s)", "def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0)"]),
  ("loop-2state", prog ["def f : Nat → UInt64 → UInt64 → UInt64", "  | 0, a, b => a", "  | n + 1, a, b => f n b a"])]
def negative : List (String × String) := [
  -- ParSpec differential findings (2026-11-18), fixed in Par1: input as data / as the body, rd on a non-input list, `List <not UInt8>`, loop with only the input as state, duplicate pattern names
  ("input-as-body", "def m (x : List UInt8) : List UInt8 := x\n"),
  ("input-as-put-arg", "def m (x : List UInt8) : List UInt8 := put x 1\n"),
  ("input-let", "def m (x : List UInt8) : List UInt8 := let y := x; put [] 1\n"),
  ("rd-non-input", "def g (z : List UInt8) (a : List UInt8) : UInt64 := rd a 0\n"),
  ("list-not-uint8", "def g (z : List def) : UInt64 := 1\n"),
  ("loop-only-input", prog ["def f : Nat → List UInt8 → UInt64 × UInt64", "  | 0, z => (1, 2)", "  | n + 1, z => f n z"]),
  ("loop-dup-pattern", prog ["def f : Nat → UInt64 → UInt64 → UInt64", "  | 0, a, a => a", "  | n + 1, a, b => a"]),
  ("call-input-swapped", prog ["def f (z : List UInt8) (a : List UInt8) : UInt64 := 1", "def g (x : List UInt8) : UInt64 := f [] x"]),
  ("call-input-twice", prog ["def f (z : List UInt8) (a : List UInt8) : UInt64 := 1", "def g (x : List UInt8) : UInt64 := f x x"]),
  ("cont-input-swapped", prog ["def f : Nat → List UInt8 → List UInt8 → UInt64", "  | 0, z, a => 1", "  | n + 1, z, a => f n [] z"]),
  ("loop-fuel-dup", prog ["def f : Nat → UInt64 → UInt64", "  | 0, a => a", "  | n + 1, n => n"]),
  ("pair-of-word", "def f (x : UInt64) : UInt64 := let (a, b) := x; a\n"),
  ("pair-result-mismatch", "def f (x : UInt64) : UInt64 := (x, x)\n"),
  ("call-width", prog ["def f (x : UInt64) : UInt64 := x", "def m (x : List UInt8) : List UInt8 := f x"]),
  ("loop-nontail-plus", prog ["def f : Nat → UInt64 → UInt64", "  | 0, s => s", "  | n + 1, s => f n s + 1"]),
  ("loop-nontail-if", prog ["def f : Nat → UInt64 → UInt64", "  | 0, s => s", "  | n + 1, s => (if s == s then f n s else s) + 1"]),
  ("loop-wrong-fuel", prog ["def f : Nat → UInt64 → UInt64", "  | 0, s => s", "  | n + 1, s => f s s"])]
def run (t : String) : List UInt64 := C.y13 (C.s10 t.toUTF8.toList)
def main : IO Unit := do
  let okV := valid.filter fun (_, t) => !(run t).isEmpty
  let okN := negative.filter fun (_, t) => (run t).isEmpty
  IO.println s!"VALID accepted {okV.length} / {valid.length} (must be 100%); NEGATIVE rejected {okN.length} / {negative.length}"
  for (n, t) in valid do if (run t).isEmpty then IO.println s!"  VALID REJECTED: {n}"
  for (n, t) in negative do if !(run t).isEmpty then IO.println s!"  NEGATIVE ACCEPTED: {n} {run t}"
  for (n, t) in valid do IO.println s!"{n}: {run t}"
