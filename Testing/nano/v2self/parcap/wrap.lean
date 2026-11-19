/- Regression for the parser width cap: `src k` doubles a pair width k times (`let a(i+1) := (a i, a i);`), so main's
nslots = 2^(k+1) − 1 without a cap (k = 3 → 15, 12 → 8191, 16 → 131071; k = 63 wraps `serialize`).  With the cap,
refParse must reject `src k` once nslots reaches 2^20 (k ≥ 19).  Run: `lake env lean Testing/nano/v2self/parcap/wrap.lean`
(`Sh.width` is exponential to evaluate: keep k small). -/
import Nano.V2Self.Proof.Main
open ParSpec
def src (k : Nat) : String :=
  "def m (x : List UInt8) : List UInt8 := let a0 := 1; " ++
  String.join ((List.range k).map fun i => s!"let a{i+1} := (a{i}, a{i}); ") ++ "put [] 0"
def nsl (k : Nat) : Option (List Nat) :=
  (lexAll ((src k).length + 1) (src k).toUTF8.toList).bind fun ts => (refParse ts).map (·.map (·.nslots))
#eval nsl 3
#eval nsl 12
#eval nsl 16
