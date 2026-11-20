/- PROBE 2 (nano-int, 2026-11-17): steps that do NOT consume input in the paged front end (`wp_compile`): a copy mode
   with a counter and a lexicographic measure.  PASSES (3 min, Sail axioms only).  Run: `lake env lean Testing/nano/wp_copy_probe.lean`. -/
import Legacy.Riscv.Frontx.WpCmd
namespace NanoW
open Proven.WA

/-- steps that do not consume input: after each input byte `c`, `c % 4` bytes are copied from the start of the
buffer (copy mode `0 < rem`); every step pushes exactly one byte. -/
def cm (buf src : ByteArray) (i rem cp : Nat) : ByteArray :=
  if i < src.size then
    cm (buf.push (if 0 < rem then buf.get! cp else src.get! i)) src
      (if 0 < rem then i else i + 1 + 0 * cp)
      (if 0 < rem then rem - 1 else (src.get! i).toNat % 4)
      (if 0 < rem then cp + 1 else 0)
  else buf
termination_by (src.size - i) * 4 + rem
decreasing_by all_goals (split <;> omega)

def cmE (xs : ByteArray) : ByteArray := cm xs xs 0 0 0
wp_compile cmE max 65536
  invariant fun (buf src : ByteArray) (i rem cp : Nat) =>
    rem < 4 ∧ cp + rem ≤ 3 ∧ i ≤ src.size ∧ buf.size + 4 * (src.size - i) + rem ≤ 524288 ∧ src.size < 2 ^ 32
  measure fun (_buf src : ByteArray) (i rem _cp : Nat) => (src.size - i) * 4 + rem

#check @cmE.compiles
#print axioms cmE.compiles
end NanoW
