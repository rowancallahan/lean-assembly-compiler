import Legacy.Riscv.Frontx.WpCmd
namespace NanoCB
open Proven.WA

def fl (b src : ByteArray) (i : Nat) : ByteArray :=
  if i < 64 then fl (b.push 0) src (i + 1) else b
termination_by 64 - i

/-- write src bytes at w, final result sets cell 0 to w -/
def mn (ob src : ByteArray) (i w : Nat) : ByteArray :=
  if i < src.size then
    mn (ob.set! w (if src.get! i == 7 then ob.get! w else src.get! i)) src (i + 1 + 0 * w)
      (if src.get! i == 7 then w else if w < 63 then w + 1 else w)
  else ob.set! 0 (UInt8.ofNat w)
termination_by src.size - i

def pE (xs : ByteArray) : ByteArray := mn (fl (xs.extract 0 0) xs 0) xs 0 1
wp_compile pE max 65536
  invariant fun (b src : ByteArray) (i : Nat) => i ≤ 64 ∧ b.size = i ∧ src.size < 2 ^ 32
  measure fun (_b _src : ByteArray) (i : Nat) => 64 - i
  invariant fun (ob src : ByteArray) (i w : Nat) => ob.size = 64 ∧ w < 64 ∧ i ≤ src.size ∧ src.size < 2 ^ 32
  measure fun (_ob src : ByteArray) (i _w : Nat) => src.size - i

#check @pE.compiles
#print axioms pE.compiles
end NanoCB
