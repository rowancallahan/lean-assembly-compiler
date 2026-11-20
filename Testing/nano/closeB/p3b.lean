import Legacy.Riscv.Frontx.WpCmd
namespace NanoCB
open Proven.WA

def mn (ob : Array UInt8) (st : Array Nat) (src : ByteArray) (i w : Nat) : Array UInt8 :=
  if i < src.size then
    mn (ob.set! w (if src.get! i == 7 then ob[w]! else src.get! i)) (st.set! w (if src.get! i == 7 then st[w]! else w)) src (i + 1 + 0 * w)
      (if src.get! i == 7 then w else if w < 63 then w + 1 else w)
  else ob
termination_by src.size - i

def pE (xs : ByteArray) : Array UInt8 := mn (Array.replicate 4096 0) (Array.replicate 64 0) xs 0 1
wp_compile pE max 65536
  invariant fun (ob : Array UInt8) (st : Array Nat) (src : ByteArray) (i w : Nat) => ob.size = 4096 ∧ st.size = 64 ∧ w < 64 ∧ i ≤ src.size ∧ src.size < 2 ^ 32
  measure fun (_ob : Array UInt8) (_st : Array Nat) (src : ByteArray) (i _w : Nat) => src.size - i

#check @pE.compiles
end NanoCB
