/- Decoding facts for the wide operations with ARBITRARY abstract registers (`Apc/Wide.lean`), checked by
enumeration (`decide +kernel`): every register triple / pair, every supported branch distance. -/
import Apc.Mach
import Compiler.Wide
namespace Proven.Apc
open Proven Proven.Mach

def ccN : Cond → Nat
  | .eq => 0 | .ne => 1 | .ltu => 3 | .geu => 2 | .lt => 11 | .ge => 10
def ccC : Cond → Arm64.CondCode
  | .eq => .EQ | .ne => .NE | .ltu => .CC | .geu => .CS | .lt => .LT | .ge => .GE
/-- `b.cond` with a 19-bit word offset `imm` (two's complement) -/
def wBc (c : Cond) (imm : Nat) : BitVec 32 := BitVec.ofNat 32 (0x54000000 ||| (imm % 2 ^ 19) <<< 5 ||| ccN c)
/-- `b +4n` -/
def wBf (n : Nat) : BitVec 32 := 0x05#6 ++ BitVec.ofNat 26 n
/-- `cmp xa, xb` / `cmp xa, xzr` -/
def wCmpO (a : Mach.Reg) : Option Mach.Reg → BitVec 32
  | some b => rrr 0xEB000000 31 (xn a) (xn b)
  | none => rrr 0xEB000000 31 (xn a) 31
def wLdrb (d a : Mach.Reg) : BitVec 32 := BitVec.ofNat 32 (0x39400000 ||| xn a <<< 5 ||| xn d)
def wStrb (v a : Mach.Reg) : BitVec 32 := BitVec.ofNat 32 (0x39000000 ||| xn a <<< 5 ||| xn v)

set_option maxRecDepth 100000 in
theorem decAdd3 : ∀ d a b : Mach.Reg, Arm64.decode (rrr 0x8B000000 (xn d) (xn a) (xn b)) =
    some (.addSubShift .W64 .ADD (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decSub3 : ∀ d a b : Mach.Reg, Arm64.decode (rrr 0xCB000000 (xn d) (xn a) (xn b)) =
    some (.addSubShift .W64 .SUB (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decAnd3 : ∀ d a b : Mach.Reg, Arm64.decode (rrr 0x8A000000 (xn d) (xn a) (xn b)) =
    some (.logicalShift .W64 .AND (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decOr3 : ∀ d a b : Mach.Reg, Arm64.decode (rrr 0xAA000000 (xn d) (xn a) (xn b)) =
    some (.logicalShift .W64 .ORR (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decXor3 : ∀ d a b : Mach.Reg, Arm64.decode (rrr 0xCA000000 (xn d) (xn a) (xn b)) =
    some (.logicalShift .W64 .EOR (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decShl3 : ∀ d a b : Mach.Reg, Arm64.decode (rrr 0x9AC02000 (xn d) (xn a) (xn b)) =
    some (.dataProc2 .W64 .LSLV (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b))) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decLshr3 : ∀ d a b : Mach.Reg, Arm64.decode (rrr 0x9AC02400 (xn d) (xn a) (xn b)) =
    some (.dataProc2 .W64 .LSRV (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b))) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decAshr3 : ∀ d a b : Mach.Reg, Arm64.decode (rrr 0x9AC02800 (xn d) (xn a) (xn b)) =
    some (.dataProc2 .W64 .ASRV (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b))) := by decide +kernel

theorem decCmp2 : ∀ a b : Mach.Reg, Arm64.decode (wCmpO a (some b)) =
    some (.addSubShift .W64 .SUBS .xzr (.gpr (xr a)) (.gpr (xr b)) .LSL 0) := by decide +kernel
theorem decCmpZ : ∀ a : Mach.Reg, Arm64.decode (wCmpO a none) =
    some (.addSubShift .W64 .SUBS .xzr (.gpr (xr a)) .xzr .LSL 0) := by decide +kernel
theorem decCset2 : ∀ d : Mach.Reg, Arm64.decode (wCset 2 d) = some (.condSelect .W64 .CSINC (.gpr (xr d)) .xzr .xzr .CS) := by
  decide +kernel
theorem decCset10 : ∀ d : Mach.Reg, Arm64.decode (wCset 10 d) = some (.condSelect .W64 .CSINC (.gpr (xr d)) .xzr .xzr .GE) := by
  decide +kernel
theorem decCset1 : ∀ d : Mach.Reg, Arm64.decode (wCset 1 d) = some (.condSelect .W64 .CSINC (.gpr (xr d)) .xzr .xzr .NE) := by
  decide +kernel
theorem decLdrbW : ∀ d a : Mach.Reg, Arm64.decode (wLdrb d a) =
    some (.ldr .W32 .B8 false (.gpr (xr d)) (.Offset (.gpr (xr a)) 0#64)) := by decide +kernel
theorem decStrbW : ∀ v a : Mach.Reg, Arm64.decode (wStrb v a) =
    some (.str .B8 (.gpr (xr v)) (.Offset (.gpr (xr a)) 0#64)) := by decide +kernel
theorem decZeroW : ∀ d : Mach.Reg, Arm64.decode (iZero d) = some (.moveWide .W64 .MOVZ (.gpr (xr d)) 0#16 0) := by
  decide +kernel
theorem decDblW : ∀ d : Mach.Reg, Arm64.decode (iShl d) =
    some (.addSubShift .W64 .ADD (.gpr (xr d)) (.gpr (xr d)) (.gpr (xr d)) .LSL 0) := by decide +kernel
theorem decIncW : ∀ d : Mach.Reg, Arm64.decode (iInc d) =
    some (.addSubImm .W64 .ADD (.gpr (xr d)) (.gpr (xr d)) 1#12 false) := by decide +kernel
set_option maxRecDepth 100000 in
theorem decBf : ∀ n : Fin 1024, Arm64.decode (wBf n.val) = some (.b (BitVec.ofNat 64 (4 * n.val))) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decBcF_eq : ∀ n : Fin 512, Arm64.decode (wBc .eq n.val) = some (.bCond (ccC .eq) (BitVec.ofNat 64 (4 * n.val))) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem decBcB_eq : ∀ n : Fin 512, Arm64.decode (wBc .eq (2 ^ 19 - (n.val + 1))) =
    some (.bCond (ccC .eq) (BitVec.ofNat 64 (2 ^ 64 - 4 * (n.val + 1)))) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decBcF_ne : ∀ n : Fin 512, Arm64.decode (wBc .ne n.val) = some (.bCond (ccC .ne) (BitVec.ofNat 64 (4 * n.val))) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem decBcB_ne : ∀ n : Fin 512, Arm64.decode (wBc .ne (2 ^ 19 - (n.val + 1))) =
    some (.bCond (ccC .ne) (BitVec.ofNat 64 (2 ^ 64 - 4 * (n.val + 1)))) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decBcF_ltu : ∀ n : Fin 512, Arm64.decode (wBc .ltu n.val) = some (.bCond (ccC .ltu) (BitVec.ofNat 64 (4 * n.val))) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem decBcB_ltu : ∀ n : Fin 512, Arm64.decode (wBc .ltu (2 ^ 19 - (n.val + 1))) =
    some (.bCond (ccC .ltu) (BitVec.ofNat 64 (2 ^ 64 - 4 * (n.val + 1)))) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decBcF_geu : ∀ n : Fin 512, Arm64.decode (wBc .geu n.val) = some (.bCond (ccC .geu) (BitVec.ofNat 64 (4 * n.val))) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem decBcB_geu : ∀ n : Fin 512, Arm64.decode (wBc .geu (2 ^ 19 - (n.val + 1))) =
    some (.bCond (ccC .geu) (BitVec.ofNat 64 (2 ^ 64 - 4 * (n.val + 1)))) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decBcF_lt : ∀ n : Fin 512, Arm64.decode (wBc .lt n.val) = some (.bCond (ccC .lt) (BitVec.ofNat 64 (4 * n.val))) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem decBcB_lt : ∀ n : Fin 512, Arm64.decode (wBc .lt (2 ^ 19 - (n.val + 1))) =
    some (.bCond (ccC .lt) (BitVec.ofNat 64 (2 ^ 64 - 4 * (n.val + 1)))) := by decide +kernel

set_option maxRecDepth 100000 in
theorem decBcF_ge : ∀ n : Fin 512, Arm64.decode (wBc .ge n.val) = some (.bCond (ccC .ge) (BitVec.ofNat 64 (4 * n.val))) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem decBcB_ge : ∀ n : Fin 512, Arm64.decode (wBc .ge (2 ^ 19 - (n.val + 1))) =
    some (.bCond (ccC .ge) (BitVec.ofNat 64 (2 ^ 64 - 4 * (n.val + 1)))) := by decide +kernel


theorem decBcF (c : Cond) (n : Fin 512) : Arm64.decode (wBc c n.val) = some (.bCond (ccC c) (BitVec.ofNat 64 (4 * n.val))) := by
  cases c
  · exact decBcF_eq n
  · exact decBcF_ne n
  · exact decBcF_ltu n
  · exact decBcF_geu n
  · exact decBcF_lt n
  · exact decBcF_ge n
theorem decBcB (c : Cond) (n : Fin 512) : Arm64.decode (wBc c (2 ^ 19 - (n.val + 1))) =
    some (.bCond (ccC c) (BitVec.ofNat 64 (2 ^ 64 - 4 * (n.val + 1)))) := by
  cases c
  · exact decBcB_eq n
  · exact decBcB_ne n
  · exact decBcB_ltu n
  · exact decBcB_geu n
  · exact decBcB_lt n
  · exact decBcB_ge n

end Proven.Apc
