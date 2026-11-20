import LeanRV64D.AddrChecks
import LeanRV64D.AextTypes
import LeanRV64D.Arith
import LeanRV64D.Arithmetic
import LeanRV64D.BaseInsts
import LeanRV64D.Callbacks
import LeanRV64D.Callbacks0
import LeanRV64D.CfiTypes
import LeanRV64D.Classify
import LeanRV64D.Common
import LeanRV64D.Common0
import LeanRV64D.DecBits
import LeanRV64D.DecodeExt
import LeanRV64D.Defs
import LeanRV64D.DextInsts
import LeanRV64D.Errors
import LeanRV64D.ExtRegs
import LeanRV64D.FakeReal
import LeanRV64D.FdextRegs
import LeanRV64D.Fetch
import LeanRV64D.FetchRvfi
import LeanRV64D.FextInsts
import LeanRV64D.Flen
import LeanRV64D.FloatClassify
import LeanRV64D.Flow
import LeanRV64D.FregType
import LeanRV64D.HexBits
import LeanRV64D.HexBitsSigned
import LeanRV64D.Inf
import LeanRV64D.InstsBegin
import LeanRV64D.InstsEnd
import LeanRV64D.InterruptRegs
import LeanRV64D.IsaVersion
import LeanRV64D.LeanRV64D
import LeanRV64D.Main
import LeanRV64D.Mapping
import LeanRV64D.Mem
import LeanRV64D.MemAddrtype
import LeanRV64D.MemMetadata
import LeanRV64D.MemTypeUtils
import LeanRV64D.MemUtils
import LeanRV64D.MextInsts
import LeanRV64D.Model
import LeanRV64D.Nan
import LeanRV64D.Normal
import LeanRV64D.PcAccess
import LeanRV64D.PhysMemInterface
import LeanRV64D.Platform
import LeanRV64D.PlatformConfig
import LeanRV64D.PmTypes
import LeanRV64D.PmUtils
import LeanRV64D.Pma
import LeanRV64D.PmpControl
import LeanRV64D.PmpRegs
import LeanRV64D.Prelude
import LeanRV64D.RangeUtil
import LeanRV64D.ReadWriteV1
import LeanRV64D.RegType
import LeanRV64D.Regs
import LeanRV64D.RiscvExtras
import LeanRV64D.RvfiDii
import LeanRV64D.Sign
import LeanRV64D.SimpleInterruptGenerator
import LeanRV64D.Smcntrpmf
import LeanRV64D.SpecializationV1
import LeanRV64D.SplitAccessUtils
import LeanRV64D.Ssqosid
import LeanRV64D.StateenAccessChecks
import LeanRV64D.StateenRegs
import LeanRV64D.Step
import LeanRV64D.StepCommon
import LeanRV64D.StepExt
import LeanRV64D.SysControl
import LeanRV64D.SysExceptions
import LeanRV64D.SysRegs
import LeanRV64D.Types
import LeanRV64D.TypesExt
import LeanRV64D.TypesKext
import LeanRV64D.ValidateConfig
import LeanRV64D.Vector
import LeanRV64D.VextArithInsts
import LeanRV64D.VextControl
import LeanRV64D.VextFpInsts
import LeanRV64D.VextFpRedInsts
import LeanRV64D.VextFpUtilsInsts
import LeanRV64D.VextFpVmInsts
import LeanRV64D.VextMaskInsts
import LeanRV64D.VextMemInsts
import LeanRV64D.VextRedInsts
import LeanRV64D.VextRegs
import LeanRV64D.VextTypes
import LeanRV64D.VextUtilsInsts
import LeanRV64D.VextVmInsts
import LeanRV64D.VextVsetInsts
import LeanRV64D.Vlen
import LeanRV64D.Vmem
import LeanRV64D.VmemPte
import LeanRV64D.VmemPtw
import LeanRV64D.VmemTlb
import LeanRV64D.VmemTypes
import LeanRV64D.VmemUtils
import LeanRV64D.Xlen
import LeanRV64D.ZaamoInsts
import LeanRV64D.ZawrsInsts
import LeanRV64D.Zero
import LeanRV64D.ZfaInsts
import LeanRV64D.ZfbfminUtils
import LeanRV64D.ZfhInsts
import LeanRV64D.ZibiInsts
import LeanRV64D.ZicbomInsts
import LeanRV64D.ZicbopInsts
import LeanRV64D.ZicfilpInsts
import LeanRV64D.ZicfilpRegs
import LeanRV64D.ZicfissInsts
import LeanRV64D.ZicondInsts
import LeanRV64D.ZicsrInsts
import LeanRV64D.ZihintntlTypes
import LeanRV64D.Zihpm
import LeanRV64D.ZkrControl
import LeanRV64D.ZvabdInsts
import LeanRV64D.ZvkUtils
import LeanRV64D.ZvknedInsts
import LeanRV64D.ZvknhabInsts
import LeanRV64D
open Lean

def ctorKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def valHash : ConstantInfo → UInt64
  | .defnInfo d => d.value.hash | .thmInfo d => d.value.hash | .opaqueInfo d => d.value.hash
  | .inductInfo i => hash (i.ctors.map (·.toString)) | .ctorInfo c => hash c.cidx
  | .recInfo r => hash (r.rules.map (·.rhs.hash))
  | _ => 0

def extra : ConstantInfo → String
  | .defnInfo d => s!"{repr d.safety}" | .inductInfo i => s!"nparams={i.numParams} rec={i.isRec}"
  | _ => ""

#eval show CoreM Unit from do
  -- hash sanity probe: must be equal across toolchains for the comparison to mean anything
  IO.println s!"#probe\t{(mkApp (mkConst ``Nat.succ) (mkNatLit 0)).hash}\t{(mkLambda `x .default (mkConst ``Nat) (.bvar 0)).hash}\t{(mkConst ``List [.succ .zero]).hash}"
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mn := env.header.moduleNames[idx.toNat]!
    unless (`LeanRV64D).isPrefixOf mn do continue
    rows := rows.push s!"{n}\t{mn}\t{ctorKind ci}\t{ci.levelParams}\t{ci.type.hash}\t{valHash ci}\t{extra ci}"
  for r in rows.qsort (· < ·) do IO.println r
