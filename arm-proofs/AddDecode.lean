import Armv9.DecodeEnd
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
theorem decode_add_word (s : SequentialState RegisterType trivialChoiceSource) (pc : Int) (see : Int) (hs : see < 1)
    (h : s.regs.get? Register.SEE = some see) :
    __DecodeA64 pc 0x8b0a0129#32 s =
    decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 9#5 9#5 0#6 10#5 0#2 0#1 0#1 1#1
      { s with regs := s.regs.insert Register.SEE (14 : Int) } := by
  have h14 : see < 14 := by omega
  simp (config := {decide := true}) [__DecodeA64, __DecodeA64_DataProcReg, andM, ToBool.toBool, EStateM.pure, BitVec.slice, PreSail.readReg, PreSail.writeReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, h, hs, h14, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
#print axioms decode_add_word
