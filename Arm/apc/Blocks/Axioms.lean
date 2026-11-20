import Blocks.Imm
import Blocks.Reg
import Blocks.Branch
import Blocks.Mem
import Blocks.KAddi
import Blocks.KAlu
import Blocks.KShift
import Blocks.KBr
import Blocks.KMem
import Blocks.BlockOK
import Blocks.A64Inst
import Blocks.ArmDMTop
open Proven.Apc.Blocks
#print axioms dm_movz
#print axioms dm_movk
#print axioms dm_addi
#print axioms dm_subi
#print axioms dm_addR
#print axioms dm_subR
#print axioms dm_subsR
#print axioms dm_andR
#print axioms dm_orrR
#print axioms dm_eorR
#print axioms dm_lslv
#print axioms dm_lsrv
#print axioms dm_madd
#print axioms dm_b
#print axioms dm_bl
#print axioms dm_bc
#print axioms dm_cbz
#print axioms dm_br
#print axioms dm_ldr
#print axioms dm_str
#print axioms dm_ldrb
#print axioms dm_strb
#print axioms blk_addi
#print axioms blk_alu
#print axioms blk_slli
#print axioms blk_srli
#print axioms blk_beq
#print axioms blk_bne
#print axioms blk_bltu
#print axioms blk_bgeu
#print axioms blk_jal
#print axioms blk_jalr
#print axioms blk_ld
#print axioms blk_sd
#print axioms blk_lbu
#print axioms blk_sb
#print axioms blockOKD
#print axioms F_movz
#print axioms F_movk
#print axioms F_addi
#print axioms F_subi
#print axioms F_alu
#print axioms F_cmpbr
#print axioms F_cbz
#print axioms F_b
#print axioms F_bl
#print axioms F_br
#print axioms F_ldr
#print axioms F_str
#print axioms F_ldrb
#print axioms F_strb
#print axioms a64DM
#print axioms C_correct_armDM
#print axioms C_runs_armDM
