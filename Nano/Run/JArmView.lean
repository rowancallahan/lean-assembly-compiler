/- E4, the program proof of the nano J → AArch64 translator (Nano/Codegen/JArm.lean, `C.e64` / `C.e45`) against the
specification `natEncJ` (Nano/Run/NatEnc.lean): THE SHARED STATEMENTS.
* The J VIEW the translator's accessor layer computes is in NatEnc.lean (`jk`, `jA` / `jB` / `jC`, `jop`); here `acode`
  (the atom code of `e35` / `candC`).
* `JArmBits`: the bit-level facts (NATIVE-ARM-PROOF proves the instance `jArmBits` in Nano/Run/JArmBits.lean):
  (L1 bytes → words `e68` / L6 words → bytes `e49` are `NanoMain.e68_g40` / `NanoMain.e49_wordBytes` of JArmBits.lean;)
  L2 the accessor layer on `encG j` for `JOK j`, L4 the A64 word
  encoders `e50` … `e63`, `e42`, `e56` (li), `e57` (memW), `e58` (aluC) against `ArmEnc`'s `Nat` encoders.
  Every field is a small lemma with explicit ranges; if one is false as stated, change the statement and tell FABLE-M4.
The structural layers (L3 `e35`/`e36`/`e37` = `cand` / length / `ok`; L5 the two passes; L7 the glue to the top
theorem) are proved from `JArmBits` in JArmCand.lean / JArmPass.lean (FABLE-M4). -/
import Nano.Codegen.JArm
import Nano.Run.NatEnc
import Nano.Run.ArmEncOK
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

/-- the atom code of `e35` -/
def acode : NTm → UInt64
  | .li _ _ => 1
  | .addi _ _ _ => 2
  | .alu _ _ _ _ => 3
  | .ld _ _ _ => 4
  | .sd _ _ _ => 5
  | .ldp _ _ _ sw => if sw then 7 else 6
  | .cj .geu _ _ _ => 8
  | .cj .ltu _ _ _ => 9
  | .cj .eq _ _ _ => 10
  | .lpz _ _ => 11
  | .bgeu _ _ _ => 12
  | .beqz _ _ => 13
  | .bnez _ _ => 14
  | .ldrbx _ _ _ => 15
  | .slli _ _ _ => 16
  | .bgetI => 0
  | .bsetI => 0
  | .bpushI => 18
  | .align8 _ _ => 19
  | .jal _ _ => 20
  | .jalr _ => 21
  | .sb _ _ => 22

/-- **the bit-level facts about the translator** -/
structure JArmBits : Prop where
  -- L2: the accessor layer
  /-- a J word is below 2^32 -/
  l2_lt : ∀ j : J, JOK j → (encG j).toNat < 2 ^ 32
  /-- a word of 2^32 or more is no J instruction -/
  l2_big : ∀ v : UInt64, 4294967295 < v → e25 v = 0
  l2_kind : ∀ j : J, JOK j → e25 (encG j) = jk j
  l2_A : ∀ (c : Buf) (i : UInt64) (j : J), bget c i = encG j → JOK j → e21 c i = jA j
  /-- (needs `e22` to return 0 for `jal`, kind 13) -/
  l2_B : ∀ (c : Buf) (i : UInt64) (j : J), bget c i = encG j → JOK j → e22 c i = jB j
  l2_C : ∀ (c : Buf) (i : UInt64) (j : J), bget c i = encG j → JOK j → e23 c i = jC j
  /-- (needs `e24` to return 0 unless the kind is 8) -/
  l2_op : ∀ (c : Buf) (i : UInt64) (j : J), bget c i = encG j → JOK j → e24 c i = jop j
  /-- the accessors on the word 0 (past the end of the buffer) -/
  l2_zero : ∀ (c : Buf) (i : UInt64), bget c i = 0 →
    e21 c i = 0 ∧ e22 c i = 0 ∧ e23 c i = 0 ∧ e24 c i = 0
  -- L4: signs and registers
  /-- the sign test -/
  l4_neg : ∀ z : Int, -2 ^ 63 ≤ z → z < 2 ^ 63 → e14 (iu z) = if z < 0 then 1 else 0
  l4_reg : ∀ r : Nat, mapped r = true → e42 r.toUInt64 = (armReg r).toUInt64
  l4_mapped : ∀ r : Nat, r < 32 → e38 r.toUInt64 = if mapped r = true then 1 else 0
  /-- the alignment test of `ld` / `sd` -/
  l4_al : ∀ off : Int, -2048 ≤ off → off < 2048 → e41 (iu off) = if 0 ≤ off → off % 8 = 0 then 1 else 0
  -- L4: the word encoders (register fields < 32)
  /-- `c ||| v << 10 ||| n << 5 ||| d` as a sum (add / sub imm, ldr / str, strb, ldp, br) -/
  l4_e50 : ∀ cN d n v : Nat, cN < 2 ^ 32 → cN % 2 ^ 22 = 0 → d < 32 → n < 32 → v < 4096 →
    e50 cN.toUInt64 d.toUInt64 n.toUInt64 v.toUInt64 = (cN + v * 2 ^ 10 + n * 2 ^ 5 + d).toUInt64
  l4_br : ∀ n : Nat, n < 32 → e50 3592355840 0 n.toUInt64 0 = (ArmEnc.brR n).toUInt64
  l4_lsl : ∀ d n sh : Nat, d < 32 → n < 32 → 0 < sh → sh < 64 →
    e50 3544186880 d.toUInt64 n.toUInt64 (63 - sh.toUInt64) ||| (((64 - sh.toUInt64) &&& e_4) <<< 16)
      = (ArmEnc.lslI d n sh).toUInt64
  /-- three registers: `c ||| m << 16 ||| n << 5 ||| d` -/
  l4_e51 : ∀ cN d n m : Nat, cN < 2 ^ 32 → cN % 2 ^ 10 = 0 → cN / 2 ^ 16 % 32 = 0 → d < 32 → n < 32 → m < 32 →
    e51 cN.toUInt64 d.toUInt64 n.toUInt64 m.toUInt64 = (ArmEnc.rr cN d n m).toUInt64
  l4_alu : ∀ p : Nat, p < 2 ^ 64 → e58 p.toUInt64 = (aluC p).toUInt64
  /-- movz / movk / movn: `c ||| j << 21 ||| v << 5 ||| d` -/
  l4_e52 : ∀ cN d v j : Nat, cN < 2 ^ 32 → cN % 2 ^ 23 = 0 → d < 32 → v < 65536 → j < 4 →
    e52 cN.toUInt64 d.toUInt64 v.toUInt64 j.toUInt64 = (cN + j * 2 ^ 21 + v * 2 ^ 5 + d).toUInt64
  /-- b.cond / cbz / cbnz: the 19-bit word offset `δ` -/
  l4_e53 : ∀ (cN : Nat) (δ : Int), cN < 2 ^ 32 → cN / 32 % 2 ^ 19 = 0 →
    e53 cN.toUInt64 (iu δ) = (cN + mo δ 19 * 2 ^ 5).toUInt64
  l4_cb : ∀ (cN r : Nat) (δ : Int), cN < 2 ^ 32 → cN % 2 ^ 24 = 0 → r < 32 →
    e53 cN.toUInt64 (iu δ) ||| r.toUInt64 = (cN + mo δ 19 * 2 ^ 5 + r).toUInt64
  /-- b / bl: the 26-bit word offset -/
  l4_e63 : ∀ (cN : Nat) (δ : Int), cN < 2 ^ 32 → cN % 2 ^ 26 = 0 → e63 cN.toUInt64 (iu δ) = (cN + mo δ 26).toUInt64
  /-- ldur / stur: the signed 9-bit byte offset -/
  l4_e62 : ∀ (cN t n : Nat) (f : Int), cN < 2 ^ 32 → cN % 2 ^ 21 = 0 → t < 32 → n < 32 →
    e62 cN.toUInt64 t.toUInt64 n.toUInt64 (iu f) = (cN + mo f 9 * 2 ^ 12 + n * 2 ^ 5 + t).toUInt64
  /-- `li` -/
  l4_li : ∀ (o : Buf) (d : Nat) (v : UInt64), d < 32 → e56 o d.toUInt64 v = o ++ (liL d v.toNat).map Nat.toUInt64
  /-- `memW` (the offsets `NTm.ok` allows) -/
  l4_mem : ∀ (o : Buf) (st : Bool) (t n : Nat) (off : Int), t < 32 → n < 32 → -4096 < off → off < 32768 →
    (0 ≤ off → off % 8 = 0) →
    e57 o (if st then 1 else 0) t.toUInt64 n.toUInt64 (iu off) = o ++ (NTm.memW st t n off).map Nat.toUInt64

end JT
