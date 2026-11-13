/- General-purpose registers of the ARM model as `Nat`-indexed functions, and the read/write lemmas. -/
import Armv9.DecodeEnd
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace ArmProof

abbrev St := SequentialState RegisterType trivialChoiceSource
abbrev Regs := Std.ExtDHashMap Register RegisterType

/-- the model's register for `X[i]`, `i < 31` -/
def xreg : Nat → Register
  | 0 => .R0
  | 1 => .R1
  | 2 => .R2
  | 3 => .R3
  | 4 => .R4
  | 5 => .R5
  | 6 => .R6
  | 7 => .R7
  | 8 => .R8
  | 9 => .R9
  | 10 => .R10
  | 11 => .R11
  | 12 => .R12
  | 13 => .R13
  | 14 => .R14
  | 15 => .R15
  | 16 => .R16
  | 17 => .R17
  | 18 => .R18
  | 19 => .R19
  | 20 => .R20
  | 21 => .R21
  | 22 => .R22
  | 23 => .R23
  | 24 => .R24
  | 25 => .R25
  | 26 => .R26
  | 27 => .R27
  | 28 => .R28
  | 29 => .R29
  | _ => .R30

theorem xreg_ty (i : Nat) : RegisterType (xreg i) = BitVec 64 := by
  unfold xreg; split <;> rfl

theorem xreg_idx (i : Nat) (hi : i < 31) : (xreg i).ctorIdx = 1089 - i := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | _ + 31, h => omega

theorem xreg_inj {i j : Nat} (hi : i < 31) (hj : j < 31) (h : xreg i = xreg j) : i = j := by
  have := congrArg Register.ctorIdx h; rw [xreg_idx i hi, xreg_idx j hj] at this; omega

/-- `X[i]` of a register map, for `i < 31` (`none` if missing or `i ≥ 31`) -/
def xget (m : Regs) (i : Nat) : Option (BitVec 64) :=
  if i < 31 then (m.get? (xreg i)).map (cast (xreg_ty i)) else none

/-- write `X[i]` (`i ≥ 31` writes nothing, like `X_set 31`) -/
def xset (m : Regs) (i : Nat) (v : BitVec 64) : Regs :=
  if i < 31 then m.insert (xreg i) (cast (xreg_ty i).symm v) else m

theorem read_gpr_ok {s : St} {n : Nat} {v : BitVec 64} (h : xget s.regs n = some v) :
    read_gpr n s = .ok v s := by
  unfold xget at h
  split at h
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    match n, ‹n < 31› with
    | 0, _ => have hx' : s.regs.get? Register.R0 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 1, _ => have hx' : s.regs.get? Register.R1 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 2, _ => have hx' : s.regs.get? Register.R2 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 3, _ => have hx' : s.regs.get? Register.R3 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 4, _ => have hx' : s.regs.get? Register.R4 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 5, _ => have hx' : s.regs.get? Register.R5 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 6, _ => have hx' : s.regs.get? Register.R6 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 7, _ => have hx' : s.regs.get? Register.R7 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 8, _ => have hx' : s.regs.get? Register.R8 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 9, _ => have hx' : s.regs.get? Register.R9 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 10, _ => have hx' : s.regs.get? Register.R10 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 11, _ => have hx' : s.regs.get? Register.R11 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 12, _ => have hx' : s.regs.get? Register.R12 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 13, _ => have hx' : s.regs.get? Register.R13 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 14, _ => have hx' : s.regs.get? Register.R14 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 15, _ => have hx' : s.regs.get? Register.R15 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 16, _ => have hx' : s.regs.get? Register.R16 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 17, _ => have hx' : s.regs.get? Register.R17 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 18, _ => have hx' : s.regs.get? Register.R18 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 19, _ => have hx' : s.regs.get? Register.R19 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 20, _ => have hx' : s.regs.get? Register.R20 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 21, _ => have hx' : s.regs.get? Register.R21 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 22, _ => have hx' : s.regs.get? Register.R22 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 23, _ => have hx' : s.regs.get? Register.R23 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 24, _ => have hx' : s.regs.get? Register.R24 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 25, _ => have hx' : s.regs.get? Register.R25 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 26, _ => have hx' : s.regs.get? Register.R26 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 27, _ => have hx' : s.regs.get? Register.R27 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 28, _ => have hx' : s.regs.get? Register.R28 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 29, _ => have hx' : s.regs.get? Register.R29 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | 30, _ => have hx' : s.regs.get? Register.R30 = some x := hx; simp [read_gpr, PreSail.readReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hx']; rfl
    | _ + 31, h => omega
  · cases h

theorem write_gpr_ok {s : St} {d : Nat} (hd : d < 31) (v : BitVec 64) :
    write_gpr d v s = .ok () { s with regs := xset s.regs d v } := by
  match d, hd with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | _ + 31, h => omega

theorem xget_xset (m : Regs) {d : Nat} (hd : d < 31) (v : BitVec 64) (i : Nat) :
    xget (xset m d v) i = if i = d then some v else xget m i := by
  unfold xget xset
  simp only [hd, ite_true]
  by_cases hi : i < 31
  · simp only [hi, ite_true, Std.ExtDHashMap.get?_insert]
    split
    · rename_i h; have := xreg_inj hd hi (eq_of_beq h); subst this; simp
    · rename_i h; have : i ≠ d := fun e => by subst e; simp at h
      simp [this]
  · have : i ≠ d := by omega
    simp [hi, this]

theorem xget_insert (m : Regs) (r : Register) (v : RegisterType r) (hr : ∀ i < 31, xreg i ≠ r) (i : Nat) :
    xget (m.insert r v) i = xget m i := by
  unfold xget; split
  · rename_i hi; simp [Std.ExtDHashMap.get?_insert, Ne.symm (hr i hi)]
  · rfl

theorem read_gpr_get {s : St} {n : Nat} (h : (xget s.regs n).isSome) :
    read_gpr n s = .ok ((xget s.regs n).getD 0) s := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  rw [hv]; exact read_gpr_ok hv

/-! The choice source is `Unit`-valued: these normalize the state record after `undefined_*` calls. -/
@[simp] theorem choice_unit (s : St) : s.choiceState = () := rfl
@[simp] theorem st_eta (s : St) : ({ regs := s.regs, choiceState := (), mem := s.mem, tags := s.tags, cycleCount := s.cycleCount, sailOutput := s.sailOutput } : St) = s := rfl
@[simp] theorem choose_ok (p : Primitive) (s : St) :
    (PreSail.choose p : PreSailM RegisterType trivialChoiceSource exception _) s = .ok (trivialChoiceSource.choose p ()) s := rfl
@[simp] theorem tcs_next (p x) : trivialChoiceSource.nextState p x = () := rfl
@[simp] theorem tcs_bool (x) : trivialChoiceSource.choose .bool x = false := rfl
@[simp] theorem tcs_bv (n x) : trivialChoiceSource.choose (.bitvector n) x = 0 := rfl
@[simp] theorem tcs_fin (n x) : trivialChoiceSource.choose (.fin n) x = 0 := rfl

theorem insert_insert (m : Regs) (r : Register) (v w : RegisterType r) : (m.insert r v).insert r w = m.insert r w :=
  Std.ExtDHashMap.ext_get? fun k => by
    simp only [Std.ExtDHashMap.get?_insert]; split <;> rfl

theorem AddWithCarry_result {k_N : Nat} (x y : BitVec k_N) (c : BitVec 1) (h : 0 < k_N) :
    (AddWithCarry x y c).1 = x + y + c.zeroExtend k_N := by
  unfold AddWithCarry
  apply BitVec.eq_of_toNat_eq
  have h1 : (((x.toNat + y.toNat + c.toNat : Nat) : Int) % 2^(k_N+1)).toNat = (x.toNat+y.toNat+c.toNat) % 2^(k_N+1) := by norm_cast
  have e2 : k_N - 1 + 1 = k_N := by omega
  simp [integer_subrange, Sail.BitVec.length, get_slice_int]
  rw [e2]; push_cast at h1; rw [h1]
  simp [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ k_N))]

theorem AddWithCarry_64_0 (x y : BitVec 64) : (AddWithCarry x y 0#1).1 = x + y := by
  rw [AddWithCarry_result _ _ _ (by decide)]; simp

theorem AddWithCarry_64_sub (x y : BitVec 64) : (AddWithCarry x (~~~y) 1#1).1 = x - y := by
  rw [AddWithCarry_result _ _ _ (by decide), BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add]
  simp [BitVec.add_assoc]

theorem shl_int_zero {w : Nat} (b : BitVec w) : b <<< (0 : Int) = b := by
  show BitVec.shiftLeft b 0 = b
  simp [BitVec.shiftLeft]

theorem shl_int_nat {w : Nat} (b : BitVec w) (k : Nat) : b <<< (k : Int) = b <<< k := rfl

theorem shr_int_nat {w : Nat} (b : BitVec w) (k : Nat) : b >>> (k : Int) = b >>> k := by
  cases k with
  | zero => show BitVec.shiftLeft b 0 = b >>> 0; simp [BitVec.shiftLeft]
  | succ k => rfl

theorem int_mod_cast (x : Nat) : ((x : Int) % 64) = ((x % 64 : Nat) : Int) := by omega
theorem shl_int_mod {w : Nat} (b : BitVec w) (x : Nat) : b <<< ((x : Int) % 64) = b <<< (x % 64) := by
  rw [int_mod_cast]; rfl
theorem shr_int_mod {w : Nat} (b : BitVec w) (x : Nat) : b >>> ((x : Int) % 64) = b >>> (x % 64) := by
  rw [int_mod_cast, shr_int_nat]
theorem toNat_int_mod (x : Nat) : ((x : Int) % 64).toNat = x % 64 := by omega

theorem nat_mod_eq (a b : Nat) : a.mod b = a % b := rfl

theorem xset_get_ne (m : Regs) (d : Nat) (v : BitVec 64) (r : Register) (hr : ∀ i < 31, xreg i ≠ r) :
    (xset m d v).get? r = m.get? r := by
  unfold xset; split
  · rename_i hd; simp [Std.ExtDHashMap.get?_insert, hr d hd]
  · rfl

/-- PSTATE after a flag-setting add/sub whose `AddWithCarry` flags are `f` (as the model writes them) -/
def setFlags (p : ProcState) (f : BitVec 4) : ProcState :=
  { p with N := Sail.BitVec.extractLsb f 3 3, Z := Sail.BitVec.extractLsb f 2 2, C := Sail.BitVec.extractLsb f 1 1, V := Sail.BitVec.extractLsb f 0 0 }

end ArmProof
