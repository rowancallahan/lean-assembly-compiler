import Nano.V2.Lang
/- nano v2 small backend: typed AST (Nano/V2/Lang.lean) → structured stack code `SC` → RISC-V words.

Calling convention (`StartCorrect`/`Implements1With`): a0 = input address, a1 = input length, a2 = work base
(8-aligned), sp = work top, a3 = output address, ra = return.  Registers used: t0-t6, a0, a1, a4, a5 (all
caller-saved; sp, gp, ra, s-registers untouched).
  t3 (x28) = input base, t4 (x29) = input length, t5 (x30) = HEAP pointer (buffers, bump-allocated upward from a2),
  t6 (x31) = VALUE-STACK pointer (8-byte slots, downward from sp rounded down to 8).
Every push checks t6 ≥ t5 after the decrement; every `mk` checks the new heap top ≤ t6: else a0 := -1 (out of work
memory), return.  A `push` on a full buffer (len = cap) sets a0 := -2 (capacity), return.
Buffer layout: [len][cap][cap data words].  A buffer value is its address (one slot).
Result (status, out): status ≠ 0 ⇒ a0 := status, a1 := 0; else the low bytes of out's words at a3, a1 := len,
a0 := 0. -/
namespace Nano.V2

/-- R-type ops -/
inductive ROp where
  | add | sub | mul | and | or | xor | sll | srl | sltu
  deriving DecidableEq, Repr
/-- I-type ALU ops (`slli`/`srli`: imm = shift amount) -/
inductive IOp where
  | addi | ori | andi | xori | slli | srli
  deriving DecidableEq, Repr
inductive BOp where
  | beq | bne | bltu | bgeu
  deriving DecidableEq, Repr

/-- machine instructions (offsets in bytes) -/
inductive I where
  | r (f : ROp) (rd rs1 rs2 : Nat)
  | i (f : IOp) (rd rs1 : Nat) (imm : Int)
  | ld (rd rs1 : Nat) (off : Int)
  | lbu (rd rs1 : Nat) (off : Int)
  | sd (rs2 rs1 : Nat) (off : Int)
  | sb (rs2 rs1 : Nat) (off : Int)
  | br (c : BOp) (rs1 rs2 : Nat) (off : Int)
  | jal (off : Int)
  | ret
  deriving DecidableEq, Repr

/-- jump targets inside structured code -/
inductive Tg where
  | head | exit | oom | cap
  deriving DecidableEq, Repr

/-- structured stack code -/
inductive SC where
  | ins (l : List I)
  | seq (a b : SC)
  /-- if `c rs1 rs2` then `t` else `e` -/
  | ite (c : BOp) (rs1 rs2 : Nat) (t e : SC)
  /-- HEAD: `test` (sets t0); if t0 = 0 goto ZERO; `dec`; `body` (ends in jumps to head/exit);
      ZERO: `z`; EXIT: -/
  | loop (test dec : List I) (z body : SC)
  | jmp (t : Tg)
  deriving Repr

def SC.len : SC → Nat
  | .ins l => l.length
  | .seq a b => a.len + b.len
  | .ite _ _ _ t e => 2 + t.len + 1 + e.len
  | .loop test dec z body => test.length + 2 + dec.length + body.len + z.len
  | .jmp _ => 1

def toff (a b : Nat) : Int := 4 * ((b : Int) - a)

/-- flatten at instruction index `pos`; `hd`/`ex`: the innermost loop's head/exit, `om`/`cp`: the abort stubs -/
def SC.flat (om cp : Nat) : SC → Nat → Nat → Nat → List I
  | .ins l, _, _, _ => l
  | .seq a b, pos, hd, ex => a.flat om cp pos hd ex ++ b.flat om cp (pos + a.len) hd ex
  | .ite c r1 r2 t e, pos, hd, ex =>
    let pe := pos + 2 + t.len + 1
    let pend := pe + e.len
    [.br c r1 r2 8, .jal (toff (pos + 1) pe)] ++ t.flat om cp (pos + 2) hd ex ++
      [.jal (toff (pos + 2 + t.len) pend)] ++ e.flat om cp pe hd ex
  | .loop test dec z body, pos, _, _ =>
    let pb := pos + test.length + 2 + dec.length
    let pz := pb + body.len
    let pex := pz + z.len
    test ++ [.br .bne 5 0 8, .jal (toff (pos + test.length + 1) pz)] ++ dec ++
      body.flat om cp pb pos pex ++ z.flat om cp pz pos pex
  | .jmp t, pos, hd, ex =>
    [.jal (toff pos (match t with | .head => hd | .exit => ex | .oom => om | .cap => cp))]

/-! ## blocks -/
def T0 := 5
def T1 := 6
def T2 := 7
def A4 := 14
def A5 := 15
def SP := 31
def HP := 30
def IB := 28
def IL := 29

def mv (rd rs : Nat) : I := .i .addi rd rs 0
/-- t6 -= 8; if t6 < t5: out of memory; [t6] := t0 -/
def push : SC := .seq (.ite .bgeu SP HP (.ins []) (.jmp .oom)) (.ins [.sd T0 SP 0])
def pushC : SC := .seq (.ins [.i .addi SP SP (-8)]) push

/-- rd := n (small: one `addi`; else byte by byte, most significant first) -/
def li (rd : Nat) (n : UInt64) : List I :=
  if n.toNat < 2048 then [.i .addi rd 0 n.toNat] else
  .i .addi rd 0 0 :: (List.range 8).reverse.flatMap fun k =>
    [.i .slli rd rd 8, .i .ori rd rd ((n >>> (8 * k).toUInt64) &&& 255).toNat]

/-- the top `k` slots slide down over the `m` slots below them -/
def slide (k m : Nat) : List I :=
  if m = 0 then [] else
  ((List.range k).flatMap fun j => [.ld T0 SP (8 * (k - 1 - j)), .sd T0 SP (8 * (k - 1 - j + m))]) ++
    [.i .addi SP SP (8 * m)]

def ROp.ofOp : Op → ROp
  | .add => .add | .sub => .sub | .mul => .mul | .and => .and | .or => .or | .xor => .xor
  | .shl => .sll | .shr => .srl
def BOp.ofCmp : Cmp → BOp
  | .eq => .beq | .ne => .bne | .lt => .bltu | .ge => .bgeu

/-- pop the two top words: t1 := top, t0 := below -/
def pop2 : List I := [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 16]

/-- offsets must fit the 12-bit immediates: slots < 256 -/
def Lim := 255

/-! ## expressions: `env` = (type, absolute slot of its first word), `d` = slots in use -/
mutual
def cE (env : List (Ty × Nat)) (d : Nat) : Ex → Option (SC × Ty)
  | .lit n => some (.seq (.ins (.i .addi SP SP (-8) :: li T0 n)) push, .w)
  | .var i => match env[i]? with
    | some (τ, p) => if d < Lim + p + 1 ∧ p < d then
        some ((List.range τ.size).foldr (fun _ acc => .seq (.seq (.ins [.ld T0 SP (8 * (d - 1 - p))]) pushC) acc)
          (.ins []), τ)
      else none
    | none => none
  | .bin o a b => match cE env d a, cE env (d + 1) b with
    | some (ca, .w), some (cb, .w) =>
      some (.seq (.seq ca cb) (.ins [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .r (ROp.ofOp o) T0 T0 T1,
        .sd T0 SP 0]), .w)
    | _, _ => none
  | .ite c a b t e => match cE env d a, cE env (d + 1) b, cE env d t, cE env d e with
    | some (ca, .w), some (cb, .w), some (ct, τ), some (ce, τ') =>
      if τ = τ' then some (.seq (.seq (.seq ca cb) (.ins pop2)) (.ite (BOp.ofCmp c) T0 T1 ct ce), τ) else none
    | _, _, _, _ => none
  | .let_ v b => match cE env d v with
    | some (cv, τ) => match cE ((τ, d) :: env) (d + τ.size) b with
      | some (cb, ρ) => if τ.size ≤ Lim then some (.seq (.seq cv cb) (.ins (slide ρ.size τ.size)), ρ) else none
      | none => none
    | none => none
  | .pair a b => match cE env d a with
    | some (ca, τ) => match cE env (d + τ.size) b with
      | some (cb, σ) => some (.seq ca cb, .prod τ σ)
      | none => none
    | none => none
  | .fst e => match cE env d e with
    | some (ce, .prod τ σ) => if σ.size ≤ Lim then some (.seq ce (.ins [.i .addi SP SP (8 * σ.size)]), τ) else none
    | _ => none
  | .snd e => match cE env d e with
    | some (ce, .prod τ σ) => if τ.size ≤ Lim ∧ σ.size ≤ Lim then some (.seq ce (.ins (slide σ.size τ.size)), σ)
      else none
    | _ => none
  | .split e b => match cE env d e with
    | some (ce, .prod τ σ) =>
      match cE ((σ, d + τ.size) :: (τ, d) :: env) (d + τ.size + σ.size) b with
      | some (cb, ρ) => if τ.size + σ.size ≤ Lim then
          some (.seq (.seq ce cb) (.ins (slide ρ.size (τ.size + σ.size))), ρ) else none
      | none => none
    | _ => none
  | .mk cap => if cap < 2 ^ 20 then
      some (.seq (.seq (.ins (mv T0 HP :: li T1 (8 * (cap.toUInt64 + 2)) ++ [.r .add T1 T1 HP]))
        (.ite .bgeu SP T1 (.ins []) (.jmp .oom)))
        (.seq (.ins (li T2 cap.toUInt64 ++ [.sd 0 T0 0, .sd T2 T0 8, mv HP T1, .i .addi SP SP (-8)])) push), .buf)
      else none
  | .size b => match cE env d b with
    | some (cb, .buf) => some (.seq cb (.ins [.ld T0 SP 0, .ld T0 T0 0, .sd T0 SP 0]), .w)
    | _ => none
  | .get b i => match cE env d b, cE env (d + 1) i with
    | some (cb, .buf), some (ci, .w) =>
      some (.seq (.seq (.seq cb ci) (.ins [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .ld T2 T0 0]))
        (.seq (.ite .bltu T1 T2 (.ins [.i .slli T1 T1 3, .r .add T0 T0 T1, .ld T0 T0 16]) (.ins [mv T0 0]))
          (.ins [.sd T0 SP 0])), .w)
    | _, _ => none
  | .set b i x => match cE env d b, cE env (d + 1) i, cE env (d + 2) x with
    | some (cb, .buf), some (ci, .w), some (cx, .w) =>
      some (.seq (.seq (.seq (.seq cb ci) cx)
        (.ins [.ld A4 SP 0, .ld T1 SP 8, .ld T0 SP 16, .i .addi SP SP 16, .ld T2 T0 0]))
        (.ite .bltu T1 T2 (.ins [.i .slli T1 T1 3, .r .add T1 T0 T1, .sd A4 T1 16]) (.ins [])), .buf)
    | _, _, _ => none
  | .push b x => match cE env d b, cE env (d + 1) x with
    | some (cb, .buf), some (cx, .w) =>
      some (.seq (.seq (.seq cb cx) (.ins [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .ld T2 T0 0, .ld A4 T0 8]))
        (.ite .bltu T2 A4 (.ins [.i .slli A5 T2 3, .r .add A5 A5 T0, .sd T1 A5 16, .i .addi T2 T2 1, .sd T2 T0 0])
          (.jmp .cap)), .buf)
    | _, _ => none
  | .isize => some (.seq (.ins [.i .addi SP SP (-8), mv T0 IL]) push, .w)
  | .iget i => match cE env d i with
    | some (ci, .w) =>
      some (.seq (.seq ci (.ins [.ld T1 SP 0]))
        (.seq (.ite .bltu T1 IL (.ins [.r .add T0 IB T1, .lbu T0 T0 0]) (.ins [mv T0 0])) (.ins [.sd T0 SP 0])), .w)
    | _ => none
  | .loop f i z body => match cE env d f, cE env (d + 1) i with
    | some (cf, .w), some (ci, σ) =>
      let env' := (σ, d + 1) :: env
      let D := d + 1 + σ.size
      match cE env' D z with
      | some (cz, ρ) => match cT env' D σ ρ 0 body with
        | some cb => if σ.size + 1 ≤ Lim then
            some (.seq (.seq cf ci) (.loop [.ld T0 SP (8 * σ.size)] [.i .addi T0 T0 (-1), .sd T0 SP (8 * σ.size)]
              (.seq cz (.ins (slide ρ.size (σ.size + 1)))) cb), ρ)
          else none
        | none => none
      | none => none
    | _, _ => none
  termination_by e => sizeOf e
/-- a loop body tail at frame depth `D` (state of type `σ` just below, fuel below it) with `x` extra slots -/
def cT (env : List (Ty × Nat)) (D : Nat) (σ ρ : Ty) (x : Nat) : Tl → Option SC
  | .ret e => match cE env (D + x) e with
    | some (ce, τ) => if τ = ρ ∧ σ.size + 1 + x ≤ Lim then
        some (.seq (.seq ce (.ins (slide ρ.size (σ.size + 1 + x)))) (.jmp .exit)) else none
    | none => none
  | .next e => match cE env (D + x) e with
    | some (ce, τ) => if τ = σ ∧ σ.size + x ≤ Lim then
        some (.seq (.seq ce (.ins (slide σ.size (σ.size + x)))) (.jmp .head)) else none
    | none => none
  | .ite c a b t e => match cE env (D + x) a, cE env (D + x + 1) b, cT env D σ ρ x t, cT env D σ ρ x e with
    | some (ca, .w), some (cb, .w), some ct, some ce =>
      some (.seq (.seq (.seq ca cb) (.ins pop2)) (.ite (BOp.ofCmp c) T0 T1 ct ce))
    | _, _, _, _ => none
  | .let_ v b => match cE env (D + x) v with
    | some (cv, τ) => match cT ((τ, D + x) :: env) D σ ρ (x + τ.size) b with
      | some cb => some (.seq cv cb)
      | none => none
    | none => none
  | .split e b => match cE env (D + x) e with
    | some (ce, .prod τ τ') => match cT ((τ', D + x + τ.size) :: (τ, D + x) :: env) D σ ρ (x + τ.size + τ'.size) b with
      | some cb => some (.seq ce cb)
      | none => none
    | _ => none
  termination_by t => sizeOf t
end

/-- prologue: t6 := sp rounded down to 8; t3/t4 := input; t5 := work base -/
def prologue : List I := [.i .srli SP 2 3, .i .slli SP SP 3, mv IB 10, mv IL 11, mv HP 12]

/-- epilogue: (status, out) on the stack -/
def epilogue : SC :=
  .seq (.ins [.ld T0 SP 0, .ld T1 SP 8])
    (.ite .beq T1 0
      (.seq (.ins [.ld T2 T0 0, mv 11 T2, .i .addi T1 T0 16, mv A4 13])
        (.seq (.loop [mv T0 T2] [.i .addi T2 T2 (-1)] (.ins [])
          (.seq (.ins [.ld A5 T1 0, .sb A5 A4 0, .i .addi T1 T1 8, .i .addi A4 A4 1]) (.jmp .head)))
          (.ins [mv 10 0, .ret])))
      (.ins [mv 10 T1, mv 11 0, .ret]))

/-- the whole program as instructions: prologue, main, epilogue, the two abort stubs -/
def genI (p : Prog) : Option (List I) :=
  match cE [] 0 p.main with
  | some (c, .prod .w .buf) =>
    let body := SC.seq (.ins prologue) (.seq c epilogue)
    let om := body.len
    some (body.flat om (om + 2) 0 0 0 ++ [.i .addi 10 0 (-1), .ret, .i .addi 10 0 (-2), .ret])
  | _ => none

/-! ## encoding (RV64IM) -/
def bits (x : Int) (k : Nat) : Nat := (x % (2 ^ k : Int)).toNat
def encR (f7 f3 rd rs1 rs2 : Nat) : Nat := f7 <<< 25 ||| rs2 <<< 20 ||| rs1 <<< 15 ||| f3 <<< 12 ||| rd <<< 7 ||| 0x33
def encIt (op f3 rd rs1 : Nat) (imm : Int) : Nat := bits imm 12 <<< 20 ||| rs1 <<< 15 ||| f3 <<< 12 ||| rd <<< 7 ||| op
def encSt (f3 rs2 rs1 : Nat) (imm : Int) : Nat :=
  let u := bits imm 12
  (u >>> 5) <<< 25 ||| rs2 <<< 20 ||| rs1 <<< 15 ||| f3 <<< 12 ||| (u &&& 31) <<< 7 ||| 0x23
def encBt (f3 rs1 rs2 : Nat) (imm : Int) : Nat :=
  let u := bits imm 13
  ((u >>> 12) &&& 1) <<< 31 ||| ((u >>> 5) &&& 63) <<< 25 ||| rs2 <<< 20 ||| rs1 <<< 15 ||| f3 <<< 12 |||
    ((u >>> 1) &&& 15) <<< 8 ||| ((u >>> 11) &&& 1) <<< 7 ||| 0x63
def encJt (imm : Int) : Nat :=
  let u := bits imm 21
  ((u >>> 20) &&& 1) <<< 31 ||| ((u >>> 1) &&& 1023) <<< 21 ||| ((u >>> 11) &&& 1) <<< 20 |||
    ((u >>> 12) &&& 255) <<< 12 ||| 0x6f

def I.enc : I → Nat
  | .r f rd a b => match f with
    | .add => encR 0 0 rd a b | .sub => encR 32 0 rd a b | .mul => encR 1 0 rd a b
    | .and => encR 0 7 rd a b | .or => encR 0 6 rd a b | .xor => encR 0 4 rd a b
    | .sll => encR 0 1 rd a b | .srl => encR 0 5 rd a b | .sltu => encR 0 3 rd a b
  | .i f rd a imm => match f with
    | .addi => encIt 0x13 0 rd a imm | .ori => encIt 0x13 6 rd a imm | .andi => encIt 0x13 7 rd a imm
    | .xori => encIt 0x13 4 rd a imm | .slli => encIt 0x13 1 rd a imm | .srli => encIt 0x13 5 rd a imm
  | .ld rd a off => encIt 0x03 3 rd a off
  | .lbu rd a off => encIt 0x03 4 rd a off
  | .sd s a off => encSt 3 s a off
  | .sb s a off => encSt 0 s a off
  | .br c a b off => match c with
    | .beq => encBt 0 a b off | .bne => encBt 1 a b off | .bltu => encBt 6 a b off | .bgeu => encBt 7 a b off
  | .jal off => encJt off
  | .ret => 0x00008067

/-- the compiled program's words -/
def gen (p : Prog) : Option (List UInt32) := (genI p).map (·.map fun x => x.enc.toUInt32)

/-! ## the reference interpreter of the instruction list (for tests: runs the code on a model memory) -/

end Nano.V2
