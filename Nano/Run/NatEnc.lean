/- The native AArch64 ENCODER as a Lean specification (option E: the native generator is the atom encoder of Gen's J
program; the nano-subset translator is proved equal to this spec).  Input: a J program (`List J`, no RISC-V words:
later the generator's IR).
* the J VIEW `jk` / `jA` / `jB` / `jC` / `jop` (kind code and fields as UInt64, what the nano translator's accessor
  layer computes); `candC`: the atom code at the head of a J list, by the view (longest fused form first), `cand` its
  atom; `atomize`: the greedy parse, checked against the
  J list, so `atomize_j : atomize n l = some tl → tl.flatMap NTm.j = l` holds by construction.  Register-exact: the
  BGET / BSET tails are three plain atoms (`slli`, `alu`, `ld` / `sd`); the fused `bgetI` / `bsetI` are never produced.
* `NChk` (decidable checks), `natEncJ` (the encoder), `natEncJ_img` (its output is an image of the J program). -/
import Nano.Run.NatImgLaws
import Nano.Run.ExprExact
namespace JT
open Proven.Top SimW CallProbe ArmEnc

deriving instance DecidableEq for CallProbe.J

/-- the kind code of a J instruction (`e20` / `e25`) -/
def jk : J → UInt64
  | .addi _ _ _ => 1
  | .slli _ _ _ => 2
  | .srli _ _ _ => 3
  | .ld _ _ _ => 4
  | .sd _ _ _ => 5
  | .sb _ _ _ => 6
  | .lbu _ _ _ => 7
  | .alu _ _ _ _ => 8
  | .beq _ _ _ => 9
  | .bne _ _ _ => 10
  | .bltu _ _ _ => 11
  | .bgeu _ _ _ => 12
  | .jal _ _ => 13
  | .jalr _ _ => 14

/-- field A (`e21`): the destination; the source register of `sd` / `sb`; the first operand of a branch -/
def jA : J → UInt64
  | .addi d _ _ => d.toUInt64
  | .slli d _ _ => d.toUInt64
  | .srli d _ _ => d.toUInt64
  | .ld d _ _ => d.toUInt64
  | .sd s _ _ => s.toUInt64
  | .sb s _ _ => s.toUInt64
  | .lbu d _ _ => d.toUInt64
  | .alu _ d _ _ => d.toUInt64
  | .beq x _ _ => x.toUInt64
  | .bne x _ _ => x.toUInt64
  | .bltu x _ _ => x.toUInt64
  | .bgeu x _ _ => x.toUInt64
  | .jal rd _ => rd.toUInt64
  | .jalr rd _ => rd.toUInt64

/-- field B (`e22`): the base / first source; the second operand of a branch (0 for `jal`) -/
def jB : J → UInt64
  | .addi _ n _ => n.toUInt64
  | .slli _ n _ => n.toUInt64
  | .srli _ n _ => n.toUInt64
  | .ld _ n _ => n.toUInt64
  | .sd _ n _ => n.toUInt64
  | .sb _ n _ => n.toUInt64
  | .lbu _ n _ => n.toUInt64
  | .alu _ _ x _ => x.toUInt64
  | .beq _ y _ => y.toUInt64
  | .bne _ y _ => y.toUInt64
  | .bltu _ y _ => y.toUInt64
  | .bgeu _ y _ => y.toUInt64
  | .jal _ _ => 0
  | .jalr _ rs => rs.toUInt64

/-- field C (`e23`): immediate / shift / offset (two's complement, branch offsets in J instructions); the second
source of `alu` -/
def jC : J → UInt64
  | .addi _ _ imm => iu imm
  | .slli _ _ sh => sh.toUInt64
  | .srli _ _ sh => sh.toUInt64
  | .ld _ _ off => iu off
  | .sd _ _ off => iu off
  | .sb _ _ off => iu off
  | .lbu _ _ off => iu off
  | .alu _ _ _ y => y.toUInt64
  | .beq _ _ off => iu off
  | .bne _ _ off => iu off
  | .bltu _ _ off => iu off
  | .bgeu _ _ off => iu off
  | .jal _ off => iu off
  | .jalr _ _ => 0

/-- the ALU op (`e24`), 0 for other instructions -/
def jop : J → UInt64
  | .alu op _ _ _ => op.toUInt64
  | _ => 0

/-! ## the atom at the head of a J list, by the view (the text mirrors the nano translator's `e35`, so that
"`e35` = `candC`" is a rewrite of the accessors) -/

/-- kind / fields of instruction `m` of `l` (0 past the end) -/
def kd (l : List J) (m : Nat) : UInt64 := ((l[m]?).map jk).getD 0
def fA (l : List J) (m : Nat) : UInt64 := ((l[m]?).map jA).getD 0
def fB (l : List J) (m : Nat) : UInt64 := ((l[m]?).map jB).getD 0
def fC (l : List J) (m : Nat) : UInt64 := ((l[m]?).map jC).getD 0
def fO (l : List J) (m : Nat) : UInt64 := ((l[m]?).map jop).getD 0

def eqb (a b : UInt64) : UInt64 := if a == b then 1 else 0
def neb (a b : UInt64) : UInt64 := if a == b then 0 else 1
/-- 1 iff instruction `m` is (kind k, A a, B b, C x) -/
def m26 (l : List J) (m : Nat) (k a b x : UInt64) : UInt64 :=
  if kd l m == k then eqb (fA l m) a * eqb (fB l m) b * eqb (fC l m) x else 0
/-- 1 iff instruction `m` is `alu p d x y` -/
def m28 (l : List J) (m : Nat) (p d x y : UInt64) : UInt64 := m26 l m 8 d x y * eqb (fO l m) p
/-- 1 iff instruction 1 is `jal 0 _` -/
def m29 (l : List J) : UInt64 := if kd l 1 == 13 then eqb (fA l 1) 0 else 0
/-- 1 iff `v` is negative (two's complement) -/
def sneg (v : UInt64) : UInt64 := if 9223372036854775807 < v then 1 else 0
/-- `v` as an unsigned byte value (negative ↦ 0) -/
def s30 (v : UInt64) : UInt64 := if sneg v == 1 then 0 else v

/-- the value of Gen's long `li` (`liT`, 8 bytes, top first), read from the `slli; addi` pairs from instruction `j` -/
def liV : Nat → List J → Nat → UInt64 → UInt64
  | 0, _, _, a => a
  | k + 1, l, j, a =>
    if kd l j == 2 then (if kd l (j + 1) == 1 then liV k l (j + 2) (a * 256 + s30 (fC l (j + 1))) else a) else a

/-- **the atom code** at the head of `l` (0: none): 1 li, 2 addi, 3 alu, 4 ld, 5 sd, 6 ldp, 7 ldp (swapped), 8 cj geu,
9 cj ltu, 10 cj eq, 11 lpz, 12 bgeu, 13 beqz, 14 bnez, 15 ldrbx, 16 slli, 18 bpushI, 19 align8, 20 jal, 21 jalr, 22 sb;
fused forms first -/
def candC (l : List J) : UInt64 :=
  let k := kd l 0;
  let k2 := kd l 1;
  if k == 1 then
    (if fB l 0 == 0 then
      (if k2 == 2 then (if fC l 1 == 8 then
        (if eqb (fA l 1) (fA l 0) * eqb (fB l 1) (fA l 0) == 1 then 1 else 2) else 2) else 2)
     else 2)
  else if k == 4 then
    (if k2 == 4 then
      (if fC l 0 == 0 then
        (if fC l 1 == 8 then
          (if eqb (fB l 0) (fB l 1) * neb (fA l 0) (fA l 1) * neb (fA l 0) (fB l 0)
              * neb (fA l 1) (fB l 0) == 1 then 6 else 4) else 4)
       else if fC l 0 == 8 then
        (if fC l 1 == 0 then
          (if eqb (fB l 0) (fB l 1) * neb (fA l 0) (fA l 1) * neb (fA l 0) (fB l 0)
              * neb (fA l 1) (fB l 0) == 1 then 7 else 4) else 4)
       else 4)
     else 4)
  else if k == 5 then 5
  else if k == 12 then (if fC l 0 == 2 then (if m29 l == 1 then 8 else 12) else 12)
  else if k == 11 then (if fC l 0 == 2 then (if m29 l == 1 then 9 else 0) else 0)
  else if k == 9 then
    (if fC l 0 == 2 then
      (if m29 l == 1 then (if fB l 0 == 0 then 11 else 10) else (if fB l 0 == 0 then 13 else 0))
     else (if fB l 0 == 0 then 13 else 0))
  else if k == 10 then (if fB l 0 == 0 then 14 else 0)
  else if k == 8 then
    (if fO l 0 == 1 then
      (if k2 == 7 then (if fC l 1 == 0 then
        (if eqb (fA l 1) (fA l 0) * eqb (fB l 1) (fA l 0) == 1 then 15 else 3) else 3) else 3)
     else 3)
  else if k == 2 then
    (if m26 l 0 2 15 7 3 * m28 l 1 1 15 15 5 == 1 then 18 else 16)
  else if k == 3 then
    (if fC l 0 == 3 then (if k2 == 2 then (if fC l 1 == 3 then
      (if eqb (fA l 1) (fA l 0) * eqb (fB l 1) (fA l 0) == 1 then 19 else 0) else 0) else 0) else 0)
  else if k == 13 then 20
  else if k == 14 then 21
  else if k == 6 then (if fC l 0 == 0 then 22 else 0)
  else 0

/-- the atom of code `t` at the head of `l`, built from the instructions' own fields (whatever `t` is, `atomize`
checks the atom against the list) -/
def mkAtom (t : UInt64) (l : List J) : Option NTm :=
  match l with
  | [] => none
  | i :: r =>
    if t == 1 then (match i with | .addi d _ _ => some (.li d (liV 8 l 1 0)) | _ => none)
    else if t == 2 then (match i with | .addi d n imm => some (.addi d n imm) | _ => none)
    else if t == 3 then (match i with | .alu op d x y => some (.alu op d x y) | _ => none)
    else if t == 4 then (match i with | .ld d n off => some (.ld d n off) | _ => none)
    else if t == 5 then (match i with | .sd x n off => some (.sd x n off) | _ => none)
    else if t == 6 then (match i, r with | .ld x n _, .ld y _ _ :: _ => some (.ldp x y n false) | _, _ => none)
    else if t == 7 then (match i, r with | .ld y n _, .ld x _ _ :: _ => some (.ldp x y n true) | _, _ => none)
    else if t == 8 then (match i, r with | .bgeu x y _, .jal _ off :: _ => some (.cj .geu x y off) | _, _ => none)
    else if t == 9 then (match i, r with | .bltu x y _, .jal _ off :: _ => some (.cj .ltu x y off) | _, _ => none)
    else if t == 10 then (match i, r with | .beq x y _, .jal _ off :: _ => some (.cj .eq x y off) | _, _ => none)
    else if t == 11 then (match i, r with | .beq x _ _, .jal _ off :: _ => some (.lpz x off) | _, _ => none)
    else if t == 12 then (match i with | .bgeu x y off => some (.bgeu x y off) | _ => none)
    else if t == 13 then (match i with | .beq x _ off => some (.beqz x off) | _ => none)
    else if t == 14 then (match i with | .bne x _ off => some (.bnez x off) | _ => none)
    else if t == 15 then (match i with | .alu _ d n m => some (.ldrbx d n m) | _ => none)
    else if t == 16 then (match i with | .slli d n sh => some (.slli d n sh) | _ => none)
    else if t == 18 then some .bpushI
    else if t == 19 then (match i with | .srli d n _ => some (.align8 d n) | _ => none)
    else if t == 20 then (match i with | .jal rd off => some (.jal rd off) | _ => none)
    else if t == 21 then (match i with | .jalr _ rs => some (.jalr rs) | _ => none)
    else if t == 22 then (match i with | .sb x n _ => some (.sb x n) | _ => none)
    else none

/-- **the atom that starts a J list** -/
def cand (l : List J) : Option NTm := mkAtom (candC l) l

/-- **the greedy parse** of a J list into atoms (`n` = fuel, the length suffices); every atom is checked against the list -/
def atomize : Nat → List J → Option (List NTm)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, i :: l =>
    match cand (i :: l) with
    | none => none
    | some t =>
      if (i :: l).take t.j.length = t.j then (atomize n ((i :: l).drop t.j.length)).map (t :: ·) else none

/-- the parse is a parse: the atoms' J instructions are the list -/
theorem atomize_j : ∀ (n : Nat) (l : List J) (tl : List NTm), atomize n l = some tl → tl.flatMap NTm.j = l
  | 0, [], tl, h => by simp only [atomize, Option.some.injEq] at h; subst h; rfl
  | n + 1, [], tl, h => by simp only [atomize, Option.some.injEq] at h; subst h; rfl
  | 0, _ :: _, tl, h => by simp [atomize] at h
  | n + 1, i :: l, tl, h => by
    simp only [atomize] at h
    split at h
    · exact absurd h (by simp)
    · rename_i t _
      split at h
      · rename_i hp
        cases hr : atomize n ((i :: l).drop t.j.length) with
        | none => rw [hr] at h; exact absurd h (by simp)
        | some r =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          rw [List.flatMap_cons, atomize_j n _ r hr]
          have e := List.take_append_drop t.j.length (i :: l)
          rw [hp] at e
          exact e
      · exact absurd h (by simp)

/-! ## the encoder -/

theorem jOf_map (ts : List NTm) : jOf (ts.map fun t => (⟨t, false, false⟩ : NAt)) = ts.flatMap NTm.j := by
  induction ts with
  | nil => rfl
  | cons t l ih => simp only [List.map_cons, jOf_cons, List.flatMap_cons, ih]

/-- all jump targets of an atom list, from J pc `q` -/
def tgs : List NAt → Nat → List Nat
  | [], _ => []
  | x :: l, q => x.t.tg q ++ tgs l (q + x.t.j.length)

theorem tgs_mem : ∀ (pre : List NAt) (x : NAt) (suf : List NAt) (q p : Nat),
    p ∈ x.t.tg (q + (jOf pre).length) → p ∈ tgs (pre ++ x :: suf) q
  | [], x, suf, q, p, h => by
    simp only [List.nil_append, tgs, List.mem_append]
    left; simpa [jOf] using h
  | y :: pre, x, suf, q, p, h => by
    simp only [List.cons_append, tgs, List.mem_append]
    right
    apply tgs_mem pre x suf (q + y.t.j.length) p
    rw [jOf_cons, List.length_append, ← Nat.add_assoc] at h
    exact h

/-- **the encoder's checks** (decidable; the nano translator performs the same ones): the size limit, the per-atom
side conditions, no dead register (flags off, no atom that kills one), every jump target an atom boundary -/
def NChk (tl : List NAt) : Prop :=
  (wordsOf tl).length < 2 ^ 18 ∧
  (∀ x ∈ tl, x.t.ok = true ∧ x.d5 = false ∧ x.d6 = false ∧ x.t.kills 5 = false ∧ x.t.kills 6 = false) ∧
  (∀ p ∈ tgs tl 0, p ∈ (bnd tl 0 0).map Prod.fst)

instance (tl : List NAt) : Decidable (NChk tl) := by unfold NChk; infer_instance

theorem kills_of (t : NTm) (h5 : t.kills 5 = false) (h6 : t.kills 6 = false) (r : Nat) : t.kills r = false := by
  cases t <;> simp_all [NTm.kills]

/-- the checks give a well-formed atom list -/
theorem nchk_wf {tl : List NAt} (h : NChk tl) : NWf tl := by
  obtain ⟨hs, ha, ht⟩ := h
  have hdead : ∀ x ∈ tl, ∀ r, x.dead r = false := fun x hx r => by
    obtain ⟨-, h5, h6, -, -⟩ := ha x hx
    simp [NAt.dead, h5, h6]
  have hout : ∀ x ∈ tl, ∀ r, x.out r = false := fun x hx r => by
    obtain ⟨-, h5, h6, k5, k6⟩ := ha x hx
    simp [NAt.out, NAt.dead, h5, h6, kills_of x.t k5 k6 r]
  have mem : ∀ {pre : List NAt} {x : NAt} {suf : List NAt}, tl = pre ++ x :: suf → x ∈ tl := fun e => by
    rw [e]; simp
  exact {
    size := hs
    ok := fun x hx => (ha x hx).1
    rd := fun x hx r hd => by rw [hdead x hx r] at hd; exact absurd hd (by decide)
    fall := fun pre x suf e _ r ho => by rw [hout x (mem e) r] at ho; exact absurd ho (by decide)
    tgt := fun pre x suf e p hp => by
      refine ⟨?_, fun r ho => by rw [hout x (mem e) r] at ho; exact absurd ho (by decide)⟩
      have hm : p ∈ tgs tl 0 := by
        rw [e]; exact tgs_mem pre x suf 0 p (by rw [Nat.zero_add]; exact hp)
      obtain ⟨⟨a, w⟩, hm', rfl⟩ := List.mem_map.1 (ht p hm)
      exact ⟨w, hm'⟩
    ret := fun pre x suf rs e _ pre' off d5 d6 suf' _ r hd => by
      rw [hdead x (mem e) r] at hd; exact absurd hd (by decide) }

/-- **the native encoder** (specification): the code bytes of a J program, or none -/
def natEncJ (Cj : List J) : Option (List UInt8) :=
  ((atomize Cj.length Cj).map fun ts => ts.map fun t => (⟨t, false, false⟩ : NAt)).bind fun tl =>
    if NChk tl then some (wordBytes (wordsOf tl)) else none

/-- **the encoder's output is an image of the J program** (the image relation by construction) -/
theorem natEncJ_img {Cj : List J} {B : List UInt8} (h : natEncJ Cj = some B) : ∃ I : Img, I.code = B ∧ NatV Cj I := by
  unfold natEncJ at h
  cases hz : atomize Cj.length Cj with
  | none => rw [hz] at h; exact absurd h (by simp)
  | some ts =>
    rw [hz] at h
    change (if NChk (ts.map fun t => (⟨t, false, false⟩ : NAt)) then _ else _) = some B at h
    split at h
    · rename_i hc
      cases h
      exact ⟨imgOf _, rfl, _, by rw [jOf_map]; exact (atomize_j _ _ _ hz).symm, rfl, nchk_wf hc⟩
    · cases h

end JT
