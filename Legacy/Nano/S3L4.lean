/- **nano → S3, link 4: an S3 program on bytes** (`Testing/notes/NANO_S3.md`).

L4 = S3 programs (`Proven.S3.Prog`, meaning `Prog.run` on bytes).  The ONE construct added: datatypes (`mk`/`cas`),
used only for I/O: byte lists (`d 0`, `[]` / `b :: rest`) and the pair (word, rest) of the decoder (`d 1`).
`toS3 p` is a one-function program (signature `S0`): `main` reads the input list 8 bytes per argument (`rdW`:
word = Σ bᵢ·256ⁱ by `mul`/`add`, returned with the rest as a pair, so its temporaries are scoped and the frame grows
by 3 registers per argument), binds the `n` words (newest = nano variable 0), evaluates `tr3 σ p.2` (link 3), and
builds the 8 result bytes
(`outB`: byte = `v`, then `v / 256`; the list keeps the low byte of each word).  Inputs that are too short give `[]`
(not reached when `nanoRun` is defined).
Theorem: `toS3_run : run2 p input = some out → (toS3 p).run input = some out` (all programs, all inputs), where
`run2` is nano's byte-level meaning (`nanoRun`) on L2 programs. -/
import Legacy.Nano.S3L3
import Legacy.Nano.Proof

namespace Nano.S3
open Proven.S3

/-- the signature: datatype `0` = byte lists, datatype `1` = pairs (word, byte list), one function
`main : d 0 → d 0` -/
abbrev S0 : Sig := ⟨[[[], [.w, .d 0]], [[.w, .d 0]]], [([.d 0], .d 0)]⟩

abbrev BL : Ty := .d 0
abbrev PR : Ty := .d 1

def nilE {Γ : List Ty} : Expr S0 Γ BL := .mk 0 0 .nil
def consE {Γ : List Ty} (h : Var Γ .w) (t : Var Γ BL) : Expr S0 Γ BL := .mk 0 1 (.cons h (.cons t .nil))
def pairE {Γ : List Ty} (h : Var Γ .w) (t : Var Γ BL) : Expr S0 Γ PR := .mk 1 0 (.cons h (.cons t .nil))

/-- `match x with | [] => n | b :: t => c` (in `c`, `b` is variable 0 and `t` variable 1) -/
def casL {Γ : List Ty} {τ : Ty} (x : Var Γ BL) (n : Expr S0 Γ τ) (c : Expr S0 (.w :: BL :: Γ) τ) : Expr S0 Γ τ :=
  .cas x (Alts.arms (Alts.cons n (Alts.cons c .nil)))

/-- `match r with | (w, t) => c` -/
def casP {Γ : List Ty} {τ : Ty} (r : Var Γ PR) (c : Expr S0 (.w :: BL :: Γ) τ) : Expr S0 Γ τ :=
  .cas r (Alts.arms (Alts.cons c .nil))

/-- the `k` little-endian bytes of `v` as a byte list -/
def outB : (k : Nat) → {Γ : List Ty} → Var Γ .w → Expr S0 Γ BL
  | 0, _, _ => nilE
  | k + 1, _, v => .let_ (.lit 256) (.let_ (.bin .udiv v.s .z) (.let_ (outB k .z) (consE v.s.s.s .z)))

/-- read `j` more bytes of a word into `acc` (byte `7 - j` weighs `256 ^ (7 - j)`): the pair (word, rest); the
temporaries of a byte are scoped inside the `let` of the new accumulator (registers do not pile up) -/
def rdW : (j : Nat) → {Γ : List Ty} → Var Γ .w → Var Γ BL → Expr S0 Γ PR
  | 0, _, acc, x => pairE acc x
  | j + 1, _, acc, x => casL x (pairE acc x)
      (.let_ (.let_ (.lit (BitVec.ofNat 64 (256 ^ (7 - j)))) (.let_ (.bin .mul Var.z.s .z) (.bin (.op .add) acc.s.s.s.s .z)))
        (rdW j .z Var.z.s.s))

/-- read `n` more words (each: `let r := (read 8 bytes); match r with (w, rest) => …`), then evaluate the body
(`tr3 σ a`, `σ` = the words, newest first) and write the result -/
def wdW (a : A) : (n : Nat) → {Γ : List Ty} → List (Var Γ .w) → Var Γ BL → Expr S0 Γ BL
  | 0, _, σ, _ => .let_ (tr3 σ a) (outB 8 .z)
  | n + 1, _, σ, x => .let_ (.let_ (.lit 0) (rdW 8 .z x.s))
      (casP .z (wdW a n (.z :: σ.map fun y => y.s.s.s) Var.z.s))

/-- **link 4**: the S3 program of an L2 program -/
def toS3 (p : Prog2) : Proven.S3.Prog where
  S := S0
  bodies := .cons (wdW p.2 p.1 [] .z) .nil
  main := ⟨0, by decide⟩

/-- nano's byte-level meaning (`nanoRun`) on L2 programs -/
def run2 (p : Prog2) (input : List UInt8) : Option (List UInt8) :=
  (wordsOf p.1 input).bind fun args => (p.eval args).map fun v => Proven.leN 8 v.toNat

/-! ## correctness -/

section
variable {bs : Bodies S0 S0.fns} {m : Fin S0.fns.length}

/-- the value `outB k` builds -/
def outV : Nat → BitVec 64 → V
  | 0, _ => .c 0 []
  | k + 1, x => .c 1 [.w x, outV k (x / 256)]

theorem bytesOut_outV : ∀ (k : Nat) (x : BitVec 64), bytesOut (outV k x) = some (Proven.leN k x.toNat)
  | 0, _ => rfl
  | k + 1, x => by
    simp only [outV, bytesOut, bytesOut_outV k, Option.map_some, Proven.leN, Option.some.injEq, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · apply UInt8.toNat_inj.mp; simp
    · simp [BitVec.toNat_udiv]

theorem outB_ok (env : List V) : ∀ (k : Nat) {Γ : List Ty} (v : Var Γ .w) (x : BitVec 64), env[v.idx]? = some (.w x) →
    Ev ⟨S0, bs, m⟩ env (outB k v) (outV k x)
  | 0, _, _, _, _ => .mk rfl
  | k + 1, _, v, x, h => by
    refine .let_ .lit (.let_ (.bin (by simpa [Var.idx] using h) rfl) (.let_ (outB_ok _ k .z _ rfl) (.mk ?_)))
    simp [Vars.get, Vars.idxs, Var.idx, h]; rfl

theorem casL_cons {Γ : List Ty} {τ : Ty} {env : List V} {x : Var Γ BL} {n : Expr S0 Γ τ}
    {c : Expr S0 (.w :: BL :: Γ) τ} {h t v : V} (hx : env[x.idx]? = some (.c 1 [h, t]))
    (hc : Ev ⟨S0, bs, m⟩ (h :: t :: env) c v) : Ev ⟨S0, bs, m⟩ env (casL x n c) v :=
  .cas (j := 1) (by show 1 < 2; decide) hx rfl hc

theorem casP_ok {Γ : List Ty} {τ : Ty} {env : List V} {r : Var Γ PR}
    {c : Expr S0 (.w :: BL :: Γ) τ} {h t v : V} (hx : env[r.idx]? = some (.c 0 [h, t]))
    (hc : Ev ⟨S0, bs, m⟩ (h :: t :: env) c v) : Ev ⟨S0, bs, m⟩ env (casP r c) v :=
  .cas (j := 0) (by show 0 < 1; decide) hx rfl hc

theorem unle_append : ∀ (l₁ l₂ : List UInt8), Proven.unle (l₁ ++ l₂) = Proven.unle l₁ + 256 ^ l₁.length * Proven.unle l₂
  | [], _ => by simp [Proven.unle]
  | b :: l, l₂ => by
    simp only [List.cons_append, Proven.unle, unle_append l l₂, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ l.length)]; omega

theorem acc_step (pre : List UInt8) (b : UInt8) :
    BitVec.ofNat 64 (Proven.unle (pre ++ [b])) =
      BitVec.ofNat 64 (Proven.unle pre) + b.toBitVec.setWidth 64 * BitVec.ofNat 64 (256 ^ pre.length) := by
  rw [unle_append]
  simp only [Proven.unle, Nat.mul_zero, Nat.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, UInt8.toNat_toBitVec]
  rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by have := b.toNat_lt; omega)]
  simp [Nat.add_mod, Nat.mul_mod, Nat.mul_comm]

theorem Agree.lift3 {Γ : List Ty} {env : List V} {σ : List (Var Γ .w)} {ws : List UInt64} (h : Agree env σ ws)
    {τ₁ τ₂ τ₃ : Ty} (v₁ v₂ v₃ : V) :
    Agree (v₁ :: v₂ :: v₃ :: env) (σ.map fun y => (Var.s (σ := τ₁) (Var.s (σ := τ₂) (Var.s (σ := τ₃) y)))) ws := by
  have := ((h.lift τ₃ v₃).lift τ₂ v₂).lift τ₁ v₁
  simpa [List.map_map, Function.comp_def] using this

/-- reading `j` bytes gives the word of the bytes read so far and the `j` next ones, and the rest -/
theorem rd_ok : ∀ (j : Nat) {Γ : List Ty} (acc : Var Γ .w) (x : Var Γ BL) (env : List V) (pre rest : List UInt8),
    env[acc.idx]? = some (.w (BitVec.ofNat 64 (Proven.unle pre))) → env[x.idx]? = some (bytesV rest) →
    pre.length + j = 8 → j ≤ rest.length →
    Ev ⟨S0, bs, m⟩ env (rdW j acc x)
      (.c 0 [.w (BitVec.ofNat 64 (Proven.unle (pre ++ rest.take j))), bytesV (rest.drop j)])
  | 0, _, acc, x, env, pre, rest, ha, hx, _, _ => by
    rw [rdW]; refine .mk ?_; simp [Vars.get, Vars.idxs, ha, hx]
  | j + 1, _, acc, x, env, pre, rest, ha, hx, hl, hr => by
    cases rest with
    | nil => simp at hr
    | cons b rest' =>
      rw [rdW]
      refine casL_cons (by simp [bytesV] at hx ⊢; exact hx) ?_
      refine .let_ (.let_ .lit (.let_ (.bin rfl rfl) (.bin (by simpa [Var.idx] using ha) rfl))) ?_
      rw [show pre ++ List.take (j + 1) (b :: rest') = (pre ++ [b]) ++ rest'.take j by simp,
        show List.drop (j + 1) (b :: rest') = rest'.drop j by simp]
      refine rd_ok j .z Var.z.s.s _ (pre ++ [b]) rest' ?_ (by simp [Var.idx]) (by simp; omega) (by simp at hr; omega)
      simp only [List.getElem?_cons_zero, Option.some.injEq, V.w.injEq, Var.idx]
      rw [acc_step, show pre.length = 7 - j by omega]; rfl

theorem wd_ok (a : A) : ∀ (n : Nat) {Γ : List Ty} (σ : List (Var Γ .w)) (x : Var Γ BL) (env : List V)
    (ws : List UInt64) (rest : List UInt8) (more : List UInt64), Agree env σ ws → env[x.idx]? = some (bytesV rest) →
    wordsOf n rest = some more → Ev ⟨S0, bs, m⟩ env (wdW a n σ x) (outV 8 (den2 a (more.reverse ++ ws)).toBitVec)
  | 0, _, σ, x, env, ws, rest, more, hσ, hx, hw => by
    simp only [wordsOf] at hw
    split at hw
    · cases hw; rw [wdW]
      exact .let_ (tr3_ok _ a σ env ws hσ) (outB_ok _ 8 .z _ rfl)
    · exact nomatch hw
  | n + 1, _, σ, x, env, ws, rest, more, hσ, hx, hw => by
    simp only [wordsOf] at hw
    split at hw
    · next h8 =>
      cases hm : wordsOf n (rest.drop 8) with
      | none => rw [hm] at hw; exact nomatch hw
      | some more' =>
        rw [hm] at hw; cases hw
        rw [wdW]
        refine .let_ (.let_ .lit (rd_ok 8 .z x.s _ [] rest rfl (by simpa [Var.idx] using hx) rfl h8)) ?_
        refine casP_ok rfl ?_
        rw [show (UInt64.ofNat (Proven.unle (List.take 8 rest)) :: more').reverse ++ ws =
          more'.reverse ++ UInt64.ofNat (Proven.unle (List.take 8 rest)) :: ws by simp]
        exact wd_ok a n _ Var.z.s
          (.w (BitVec.ofNat 64 (Proven.unle (rest.take 8))) :: bytesV (rest.drop 8) ::
            .c 0 [.w (BitVec.ofNat 64 (Proven.unle (rest.take 8))), bytesV (rest.drop 8)] :: env) (UInt64.ofNat (Proven.unle (rest.take 8)) :: ws)
          (rest.drop 8) more' ⟨by simp [Var.idx]; rfl, hσ.lift3 (τ₁ := .w) (τ₂ := BL) (τ₃ := PR) _ _ _⟩
          (by simp [Var.idx]) hm
    · exact nomatch hw

end

/-- **link 4 is correct**: wherever nano's byte-level meaning gives `out`, the S3 program's meaning gives `out` -/
theorem toS3_run (p : Prog2) (input out : List UInt8) (h : run2 p input = some out) : (toS3 p).run input = some out := by
  unfold run2 at h
  cases hw : wordsOf p.1 input with
  | none => rw [hw] at h; exact nomatch h
  | some args =>
    rw [hw, Option.bind_some] at h
    unfold Prog2.eval at h
    split at h
    · next hl =>
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hD : (toS3 p).Den input (outV 8 (den2 p.2 args.reverse).toBitVec) := by
        have := wd_ok (bs := (toS3 p).bodies) (m := (toS3 p).main) p.2 p.1 (Γ := [BL]) [] .z [bytesV input] [] input args trivial
          (by simp [Var.idx]) hw
        simpa using this
      rw [Prog.run_eq hD, bytesOut_outV]; rfl
    · exact nomatch h

end Nano.S3
