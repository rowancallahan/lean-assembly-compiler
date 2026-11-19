/- Nano/V2Self/Proof/ParInvRep: Layer 3 (machine ↔ spec) representation relations that do not depend on the task `Frame`
(see Testing/notes/NANO_V2_PARINV_DESIGN.md).  Box C owns this file; box D builds handler lemmas on it.
* `TokAt h p toks`  : the token region from cursor `p` decodes to the spec tokens `toks` (numerals: 8 byte words, each < 256).
* `RNRep h u n ids` / `KidsR h f ns ids` : the arena record u (8 words at d5 + 8u: tag, a, b, shape code, pending, first child, count,
  next) and its child chain represent box B's Layer-2 tree `n : ParRun.RN` EXACTLY; `ids` = the records read (u first).
* `ShOpt h c o` : shape code ↔ `Option Sh` (0 ↔ none).
* `ArenaRep h arena vals` : h[9] = |arena|, record u ↔ arena[u] for every u; h[8] = |vals|, operand k (TOP = 0) is a node id r with
  arena[r] = vals[k], distinct roots, and a root lies in no other node's subtree (so relinking roots is local). -/
import Nano.V2Self.Proof.ParRep
import Nano.V2Self.Proof.ParRun
namespace ParInv
open C BufL ParSpec

/-! ## tokens -/
/-- the token words from cursor `p` decode to `toks` (cf. `ParSpec.detokA`), ending at the token count h[7] -/
inductive TokAt (h : Buf) : UInt64 → List Tok → Prop
  | nil {p : UInt64} : p = bget h 7 → TokAt h p []
  | kw {p : UInt64} {r : List Tok} (t : UInt64) : p < bget h 7 → bget h (d11 + p) = t → t ≠ 5 → t ≠ 14 → okTag t.toNat = true →
      TokAt h (p + 1) r → TokAt h p (.k t.toNat :: r)
  | num {p : UInt64} {r : List Tok} (bs : List UInt64) : p < bget h 7 → bget h (d11 + p) = 5 → bs.length = 8 →
      (∀ i, i < 8 → bget h (d11 + (p + 1 + i.toUInt64)) = bs.getD i 0) → (∀ b ∈ bs, b.toNat < 256) →
      TokAt h (p + 9) r → TokAt h p (.num (bytesVal (bs.map UInt64.toNat)) :: r)
  | id {p : UInt64} {r : List Tok} (nm : List UInt64) : NameOK h p nm →
      TokAt h (p + 2 + 2 * nm.length.toUInt64) r → TokAt h p (.id (nm.map UInt64.toNat) :: r)

/-! ## arena nodes ↔ Layer-2 trees -/
/-- field `k` of node `u` (record of 8 words at d5 + 8u) -/
def fld (h : Buf) (u : UInt64) (k : UInt64) : UInt64 := bget h (d5 + 8 * u + k)

/-- shape code ↔ optional shape (code 0 = none: the CONTINUE state tuple, a binder not typed yet) -/
def ShOpt (h : Buf) (c : UInt64) : Option Sh → Prop
  | none => c = 0
  | some s => ShapeCode h c s

open ParRun in
mutual
inductive RNRep (h : Buf) : UInt64 → RN → List UInt64 → Prop
  | mk {u : UInt64} {t a b : Nat} {sh : Option Sh} {p : Bool} {ks : List RN} {ids : List UInt64} :
      fld h u 0 = t.toUInt64 → fld h u 1 = a.toUInt64 → fld h u 2 = b.toUInt64 → ShOpt h (fld h u 3) sh →
      fld h u 4 = (if p then 1 else 0) → fld h u 6 = ks.length.toUInt64 → t < 2 ^ 64 → a < 2 ^ 64 → b < 2 ^ 64 →
      KidsR h (fld h u 5) ks ids → RNRep h u (.mk t a b sh p ks) (u :: ids)
inductive KidsR (h : Buf) : UInt64 → List RN → List UInt64 → Prop
  | nil {f : UInt64} : KidsR h f [] []
  | cons {f : UInt64} {n : RN} {ns : List RN} {i1 ids : List UInt64} :
      RNRep h f n i1 → KidsR h (fld h f 7) ns ids → KidsR h f (n :: ns) (i1 ++ ids)
end

/-! ## arena frame rule -/
theorem RNRep.mem {h : Buf} {u : UInt64} {n : ParRun.RN} {ids : List UInt64} (r : RNRep h u n ids) : u ∈ ids := by
  cases r; simp

theorem RNRep.head {h : Buf} {u : UInt64} {n : ParRun.RN} {ids : List UInt64} (r : RNRep h u n ids) : ∃ t, ids = u :: t := by
  cases r; exact ⟨_, rfl⟩

/-- cells of the records `ids` (all 8 fields) agree -/
def RecAgree (h h' : Buf) (ids : List UInt64) : Prop := ∀ v ∈ ids, ∀ k : UInt64, k.toNat < 8 → fld h' v k = fld h v k

/-- the shape table region `[155712, 155712 + 3·8192)` agrees -/
def ShTabAgree (h h' : Buf) : Prop := ∀ i : UInt64, 155712 ≤ i.toNat → i.toNat < 155712 + 3 * 8192 → bget h' i = bget h i

theorem shapeRow (c : UInt64) (h1 : 5 ≤ c.toNat) (h2 : c.toNat < 5 + 8192) (k : UInt64) (hk : k.toNat < 3) :
    (d7 + 8192 + 3 * (c - 5) + k).toNat = 155712 + 3 * (c.toNat - 5) + k.toNat := by
  have e5 : (c - 5).toNat = c.toNat - 5 := by rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have e3 : (3 * (c - 5)).toNat = 3 * (c.toNat - 5) := by
    rw [UInt64.toNat_mul, e5, show (3 : UInt64).toNat = 3 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have a1 : (d7 + 8192 : UInt64).toNat = 155712 := rfl
  have a2 : (d7 + 8192 + 3 * (c - 5)).toNat = 155712 + 3 * (c.toNat - 5) := by
    rw [UInt64.toNat_add, a1, e3]; exact Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_add, a2]; exact Nat.mod_eq_of_lt (by omega)

theorem ShapeCode.frame {h h' : Buf} {c : UInt64} {s : Sh} (r : ShapeCode h c s) (e : ShTabAgree h h') : ShapeCode h' c s := by
  induction r with
  | uw => exact .uw
  | bf => exact .bf
  | ls => exact .ls
  | nt => exact .nt
  | pr h1 h2 hl hr _ _ il ir =>
    have r0 := shapeRow _ h1 h2 0 (by decide)
    have r1 := shapeRow _ h1 h2 1 (by decide)
    simp only [UInt64.add_zero, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl, Nat.add_zero] at r0 r1
    exact .pr h1 h2 (by rw [e _ (by omega) (by omega)]; exact hl) (by rw [e _ (by omega) (by omega)]; exact hr) il ir

theorem ShOpt.frame {h h' : Buf} {c : UInt64} {o : Option Sh} (r : ShOpt h c o) (e : ShTabAgree h h') : ShOpt h' c o := by
  cases o with
  | none => exact r
  | some s => exact ShapeCode.frame (h := h) r e

mutual
/-- a subtree's representation only reads its own records and the shape table (the root's next field is not read) -/
theorem RNRep.frame {h h' : Buf} {u : UInt64} {n : ParRun.RN} {ids : List UInt64} (r : RNRep h u n ids)
    (e0 : ∀ k : UInt64, k.toNat < 7 → fld h' u k = fld h u k) (e : RecAgree h h' ids.tail) (es : ShTabAgree h h') :
    RNRep h' u n ids := by
  have g : ∀ k : UInt64, k.toNat < 7 → fld h u k = fld h' u k := fun k hk => (e0 k hk).symm
  match r with
  | .mk a0 a1 a2 a3 a4 a6 x y z k =>
    exact .mk (by rw [← g 0 (by decide)]; exact a0) (by rw [← g 1 (by decide)]; exact a1) (by rw [← g 2 (by decide)]; exact a2)
      (by rw [← g 3 (by decide)]; exact a3.frame es) (by rw [← g 4 (by decide)]; exact a4) (by rw [← g 6 (by decide)]; exact a6) x y z
      (by rw [← g 5 (by decide)]; exact k.frame e es)

theorem KidsR.frame {h h' : Buf} {f : UInt64} {ns : List ParRun.RN} {ids : List UInt64} (r : KidsR h f ns ids)
    (e : RecAgree h h' ids) (es : ShTabAgree h h') : KidsR h' f ns ids := by
  match r with
  | .nil => exact .nil
  | .cons (i1 := i1) nr k =>
    have hm : f ∈ i1 := nr.mem
    have g : ∀ k : UInt64, k.toNat < 8 → fld h' f k = fld h f k := e f (List.mem_append_left _ hm)
    exact .cons (nr.frame (fun k hk => g k (by omega)) (fun v hv => e v (List.mem_append_left _ (List.mem_of_mem_tail hv))) es)
      (by rw [g 7 (by decide)]; exact k.frame (fun v hv => e v (List.mem_append_right _ hv)) es)
end

/-! ## the arena and the operand stack -/
/-- operand stack position k (0 = bottom) -/
def opAt (h : Buf) (k : Nat) : UInt64 := bget h (d3 + k.toUInt64)

open ParRun in
/-- record u ↔ arena[u] (records read: `I u`, nodup, all allocated); operand k (TOP = 0) ↔ vals[k] -/
def ArenaRep (h : Buf) (arena vals : List RN) : Prop :=
  (bget h 9).toNat = arena.length ∧ arena.length ≤ 16384 ∧ (bget h 8).toNat = vals.length ∧ vals.length ≤ 4096 ∧
  ∃ I : Nat → List UInt64,
    (∀ u (hu : u < arena.length), RNRep h u.toUInt64 (arena[u]'hu) (I u) ∧ (I u).Nodup ∧ ∀ v ∈ I u, v.toNat < arena.length) ∧
    (∀ k (hk : k < vals.length), let r := opAt h (vals.length - 1 - k)
      ∃ hr : r.toNat < arena.length, arena[r.toNat]'hr = vals[k]'hk ∧ ∀ u, u < arena.length → r ∈ I u → r.toNat = u) ∧
    (∀ k1 k2, k1 < vals.length → k2 < vals.length → opAt h k1 = opAt h k2 → k1 = k2) ∧
    (∀ k1 k2, k1 < vals.length → k2 < vals.length → k1 ≠ k2 → ∀ v, v ∈ I (opAt h k1).toNat → v ∉ I (opAt h k2).toNat)

end ParInv
