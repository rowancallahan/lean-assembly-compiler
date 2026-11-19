/- Nano/V2Self/Proof/ParInvRep: Layer 3 (machine ↔ spec) representation relations that do not depend on the task `Frame`
(see Testing/notes/NANO_V2_PARINV_DESIGN.md).  Box C owns this file; box D builds handler lemmas on it.
* `TokAt h p toks`  : the token region from cursor `p` decodes to the spec tokens `toks` (numerals: 8 byte words, each < 256).
* `NodeRep h u nd ids` / `Kids h f n cs ids` : the arena subtree at node `u` represents the SPEC node `nd`; `ids` = its node ids.
  The child chain (field 5 = first, field 6 = count, field 7 = next) is read exactly as the flattener v142/v143 reads it:
  INPUT LOCALS (tag 2, payload2 = 0) are skipped (spec `dropInp`), and a PAIR whose visible children are `[c]` is `c` (`mkPairFlat`).
* `pendM` : the machine's pending bit (field 4) as a function of the spec node: CONTINUE, and `if`/`let` propagate it from
  then/else resp. the body; every other node has 0.  (`Nd.pendM` is what box B's `binLoop` / `pairBuild` must test.)
* `TyRep h res u ty` : the shape field (3) and tag represent the spec type (`lit` ⇒ shape 1, `inp` = input local, `bot` ⇒ shape = res,
  the current def's result shape code); a const node always has type `lit`.
* `OpsRep h res vals` : operand stack (depth h[8], ids at d3 + k) ↔ `vals` (HEAD = TOP), disjoint subtrees below h[9]. -/
import Nano.V2Self.Proof.ParRep
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

/-! ## arena nodes -/
/-- field `k` of node `u` (record of 8 words at d5 + 8u) -/
def fld (h : Buf) (u : UInt64) (k : UInt64) : UInt64 := bget h (d5 + 8 * u + k)

/-- the width-0 input local (tag 2, payload2 0): skipped in child chains, as v143 does -/
def InpLoc (h : Buf) (u : UInt64) : Prop := fld h u 0 = 2 ∧ fld h u 2 = 0

/-- the machine's pending bit as a function of the spec node -/
def _root_.ParSpec.Nd.pendM : Nd → Bool
  | .cont _ => true
  | .ite _ _ _ t e => t.pendM || e.pendM
  | .letE _ _ _ b => b.pendM
  | _ => false

mutual
inductive NodeRep (h : Buf) : UInt64 → Nd → List UInt64 → Prop
  | const {u v : UInt64} : fld h u 0 = 1 → fld h u 1 = v → fld h u 6 = 0 → NodeRep h u (.const v) [u]
  | loc {u : UInt64} {s w : Nat} : fld h u 0 = 2 → fld h u 1 = s.toUInt64 → fld h u 2 = w.toUInt64 → fld h u 6 = 0 →
      s < 2 ^ 32 → w < 2 ^ 32 → NodeRep h u (.loc s w) [u]
  | bin {u : UInt64} {op : Nat} {a b : Nd} {ids : List UInt64} : fld h u 0 = 3 → fld h u 1 = op.toUInt64 → fld h u 6 = 2 → op < 2 ^ 32 →
      Kids h (fld h u 5) 2 [a, b] ids → NodeRep h u (.bin op a b) (u :: ids)
  | ite {u : UInt64} {c : Nat} {a b t e : Nd} {ids : List UInt64} : fld h u 0 = 4 → fld h u 1 = c.toUInt64 → fld h u 6 = 4 → c < 2 ^ 32 →
      Kids h (fld h u 5) 4 [a, b, t, e] ids → NodeRep h u (.ite c a b t e) (u :: ids)
  | letE {u : UInt64} {s w : Nat} {v b : Nd} {ids : List UInt64} : fld h u 0 = 5 → fld h u 1 = s.toUInt64 → fld h u 2 = w.toUInt64 →
      fld h u 6 = 2 → s < 2 ^ 32 → w < 2 ^ 32 → Kids h (fld h u 5) 2 [v, b] ids → NodeRep h u (.letE s w v b) (u :: ids)
  | pair {u : UInt64} {cs : List Nd} {ids : List UInt64} : fld h u 0 = 6 → cs ≠ [] →
      Kids h (fld h u 5) (fld h u 6).toNat cs ids → NodeRep h u (mkPairFlat cs) (u :: ids)
  | call {u : UInt64} {i : Nat} {cs : List Nd} {ids : List UInt64} : fld h u 0 = 8 → fld h u 1 = i.toUInt64 → i < 512 →
      Kids h (fld h u 5) (fld h u 6).toNat cs ids → NodeRep h u (.call i cs) (u :: ids)
  | prim {u : UInt64} {p : Nat} {cs : List Nd} {ids : List UInt64} : fld h u 0 = 9 → fld h u 1 = p.toUInt64 → p < 2 ^ 32 →
      Kids h (fld h u 5) (fld h u 6).toNat cs ids → NodeRep h u (.prim p cs) (u :: ids)
  | loop {u : UInt64} {z s : Nd} {ids : List UInt64} : fld h u 0 = 10 → fld h u 6 = 2 →
      Kids h (fld h u 5) 2 [z, s] ids → NodeRep h u (.loop z s) (u :: ids)
  | cont {u : UInt64} {e : Nd} {ids : List UInt64} : fld h u 0 = 11 → fld h u 6 = 1 →
      Kids h (fld h u 5) 1 [e] ids → NodeRep h u (.cont e) (u :: ids)

/-- the chain of `n` siblings starting at `f` (next = field 7) represents `cs`, input locals skipped -/
inductive Kids (h : Buf) : UInt64 → Nat → List Nd → List UInt64 → Prop
  | nil {f : UInt64} : Kids h f 0 [] []
  | skip {f : UInt64} {n : Nat} {cs : List Nd} {ids : List UInt64} : InpLoc h f →
      Kids h (fld h f 7) n cs ids → Kids h f (n + 1) cs (f :: ids)
  | cons {f : UInt64} {n : Nat} {c : Nd} {cs : List Nd} {i1 ids : List UInt64} : NodeRep h f c i1 → ¬ InpLoc h f →
      Kids h (fld h f 7) n cs ids → Kids h f (n + 1) (c :: cs) (i1 ++ ids)
end

/-- shape field / tag ↔ spec type; `res` = the current def's result shape code (the shape the machine gives a CONTINUE) -/
def TyRep (h : Buf) (res : UInt64) (u : UInt64) : Ty → Prop
  | .s s => ShapeCode h (fld h u 3) s ∧ fld h u 0 ≠ 1 ∧ ¬ InpLoc h u
  | .lit => fld h u 3 = 1 ∧ ¬ InpLoc h u
  | .inp => InpLoc h u ∧ fld h u 3 = 3
  | .bot => fld h u 3 = res ∧ fld h u 0 ≠ 1 ∧ ¬ InpLoc h u

/-- one operand: node `u` represents `(nd, ty)` with the faithful pending bit; its subtree `ids` -/
def ValRep (h : Buf) (res : UInt64) (u : UInt64) (v : Nd × Ty) (ids : List UInt64) : Prop :=
  NodeRep h u v.1 ids ∧ TyRep h res u v.2 ∧ fld h u 4 = (if v.1.pendM then 1 else 0)

/-- the operand stack (depth h[8], node ids at d3 + k, k = 0 bottom) represents `vals` (HEAD = TOP); subtrees disjoint, below h[9] -/
def OpsRep (h : Buf) (res : UInt64) (vals : List (Nd × Ty)) : Prop :=
  (bget h 8).toNat = vals.length ∧ vals.length ≤ 4096 ∧ (bget h 9).toNat ≤ 16384 ∧
  ∃ idss : List (List UInt64), idss.length = vals.length ∧ idss.flatten.Nodup ∧
    (∀ v ∈ idss.flatten, v < bget h 9) ∧
    ∀ (i : Nat) (hi : i < vals.length),
      ValRep h res (bget h (d3 + (vals.length - 1 - i).toUInt64)) (vals[i]'hi) (idss.getD i [])

/-! ## arena frame rule -/
theorem NodeRep.mem {h : Buf} {u : UInt64} {nd : Nd} {ids : List UInt64} (r : NodeRep h u nd ids) : u ∈ ids := by
  cases r <;> simp

/-- cells of the records `ids` (all 8 fields) agree -/
def RecAgree (h h' : Buf) (ids : List UInt64) : Prop := ∀ v ∈ ids, ∀ k : UInt64, k.toNat < 8 → fld h' v k = fld h v k

mutual
/-- a subtree's representation only reads its own records (the root's next field is not read) -/
theorem NodeRep.frame {h h' : Buf} {u : UInt64} {nd : Nd} {ids : List UInt64} (r : NodeRep h u nd ids)
    (e0 : ∀ k : UInt64, k.toNat < 7 → fld h' u k = fld h u k) (e : RecAgree h h' ids.tail) : NodeRep h' u nd ids := by
  have g : ∀ k : UInt64, k.toNat < 7 → fld h u k = fld h' u k := fun k hk => (e0 k hk).symm
  match r with
  | .const a b c =>
    exact .const (by rw [← g 0 (by decide)]; exact a) (by rw [← g 1 (by decide)]; exact b) (by rw [← g 6 (by decide)]; exact c)
  | .loc a b c d x y =>
    exact .loc (by rw [← g 0 (by decide)]; exact a) (by rw [← g 1 (by decide)]; exact b) (by rw [← g 2 (by decide)]; exact c)
      (by rw [← g 6 (by decide)]; exact d) x y
  | .bin a b c x k =>
    exact .bin (by rw [← g 0 (by decide)]; exact a) (by rw [← g 1 (by decide)]; exact b) (by rw [← g 6 (by decide)]; exact c) x
      (by rw [← g 5 (by decide)]; exact k.frame e)
  | .ite a b c x k =>
    exact .ite (by rw [← g 0 (by decide)]; exact a) (by rw [← g 1 (by decide)]; exact b) (by rw [← g 6 (by decide)]; exact c) x
      (by rw [← g 5 (by decide)]; exact k.frame e)
  | .letE a b c d x y k =>
    exact .letE (by rw [← g 0 (by decide)]; exact a) (by rw [← g 1 (by decide)]; exact b) (by rw [← g 2 (by decide)]; exact c)
      (by rw [← g 6 (by decide)]; exact d) x y (by rw [← g 5 (by decide)]; exact k.frame e)
  | .pair a x k =>
    exact .pair (by rw [← g 0 (by decide)]; exact a) x (by rw [← g 5 (by decide), ← g 6 (by decide)]; exact k.frame e)
  | .call a b x k =>
    exact .call (by rw [← g 0 (by decide)]; exact a) (by rw [← g 1 (by decide)]; exact b) x
      (by rw [← g 5 (by decide), ← g 6 (by decide)]; exact k.frame e)
  | .prim a b x k =>
    exact .prim (by rw [← g 0 (by decide)]; exact a) (by rw [← g 1 (by decide)]; exact b) x
      (by rw [← g 5 (by decide), ← g 6 (by decide)]; exact k.frame e)
  | .loop a c k =>
    exact .loop (by rw [← g 0 (by decide)]; exact a) (by rw [← g 6 (by decide)]; exact c) (by rw [← g 5 (by decide)]; exact k.frame e)
  | .cont a c k =>
    exact .cont (by rw [← g 0 (by decide)]; exact a) (by rw [← g 6 (by decide)]; exact c) (by rw [← g 5 (by decide)]; exact k.frame e)

theorem Kids.frame {h h' : Buf} {f : UInt64} {n : Nat} {cs : List Nd} {ids : List UInt64} (r : Kids h f n cs ids)
    (e : RecAgree h h' ids) : Kids h' f n cs ids := by
  match r with
  | .nil =>
    exact .nil
  | .skip ⟨a, b⟩ k =>
    have g : ∀ k : UInt64, k.toNat < 8 → fld h' f k = fld h f k := e f (by simp)
    exact .skip ⟨by rw [g 0 (by decide)]; exact a, by rw [g 2 (by decide)]; exact b⟩
      (by rw [g 7 (by decide)]; exact k.frame (fun v hv => e v (by simp [hv])))
  | .cons (i1 := i1) (ids := ids2) nr ni k =>
    have hm : f ∈ i1 := nr.mem
    have g : ∀ k : UInt64, k.toNat < 8 → fld h' f k = fld h f k := e f (List.mem_append_left _ hm)
    refine .cons (nr.frame (fun k hk => g k (by omega)) (fun v hv => e v (List.mem_append_left _ (List.mem_of_mem_tail hv))))
      (fun ⟨a, b⟩ => ni ⟨by rw [← g 0 (by decide)]; exact a, by rw [← g 2 (by decide)]; exact b⟩)
      (by rw [g 7 (by decide)]; exact k.frame (fun v hv => e v (List.mem_append_right _ hv)))
end

end ParInv
