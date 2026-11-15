/- Results with several components (tuples, structures) as bytes, once and for all (source level).

The components are in variables (`AllEnv`); `storeC` writes them one after another into the output block (heap
block 1), each as `k` little-endian bytes (`k ≤ 8`): the field-after-field layout of `Bytes (α × β)` in
`Spec/Encode.lean`, with fixed-width fields (`Nat`: 8 bytes, mod `2 ^ 64`). -/
import Riscv.Frontx.Rep
import Spec.Encode

namespace Proven.Frontx
open Proven

/-- `n + 1` bytes of variable `v`, shifted right by `s`, to the output block from index `o` -/
def storeW (v o s : Nat) : Nat → BStmt
  | 0 => .store 1 (.const (BitVec.ofNat 64 o)) (.bin .lshr (.var v) (.const (BitVec.ofNat 64 s)))
  | n + 1 => .seq (storeW v o s 0) (storeW v (o + 1) (s + 8) n)

/-- the components `(variable, bytes)` one after another from index `o` -/
def storeC : List (Nat × Nat) → Nat → BStmt
  | [], _ => .assign 4 (.var 4)
  | [(v, k)], o => storeW v o 0 (k - 1)
  | (v, k) :: cs, o => .seq (storeW v o 0 (k - 1)) (storeC cs (o + k))

/-- the bytes of the components of `b` (each `(variable, bytes, value)`) -/
def encC {β : Type} (comps : List (Nat × Nat × (β → BitVec 64))) (b : β) : List UInt8 :=
  (comps.map fun c => leN c.2.1 (c.2.2 b).toNat).flatten

theorem wrO_single (O : List (BitVec 8)) (o : Nat) (y : UInt8) (h : o < O.length) :
    wrO O o [y] = O.set o y.toBitVec := by
  rw [wrO_cons _ _ _ _ h, wrO_nil]

theorem wrO_append (O : List (BitVec 8)) (o : Nat) (L M : List UInt8) (h : o + L.length ≤ O.length) :
    wrO O o (L ++ M) = wrO (wrO O o L) (o + L.length) M := by
  have hl : (O.take o ++ L.map (·.toBitVec)).length = o + L.length := by simp; omega
  unfold wrO
  rw [List.take_left' hl]
  have e : o + L.length + M.length = (O.take o ++ L.map (·.toBitVec)).length + M.length := by rw [hl]
  rw [e, List.drop_append, List.drop_drop, hl]
  simp only [List.map_append, List.append_assoc, List.length_append, Nat.add_assoc]
  rw [List.drop_eq_nil_of_le (as := List.take o O ++ _) (by rw [hl]; omega), List.nil_append,
    show o + (L.length + (o + (L.length + M.length) - (o + L.length))) = o + (L.length + M.length) by omega]

theorem wrO_length (O : List (BitVec 8)) (o : Nat) (L : List UInt8) (h : o + L.length ≤ O.length) :
    (wrO O o L).length = O.length := by
  simp [wrO]; omega

theorem u8' (k : Nat) : (UInt8.ofNat (k % 256)).toBitVec = BitVec.ofNat 8 k := by
  apply BitVec.eq_of_toNat_eq; simp

theorem byte_shr (w : BitVec 64) (s : Nat) (hs : s < 64) :
    (Op.eval .lshr w (BitVec.ofNat 64 s)).setWidth 8 = (UInt8.ofNat (w.toNat / 2 ^ s % 256)).toBitVec := by
  rw [u8']
  apply BitVec.eq_of_toNat_eq
  have : s % 2 ^ 64 % 64 = s := by omega
  simp only [Op.eval, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, this,
    Nat.shiftRight_eq_div_pow]

theorem storeW_exec (v : Nat) (w : BitVec 64) (X : List (BitVec 8)) : ∀ (n o s : Nat) (O : List (BitVec 8))
    (env : BEnv), env v = w → o + n + 1 ≤ O.length → O.length < 2 ^ 64 → s + 8 * n < 64 →
    BExec (storeW v o s n) ⟨env, [X, O]⟩ ⟨env, [X, wrO O o (leN (n + 1) (w.toNat / 2 ^ s))]⟩
  | 0, o, s, O, env, hv, hl, hO, hs => by
    have h := BExec.store' (b := 1) (i := .const (BitVec.ofNat 64 o))
      (e := .bin .lshr (.var v) (.const (BitVec.ofNat 64 s))) (σ := ⟨env, [X, O]⟩) (B := O) (j := o) rfl
      (by simp [BExp.denote]; omega) (by omega)
    simp only [BExp.denote, hv, byte_shr w s (by omega), List.set_cons_succ, List.set_cons_zero] at h
    rw [leN, leN, wrO_single _ _ _ (by omega), storeW]
    exact h
  | n + 1, o, s, O, env, hv, hl, hO, hs => by
    have h1 := storeW_exec v w X 0 o s O env hv (by omega) hO (by omega)
    have h2 := storeW_exec v w X n (o + 1) (s + 8) (wrO O o (leN 1 (w.toNat / 2 ^ s))) env hv
      (by rw [wrO_length _ _ _ (by simp [leN_length]; omega)]; omega)
      (by rw [wrO_length _ _ _ (by simp [leN_length]; omega)]; exact hO) (by omega)
    have e : leN (n + 1 + 1) (w.toNat / 2 ^ s) = leN 1 (w.toNat / 2 ^ s) ++ leN (n + 1) (w.toNat / 2 ^ (s + 8)) := by
      rw [leN, leN, leN, Nat.pow_add, ← Nat.div_div_eq_div_mul]; rfl
    rw [e, wrO_append _ _ _ _ (by rw [leN_length]; omega), show (leN 1 (w.toNat / 2 ^ s)).length = 1 from leN_length 1 _]
    rw [storeW]
    exact .seq h1 h2

theorem encC_cons {β : Type} (v k : Nat) (r : β → BitVec 64) (cs : List (Nat × Nat × (β → BitVec 64))) (b : β) :
    encC ((v, k, r) :: cs) b = leN k (r b).toNat ++ encC cs b := by
  simp [encC]

theorem storeC_exec {β : Type} (b : β) (X : List (BitVec 8)) (env : BEnv) :
    ∀ (comps : List (Nat × Nat × (β → BitVec 64))) (o : Nat) (O : List (BitVec 8)),
    AllEnv env (comps.map fun c => (c.1, c.2.2 b)) → (∀ c ∈ comps, 1 ≤ c.2.1 ∧ c.2.1 ≤ 8) →
    o + (encC comps b).length ≤ O.length → O.length < 2 ^ 64 →
    BExec (storeC (comps.map fun c => (c.1, c.2.1)) o) ⟨env, [X, O]⟩ ⟨env, [X, wrO O o (encC comps b)]⟩
  | [], o, O, ha, hk, hl, hO => by
    have := BExec.assign' (v := 4) (e := .var 4) (σ := ⟨env, [X, O]⟩) rfl
    simp only [BExp.denote] at this
    rw [show env.set 4 (env 4) = env from funext fun j => by simp [BEnv.set]; intro h; rw [h]] at this
    simpa [encC, wrO_nil] using this
  | [(v, k, r)], o, O, ha, hk, hl, hO => by
    have hk' : 1 ≤ k ∧ k ≤ 8 := hk _ (List.mem_singleton_self _)
    have hv : env v = r b := ha _ (List.mem_singleton_self _)
    have hl' : o + k ≤ O.length := by simpa [encC, leN_length] using hl
    have := storeW_exec v (r b) X (k - 1) o 0 O env hv (by omega) hO (by omega)
    rw [show k - 1 + 1 = k by omega, Nat.pow_zero, Nat.div_one] at this
    simpa [encC] using this
  | (v, k, r) :: c2 :: cs, o, O, ha, hk, hl, hO => by
    have hk' : 1 ≤ k ∧ k ≤ 8 := hk _ (List.mem_cons_self ..)
    have hv : env v = r b := ha _ (List.mem_cons_self ..)
    rw [encC_cons] at hl ⊢
    have hl' : o + k + (encC (c2 :: cs) b).length ≤ O.length := by
      simp only [List.length_append, leN_length] at hl; omega
    have h1 := storeW_exec v (r b) X (k - 1) o 0 O env hv (by omega) hO (by omega)
    rw [show k - 1 + 1 = k by omega, Nat.pow_zero, Nat.div_one] at h1
    have hw : (wrO O o (leN k (r b).toNat)).length = O.length := wrO_length _ _ _ (by rw [leN_length]; omega)
    have h2 := storeC_exec b X env (c2 :: cs) (o + k) (wrO O o (leN k (r b).toNat))
      (fun p hp => ha p (List.mem_cons_of_mem _ hp)) (fun c hc => hk c (List.mem_cons_of_mem _ hc))
      (by rw [hw]; exact hl') (by rw [hw]; exact hO)
    rw [wrO_append _ _ _ _ (by rw [leN_length]; omega), leN_length]
    exact .seq h1 h2

/-- a run on the heap `H` is a run on `H ++ X` (more blocks behind) -/
theorem exec_frame {p : BStmt} {σ σ' : BState} (h : BExec p σ σ') (X : Heap) :
    BExec p ⟨σ.env, σ.heap ++ X⟩ ⟨σ'.env, σ'.heap ++ X⟩ := by
  induction h with
  | @assign v e σ => exact .assign
  | mop => exact .mop
  | @load v b i σ hb hi =>
    have hb' : b < (σ.heap ++ X).length := by rw [List.length_append]; omega
    have hg : (σ.heap ++ X)[b] = σ.heap[b] := List.getElem_append_left hb
    have := BExec.load (v := v) (i := i) (σ := ⟨σ.env, σ.heap ++ X⟩) hb' (by show _ < _; rw [hg]; exact hi)
    simp only [hg] at this; exact this
  | @store b i e σ hb hi =>
    have hb' : b < (σ.heap ++ X).length := by rw [List.length_append]; omega
    have hg : (σ.heap ++ X)[b] = σ.heap[b] := List.getElem_append_left hb
    have := BExec.store (e := e) (i := i) (σ := ⟨σ.env, σ.heap ++ X⟩) hb' (by show _ < _; rw [hg]; exact hi)
    simp only [hg, List.set_append_left _ _ hb] at this; exact this
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | loopF hc => exact .loopF hc
  | loopT hc _ _ ih1 ih2 => exact .loopT hc ih1 ih2

/-- **the entry point of a function with several result components**: the program, then the stores -/
theorem entry_bytes {β : Type} {p : BStmt} (comps : List (Nat × Nat × (β → BitVec 64))) (b : β) {env : BEnv}
    {X O : List (BitVec 8)}
    (hex : ∃ σ', BExec p ⟨env, [X]⟩ σ' ∧ σ'.heap = [X] ∧ AllEnv σ'.env (comps.map fun c => (c.1, c.2.2 b)))
    (hk : (comps.map (·.2.1)).all (fun k => 1 ≤ k && k ≤ 8) = true) (hcap : (encC comps b).length ≤ O.length)
    (hO : O.length < 2 ^ 64) :
    ∃ σ', BExec (.seq p (storeC (comps.map fun c => (c.1, c.2.1)) 0)) ⟨env, [X, O]⟩ σ' ∧
      σ'.heap = [X, wrO O 0 (encC comps b)] := by
  have hk : ∀ c ∈ comps, 1 ≤ c.2.1 ∧ c.2.1 ≤ 8 := fun c hc => by
    have := List.all_eq_true.1 hk c.2.1 (List.mem_map.2 ⟨c, hc, rfl⟩)
    simpa using this
  obtain ⟨σ', hx, hh, ha⟩ := hex
  have hx' := exec_frame hx [O]
  simp only [hh, List.cons_append, List.nil_append] at hx'
  exact ⟨_, .seq hx' (storeC_exec b X σ'.env comps 0 O ha hk (by omega) hO), rfl⟩

/-- the result variable and the extra ones, as one list -/
theorem allEnv_res {P : BState → Prop} {H : Heap} {r : BitVec 64} {rs : List (Nat × BitVec 64)}
    (h : ∃ σ', P σ' ∧ σ'.env 4 = r ∧ σ'.heap = H ∧ AllEnv σ'.env rs) :
    ∃ σ', P σ' ∧ σ'.heap = H ∧ AllEnv σ'.env ((4, r) :: rs) :=
  h.imp fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h3, allEnv_cons h2 h4⟩

end Proven.Frontx
