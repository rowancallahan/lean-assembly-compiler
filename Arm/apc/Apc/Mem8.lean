/- 8-byte memory on DeepMind's `Arm64.Memory`: `read64`/`write64` against our byte view `memV` (`Mem.wr`, `le8`),
permissions kept by stores, and the one-word laws for `ldr`/`str` (64-bit, unsigned immediate offset). -/
import Apc.Mach
import Nano.Base.Compiler.Frame
namespace Proven.Apc
open Proven Proven.Mach

/-- our byte view of a memory (`memV s = memM s.mem`) -/
def memM (m : Arm64.Memory) : Mem := fun a =>
  if a < 2 ^ 64 ∧ m.canRead (BitVec.ofNat 64 a) 1 = true then some (m.read8 (BitVec.ofNat 64 a)) else none
theorem memV_eq (s : Arm64.State) : memV s = memM s.mem := rfl

theorem ofNat_add' (a : BitVec 64) (i : Nat) : BitVec.ofNat 64 (a.toNat + i) = a + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq; simp

theorem bytes8 (x : BitVec 64) :
    x.extractLsb' 56 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 32 8 ++ x.extractLsb' 24 8 ++
      x.extractLsb' 16 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 0 8 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have hi' : i < 64 := hi
  repeat' split
  all_goals first
    | (rename_i hh; simp only [decide_eq_true hh, Bool.true_and]; congr 1; omega)
    | (simp only [decide_eq_true (show i - 8 - 8 - 8 - 8 - 8 - 8 - 8 < 8 by omega), Bool.true_and]; congr 1; omega)

theorem allPerm_of (m : Arm64.Memory) (p : Option Arm64.Perm → Bool) : ∀ (n : Nat) (a : BitVec 64),
    (∀ i, i < n → m.allPerm p (a + BitVec.ofNat 64 i) 1 = true) → m.allPerm p a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [Arm64.Memory.allPerm, Bool.and_true, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    simp only [Arm64.Memory.allPerm, Bool.and_eq_true]
    refine ⟨h0, allPerm_of m p n (a + 1#64) fun i hi => ?_⟩
    have := h (i + 1) (by omega)
    rwa [show a + BitVec.ofNat 64 (i + 1) = a + 1#64 + BitVec.ofNat 64 i by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this
theorem allNoLazy_of (m : Arm64.Memory) : ∀ (n : Nat) (a : BitVec 64),
    (∀ i, i < n → m.allNoLazyFree (a + BitVec.ofNat 64 i) 1 = true) → m.allNoLazyFree a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [Arm64.Memory.allNoLazyFree, Bool.and_true, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    simp only [Arm64.Memory.allNoLazyFree, Bool.and_eq_true]
    refine ⟨h0, allNoLazy_of m n (a + 1#64) fun i hi => ?_⟩
    have := h (i + 1) (by omega)
    rwa [show a + BitVec.ofNat 64 (i + 1) = a + 1#64 + BitVec.ofNat 64 i by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this
theorem canRead_of (m : Arm64.Memory) (n : Nat) (a : BitVec 64)
    (h : ∀ i, i < n → m.canRead (a + BitVec.ofNat 64 i) 1 = true) : m.canRead a n = true := by
  simp only [Arm64.Memory.canRead, Bool.and_eq_true] at h ⊢
  exact ⟨allPerm_of m _ n a fun i hi => (h i hi).1, allNoLazy_of m n a fun i hi => (h i hi).2⟩
theorem canWrite_of (m : Arm64.Memory) (n : Nat) (a : BitVec 64)
    (h : ∀ i, i < n → m.canWrite (a + BitVec.ofNat 64 i) 1 = true) : m.canWrite a n = true :=
  allPerm_of m _ n a h

/-- an executable byte is never writable -/
theorem exec_ne_write {m : Arm64.Memory} {a b : BitVec 64} (hx : m.canExec b 1 = true) (hw : m.canWrite a 1 = true) :
    b ≠ a := by
  rintro rfl
  simp only [Arm64.Memory.canExec, Arm64.Memory.canWrite, Arm64.Memory.allPerm, Bool.and_true,
    Bool.and_eq_true, Bool.not_eq_true'] at hx hw
  rw [hx] at hw; exact absurd hw.2 (by decide)

/-! ## what a store keeps -/
structure Pres (m m' : Arm64.Memory) : Prop where
  ex : ∀ b, m'.canExec b 1 = m.canExec b 1
  rd : ∀ b, m.canRead b 1 = true → m'.canRead b 1 = true
  wr : ∀ b, m'.canWrite b 1 = m.canWrite b 1

theorem Pres.refl (m : Arm64.Memory) : Pres m m := ⟨fun _ => rfl, fun _ h => h, fun _ => rfl⟩
theorem Pres.trans {m₁ m₂ m₃ : Arm64.Memory} (h₁ : Pres m₁ m₂) (h₂ : Pres m₂ m₃) : Pres m₁ m₃ :=
  ⟨fun b => (h₂.ex b).trans (h₁.ex b), fun b h => h₂.rd b (h₁.rd b h), fun b => (h₂.wr b).trans (h₁.wr b)⟩
theorem pres_w8 (m : Arm64.Memory) (a : BitVec 64) (v : BitVec 8) : Pres m (m.write8 a v) :=
  ⟨fun b => canExec_w8 m a b v, fun b h => canRead_w8 m a b v h, fun b => canWrite_w8 m a b v⟩

theorem okS_pres {L : Lay} {s s' : Arm64.State} (h : okS L s) (hs : s'.status = s.status) (hp : Pres s.mem s'.mem) :
    okS L s' := by
  refine ⟨hs.trans h.1, fun x h1 h2 => ?_, fun x h1 h2 => ⟨hp.rd _ (h.2.2 x h1 h2).1, ?_⟩⟩
  · rw [hp.ex]; exact h.2.1 x h1 h2
  · rw [hp.wr]; exact (h.2.2 x h1 h2).2

theorem memM_w8 (m : Arm64.Memory) (a : BitVec 64) (v : BitVec 8) (hr : m.canRead a 1 = true) :
    memM (m.write8 a v) = (memM m).upd a.toNat v := by
  funext x
  unfold memM Mem.upd
  by_cases hx : x = a.toNat
  · subst hx
    have : BitVec.ofNat 64 a.toNat = a := by simp
    simp [this, canRead_w8 _ _ _ _ hr, read_w8, a.isLt]
  · have hne : x < 2 ^ 64 → BitVec.ofNat 64 x ≠ a := fun hlt e => hx (by rw [← e]; simp; omega)
    by_cases hlt : x < 2 ^ 64
    · simp [hx, hlt, canRead_w8_ne _ _ _ _ (hne hlt), read_w8, hne hlt]
    · simp [hx, hlt]

theorem memM_w8_ne (m : Arm64.Memory) (a : BitVec 64) (v : BitVec 8) (x : Nat) (hx : x < 2 ^ 64 → BitVec.ofNat 64 x ≠ a) :
    memM (m.write8 a v) x = memM m x := by
  unfold memM
  by_cases hlt : x < 2 ^ 64
  · simp [hlt, canRead_w8_ne _ _ _ _ (hx hlt), read_w8, hx hlt]
  · simp [hlt]

/-- writing bytes: permissions kept, our view is `Mem.wr` -/
theorem writeBytes_ok : ∀ (l : List (BitVec 8)) (m : Arm64.Memory) (a : BitVec 64), a.toNat + l.length < 2 ^ 64 →
    (∀ i, i < l.length → m.canRead (a + BitVec.ofNat 64 i) 1 = true) →
    Pres m (m.writeBytes a l) ∧ memM (m.writeBytes a l) = Mem.wr (memM m) a.toNat l
  | [], m, a, _, _ => ⟨Pres.refl m, rfl⟩
  | b :: l, m, a, hl, hr => by
    simp only [List.length_cons] at hl hr
    have e1 : (a + 1#64).toNat = a.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    have h0 := hr 0 (by omega); simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    obtain ⟨p, q⟩ := writeBytes_ok l (m.write8 a b) (a + 1#64) (by omega) fun i hi => by
      have := hr (i + 1) (by omega)
      rw [show a + BitVec.ofNat 64 (i + 1) = a + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this
      exact canRead_w8 _ _ _ _ this
    refine ⟨(pres_w8 m a b).trans p, ?_⟩
    show memM ((m.write8 a b).writeBytes (a + 1#64) l) = Mem.wr ((memM m).upd a.toNat b) (a.toNat + 1) l
    rw [q, e1, memM_w8 _ _ _ h0]

theorem write64_eq (m : Arm64.Memory) (a v : BitVec 64) : m.write64 a v = m.writeBytes a (le8 v) := by
  rw [show le8 v = [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8, v.extractLsb' 32 8,
    v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8] from rfl]
  simp only [Arm64.Memory.write64, Arm64.Memory.writeBytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]

theorem bytes_at {M : Mem} {a : Nat} {l : List (BitVec 8)} (h : bytes M a l.length = l.map some) {i : Nat}
    (hi : i < l.length) : M (a + i) = some l[i] := get_of_bytes h hi

/-- the 8 bytes our view shows at `a` are those of `read64 a` -/
theorem read64_of {m : Arm64.Memory} {a : BitVec 64} {v : BitVec 64} (h : bytes (memM m) a.toNat 8 = (le8 v).map some) :
    m.canRead a 8 = true ∧ m.read64 a = v := by
  have hb : ∀ i, i < 8 → m.canRead (a + BitVec.ofNat 64 i) 1 = true ∧
      m.read8 (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := fun i hi => by
    have := bytes_at (l := le8 v) (by rw [length_le8]; exact h) (i := i) (by rw [length_le8]; exact hi)
    unfold memM at this
    rw [ofNat_add'] at this
    split at this
    · rename_i hc; refine ⟨hc.2, ?_⟩
      have := Option.some.inj this; rw [this]; simp [le8]
    · exact absurd this (by simp)
  refine ⟨canRead_of m 8 a fun i hi => (hb i hi).1, ?_⟩
  unfold Arm64.Memory.read64
  simp only [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, (hb 0 (by omega)).2, (hb 1 (by omega)).2,
    (hb 2 (by omega)).2, (hb 3 (by omega)).2, (hb 4 (by omega)).2, (hb 5 (by omega)).2, (hb 6 (by omega)).2,
    (hb 7 (by omega)).2]
  exact bytes8 v

/-- an 8-byte store into the data range: permissions kept, our view gets `le8 v` -/
theorem write64_ok {L : Lay} {s : Arm64.State} (hok : okS L s) {a : BitVec 64} (ha : a.toNat + 8 < 2 ^ 64)
    (hw : ∀ i, i < 8 → L.dLo ≤ a.toNat + i ∧ a.toNat + i < L.dHi) (v : BitVec 64) :
    s.mem.canWrite a 8 = true ∧ Pres s.mem (s.mem.write64 a v) ∧
      memM (s.mem.write64 a v) = Mem.wr (memM s.mem) a.toNat (le8 v) := by
  have hb : ∀ i, i < 8 → s.mem.canRead (a + BitVec.ofNat 64 i) 1 = true ∧ s.mem.canWrite (a + BitVec.ofNat 64 i) 1 = true :=
    fun i hi => by rw [← ofNat_add']; exact hok.2.2 _ (hw i hi).1 (hw i hi).2
  refine ⟨canWrite_of _ 8 a fun i hi => (hb i hi).2, ?_⟩
  rw [write64_eq]
  exact writeBytes_ok _ _ _ (by rw [length_le8]; exact ha) fun i hi => (hb i (by rw [length_le8] at hi; exact hi)).1

/-- stores never change the bytes of executable addresses: the code stays -/
theorem instrAt_pres {L : Lay} {s s' : Arm64.State} (hok : okS L s)
    (hm : ∀ x, L.cLo ≤ x → x < L.cHi → memM s'.mem x = memM s.mem x) {q : BitVec 64} {w : BitVec 32}
    (hi : instrAt L s q w) : instrAt L s' q w :=
  ⟨hi.1, fun j hj => by rw [memV_eq, hm _ (by have := hi.1; omega) (by have := hi.1; omega)]; exact hi.2 j hj⟩

theorem w64_code {L : Lay} {s : Arm64.State} (hok : okS L s) {a : BitVec 64}
    (hw : ∀ i, i < 8 → s.mem.canWrite (a + BitVec.ofNat 64 i) 1 = true) (v : BitVec 64) :
    ∀ x, L.cLo ≤ x → x < L.cHi → memM (s.mem.write64 a v) x = memM s.mem x := by
  intro x h1 h2
  have hlt : x < 2 ^ 64 := by have := L.hc; omega
  have hx : s.mem.canExec (BitVec.ofNat 64 x) 1 = true := hok.2.1 x h1 h2
  have ne : ∀ i, i < 8 → BitVec.ofNat 64 x ≠ a + BitVec.ofNat 64 i := fun i hi => exec_ne_write hx (hw i hi)
  -- every intermediate memory keeps `x` executable and its byte
  rw [write64_eq]
  suffices ∀ (l : List (BitVec 8)) (m : Arm64.Memory) (k : Nat), k + l.length ≤ 8 →
      memM (m.writeBytes (a + BitVec.ofNat 64 k) l) x = memM m x from by
    have := this (le8 v) s.mem 0 (by simp [length_le8]); simpa using this
  intro l
  induction l with
  | nil => intro m k _; rfl
  | cons b l ih =>
    intro m k hk
    simp only [List.length_cons] at hk
    show memM ((m.write8 (a + BitVec.ofNat 64 k) b).writeBytes (a + BitVec.ofNat 64 k + 1#64) l) x = _
    rw [show a + BitVec.ofNat 64 k + 1#64 = a + BitVec.ofNat 64 (k + 1) by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp, ih _ _ (by omega)]
    exact memM_w8_ne _ _ _ _ fun _ => ne k (by omega)

end Proven.Apc
