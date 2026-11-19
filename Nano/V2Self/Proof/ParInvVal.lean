/- Nano/V2Self/Proof/ParInvVal: the VALIDATION loops of Par1 at cell level (parser lead): `v205` (count the input-local children of a
sibling chain), `v210` (argument i is the input local iff parameter i is the first List parameter) and the arena scan `v209`.
Independent of the representation relations: a sibling chain is given by its id list (`Links`), parameter codes by a list of cells.
* `v205_eq` : `v205 N h f c m = m + cntC h us` for the chain `us` from `f`;
* `v210_eq` : `v210 N h f s1 i c g = imC ws g (us.map (inpC h))` for the codes `ws` at `d7 + 4096 + s1 + i …`;
* `v209_eq` : `v209 N h u = 1` iff every node `j ∈ [u, h[9])` passes the per-node check `nodeC h j` (the body of `v209`, verbatim). -/
import Nano.V2Self.Proof.ParInv
namespace ParInv
open C BufL

/-- the machine's "is the input local" test of node `u` (tag 2, payload 2 = 0), as the 0/1 word it computes -/
def inpC (h : Buf) (u : UInt64) : UInt64 :=
  if bget h ((d5 + 8*u) + 0) == 2 then if bget h ((d5 + 8*u) + 2) == 0 then k1 else k0 else k0

/-- `us` is the sibling chain starting at `f` (next = field 7); the last node's next field is not read -/
def Links (h : Buf) : UInt64 → List UInt64 → Prop
  | _, [] => True
  | f, u :: r => f = u ∧ Links h (bget h ((d5 + 8*u) + 7)) r

def cntC (h : Buf) : List UInt64 → UInt64
  | [] => 0
  | u :: r => inpC h u + cntC h r

theorem sub1_toNat (c : UInt64) (n : Nat) (hc : c.toNat = n + 1) : (c - 1).toNat = n := by
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

theorem ne0_of_toNat (c : UInt64) (n : Nat) (hc : c.toNat = n + 1) : (c == 0) = false := by
  have : c ≠ 0 := fun e => by subst e; simp at hc
  simpa using this

/-- **v205** counts the input locals of a chain -/
theorem v205_eq (h : Buf) : ∀ (us : List UInt64) (N : Nat) (f c m : UInt64), us.length < N → c.toNat = us.length → Links h f us →
    v205 N h f c m = m + cntC h us
  | [], N + 1, f, c, m, _, hc, _ => by
    have : c = 0 := UInt64.toNat_inj.mp (by simpa using hc)
    subst this; simp [v205, cntC]
  | u :: r, N + 1, f, c, m, hN, hc, hl => by
    obtain ⟨rfl, hl⟩ := hl
    have hc0 := ne0_of_toNat c r.length (by simpa using hc)
    simp only [v205, hc0, Bool.false_eq_true, if_false]
    rw [v205_eq h r N _ (c - 1) _ (by simp at hN; omega) (sub1_toNat c r.length (by simpa using hc)) hl]
    simp only [cntC, inpC, UInt64.add_assoc]

/-- the pure form of `v210`: parameter codes `ws`, "a List was seen" flag `g`, the arguments' input-local words `as` -/
def imC : List UInt64 → UInt64 → List UInt64 → UInt64
  | w :: ws, g, a :: as =>
    if (if w == 3 then (if g == 0 then k1 else k0) else k0) == a then imC ws (if w == 3 then k1 else g) as else 0
  | _, _, _ => 1

/-- **v210** over a chain and a block of parameter-code cells -/
theorem v210_eq (h : Buf) (s1 c : UInt64) : ∀ (us ws : List UInt64) (N : Nat) (f i g : UInt64), us.length < N →
    i.toNat + us.length = c.toNat → ws.length = us.length → Links h f us →
    (∀ j (hj : j < ws.length), bget h (d7 + 4096 + s1 + (i + j.toUInt64)) = ws[j]) →
    v210 N h f s1 i c g = imC ws g (us.map (inpC h))
  | [], ws, N + 1, f, i, g, _, hc, hw, _, _ => by
    have : i = c := UInt64.toNat_inj.mp (by simpa using hc)
    subst this
    cases ws with
    | nil => simp [v210, imC]
    | cons _ _ => simp at hw
  | u :: r, [], N + 1, f, i, g, _, _, hw, _, _ => by simp at hw
  | u :: r, w :: ws, N + 1, f, i, g, hN, hc, hw, hl, hcell => by
    obtain ⟨rfl, hl⟩ := hl
    have hic : (i == c) = false := by
      have : i ≠ c := fun e => by subst e; simp at hc
      simpa using this
    have hw0 : bget h (d7 + 4096 + s1 + i) = w := by
      have := hcell 0 (by simp)
      simpa using this
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      have := c.toNat_lt
      rw [UInt64.toNat_add]; simp at hc ⊢; omega
    have ih := v210_eq h s1 c r ws N (bget h ((d5 + 8*f) + 7)) (i + 1) (if w == 3 then k1 else g) (by simp at hN; omega)
      (by rw [hi1]; simp at hc; omega) (by simpa using hw) hl
      (by
        intro j hj
        have := hcell (j + 1) (by simp; omega)
        have e : i + (j + 1).toUInt64 = i + 1 + j.toUInt64 := by
          apply UInt64.toNat_inj.mp
          simp [UInt64.toNat_add, Nat.toUInt64]; omega
        rw [e] at this
        simpa using this)
    simp only [v210, hic, Bool.false_eq_true, if_false, hw0, List.map_cons, imC, inpC]
    by_cases hq : ((if w == 3 then (if g == 0 then k1 else k0) else k0) ==
        (if bget h ((d5 + 8*f) + 0) == 2 then if bget h ((d5 + 8*f) + 2) == 0 then k1 else k0 else k0)) = true
    · rw [if_pos hq, if_pos hq]; exact ih
    · rw [if_neg hq, if_neg hq]

/-- the first per-node check of `v209` (verbatim): where an input-local child is allowed -/
def rC (h : Buf) (u : UInt64) : UInt64 :=
  let t := bget h ((d5 + 8*u) + 0);
  let a := bget h ((d5 + 8*u) + 1);
  let w := bget h ((d5 + 8*u) + 3);
  let c := bget h ((d5 + 8*u) + 6);
  let f := bget h ((d5 + 8*u) + 5);
  let m := v205 16777216 h f c 0;
  let p0 := if c == 0 then k0 else if bget h ((d5 + 8*f) + 0) == 2 then if bget h ((d5 + 8*f) + 2) == 0 then k1 else k0 else k0;
  if m == 0 then (if t == 9 then (if a < 4 then k0 else k1) else k1)
           else if t == 8 then k1
           else if t == 6 then (if w == 0 then k1 else k0)
           else if t == 9 then (if a < 4 then (if m == 1 then p0 else k0) else k0)
           else k0

/-- the second per-node check of `v209` (verbatim): CALL / CONTINUE-tuple arguments against the callee's parameter codes -/
def r2C (h : Buf) (u : UInt64) : UInt64 :=
  let t := bget h ((d5 + 8*u) + 0);
  let a := bget h ((d5 + 8*u) + 1);
  let w := bget h ((d5 + 8*u) + 3);
  let c := bget h ((d5 + 8*u) + 6);
  let f := bget h ((d5 + 8*u) + 5);
  let d := (bget h 12) - 1;
  if t == 8 then (if bget h (d7 + 8*a + 6) == c then v210 16777216 h f (bget h (d7 + 8*a + 5)) 0 c 0 else k0)
            else if t == 6 then (if w == 0 then (if bget h 12 == 0 then k0 else if bget h (d7 + 8*d + 6) == c + 1 then v210 16777216 h f (bget h (d7 + 8*d + 5) + 1) 0 c 0 else k0) else k1)
            else k1

/-- the per-node check of `v209` -/
def nodeC (h : Buf) (u : UInt64) : Bool := rC h u == 1 && r2C h u == 1

theorem v209_succ0 (n : Nat) (h : Buf) (u : UInt64) :
    v209 (n + 1) h u = if u < bget h 9 then (if rC h u == 1 then (if r2C h u == 1 then v209 n h (u + 1) else 0) else 0) else 1 := rfl

theorem v209_succ (n : Nat) (h : Buf) (u : UInt64) :
    v209 (n + 1) h u = if u < bget h 9 then (if nodeC h u then v209 n h (u + 1) else 0) else 1 := by
  rw [v209_succ0]
  unfold nodeC
  cases rC h u == 1 <;> cases r2C h u == 1 <;> rfl

/-- **v209** = every node from `u` up to the node count passes `nodeC` -/
theorem v209_eq (h : Buf) : ∀ (k N : Nat) (u : UInt64), (bget h 9).toNat - u.toNat = k → u.toNat ≤ (bget h 9).toNat → k < N →
    (v209 N h u = 1 ↔ ∀ j : Nat, u.toNat ≤ j → j < (bget h 9).toNat → nodeC h j.toUInt64 = true) ∧ (v209 N h u = 1 ∨ v209 N h u = 0)
  | 0, N + 1, u, hk, hu, _ => by
    have hlt : ¬ u < bget h 9 := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [v209_succ, if_neg hlt]
    exact ⟨⟨fun _ j h1 h2 => by omega, fun _ => rfl⟩, Or.inl rfl⟩
  | k + 1, N + 1, u, hk, hu, hN => by
    have hlt : u < bget h 9 := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hu1 : (u + 1).toNat = u.toNat + 1 := by
      have := (bget h 9).toNat_lt
      rw [UInt64.toNat_add]; simp; omega
    have ih := v209_eq h k N (u + 1) (by rw [hu1]; omega) (by rw [hu1]; omega) (by omega)
    rw [v209_succ, if_pos hlt]
    have huu : u.toNat.toUInt64 = u := by apply UInt64.toNat_inj.mp; simp [Nat.toUInt64]
    by_cases hc : nodeC h u = true
    · rw [if_pos hc]
      refine ⟨⟨fun e j h1 h2 => ?_, fun e => ih.1.mpr (fun j h1 h2 => e j (by rw [hu1] at h1; omega) h2)⟩, ih.2⟩
      by_cases hj : j = u.toNat
      · subst hj; rw [huu]; exact hc
      · exact ih.1.mp e j (by rw [hu1]; omega) h2
    · rw [if_neg hc]
      refine ⟨⟨fun e => by simp at e, fun e => ?_⟩, Or.inr rfl⟩
      exact absurd (by have := e u.toNat (Nat.le_refl _) (by omega); rwa [huu] at this) hc

end ParInv
