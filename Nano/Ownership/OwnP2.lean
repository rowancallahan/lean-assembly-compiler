/- Nano/Ownership/OwnP2: `o7` (dead), `o10`/`o9` (destinations = `OwnSpec.dest`), `o12` (= `OwnSpec.ok1`) and the
argument-check loop `o14` (= `OwnSpec.okAll`), all in mode 0 (verify). -/
import Nano.Ownership.OwnP1
namespace OwnP
open C OwnSpec

/-- the destinations of a frame (`dsrc` 0 transfer, 1 two words, 2 prim, 3 call, 4 CONTINUE) -/
def dsOf (W : WCx) (r : Fr) : Option (List Nat) :=
  if r.d = 0 then none else if r.d = 1 then some [0, 0] else if r.d = 2 then some (dsP r.a)
  else if r.d = 3 then some (W.ps.getD r.a []) else some (stD W.K W.npw)

/-- what `o9` needs of a frame -/
def Fr.ok (W : WCx) (r : Fr) : Prop := r.d ≤ 4 ∧ (r.d = 2 → r.a < 10) ∧ (r.d = 3 → r.a < W.ps.length)

theorem u_b2n_beq0 (b : Bool) : (u (b2n b) == u 0) = !b := by cases b <;> decide

theorem o7_eq {W : WCx} {s f : Buf} {A : AS} (hS : RS W s A) (hF : RF W f A) (hB : Bnd W A) {q : Nat} (hq : q < 2 ^ 40) :
    o7 s f (u q) = if q < W.ns then u (b2n (A.F.getD q false)) else 1 := by
  have h6 := (regs hS).2.2.2.2.2.1
  have hns := hB.1
  unfold o7; simp only [h6]
  by_cases h : q < W.ns
  · rw [if_pos ((u_lt (by omega) (by omega)).mpr h), if_pos h, u_add, bget_u f (by omega)]
    exact hF.2.2.2.2.2.1 q h
  · rw [if_neg (fun e => h ((u_lt (by omega) (by omega)).mp e)), if_neg h]

theorem o7_dead {W : WCx} {s f : Buf} {A : AS} (hS : RS W s A) (hF : RF W f A) (hB : Bnd W A) {q : Nat} (hq : q < 2 ^ 40) :
    (o7 s f (u q) == u 0) = !dead A.F q := by
  rw [o7_eq hS hF hB hq]
  unfold dead
  by_cases h : q < W.ns
  · rw [if_pos h, u_b2n_beq0]
    have : q < A.F.length := by rw [hF.1]; exact h
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
  · rw [if_neg h]
    show (u 1 == u 0) = _
    have : A.F.length ≤ q := by rw [hF.1]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]; decide

theorem o10_eq {p o : Nat} (hp : p < 10) (ho : o < 2 ^ 40) : o10 (u p) (u o) = u (dest (some (dsP p)) o) := by
  unfold o10 dest
  have e : ∀ k : Nat, k < 10 → (u p == u k) = decide (p = k) := fun k hk => u_beq (by omega) (by omega)
  have eo : ∀ k : Nat, k < 10 → (u o == u k) = decide (o = k) := fun k hk => u_beq (by omega) (by omega)
  have lo : (u o < u 3) = (o < 3) := propext (u_lt (by omega) (by omega))
  simp only [show (2 : UInt64) = u 2 from rfl, show (4 : UInt64) = u 4 from rfl, show (6 : UInt64) = u 6 from rfl,
    show (7 : UInt64) = u 7 from rfl, show (8 : UInt64) = u 8 from rfl, show (9 : UInt64) = u 9 from rfl,
    show (0 : UInt64) = u 0 from rfl, show (1 : UInt64) = u 1 from rfl, show (3 : UInt64) = u 3 from rfl,
    e 2 (by omega), e 4 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega),
    eo 0 (by omega), eo 1 (by omega), lo]
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9) with
    h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    rcases o with _ | _ | _ | o <;> simp [dsP] <;> omega

theorem o9_eq {W : WCx} {s f : Buf} {A : AS} (hS : RS W s A) (hF : RF W f A) (hT : RT W) (hB : Bnd W A)
    {Φ0 : List Fr} {r : Fr} (hΦ : A.Φ = Φ0 ++ [r]) (hr : r.ok W) {o : Nat} (ho : o < 2 ^ 40) :
    o9 s f W.t (u o) = u (dest (dsOf W r) o) := by
  have hb : A.Φ.length ≤ 2 ^ 30 := hB.2.2.2.2.2.1
  have hsm : r.small := hB.2.2.2.2.2.2.2.2.2.1 r (by rw [hΦ]; simp)
  have h3 := o1_eq hS hΦ hb (k := 3) (by omega)
  have h6 := o1_eq hS hΦ hb (k := 6) (by omega)
  have h2 := (regs hS).2.2.1
  have hns := hB.1
  have hnpw := hB.2.1
  have hd := hsm 3 (by omega)
  have ha6 := hsm 6 (by omega)
  simp only [Fr.fld] at h3 h6 hd ha6
  unfold o9 dsOf
  simp only [lit] at h2 ⊢
  simp only [h3, h6, h2]
  simp (disch := omega) only [u_beq, u_lt', u_add]
  by_cases d0 : r.d = 0
  · simp [d0, dest]
  by_cases d1 : r.d = 1
  · simp only [d1, decide_true, if_true, dest]; rcases o with _ | _ | o <;> simp <;> omega
  by_cases d2 : r.d = 2
  · simp only [d2, decide_true, if_true, decide_false]; simp; exact o10_eq (hr.2.1 d2) ho
  by_cases d3 : r.d = 3
  · simp only [d3, decide_true, if_true, dest]
    try simp only [decide_false, Bool.false_eq_true, if_false]
    have hc := hr.2.2 d3
    obtain ⟨a, ha, hlen, hp20, -, hnp, -, hP, -, -, -⟩ := hT.2.2.2 r.a hc
    have ht := hT.2.2.1
    generalize hL : W.ps.getD r.a [] = L at *
    rw [bget_u _ (by omega), ha, bget_u _ (by omega), hnp]
    simp only [u_lt' (show o < 2 ^ 64 by omega) (show L.length < 2 ^ 64 by omega)]
    by_cases ho2 : o < L.length
    · rw [if_pos ho2]; simp only [lit, u_add]; rw [bget_u _ (by omega), hP o ho2]
      congr 1; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho2]
    · rw [if_neg ho2]; congr 1; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show L.length ≤ o by omega)]
  simp only [d0, d1, d2, d3, decide_false, Bool.false_eq_true, if_false, dest]
  have hK := hF.2.2.2.2.1
  have hnsK : W.ns = W.K.length := rfl
  have hlen : (stD W.K W.npw).length = W.npw - 1 := by simp [stD]; omega
  by_cases ho1 : o + 1 < W.npw
  · rw [if_pos ho1, bget_u _ (by omega), hK (o + 1) (by omega)]
    have hk2 : W.K.getD (o + 1) 0 ≤ 2 := by
      have : o + 1 < W.K.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; exact hB.2.2.1 _ (List.getElem_mem _)
    have hget : (stD W.K W.npw).getD o 4 = if W.K.getD (o + 1) 0 = 2 then 3 else W.K.getD (o + 1) 0 := by
      have : o + 1 < W.K.length := by omega
      simp [stD, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, show o < W.npw - 1 by omega,
        List.getElem?_eq_getElem this]
    rw [hget]
    generalize W.K.getD (o + 1) 0 = k at *
    rw [u_beq (by omega) (by omega)]
    by_cases k2 : k = 2 <;> simp [k2] <;> rfl
  · rw [if_neg ho1]
    congr 1; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (stD W.K W.npw).length ≤ o by omega)]

theorem err_set1 {s : Buf} (h : 2 ≤ s.length) : bget (bset s 1 1) 1 = 1 := by
  simp only [bget, bset]; rw [show (1 : UInt64).toNat = 1 from rfl, getD_set]; simp; omega

theorem err_o5 {s : Buf} (h : 6 ≤ s.length) : bget (o5 s) 1 = 1 := by
  unfold o5; simp only [bget, bset]
  rw [show (1 : UInt64).toNat = 1 from rfl, show (5 : UInt64).toNat = 5 from rfl, getD_set, getD_set]; simp; omega

theorem o12_eq {W : WCx} {s f : Buf} {A : AS} (hS : RS W s A) (hF : RF W f A) (hB : Bnd W A) {e d : Nat}
    (he : e < 2 ^ 30) (hd : d < 2 ^ 30) : o12 s f (u e) (u d) = u (if ok1 A.F e d then 1 else 0) := by
  unfold o12 ok1
  simp only [lit]
  simp (disch := omega) only [u_lt', u_beq, u_and3, u_shr2, u_sub']
  by_cases e4 : e < 4
  · simp only [e4, if_true]
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with h | h | h | h <;> subst h <;>
      by_cases d4 : d < 4 <;> by_cases d1 : d = 1 <;> by_cases d2 : d = 2 <;> simp [d4, d1, d2]
  · simp only [e4, if_false]
    have q1 : 1 ≤ e / 4 := by omega
    rw [o7_dead hS hF hB (q := e / 4 - 1) (by omega)]
    by_cases k0 : e % 4 = 0
    · simp [k0]; by_cases d4 : d < 4 <;> simp [d4]
    by_cases k1 : e % 4 = 1
    · simp [k1]
      by_cases d1 : d = 1 <;> by_cases d2 : d = 2 <;> by_cases dd : dead A.F (e / 4 - 1) <;> simp [d1, d2, dd] <;> omega
    by_cases k2 : e % 4 = 2
    · simp [k2]; by_cases d2 : d = 2 <;> by_cases d3 : d = 3 <;> simp [d2, d3] <;> omega
    · simp [k0, k1, k2]

end OwnP
