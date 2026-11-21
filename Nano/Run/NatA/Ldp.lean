/- T03 (round 2): the atom `ldp a b n sw` (two J loads `ld a n 0; ld b n 8`, in either order) ↔ `ldp xa, xb, [xn]`. -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

theorem ea0 (x : UInt64) : CallProbe.ea x 0 = x.toNat := by unfold CallProbe.ea; omega
theorem ea8 (x : UInt64) : CallProbe.ea x 8 = x.toNat + 8 := by unfold CallProbe.ea; omega

theorem wr_comm {st : CallProbe.St} {a b : Nat} {X Y : UInt64} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) :
    CallProbe.wr (CallProbe.wr st a X) b Y = CallProbe.wr (CallProbe.wr st b Y) a X := by
  have : CallProbe.upd (CallProbe.upd st.x a X) b Y = CallProbe.upd (CallProbe.upd st.x b Y) a X := by
    funext i; simp only [CallProbe.upd]
    by_cases e1 : i = a
    · subst e1; simp [hab]
    · simp [e1]
  simp only [CallProbe.wr, ha0, hb0, if_false]
  show ({ st with x := CallProbe.upd (CallProbe.upd st.x a X) b Y } : CallProbe.St) =
    { st with x := CallProbe.upd (CallProbe.upd st.x b Y) a X }
  rw [this]

theorem wr_x_ne {st : CallProbe.St} {d r : Nat} {v : UInt64} (h : d ≠ r) : (CallProbe.wr st d v).x r = st.x r := by
  by_cases h0 : d = 0 <;> simp [CallProbe.wr, CallProbe.upd, h0, Ne.symm h]

/-- one J load -/
theorem ld_j {K : LayW} {C : List CallProbe.J} {q : Nat} {st : CallProbe.St} {b : Nat × CallProbe.St} {d r : Nat}
    {off : Int} (c0 : C[q]? = some (.ld d r off)) (hS : SafeX K C (q, st)) (hs : CallProbe.step C (q, st) = some b) :
    wok K (CallProbe.ea (st.x r) off) ∧ b = (q + 1, CallProbe.wr st d (st.m (CallProbe.ea (st.x r) off))) := by
  simp only [SafeX, c0] at hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs
  exact ⟨hS.2.2.2.2.2, hs.symm⟩

/-- two J loads from the same base (not overwritten by the first) -/
theorem ld2_j {K : LayW} {C : List CallProbe.J} {q n : Nat} {st : CallProbe.St} {z : Nat × CallProbe.St} {d1 d2 r : Nat}
    {o1 o2 : Int} (c0 : C[q]? = some (.ld d1 r o1)) (c1 : C[q + 1]? = some (.ld d2 r o2)) (h1r : d1 ≠ r)
    (hz : z.1 ≠ q + 1) (hrun : SRunN K C (n + 1) (q, st) z) :
    ∃ k, n = k + 1 ∧ wok K (CallProbe.ea (st.x r) o1) ∧ wok K (CallProbe.ea (st.x r) o2) ∧
      SRunN K C k (q + 2, CallProbe.wr (CallProbe.wr st d1 (st.m (CallProbe.ea (st.x r) o1))) d2
        (st.m (CallProbe.ea (st.x r) o2))) z := by
  cases hrun with
  | head hS hs hrest =>
  obtain ⟨w1, e1⟩ := ld_j c0 hS hs
  subst e1
  cases hrest with
  | refl => exact absurd rfl hz
  | head hS2 hs2 hrest2 =>
  obtain ⟨w2, e2⟩ := ld_j c1 hS2 hs2
  subst e2
  have hx := wr_x_ne (st := st) (v := st.m (CallProbe.ea (st.x r) o1)) h1r
  have hm : (CallProbe.wr st d1 (st.m (CallProbe.ea (st.x r) o1))).m = st.m := by
    by_cases h0 : d1 = 0 <;> simp [CallProbe.wr, h0]
  rw [hx] at w2
  rw [hx, hm] at hrest2
  exact ⟨_, rfl, w1, w2, hrest2⟩

theorem asim_ldp (S : A64SemN M X W) {a b n : Nat} {sw : Bool} (hok : (NTm.ldp a b n sw).ok = true) :
    ASim M X W (NTm.ldp a b n sw) := by
  intro K C A s0 s v st z n' π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨ha, ha0⟩, hb', hb0⟩, hn, hn0⟩, hab, han, hbn⟩ := hok
  have hjl : (NTm.ldp a b n sw).j.length = 2 := by cases sw <;> simp [NTm.j]
  have hal : (NTm.ldp a b n sw).alen = 1 := by simp [NTm.alen, NTm.a]
  have hz1 : z.1 ≠ q + 1 := hz 1 (by omega) (by omega)
  have key : ∃ k, n' = k + 1 ∧ wok K (st.x n).toNat ∧ wok K ((st.x n).toNat + 8) ∧
      SRunN K C k (q + 2, CallProbe.wr (CallProbe.wr st a (st.m (st.x n).toNat)) b (st.m ((st.x n).toNat + 8))) z := by
    cases sw
    · have c0 : C[q]? = some (.ld a n 0) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
      have c1 : C[q + 1]? = some (.ld b n 8) := by simpa [NTm.j] using hJ 1 (by simp [NTm.j])
      obtain ⟨k, hk, w1, w2, hr⟩ := ld2_j c0 c1 han hz1 hrun
      rw [ea0] at w1 hr; rw [ea8] at w2 hr
      exact ⟨k, hk, w1, w2, hr⟩
    · have c0 : C[q]? = some (.ld b n 8) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
      have c1 : C[q + 1]? = some (.ld a n 0) := by simpa [NTm.j] using hJ 1 (by simp [NTm.j])
      obtain ⟨k, hk, w1, w2, hr⟩ := ld2_j c0 c1 hbn hz1 hrun
      rw [ea0] at w2 hr; rw [ea8] at w1 hr
      exact ⟨k, hk, w2, w1, by rw [wr_comm ha0 hb0 hab]; exact hr⟩
  obtain ⟨k, hk, hw0, hw8, hr⟩ := key
  subst hk
  have vn : v.x n = st.x n := hag.x n (by omega) (mapped_lt hn) (fun hD => by simpa [NTm.reads] using hrd n hD)
  have a0 : A[h]? = some (ArmEnc.ldp (armReg a) (armReg b) (armReg n)) := by
    simpa [NTm.a] using hA 0 (by simp [hal])
  obtain ⟨s', r, N⟩ := n_ldp S hM hB a0 ha ha0 hb' hb0 hab (armReg_lt hn hn0)
    (hM.x n (by omega) (mapped_lt hn)) (by rw [vn]; exact hw0) (by rw [vn]; exact hw8)
  rw [vn, hag.m] at N
  rw [hjl] at hft
  refine ⟨1, (q + 2, CallProbe.wr (CallProbe.wr st a (st.m (st.x n).toNat)) b (st.m ((st.x n).toNat + 8))), _, s',
    Nat.le_add_left _ _, by rw [Nat.add_sub_cancel]; exact hr, r, by rw [hft]; simpa [hal] using N, ?_,
    (CallProbe.wr_b _ _ _).trans (CallProbe.wr_b _ _ _), (CallProbe.wr_w _ _ _).trans (CallProbe.wr_w _ _ _),
    Or.inl (by rw [hjl])⟩
  refine (agree_wr (agree_wr hag a _) b _).mono (fun r hr => Or.inl ⟨hr.1.1, ?_⟩)
  simp only [NTm.writes, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨fun e => hr.1.2 e.symm, fun e => hr.2 e.symm⟩

end JT
