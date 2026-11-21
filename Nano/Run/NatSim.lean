/- The bridge between the general relation `GTarget.Rel` of the native target at an anchor and ArmNat's `NMid`
(M3): at an anchor whose byte offset is word `q` of the image's words `A`, a related machine state shows the VIEW
`mview s st` (the machine's registers through `armReg`, J's memory) at word `q`, and the view agrees with the J state
off the anchor's dead registers (`Agree`); conversely an `NMid` state whose view agrees with a J state off the dead
set of an anchor is related there.  A segment case of an atom is then: `nmid_of_rel`, ArmNat steps on the view, the J
steps on the J state, `rel_of_nmid`. -/
import Nano.Run.NatImg
import Nano.Run.NatTarget
import Nano.Run.GUniform
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {V : List J → Img → Prop}

/-- the machine's view of the J state: registers from the machine, the rest from `st` -/
def mview (s : M.State) (st : CallProbe.St) : CallProbe.St :=
  { st with x := fun j => if 0 < j ∧ j < 32 then (M.observe s).register (armReg j) else 0 }

/-- the view `v` agrees with the J state `st` off the registers `D` -/
structure Agree (D : Nat → Prop) (v st : CallProbe.St) : Prop where
  x : ∀ j, 0 < j → j < 32 → ¬ D j → v.x j = st.x j
  m : v.m = st.m
  x0 : st.x 0 = 0

theorem wordBytes_len (A : List Nat) : (wordBytes A).length = 4 * A.length := by
  unfold wordBytes; exact flat_len _ 4 (fun _ => rfl) A

theorem wordBytes_get (A : List Nat) (i : Nat) (hi : i < A.length) (k : Nat) (hk : k < 4) :
    (wordBytes A)[4 * i + k]? = some (wbyte (BitVec.ofNat 32 A[i]) k) := by
  unfold wordBytes
  rw [flat_get _ 4 (fun _ => rfl) A i k hi hk]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem ofNat_offmod (b o : Nat) : UInt64.ofNat (b + o) = UInt64.ofNat (b + o % 2 ^ 64) := by
  apply UInt64.toNat_inj.1; rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat']; omega

/-- **from the relation to the view**: at an anchor at word `q` of the image's words `A` -/
theorem nmid_of_rel {K : LayW} {C : List J} {I : Img} {s0 s : M.State} {p : Nat × CallProbe.St} {A : List Nat} {q : Nat}
    (hl : JTarget.LayOK M I.code.length K) (hR : (natTarget M X W V).Rel K C I s0 p s) (hI : I.code = wordBytes A)
    (hq : I.off p.1 % 2 ^ 64 = 4 * q) :
    NMid X W K A s0 (mview s p.2) q s ∧ Agree (I.dead p.1) (mview s p.2) p.2 := by
  have hlen : I.code.length = 4 * A.length := by rw [hI, wordBytes_len]
  refine ⟨⟨hR.cfg, by rw [← hq, ← ofNat_offmod]; exact hR.pc, ?_, by simp [mview], fun j h0 h32 => by simp [mview, h0, h32],
    hR.keep, hR.w, hR.bw, hR.fr, hlen ▸ hl, (show PermOK X W K (4 * A.length) s by rw [← hlen]; exact hR.inv)⟩, ⟨fun j h0 h32 hd => ?_, rfl, hR.x0⟩⟩
  · intro i hi k hk
    have hlt : 4 * i + k < I.code.length := by omega
    have : (M.observe s).memory (UInt64.ofNat (K.base + (4 * i + k))) = some I.code[4 * i + k] := hR.code (4 * i + k) hlt
    rw [show K.base + 4 * i + k = K.base + (4 * i + k) by omega, this]
    have e := wordBytes_get A i hi k hk
    rw [← hI, List.getElem?_eq_getElem hlt] at e
    exact e
  · simp only [mview, h0, h32, and_self, if_true]; exact hR.x j h0 h32 hd

/-- **from the view to the relation**: at an anchor `pc` at word `q` -/
theorem rel_of_nmid {K : LayW} {C : List J} {I : Img} {s0 s : M.State} {A : List Nat} {q pc : Nat}
    {v st : CallProbe.St} (hM : NMid X W K A s0 v q s) (hag : Agree (I.dead pc) v st) (hI : I.code = wordBytes A)
    (hq : I.off pc % 2 ^ 64 = 4 * q) (hb : st.b = K.base) (hly : st.ly = I.ly) :
    (natTarget M X W V).Rel K C I s0 (pc, st) s := by
  have hlen : I.code.length = 4 * A.length := by rw [hI, wordBytes_len]
  refine ⟨hM.cfg, by show (M.observe s).programCounter = UInt64.ofNat (K.base + I.off pc); rw [ofNat_offmod, hq]; exact hM.pc, ?_, hag.x0, hb, hly,
    fun j h0 h32 hd => (hM.x j h0 h32).trans (hag.x j h0 h32 hd), hM.keep, fun a ha k hk => by rw [← hag.m]; exact hM.w a ha k hk,
    fun a ha => by rw [← hag.m]; exact hM.bw a ha, hM.fr, (show PermOK X W K I.code.length s by rw [hlen]; exact hM.pm)⟩
  intro a ha
  have hi : a / 4 < A.length := by omega
  have hk := Nat.mod_lt a (show 0 < 4 by decide)
  have e := wordBytes_get A (a / 4) hi (a % 4) hk
  rw [show 4 * (a / 4) + a % 4 = a by omega, ← hI, List.getElem?_eq_getElem ha] at e
  have := hM.code (a / 4) hi (a % 4) hk
  rw [show K.base + 4 * (a / 4) + a % 4 = K.base + a by omega] at this
  exact (this.trans e.symm : (M.observe s).memory (UInt64.ofNat (K.base + a)) = some I.code[a])

/-! ## the simulation of one atom -/

/-- the dead set after atom `t`, from the dead set `D` at its start -/
def outD (t : NTm) (D : Nat → Prop) (r : Nat) : Prop := (D r ∧ t.writes r = false) ∨ t.kills r = true

/-- **the segment case of atom `t`**: `t`'s J instructions sit at J pc `q` of `C`, its words at word `h` of `A`
(`π` = word index of a J pc); the machine shows a view `v` that agrees with the J state `st` off `D`, and `t` reads
nothing in `D`.  Then along any safe J run from `(q, st)` that does not end inside the atom, the J run reaches an
exit `c` of the atom, and the machine runs to word `π c.1` with a view that agrees with `c.2` off `outD t D`. -/
def ASim (M : Machine) (X W : M.State → Nat → Prop) (t : NTm) : Prop :=
  ∀ {K : LayW} {C : List J} {A : List Nat} {s0 s : M.State} {v st : CallProbe.St} {z : Nat × CallProbe.St} {n : Nat}
    {π : Nat → Nat} {q h : Nat} {D : Nat → Prop},
    (∀ i, i < t.j.length → C[q + i]? = t.j[i]?) → (∀ i, i < t.alen → A[h + i]? = (t.a π q h)[i]?) →
    K.base + 4 * A.length ≤ 2 ^ 32 → A.length < 2 ^ 18 →
    NMid X W K A s0 v h s → Agree D v st → (∀ r, D r → t.reads r = false) → st.b = K.base →
    -- the layout: the fall-through boundary, a call's link value, the targets, and link values (an offset below 2^64
    -- is a return point's)
    π (q + t.j.length) = h + t.alen → (t.isCall = true → st.lo (q + t.j.length) = 4 * (h + t.alen)) →
    (∀ p ∈ t.tg q, π p ≤ A.length) → (∀ p, st.lo p < 2 ^ 64 → st.lo p = 4 * π p ∧ π p ≤ A.length) →
    SRunN K C (n + 1) (q, st) z → (∀ i, 0 < i → i < t.j.length → z.1 ≠ q + i) →
    ∃ m c v' s', m ≤ n ∧ SRunN K C (n - m) c z ∧ Runs M s s' ∧ NMid X W K A s0 v' (π c.1) s' ∧
      Agree (outD t D) v' c.2 ∧ c.2.b = st.b ∧ c.2.ly = st.ly ∧
      ((c.1 = q + t.j.length ∧ t.ft = true) ∨ c.1 ∈ t.tg q ∨ c.2.lo c.1 < 2 ^ 64)

/-- a register write on both sides keeps the agreement (the written register is live afterwards) -/
theorem agree_wr {D : Nat → Prop} {v st : CallProbe.St} (h : Agree D v st) (d : Nat) (x : UInt64) :
    Agree (fun r => D r ∧ r ≠ d) (CallProbe.wr v d x) (CallProbe.wr st d x) := by
  refine ⟨fun j h0 h32 hd => ?_, ?_, ?_⟩
  · by_cases e : j = d
    · subst e; simp [CallProbe.wr, CallProbe.upd, show j ≠ 0 by omega]
    · have : v.x j = st.x j := h.x j h0 h32 (fun hD => hd ⟨hD, e⟩)
      by_cases hd0 : d = 0 <;> simp [CallProbe.wr, CallProbe.upd, hd0, e, this]
  · have := h.m; by_cases hd0 : d = 0 <;> simp [CallProbe.wr, hd0, this]
  · have := h.x0
    by_cases hd0 : d = 0
    · simp [CallProbe.wr, hd0, this]
    · simp [CallProbe.wr, CallProbe.upd, hd0, this, show (0 : Nat) ≠ d from fun e => hd0 e.symm]

theorem Agree.mono {D D' : Nat → Prop} {v st : CallProbe.St} (h : Agree D v st) (hs : ∀ r, D r → D' r) :
    Agree D' v st := ⟨fun j h0 h32 hd => h.x j h0 h32 (fun hD => hd (hs j hD)), h.m, h.x0⟩

theorem mr_iff {r : Nat} : NTm.mr r = true ↔ mapped r = true ∧ r ≠ 0 := by simp [NTm.mr]

/-- **worked case: the ALU atom** `alu op d x y` ↔ one 3-register word (mul: `movz x17, #0; madd`) -/
theorem asim_alu (S : A64SemN M X W) {op d x y : Nat} (hok : (NTm.alu op d x y).ok = true) :
    ASim M X W (NTm.alu op d x y) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff] at hok
  obtain ⟨⟨⟨hd, hd0⟩, hx, hx0⟩, hy, hy0⟩ := hok
  have c0 : C[q]? = some (.alu op d x y) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  obtain ⟨-, -, -, ⟨h1, h2⟩, -⟩ := hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have vx : v.x x = st.x x := hag.x x (by omega) (mapped_lt hx) (fun hD => by simpa [NTm.reads] using hrd x hD)
  have vy : v.x y = st.x y := hag.x y (by omega) (mapped_lt hy) (fun hD => by simpa [NTm.reads] using hrd y hD)
  have hfin : ∀ {s' : M.State}, Runs M s s' →
      NMid X W K A s0 (CallProbe.wr v d (CallProbe.aluf op (v.x x) (v.x y))) (h + (NTm.alu op d x y).alen) s' → _ :=
    fun {s'} r N => (⟨0, _, _, s', Nat.zero_le _, hrest, r, by rw [show π (q + 1) = _ from hft]; exact N,
      (by rw [vx, vy]; exact (agree_wr hag d _).mono (fun r hr => Or.inl ⟨hr.1, by simp only [NTm.writes, beq_eq_false_iff_ne]; exact fun e => hr.2 e.symm⟩)),
      CallProbe.wr_b _ _ _, CallProbe.wr_w _ _ _, Or.inl ⟨rfl, rfl⟩⟩ :
      ∃ m c v' s', m ≤ n ∧ SRunN K C (n - m) c z ∧ Runs M s s' ∧ NMid X W K A s0 v' (π c.1) s' ∧
        Agree (outD (NTm.alu op d x y) D) v' c.2 ∧ c.2.b = st.b ∧ c.2.ly = st.ly ∧
        ((c.1 = q + (NTm.alu op d x y).j.length ∧ (NTm.alu op d x y).ft = true) ∨ c.1 ∈ (NTm.alu op d x y).tg q ∨ c.2.lo c.1 < 2 ^ 64))
  by_cases h3 : op = 3
  · subst h3
    have a0 : A[h]? = some (ArmEnc.movz 17 0) := by simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
    have a1 : A[h + 1]? = some (ArmEnc.rr (ArmEnc.aluC 3) (armReg d) (armReg x) (armReg y)) := by
      simpa [NTm.a] using hA 1 (by simp [NTm.alen, NTm.a])
    obtain ⟨s', r, N⟩ := n_mul S hM hB a0 a1 hd hd0 hx hx0 hy hy0
    exact hfin r (by simpa [NTm.alen, NTm.a] using N)
  · have a0 : A[h]? = some (ArmEnc.rr (ArmEnc.aluC op) (armReg d) (armReg x) (armReg y)) := by
      simpa [NTm.a, h3] using hA 0 (by simp [NTm.alen, NTm.a, h3])
    obtain ⟨s', r, N⟩ := n_alu S hM hB a0 h1 h2 h3 hd hd0 hx hx0 hy hy0
    exact hfin r (by simpa [NTm.alen, NTm.a, h3] using N)

end JT
