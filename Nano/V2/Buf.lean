import Nano.V2.Comp
/- nano v2 increment 5 (buffers), proof layer: the buffer REPRESENTATION on the abstract machine (Nano/V2/Sem.lean),
after Testing/notes/NANO_V2_SKELETONS6.lean `Round6.MultiBuffer` (`BufferRep`, footprints, `SameOutside`), and the
node lemmas of the buffer blocks of `cE` (Nano/V2/Gen.lean).  Layout: `[len][cap][cap data words]` at `a`.
Here: the BORROW nodes (`size`, `get`: memory unchanged).  Next: `set`/`push` (one footprint changes,
`SameOutside`), `mk` (the heap top grows), then the generalised `Post`/`EnvRep` for `cE_ok`. -/
namespace Nano.V2B

/-- the buffer `l` (capacity `cap`) at address `a` -/
structure BufRep (c : Cfg) (s : St) (a cap : Nat) (l : List UInt64) : Prop where
  al : a % 8 = 0
  lo : c.lo ≤ a
  cap_lt : cap < 2 ^ 20
  len_le : l.length ≤ cap
  hd : s.w a = UInt64.ofNat l.length
  hc : s.w (a + 8) = UInt64.ofNat cap
  el : ∀ i < l.length, s.w (a + 16 + 8 * i) = l.getD i 0

/-- the end of the footprint `[a, a + 16 + 8·cap)` -/
def foot (a cap : Nat) : Nat := a + 16 + 8 * cap

/-- a buffer below the heap top survives every block that keeps the heap -/
theorem BufRep.keep {c : Cfg} {s s' : St} {a cap : Nat} {l : List UInt64} (hr : BufRep c s a cap l)
    (hf : foot a cap ≤ (s.get 30).toNat) (k : Keep s s') : BufRep c s' a cap l where
  al := hr.al
  lo := hr.lo
  cap_lt := hr.cap_lt
  len_le := hr.len_le
  hd := by rw [k.heap a (by unfold foot at hf; omega)]; exact hr.hd
  hc := by rw [k.heap (a + 8) (by unfold foot at hf; omega)]; exact hr.hc
  el := fun i hi => by
    rw [k.heap _ (by have := hr.len_le; unfold foot at hf; omega)]; exact hr.el i hi

theorem run1 {c : Cfg} {i : I} {s s' : St} (e : runL c [i] s = some s') : i.run c s = some s' := by
  simp only [runL] at e
  cases h : i.run c s with
  | none => rw [h] at e; simp at e
  | some x => rw [h] at e; simpa using e

/-- loading the word at address `p` (a word inside the heap) through register `rs` holding `p` -/
theorem ld_heap {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hc : c.Good) (hs : Stk c s h L) (rd rs : Nat)
    (p : Nat) (hp : (s.get rs).toNat = p) (h8 : p % 8 = 0) (hlo : c.lo ≤ p) (hh : p + 8 ≤ h) :
    I.run c s (.ld rd rs 0) = some (s.set rd (s.w p)) := by
  have hea : ea s rs 0 = p := by
    unfold ea; rw [show UInt64.ofInt (0 : Int) = 0 from rfl, UInt64.add_zero, hp]
  have hw : c.wok p := ⟨hlo, by have := hs.hsp; omega, h8⟩
  simp only [I.run, hea, if_pos hw]

/-- **`size`** (borrow): the block `cb` pushes the buffer's address -/
theorem size_node {c : Cfg} {cb : SC} {s : St} {h : Nat} {L : List UInt64} {a cap : Nat} {l : List UInt64}
    (hc : c.Good) (hs : Stk c s h L) (hr : BufRep c s a cap l) (hf : foot a cap ≤ h)
    (hb : ∃ r, SC.Ex c cb s r ∧ Post c s h L [UInt64.ofNat a] r) :
    ∃ r, SC.Ex c (.seq cb (.ins [.ld T0 SP 0, .ld T0 T0 0, .sd T0 SP 0])) s r ∧
      Post c s h L [l.length.toUInt64] r := by
  obtain ⟨r, e, p⟩ := hb
  cases r with
  | jmp t s1 => exact ⟨_, .seqJ e, p⟩
  | ok s1 =>
    obtain ⟨hs1, k1⟩ := p
    have hr1 := hr.keep (by rw [hs.hp]; exact hf) k1
    have ha : a < 2 ^ 64 := by have := hs.hsp; have := hc.hi_lt; unfold foot at hf; omega
    have e1 := run1 (ld_slot hc hs1 T0 0 (by simp))
    rw [show (L ++ [UInt64.ofNat a]).getD ((L ++ [UInt64.ofNat a]).length - 1 - 0) 0 = UInt64.ofNat a by simp] at e1
    let s2 := s1.set T0 (UInt64.ofNat a)
    have hs2 : Stk c s2 h (L ++ [UInt64.ofNat a]) := hs1.set T0 _ (by decide) (by decide)
    have e2 := ld_heap hc hs2 T0 T0 a
      (by simp only [s2]; rw [get_set_eq _ _ _ (by decide), UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha])
      hr1.al hr1.lo (by unfold foot at hf; omega)
    let s3 := s2.set T0 (s2.w a)
    have hs3 : Stk c s3 h (L ++ [UInt64.ofNat a]) := hs2.set T0 _ (by decide) (by decide)
    obtain ⟨s4, e3, hs4, k4, _⟩ := sd_top hc hs3 T0
    have g3 : s3.get T0 = l.length.toUInt64 := by
      simp only [s3, s2]; rw [get_set_eq _ _ _ (by decide)]; simp only [set_w]; rw [hr1.hd]
    rw [g3] at hs4
    have k3 : Keep s1 s3 :=
      (Keep.set s1 T0 _ (by decide) (by decide)).trans (Keep.set s2 T0 _ (by decide) (by decide))
        (get_set_ne _ _ _ _ (by decide))
    have e1' : I.run c s1 (I.ld T0 SP 0) = some s2 := by simpa using e1
    have run3 : runL c [.ld T0 SP 0, .ld T0 T0 0, .sd T0 SP 0] s1 = some s4 := by
      simp only [runL]; rw [e1']; simp only [Option.bind_some]; rw [e2]; simp only [Option.bind_some]
      rw [show s2.set T0 (s2.w a) = s3 from rfl, run1 e3]; rfl
    refine ⟨_, .seq e (.ins run3), hs4, ?_⟩
    exact (k1.trans k3 (hp_eq hs hs1)).trans k4 (hp_eq hs hs3)

end Nano.V2B
