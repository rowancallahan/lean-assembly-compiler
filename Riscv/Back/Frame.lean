/- The RISC-V instance of the extended interface (`Compiler/Frame.lean`): `rvF : MachineF` over `rv`.
Frame register `gp` (`x3`); `enter n` is `Arr2Code.prologue n`, `leave` is `ld gp, 0(gp)`, slot `j` is
`8 (j + 1)(gp)` (`iLdS`, `iSdS`), `ld`/`sd` are `ld t0, 0(t0)` / `sd t1, 0(t0)`.  Every law is proved from
the existing step lemmas (`Riscv/Steps/Arr2Words.lean`) and `prologue_ok` (`Riscv/Direct/Arr2F.lean`). -/
import Compiler.Frame
import Riscv.Back.Iface
import Riscv.Back.Arr
import Riscv.Direct.Arr2F
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

def encX : FOp → List (BitVec 32)
  | .enter n => prologue n
  | .leave => [iLdGp]
  | .ldS d j => [iLdS j d.val]
  | .stS j _ => [iSdS j]
  | .ld _ _ => [0x0002b283#32]     -- ld t0, 0(t0)
  | .sd _ _ => [0x0062b023#32]     -- sd t1, 0(t0)

theorem phys_ne3 : ∀ r : Reg, (3 : Fin 32) ≠ phys r := by decide
theorem phys_ge7 : ∀ r : Reg, 7 ≤ r.val → ∀ i, i < 7 → phys r ≠ T i := by
  intro r hr i hi
  have : ∀ r : Reg, 7 ≤ r.val → ∀ i : Fin 7, phys r ≠ T i.val := by decide
  exact this r hr ⟨i, hi⟩

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- the model's byte memory after `storeBytes` is `Mem.wr` -/
theorem storeBytes_wr : ∀ (m : Proven.Mem) (a : Nat) (l : List (BitVec 8)) (x : Nat),
    (storeBytes m a l)[x]? = Mem.wr (fun y => m[y]?) a l x
  | m, a, [], x => rfl
  | m, a, v :: l, x => by
    show (writeCells (m.insert a v) (List.range' (a + 1) l.length) l)[x]? = _
    have := storeBytes_wr (m.insert a v) (a + 1) l x
    unfold storeBytes at this; rw [this]
    show _ = Mem.wr (Mem.upd (fun y => m[y]?) a v) (a + 1) l x
    congr 1; funext y; unfold Mem.upd
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases hy : y = a
    · subst hy; simp
    · rw [ite_neg hy]; simp [Ne.symm hy]

theorem bytes_le8 {s : St} {a : Nat} {v : BitVec 64} (h : bytes (core.mem s) a 8 = (le8 v).map some) :
    bytesAt s a 8 = (Proven.le8 v).map some := (Proven.Mach.Riscv.bytes_eq s a 8).symm.trans h

def frX : St → BitVec 64 := fun s => getX s 3

theorem first' {s : St} {pc : BitVec 64} {ws} (hA : core.At s pc ws) : codeAt s pc ws ∧ codeOK pc ws.length :=
  ⟨hA.code, hA.codeOK⟩

theorem law_enter {n : Nat} {s : St} {pc : BitVec 64} (hf : FrOK n (frameBase n (getX s 2)))
    (hA : core.At s pc (encX (.enter n)))
    (hcd : disjoint ⟨pc.toNat, 4 * (encX (.enter n)).length⟩ ⟨frameBase n (getX s 2), 8 * (n + 1)⟩) :
    core.runsTo s fun s' => core.ok s' ∧
      (∀ j : Fin 32, (∀ r : Reg, j ≠ phys r) → j ≠ 3 → getX s' j = getX s j) ∧
      core.pcIs s' (next pc (encX (.enter n)).length) ∧
      getX s' 3 = BitVec.ofNat 64 (frameBase n (getX s 2)) ∧ (∀ r : Reg, 7 ≤ r.val → core.get s' r = core.get s r) ∧
      Out [⟨frameBase n (getX s 2), 8 * (n + 1)⟩] (core.mem s) (core.mem s') ∧
      bytes (core.mem s') (frameBase n (getX s 2)) 8 = (le8 (getX s 3)).map some ∧
      ∀ j, j < n → bytes (core.mem s') (frameBase n (getX s 2) + 8 * (j + 1)) 8 = (le8 0).map some := by
  have hsp : 8 * (n + 1) ≤ (getX s 2).toNat / 8 * 8 := by have := hf.lo; unfold frameBase at this; omega
  obtain ⟨s', r, h', pc', u, k, g, sv, z⟩ := prologue_ok hA.ok hA.hpc hA.code hA.codeOK hf hsp
    (by unfold Mach.disjoint at hcd; unfold Proven.disjoint; exact hcd)
  refine runsTo_of_reach r ⟨h', fun j hj h3 => k j (fun i hi e => hj (rk i) (e.trans (phys_rk (by omega)).symm)) h3,
    pc', g, fun q hq => k _ (phys_ge7 q hq) (phys_ne3 q).symm, fun a ha => u a fun r hr => ?_,
    (Proven.Mach.Riscv.bytes_eq s' _ _).trans sv, fun j hj => (Proven.Mach.Riscv.bytes_eq s' _ _).trans (z j hj)⟩
  simp only [List.mem_singleton] at hr; subst hr; exact ha _ (List.mem_singleton_self _)

theorem law_leave {s : St} {pc : BitVec 64} {w : BitVec 64} (hA : core.At s pc (encX .leave))
    (hr : core.inRAM (getX s 3).toNat 8) (hal : (getX s 3).toNat % 8 = 0)
    (hb : bytes (core.mem s) (getX s 3).toNat 8 = (le8 w).map some) :
    core.runsTo s fun s' => core.ok s' ∧
      (∀ j : Fin 32, (∀ r : Reg, j ≠ phys r) → j ≠ 3 → getX s' j = getX s j) ∧
      core.pcIs s' (next pc (encX .leave).length) ∧ getX s' 3 = w ∧ core.Same s s' ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytesAt_le8 (bytes_le8 hb)
  obtain ⟨s', hn⟩ := W2.ldGp h hpc hok (by simpa [iLdGp] using hi) hr hal h0 h1 h2 h3 h4 h5 h6 h7
  rw [Proven.le8_cat] at hn
  refine run1 hn ⟨hn.cfg, fun j _ h3' => by rw [hn.x j]; exact ite_neg (fun e => h3' e.1), hn.pc,
    by rw [hn.x 3]; exact ite_pos ⟨rfl, by decide⟩, fun q => ?_, memOf hn⟩
  show getX s' (phys q) = getX s (phys q)
  rw [hn.x]; exact ite_neg (fun e => phys_ne3 q e.1.symm)

theorem slotA {s : St} {j : Nat} (hr : core.inRAM ((getX s 3).toNat + 8 * (j + 1)) 8) :
    getX s 3 + BitVec.ofNat 64 (8 * (j + 1)) = BitVec.ofNat 64 ((getX s 3).toNat + 8 * (j + 1)) ∧
    (BitVec.ofNat 64 ((getX s 3).toNat + 8 * (j + 1))).toNat = (getX s 3).toNat + 8 * (j + 1) := by
  obtain ⟨_, h2⟩ := hr
  have h2' : (getX s 3).toNat + 8 * (j + 1) + 8 ≤ 0x100000000 := h2
  have e := toNat_ofNat_lt (n := (getX s 3).toNat + 8 * (j + 1)) (by omega)
  refine ⟨BitVec.eq_of_toNat_eq ?_, e⟩
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * (j + 1)) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem law_ldS {d : Reg} {j : Nat} {s : St} {pc : BitVec 64} {v : BitVec 64} (hd : d.val < 7) (hj : j < NS)
    (hA : core.At s pc (encX (.ldS d j))) (hr : core.inRAM ((getX s 3).toNat + 8 * (j + 1)) 8)
    (hal : ((getX s 3).toNat + 8 * (j + 1)) % 8 = 0)
    (hb : bytes (core.mem s) ((getX s 3).toNat + 8 * (j + 1)) 8 = (le8 v).map some) :
    core.runsTo s fun s' => core.Done s s' (next pc (encX (.ldS d j)).length) ∧ core.Set1 s s' d v ∧
      core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨e1, e2⟩ := slotA hr
  obtain ⟨s', hn⟩ := step_ldS h hpc hok j d.val hj hd hi (A := BitVec.ofNat 64 ((getX s 3).toNat + 8 * (j + 1)))
    (by rw [e2]; exact hr) (by rw [e2]; exact hal) e1 (by rw [e2]; exact bytes_le8 hb)
  rw [← phys_rk (k := d.val) (by omega), show rk d.val = d from Fin.ext (rk_val (by omega))] at hn
  exact run1 hn ⟨ofNext hn (.inr ⟨d, rfl⟩), set1Of hn, memOf hn⟩

theorem law_stS {j : Nat} {v : Reg} {s : St} {pc : BitVec 64} (hv : v.val = 0) (hj : j < NS)
    (hA : core.At s pc (encX (.stS j v))) (hr : core.inRAM ((getX s 3).toNat + 8 * (j + 1)) 8)
    (hal : ((getX s 3).toNat + 8 * (j + 1)) % 8 = 0) :
    core.runsTo s fun s' => core.Done s s' (next pc (encX (.stS j v)).length) ∧ core.Same s s' ∧
      core.mem s' = (core.mem s).wr ((getX s 3).toNat + 8 * (j + 1)) (le8 (core.get s v)) := by
  have ev : phys v = 5 := by rw [phys_T v (by omega), hv]; rfl
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨e1, e2⟩ := slotA hr
  obtain ⟨s', hn⟩ := step_sdS h hpc hok j hj hi (A := BitVec.ofNat 64 ((getX s 3).toNat + 8 * (j + 1)))
    (by rw [e2]; exact hr) (by rw [e2]; exact hal) e1
  refine run1 hn ⟨ofNext hn (.inl rfl), sameOf hn, ?_⟩
  funext x
  show s'.mem[x]? = _
  rw [hn.mem, e2, storeBytes_wr]
  show _ = Mem.wr (core.mem s) _ (le8 (getX s (phys v))) x
  rw [ev]; rfl

theorem law_ld {d a : Reg} {s : St} {pc : BitVec 64} {v : BitVec 64} (hd : d.val = 0) (ha : a.val = 0)
    (hA : core.At s pc (encX (.ld d a))) (hr : core.inRAM (core.get s a).toNat 8) (hal : (core.get s a).toNat % 8 = 0)
    (hb : bytes (core.mem s) (core.get s a).toNat 8 = (le8 v).map some) :
    core.runsTo s fun s' => core.Done s s' (next pc (encX (.ld d a)).length) ∧ core.Set1 s s' d v ∧
      core.mem s' = core.mem s := by
  have ed : phys d = 5 := by rw [phys_T d (by omega), hd]; rfl
  have ea : phys a = 5 := by rw [phys_T a (by omega), ha]; rfl
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  have ga : core.get s a = getX s 5 := by show getX s (phys a) = _; rw [ea]
  rw [ga] at hr hal hb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytesAt_le8 (bytes_le8 hb)
  obtain ⟨s', hn⟩ := W2.ldT h hpc hok hi hr hal h0 h1 h2 h3 h4 h5 h6 h7
  rw [Proven.le8_cat, ← ed] at hn
  exact run1 hn ⟨ofNext hn (.inr ⟨d, rfl⟩), set1Of hn, memOf hn⟩

theorem law_sd {v a : Reg} {s : St} {pc : BitVec 64} (hv : v.val = 1) (ha : a.val = 0)
    (hA : core.At s pc (encX (.sd v a))) (hr : core.inRAM (core.get s a).toNat 8) (hal : (core.get s a).toNat % 8 = 0) :
    core.runsTo s fun s' => core.Done s s' (next pc (encX (.sd v a)).length) ∧ core.Same s s' ∧
      core.mem s' = (core.mem s).wr (core.get s a).toNat (le8 (core.get s v)) := by
  have ev : phys v = 6 := by rw [phys_T v (by omega), hv]; rfl
  have ea : phys a = 5 := by rw [phys_T a (by omega), ha]; rfl
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  have ga : core.get s a = getX s 5 := by show getX s (phys a) = _; rw [ea]
  have gv : core.get s v = getX s 6 := by show getX s (phys v) = _; rw [ev]
  rw [ga] at hr hal ⊢; rw [gv]
  obtain ⟨s', hn⟩ := W2.sdT h hpc hok hi hr hal
  refine run1 hn ⟨ofNext hn (.inl rfl), sameOf hn, ?_⟩
  funext x
  show s'.mem[x]? = _
  rw [hn.mem, storeBytes_wr]; rfl

/-- **The Sail RV64 model is a `MachineF`.** -/
def rvF : MachineF where
  toMachine := rv
  encX := encX
  fr s := getX s 3
  keepF s s' := ∀ j : Fin 32, (∀ r : Reg, j ≠ phys r) → j ≠ 3 → getX s' j = getX s j
  frameAt s n := frameBase n (getX s 2)
  enterOK s n := FrOK n (frameBase n (getX s 2))
  maxSlots := NS
  keepF_of_keep h j hj _ := h j hj
  keepF_trans h₁ h₂ j hj h3 := (h₂ j hj h3).trans (h₁ j hj h3)
  keep_fr h := h 3 phys_ne3
  keep_of_keepF h e j hj := by
    by_cases h3 : j = 3
    · subst h3; exact e
    · exact h j hj h3
  keepF_ra h := h 1 phys_ne1 (by decide)
  enterOK_frame hf := ⟨hf.ns, ⟨hf.lo, hf.hi⟩, hf.al⟩
  law_enter := law_enter
  law_leave := law_leave
  law_ldS := law_ldS
  law_stS := law_stS
  law_ld := law_ld
  law_sd := law_sd

end Proven.Mach.Riscv
