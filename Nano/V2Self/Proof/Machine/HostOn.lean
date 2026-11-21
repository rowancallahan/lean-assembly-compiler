/- The generic host lift, part 1 (over any general target `GTarget`): J's view of a machine state (`jOfG`), the entry
(`rel_entry`: the start state is related to its J view at pc 0) and the exit (`fin_on`: from an anchor at the final
`jalr x0, 0(x1)`, the return to the host with the result registers, the output bytes, the kept registers and the
memory frame).  Replaces SimW's `jOf`/`rel_init`/`fin_out` (Sail-RV) for every target. -/
import Nano.V2Self.Proof.Machine.GTarget
namespace JT
open Proven.Top SimW CallProbe

/-- the byte at address `a` (0 if absent) -/
def gbM (M : Machine) (s : M.State) (a : Nat) : UInt8 := ((M.observe s).memory (UInt64.ofNat a)).getD 0

/-- the little-endian 8-byte cell at `a` -/
def wordM (M : Machine) (s : M.State) (a : Nat) : UInt64 :=
  UInt64.ofNat ((gbM M s a).toNat + 256 * (gbM M s (a + 1)).toNat + 65536 * (gbM M s (a + 2)).toNat +
    16777216 * (gbM M s (a + 3)).toNat + 4294967296 * (gbM M s (a + 4)).toNat +
    1099511627776 * (gbM M s (a + 5)).toNat + 281474976710656 * (gbM M s (a + 6)).toNat +
    72057594037927936 * (gbM M s (a + 7)).toNat)

theorem cbyte_toNat (v : UInt64) (k : Nat) (hk : k < 8) : (cbyte v k).toNat = v.toNat / 2 ^ (8 * k) % 256 := by
  have : (8 * k) % 64 = 8 * k := Nat.mod_eq_of_lt (by omega)
  simp [cbyte, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, this]

theorem cbyte_wordM {M : Machine} (s : M.State) (a k : Nat) (hk : k < 8) : cbyte (wordM M s a) k = gbM M s (a + k) := by
  apply UInt8.toNat_inj.1
  rw [cbyte_toNat _ _ hk]
  have h0 := (gbM M s a).toNat_lt; have h1 := (gbM M s (a + 1)).toNat_lt; have h2 := (gbM M s (a + 2)).toNat_lt
  have h3 := (gbM M s (a + 3)).toNat_lt; have h4 := (gbM M s (a + 4)).toNat_lt; have h5 := (gbM M s (a + 5)).toNat_lt
  have h6 := (gbM M s (a + 6)).toNat_lt; have h7 := (gbM M s (a + 7)).toNat_lt
  simp only [wordM, UInt64.toNat_ofNat']
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-- J's view of a machine state: the J registers through `reg`, the little-endian cells, the code base `b`, the
link layout `ly` (the image's) -/
def jOfG (T : GTarget) (s : T.M.State) (b : Nat) (ly : CallProbe.LinkLay) : CallProbe.St :=
  ⟨fun j => if 0 < j ∧ j < 32 then (T.M.observe s).register (T.reg j) else 0, wordM T.M s, b, ly⟩

theorem gbM_some {M : Machine} {s : M.State} {a : Nat} (h : ((M.observe s).memory (UInt64.ofNat a)).isSome) :
    (M.observe s).memory (UInt64.ofNat a) = some (gbM M s a) := by
  unfold gbM; cases e : (M.observe s).memory (UInt64.ofNat a) with
  | none => rw [e] at h; simp at h
  | some v => rfl

variable {T : GTarget}

/-- **the entry**: a configured state at pc = base with the code bytes, the work cells and the input/output bytes
present, and `m0` = its memory, is related to its J view at pc 0 -/
theorem rel_entry (L : T.Laws) {K : LayW} {C : List J} {I : Img} {s : T.M.State} (hc : T.M.configured s)
    (hpc : (T.M.observe s).programCounter = UInt64.ofNat K.base) (hv : T.valid C I)
    (hcode : ∀ a (h : a < I.code.length), (T.M.observe s).memory (UInt64.ofNat (K.base + a)) = some I.code[a])
    (hw : ∀ a, wok K a → ∀ k < 8, ((T.M.observe s).memory (UInt64.ofNat (a + k))).isSome)
    (hio : ∀ a, io K a → ((T.M.observe s).memory (UInt64.ofNat a)).isSome) (hm0 : K.m0 = T.m0 s)
    (hinv : T.inv K C I s) :
    T.Rel K C I s (0, jOfG T s K.base I.ly) s where
  cfg := hc
  pc := by show _ = UInt64.ofNat (K.base + I.off 0); rw [hpc, (L.entry C I hv).2, Nat.add_zero]
  code := hcode
  x0 := by simp [jOfG]
  bb := rfl
  lk := rfl
  x := fun j h0 h32 => by simp [jOfG, h0, h32]
  keep := fun _ _ _ => rfl
  w := fun a ha k hk => by rw [gbM_some (hw a ha k hk)]; simp only [jOfG]; rw [cbyte_wordM s a k hk]
  bw := fun c hc => by
    rw [gbM_some (hio c hc)]; simp only [jOfG]
    rw [cbyte_wordM s _ _ (Nat.mod_lt _ (by decide)), show c - c % 8 + c % 8 = c by omega]
  fr := fun a ha _ _ => by rw [hm0, L.m0_obs s a ha]
  inv := hinv

theorem lbm_cbyte (m : Nat → UInt64) (a : Nat) : CallProbe.lbm m a = (cbyte (m (a - a % 8)) (a % 8)).toUInt64 := by
  apply UInt64.toNat_inj.1
  have hk : a % 8 < 8 := Nat.mod_lt _ (by decide)
  have : (8 * (a % 8)) % 64 = 8 * (a % 8) := Nat.mod_eq_of_lt (by omega)
  simp [CallProbe.lbm, cbyte, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, this, UInt64.toNat_and]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- **the exit**: at the final `jalr x0, 0(x1)` (J registers kept as Gen keeps them, the result `y` at the output),
the machine returns to `x1` with x10/x11 as J's, the output bytes, the kept registers and the memory frame -/
theorem fin_on (L : T.Laws) {K : LayW} {C : List J} {I : Img} {s0 st : T.M.State} {pr : Nat} {s3 : CallProbe.St}
    (hl : T.lay K C I) (hR : T.Rel K C I s0 (pr, s3) st) (hvis : I.vis pr) (hC : C[pr]? = some (.jalr 0 1))
    (hra : (s3.x 1).toNat % 4 = 0)
    (hkeep : ∀ j, Templates.keepR j = true → s3.x j = (jOfG T s0 K.base I.ly).x j)
    (hx8 : s3.x 8 = (jOfG T s0 K.base I.ly).x 8)
    (hm0 : K.m0 = T.m0 s0) (lo hi : Nat) (hlo : lo ≤ K.lo) (hhi : K.hi ≤ hi)
    (y : List UInt8) (hol : K.ol = y.length)
    (hy : ∀ i, i < y.length → CallProbe.lbm s3.m (K.ob + i) = (y.getD i 0).toUInt64) :
    ∃ s4, Runs T.M st s4 ∧ (T.M.observe s4).programCounter = s3.x 1 ∧
      (T.M.observe s4).register (T.reg 10) = s3.x 10 ∧ (T.M.observe s4).register (T.reg 11) = s3.x 11 ∧
      (∀ r ∈ T.M.mapping.kept, (T.M.observe s4).register r = (T.M.observe s0).register r) ∧
      (∀ i, i < y.length → (T.M.observe s4).memory (UInt64.ofNat (K.ob + i)) = some (y.getD i 0)) ∧
      (∀ a, a < 2 ^ 64 → (a < K.ob ∨ K.ob + y.length ≤ a) → (a < lo ∨ hi ≤ a) →
        (T.M.observe s4).memory (UInt64.ofNat a) = (T.M.observe s0).memory (UInt64.ofNat a)) ∧
      T.M.configured s4 := by
  obtain ⟨s4, hr, hpc, hreg, hmem, hcfg⟩ := L.ret_ok hl hR hvis hC hra
  refine ⟨s4, hr, hpc, by rw [hreg, hR.x 10 (by omega) (by omega)], by rw [hreg, hR.x 11 (by omega) (by omega)],
    ?_, ?_, ?_, hcfg⟩
  · intro r hr'
    rw [hreg]
    rcases L.kept_map r hr' with ⟨j, h0, h32, rfl, hj⟩ | ⟨hn, hs⟩
    · rw [hR.x j h0 h32]
      have e : s3.x j = (jOfG T s0 K.base I.ly).x j := by
        rcases hj with hj | rfl
        · exact hkeep j hj
        · exact hx8
      rw [e]; simp [jOfG, h0, h32]
    · exact hR.keep r hn hs
  · intro i hi
    rw [hmem]
    have hio : io K (K.ob + i) := Or.inr ⟨by omega, by omega⟩
    rw [hR.bw _ hio]
    congr 1
    have := hy i hi
    rw [lbm_cbyte] at this
    exact UInt8.toNat_inj.1 (by have := congrArg UInt64.toNat this; simpa using this)
  · intro a ha h1 h2
    rw [hmem]
    have n1 : ¬ wok K (a - a % 8) := fun hw => by unfold wok at hw; omega
    have n2 : ¬ outB K a := fun ho => by unfold outB at ho; omega
    rw [hR.fr a ha n1 n2, hm0, L.m0_obs s0 a ha]

end JT
