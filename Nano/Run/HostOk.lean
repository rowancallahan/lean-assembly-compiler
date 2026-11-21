/- The generic host lift, part 3 (over any general target `GTarget`): the normal return (`host_ok`).  Gen's program
`Cj` for a parsed, linear program, loaded as the bytes of an image `I` valid for `Cj`, called per `StartCorrect`: if `semAt main` succeeds in the work
block, the run returns to the caller with status = (y = [] ? 1 : 0), the length register = |y|, `y` in the output
block, memory changed only in the work block and the result prefix, the kept registers, configured. -/
import Nano.Run.HostGen
import Nano.Run.GenMainN
import Spec.Alloc
namespace JT
open Proven.Top Proven.Top.Alloc SimW CallProbe ParSpec Templates

variable {T : GTarget}

theorem mapM_of (g : Nat → Option UInt8) : ∀ (l : List Nat) (bs : List UInt8), bs.length = l.length →
    (∀ i (hi : i < l.length), g l[i] = bs[i]?) → l.mapM g = some bs
  | [], [], _, _ => by simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: bs, h, hg => by
    rw [List.mapM_cons, show g a = some b from hg 0 (by simp),
      mapM_of g l bs (by simpa using h) (fun i hi => hg (i + 1) (by simp; omega))]
    rfl

/-- `readMemory` from its bytes -/
theorem read_of {st : MachineState} {a : UInt64} {y : List UInt8}
    (h : ∀ i, i < y.length → st.memory (UInt64.ofNat (a.toNat + i)) = some (y.getD i 0)) :
    readMemory st a y.length = some y := by
  refine mapM_of _ _ _ (by simp) fun i hi => ?_
  simp only [List.getElem_range, add_ofNat]
  rw [h i (by simpa using hi), List.getElem?_eq_getElem (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < y.length by simpa using hi)]

theorem lbm_wordM {M : Machine} (s : M.State) (a : Nat) : lbm (wordM M s) a = (gbM M s a).toUInt64 := by
  rw [lbm_cbyte, cbyte_wordM s _ _ (Nat.mod_lt _ (by decide)), show a - a % 8 + a % 8 = a by omega]

/-- **the normal return, on any target** -/
theorem host_ok (L : T.Laws) (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
    (Ks : List (List Nat)) (hO : OwnSpec.progOk [] [] Ks p = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hXl : (serialize p).length < 2 ^ 31) (h : C.g41 c (serialize p) ≠ []) (hdb : ∀ d ∈ p, DB d)
    (I : Img) (hB : ∀ Cj : List J, Cj.length < 2 ^ 18 →
      C.g41 c (serialize p) = C.g40 16777216 c (Cj.map encG) 0 [] →
      (∀ j ∈ Cj, SimW.JOK j) → T.valid Cj I)
    {s : T.M.State} {call : Call} {x : List UInt8} (sc : StartCorrect T.M s call I.code x)
    (hld : T.loader s call I.code x)
    (y : List UInt8) (hSem : NanoMain.Sem NanoMain.κC p x = .ok y) (hy : y.length ≤ call.outputLength)
    (h16 : call.workAddress.toNat + 16 ≤ (call.workAddress.toNat + call.workLength) / 8 * 8)
    (hS : ∀ Tb, ∃ vs H', semAt (pcOf 524288 (call.workAddress.toNat + 16) (UInt64.ofNat x.length)
      (NanoMain.inpW x) Tb) p (p.length - 1) [] ((call.workAddress.toNat + call.workLength) / 8 * 8)
      ⟨call.workAddress.toNat + 16, fun _ => none⟩ = some (vs, H')) :
    ∃ s', Runs T.M s s' ∧ (T.M.observe s').programCounter = call.returnAddress ∧
      (T.M.observe s').register T.M.mapping.status = (if y = [] then 1 else 0) ∧
      (T.M.observe s').register T.M.mapping.outputLength = y.length.toUInt64 ∧
      readMemory (T.M.observe s') call.outputAddress y.length = some y ∧
      (∀ a, Outside a (call.outputAddress, y.length) → Outside a (call.workAddress, call.workLength) →
        (T.M.observe s').memory a = (T.M.observe s).memory a) ∧
      KeptRegisters T.M s s' ∧ T.M.configured s' := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, e3, f1, f2, g1, r32⟩ := blocks_of L sc
  have r0 := L.ram.1
  have ilen := sc.inputLength
  have xs := sc.inputSmall
  let base := (T.M.observe s).programCounter.toNat
  let s0 := jOfG T s base I.ly
  obtain ⟨j1, j2, j10, j11, j12, j13, j0, jb⟩ := jregs L sc base I.ly
  have hx11 : s0.x 11 = UInt64.ofNat x.length := j11
  have hxl : x.length < 2 ^ 64 := by omega
  have hxm : ∀ i, i < x.length → lbm s0.m ((s0.x 10).toNat + i) = (x.getD i 0).toUInt64 := by
    intro i hi
    obtain ⟨-, hr⟩ := read_some sc.inputLoaded
    show lbm (wordM T.M s) _ = _
    rw [lbm_wordM, j10]; unfold gbM; rw [hr i hi, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  obtain ⟨Cj, pr, S0, Tb, hg, hc18, -, -, -, hwd, hrun⟩ := gen_mainN c hP Ks hO hK2 hXl h hdb s0 x hx11 hxl hxm
  have hv := hB Cj hc18 hg hwd
  let wb := call.workAddress.toNat
  let E0 := (wb + call.workLength) / 8 * 8
  have x12 : (s0.x 12).toNat = wb := by rw [j12]
  have x10 : (s0.x 10).toNat = call.inputAddress.toNat := by rw [j10]
  have x13 : (s0.x 13).toNat = call.outputAddress.toNat := by rw [j13]
  have x11' : (s0.x 11).toNat = x.length := by rw [j11]; simp; omega
  have hE0 : ((s0.x 2 >>> 3) <<< 3).toNat = E0 := by
    rw [j2]
    have : (call.workAddress + call.workLength.toUInt64).toNat = wb + call.workLength := by
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.toUInt64]
      rw [Nat.mod_eq_of_lt (show call.workLength < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, this]
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, E0]; omega
  let KL : LayW := ⟨base, wb, E0, call.inputAddress.toNat, x.length, call.outputAddress.toNat,
    y.length, T.m0 s⟩
  have hb4 : 4 * Cj.length ≤ 2 ^ 20 := by omega
  obtain ⟨vs, H', hSd⟩ := hS Tb
  obtain ⟨y', hSem', hcont⟩ := (hrun KL E0 hE0 j0 (by rw [x12]; exact sc.workAligned) (by rw [x12]; omega)
    (by rw [x12]; omega) (by omega) (fun n off h => by
      have hn := (List.getElem?_eq_some_iff.1 h).1
      have := L.off_le Cj I hv (n + 1) (by omega) (L.vis_link Cj I n off hv h)
      have e : s0.lo (n + 1) = I.off (n + 1) := rfl
      rw [jb, e]; omega) (by rw [x10, x11']; omega)
    (by rw [x10, x11', x12]; omega) (by rw [x12]; exact Nat.le_refl _) (Nat.le_refl _) jb
    (fun i hi => by rw [x11'] at hi; rw [x10]; exact Or.inr (Or.inl ⟨by simp [KL], by simp [KL]; omega⟩))).1
    vs H' (by rw [x12, hx11]; exact hSd)
  rw [hSem] at hSem'; cases hSem'
  obtain ⟨s3, h3, c31, kp, -, e1, e8, e10, e11, hby⟩ := hcont (by rw [x13]; omega) (by rw [x13, x12]; omega)
    (fun i hi => by rw [x13]; exact Or.inr ⟨by simp [KL], by simp [KL]; omega⟩)
  obtain ⟨hl, hR0⟩ := enter L sc hld KL rfl rfl rfl (by simp [KL, E0]; omega) rfl rfl rfl hy hv
  obtain ⟨s', r1, R1⟩ := gsim L hl h3 (L.entry Cj I hv).1 (L.vis_ret Cj I pr hv c31) hR0
  have hra : (s3.x 1).toNat % 4 = 0 := by rw [e1, j1]; exact sc.returnAligned
  obtain ⟨s4, r2, pc4, q10, q11, kept, bytes, frame, cfg⟩ := fin_on L hl R1 (L.vis_ret Cj I pr hv c31) (L.live_ret Cj I pr hv c31) c31 hra kp e8 rfl wb
    (wb + call.workLength) (Nat.le_refl _) (by simp [KL, E0]; omega) y rfl
    (fun i hi => by show lbm s3.m (call.outputAddress.toNat + i) = _; rw [← x13]; exact hby i hi)
  obtain ⟨-, -, -, -, -, -, hst, hol⟩ := L.reg_map
  refine ⟨s4, Runs.trans r1 r2, by rw [pc4, e1, j1], by rw [hst, q10, e10], by rw [hol, q11, e11],
    read_of fun i hi => bytes i hi, fun a ho hw => ?_, kept, cfg⟩
  have := frame a.toNat a.toNat_lt ho hw
  rwa [UInt64.ofNat_toNat] at this

end JT
