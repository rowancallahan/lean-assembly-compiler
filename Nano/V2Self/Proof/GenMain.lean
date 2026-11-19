/- Opus box E: Gen + E's semantics + D's `main_bridge` composed (`gen_main`): on Gen success, a parsed, linear program's
code runs main on Sail-safe steps and returns `Sem κC p x`'s bytes, given that `semAt main` succeeds. -/
import Nano.V2Self.Proof.GenRunS
import Nano.V2Self.Proof.MainBridge15
import Nano.V2Self.Proof.MainOk
namespace Templates
open CallProbe C GenRef ParSpec

/-- the width chain has one def header per def -/
theorem wlen {X : Buf} {ds : List DefA} :
    ∀ {D i hs D'}, WDefs X D i hs D' X.length → ∀ (k : Nat) (r : List DefA), ds.drop k = r →
      SerAt X i (r.flatMap DefA.ser) → X.length = i + (r.flatMap DefA.ser).length → (∀ d ∈ r, DB d) →
      hs.length = r.length
  | _, _, _, _, .nil, k, r, _, _, hX, _ => by
    rcases r with _ | ⟨d, r⟩
    · rfl
    · exfalso; simp [DefA.ser] at hX
  | D, i, _, _, .cons (i1 := i1) t20 hW _ hr, k, r, hdr, sa, hX, hdb => by
    rcases r with _ | ⟨d, r⟩
    · exfalso; simp at hX
      have : tg X i = 0 := by simp [tg, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : X.length ≤ i)]
      rw [this] at t20; exact absurd t20 (by decide)
    obtain ⟨-, -, -, -, -, dnb⟩ := hdb d (by simp)
    simp only [List.flatMap_cons] at sa hX
    obtain ⟨saD, saR⟩ := sa.app
    simp only [DefA.ser] at saD
    obtain ⟨sa1, _⟩ := saD.app
    obtain ⟨_, sb⟩ := sa1.app
    have sbody : SerAt X (i + 6) d.body.ser := by simpa [Nat.add_assoc] using sb
    have e1 : i1 = i + 6 + d.body.ser.length := sk_det (w_sk hW) (ser_sk d.body (i + 6) dnb sbody)
    have := wlen hr (k + 1) r (drop_succ_of hdr)
      (by rw [e1]; simp only [DefA.ser, List.length_append, List.length_cons, List.length_nil] at saR
          rw [show i + 6 + d.body.ser.length + 1 = i + (0 + 1 + 1 + 1 + 1 + 1 + 1 + d.body.ser.length + (0 + 1)) by omega]
          exact saR)
      (by rw [hX, e1]; simp [DefA.ser]; omega) (fun d' h' => hdb d' (by simp [h']))
    simp [this]

theorem hs_len (c : List UInt8) (p : List DefA) (hXl : (serialize p).length < 2 ^ 31) (h : g41 c (serialize p) ≠ [])
    (hdb : ∀ d ∈ p, DB d) {hs T o} (hD : DefsC (serialize p) g_999 bnew 1 (g34 bnew) hs T (serialize p).length o) :
    hs.length = p.length := by
  obtain ⟨-, hs', -, -, D, -, hW, -⟩ := gen41_full c (serialize p) hXl h
  obtain ⟨e, -⟩ := chains hD hW rfl (Nat.le_refl _)
  subst e
  exact wlen hW 0 p rfl (SerAt_serialize p) (by simp [serialize]; omega) hdb

/-- the parser's scoping facts in E's per-def context -/
theorem par_sc {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p) (P : PC) (k : Nat) (hk : k < p.length) :
    ScV (scAt P p k) (dA p k).body ∧ ∀ j, rd (dA p k).body j → j < (dA p k).npw := by
  have hd : p[k]? = some (dA p k) := by rw [NanoMain.dA_get p k hk]; exact List.getElem?_eq_getElem hk
  obtain ⟨a, b, -⟩ := NanoMain.parsed_sc hP k (dA p k) hd (scAt P p k) rfl rfl rfl rfl (fun j hj dj hdj => by
    have hjl : j < p.length := by omega
    have : dA p j = dj := by
      rw [NanoMain.dA_get p j hjl]; rw [List.getElem?_eq_getElem hjl] at hdj; exact Option.some.inj hdj
    simp [scAt, this])
  exact ⟨a, b⟩

/-- **Gen's code runs main as `Sem`**: on g41 success for a parsed program `p` with an ownership witness (kinds ≤ 2), and
input bytes `x` at a0 (a1 = |x|): if `semAt main` succeeds in the work area, then `Sem κC p x = .ok y` and C's code
(safe J steps, simulated on Sail) returns to ra with a1 = |y| and `y` at a3. -/
theorem gen_main (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
    (Ks : List (List Nat)) (hO : OwnSpec.progOk [] [] Ks p = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hXl : (serialize p).length < 2 ^ 31) (h : g41 c (serialize p) ≠ []) (hdb : ∀ d ∈ p, DB d)
    (s0 : St) (x : List UInt8) (hx11 : s0.x 11 = UInt64.ofNat x.length) (hxl : x.length < 2 ^ 64)
    (hxm : ∀ i, i < x.length → lbm s0.m ((s0.x 10).toNat + i) = (x.getD i 0).toUInt64) :
    ∃ (C : List J) (pr S : Nat) (T : Buf),
      let P := pcOf 524288 ((s0.x 12).toNat + 16) (s0.x 11) (NanoMain.inpW x) T
      g41 c (serialize p) = g40 16777216 c (C.map encG) 0 [] ∧ C.length < 2 ^ 18 ∧ At C 0 (stubJ S) ∧
      ∀ (KL : SimW.LayW) E0, ((s0.x 2 >>> 3) <<< 3).toNat = E0 → s0.x 0 = 0 → (s0.x 12).toNat % 8 = 0 →
        (s0.x 12).toNat + 16 ≤ E0 → E0 < 2 ^ 62 → s0.b + 4 * C.length < 2 ^ 64 →
        (s0.x 10).toNat + (s0.x 11).toNat < 2 ^ 63 →
        ((s0.x 10).toNat + (s0.x 11).toNat ≤ (s0.x 12).toNat ∨ E0 ≤ (s0.x 10).toNat) →
        KL.lo ≤ (s0.x 12).toNat → E0 ≤ KL.hi → s0.b = KL.base →
        (∀ i, i < (s0.x 11).toNat → SimW.bok KL ((s0.x 10).toNat + i)) →
        (∀ vs H', semAt P p (p.length - 1) [] E0 ⟨(s0.x 12).toNat + 16, fun _ => none⟩ = some (vs, H') →
        ∃ y, NanoMain.Sem NanoMain.κC p x = .ok y ∧
          ((s0.x 13).toNat + y.length < 2 ^ 64 →
           ((s0.x 13).toNat + y.length ≤ (s0.x 12).toNat ∨ E0 ≤ (s0.x 13).toNat) →
           (∀ i, i < y.length → SimW.sok KL ((s0.x 13).toNat + i)) →
           ∃ s3, SimW.SStarX KL C (0, s0) (pr, s3) ∧ C[pr]? = some (.jalr 0 1) ∧ (∀ j, keepR j = true → s3.x j = s0.x j) ∧ s3.b = s0.b ∧ s3.x 1 = s0.x 1 ∧
             s3.x 8 = s0.x 8 ∧ s3.x 10 = (if y = [] then 1 else 0) ∧ s3.x 11 = UInt64.ofNat y.length ∧
             (∀ i, i < y.length → lbm s3.m ((s0.x 13).toNat + i) = (y.getD i 0).toUInt64) ∧
             (KL.Ok → KL.W = (C.map encG).map UInt64.toNat → ∀ t, SimW.RelW KL (0, s0) t →
               ∃ n t', Proven.Steps n t t' ∧ SimW.RelW KL (pr, s3) t'))) ∧
        (semAtF P p (p.length - 1) [] E0 ⟨(s0.x 12).toNat + 16, fun _ => none⟩ = .error .cap →
         ∃ s2, SimW.SStarX KL C (0, s0) (6, s2) ∧ s2.m (s0.x 12).toNat = s0.x 1 ∧
           s2.m ((s0.x 12).toNat + 8) = s0.x 8 ∧ s2.x 0 = 0 ∧ (∀ j, keepR j = true → s2.x j = s0.x j) ∧ s2.b = s0.b ∧
           (KL.Ok → KL.W = (C.map encG).map UInt64.toNat → ∀ t, SimW.RelW KL (0, s0) t →
             ∃ n t', Proven.Steps n t t' ∧ SimW.RelW KL (6, s2) t')) := by
  have hx11' : (s0.x 11).toNat = x.length := by rw [hx11]; exact NanoMain.toNat_ofNat_lt hxl
  obtain ⟨hs, T, o, hD, hne, hg, hc18, hst, hrun⟩ := gen_runS c p hXl h hdb s0 (NanoMain.inpW x)
    (fun i hi => by rw [hx11'] at hi; exact hxm i hi)
  have hsl := hs_len c p hXl h hdb hD
  refine ⟨_, 11 + (defsJ (pcOf 524288 ((s0.x 12).toNat + 16) (s0.x 11) (NanoMain.inpW x) T) p 0 hs.length).length + 31, _, T, hg, hc18, hst, ?_⟩
  intro KL E0 hE0 z0 ha8 hroom hE62 hcb hin63 hin hlo hhi hbase hinw
  have hR := hrun KL (fun k hk => par_sc hP _ k (by omega)) E0 hE0 z0 ha8 hroom hE62 hcb hin63 hin hlo hhi hbase hinw
  refine ⟨fun vs H' hSd => ?_, fun hSd => hR.2 (by rw [hsl]; exact hSd)⟩
  obtain ⟨sigs, hTy⟩ := NanoMain.refParse_ty hP
  obtain ⟨a, l, rfl, hB, hS⟩ := NanoMain.main_bridge _ p sigs Ks x hTy hO hK2 hx11 rfl hxl E0 _ _ _
    (by show ((s0.x 12).toNat + 16) % 8 = 0; omega) (Nat.le_refl _) hSd
  refine ⟨_, hS, fun hQ hout hwO => ?_⟩
  obtain ⟨b1, b2, b3, -, hll, -, hm0, -, hcell⟩ := hB
  simp only [List.length_map] at hQ hout hwO ⊢
  have hll' : l.length < 2 ^ 64 := by omega
  have hN := NanoMain.toNat_ofNat_lt hll'
  obtain ⟨s3, h3, c31, kp, r1, r2, r3, r4, r5, r6, r7⟩ := hR.1 [a] H' (by rw [hsl]; exact hSd) (UInt64.ofNat l.length) (fun i => l.getD i 0) hm0 b1 (by simp only [List.getD_cons_zero]; omega)
    (fun i hi => by rw [hN] at hi; simp only [List.getD_cons_zero]; rw [hcell i (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)])
    (by rw [hN]; exact hQ) (by rw [hN]; exact hout) (fun i hi => by rw [hN] at hi; exact hwO i hi)
  refine ⟨s3, h3, c31, kp, r1, r2, r3, ?_, r5, fun i hi => ?_, r7⟩
  · rw [r4]
    rcases l with _ | ⟨b, l⟩
    · rfl
    · have : UInt64.ofNat (b :: l).length ≠ 0 := fun e => by
        have := congrArg UInt64.toNat e; rw [hN] at this; simp at this
      rw [if_neg this, if_neg (by simp)]
  · rw [r6 i (by rw [hN]; exact hi)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
      Option.getD_some]
    rw [← UInt64.toNat_inj]
    simp [UInt64.toNat_and, Nat.and_two_pow_sub_one_eq_mod _ 8]

end Templates
