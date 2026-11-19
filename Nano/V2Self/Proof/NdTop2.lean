/- Machine bridge (Opus box E): the J-level program theorem with the width facts discharged by A's width pass
(`gen41_full`: code chain DefsC and width chain WDefs).  Remaining hypotheses are the parser's: field bounds `DB`,
scoping `ScV`, body reads ⊆ parameters, npw ≤ nslots, npw < 2^20 — and `o.length < 2^24` (Gen's code-size check). -/
import Nano.V2Self.Proof.NdTop
import Nano.V2Self.Proof.NdWidthB
import Nano.V2Self.Proof.GenAll
namespace Templates
open CallProbe C GenRef ParSpec

/-- the width-pass def table after k defs -/
def dD (ds : List DefA) (k : Nat) : List (UInt64 × UInt64) :=
  (ds.take k).map fun d => (d.npw.toUInt64, d.nres.toUInt64)

theorem dD_len (ds : List DefA) (k : Nat) (hk : k ≤ ds.length) : (dD ds k).length = k := by
  simp [dD]; omega

theorem dD_get (ds : List DefA) (k n : Nat) (hn : n < k) (hk : k ≤ ds.length) :
    (dD ds k).getD n (0, 0) = ((dA ds n).npw.toUInt64, (dA ds n).nres.toUInt64) := by
  simp [dD, dA, List.getD_eq_getElem?_getD, List.getElem?_take, hn]
  rw [List.getElem?_eq_getElem (by omega)]; simp

theorem dD_succ (ds : List DefA) (k : Nat) (hk : k < ds.length) :
    dD ds (k + 1) = dD ds k ++ [((dA ds k).npw.toUInt64, (dA ds k).nres.toUInt64)] := by
  simp only [dD, dA]
  rw [List.take_succ, List.map_append]
  rw [List.getElem?_eq_getElem hk]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem Sk.cast' {X : Buf} {i a b : Nat} (h : Sk X i a) (e : a = b) : Sk X i b := e ▸ h
theorem Sks.cast' {X : Buf} {i n a b : Nat} (h : Sks X i n a) (e : a = b) : Sks X i n b := e ▸ h

mutual
theorem ser_sk {X : Buf} {pp : Nat} : ∀ (e : Nd) (i : Nat), NB pp e → SerAt X i e.ser → Sk X i (i + e.ser.length)
  | .const v, i, _, sa => by
    simp only [Nd.ser] at sa ⊢; exact .const sa.cons.1
  | .loc s w, i, _, sa => by
    simp only [Nd.ser] at sa ⊢; exact .local sa.cons.1
  | .bin op a b, i, nb, sa => by
    simp only [Nd.ser] at sa ⊢; simp only [NB] at nb
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons; obtain ⟨sA, sB⟩ := sa2.app
    have hA := ser_sk a _ nb.2.1 sA
    have hB := ser_sk b _ nb.2.2 sB
    have := Sk.bin t0 (by simpa using hA) (by simpa [Nat.add_assoc] using hB)
    exact Sk.cast' this (by simp; omega)
  | .ite cm a b t e, i, nb, sa => by
    simp only [Nd.ser] at sa ⊢; simp only [NB] at nb
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons
    obtain ⟨sa3, sE⟩ := sa2.app; obtain ⟨sa4, sT⟩ := sa3.app; obtain ⟨sA, sB⟩ := sa4.app
    have hA := ser_sk a _ nb.2.1 sA; have hB := ser_sk b _ nb.2.2.1 sB
    have hT := ser_sk t _ nb.2.2.2.1 sT; have hE := ser_sk e _ nb.2.2.2.2 sE
    have := Sk.ite t0 (by simpa using hA) (by simpa [Nat.add_assoc] using hB) (by simpa [Nat.add_assoc] using hT)
      (by simpa [Nat.add_assoc] using hE)
    exact Sk.cast' this (by simp; omega)
  | .letE s w v b, i, nb, sa => by
    simp only [Nd.ser] at sa ⊢; simp only [NB] at nb
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons; obtain ⟨_, sa3⟩ := sa2.cons
    obtain ⟨sV, sB⟩ := sa3.app
    have hV := ser_sk v _ nb.2.2.1 sV; have hB := ser_sk b _ nb.2.2.2 sB
    have := Sk.lett t0 (by simpa using hV) (by simpa [Nat.add_assoc] using hB)
    exact Sk.cast' this (by simp; omega)
  | .pair cs, i, nb, sa => by
    simp only [Nd.ser] at sa ⊢; simp only [NB] at nb
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨t1, sa2⟩ := sa1.cons
    have hL := serL_sks cs _ nb.2 sa2
    exact .pair t0 (by rw [t1, toU_lt _ nb.1]; exact Sks.cast' hL (by simp; omega))
  | .call n as, i, nb, sa => by
    simp only [Nd.ser] at sa ⊢; simp only [NB] at nb
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons; obtain ⟨t2, sa3⟩ := sa2.cons
    have hL := serL_sks as _ nb.2.2 sa3
    exact .call t0 (by rw [t2, toU_lt _ nb.2.1]; exact Sks.cast' hL (by simp; omega))
  | .prim pn as, i, nb, sa => by
    simp only [Nd.ser] at sa ⊢; simp only [NB] at nb
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨t1, sa2⟩ := sa1.cons
    have hL := serL_sks as _ nb.2.2 sa2
    exact .prim t0 (by rw [t1, ← nb.2.1]; exact Sks.cast' hL (by simp; omega))
  | .loop z s, i, nb, sa => by
    simp only [Nd.ser] at sa ⊢; simp only [NB] at nb
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨sZ, sS⟩ := sa1.app
    have hZ := ser_sk z _ nb.1 sZ; have hS := ser_sk s _ nb.2 sS
    have := Sk.loop t0 hZ (by simpa [Nat.add_assoc] using hS)
    exact Sk.cast' this (by simp; omega)
  | .cont e, i, nb, sa => by
    simp only [Nd.ser] at sa ⊢; simp only [NB] at nb
    obtain ⟨t0, sE⟩ := sa.cons
    have := Sk.cont t0 (ser_sk e _ nb.2 sE)
    exact Sk.cast' this (by simp; omega)
theorem serL_sks {X : Buf} {pp : Nat} : ∀ (cs : List Nd) (i : Nat), NBL pp cs → SerAt X i (serL cs) →
    Sks X i cs.length (i + (serL cs).length)
  | [], i, _, _ => by simpa [serL] using (Sks.nil : Sks X i 0 i)
  | c :: cs, i, nb, sa => by
    simp only [serL] at sa ⊢; simp only [NBL] at nb
    obtain ⟨s1, s2⟩ := sa.app
    have h1 := ser_sk c _ nb.1 s1
    have h2 := serL_sks cs _ nb.2 s2
    have := Sks.cons h1 h2
    exact Sks.cast' this (by simp; omega)
end

/-- along the width chain, every def body has width relation W in its context -/
theorem wchain {X : Buf} {ds : List DefA} :
    ∀ {D i hs D' i'}, WDefs X D i hs D' i' → ∀ (k : Nat) (r : List DefA), ds.drop k = r → D = dD ds k →
      k + r.length = ds.length →
      SerAt X i (r.flatMap DefA.ser) → X.length = i + (r.flatMap DefA.ser).length → (∀ d ∈ r, DB d) →
      ∀ j, j < hs.length → ∃ i0, SerAt X i0 (dA ds (k + j)).ser ∧
        W X (dD ds (k + j + 1)) (dA ds (k + j)).npw.toUInt64 (dA ds (k + j)).nres.toUInt64 true (i0 + 6)
          (dA ds (k + j)).nres.toUInt64 (i0 + 6 + (dA ds (k + j)).body.ser.length)
  | _, _, _, _, _, .nil, _, _, _, _, _, _, _, _, j, hj => absurd hj (by simp)
  | D, i, _, _, _, .cons (i1 := i1) t20 hW t21 hr, k, r, hdr, hD, hkl, sa, hX, hdb, j, hj => by
    rcases r with _ | ⟨d, r⟩
    · exfalso; simp at hX
      have : tg X i = 0 := by simp [tg, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : X.length ≤ i)]
      rw [this] at t20; exact absurd t20 (by decide)
    have hd : dA ds k = d := dA_of_drop hdr
    have hkd : k < ds.length := by simp at hkl; omega
    obtain ⟨did, dnp, dns, dk, dnr, dnb⟩ := hdb d (by simp)
    simp only [List.flatMap_cons] at sa hX
    obtain ⟨saD, saR⟩ := sa.app
    have saD' := saD
    simp only [DefA.ser] at saD
    obtain ⟨sa1, _⟩ := saD.app
    obtain ⟨sh, sb⟩ := sa1.app
    have th : ∀ m, m < 6 → tg X (i + m) = [20, d.id.toUInt64, d.npw.toUInt64, d.nslots.toUInt64, d.kind.toUInt64,
        d.nres.toUInt64].getD m 0 := fun m hm => sh m (by simp; omega)
    have t2 : tg X (i + 2) = d.npw.toUInt64 := th 2 (by omega)
    have t5 : tg X (i + 5) = d.nres.toUInt64 := th 5 (by omega)
    rw [t2, t5] at hW
    -- the end of this def's body
    have sbody : SerAt X (i + 6) d.body.ser := by simpa [Nat.add_assoc] using sb
    have e1 : i1 = i + 6 + d.body.ser.length := sk_det (w_sk hW) (ser_sk d.body (i + 6) dnb sbody)
    have hD1 : D ++ [(d.npw.toUInt64, d.nres.toUInt64)] = dD ds (k + 1) := by rw [hD, dD_succ ds k hkd, hd]
    rcases j with _ | j
    · refine ⟨i, by rw [Nat.add_zero, hd]; exact saD', ?_⟩
      simp only [Nat.add_zero]; rw [hd, ← hD1, ← e1]; exact hW
    · have := wchain hr (k + 1) r (drop_succ_of hdr) (by rw [t2, t5]; exact hD1) (by simp at hkl; omega)
        (by rw [e1]; simp only [DefA.ser, List.length_append, List.length_cons, List.length_nil] at saR
            rw [show i + 6 + d.body.ser.length + 1 = i + (0 + 1 + 1 + 1 + 1 + 1 + 1 + d.body.ser.length + (0 + 1)) by omega]
            exact saR)
        (by rw [hX, e1]; simp [DefA.ser]; omega) (fun d' h' => hdb d' (by simp [h'])) j (by simpa using hj)
      rw [show k + (j + 1) = k + 1 + j by omega]; exact this

theorem dD_get' (ds : List DefA) (k n : Nat) (hn : n < (dD ds k).length) :
    (dD ds k).getD n (0, 0) = ((dA ds n).npw.toUInt64, (dA ds n).nres.toUInt64) := by
  simp only [dD, List.length_map, List.length_take] at hn
  simp [dD, dA, List.getD_eq_getElem?_getD, List.getElem?_take, show n < k by omega]
  rw [List.getElem?_eq_getElem (by omega)]; simp

theorem h251_dA {ds : List DefA} (h : ∀ d ∈ ds, d.npw < 251 ∧ d.nres < 251) (k : Nat) :
    (dA ds k).npw < 251 ∧ (dA ds k).nres < 251 := by
  unfold dA
  rcases Nat.lt_or_ge k ds.length with hk | hk
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; simp

theorem mem_ser_le : ∀ {ds : List DefA} {d : DefA}, d ∈ ds → d.ser.length ≤ (ds.flatMap DefA.ser).length
  | [], _, h => by simp at h
  | x :: xs, d, h => by
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with e | e
    · subst e; omega
    · have := mem_ser_le e; omega

theorem body_ser_lt (ds : List DefA) (hX : (serialize ds).length < 2 ^ 31) (k : Nat) :
    (dA ds k).body.ser.length < 2 ^ 31 := by
  unfold dA
  rcases Nat.lt_or_ge k ds.length with hk | hk
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; simp only [Option.getD_some]
    have := mem_ser_le (List.getElem_mem hk)
    simp [DefA.ser, serialize] at this hX; omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; simp [Nd.ser]

theorem DB_dA {ds : List DefA} (hdb : ∀ d ∈ ds, DB d) (k : Nat) : DB (dA ds k) := by
  unfold dA
  rcases Nat.lt_or_ge k ds.length with hk | hk
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact hdb _ (List.getElem_mem hk)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; simp [DB, NB]

/-- **the J-level program theorem**: Gen's success on the serialized program gives its code (stubs ++ def templates)
and, on any J program holding those templates, every def — main included — runs per its machine-level semantics.
Widths come from Gen's width pass; the remaining hypotheses are the parser's. -/
theorem gen_top (c : List UInt8) (ds : List DefA) (hXl : (serialize ds).length < 2 ^ 31)
    (h : g41 c (serialize ds) ≠ []) (hdb : ∀ d ∈ ds, DB d)
    (hb : Nat) (c29 : UInt64) (inp : Nat → UInt64) :
    ∃ hs T o, DefsC (serialize ds) g_999 bnew 1 (g34 bnew) hs T (serialize ds).length o ∧ hs ≠ [] ∧
      g41 c (serialize ds) = g40 16777216 c (startW (bset o 0 (g13 0 0 (bsize o))) (bget T (bsize T - 1))) 0 [] ∧
      tg (serialize ds) (hs.getLastD 0 + 2) = 0 ∧ tg (serialize ds) (hs.getLastD 0 + 5) = 1 ∧
      (o.length < 2 ^ 24 →
        o = g34 bnew ++ (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length).map encG ∧
        (∀ j, j < hs.length → tg (serialize ds) (hs.getD j 0 + 2) = (dA ds j).npw.toUInt64 ∧
          tg (serialize ds) (hs.getD j 0 + 5) = (dA ds j).nres.toUInt64 ∧ OpV (dA ds j).body) ∧
        (∀ j, j < hs.length → (dA ds j).npw < 251 ∧ (dA ds j).nslots < 251 ∧ (dA ds j).nres < 251 ∧
          (dA ds j).npw ≤ (dA ds j).nslots) ∧
        (∀ j, j < hs.length → (pcOf 524288 hb c29 inp T).T j =
          (g34 bnew).length + (defsJ (pcOf 524288 hb c29 inp T) ds 0 j).length) ∧
        (∀ k, k < hs.length → ScV (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body →
          OkV (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body ∧
          wd (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body = (dA ds k).nres) ∧
        ∀ (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64), IGOK hb E0 IG → E0 < 2 ^ 62 →
          (∀ s, IG s → s.b + 4 * C.length < 2 ^ 64) → InpOK IG c28 c29 inp →
          At C (g34 bnew).length (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length) →
          (∀ k, k < hs.length → (dA ds k).npw < 2 ^ 20 ∧ (dA ds k).npw ≤ (dA ds k).nslots ∧
            ScV (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body ∧ ∀ j, rd (dA ds k).body j → j < (dA ds k).npw) →
          ∀ k, k < hs.length → DefX C ((pcOf 524288 hb c29 inp T).T k) (dA ds k).npw (dA ds k).nres IG hb E0
            (semAt (pcOf 524288 hb c29 inp T) ds k)) := by
  obtain ⟨_, hs, T, o, D, hD, hW, hne, l2, l5, hg⟩ := gen41_full c (serialize ds) hXl h
  refine ⟨hs, T, o, hD, hne, hg, l2, l5, fun hol => ?_⟩
  have cw := chainW (P := pcOf 524288 hb c29 inp T) (ds := ds) (u := g_999) rfl (Tf := T) (fun j => rfl) hD rfl ds
    (by simp [bnew]) (SerAt_serialize ds) (by simp [serialize]; omega) hdb (by simp [bnew]) (by simp [bnew]) hol
  simp only [bnew, List.length_nil, Nat.zero_add] at cw
  have perK : ∀ k, k < hs.length → ScV (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body →
      OkV (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body ∧
      wd (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body = (dA ds k).nres := by
    intro k hk hsc
    have wc := wchain (ds := ds) hW 0 ds (by simp) (by simp [dD]) (by simp) (SerAt_serialize ds)
      (by simp [serialize]; omega) hdb k hk
    simp only [Nat.zero_add] at wc
    obtain ⟨i0, sa0, hWk⟩ := wc
    obtain ⟨_, dnp, dns, _, dnr, dnb⟩ := DB_dA hdb k
    obtain ⟨p251, -, q251, -⟩ := by simpa using cw.2.2.2 k hk
    have hK : WK (scAt (pcOf 524288 hb c29 inp T) ds k) (dD ds (k + 1)) (dA ds k).npw.toUInt64
        (dA ds k).nres.toUInt64 := {
      ep := by show (dA ds k).npw = _; rw [toU_lt _ dnp]
      eq := by show (dA ds k).nres = _; rw [toU_lt _ dnr]
      q251 := by rw [toU_lt _ dnr]; exact q251
      p251 := by rw [toU_lt _ dnp]; exact p251
      npw := fun n hn => by
        show (dA ds n).npw = _; rw [dD_get' ds _ n hn]; exact (toU_lt _ (DB_dA hdb n).2.1).symm
      nres := fun n hn => by
        show (dA ds n).nres = _; rw [dD_get' ds _ n hn]; exact (toU_lt _ (DB_dA hdb n).2.2.2.2.1).symm
      r32 := fun n => (DB_dA hdb n).2.2.2.2.1 }
    simp only [DefA.ser] at sa0
    have sb : SerAt (serialize ds) (i0 + 6) (dA ds k).body.ser := by
      obtain ⟨sa1, _⟩ := sa0.app; obtain ⟨_, sb⟩ := sa1.app; simpa using sb
    have bl := body_ser_lt ds hXl k
    obtain ⟨_, wdv, ew⟩ := wV hK (dA ds k).body true (i0 + 6) _ _ dnb hsc sb hWk bl
    have lw := wd_lt hK (dA ds k).body dnb bl
    have ewd : wd (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body = (dA ds k).nres :=
      ofNat_inj' (by simpa [Nat.toUInt64] using ew) (by omega) (by omega)
    exact ⟨okV_of _ _ wdv hsc, ewd⟩
  refine ⟨cw.1, by simpa using cw.2.2.1, by simpa using cw.2.2.2, cw.2.1, perK, fun C IG E0 c28 hig he hcb hinp hC hpar k hk => ?_⟩
  exact gen_defs_run _ ds C IG E0 c28 hs.length (g34 bnew).length hig he hcb hinp hC cw.2.1
    (fun k' hk' => by
      obtain ⟨hpw', hpn', hsc', hrd'⟩ := hpar k' hk'
      exact ⟨hpw', hpn', (perK k' hk' hsc').1, (perK k' hk' hsc').2, hrd'⟩) k hk

end Templates
