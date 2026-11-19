/- Machine bridge (Opus box E): the program's words.  Along A's def chain `DefsC` (Proof/GenTop.lean), every def's
code is its template: `chainW` — for the resolved program `ds` serialized in X, the code after the def phase is the
code before it followed by `(defsJ P ds k n).map encG`, the def templates back to back, each at its table start word. -/
import Nano.V2Self.Proof.NdProg
import Nano.V2Self.Proof.GenTop
namespace Templates
open CallProbe C GenRef ParSpec

/-- the def templates of defs k … k+n−1, back to back -/
def defsJ (P : PC) (ds : List DefA) : Nat → Nat → List J
  | _, 0 => []
  | k, n + 1 => defT (scAt P ds k) (dA ds k).body (P.T k) (dA ds k).nres ++ defsJ P ds (k + 1) n

/-- field bounds of a def -/
def DB (d : DefA) : Prop := d.id < 2 ^ 32 ∧ d.npw < 2 ^ 32 ∧ d.nslots < 2 ^ 32 ∧ d.kind < 2 ^ 32 ∧ d.nres < 2 ^ 32 ∧
  NB d.npw d.body

theorem DefsC.prefix {X : Buf} {u : UInt64} : ∀ {T i o hs T' i' o'}, DefsC X u T i o hs T' i' o' →
    T' = T ++ T'.drop T.length ∧ T'.length = T.length + hs.length
  | _, _, _, _, _, _, _, .nil => ⟨by simp, by simp⟩
  | T, _, o, _, _, _, _, .cons _ hr => by
    obtain ⟨h1, h2⟩ := DefsC.prefix hr
    simp only [bpush, List.length_append, List.length_cons, List.length_nil] at h1 h2
    refine ⟨?_, by simp; omega⟩
    rw [h1]; simp

theorem DefC.olen {X : Buf} {u : UInt64} {T : Buf} {i : Nat} {o o' : Buf} {i' : Nat} (h : DefC X u T i o o' i') :
    o.length ≤ o'.length := by
  obtain ⟨_, _, _, _, _, c, _, E, _, _, _, rfl, _⟩ := h
  rw [pi_g29 512 _ _ 0 _]
  simp only [List.length_append, bpush, patchR_len, List.length_cons, List.length_nil]
  rw [pi_pro _ _ o]; simp; omega

theorem DefsC.olen {X : Buf} {u : UInt64} : ∀ {T i o hs T' i' o'}, DefsC X u T i o hs T' i' o' → o.length ≤ o'.length
  | _, _, _, _, _, _, _, .nil => Nat.le_refl _
  | _, _, _, _, _, _, _, .cons hd hr => Nat.le_trans (DefC.olen hd) (DefsC.olen hr)

theorem dA_of_drop {ds : List DefA} {k : Nat} {d : DefA} {r : List DefA} (h : ds.drop k = d :: r) : dA ds k = d := by
  have : ds[k]? = some d := by rw [← List.head?_drop, h]; rfl
  simp [dA, List.getD_eq_getElem?_getD, this]

theorem drop_succ_of {ds : List DefA} {k : Nat} {d : DefA} {r : List DefA} (h : ds.drop k = d :: r) :
    ds.drop (k + 1) = r := by
  rw [← List.drop_drop, h]; rfl

/-- **the def phase's words**: along the chain, the code grows by the def templates -/
theorem chainW {X : Buf} {u : UInt64} {P : PC} {ds : List DefA} (hκ : P.κ = u.toNat) {Tf : Buf}
    (hT : ∀ j, P.T j = (bget Tf j.toUInt64).toNat) :
    ∀ {T i o hs T' i' o'}, DefsC X u T i o hs T' i' o' → T' = Tf → ∀ r : List DefA, ds.drop T.length = r →
      SerAt X i (r.flatMap DefA.ser) → X.length = i + (r.flatMap DefA.ser).length → (∀ d ∈ r, DB d) →
      (∀ v ∈ T, v.toNat ≤ o.length) → T.length ≤ o.length → o'.length < 2 ^ 24 →
      o' = o ++ (defsJ P ds T.length hs.length).map encG ∧
      (∀ j, j < hs.length → P.T (T.length + j) = o.length + (defsJ P ds T.length j).length) ∧
      (∀ j, j < hs.length → tg X (hs.getD j 0 + 2) = (dA ds (T.length + j)).npw.toUInt64 ∧
        tg X (hs.getD j 0 + 5) = (dA ds (T.length + j)).nres.toUInt64 ∧ OpV (dA ds (T.length + j)).body) ∧
      ∀ j, j < hs.length → (dA ds (T.length + j)).npw < 251 ∧ (dA ds (T.length + j)).nslots < 251 ∧
        (dA ds (T.length + j)).nres < 251 ∧ (dA ds (T.length + j)).npw ≤ (dA ds (T.length + j)).nslots
  | _, _, _, _, _, _, _, .nil, _, _, _, _, _, _, _, _, _ => by simp [defsJ]
  | T, i, o, _, T', _, o', .cons (o1 := o1) (i1 := i1) (hs := hs) hD hr, eT, r, hdr, sa, hX, hdb, hTo, hTl, hlen => by
    subst eT
    -- the def in the AST
    rcases r with _ | ⟨d, r⟩
    · exfalso
      have t20 := hD.1
      simp at hX
      have : tg X i = 0 := by simp [tg, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : X.length ≤ i)]
      rw [this] at t20; exact absurd t20 (by decide)
    have hd : dA ds T.length = d := dA_of_drop hdr
    obtain ⟨did, dnp, dns, dk, dnr, dnb⟩ := hdb d (by simp)
    simp only [List.flatMap_cons, DefA.ser] at sa hX
    obtain ⟨sa1, sa2⟩ := sa.app
    obtain ⟨sa3, _⟩ := sa1.app
    obtain ⟨sh, sb⟩ := sa3.app
    have th : ∀ j, j < 6 → tg X (i + j) = [20, d.id.toUInt64, d.npw.toUInt64, d.nslots.toUInt64, d.kind.toUInt64,
        d.nres.toUInt64].getD j 0 := fun j hj => sh j (by simp; omega)
    have t2 : tg X (i + 2) = d.npw.toUInt64 := th 2 (by omega)
    have t3 : tg X (i + 3) = d.nslots.toUInt64 := th 3 (by omega)
    have t5 : tg X (i + 5) = d.nres.toUInt64 := th 5 (by omega)
    -- the table
    obtain ⟨pf, _⟩ := DefsC.prefix hr
    have hb : ∀ n : Nat, n.toUInt64 < bsize (bpush T (bsize o)) →
        bget (bpush T (bsize o)) n.toUInt64 = bget T' n.toUInt64 := by
      intro n hn
      rw [pf]; simp only [bget, List.getD_eq_getElem?_getD]
      have hl0 := DefsC.olen hr; have hl1 := DefC.olen hD
      rw [List.getElem?_append_left (by
        simp only [bsize, bpush, List.length_append, List.length_singleton, UInt64.lt_iff_toNat_lt] at hn
        simp only [bpush, List.length_append, List.length_singleton]
        simp [Nat.toUInt64] at hn ⊢; rw [Nat.mod_eq_of_lt (show T.length + 1 < 2 ^ 64 by omega)] at hn; omega)]
    have hlo := DefsC.olen hr
    have SKk : SK (scAt P ds T.length) (dK X u (bpush T (bsize o)) i) := {
      p := by show (dA ds T.length).npw = (tg X (i + 2)).toNat; rw [hd, t2, toU_lt _ dnp]
      κ := by show P.κ = u.toNat; exact hκ
      T := fun n hn => by
        show P.T n = (bget (bpush T (bsize o)) n.toUInt64).toNat; rw [hT n, hb n hn]
      Tb := fun n hn => by
        show (bget (bpush T (bsize o)) n.toUInt64).toNat < 2 ^ 32
        simp only [bget, bpush, List.getD_eq_getElem?_getD]
        rcases h : (T ++ [bsize o])[n.toUInt64.toNat]? with _ | v
        · simp
        · simp only [Option.getD_some]
          have hv := List.mem_of_getElem? h
          simp only [List.mem_append, List.mem_singleton] at hv
          rcases hv with hv | hv
          · have := hTo v hv; have := DefC.olen hD; omega
          · subst hv; simp [bsize]; have := DefC.olen hD; omega
      p251 := by show tg X (i + 2) < 251; have q1 := hD.2.2.1; have q2 := hD.2.1
                 rw [UInt64.lt_iff_toNat_lt] at q1 q2 ⊢; rw [UInt64.toNat_add] at q1; simp at q1; omega
      ns251 := hD.2.1 }
    have hw := defWords hD SKk (by show (dA ds T.length).nslots = _; rw [hd, t3, toU_lt _ dns])
      (by show NB (dA ds T.length).npw (dA ds T.length).body; rw [hd]; exact dnb)
      (by simpa [Nat.add_assoc, hd] using sb) (by omega)
    obtain ⟨ei1, eo1, hop⟩ := hw
    -- the rest of the chain
    have ih := chainW hκ hT hr rfl r (by simp only [bpush, List.length_append, List.length_singleton]; exact drop_succ_of hdr)
      (by simp only [List.length_append, List.length_cons, List.length_nil] at sa2
          rw [ei1, hd, show i + 6 + d.body.ser.length + 1 = i + (0 + 1 + 1 + 1 + 1 + 1 + 1 + d.body.ser.length + (0 + 1))
            by omega]; exact sa2)
      (by rw [ei1, hX, hd]; simp; omega) (fun d' hd' => hdb d' (by simp [hd']))
      (by intro v hv; simp only [bpush, List.mem_append, List.mem_singleton] at hv
          rcases hv with hv | hv
          · have := hTo v hv; have := DefC.olen hD; omega
          · subst hv; simp [bsize]; have := DefC.olen hD; omega)
      (by rw [eo1]; simp [bpush, defT, proA, pushA, push]; omega) hlen
    have hl0 := DefsC.olen hr
    have hl1 := DefC.olen hD
    have pT : P.T T.length = o.length := by
      rw [hT, ← hb T.length (by
        simp only [bsize, bpush, List.length_append, List.length_singleton, UInt64.lt_iff_toNat_lt]
        simp [Nat.toUInt64]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
      have : T.length.toUInt64.toNat = T.length := by simp [Nat.toUInt64]; omega
      simp only [bget, bpush, List.getD_eq_getElem?_getD, this]
      simp [bsize, Nat.toUInt64]; omega
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    have b3 : d.nslots < 251 := by
      have q := hD.2.1; rw [t3, UInt64.lt_iff_toNat_lt, toU_lt _ dns] at q; exact q
    have b5 : d.nres < 251 := by
      have q := hD.2.2.2.1; rw [t5, UInt64.lt_iff_toNat_lt, toU_lt _ dnr] at q; exact q
    have b2 : d.npw ≤ d.nslots := by
      have q := hD.2.2.1; rw [t2, t3, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, toU_lt _ dnp, toU_lt _ dns] at q
      simp at q; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ih1, eo1]
      simp only [bpush, List.length_append, List.length_singleton, List.length_cons, defsJ, hd, t5, toU_lt _ dnr, pT,
        List.map_append, List.append_assoc, List.length_nil, Nat.zero_add]
    · intro j hj
      rcases j with _ | j
      · simp [defsJ, pT]
      · have q := ih2 j (by simpa using hj)
        simp only [bpush, List.length_append, List.length_singleton] at q
        rw [show T.length + (j + 1) = T.length + 1 + j by omega, q, eo1]
        simp [defsJ, hd, t5, toU_lt _ dnr, pT]; omega
    · intro j hj
      rcases j with _ | j
      · simp only [List.getD_cons_zero, Nat.add_zero, hd]; exact ⟨t2, t5, by rw [← hd]; exact hop⟩
      · have q := ih3 j (by simpa using hj)
        simp only [bpush, List.length_append, List.length_singleton] at q
        rw [show T.length + (j + 1) = T.length + 1 + j by omega]; simpa using q
    · intro j hj
      rcases j with _ | j
      · simp only [Nat.add_zero, hd]; exact ⟨by omega, b3, b5, b2⟩
      · have q := ih4 j (by simpa using hj)
        simp only [bpush, List.length_append, List.length_singleton] at q
        rw [show T.length + (j + 1) = T.length + 1 + j by omega]; exact q

end Templates
