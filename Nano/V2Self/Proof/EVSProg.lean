/- Safe retrofit (EVS) P6b: defs and the program with SafeX runs (Opus box E): `defRunS`, `progRunS` (every def k < N
satisfies `DefXS` for `semAt`, callee-first), `gen_defs_runS` (on any J program holding Gen's def templates). -/
import Nano.V2Self.Proof.EVSRun
import Nano.V2Self.Proof.NdTop
namespace Templates
open CallProbe SimW SafeRun ParSpec

theorem At.len {C : List J} {pos : Nat} {l : List J} (h : At C pos l) (hl : l ≠ []) : pos + l.length ≤ C.length := by
  have hp : 0 < l.length := List.length_pos_iff.mpr hl
  have := h (l.length - 1) (by omega)
  rcases Nat.lt_or_ge (pos + (l.length - 1)) C.length with q | q
  · omega
  · rw [List.getElem?_eq_none q, List.getElem?_eq_getElem (by omega)] at this; simp at this

theorem defT_ne (S : SC) (e : Nd) (f q : Nat) : defT S e f q ≠ [] := by simp [defT, proA, pushA, push]

theorem defRunS {S : SC} {C : List J} {IG : St → Prop} {E0 : Nat} {c28 : UInt64} {KL : LayW}
    (X : RunCxS S C IG E0 c28 KL) {e : Nd} {f q : Nat} (ok : OkV S e) (hop : OpV e) (hw : wd S e = q)
    (hR : ∀ k, rd e k → k < S.p) (hpn : S.p ≤ S.nl) (hq : q < 251) (hC : At C f (defT S e f q)) :
    DefXS KL C f S.p q IG S.hb E0 (defS S.p S.nl (sv S e)) := by
  have hl := At.len hC (defT_ne S e f q)
  obtain ⟨hP, hB, hE⟩ := At.mid hC
  have lp : (proA 1 f (S.nl - S.p)).length = 12 := by simp [proA, pushA, push]
  rw [lp] at hB hE; rw [tm_len] at hE
  have le : 1 ≤ (epi S.p q).length := by simp [epi]
  simp only [defT, List.length_append, lp, tm_len] at hl
  exact defXS X.ig hP ((runVS X e (f + 12) ok hop hB (by omega)).wid hw) hE hpn hR X.nl251 (by omega)

/-- the per-def facts of the safe program theorem -/
structure DefOKS (P : PC) (ds : List DefA) (C : List J) (k : Nat) : Prop where
  base : DefOK P ds C k
  op : OpV (dA ds k).body
  nl : (dA ds k).nslots < 251
  q : (dA ds k).nres < 251

theorem progRunS (P : PC) (ds : List DefA) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64) (KL : LayW)
    (hig : IGOK P.hb E0 IG) (he : E0 < 2 ^ 62) (hcb : ∀ s, IG s → s.b + 4 * C.length < 2 ^ 64)
    (hinp : InpOK IG c28 P.c29 P.inp) (hinw : InpW KL IG) (hc18 : C.length < 2 ^ 18) (N : Nat)
    (hd : ∀ k, k < N → DefOKS P ds C k) :
    ∀ k, k < N → DefXS KL C (P.T k) (dA ds k).npw (dA ds k).nres IG P.hb E0 (semAt P ds k) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    have D := hd k hk
    have X : RunCxS (scAt P ds k) C IG E0 c28 KL := {
      ig := hig, e62 := he, cb := hcb, p20 := D.base.p20, inp := hinp, inw := hinw, nl251 := D.nl, c18 := hc18,
      defs := fun n hn => by
        show DefXS KL C (P.T n) (dA ds n).npw (dA ds n).nres IG P.hb E0
          (if _h : n < k then semAt P ds n else dflt)
        have hn' : n < k := hn
        rw [dif_pos hn']; exact ih n hn' (by omega)
      tl := fun n hn => by
        have hn' : n < k := hn
        have := At.len (hd n (by omega)).base.at_ (defT_ne _ _ _ _)
        have : 0 < (defT (scAt P ds n) (dA ds n).body (P.T n) (dA ds n).nres).length :=
          List.length_pos_iff.mpr (defT_ne _ _ _ _)
        show P.T n < C.length; omega }
    rw [semAt_eq]
    exact defRunS X D.base.ok D.op D.base.wd D.base.rd D.base.pn D.q D.base.at_

theorem gen_defs_runS (P : PC) (ds : List DefA) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64)
    (KL : LayW) (n h : Nat)
    (hig : IGOK P.hb E0 IG) (he : E0 < 2 ^ 62) (hcb : ∀ s, IG s → s.b + 4 * C.length < 2 ^ 64)
    (hinp : InpOK IG c28 P.c29 P.inp) (hinw : InpW KL IG) (hc18 : C.length < 2 ^ 18)
    (hC : At C h (defsJ P ds 0 n))
    (hT : ∀ j, j < n → P.T j = h + (defsJ P ds 0 j).length)
    (hd : ∀ k, k < n → (dA ds k).npw < 2 ^ 20 ∧ (dA ds k).npw ≤ (dA ds k).nslots ∧ OkV (scAt P ds k) (dA ds k).body ∧
      wd (scAt P ds k) (dA ds k).body = (dA ds k).nres ∧ (∀ j, rd (dA ds k).body j → j < (dA ds k).npw) ∧
      OpV (dA ds k).body ∧ (dA ds k).nslots < 251 ∧ (dA ds k).nres < 251) :
    ∀ k, k < n → DefXS KL C (P.T k) (dA ds k).npw (dA ds k).nres IG P.hb E0 (semAt P ds k) := by
  apply progRunS P ds C IG E0 c28 KL hig he hcb hinp hinw hc18 n
  intro k hk
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hd k hk
  have := At_defsJ n 0 h hC (fun j hj => by rw [Nat.zero_add]; exact hT j hj) k hk
  rw [Nat.zero_add] at this
  exact ⟨⟨a1, a2, a3, a4, a5, this⟩, a6, a7, a8⟩

end Templates
