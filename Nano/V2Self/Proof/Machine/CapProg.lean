/- Defs and the program, all outcomes (`defRunO`, `progRunO`, `gen_defs_runO`): every def k satisfies `DefO` — the
success contract `DefXS` for `semAt`, and for every failure kind of `semAtF` (cap, room) a safe run to that kind's
stub with `IG`.  One strong induction on k (callee first). -/
import Nano.V2Self.Proof.Machine.CapNode
import Nano.V2Self.Proof.Machine.EVSProg
namespace Templates
open CallProbe SimW SafeRun ParSpec

/-- one def, all outcomes: its template at word `f` meets the def contract and, for every failure kind, reaches
that kind's stub -/
theorem defRunO {S : SC} {C : List J} {IG : St → Prop} {E0 : Nat} {c28 : UInt64} {KL : LayW} {fsX : Nat → SemDX}
    (X : RunCxS S C IG E0 c28 KL) (Y0 : OCx S C IG E0 fsX KL) {e : Nd} {f q : Nat} (ok : OkV S e) (hop : OpV e)
    (hw : wd S e = q) (hR : ∀ k, rd e k → k < S.p) (hpn : S.p ≤ S.nl) (hq : q < 251) (hC : At C f (defT S e f q)) :
    DefO KL C f S.p q IG S.hb E0 (defS S.p S.nl (sv S e)) (defSF S.p S.nl (svF S fsX e)) := by
  have hl := At.len hC (defT_ne S e f q)
  obtain ⟨hP, hB, hE⟩ := At.mid hC
  have lp : (proA 1 f (S.nl - S.p)).length = 12 := by simp [proA, pushA, push]
  rw [lp] at hB hE; rw [tm_len] at hE
  have le : 1 ≤ (epi S.p q).length := by simp [epi]
  simp only [defT, List.length_append, lp, tm_len] at hl
  have r := runVO X Y0 e (f + 12) ok hop hB (by omega)
  refine ⟨defXS X.ig hP (r.ok.wid hw) hE hpn hR X.nl251 (by omega), fun fk hk => ?_⟩
  have Y := Y0.cx fk hk
  exact defCapK X.ig hP (r.fail fk hk) Y.t1 Y.hb2k (by have := Y.h6; omega) X.c18 (by omega) hpn hR X.nl251

/-- **program level, all outcomes**: every def k < N satisfies `DefO` (strong induction on k = call-graph order) -/
theorem progRunO (P : PC) (ds : List DefA) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64) (KL : LayW)
    (hig : IGOK P.hb E0 IG) (he : E0 < 2 ^ 62) (hcb : ∀ s, IG s → s.b + s.w * C.length < 2 ^ 64)
    (hinp : InpOK IG c28 P.c29 P.inp) (hinw : InpW KL IG) (hc18 : C.length < 2 ^ 18) (h6 : 6 < C.length)
    (kap : P.κ < 2 ^ 40) (hb2k : 2048 ≤ P.hb) (N : Nat) (hd : ∀ k, k < N → DefOKS P ds C k) :
    ∀ k, k < N → DefO KL C (P.T k) (dA ds k).npw (dA ds k).nres IG P.hb E0 (semAt P ds k) (semAtF P ds k) := by
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
        rw [dif_pos hn']; exact (ih n hn' (by omega)).ok
      tl := fun n hn => by
        have hn' : n < k := hn
        have := At.len (hd n (by omega)).base.at_ (defT_ne _ _ _ _)
        have : 0 < (defT (scAt P ds n) (dA ds n).body (P.T n) (dA ds n).nres).length :=
          List.length_pos_iff.mpr (defT_ne _ _ _ _)
        show P.T n < C.length; omega }
    have Y0 : OCx (scAt P ds k) C IG E0 (fun n => if _h : n < k then semAtF P ds n else dfltF) KL := {
      hf := fun n => by
        show (if _h : n < k then semAt P ds n else dflt) = oD (if _h : n < k then semAtF P ds n else dfltF)
        split
        · exact (oD_semAt P ds n).symm
        · rfl
      defs := fun n hn fk hfk => by
        show CapD fk (stubW fk) KL C (P.T n) (dA ds n).npw IG P.hb E0 (if _h : n < k then semAtF P ds n else dfltF)
        have hn' : n < k := hn
        rw [dif_pos hn']; exact (ih n hn' (by omega)).fail fk hfk
      h6 := h6, kap := kap, hb2k := hb2k }
    rw [semAt_eq, semAtF]
    exact defRunO X Y0 D.base.ok D.op D.base.wd D.base.rd D.base.pn D.q D.base.at_

/-- on any J program holding Gen's def templates: every def, all outcomes -/
theorem gen_defs_runO (P : PC) (ds : List DefA) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64)
    (KL : LayW) (n h : Nat)
    (hig : IGOK P.hb E0 IG) (he : E0 < 2 ^ 62) (hcb : ∀ s, IG s → s.b + s.w * C.length < 2 ^ 64)
    (hinp : InpOK IG c28 P.c29 P.inp) (hinw : InpW KL IG) (hc18 : C.length < 2 ^ 18) (h6 : 6 < C.length)
    (kap : P.κ < 2 ^ 40) (hb2k : 2048 ≤ P.hb) (hC : At C h (defsJ P ds 0 n))
    (hT : ∀ j, j < n → P.T j = h + (defsJ P ds 0 j).length)
    (hd : ∀ k, k < n → (dA ds k).npw < 2 ^ 20 ∧ (dA ds k).npw ≤ (dA ds k).nslots ∧ OkV (scAt P ds k) (dA ds k).body ∧
      wd (scAt P ds k) (dA ds k).body = (dA ds k).nres ∧ (∀ j, rd (dA ds k).body j → j < (dA ds k).npw) ∧
      OpV (dA ds k).body ∧ (dA ds k).nslots < 251 ∧ (dA ds k).nres < 251) :
    ∀ k, k < n → DefO KL C (P.T k) (dA ds k).npw (dA ds k).nres IG P.hb E0 (semAt P ds k) (semAtF P ds k) := by
  apply progRunO P ds C IG E0 c28 KL hig he hcb hinp hinw hc18 h6 kap hb2k n
  intro k hk
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hd k hk
  have := At_defsJ n 0 h hC (fun j hj => by rw [Nat.zero_add]; exact hT j hj) k hk
  rw [Nat.zero_add] at this
  exact ⟨⟨a1, a2, a3, a4, a5, this⟩, a6, a7, a8⟩

end Templates
