/- Opus box E: defs and the program at the capacity exit: every def k's kinded semantics failing with `cap` means
its code, called as `DefXS`, reaches the cap stub with `IG` (`progCap`, `gen_defs_cap`). -/
import Nano.V2Self.Proof.CapNode
import Nano.V2Self.Proof.EVSProg
namespace Templates
open CallProbe SimW SafeRun ParSpec

theorem defCapRun {S : SC} {C : List J} {IG : St → Prop} {E0 : Nat} {c28 : UInt64} {KL : LayW} {fk : Fail} {tg : Nat} {fsX : Nat → SemDX}
    (X : RunCxS S C IG E0 c28 KL) (Y : CapCx fk tg S C IG E0 fsX KL) {e : Nd} {f q : Nat} (ok : OkV S e) (hop : OpV e)
    (hR : ∀ k, rd e k → k < S.p) (hpn : S.p ≤ S.nl) (hC : At C f (defT S e f q)) :
    CapD fk tg KL C f S.p IG S.hb E0 (defSF S.p S.nl (svF S fsX e)) := by
  have hl := At.len hC (defT_ne S e f q)
  obtain ⟨hP, hB, hE⟩ := At.mid hC
  have lp : (proA 1 f (S.nl - S.p)).length = 12 := by simp [proA, pushA, push]
  rw [lp] at hB hE; rw [tm_len] at hE
  have le : 1 ≤ (epi S.p q).length := by simp [epi]
  simp only [defT, List.length_append, lp, tm_len] at hl
  exact defCap X.ig hP (runVCap X Y e (f + 12) ok hop hB (by omega)) Y.nr hpn hR X.nl251

theorem progCap (P : PC) (ds : List DefA) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64) (KL : LayW) {fk : Fail} {tg : Nat}
    (hig : IGOK P.hb E0 IG) (he : E0 < 2 ^ 62) (hcb : ∀ s, IG s → s.b + 4 * C.length < 2 ^ 64)
    (hinp : InpOK IG c28 P.c29 P.inp) (hinw : InpW KL IG) (hc18 : C.length < 2 ^ 18) (h6 : 6 < C.length)
    (hkS : fk ≠ .stuck) (nr : fk ≠ .room) (t6 : fk = .cap → tg = 6) (N : Nat)
    (hd : ∀ k, k < N → DefOKS P ds C k) :
    ∀ k, k < N → CapD fk tg KL C (P.T k) (dA ds k).npw IG P.hb E0 (semAtF P ds k) := by
  have hS := progRunS P ds C IG E0 c28 KL hig he hcb hinp hinw hc18 N hd
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
        rw [dif_pos hn']; exact hS n (by omega)
      tl := fun n hn => by
        have hn' : n < k := hn
        have := At.len (hd n (by omega)).base.at_ (defT_ne _ _ _ _)
        have : 0 < (defT (scAt P ds n) (dA ds n).body (P.T n) (dA ds n).nres).length :=
          List.length_pos_iff.mpr (defT_ne _ _ _ _)
        show P.T n < C.length; omega }
    have Y : CapCx fk tg (scAt P ds k) C IG E0 (fun n => if _h : n < k then semAtF P ds n else dfltF) KL := {
      hf := fun n => by
        show (if _h : n < k then semAt P ds n else dflt) = oD (if _h : n < k then semAtF P ds n else dfltF)
        split
        · exact (oD_semAt P ds n).symm
        · rfl
      defs := fun n hn => by
        show CapD fk tg KL C (P.T n) (dA ds n).npw IG P.hb E0 (if _h : n < k then semAtF P ds n else dfltF)
        have hn' : n < k := hn
        rw [dif_pos hn']; exact ih n hn' (by omega)
      h6 := h6, hk := hkS, nr := nr, t6 := t6 }
    rw [semAtF]
    exact defCapRun X Y D.base.ok D.op D.base.rd D.base.pn D.base.at_

theorem gen_defs_cap (P : PC) (ds : List DefA) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64)
    (KL : LayW) {fk : Fail} {tg : Nat} (n h : Nat)
    (hig : IGOK P.hb E0 IG) (he : E0 < 2 ^ 62) (hcb : ∀ s, IG s → s.b + 4 * C.length < 2 ^ 64)
    (hinp : InpOK IG c28 P.c29 P.inp) (hinw : InpW KL IG) (hc18 : C.length < 2 ^ 18) (h6 : 6 < C.length)
    (hk : fk ≠ .stuck) (nr : fk ≠ .room) (t6 : fk = .cap → tg = 6)
    (hC : At C h (defsJ P ds 0 n))
    (hT : ∀ j, j < n → P.T j = h + (defsJ P ds 0 j).length)
    (hd : ∀ k, k < n → (dA ds k).npw < 2 ^ 20 ∧ (dA ds k).npw ≤ (dA ds k).nslots ∧ OkV (scAt P ds k) (dA ds k).body ∧
      wd (scAt P ds k) (dA ds k).body = (dA ds k).nres ∧ (∀ j, rd (dA ds k).body j → j < (dA ds k).npw) ∧
      OpV (dA ds k).body ∧ (dA ds k).nslots < 251 ∧ (dA ds k).nres < 251) :
    ∀ k, k < n → CapD fk tg KL C (P.T k) (dA ds k).npw IG P.hb E0 (semAtF P ds k) := by
  apply progCap P ds C IG E0 c28 KL hig he hcb hinp hinw hc18 h6 hk nr t6 n
  intro k hk
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hd k hk
  have := At_defsJ n 0 h hC (fun j hj => by rw [Nat.zero_add]; exact hT j hj) k hk
  rw [Nat.zero_add] at this
  exact ⟨⟨a1, a2, a3, a4, a5, this⟩, a6, a7, a8⟩

end Templates
