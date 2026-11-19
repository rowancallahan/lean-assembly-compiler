/- Nano/V2Self/Proof/ParInvName: Layer 3, NAME LOOKUP on `Rep` (box G; for tasks 43 / 55).
* `v85_drop` / `v8_drop`: the comparison / def-lookup loops write only cells 0, 22, 31 (the output suffix is untouched);
* `v8_val`: h[22] after the def lookup = `findD st.defs x` (+1, 0 for none);
* `rep_same`: `Rep` survives a `Same 21` / `Same 22` change (scratch cells) that keeps the output suffix. -/
import Nano.V2Self.Proof.ParInvDefs
import Nano.V2Self.Proof.ParInvBind
namespace ParInv
open C BufL ParSpec ParRun

theorem v85_drop : ∀ (n : Nat) (h : Buf) (a b : UInt64), (v85 n h a b).drop 184384 = h.drop 184384
  | 0, h, a, b => by rw [v85]; exact drop_bset _ _ _ (by decide)
  | n + 1, h, a, b => by
    rw [v85]
    simp only []
    repeat' split
    all_goals first
      | exact drop_bset _ _ _ (by decide)
      | exact v85_drop n h _ _

theorem v8_drop : ∀ (n : Nat) (h : Buf) (j x : UInt64), (v8 n h j x).drop 184384 = h.drop 184384
  | 0, h, j, x => by rw [v8]; exact drop_bset _ _ _ (by decide)
  | n + 1, h, j, x => by
    rw [v8]
    simp only []
    repeat' split
    all_goals first
      | exact drop_bset _ _ _ (by decide)
      | (rw [drop_bset _ _ _ (by decide)]; exact v85_drop _ _ _ _)
      | (rw [v8_drop n]; exact v85_drop _ _ _ _)

/-- **def lookup, value**: h[22] = index + 1 of the innermost finished def with this name, 0 if none -/
theorem v8_val {h : Buf} {st : St} {bb : Bool} {p : UInt64} {nm : List UInt64} (hD : DefsRep h st bb)
    (h7 : (bget h 7).toNat < 2 ^ 24) (hl : 31 < h.length) (hn : NameOK h p nm) :
    bget (v8 16777216 h (bget h 12) p) 22 = (((findD st.defs (nm.map UInt64.toNat)).map (· + 1)).getD 0).toUInt64 := by
  obtain ⟨tab, htl, hTab, hnames⟩ := defTab_of hD h7
  obtain ⟨e12, hlt, _⟩ := hD
  have hnm : nm.length < 2 ^ 24 := by obtain ⟨_, _, hb⟩ := hn; omega
  obtain ⟨_, h22⟩ := v8_lookup tab p nm st.defs.length 16777216 h (bget h 12) e12 (by omega) (by omega) (by omega) hl
    (by omega) hTab hn hnm
  rw [h22, idxOf_findD tab st.defs nm _ rfl htl (fun i hi hi' => hnames i hi hi') _ (Nat.le_refl _), List.take_length]

/-- `Rep` ignores the scratch cells 21, 22 and 31 -/
theorem rep_same {r : Nat} {h h' ts : Buf} {st : St} {fs : List Frame} (R : Rep h ts st fs) (s : Same r h h')
    (hr : r = 21 ∨ r = 22) (ed : h'.drop 184384 = h.drop 184384) : Rep h' ts st fs := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := R
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have e : ∀ i : UInt64, i.toNat ≠ 21 → i.toNat ≠ 22 → i.toNat ≠ 31 → bget h' i = bget h i :=
    fun i a b c => s.2 i (by omega) c
  have et : TokAgree h h' := ⟨e 7 (by decide) (by decide) (by decide), fun i hi => e i (by omega) (by omega) (by omega)⟩
  have es : ShTabAgree h h' := fun i a _ => e i (by omega) (by omega) (by omega)
  have c : ∀ n : UInt64, n.toNat ≠ 21 → n.toNat ≠ 22 → n.toNat ≠ 31 → bget h' n = bget h n := e
  refine ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide) (by decide) (by decide)]; exact r0,
    by rw [c 3 (by decide) (by decide) (by decide)]; exact tokAt_frame et hn r3,
    by rw [c 11 (by decide) (by decide) (by decide)]; exact r11,
    binds_frame rB (c 4 (by decide) (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega) (by omega)) et hn es,
    defs_frame rD (c 12 (by decide) (by decide) (by decide)) (c 27 (by decide) (by decide) (by decide))
      (fun i a _ => e i (by omega) (by omega) (by omega)) et hn es,
    arena_frame rA (c 8 (by decide) (by decide) (by decide)) (c 9 (by decide) (by decide) (by decide))
      (fun i a _ => e i (by omega) (by omega) (by omega)) es,
    fun s hs => by rw [c 25 (by decide) (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx hne => by rw [c 29 (by decide) (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx hne),
    by rw [c 30 (by decide) (by decide) (by decide)]; exact r30, by rw [c 32 (by decide) (by decide) (by decide)]; exact r32,
    out_frame rO ed,
    tasks_frame rK (c 5 (by decide) (by decide) (by decide)) (fun i _ _ => e i (by omega) (by omega) (by omega)) et hn es
      (fun i a _ => e i (by omega) (by omega) (by omega)) rA.2.1⟩

end ParInv
