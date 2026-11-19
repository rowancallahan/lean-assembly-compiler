/- Nano/V2Self/Proof/OwnP30: the program loop `o39` and the stage `o41`: an accepted AST of WF defs is `LinearK`. -/
import Nano.V2Self.Proof.OwnP29
namespace OwnP
open C OwnSpec ParSpec

theorem o39_ok : ∀ (ds : List DefA) (n : Nat) (x s f v a b c t : Buf) (ps rs : List (List Nat)) (i : Nat),
    VInv x ps rs a b c t i → x.drop i = ds.flatMap DefA.ser → (∀ d ∈ ds, WFD d) → o39 n x s f v a b c t = 1 →
    ∃ Ks, progOk ps rs Ks ds = true ∧ ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2
  | _, 0, x, s, f, v, a, b, c, t, ps, rs, i, _, _, _, h => by simp [o39] at h
  | [], n + 1, x, s, f, v, a, b, c, t, ps, rs, i, hI, hx, _, _ => ⟨[], by simp [progOk], by simp⟩
  | d :: ds, n + 1, x, s, f, v, a, b, c, t, ps, rs, i, hI, hx, hw, h => by
    have hI' := hI
    obtain ⟨hl, -, h0, h1, -, -, -, -, hx40, -⟩ := hI'
    have hx' : x.drop i = d.ser ++ ds.flatMap DefA.ser := by rw [hx]; simp
    have hxl := drop_len hx' (by simp [DefA.ser])
    have hi : i < x.length := by simp [DefA.ser] at hxl; omega
    have x0 : bget x (u i) = 20 := by
      rw [show i = i + 0 from rfl, xw hx' (by simp [DefA.ser]) (by omega)]; simp [DefA.ser]
    rw [o39] at h
    simp only [h0, h1, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false,
      bsize_u, u_lt' (show i < 2 ^ 64 by omega) (show x.length < 2 ^ 64 by omega), hi, if_true, x0,
      show ((20 : UInt64) == 20) = true from rfl] at h
    generalize hO : o38 x s f v a b c t = O at h
    have hok : bget O.2.2.2.1 1 ≠ 1 := by
      intro he; revert h; rcases n with _ | n
      · simp [o39]
      · rw [o39]; simp [he]
    obtain ⟨K, R, hd, hK, hI2⟩ := o38_ok (rest := ds.flatMap DefA.ser) hI hx' (hw d (by simp)) (by rw [hO]; exact hok)
    rw [hO] at hI2
    obtain ⟨Ks, hp, hk⟩ := o39_ok ds n x O.1 O.2.1 O.2.2.1 O.2.2.2.1 O.2.2.2.2.1 O.2.2.2.2.2.1 O.2.2.2.2.2.2 _ _ _ hI2
      (by rw [← List.drop_drop, hx', List.drop_left]) (fun d' hd' => hw d' (by simp [hd'])) h
    refine ⟨K :: Ks, ?_, ?_⟩
    · simp only [progOk, hd]; exact hp
    · intro K' hK'; simp at hK'; rcases hK' with rfl | hK'
      · exact hK
      · exact hk K' hK'

theorem o40_16 : o40 64 bnew 16 = List.replicate 16 0 := by decide

theorem t0_len : (o40 4096 bnew 4096).length = 4096 := by
  obtain ⟨h1, h2, -⟩ := o40_ge 4096 bnew 4096 (by omega) (by simp [bnew]) (by simp [bnew])
  simp only [bnew, List.length_nil] at h1 h2
  show (o40 4096 [] (u 4096)).length = 4096; omega

/-- **soundness of the ownership stage**: an AST of WF defs that `o41` accepts is linear, with slot kinds ≤ 2 -/
theorem o41_sound (p : List DefA) (hw : ∀ d ∈ p, WFD d) (hlen : (serialize p).length < 2 ^ 64)
    (h : o41 (serialize p) ≠ []) :
    ∃ Ks, progOk [] [] Ks p = true ∧ ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2 := by
  unfold o41 at h
  generalize hr : (if bget (serialize p) 0 == 2 then (if bsize (serialize p) < 1099511627776 then
    o39 16777216 (serialize p) (o40 64 bnew 16) bnew bnew (bset (o40 64 bnew 16) 0 1) bnew bnew (o40 4096 bnew 4096)
    else 0) else 0) = r at h
  have hr1 : r = 1 := by
    rcases Nat.lt_or_ge 0 1 with _ | _
    · by_cases e : r = 1
      · exact e
      · exact absurd (by simp only [beq_iff_eq, e, if_false]; rfl) h
    · omega
  subst hr1
  have hx0 : bget (serialize p) 0 = 2 := by simp [serialize, bget]
  rw [hx0] at hr; simp only [beq_self_eq_true, if_true] at hr
  have c40 : (bsize (serialize p) < (1099511627776 : UInt64)) = ((serialize p).length < 2 ^ 40) := by
    rw [bsize_u]; exact u_lt' (b := 1099511627776) hlen (by omega)
  have hsz : (serialize p).length < 2 ^ 40 := by
    rcases Nat.lt_or_ge (serialize p).length (2 ^ 40) with e | e
    · exact e
    · simp only [c40, show ¬ (serialize p).length < 2 ^ 40 by omega, ↓reduceIte] at hr; exact absurd hr (by decide)
  simp only [c40, hsz, ↓reduceIte] at hr
  refine o39_ok p _ _ _ _ _ _ _ _ _ [] [] 1 ?_ (by simp [serialize]) hw hr
  refine ⟨?_, ?_, ?_, ?_, ?_, by simp, by simp [bnew], by simp [bnew], hsz, ⟨rfl, by rw [t0_len]; omega, by rw [t0_len]; simp,
    fun c hc => by simp at hc⟩⟩
  all_goals rw [o40_16]; decide

end OwnP
