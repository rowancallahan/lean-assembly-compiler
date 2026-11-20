/- Nano/V2Self/Proof/Bridge/MainConv8: E's form of the room theorem.  `memoryNeeded` is a function of the program and its
input only, so the room bound must not depend on the work block's base (hb = base + 16) or on Gen's def table T:
* `sv` never reads `K.T` (T only places code), so `semAt` does not depend on T (`semAt_T`);
* hb takes finitely many values (base < 2^32) and room is monotone, so the largest of finitely many bounds is uniform
  (`unif_fin`). -/
import Nano.V2Self.Proof.Bridge.MainConv7

namespace NanoMain
open Templates

mutual
theorem wd_T (K : SC) (T' : Nat → Nat) : ∀ e : ParSpec.Nd, wd { K with T := T' } e = wd K e
  | .ite _ _ _ t _ => by simp only [wd]; rw [wd_T K T' t]
  | .letE _ _ _ b => by simp only [wd]; rw [wd_T K T' b]
  | .pair cs => by simp only [wd]; rw [wdL_T K T' cs]
  | .const _ | .loc _ _ | .bin _ _ _ | .call _ _ | .prim _ _ | .loop _ _ | .cont _ => by simp only [wd]
theorem wdL_T (K : SC) (T' : Nat → Nat) : ∀ cs : List ParSpec.Nd, wdL { K with T := T' } cs = wdL K cs
  | [] => by simp only [wdL]
  | c :: cs => by simp only [wdL]; rw [wd_T K T' c, wdL_T K T' cs]
end

mutual
theorem sv_T (K : SC) (T' : Nat → Nat) : ∀ e : ParSpec.Nd, sv { K with T := T' } e = sv K e
  | .const _ => by simp only [sv]
  | .loc _ _ => by simp only [sv]
  | .bin op a b => by simp only [sv]; rw [sv_T K T' a, sv_T K T' b]
  | .ite c a b t e => by simp only [sv]; rw [sv_T K T' a, sv_T K T' b, sv_T K T' t, sv_T K T' e]
  | .letE s w v b => by simp only [sv]; rw [sv_T K T' v, sv_T K T' b]
  | .pair cs => by simp only [sv]; rw [svL_T K T' cs]
  | .call id as => by simp only [sv]; rw [svL_T K T' as]
  | .prim pn as => by simp only [sv]; rw [svL_T K T' as]; rfl
  | .loop z s => by simp only [sv]; rw [st_T K T' z, st_T K T' s]
  | .cont _ => by simp only [sv]
theorem st_T (K : SC) (T' : Nat → Nat) : ∀ e : ParSpec.Nd, st { K with T := T' } e = st K e
  | .ite c a b t e => by simp only [st]; rw [sv_T K T' a, sv_T K T' b, st_T K T' t, st_T K T' e]
  | .letE s w v b => by simp only [st]; rw [sv_T K T' v, st_T K T' b]
  | .cont e => by simp only [st]; rw [sv_T K T' e]
  | .const _ => by simp only [st]; rw [sv_T K T' (.const _)]
  | .loc _ _ => by simp only [st]; rw [sv_T K T' (.loc _ _)]
  | .bin op a b => by simp only [st]; rw [sv_T K T' (.bin op a b)]
  | .pair cs => by simp only [st]; rw [sv_T K T' (.pair cs)]
  | .call id as => by simp only [st]; rw [sv_T K T' (.call id as)]
  | .prim pn as => by simp only [st]; rw [sv_T K T' (.prim pn as)]
  | .loop z s => by simp only [st]; rw [sv_T K T' (.loop z s)]
theorem svL_T (K : SC) (T' : Nat → Nat) : ∀ cs : List ParSpec.Nd, svL { K with T := T' } cs = svL K cs
  | [] => by simp only [svL]
  | c :: cs => by simp only [svL]; rw [sv_T K T' c, svL_T K T' cs, wd_T K T' c]
end

/-- `semAt` does not depend on the def table T -/
theorem semAt_T (P : Templates.PC) (T' : Nat → Nat) (ds : List ParSpec.DefA) :
    ∀ k, semAt ⟨P.κ, P.hb, P.c29, P.inp, T'⟩ ds k = semAt P ds k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rw [semAt_eq, semAt_eq]
    have e : scAt ⟨P.κ, P.hb, P.c29, P.inp, T'⟩ ds k = { scAt P ds k with T := T' } := by
      simp only [scAt]
      congr 1
      funext n
      split
      · exact ih n ‹_›
      · rfl
    rw [e, sv_T]

/-- finitely many monotone bounds have a common bound -/
theorem unif_fin (Q : Nat → Nat → Prop) (hmono : ∀ b N N', N ≤ N' → Q b N → Q b N') :
    ∀ M, (∀ b < M, ∃ N, Q b N) → ∃ R, ∀ b < M, Q b R
  | 0, _ => ⟨0, fun b h => absurd h (Nat.not_lt_zero b)⟩
  | M + 1, h => by
    obtain ⟨R, hR⟩ := unif_fin Q hmono M (fun b hb => h b (by omega))
    obtain ⟨N, hN⟩ := h M (by omega)
    refine ⟨max R N, fun b hb => ?_⟩
    rcases Nat.lt_or_ge b M with hb' | hb'
    · exact hmono b R _ (Nat.le_max_left _ _) (hR b hb')
    · obtain rfl : b = M := by omega
      exact hmono b N _ (Nat.le_max_right _ _) hN

/-- **the room theorem, E's form**: if `Sem` succeeds, one room bound `R` (independent of the work block's base and of
the def table) makes main's E semantics succeed with `Sem`'s result, from the empty heap at `base + 16` with the stack
top at the block's end rounded down to 8 -/
theorem main_room (ds : List ParSpec.DefA) (sigs : List Sig) (Ks : List (List Nat)) (inp : List UInt8)
    (hTy : TyProg ds sigs) (hO : OwnSpec.progOk [] [] Ks ds = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hil : inp.length < 2 ^ 64) (κ : Nat) (hκ : κ < 2 ^ 40) (y : List UInt8) (hS : Sem κ ds inp = .ok y) :
    ∃ R, ∀ (P : Templates.PC) (base len : Nat), P.κ = κ → P.hb = base + 16 → P.c29 = UInt64.ofNat inp.length →
      P.inp = inpW inp → base % 8 = 0 → base + len ≤ 2 ^ 32 → R ≤ len →
      ∃ a l H', semAt P ds (ds.length - 1) [] ((base + len) / 8 * 8) ⟨base + 16, fun _ => none⟩ = some ([a], H') ∧
        BufAt P.hb P.κ H' a l ∧ y = l.map UInt64.toUInt8 := by
  let P0 : Nat → Templates.PC := fun b => ⟨κ, b + 16, UInt64.ofNat inp.length, inpW inp, fun _ => 0⟩
  let Q : Nat → Nat → Prop := fun b N => ∀ len, b % 8 = 0 → b + len ≤ 2 ^ 32 → N ≤ len →
    ∃ a l H', semAt (P0 b) ds (ds.length - 1) [] ((b + len) / 8 * 8) ⟨b + 16, fun _ => none⟩ = some ([a], H') ∧
      BufAt (P0 b).hb (P0 b).κ H' a l ∧ y = l.map UInt64.toUInt8
  have hmono : ∀ b N N', N ≤ N' → Q b N → Q b N' := fun b N N' hle hQ len h1 h2 h3 => hQ len h1 h2 (by omega)
  obtain ⟨R, hR⟩ := unif_fin Q hmono (2 ^ 32 + 1) (fun b _ => by
    by_cases h8 : b % 8 = 0
    · obtain ⟨N, hN⟩ := main_ex (P0 b) ds sigs Ks inp hTy hO hK2 rfl rfl hil hκ ⟨b + 16, fun _ => none⟩
        (by show (b + 16) % 8 = 0; omega) (Nat.le_refl _) y hS
      refine ⟨N + 24, fun len _ h2 h3 => hN _ ?_ ?_⟩
      · show b + 16 + N ≤ (b + len) / 8 * 8; omega
      · omega
    · exact ⟨0, fun len h1 => absurd h1 h8⟩)
  refine ⟨R, fun P base len e1 e2 e3 e4 h8 h2 h3 => ?_⟩
  have hP : P = ⟨(P0 base).κ, (P0 base).hb, (P0 base).c29, (P0 base).inp, P.T⟩ := by
    cases P; simp only [P0] at *; subst e1 e2 e3 e4; rfl
  rw [hP, semAt_T (P0 base) P.T ds]
  obtain ⟨a, l, H', h1, h2', h3'⟩ := hR base (by omega) len h8 h2 h3
  exact ⟨a, l, H', h1, by simpa [P0] using h2', h3'⟩

end NanoMain
