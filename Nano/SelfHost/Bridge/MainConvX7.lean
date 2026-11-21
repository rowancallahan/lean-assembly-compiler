/- Nano/SelfHost/Bridge/MainConvX7: the cap half — the program: every def meets the cap contract too, and when `Sem`
stops with `cap`, main's kinded E semantics reports `cap` given enough room (`main_cap`, uniform: `main_capR`). -/
import Nano.SelfHost.Bridge.MainConvX6

namespace NanoMain
open Templates

/-- **every def meets its contract** (by induction over the program, O's walk accumulating parameter / result kinds) -/
theorem prog_three (P : Templates.PC) (ds : List ParSpec.DefA) (sigs : List Sig) (Ks : List (List Nat)) (inp : List UInt8)
    (hTy : TyProg ds sigs) (hO : OwnSpec.progOk [] [] Ks ds = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hc29 : P.c29 = UInt64.ofNat inp.length) (hinp : P.inp = inpW inp) (hil : inp.length < 2 ^ 64) (hκ : P.κ < 2 ^ 40) :
    ∀ n, n ≤ ds.length → ∃ ps rs, ps.length = n ∧ rs.length = n ∧
      OwnSpec.progOk ps rs (Ks.drop n) (ds.drop n) = true ∧
      ∀ i (hi : i < n), ∃ R, rs[i]? = some R ∧ (∀ x ∈ R, x ≤ 1) ∧ R.length = (dA ds i).nres ∧
        ps[i]? = some ((Ks.getD i []).take (dA ds i).npw) ∧
        ∃ f, (means inp P.κ [] ds)[i]? = some f ∧
          DefR P.hb P.κ (sigs.getD i ([], [])).1 ((Ks.getD i []).take (dA ds i).npw) R f (semAt P ds i) ∧
          DefEx P.hb P.κ (sigs.getD i ([], [])).1 ((Ks.getD i []).take (dA ds i).npw) f (semAt P ds i) ∧
          DefExC P.hb P.κ (sigs.getD i ([], [])).1 ((Ks.getD i []).take (dA ds i).npw) f (semAtF P ds i) := by
  obtain ⟨hsl, hts, -⟩ := hTy
  have hC := means_ok inp P.κ ds [] [] sigs ⟨rfl, by simp⟩ hsl (by simpa using hts)
  simp only [List.nil_append] at hC
  intro n
  induction n with
  | zero => intro _; exact ⟨[], [], rfl, rfl, by simpa using hO, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    intro hn
    obtain ⟨ps, rs, hl1, hl2, hpo, hall⟩ := ih (by omega)
    have hdn : ds.drop n = ds[n] :: ds.drop (n + 1) := List.drop_eq_getElem_cons (by omega)
    rw [hdn] at hpo
    obtain ⟨K, Ks', hK⟩ : ∃ K Ks', Ks.drop n = K :: Ks' := by
      cases h : Ks.drop n with
      | nil => rw [h] at hpo; simp [OwnSpec.progOk] at hpo
      | cons K Ks' => exact ⟨K, Ks', rfl⟩
    rw [hK] at hpo
    simp only [OwnSpec.progOk] at hpo
    split at hpo
    · rename_i R hd
      have hKn : Ks.getD n [] = K := by
        have := congrArg (·[0]?) hK; simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
        simp [List.getD_eq_getElem?_getD, this]
      have hKmem : K ∈ Ks := by
        have := congrArg (·[0]?) hK; simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
        exact List.mem_of_getElem? this
      obtain ⟨hKl, hpn, hRl, hR1⟩ := defOk_res hd
      have hda := dA_get ds n (by omega)
      have hsn : n < sigs.length := by omega
      obtain ⟨t1, t2, t3, t4⟩ := hts n ds[n] sigs[n] (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _)
      -- the def's context
      have hCR : CallR ⟨inp, P.κ, (means inp P.κ [] ds).take n⟩ (scAt P ds n) ⟨ps, rs, K, ds[n].npw⟩ (sigs.take n) :=
        (fun i P' R' hp hr => by
          have hi : i < n := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨R0, h0, -, -, hp0, f, hf, hdr, -, -⟩ := hall i hi
          simp only at hp hr; rw [hp] at hp0; cases hp0; rw [hr] at h0; cases h0
          refine ⟨f, by simp only; rw [List.getElem?_take_of_lt hi]; exact hf, fun sg' hs => ?_⟩
          rw [List.getElem?_take_of_lt hi] at hs
          have : sigs.getD i ([], []) = sg' := by simp [List.getD_eq_getElem?_getD, hs]
          rw [this] at hdr
          have hfs : (scAt P ds n).fs i = semAt P ds i := by simp [scAt, hi]
          rw [hfs]; exact hdr)
      have hCE : CallEx ⟨inp, P.κ, (means inp P.κ [] ds).take n⟩ (scAt P ds n) ⟨ps, rs, K, ds[n].npw⟩ (sigs.take n) :=
        (fun i P' R' hp hr => by
          have hi : i < n := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨R0, h0, -, -, hp0, f, hf, -, hdr, -⟩ := hall i hi
          simp only at hp hr; rw [hp] at hp0; cases hp0; rw [hr] at h0; cases h0
          refine ⟨f, by simp only; rw [List.getElem?_take_of_lt hi]; exact hf, fun sg' hs => ?_⟩
          rw [List.getElem?_take_of_lt hi] at hs
          have : sigs.getD i ([], []) = sg' := by simp [List.getD_eq_getElem?_getD, hs]
          rw [this] at hdr
          have hfs : (scAt P ds n).fs i = semAt P ds i := by simp [scAt, hi]
          rw [hfs]; exact hdr)
      have hfX : ∀ m, (scAt P ds n).fs m = oD ((fun m => if _h : m < n then semAtF P ds m else dfltF) m) := by
        intro m; simp only [scAt]; split
        · exact (oD_semAt P ds m).symm
        · rfl
      have hCC : CallExC ⟨inp, P.κ, (means inp P.κ [] ds).take n⟩ (scAt P ds n)
          (fun m => if _h : m < n then semAtF P ds m else dfltF) ⟨ps, rs, K, ds[n].npw⟩ (sigs.take n) :=
        (fun i P' R' hp hr => by
          have hi : i < n := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨R0, h0, -, -, hp0, f, hf, -, -, hdr⟩ := hall i hi
          simp only at hp hr; rw [hp] at hp0; cases hp0; rw [hr] at h0; cases h0
          refine ⟨f, by simp only; rw [List.getElem?_take_of_lt hi]; exact hf, fun sg' hs => ?_⟩
          rw [List.getElem?_take_of_lt hi] at hs
          have : sigs.getD i ([], []) = sg' := by simp [List.getD_eq_getElem?_getD, hs]
          rw [this] at hdr
          simp only [dif_pos hi]; exact hdr)
      have hFMn : ∀ i args, Mo ((scAt P ds n).fs i args) := fun i a => by
        simp only [scAt]; split
        · exact semAt_mo P ds i a
        · exact fun _ _ _ _ h => by simp [dflt] at h
      have hDR := def_ok ⟨inp, P.κ, (means inp P.κ [] ds).take n⟩ (scAt P ds n) ⟨ps, rs, K, ds[n].npw⟩ (sigs.take n)
        (fun i R' sg' hr hs => by
          have hi : i < n := by rw [← hl2]; exact (List.getElem?_eq_some_iff.1 hr).1
          obtain ⟨R0, h0, -, hl0, -⟩ := hall i hi
          simp only at hr; rw [hr] at h0; cases h0
          rw [List.getElem?_take_of_lt hi] at hs
          obtain ⟨-, -, t3', -⟩ := hts i (dA ds i) sg' (by rw [dA_get ds i (by omega)]; exact List.getElem?_eq_getElem _) hs
          omega)
        (fun R' hR' x hx => by
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hR'
          have hi' : i < n := by rw [← hl2]; exact (List.getElem?_eq_some_iff.1 hi).1
          obtain ⟨R0, h0, h01, -⟩ := hall i hi'
          rw [hi] at h0; cases h0; exact h01 x hx)
        ⟨rfl, by simp [scAt, hc29], by simp [scAt, hinp], hil⟩
        hCR
        (ctxOK_take hC n)
        (fun s => by
          rw [List.getD_eq_getElem?_getD]
          cases h : K[s]? with
          | none => simp
          | some k => exact hK2 K hKmem k (List.mem_of_getElem? h))
        ds[n] sigs[n] R ⟨t1, t2, t3, t4⟩ hd rfl (by simp only [scAt, hda]; try rfl)
      have hDE := def_ex ⟨inp, P.κ, (means inp P.κ [] ds).take n⟩ (scAt P ds n) ⟨ps, rs, K, ds[n].npw⟩ (sigs.take n)
        (fun i R' sg' hr hs => by
          have hi : i < n := by rw [← hl2]; exact (List.getElem?_eq_some_iff.1 hr).1
          obtain ⟨R0, h0, -, hl0, -⟩ := hall i hi
          simp only at hr; rw [hr] at h0; cases h0
          rw [List.getElem?_take_of_lt hi] at hs
          obtain ⟨-, -, t3', -⟩ := hts i (dA ds i) sg' (by rw [dA_get ds i (by omega)]; exact List.getElem?_eq_getElem _) hs
          omega)
        (fun R' hR' x hx => by
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hR'
          have hi' : i < n := by rw [← hl2]; exact (List.getElem?_eq_some_iff.1 hi).1
          obtain ⟨R0, h0, h01, -⟩ := hall i hi'
          rw [hi] at h0; cases h0; exact h01 x hx)
        ⟨rfl, by simp [scAt, hc29], by simp [scAt, hinp], hil⟩
        hCR hCE hFMn (by simpa [scAt] using hκ)
        (ctxOK_take hC n)
        (fun s => by
          rw [List.getD_eq_getElem?_getD]
          cases h : K[s]? with
          | none => simp
          | some k => exact hK2 K hKmem k (List.mem_of_getElem? h))
        ds[n] sigs[n] R ⟨t1, t2, t3, t4⟩ hd rfl (by simp only [scAt, hda]; try rfl)
      have hDC := def_exc ⟨inp, P.κ, (means inp P.κ [] ds).take n⟩ (scAt P ds n)
        (fun m => if _h : m < n then semAtF P ds m else dfltF) hfX ⟨ps, rs, K, ds[n].npw⟩ (sigs.take n)
        (fun i R' sg' hr hs => by
          have hi : i < n := by rw [← hl2]; exact (List.getElem?_eq_some_iff.1 hr).1
          obtain ⟨R0, h0, -, hl0, -⟩ := hall i hi
          simp only at hr; rw [hr] at h0; cases h0
          rw [List.getElem?_take_of_lt hi] at hs
          obtain ⟨-, -, t3', -⟩ := hts i (dA ds i) sg' (by rw [dA_get ds i (by omega)]; exact List.getElem?_eq_getElem _) hs
          omega)
        (fun R' hR' x hx => by
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hR'
          have hi' : i < n := by rw [← hl2]; exact (List.getElem?_eq_some_iff.1 hi).1
          obtain ⟨R0, h0, h01, -⟩ := hall i hi'
          rw [hi] at h0; cases h0; exact h01 x hx)
        ⟨rfl, by simp [scAt, hc29], by simp [scAt, hinp], hil⟩
        hCR hCE hCC hFMn (by simpa [scAt] using hκ)
        (ctxOK_take hC n)
        (fun s => by
          rw [List.getD_eq_getElem?_getD]
          cases h : K[s]? with
          | none => simp
          | some k => exact hK2 K hKmem k (List.mem_of_getElem? h))
        ds[n] sigs[n] R ⟨t1, t2, t3, t4⟩ hd rfl (by simp only [scAt, hda]; try rfl)
      refine ⟨ps ++ [K.take ds[n].npw], rs ++ [R], by simp [hl1], by simp [hl2], ?_, fun i hi => ?_⟩
      · have e1 : Ks.drop (n + 1) = Ks' := by
          have := congrArg List.tail hK; simpa [List.tail_drop] using this
        rw [e1]; exact hpo
      · rcases Nat.lt_or_ge i n with h | h
        · obtain ⟨R0, h0, a, b, c, rest⟩ := hall i h
          exact ⟨R0, by rw [List.getElem?_append_left (by omega)]; exact h0, a, b,
            by rw [List.getElem?_append_left (by omega)]; exact c, rest⟩
        · have hin : i = n := by omega
          subst hin
          refine ⟨R, by simp [hl2], hR1, by rw [hda]; exact hRl, by simp [hl1, hda]; rw [← hKn]; simp [List.getD_eq_getElem?_getD]; try rfl, ?_⟩
          have hmg := means_get inp P.κ ds [] i (by omega)
          simp only [List.length_nil, Nat.zero_add] at hmg
          refine ⟨_, hmg, ?_⟩
          rw [semAt_eq, hda, show sigs.getD i ([], []) = sigs[i] by simp [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hsn], hKn]
          refine ⟨hDR, hDE, ?_⟩
          rw [semAtF, hda]; exact hDC
    · simp at hpo

/-- **main, cap**: if `Sem` stops with `cap`, main's kinded E semantics reports `cap` given enough room -/
theorem main_cap (P : Templates.PC) (ds : List ParSpec.DefA) (sigs : List Sig) (Ks : List (List Nat)) (inp : List UInt8)
    (hTy : TyProg ds sigs) (hO : OwnSpec.progOk [] [] Ks ds = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hc29 : P.c29 = UInt64.ofNat inp.length) (hinp : P.inp = inpW inp) (hil : inp.length < 2 ^ 64) (hκ : P.κ < 2 ^ 40)
    (H : Hp) (h8 : H.top % 8 = 0) (hhb : P.hb ≤ H.top) (hS : Sem P.κ ds inp = .error .cap) :
    ExC (semAtF P ds (ds.length - 1) []) H := by
  obtain ⟨hsl, hts, hlast⟩ := id hTy
  have hne : sigs ≠ [] := by intro e; simp [e] at hlast
  have hpos : 0 < ds.length := by have := List.length_pos_iff.2 hne; omega
  have hk : ds.length - 1 < ds.length := by omega
  have hsk : sigs[ds.length - 1]? = some ([], [.b]) := by
    rw [List.getLast?_eq_getElem?] at hlast; rw [← hsl]; exact hlast
  obtain ⟨ps, rs, -, -, -, hall⟩ := prog_three P ds sigs Ks inp hTy hO hK2 hc29 hinp hil hκ ds.length (Nat.le_refl _)
  obtain ⟨R, -, -, -, -, f, hf, -, -, hDC⟩ := hall (ds.length - 1) hk
  have hsg : sigs.getD (ds.length - 1) ([], []) = ([], [.b]) := by simp [List.getD_eq_getElem?_getD, hsk]
  rw [hsg] at hDC
  obtain ⟨t1, -, -, -⟩ := hts (ds.length - 1) _ _ (List.getElem?_eq_getElem hk) hsk
  have hnpw : (dA ds (ds.length - 1)).npw = 0 := by rw [dA_get ds _ hk]; simpa using t1
  rw [hnpw, List.take_zero] at hDC
  have hA0 : AHeap P.hb P.κ H (fun _ => none) := ⟨fun a l h => (by cases h), fun a b _ h _ => (by simp at h)⟩
  have hAr : ArgsR (fun _ => none) [] [] [] :=
    ⟨rfl, rfl, fun j x u h => by simp at h, fun j x h => by simp at h, fun j j' l l' u u' _ h => by simp at h⟩
  have hml := means_len inp P.κ ds []
  simp only [List.length_nil, Nat.zero_add] at hml
  have hf' : (means inp P.κ [] ds)[ds.length - 1]? = some f := by simpa using hf
  unfold Sem at hS
  rw [List.getLast?_eq_getElem?, hml, hf'] at hS
  have hfc : f [] = .error .cap := by
    simp only at hS; split at hS
    · cases hS
    · cases hS
    · rename_i e he; cases hS; exact he
  exact hDC _ [] [] H hA0 h8 hhb rfl hAr hfc

mutual
theorem svF_T (K : SC) (fsX : Nat → SemDX) (T' : Nat → Nat) : ∀ e : ParSpec.Nd, svF { K with T := T' } fsX e = svF K fsX e
  | .const _ => by simp only [svF]
  | .loc _ _ => by simp only [svF]
  | .bin op a b => by simp only [svF]; rw [svF_T K fsX T' a, svF_T K fsX T' b]
  | .ite c a b t e => by simp only [svF]; rw [svF_T K fsX T' a, svF_T K fsX T' b, svF_T K fsX T' t, svF_T K fsX T' e]
  | .letE s w v b => by simp only [svF]; rw [svF_T K fsX T' v, svF_T K fsX T' b]
  | .pair cs => by simp only [svF]; rw [svLF_T K fsX T' cs]
  | .call id as => by simp only [svF]; rw [svLF_T K fsX T' as]
  | .prim pn as => by simp only [svF]; rw [svLF_T K fsX T' as]; rfl
  | .loop z s => by simp only [svF]; rw [stF_T K fsX T' z, stF_T K fsX T' s]
  | .cont _ => by simp only [svF]
theorem stF_T (K : SC) (fsX : Nat → SemDX) (T' : Nat → Nat) : ∀ e : ParSpec.Nd, stF { K with T := T' } fsX e = stF K fsX e
  | .ite c a b t e => by simp only [stF]; rw [svF_T K fsX T' a, svF_T K fsX T' b, stF_T K fsX T' t, stF_T K fsX T' e]
  | .letE s w v b => by simp only [stF]; rw [svF_T K fsX T' v, stF_T K fsX T' b]
  | .cont e => by simp only [stF]; rw [svF_T K fsX T' e]
  | .const _ => by simp only [stF]; rw [svF_T K fsX T' (.const _)]
  | .loc _ _ => by simp only [stF]; rw [svF_T K fsX T' (.loc _ _)]
  | .bin op a b => by simp only [stF]; rw [svF_T K fsX T' (.bin op a b)]
  | .pair cs => by simp only [stF]; rw [svF_T K fsX T' (.pair cs)]
  | .call id as => by simp only [stF]; rw [svF_T K fsX T' (.call id as)]
  | .prim pn as => by simp only [stF]; rw [svF_T K fsX T' (.prim pn as)]
  | .loop z s => by simp only [stF]; rw [svF_T K fsX T' (.loop z s)]
theorem svLF_T (K : SC) (fsX : Nat → SemDX) (T' : Nat → Nat) :
    ∀ cs : List ParSpec.Nd, svLF { K with T := T' } fsX cs = svLF K fsX cs
  | [] => by simp only [svLF]
  | c :: cs => by simp only [svLF]; rw [svF_T K fsX T' c, svLF_T K fsX T' cs, wd_T K T' c]
end

/-- `semAtF` does not depend on the def table T -/
theorem semAtF_T (P : Templates.PC) (T' : Nat → Nat) (ds : List ParSpec.DefA) :
    ∀ k, semAtF ⟨P.κ, P.hb, P.c29, P.inp, T'⟩ ds k = semAtF P ds k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rw [semAtF, semAtF]
    have e : scAt ⟨P.κ, P.hb, P.c29, P.inp, T'⟩ ds k = { scAt P ds k with T := T' } := by
      simp only [scAt]
      congr 1
      funext n
      split
      · exact semAt_T P T' ds n
      · rfl
    have e2 : (fun n => if _h : n < k then semAtF ⟨P.κ, P.hb, P.c29, P.inp, T'⟩ ds n else dfltF) =
        (fun n => if _h : n < k then semAtF P ds n else dfltF) := by
      funext n; split
      · exact ih n ‹_›
      · rfl
    rw [e, e2, svF_T]

/-- **the cap theorem, E's form**: if `Sem` stops with `cap`, one room bound `R` (independent of the work block's base
and of the def table) makes main's kinded E semantics report `cap` -/
theorem main_capR (ds : List ParSpec.DefA) (sigs : List Sig) (Ks : List (List Nat)) (inp : List UInt8)
    (hTy : TyProg ds sigs) (hO : OwnSpec.progOk [] [] Ks ds = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hil : inp.length < 2 ^ 64) (κ : Nat) (hκ : κ < 2 ^ 40) (hS : Sem κ ds inp = .error .cap) :
    ∃ R, ∀ (P : Templates.PC) (base len : Nat), P.κ = κ → P.hb = base + 16 → P.c29 = UInt64.ofNat inp.length →
      P.inp = inpW inp → base % 8 = 0 → base + len ≤ 2 ^ 32 → R ≤ len →
      semAtF P ds (ds.length - 1) [] ((base + len) / 8 * 8) ⟨base + 16, fun _ => none⟩ = .error .cap := by
  let P0 : Nat → Templates.PC := fun b => ⟨κ, b + 16, UInt64.ofNat inp.length, inpW inp, fun _ => 0⟩
  let Q : Nat → Nat → Prop := fun b N => ∀ len, b % 8 = 0 → b + len ≤ 2 ^ 32 → N ≤ len →
    semAtF (P0 b) ds (ds.length - 1) [] ((b + len) / 8 * 8) ⟨b + 16, fun _ => none⟩ = .error .cap
  have hmono : ∀ b N N', N ≤ N' → Q b N → Q b N' := fun b N N' hle hQ len h1 h2 h3 => hQ len h1 h2 (by omega)
  obtain ⟨R, hR⟩ := unif_fin Q hmono (2 ^ 32 + 1) (fun b _ => by
    by_cases h8 : b % 8 = 0
    · obtain ⟨N, hN⟩ := main_cap (P0 b) ds sigs Ks inp hTy hO hK2 rfl rfl hil hκ ⟨b + 16, fun _ => none⟩
        (by show (b + 16) % 8 = 0; omega) (Nat.le_refl _) hS
      refine ⟨N + 24, fun len _ h2 h3 => hN _ ?_ ?_⟩
      · show b + 16 + N ≤ (b + len) / 8 * 8; omega
      · omega
    · exact ⟨0, fun len h1 => absurd h1 h8⟩)
  refine ⟨R, fun P base len e1 e2 e3 e4 h8 h2 h3 => ?_⟩
  have hP : P = ⟨(P0 base).κ, (P0 base).hb, (P0 base).c29, (P0 base).inp, P.T⟩ := by
    cases P; simp only [P0] at *; subst e1 e2 e3 e4; rfl
  rw [hP, semAtF_T (P0 base) P.T ds]
  exact hR base (by omega) len h8 h2 h3

end NanoMain
