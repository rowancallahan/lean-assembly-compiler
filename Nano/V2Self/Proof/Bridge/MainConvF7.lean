/- Nano/V2Self/Proof/Bridge/MainConvF7: the failure kinds forward — the program, and E's all-room statement: at ANY work size,
main's kinded E semantics returns `Sem`'s result, or `room`, or `cap` exactly when `Sem` stops with `cap`. -/
import Nano.V2Self.Proof.Bridge.MainConvF6

namespace NanoMain
open Templates

/-- **every def meets its contract** (by induction over the program, O's walk accumulating parameter / result kinds) -/
theorem prog_fail (P : Templates.PC) (ds : List ParSpec.DefA) (sigs : List Sig) (Ks : List (List Nat)) (inp : List UInt8)
    (hTy : TyProg ds sigs) (hO : OwnSpec.progOk [] [] Ks ds = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hc29 : P.c29 = UInt64.ofNat inp.length) (hinp : P.inp = inpW inp) (hil : inp.length < 2 ^ 64) :
    ∀ n, n ≤ ds.length → ∃ ps rs, ps.length = n ∧ rs.length = n ∧
      OwnSpec.progOk ps rs (Ks.drop n) (ds.drop n) = true ∧
      ∀ i (hi : i < n), ∃ R, rs[i]? = some R ∧ (∀ x ∈ R, x ≤ 1) ∧ R.length = (dA ds i).nres ∧
        ps[i]? = some ((Ks.getD i []).take (dA ds i).npw) ∧
        ∃ f, (means inp P.κ [] ds)[i]? = some f ∧
          DefR P.hb P.κ (sigs.getD i ([], [])).1 ((Ks.getD i []).take (dA ds i).npw) R f (semAt P ds i) ∧
          DefFail P.hb P.κ (sigs.getD i ([], [])).1 ((Ks.getD i []).take (dA ds i).npw) f (semAtF P ds i) := by
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
          obtain ⟨R0, h0, -, -, hp0, f, hf, hdr, -⟩ := hall i hi
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
      have hCF : CallFail ⟨inp, P.κ, (means inp P.κ [] ds).take n⟩ (scAt P ds n)
          (fun m => if _h : m < n then semAtF P ds m else dfltF) ⟨ps, rs, K, ds[n].npw⟩ (sigs.take n) :=
        (fun i P' R' hp hr => by
          have hi : i < n := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨R0, h0, -, -, hp0, f, hf, -, hdr⟩ := hall i hi
          simp only at hp hr; rw [hp] at hp0; cases hp0; rw [hr] at h0; cases h0
          refine ⟨f, by simp only; rw [List.getElem?_take_of_lt hi]; exact hf, fun sg' hs => ?_⟩
          rw [List.getElem?_take_of_lt hi] at hs
          have : sigs.getD i ([], []) = sg' := by simp [List.getD_eq_getElem?_getD, hs]
          rw [this] at hdr
          simp only [dif_pos hi]; exact hdr)
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
      have hDC := def_fail ⟨inp, P.κ, (means inp P.κ [] ds).take n⟩ (scAt P ds n)
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
        hCR hCF
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
          refine ⟨hDR, ?_⟩
          rw [semAtF, hda]; exact hDC
    · simp at hpo

/-- **main, failure kinds**: at any stack pointer, if main's kinded E semantics fails, the failure is `room`, or `cap`
with `Sem` stopping with `cap` -/
theorem main_kind (P : Templates.PC) (ds : List ParSpec.DefA) (sigs : List Sig) (Ks : List (List Nat)) (inp : List UInt8)
    (hTy : TyProg ds sigs) (hO : OwnSpec.progOk [] [] Ks ds = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hc29 : P.c29 = UInt64.ofNat inp.length) (hinp : P.inp = inpW inp) (hil : inp.length < 2 ^ 64)
    (sp : Nat) (H : Hp) (h8 : H.top % 8 = 0) (hhb : P.hb ≤ H.top) (fl : Fail)
    (h : semAtF P ds (ds.length - 1) [] sp H = .error fl) : FailOK fl (Sem P.κ ds inp) := by
  obtain ⟨hsl, hts, hlast⟩ := id hTy
  have hne : sigs ≠ [] := by intro e; simp [e] at hlast
  have hpos : 0 < ds.length := by have := List.length_pos_iff.2 hne; omega
  have hk : ds.length - 1 < ds.length := by omega
  have hsk : sigs[ds.length - 1]? = some ([], [.b]) := by
    rw [List.getLast?_eq_getElem?] at hlast; rw [← hsl]; exact hlast
  obtain ⟨ps, rs, -, -, -, hall⟩ := prog_fail P ds sigs Ks inp hTy hO hK2 hc29 hinp hil ds.length (Nat.le_refl _)
  obtain ⟨R, -, -, -, -, f, hf, -, hDF⟩ := hall (ds.length - 1) hk
  have hsg : sigs.getD (ds.length - 1) ([], []) = ([], [.b]) := by simp [List.getD_eq_getElem?_getD, hsk]
  rw [hsg] at hDF
  obtain ⟨t1, -, -, -⟩ := hts (ds.length - 1) _ _ (List.getElem?_eq_getElem hk) hsk
  have hnpw : (dA ds (ds.length - 1)).npw = 0 := by rw [dA_get ds _ hk]; simpa using t1
  rw [hnpw, List.take_zero] at hDF
  have hA0 : AHeap P.hb P.κ H (fun _ => none) := ⟨fun a l h => (by cases h), fun a b _ h _ => (by simp at h)⟩
  have hAr : ArgsR (fun _ => none) [] [] [] :=
    ⟨rfl, rfl, fun j x u h => by simp at h, fun j x h => by simp at h, fun j j' l l' u u' _ h => by simp at h⟩
  have hml := means_len inp P.κ ds []
  simp only [List.length_nil, Nat.zero_add] at hml
  have hf' : (means inp P.κ [] ds)[ds.length - 1]? = some f := by simpa using hf
  rcases hDF _ [] [] sp H fl hA0 h8 hhb rfl hAr h with h' | ⟨h1, h2⟩
  · exact .inl h'
  · refine .inr ⟨h1, ?_⟩
    unfold Sem
    rw [List.getLast?_eq_getElem?, hml, hf']
    simp only [h2]

/-- **E's all-room statement**: for every work block, main's kinded E semantics from the empty heap returns `Sem`'s
result, or fails by `room`, or reports `cap` exactly when `Sem` does -/
theorem main_all (P : Templates.PC) (ds : List ParSpec.DefA) (sigs : List Sig) (Ks : List (List Nat)) (inp : List UInt8)
    (hTy : TyProg ds sigs) (hO : OwnSpec.progOk [] [] Ks ds = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hc29 : P.c29 = UInt64.ofNat inp.length) (hinp : P.inp = inpW inp) (hil : inp.length < 2 ^ 64)
    (sp : Nat) (H : Hp) (h8 : H.top % 8 = 0) (hhb : P.hb ≤ H.top) :
    (∃ a l H', semAtF P ds (ds.length - 1) [] sp H = .ok ([a], H') ∧ BufAt P.hb P.κ H' a l ∧
      Sem P.κ ds inp = .ok (l.map UInt64.toUInt8)) ∨
    semAtF P ds (ds.length - 1) [] sp H = .error .room ∨
    (semAtF P ds (ds.length - 1) [] sp H = .error .cap ∧ Sem P.κ ds inp = .error .cap) := by
  cases hr : semAtF P ds (ds.length - 1) [] sp H with
  | ok r =>
    left
    have hs : semAt P ds (ds.length - 1) [] sp H = some r := by
      rw [← oD_semAt]; simp only [oD, hr]; rfl
    obtain ⟨a, l, e, hb, hS⟩ := main_bridge P ds sigs Ks inp hTy hO hK2 hc29 hinp hil sp H r.1 r.2 h8 hhb hs
    exact ⟨a, l, r.2, by rw [← e], hb, hS⟩
  | error fl =>
    rcases main_kind P ds sigs Ks inp hTy hO hK2 hc29 hinp hil sp H h8 hhb fl hr with rfl | ⟨rfl, hS⟩
    · exact .inr (.inl rfl)
    · exact .inr (.inr ⟨rfl, hS⟩)

end NanoMain
