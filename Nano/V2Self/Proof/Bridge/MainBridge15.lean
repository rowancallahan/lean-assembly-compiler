/- Nano/V2Self/Proof/Bridge/MainBridge15: the Sem ⇐ sv bridge — the program: every def meets its contract (`prog_ok`), and
main's E semantics determines `Sem` (`main_bridge`). -/
import Nano.V2Self.Proof.Bridge.MainBridge14
import Nano.V2Self.Proof.Machine.NdProg

namespace NanoMain
open Templates

/-! ## `Sem`'s def meanings, one by one -/

theorem means_len (inp : List UInt8) (κ : Nat) : ∀ (ds : List ParSpec.DefA) (ms : List (List W → Except Stop (List W))),
    (means inp κ ms ds).length = ms.length + ds.length
  | [], ms => by simp [means]
  | d :: r, ms => by rw [means, means_len inp κ r]; simp; omega

theorem means_take (inp : List UInt8) (κ : Nat) : ∀ (ds : List ParSpec.DefA) (ms : List (List W → Except Stop (List W))),
    (means inp κ ms ds).take ms.length = ms
  | [], ms => by simp [means]
  | d :: r, ms => by
    rw [means]
    have := means_take inp κ r (ms ++ [defMean inp κ ms d])
    have h3 : List.take ms.length (means inp κ (ms ++ [defMean inp κ ms d]) r) =
        List.take ms.length (List.take (ms ++ [defMean inp κ ms d]).length (means inp κ (ms ++ [defMean inp κ ms d]) r)) := by
      rw [List.take_take]; congr 1; simp
    rw [h3, this]; simp

theorem means_get (inp : List UInt8) (κ : Nat) : ∀ (ds : List ParSpec.DefA) (ms : List (List W → Except Stop (List W)))
    (k : Nat) (hk : k < ds.length),
    (means inp κ ms ds)[ms.length + k]? = some (defMean inp κ ((means inp κ ms ds).take (ms.length + k)) ds[k])
  | [], _, k, hk => by simp at hk
  | d :: r, ms, 0, _ => by
    rw [means]
    have ht := means_take inp κ r (ms ++ [defMean inp κ ms d])
    have hl := means_len inp κ r (ms ++ [defMean inp κ ms d])
    have e1 : (means inp κ (ms ++ [defMean inp κ ms d]) r)[ms.length]? = some (defMean inp κ ms d) := by
      have := congrArg (·[ms.length]?) ht
      simp only at this
      rw [List.getElem?_take_of_lt (by simp)] at this
      rw [this]; simp
    have e2 : (means inp κ (ms ++ [defMean inp κ ms d]) r).take ms.length = ms := by
      have := congrArg (List.take ms.length) ht
      simp only [List.take_take] at this
      rw [show min ms.length (ms ++ [defMean inp κ ms d]).length = ms.length by simp] at this
      rw [this]; simp
    simp only [Nat.add_zero, List.getElem_cons_zero]
    rw [e1, e2]
  | d :: r, ms, k + 1, hk => by
    rw [means]
    have := means_get inp κ r (ms ++ [defMean inp κ ms d]) k (by simpa using hk)
    simp only [List.length_append, List.length_singleton] at this
    rw [show ms.length + (k + 1) = ms.length + 1 + k by omega, this]
    simp

theorem ctxOK_take {inp : List UInt8} {κ : Nat} {ms : List (List W → Except Stop (List W))} {D : List Sig}
    (h : CtxOK ⟨inp, κ, ms⟩ D) (k : Nat) : CtxOK ⟨inp, κ, ms.take k⟩ (D.take k) := by
  obtain ⟨hl, hr⟩ := h
  refine ⟨by simp [hl], fun i f sg hf hs => ?_⟩
  simp only [List.getElem?_take] at hf hs
  split at hf
  · rw [if_pos (by assumption)] at hs; exact hr i f sg hf hs
  · simp at hf

/-! ## O's program walk -/

theorem join_le1 {a b k : List Nat} (ha : ∀ x ∈ a, x ≤ 1) (hb : ∀ x ∈ b, x ≤ 1) (h : OwnSpec.join a b = some k) :
    ∀ x ∈ k, x ≤ 1 := by
  unfold OwnSpec.join at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact hb
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact ha
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact max_le1 _ _ ha hb
      · cases h

theorem defOk_res {ps rs : List (List Nat)} {K : List Nat} {d : ParSpec.DefA} {R : List Nat}
    (h : OwnSpec.defOk ps rs K d = some R) :
    K.length = d.nslots ∧ d.npw ≤ d.nslots ∧ R.length = d.nres ∧ ∀ x ∈ R, x ≤ 1 := by
  unfold OwnSpec.defOk at h
  split at h
  · rename_i hc
    obtain ⟨k, hr, hk⟩ := Option.bind_eq_some_iff.1 h
    split at hk
    · simp only [Option.some.injEq] at hk; subst hk
      refine ⟨hc.1, hc.2, by assumption, ?_⟩
      split at hr
      · obtain ⟨z0, -, h⟩ := Option.bind_eq_some_iff.1 hr
        obtain ⟨z1, hz1, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨s0, -, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨s1, hs1, hj⟩ := Option.bind_eq_some_iff.1 h
        exact join_le1 (tr_le1 _ _ _ _ hz1) (tr_le1 _ _ _ _ hs1) hj
      · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.1 hr
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
        exact tr_le1 _ _ _ _ hy
    · cases hk
  · cases h

theorem dA_get (ds : List ParSpec.DefA) (n : Nat) (hn : n < ds.length) : dA ds n = ds[n] := by
  simp [dA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

/-- **every def meets its contract** (by induction over the program, O's walk accumulating parameter / result kinds) -/
theorem prog_ok (P : Templates.PC) (ds : List ParSpec.DefA) (sigs : List Sig) (Ks : List (List Nat)) (inp : List UInt8)
    (hTy : TyProg ds sigs) (hO : OwnSpec.progOk [] [] Ks ds = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hc29 : P.c29 = UInt64.ofNat inp.length) (hinp : P.inp = inpW inp) (hil : inp.length < 2 ^ 64) :
    ∀ n, n ≤ ds.length → ∃ ps rs, ps.length = n ∧ rs.length = n ∧
      OwnSpec.progOk ps rs (Ks.drop n) (ds.drop n) = true ∧
      ∀ i (hi : i < n), ∃ R, rs[i]? = some R ∧ (∀ x ∈ R, x ≤ 1) ∧ R.length = (dA ds i).nres ∧
        ps[i]? = some ((Ks.getD i []).take (dA ds i).npw) ∧
        ∃ f, (means inp P.κ [] ds)[i]? = some f ∧
          DefR P.hb P.κ (sigs.getD i ([], [])).1 ((Ks.getD i []).take (dA ds i).npw) R f (semAt P ds i) := by
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
        (fun i P' R' hp hr => by
          have hi : i < n := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨R0, h0, -, -, hp0, f, hf, hdr⟩ := hall i hi
          simp only at hp hr; rw [hp] at hp0; cases hp0; rw [hr] at h0; cases h0
          refine ⟨f, by simp only; rw [List.getElem?_take_of_lt hi]; exact hf, fun sg' hs => ?_⟩
          rw [List.getElem?_take_of_lt hi] at hs
          have : sigs.getD i ([], []) = sg' := by simp [List.getD_eq_getElem?_getD, hs]
          rw [this] at hdr
          have hfs : (scAt P ds n).fs i = semAt P ds i := by simp [scAt, hi]
          rw [hfs]; exact hdr)
        (ctxOK_take hC n)
        (fun s => by
          rw [List.getD_eq_getElem?_getD]
          cases h : K[s]? with
          | none => simp
          | some k => exact hK2 K hKmem k (List.mem_of_getElem? h))
        ds[n] sigs[n] R ⟨t1, t2, t3, t4⟩ hd rfl (by simp only [scAt, hda]; rfl)
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
          refine ⟨R, by simp [hl2], hR1, by rw [hda]; exact hRl, by simp [hl1, hda]; rw [← hKn]; simp [List.getD_eq_getElem?_getD]; rfl, ?_⟩
          have hmg := means_get inp P.κ ds [] i (by omega)
          simp only [List.length_nil, Nat.zero_add] at hmg
          refine ⟨_, hmg, ?_⟩
          rw [semAt_eq, hda, show sigs.getD i ([], []) = sigs[i] by simp [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hsn], hKn]
          exact hDR
    · simp at hpo

/-- **main**: if E's semantics of the last def (main, no parameters) returns `vs`, then `vs` is one buffer word whose
block holds `l`, and `Sem` returns the low bytes of `l` -/
theorem main_bridge (P : Templates.PC) (ds : List ParSpec.DefA) (sigs : List Sig) (Ks : List (List Nat)) (inp : List UInt8)
    (hTy : TyProg ds sigs) (hO : OwnSpec.progOk [] [] Ks ds = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hc29 : P.c29 = UInt64.ofNat inp.length) (hinp : P.inp = inpW inp) (hil : inp.length < 2 ^ 64)
    (sp : Nat) (H : Hp) (vs : List UInt64) (H' : Hp) (h8 : H.top % 8 = 0) (hhb : P.hb ≤ H.top)
    (hs : semAt P ds (ds.length - 1) [] sp H = some (vs, H')) :
    ∃ a l, vs = [a] ∧ BufAt P.hb P.κ H' a l ∧ Sem P.κ ds inp = .ok (l.map UInt64.toUInt8) := by
  have hTy' := hTy
  obtain ⟨hsl, hts, hlast⟩ := hTy'
  have hne : sigs ≠ [] := by intro e; simp [e] at hlast
  have hpos : 0 < ds.length := by have := List.length_pos_iff.2 hne; omega
  have hk : ds.length - 1 < ds.length := by omega
  have hsk : sigs[ds.length - 1]? = some ([], [.b]) := by
    rw [List.getLast?_eq_getElem?] at hlast; rw [← hsl]; exact hlast
  obtain ⟨ps, rs, -, -, -, hall⟩ := prog_ok P ds sigs Ks inp hTy hO hK2 hc29 hinp hil ds.length (Nat.le_refl _)
  obtain ⟨R, -, -, hRl, -, f, hf, hDR⟩ := hall (ds.length - 1) hk
  have hsg : sigs.getD (ds.length - 1) ([], []) = ([], [.b]) := by simp [List.getD_eq_getElem?_getD, hsk]
  rw [hsg] at hDR
  obtain ⟨t1, -, t3, -⟩ := hts (ds.length - 1) _ _ (List.getElem?_eq_getElem hk) hsk
  have hnpw : (dA ds (ds.length - 1)).npw = 0 := by rw [dA_get ds _ hk]; simpa using t1
  rw [hnpw, List.take_zero] at hDR
  have hA0 : AHeap P.hb P.κ H (fun _ => none) := ⟨fun a l h => (by cases h), fun a b _ h _ => (by simp at h)⟩
  have hAr : ArgsR (fun _ => none) [] [] [] :=
    ⟨rfl, rfl, fun j x u h => by simp at h, fun j x h => by simp at h, fun j j' l l' u u' _ h => by simp at h⟩
  obtain ⟨σ', res, hfres, hA', -, -, l1, l2, c1, -⟩ := hDR _ [] [] sp H vs H' hA0 h8 hhb rfl hAr hs
  have hR1 : R.length = 1 := by rw [hRl, dA_get ds _ hk]; simpa using t3.symm
  -- the result kinds
  have hC := means_ok inp P.κ ds [] [] sigs ⟨rfl, by simp⟩ hsl (by simpa using hts)
  simp only [List.nil_append] at hC
  have hml := means_len inp P.κ ds []
  simp only [List.length_nil, Nat.zero_add] at hml
  have hresp := hC.2 (ds.length - 1) f ([], [.b]) (by simpa using hf) hsk
  have kres := (hresp [] rfl).2 res hfres
  obtain ⟨l, rfl⟩ := kOf_b kres
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 (show vs.length = 1 by omega)
  obtain ⟨e, he⟩ := List.length_eq_one_iff.1 hR1
  have vr := (c1 0 e (.b l) a (by simp [he]) rfl rfl).1
  refine ⟨a, l, rfl, bufAt_of hA' vr, ?_⟩
  unfold Sem
  rw [List.getLast?_eq_getElem?, hml]
  have hf' : (means inp P.κ [] ds)[ds.length - 1]? = some f := by simpa using hf
  rw [hf']
  simp [hfres]

end NanoMain
