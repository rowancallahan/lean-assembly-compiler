/- Nano/V2Self/Proof/Bridge/MainOk: E's side conditions of the node theorem (`Templates.OkV` / `OkT`, Proof/NdRun.lean) hold for
every def of a parsed program.  From the kind judgment (`MainTy.TyN`/`TyB`, produced by the parser per `MainTyP`):
reads hit known slots, let writes hit fresh slots (so every read/write disjointness holds), widths = kind counts. -/
import Nano.V2Self.Proof.Parser.MainTyP
import Nano.V2Self.Proof.Machine.NdRun
import Nano.V2Self.Proof.Machine.NdWidth

namespace NanoMain
open ParSpec Templates

theorem setK_get_out {Γ : List (Option Kd)} {s : Nat} {ks : List Kd} (h : s + ks.length ≤ Γ.length) (k : Nat)
    (hk : k < s ∨ s + ks.length ≤ k) : (setK Γ s ks)[k]? = Γ[k]? := by
  rcases hk with hk | hk
  · unfold setK
    rw [List.append_assoc, List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hk]
  · exact setK_get_above h k hk

theorem setK_get_in {Γ : List (Option Kd)} {s : Nat} {ks : List Kd} (h : s + ks.length ≤ Γ.length) (k : Nat)
    (h1 : s ≤ k) (h2 : k < s + ks.length) : ∃ kd, (setK Γ s ks)[k]? = some (some kd) := by
  unfold setK
  have hl : (List.take s Γ).length = s := by simp; omega
  rw [List.append_assoc, List.getElem?_append_right (by omega), hl, List.getElem?_append_left (by simp; omega)]
  refine ⟨ks[k - s]'(by omega), ?_⟩
  simp

theorem known_get {Γ : List (Option Kd)} {s w : Nat} {ks : List Kd} (h : known Γ s w ks) (k : Nat) (h1 : s ≤ k)
    (h2 : k < s + w) : ∃ kd, Γ[k]? = some (some kd) := by
  obtain ⟨hl, he⟩ := h
  have := congrArg (·[k - s]?) he
  simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_map] at this
  rw [if_pos (by omega), show s + (k - s) = k by omega] at this
  cases hk : ks[k - s]? with
  | none =>
    rw [hk] at this
    have : k < Γ.length := by omega
    simp_all
  | some kd => rw [hk] at this; exact ⟨kd, by simpa using this⟩

mutual
/-- reads hit known slots -/
theorem rd_known {D : List Sig} : ∀ {Γ S e ks}, TyN D Γ S e ks → ∀ k, Templates.rd e k → ∃ kd, Γ[k]? = some (some kd)
  | _, _, _, _, .const, k, h => by simp [Templates.rd] at h
  | _, _, _, _, .loc hk, k, h => by simp only [Templates.rd] at h; exact known_get hk k h.1 h.2
  | _, _, _, _, .bin _ _ ha hb, k, h => by
    simp only [Templates.rd] at h; rcases h with h | h; exact rd_known ha k h; exact rd_known hb k h
  | _, _, _, _, .ite _ ha hb ht he, k, h => by
    simp only [Templates.rd] at h
    rcases h with (h | h) | h | h
    · exact rd_known ha k h
    · exact rd_known hb k h
    · exact rd_known ht k h
    · exact rd_known he k h
  | _, _, _, _, .letE (s := s) (vs := vs) hv hw hs _ hb, k, h => by
    simp only [Templates.rd] at h
    rcases h with h | ⟨h, hn⟩
    · exact rd_known hv k h
    · obtain ⟨kd, e⟩ := rd_known hb k h
      rw [setK_get_out (ks := vs) (by omega) k (by omega)] at e; exact ⟨kd, e⟩
  | _, _, _, _, .pair hl, k, h => by simp only [Templates.rd] at h; exact rdL_known hl k h
  | _, _, _, _, .call hl _, k, h => by simp only [Templates.rd] at h; exact rdL_known hl k h
  | _, _, _, _, .prim hl _ _, k, h => by simp only [Templates.rd] at h; exact rdL_known hl k h
  | _, _, _, _, .cont he, k, h => by simp only [Templates.rd] at h; exact rd_known he k h
theorem rdL_known {D : List Sig} : ∀ {Γ cs ks}, TyL D Γ cs ks → ∀ k, rdL cs k → ∃ kd, Γ[k]? = some (some kd)
  | _, _, _, .nil, k, h => by simp [rdL] at h
  | _, _, _, .cons hn hr, k, h => by
    simp only [rdL] at h; rcases h with h | h; exact rd_known hn k h; exact rdL_known hr k h
end

mutual
/-- let writes hit fresh slots -/
theorem wr_fresh {D : List Sig} (p : Nat) : ∀ {Γ S e ks}, TyN D Γ S e ks → ∀ k, wr p e k → Γ[k]? = some none
  | _, _, _, _, .const, k, h => by simp [wr] at h
  | _, _, _, _, .loc _, k, h => by simp [wr] at h
  | _, _, _, _, .bin _ _ ha hb, k, h => by
    simp only [wr] at h; rcases h with h | h; exact wr_fresh p ha k h; exact wr_fresh p hb k h
  | _, _, _, _, .ite _ ha hb ht he, k, h => by
    simp only [wr] at h
    rcases h with (h | h) | h | h
    · exact wr_fresh p ha k h
    · exact wr_fresh p hb k h
    · exact wr_fresh p ht k h
    · exact wr_fresh p he k h
  | _, _, _, _, .letE (s := s) (vs := vs) hv hw hs hf hb, k, h => by
    simp only [wr] at h
    rcases h with h | h | h
    · exact wr_fresh p hv k h
    · exact hf k h.1 h.2
    · have e := wr_fresh p hb k h
      have hvs := hw ▸ hs
      by_cases hin : s ≤ k ∧ k < s + vs.length
      · obtain ⟨kd, e'⟩ := setK_get_in hvs k hin.1 hin.2; rw [e'] at e; cases e
      · rw [setK_get_out (by omega) k (by omega)] at e; exact e
  | _, _, _, _, .pair hl, k, h => by simp only [wr] at h; exact wrL_fresh p hl k h
  | _, _, _, _, .call hl _, k, h => by simp only [wr] at h; exact wrL_fresh p hl k h
  | _, _, _, _, .prim hl _ _, k, h => by simp only [wr] at h; exact wrL_fresh p hl k h
  | _, _, _, _, .cont he, k, h => by simp only [wr] at h; exact wr_fresh p he k h
theorem wrL_fresh {D : List Sig} (p : Nat) : ∀ {Γ cs ks}, TyL D Γ cs ks → ∀ k, wrL p cs k → Γ[k]? = some none
  | _, _, _, .nil, k, h => by simp [wrL] at h
  | _, _, _, .cons hn hr, k, h => by
    simp only [wrL] at h; rcases h with h | h; exact wr_fresh p hn k h; exact wrL_fresh p hr k h
end

/-- a read is never a let write of a term typed under the same `Γ` -/
theorem rw_disj {D : List Sig} {Γ S S' e e' ks ks'} (p : Nat) (h : TyN D Γ S e ks) (h' : TyN D Γ S' e' ks') :
    ∀ k, Templates.rd e k → ¬ wr p e' k := fun k hr hw => by
  obtain ⟨kd, e1⟩ := rd_known h k hr; rw [wr_fresh p h' k hw] at e1; cases e1

theorem rdL_disj {D : List Sig} {Γ S e cs ks ks'} (p : Nat) (h : TyL D Γ cs ks) (h' : TyN D Γ S e ks') :
    ∀ k, rdL cs k → ¬ wr p e k := fun k hr hw => by
  obtain ⟨kd, e1⟩ := rdL_known h k hr; rw [wr_fresh p h' k hw] at e1; cases e1

/-- `K`'s callee table agrees with the signatures `D` -/
def KD (K : SC) (D : List Sig) : Prop :=
  ∀ (i : Nat) sg, D[i]? = some sg → i < K.nd ∧ K.npwOf i = sg.1.length ∧ K.nresOf i = sg.2.length

theorem primK_ar {p : Nat} {ps rs : List Kd} (h : primK p ps = some rs) : rs.length = 1 ∧ ps.length = arity p := by
  unfold primK at h; split at h <;> cases h <;> simp [arity]

mutual
theorem wd_ok {K : SC} {D : List Sig} (hK : KD K D) : ∀ {Γ S e ks}, TyN D Γ S e ks → S = none →
    wd K e = ks.length ∧ wdT K e = ks.length
  | _, _, _, _, .const, _ => by simp [wd, wdT]
  | _, _, _, _, .loc hk, _ => by
    have := congrArg List.length hk.2; have := hk.1; simp at *; simp [wd, wdT]; omega
  | _, _, _, _, .bin _ _ _ _, _ => by simp [wd, wdT]
  | _, _, _, _, .ite _ _ _ ht _, hS => by
    have := wd_ok hK ht hS; simp only [wd, wdT]; exact this
  | _, _, _, _, .letE _ _ _ _ hb, hS => by
    have := wd_ok hK hb hS; simp only [wd, wdT]; exact this
  | _, _, _, _, .pair hl, _ => by have := wdL_ok hK hl; simp only [wd, wdT]; exact ⟨this, this⟩
  | _, _, _, _, .call (i := i) _ hd, _ => by have := (hK i _ hd).2.2; simp only [wd, wdT]; exact ⟨this, this⟩
  | _, _, _, _, .prim _ hp _, _ => by have := (primK_ar hp).1; simp only [wd, wdT]; omega
  | _, _, _, _, .cont _, hS => by cases hS
theorem wdL_ok {K : SC} {D : List Sig} (hK : KD K D) : ∀ {Γ cs ks}, TyL D Γ cs ks → wdL K cs = ks.length
  | _, _, _, .nil => by simp [wdL]
  | _, _, _, .cons hn hr => by
    have := (wd_ok hK hn rfl).1; have := wdL_ok hK hr; simp only [wdL, List.length_append]; omega
end

mutual
theorem okV {K : SC} {D : List Sig} (hK : KD K D) : ∀ {Γ S e ks}, TyN D Γ S e ks → S = none → Γ.length = K.nl → OkV K e
  | _, _, _, _, .const, _, _ => by simp [OkV]
  | _, _, _, _, .loc hk, _, hl => by simp only [OkV]; have := hk.1; omega
  | _, _, _, _, .bin h1 h2 ha hb, hS, hl => by
    simp only [OkV]
    exact ⟨okV hK ha rfl hl, okV hK hb rfl hl, (wd_ok hK ha rfl).1, (wd_ok hK hb rfl).1, rw_disj K.p hb ha⟩
  | _, _, _, _, .ite _ ha hb ht he, hS, hl => by
    subst hS
    simp only [OkV]
    refine ⟨okV hK ha rfl hl, okV hK hb rfl hl, okV hK ht rfl hl, okV hK he rfl hl, (wd_ok hK ha rfl).1,
      (wd_ok hK hb rfl).1, by rw [(wd_ok hK he rfl).1, (wd_ok hK ht rfl).1], rw_disj K.p hb ha,
      fun k r w => ?_, fun k r w => ?_⟩
    · rcases w with w | w; exact rw_disj K.p ht ha k r w; exact rw_disj K.p ht hb k r w
    · rcases w with w | w; exact rw_disj K.p he ha k r w; exact rw_disj K.p he hb k r w
  | _, _, _, _, .letE (s := s) (vs := vs) hv hw hs hf hb, hS, hl => by
    simp only [OkV]
    have hvs := hw ▸ hs
    refine ⟨okV hK hv rfl hl, okV hK hb hS (by rw [setK_length hvs]; exact hl), by rw [(wd_ok hK hv rfl).1, hw],
      by omega, fun k r hn w => ?_⟩
    obtain ⟨kd, e⟩ := rd_known hb k r
    rw [setK_get_out hvs k (by omega)] at e
    rw [wr_fresh K.p hv k w] at e; cases e
  | _, _, _, _, .pair hl', _, hl => by simp only [OkV]; exact okL hK hl' hl
  | _, _, _, _, .call (i := i) hl' hd, _, hl => by
    simp only [OkV]
    exact ⟨okL hK hl' hl, (hK i _ hd).1, by rw [wdL_ok hK hl', (hK i _ hd).2.1]⟩
  | _, _, _, _, .prim hl' hp h0, _, hl => by
    simp only [OkV]
    exact ⟨okL hK hl' hl, by rw [wdL_ok hK hl', (primK_ar hp).2], h0⟩
  | _, _, _, _, .cont _, hS, _ => by cases hS
theorem okL {K : SC} {D : List Sig} (hK : KD K D) : ∀ {Γ cs ks}, TyL D Γ cs ks → Γ.length = K.nl → OkL K cs
  | _, _, _, .nil, _ => by simp [OkL]
  | _, _, _, .cons hn hr, hl => by
    simp only [OkL]
    exact ⟨okV hK hn rfl hl, okL hK hr hl, fun k r w => by
      obtain ⟨kd, e⟩ := rdL_known hr k r; rw [wr_fresh K.p hn k w] at e; cases e⟩
end

theorem okT {K : SC} {D : List Sig} (hK : KD K D) : ∀ {Γ S e ks}, TyN D Γ S e ks → Γ.length = K.nl →
    (∀ sk, S = some sk → K.p = sk.length + 1 ∧ K.p ≤ K.nl) → OkT K e ks.length
  | Γ, _, .const v, _, .const, hl, _ => by
    have h : TyN D Γ none (.const v) [.w] := .const; simp only [OkT]; exact ⟨okV hK h rfl hl, (wd_ok hK h rfl).1⟩
  | _, _, _, _, .loc hk, hl, _ => by
    have h := TyN.loc (D := D) (S := none) hk; simp only [OkT]; exact ⟨okV hK h rfl hl, (wd_ok hK h rfl).1⟩
  | _, _, _, _, .bin h1 h2 ha hb, hl, _ => by
    have h := TyN.bin (S := none) h1 h2 ha hb; simp only [OkT]; exact ⟨okV hK h rfl hl, (wd_ok hK h rfl).1⟩
  | _, _, _, _, .pair hl', hl, _ => by
    have h := TyN.pair (S := none) hl'; simp only [OkT]; exact ⟨okV hK h rfl hl, (wd_ok hK h rfl).1⟩
  | _, _, _, _, .call hl' hd, hl, _ => by
    have h := TyN.call (S := none) hl' hd; simp only [OkT]; exact ⟨okV hK h rfl hl, (wd_ok hK h rfl).1⟩
  | _, _, _, _, .prim hl' hp h0, hl, _ => by
    have h := TyN.prim (S := none) hl' hp h0; simp only [OkT]; exact ⟨okV hK h rfl hl, (wd_ok hK h rfl).1⟩
  | _, _, _, _, .ite _ ha hb ht he, hl, hS => by
    simp only [OkT]
    refine ⟨okV hK ha rfl hl, okV hK hb rfl hl, okT hK ht hl hS, okT hK he hl hS, (wd_ok hK ha rfl).1,
      (wd_ok hK hb rfl).1, rw_disj K.p hb ha, fun k r w => ?_, fun k r w => ?_⟩
    · rcases w with w | w; exact rw_disj K.p ht ha k r w; exact rw_disj K.p ht hb k r w
    · rcases w with w | w; exact rw_disj K.p he ha k r w; exact rw_disj K.p he hb k r w
  | _, _, _, _, .letE (s := s) (vs := vs) hv hw hs hf hb, hl, hS => by
    simp only [OkT]
    have hvs := hw ▸ hs
    refine ⟨okV hK hv rfl hl, okT hK hb (by rw [setK_length hvs]; exact hl) hS, by rw [(wd_ok hK hv rfl).1, hw],
      by omega, fun k r hn w => ?_⟩
    obtain ⟨kd, e⟩ := rd_known hb k r
    rw [setK_get_out hvs k (by omega)] at e
    rw [wr_fresh K.p hv k w] at e; cases e
  | _, _, _, _, .cont (sk := sk) he, hl, hS => by
    obtain ⟨h1, h2⟩ := hS sk rfl
    simp only [OkT]
    exact ⟨okV hK he rfl hl, by rw [(wd_ok hK he rfl).1]; omega, by omega, h2⟩

theorem somes_eq : ∀ (a b : List Kd) (m n : Nat), a.map some ++ List.replicate m none = b.map some ++ List.replicate n none →
    a = b
  | [], [], _, _, _ => rfl
  | x :: a, y :: b, m, n, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq, Option.some.injEq] at h
    rw [h.1, somes_eq a b m n h.2]
  | [], y :: b, m, n, h => by cases m <;> simp [List.replicate_succ] at h
  | x :: a, [], m, n, h => by cases n <;> simp [List.replicate_succ] at h

/-- **a def body** (E's `OkV` at the def's frame `K.p`, `K.nl`) -/
theorem okBody {K : SC} {D : List Sig} (hK : KD K D) {ps : List Kd} {m : Nat} {e : Nd} {ks : List Kd}
    (h : TyB D (ps.map some ++ List.replicate m none) e ks) (hp : K.p = ps.length) (hl : ps.length + m = K.nl)
    (hq : K.q = ks.length) : OkV K e ∧ wd K e = ks.length := by
  have hlen : (ps.map some ++ List.replicate m none).length = K.nl := by simp; omega
  cases h with
  | plain h => exact ⟨okV hK h rfl hlen, (wd_ok hK h rfl).1⟩
  | loop hΓ hz hs =>
    rename_i z s sk n
    have hps : ps = Kd.w :: sk := somes_eq _ (Kd.w :: sk) m n (by rw [hΓ]; rfl)
    subst hps
    have hS : ∀ sk', some sk = some sk' → K.p = sk'.length + 1 ∧ K.p ≤ K.nl := by
      intro sk' e; cases e; simp at hp hl; omega
    have big : ∀ k, (some Kd.w :: sk.map some ++ List.replicate n none)[k]? = some none → K.p ≤ k := by
      intro k e
      refine Nat.le_of_not_lt (fun hk => ?_)
      simp at hp
      have : k < (some Kd.w :: sk.map some).length := by simp; omega
      rw [List.getElem?_append_left this] at e
      cases k with
      | zero => simp at e
      | succ k => simp at e
    rw [hΓ] at hlen hz hs
    simp only [OkV, wd]
    refine ⟨⟨by rw [hq]; exact okT hK hz hlen (fun _ e => by cases e), by rw [hq]; exact okT hK hs hlen hS,
      by simp at hp; omega, by simp at hp hlen; omega, fun k w => ?_, fun k r w => ?_⟩, hq⟩
    · rcases w with w | w
      · exact big k (wr_fresh K.p hz k w)
      · exact big k (wr_fresh K.p hs k w)
    · rcases r with r | r <;> rcases w with w | w
      · exact rw_disj K.p hz hz k r w
      · exact rw_disj K.p hz hs k r w
      · exact rw_disj K.p hs hz k r w
      · exact rw_disj K.p hs hs k r w

/-- **E's side conditions for every def of a parsed program**: at def `i`'s frame (`K.p` = npw, `K.nl` = nslots, the
callees = the earlier defs, `K.q` = nres), the body satisfies `OkV` and has width `nres`; also `npw ≤ nslots`. -/
theorem parsed_ok {ts : List UInt64} {p : List DefA} (h : ParsesProgram ts p) (i : Nat) (d : DefA) (hd : p[i]? = some d)
    (K : SC) (hp : K.p = d.npw) (hn : K.nl = d.nslots) (hi : K.nd = i) (hq : K.q = d.nres)
    (hc : ∀ j < i, ∀ dj, p[j]? = some dj → K.npwOf j = dj.npw ∧ K.nresOf j = dj.nres) :
    OkV K d.body ∧ wd K d.body = d.nres ∧ d.npw ≤ d.nslots := by
  obtain ⟨sigs, hl, ht, -⟩ := refParse_ty h
  have hil : i < sigs.length := by rw [hl]; exact (List.getElem?_eq_some_iff.1 hd).1
  obtain ⟨sg, hsg⟩ : ∃ sg, sigs[i]? = some sg := ⟨_, List.getElem?_eq_getElem hil⟩
  obtain ⟨h1, h2, h3, h4⟩ := ht i d sg hd hsg
  have hK : KD K (sigs.take i) := by
    intro j sgj hj
    rw [List.getElem?_take] at hj
    split at hj
    · rename_i hji
      have hjl : j < p.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hj).1
      obtain ⟨dj, hdj⟩ : ∃ dj, p[j]? = some dj := ⟨_, List.getElem?_eq_getElem hjl⟩
      obtain ⟨g1, -, g3, -⟩ := ht j dj sgj hdj hj
      obtain ⟨c1, c2⟩ := hc j hji dj hdj
      exact ⟨by omega, by rw [c1, g1], by rw [c2, g3]⟩
    · cases hj
  obtain ⟨o1, o2⟩ := okBody hK h4 (by rw [hp, h1]) (by rw [hn, ← h1]; omega) (by rw [hq, h3])
  exact ⟨o1, by rw [o2, h3], h2⟩

/-- the last def of a parsed program is main: no parameters, one result word -/
theorem parsed_main {ts : List UInt64} {p : List DefA} (h : ParsesProgram ts p) :
    ∃ d, p.getLast? = some d ∧ d.npw = 0 ∧ d.nres = 1 := by
  obtain ⟨sigs, hl, ht, hm⟩ := refParse_ty h
  have hne : sigs ≠ [] := by intro e; simp [e] at hm
  have hpl : 0 < p.length := by rw [← hl]; exact List.length_pos_iff.2 hne
  rw [List.getLast?_eq_getElem?] at hm ⊢
  have hi : p.length - 1 < p.length := by omega
  refine ⟨_, List.getElem?_eq_getElem hi, ?_⟩
  obtain ⟨h1, -, h3, -⟩ := ht _ _ _ (List.getElem?_eq_getElem hi) (by rw [hl] at hm; exact hm)
  simp at h1 h3; exact ⟨h1, h3.symm⟩

/-! ## E's scoping form `ScV` (NdWidth) and reads ⊆ parameters -/

mutual
theorem sc_of_okV (K : SC) : ∀ e : Nd, OkV K e → ScV K e
  | .const _, _ => by simp [ScV]
  | .loc _ _, h => by simpa [OkV, ScV] using h
  | .bin _ a b, h => by
    simp only [OkV, ScV] at h ⊢; exact ⟨sc_of_okV K a h.1, sc_of_okV K b h.2.1, h.2.2.2.2⟩
  | .ite _ a b t e, h => by
    simp only [OkV, ScV] at h ⊢
    obtain ⟨h1, h2, h3, h4, -, -, -, h8, h9, h10⟩ := h
    exact ⟨sc_of_okV K a h1, sc_of_okV K b h2, sc_of_okV K t h3, sc_of_okV K e h4, h8, h9, h10⟩
  | .letE _ _ v b, h => by
    simp only [OkV, ScV] at h ⊢; exact ⟨sc_of_okV K v h.1, sc_of_okV K b h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  | .pair cs, h => by simp only [OkV, ScV] at h ⊢; exact sc_of_okL K cs h
  | .call _ as, h => by simp only [OkV, ScV] at h ⊢; exact ⟨sc_of_okL K as h.1, h.2.1⟩
  | .prim _ as, h => by simp only [OkV, ScV] at h ⊢; exact sc_of_okL K as h.1
  | .loop z s, h => by
    simp only [OkV, ScV] at h ⊢
    exact ⟨sc_of_okT K z _ h.1, sc_of_okT K s _ h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  | .cont _, h => by simp [OkV] at h
theorem sc_of_okT (K : SC) : ∀ (e : Nd) (w : Nat), OkT K e w → ScT K e
  | .ite _ a b t e, w, h => by
    simp only [OkT, ScT] at h ⊢
    obtain ⟨h1, h2, h3, h4, -, -, h7, h8, h9⟩ := h
    exact ⟨sc_of_okV K a h1, sc_of_okV K b h2, sc_of_okT K t w h3, sc_of_okT K e w h4, h7, h8, h9⟩
  | .letE _ _ v b, w, h => by
    simp only [OkT, ScT] at h ⊢; exact ⟨sc_of_okV K v h.1, sc_of_okT K b w h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  | .cont e, _, h => by simp only [OkT, ScT] at h ⊢; exact ⟨sc_of_okV K e h.1, h.2.2.1, h.2.2.2⟩
  | .const _, w, h | .loc _ _, w, h | .bin _ _ _, w, h | .pair _, w, h | .call _ _, w, h | .prim _ _, w, h
  | .loop _ _, w, h => by simp only [OkT, ScT] at h ⊢; exact sc_of_okV K _ h.1
theorem sc_of_okL (K : SC) : ∀ cs : List Nd, OkL K cs → ScL K cs
  | [], _ => by simp [ScL]
  | c :: cs, h => by simp only [OkL, ScL] at h ⊢; exact ⟨sc_of_okV K c h.1, sc_of_okL K cs h.2.1, h.2.2⟩
end

/-- reads of a def body are parameters -/
theorem rd_body {D : List Sig} {ps : List Kd} {m : Nat} {e : Nd} {ks : List Kd}
    (h : TyB D (ps.map some ++ List.replicate m none) e ks) : ∀ j, Templates.rd e j → j < ps.length := by
  have known : ∀ j kd, (ps.map some ++ List.replicate m none)[j]? = some (some kd) → j < ps.length := by
    intro j kd e
    refine Nat.lt_of_not_le (fun hj => ?_)
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_replicate] at e
    split at e <;> simp at e
  intro j hr
  cases h with
  | plain h => obtain ⟨kd, e⟩ := rd_known h j hr; exact known j kd e
  | loop hΓ hz hs =>
    rename_i z s sk n
    have hps : ps = Kd.w :: sk := somes_eq _ (Kd.w :: sk) m n (by rw [hΓ]; rfl)
    simp only [Templates.rd] at hr
    rcases hr with hr | hr | hr
    · obtain ⟨kd, e⟩ := rd_known hz j hr; exact known j kd e
    · obtain ⟨kd, e⟩ := rd_known hs j hr; exact known j kd e
    · subst hr; rw [hps]; simp

/-- **the parser's per-def facts for E's `gen_top`**: scoping `ScV`, reads ⊆ parameters, npw ≤ nslots (plus `OkV`) -/
theorem parsed_sc {ts : List UInt64} {p : List DefA} (h : ParsesProgram ts p) (i : Nat) (d : DefA) (hd : p[i]? = some d)
    (K : SC) (hp : K.p = d.npw) (hn : K.nl = d.nslots) (hi : K.nd = i) (hq : K.q = d.nres)
    (hc : ∀ j < i, ∀ dj, p[j]? = some dj → K.npwOf j = dj.npw ∧ K.nresOf j = dj.nres) :
    ScV K d.body ∧ (∀ j, Templates.rd d.body j → j < d.npw) ∧ d.npw ≤ d.nslots := by
  obtain ⟨o1, -, o3⟩ := parsed_ok h i d hd K hp hn hi hq hc
  refine ⟨sc_of_okV K _ o1, ?_, o3⟩
  obtain ⟨sigs, hl, ht, -⟩ := refParse_ty h
  have hil : i < sigs.length := by rw [hl]; exact (List.getElem?_eq_some_iff.1 hd).1
  obtain ⟨sg, hsg⟩ : ∃ sg, sigs[i]? = some sg := ⟨_, List.getElem?_eq_getElem hil⟩
  obtain ⟨h1, -, -, h4⟩ := ht i d sg hd hsg
  intro j hr; rw [h1]; exact rd_body h4 j hr

end NanoMain
