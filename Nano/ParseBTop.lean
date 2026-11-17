/- nano stage 2, layer A: defs and parameters, and the top theorem `parseA_eq`: the machine computes
`(pDefsU (ts.length + 1) [] [] ts).map serU` for every token list. -/
import Nano.ParseBSim
import Nano.ElabBProof

namespace Nano.PB
open Nano Nano.U

inductive NV where
  | name (x : List UInt8) (ts : List Tok)
  | close (ts : List Tok)
  | other

def namesV : List Tok → NV
  | Tok.id x :: ts => .name x ts
  | Tok.colon :: Tok.kty _ :: Tok.rp :: ts => .close ts
  | _ => .other

theorem pNames_succ (f : Nat) (sc : List (List UInt8)) (n : Nat) (ts : List Tok) :
    pNames (f + 1) sc n ts = match namesV ts with
    | .name x ts' => pNames f (x :: sc) (n + 1) ts'
    | .close ts' => some (sc, n, ts')
    | .other => none := by
  tcases ts <;> simp only [pNames, namesV] <;> rfl

theorem step_names (f fp n : Nat) (s : St) : step (.names (f + 1) fp n) s = match namesV s.ts with
    | .name x ts => .go (.names f fp (n + 1)) { s with ts := ts, sc := (x, n) :: s.sc }
    | .close ts => .go (.params fp n) { s with ts := ts }
    | .other => .fail := by
  rcases s with ⟨ts⟩; tcases ts <;> simp only [step, namesV] <;> rfl

def lpV : List Tok → Option (List Tok)
  | Tok.lp :: ts => some ts
  | _ => none

theorem pParams_succ (f : Nat) (sc : List (List UInt8)) (n : Nat) (ts : List Tok) :
    pParams (f + 1) sc n ts = match lpV ts with
    | some ts' =>
      match pNames f sc n ts' with
      | some (sc2, n2, r) => pParams f sc2 n2 r
      | none => none
    | none => some (sc, n, ts) := by
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _⟩ <;> simp only [pParams, lpV] <;> rfl

theorem step_params (f n : Nat) (s : St) : step (.params (f + 1) n) s = match lpV s.ts with
    | some ts => .go (.names f f n) { s with ts := ts }
    | none => .go .dbody { s with na := n } := by
  rcases s with ⟨ts⟩
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _⟩ <;> simp only [step, lpV] <;> rfl

def Out3 (o : Option (List (List UInt8) × Nat × List Tok)) (ok : List (List UInt8) → Nat → List Tok → Prop)
    (bad : Prop) : Prop :=
  match o with
  | some (a, b, c) => ok a b c
  | none => bad

theorem Out3.imp {o : Option (List (List UInt8) × Nat × List Tok)} {ok1 ok2 : List (List UInt8) → Nat → List Tok → Prop}
    {bad1 bad2 : Prop} (hok : ∀ a b c, ok1 a b c → ok2 a b c) (hbad : bad1 → bad2) (h : Out3 o ok1 bad1) :
    Out3 o ok2 bad2 := by
  rcases o with _ | ⟨a, b, c⟩
  · exact hbad h
  · exact hok a b c h

theorem zip_mkSc (x : List UInt8) (scN : List (List UInt8)) (n : Nat) :
    (x :: scN).zip (mkSc (n + 1) 0) = (x, n) :: scN.zip (mkSc n 0) := by simp [mkSc]

theorem names_sim : ∀ (f fp : Nat) (ts : List Tok) (n : Nat) (scN : List (List UInt8)) out d mds K cg cf na,
    scN.length = n →
    Out3 (pNames f scN n ts)
      (fun scN' n' r => scN'.length = n' ∧ Reach (.names f fp n) ⟨ts, out, d, scN.zip (mkSc n 0), mds, K, cg, cf, na⟩
        (.params fp n') ⟨r, out, d, scN'.zip (mkSc n' 0), mds, K, cg, cf, na⟩)
      (Fails (.names f fp n) ⟨ts, out, d, scN.zip (mkSc n 0), mds, K, cg, cf, na⟩)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => Fails.one rfl
  | f + 1, fp, ts, n, scN, out, d, mds, K, cg, cf, na, hl => by
    have hst := step_names f fp n ⟨ts, out, d, scN.zip (mkSc n 0), mds, K, cg, cf, na⟩
    rw [pNames_succ]
    cases hv : namesV ts with
    | name x ts' =>
      simp only [hv] at hst ⊢
      rw [← zip_mkSc] at hst
      exact Out3.imp (fun _ _ _ h => ⟨h.1, Reach.stepT hst h.2⟩) (Fails.stepT hst)
        (names_sim f fp ts' (n + 1) (x :: scN) out d mds K cg cf na (by simp [hl]))
    | close ts' => simp only [hv] at hst ⊢; exact ⟨hl, Reach.one hst⟩
    | other => simp only [hv] at hst ⊢; exact Fails.one hst

theorem params_sim : ∀ (f : Nat) (ts : List Tok) (n : Nat) (scN : List (List UInt8)) out d mds K cg cf na,
    scN.length = n →
    Out3 (pParams f scN n ts)
      (fun scN' n' r => scN'.length = n' ∧ Reach (.params f n) ⟨ts, out, d, scN.zip (mkSc n 0), mds, K, cg, cf, na⟩
        .dbody ⟨r, out, d, scN'.zip (mkSc n' 0), mds, K, cg, cf, n'⟩)
      (Fails (.params f n) ⟨ts, out, d, scN.zip (mkSc n 0), mds, K, cg, cf, na⟩)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => Fails.one rfl
  | f + 1, ts, n, scN, out, d, mds, K, cg, cf, na, hl => by
    have hst := step_params f n ⟨ts, out, d, scN.zip (mkSc n 0), mds, K, cg, cf, na⟩
    rw [pParams_succ]
    cases hv : lpV ts with
    | none => simp only [hv] at hst ⊢; exact ⟨hl, Reach.one hst⟩
    | some ts' =>
      simp only [hv] at hst ⊢
      have h1 := names_sim f f ts' n scN out d mds K cg cf na hl
      cases hn : pNames f scN n ts' with
      | none => rw [hn] at h1; exact Fails.stepT hst h1
      | some r =>
        obtain ⟨scN2, n2, r⟩ := r
        rw [hn] at h1
        obtain ⟨hl2, h1⟩ := h1
        exact Out3.imp (fun _ _ _ h => ⟨h.1, Reach.stepT hst (h1.trans h.2)⟩)
          (fun h => Fails.stepT hst (h1.fails h)) (params_sim f r n2 scN2 out d mds K cg cf na hl2)

def defsV : List Tok → Option (List UInt8 × List Tok)
  | Tok.kdef :: Tok.id g :: ts => some (g, ts)
  | _ => none

def hdV : List Tok → Option (List Tok)
  | Tok.colon :: Tok.kty _ :: Tok.assign :: r => some r
  | _ => none

theorem pDefsU_succ (f : Nat) (ds : Defs) (acc : List (Nat × Ex)) (ts : List Tok) :
    pDefsU (f + 1) ds acc ts = match defsV ts with
    | some (g, ts') =>
      match pParams f [] 0 ts' with
      | some (sc, n, r) =>
        match hdV r with
        | some r' =>
          match findDef g ds with
          | some _ => none
          | none =>
            match pExpr f sc ds r' with
            | some (e, r2) => if r2 = [] then some ((n, e) :: acc)
                else pDefsU f ((g, n, Ex.var acc.length) :: ds) ((n, e) :: acc) r2
            | none => none
        | none => none
      | none => none
    | none => none := by
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _, ts⟩⟩ <;> simp only [pDefsU, defsV] <;> try rfl
  rename_i g
  cases pParams f [] 0 ts with
  | none => rfl
  | some x =>
    obtain ⟨sc, n, r⟩ := x
    tcases r <;> simp only [hdV] <;> try rfl
    all_goals
      cases findDef g ds with
      | some _ => rfl
      | none =>
        simp only
        rcases pExpr f sc ds _ with _ | ⟨e, _ | ⟨t, r2⟩⟩ <;> simp

theorem step_defs (f : Nat) (s : St) : step (.defs (f + 1)) s = match defsV s.ts with
    | some (g, ts) => .go (.params f 0) { s with ts := ts, cg := g, cf := f, sc := [] }
    | none => .fail := by
  rcases s with ⟨ts⟩
  rcases ts with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _, ts⟩⟩ <;> simp only [step, defsV] <;> rfl

theorem step_dbody (s : St) : step .dbody s = match hdV s.ts with
    | some r =>
      match findD s.cg s.ds with
      | some _ => .fail
      | none => .go (.expr s.cf) { s with ts := r, d := s.na, K := [] }
    | none => .fail := by
  rcases s with ⟨ts⟩; tcases ts <;> simp only [step, hdV] <;> rfl

/-- a run that ends with output `o` -/
def Done (c : Ctl) (s : St) (o : List UInt8) : Prop := ∃ n, ∀ g, run (g + n) c s = some o

theorem Reach.done {c c' : Ctl} {s s' : St} {o : List UInt8} (h : Reach c s c' s') (h2 : step c' s' = .done o) :
    Done c s o := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, fun g => by rw [show g + (n + 1) = (g + 1) + n by omega, h]; simp only [run, h2]⟩

theorem Reach.thenDone {c c' : Ctl} {s s' : St} {o : List UInt8} (h : Reach c s c' s') (h2 : Done c' s' o) :
    Done c s o := by
  obtain ⟨n, h⟩ := h; obtain ⟨m, h2⟩ := h2
  exact ⟨m + n, fun g => by rw [← Nat.add_assoc, h, h2]⟩

theorem defs_sim : ∀ (f : Nat) (ts : List Tok) (acc : List (Nat × Ex)) out d sc mds K cg cf na,
    mds.length = acc.length → out = serU acc →
    match pDefsU f (dsOf mds) acc ts with
    | some u => Done (.defs f) ⟨ts, out, d, sc, mds, K, cg, cf, na⟩ (serU u)
    | none => Fails (.defs f) ⟨ts, out, d, sc, mds, K, cg, cf, na⟩
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => Fails.one rfl
  | f + 1, ts, acc, out, d, sc, mds, K, cg, cf, na, hl, ho => by
    have hst := step_defs f ⟨ts, out, d, sc, mds, K, cg, cf, na⟩
    rw [pDefsU_succ]
    cases hv : defsV ts with
    | none => simp only [hv] at hst ⊢; exact Fails.one hst
    | some gt =>
      obtain ⟨g, ts'⟩ := gt
      simp only [hv] at hst ⊢
      have h1 := params_sim f ts' 0 [] out d mds K g f na rfl
      cases hp : pParams f [] 0 ts' with
      | none => rw [hp] at h1; exact Fails.stepT hst h1
      | some x =>
        obtain ⟨scN, n, r⟩ := x
        rw [hp] at h1
        obtain ⟨hln, h1⟩ := h1
        simp only []
        have hsd := step_dbody ⟨r, out, d, scN.zip (mkSc n 0), mds, K, g, f, n⟩
        cases hh : hdV r with
        | none =>
          simp only [hh] at hsd ⊢
          exact Fails.stepT hst (h1.fails (Fails.one hsd))
        | some r' =>
          simp only [hh] at hsd ⊢
          rw [findDef_dsOf]
          cases hf : findD g mds with
          | some _ =>
            simp only [hf, Option.map] at hsd ⊢
            exact Fails.stepT hst (h1.fails (Fails.one hsd))
          | none =>
            simp only [hf, Option.map] at hsd ⊢
            have h2 := (sim f).1 r' out n scN (mkSc n 0) mds [] g f n (by rw [mkSc_length]; exact hln)
            cases he : pExpr f scN (dsOf mds) r' with
            | none =>
              rw [he] at h2
              exact Fails.stepT hst (h1.fails (Fails.stepT hsd h2))
            | some er =>
              obtain ⟨e, r2⟩ := er
              rw [he] at h2
              simp only []
              have hR := Reach.stepT hst (h1.trans (Reach.stepT hsd h2))
              have hser : serU ((n, e) :: acc) = out ++ serUE (mkSc n 0) n e ++ mo 13 n.toUInt8 := by
                simp [serU, serUD, ho, List.append_assoc]
              by_cases hr : r2 = []
              · subst hr
                simp only [if_true]
                rw [hser]
                exact hR.done rfl
              · simp only [hr, if_false]
                have hst2 : step .ret ⟨r2, out ++ serUE (mkSc n 0) n e, n + 1, scN.zip (mkSc n 0), mds, [], g, f, n⟩ =
                    .go (.defs f) ⟨r2, out ++ serUE (mkSc n 0) n e ++ mo 13 n.toUInt8, n + 1, scN.zip (mkSc n 0),
                      (g, n, mds.length) :: mds, [], g, f, n⟩ := by
                  rcases r2 with _ | ⟨t, r2⟩
                  · exact absurd rfl hr
                  · rfl
                have h3 := defs_sim f r2 ((n, e) :: acc) (out ++ serUE (mkSc n 0) n e ++ mo 13 n.toUInt8) (n + 1)
                  (scN.zip (mkSc n 0)) ((g, n, mds.length) :: mds) [] g f n (by simp [hl]) hser.symm
                have hds : dsOf ((g, n, mds.length) :: mds) = (g, n, Ex.var acc.length) :: dsOf mds := by
                  simp [dsOf, hl]
                rw [hds] at h3
                cases hu : pDefsU f ((g, n, Ex.var acc.length) :: dsOf mds) ((n, e) :: acc) r2 with
                | none => rw [hu] at h3; exact hR.fails (Fails.stepT hst2 h3)
                | some u => rw [hu] at h3; exact (hR.trans (Reach.one hst2)).thenDone h3

/-- **layer A is the non-inlining parser**: for every token list, with enough gas the machine returns `serU u`
when `pDefsU` returns `u`, and with any gas it returns `none` when `pDefsU` does -/
theorem parseA_eq (ts : List Tok) :
    match pDefsU (ts.length + 1) [] [] ts with
    | some u => ∃ n, ∀ g, parseA (g + n) ts = some (serU u)
    | none => ∀ g, parseA g ts = none :=
  defs_sim (ts.length + 1) ts [] [] 0 [] [] [] [] 0 0 rfl rfl

end Nano.PB

namespace Nano.PB
open Nano Nano.U Nano.B

/-- stage 2 on stage 1's bytes (layer A, gas `g`): `serU u`, or `[]` for a rejected input -/
def stage2A (g : Nat) (bs : List UInt8) : List UInt8 :=
  match decL bs with
  | some (_, ts) => (parseA g ts).getD []
  | none => []

theorem nanoElabU_lexT (xs : List UInt8) :
    nanoElabU xs = (lexT xs).bind fun st => pDefsU (st.2.length + 1) [] [] st.2 := by
  unfold nanoElabU lexT
  cases (if adjOk xs then lex xs.length xs else none) with
  | none => rfl
  | some ts => cases h : uniTy none ts <;> simp [h]

/-- **stage 1 then stage 2 (layer A) = the non-inlined elaboration, for every source**: on an accepted source the
two stages emit `serU u` (with enough gas), on a rejected one `[]` (with any gas) -/
theorem stage2A_lexB (xs : List UInt8) :
    match nanoElabU xs with
    | some u => ∃ n, ∀ g, stage2A (g + n) (lexB xs) = serU u
    | none => ∀ g, stage2A g (lexB xs) = [] := by
  rw [nanoElabU_lexT]
  unfold stage2A
  rw [lexB_eq]
  cases lexT xs with
  | none => intro g; rfl
  | some st =>
    obtain ⟨s, ts⟩ := st
    have h := parseA_eq ts
    simp only [Option.bind]
    cases hp : pDefsU (ts.length + 1) [] [] ts with
    | none => rw [hp] at h; intro g; simp [h g]
    | some u => rw [hp] at h; obtain ⟨n, h⟩ := h; exact ⟨n, fun g => by simp [h g]⟩

end Nano.PB
