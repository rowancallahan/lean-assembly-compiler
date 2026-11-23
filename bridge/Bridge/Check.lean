/- Bridge.Check: a decidable checker for `Typed.Wf` (and `PWf`), with soundness.  `emit ⇒ Wf` does NOT hold in
general: `emit` accepts a CONTINUE inside a `let` value (as an `ite` branch), which Sem rejects at run time
(`ev_let` needs `.inl`) and which is ill-typed in Lean.  So `Wf` is established PER PROGRAM by running `chk` on the
emitted Expr (for the compiler itself, on its own Expr, as `C_lean_all` does for the Expr identity).

STATUS: proved, no sorry. -/
import Bridge.Typed

namespace Bridge.Check
open ExprSpec ParSpec Bridge.Typed

theorem spine_eq : ∀ {e h : X} {as : List X}, spine e = (h, as) → e = apps h as
  | .app f a, h, as, hs => by
    simp only [spine] at hs
    rcases hf : spine f with ⟨h', as'⟩
    rw [hf] at hs; simp at hs; obtain ⟨rfl, rfl⟩ := hs
    rw [spine_eq hf]; simp [apps, List.foldl_append]
  | .bv _, _, _, hs => by simp [spine] at hs; obtain ⟨rfl, rfl⟩ := hs; rfl
  | .c _ _, _, _, hs => by simp [spine] at hs; obtain ⟨rfl, rfl⟩ := hs; rfl
  | .lam _ _, _, _, hs => by simp [spine] at hs; obtain ⟨rfl, rfl⟩ := hs; rfl
  | .pi _ _, _, _, hs => by simp [spine] at hs; obtain ⟨rfl, rfl⟩ := hs; rfl
  | .lt _ _ _ _, _, _, hs => by simp [spine] at hs; obtain ⟨rfl, rfl⟩ := hs; rfl
  | .nat _, _, _, hs => by simp [spine] at hs; obtain ⟨rfl, rfl⟩ := hs; rfl

/-- inverse of `shTy` (the checker re-checks `T = shTy s`, so this needs no proof) -/
def shInv : X → Option Sh
  | .c "UInt64" [] => some .uw
  | .c "Nat" [] => some .nt
  | .c "Buf" [] => some .bf
  | .app (.c "List" [0]) (.c "UInt8" []) => some .ls
  | .app (.app (.c "Prod" [0, 0]) A) B => do some (.p (← shInv A) (← shInv B))
  | _ => none

/-- recover `(n, cmp, a, b)` of an `ite` condition (re-checked through `condX`) -/
def condInv (c : X) : Option (Bool × Nat × X × X) :=
  match spine c with
  | (.c "Eq" _, [_, q, _]) =>
    match spine q with
    | (.c "BEq.beq" _, [T, _, a, b]) => some (T == .c "Nat" [], 1, a, b)
    | _ => none
  | (.c "LT.lt" _, [T, _, a, b]) => some (T == .c "Nat" [], 2, a, b)
  | _ => none

def opOf : String → Nat
  | "HAdd.hAdd" => 1 | "HSub.hSub" => 2 | "HMul.hMul" => 3 | "HAnd.hAnd" => 4 | "HOr.hOr" => 5
  | "HShiftLeft.hShiftLeft" => 6 | _ => 7

def primOf : String → Nat
  | "len'" => 1 | "rd" => 2 | "len" => 3 | "put" => 4 | "bsize" => 6 | "bget" => 7 | "bset" => 8 | _ => 9

def chkL (g : X → Option Sh) : List X → List Sh → Bool
  | [], [] => true
  | a :: as, s :: ss => g a == some s && chkL g as ss
  | _, _ => false

/-- one constant application `n.{ls} as` -/
def node (sig : Sig) (g : List Sh → X → Option Sh) (Γ : List Sh) (n : String) (ls : List Nat) (as : List X) :
    Option Sh :=
  if n = "OfNat.ofNat" then
    match as with
    | [T, .nat k, i] =>
      if ls = [0] ∧ T = U ∧ i = .app (.c "UInt64.instOfNat" []) (.nat k) ∧ k < UInt64.size then some .uw
      else if ls = [0] ∧ T = .c "Nat" [] ∧ i = .app (.c "instOfNatNat" []) (.nat k) then some .nt else none
    | _ => none
  else if n ∈ binList then
    match as with
    | [T1, T2, T3, i, a, b] =>
      if ls = [0, 0, 0] ∧ T1 = U ∧ T2 = U ∧ T3 = U ∧ binHead (opOf n) = (n, i) ∧ 1 ≤ opOf n ∧ opOf n ≤ 7 ∧
        g Γ a = some .uw ∧ g Γ b = some .uw then some .uw else none
    | _ => none
  else if n = "ite" then
    match as with
    | [T, c, d, t, el] => do
      let r ← shInv T
      let (nb, cmp, a, b) ← condInv c
      if ls = [1] ∧ T = shTy r ∧ condX nb cmp a b = (c, d) ∧ (cmp = 1 ∨ cmp = 2) ∧
        g Γ a = some (if nb then .nt else .uw) ∧ g Γ b = some (if nb then .nt else .uw) ∧ g Γ t = some r ∧
        g Γ el = some r then some r else none
    | _ => none
  else if n = "Prod.mk" then
    match as with
    | [A, B, a, b] => do
      let sa ← g Γ a
      let sb ← g Γ b
      if ls = [0, 0] ∧ A = shTy sa ∧ B = shTy sb then some (.p sa sb) else none
    | _ => none
  else if n = "Prod.casesOn" then
    match as with
    | [A, B, .lam _ RT, v, .lam _ (.lam _ body)] => do
      let l ← shInv A
      let r ← shInv B
      let R ← shInv RT
      if ls = [1, 0, 0] ∧ as = [shTy l, shTy r, .lam (shTy (.p l r)) (shTy R), v, .lam (shTy l) (.lam (shTy r) body)] ∧
        g Γ v = some (.p l r) ∧ g (r :: l :: Γ) body = some R then some R else none
    | _ => none
  else if n = "Nat.casesOn" then
    match as with
    | [.lam _ RT, d, z, .lam _ s] => do
      let R ← shInv RT
      if ls = [1] ∧ as = [.lam (.c "Nat" []) (shTy R), d, z, .lam (.c "Nat" []) s] ∧ g Γ d = some .nt ∧
        g Γ z = some R ∧ g (.nt :: Γ) s = some R then some R else none
    | _ => none
  else if n = "List.nil" then
    if ls = [0] ∧ as = [.c "UInt8" []] then some .ls else none
  else if n = "bnew" then
    if ls = [] ∧ as = [] then some .bf else none
  else if n ∈ primList then
    match primInfo (primOf n) with
    | (n', ps, r) =>
      if n' = n ∧ ls = [] ∧ primOf n ≠ 5 ∧ primOf n ≠ 0 ∧ primOf n ≤ 9 ∧ chkL (g Γ) as (ps.map psSh) then some r
      else none
  else if n ∉ Typed.reserved ∧ ls = [] then
    match sig n with
    | some (ps, r) => if chkL (g Γ) as ps then some r else none
    | none => none
  else none

/-- the checker (fuel bounds the recursion) -/
def chk (sig : Sig) : Nat → List Sh → X → Option Sh
  | 0, _, _ => none
  | f + 1, Γ, e =>
    match e with
    | .bv i => Γ[i]?
    | .lt nd t v b =>
      if nd then (chk sig f Γ v).bind fun s => if t = shTy s then chk sig f (s :: Γ) b else none else none
    | e =>
      match spine e with
      | (.c n ls, as) => node sig (chk sig f) Γ n ls as
      | _ => none

/-! ## soundness -/

theorem chkL_sound {sig : Sig} {Γ : List Sh} {g : X → Option Sh} (hg : ∀ e s, g e = some s → Wf sig Γ e s) :
    ∀ {as ss}, chkL g as ss = true → WfL sig Γ as ss
  | [], [], _ => .nil
  | a :: as, s :: ss, h => by
    simp only [chkL, Bool.and_eq_true, beq_iff_eq] at h
    exact .cons (hg a s h.1) (chkL_sound hg h.2)
  | [], _ :: _, h => by simp [chkL] at h
  | _ :: _, [], h => by simp [chkL] at h

theorem node_sound {sig : Sig} {g : List Sh → X → Option Sh}
    (hg : ∀ Γ e s, g Γ e = some s → Wf sig Γ e s) {Γ n ls as s} (h : node sig g Γ n ls as = some s) :
    Wf sig Γ (apps (.c n ls) as) s := by
  unfold node at h
  by_cases h1 : n = "OfNat.ofNat"
  · subst h1; rw [if_pos rfl] at h
    split at h
    · rename_i T k i
      split at h
      · rename_i hc; obtain ⟨rfl, rfl, rfl, hk⟩ := hc; cases h; exact .litU rfl hk
      · split at h
        · rename_i hc; obtain ⟨rfl, rfl, rfl⟩ := hc; cases h; exact .litN rfl
        · cases h
    · cases h
  rw [if_neg h1] at h
  by_cases h2 : n ∈ binList
  · rw [if_pos h2] at h
    split at h
    · split at h
      · rename_i T1 T2 T3 i a b hc
        obtain ⟨rfl, rfl, rfl, rfl, hb, h3, h4, ha', hb'⟩ := hc; cases h
        exact .bin rfl hb h2 h3 h4 (hg _ _ _ ha') (hg _ _ _ hb')
      · cases h
    · cases h
  rw [if_neg h2] at h
  by_cases h3 : n = "ite"
  · subst h3; rw [if_pos rfl] at h
    split at h
    · rename_i T c d t el
      simp only [bind, Option.bind] at h
      rcases hr : shInv T with _ | r
      · rw [hr] at h; simp at h
      rw [hr] at h; simp only at h
      rcases hc : condInv c with _ | ⟨nb, cmp, a, b⟩
      · rw [hc] at h; simp at h
      rw [hc] at h; simp only at h
      by_cases hh : ls = [1] ∧ T = shTy r ∧ condX nb cmp a b = (c, d) ∧ (cmp = 1 ∨ cmp = 2) ∧
          g Γ a = some (if nb then .nt else .uw) ∧ g Γ b = some (if nb then .nt else .uw) ∧ g Γ t = some r ∧
          g Γ el = some r
      · rw [if_pos hh] at h
        obtain ⟨rfl, rfl, hcd, hcmp, ha, hb, ht, he⟩ := hh; cases h
        exact .ite rfl hcd hcmp (hg _ _ _ ha) (hg _ _ _ hb) (hg _ _ _ ht) (hg _ _ _ he)
      · rw [if_neg hh] at h; cases h
    · cases h
  rw [if_neg h3] at h
  by_cases h4 : n = "Prod.mk"
  · subst h4; rw [if_pos rfl] at h
    split at h
    · rename_i A B a b
      simp only [bind, Option.bind] at h
      rcases ha : g Γ a with _ | sa
      · rw [ha] at h; simp at h
      rw [ha] at h; simp only at h
      rcases hb : g Γ b with _ | sb
      · rw [hb] at h; simp at h
      rw [hb] at h; simp only at h
      split at h
      · rename_i hh; obtain ⟨rfl, rfl, rfl⟩ := hh; cases h; exact .mk rfl (hg _ _ _ ha) (hg _ _ _ hb)
      · cases h
    · cases h
  rw [if_neg h4] at h
  by_cases h5 : n = "Prod.casesOn"
  · subst h5; rw [if_pos rfl] at h
    split at h
    · rename_i A B T0 RT v T1 T2 body
      simp only [bind, Option.bind] at h
      rcases hl : shInv A with _ | l
      · rw [hl] at h; simp at h
      rw [hl] at h; simp only at h
      rcases hr : shInv B with _ | r
      · rw [hr] at h; simp at h
      rw [hr] at h; simp only at h
      rcases hR : shInv RT with _ | R
      · rw [hR] at h; simp at h
      rw [hR] at h; simp only at h
      split at h
      · rename_i hh; obtain ⟨rfl, has, hv, hb⟩ := hh; cases h; rw [has]
        exact .cases rfl (hg _ _ _ hv) (hg _ _ _ hb)
      · cases h
    · cases h
  rw [if_neg h5] at h
  by_cases h6 : n = "Nat.casesOn"
  · subst h6; rw [if_pos rfl] at h
    split at h
    · rename_i T0 RT d z T1 sb
      simp only [bind, Option.bind] at h
      rcases hR : shInv RT with _ | R
      · rw [hR] at h; simp at h
      rw [hR] at h; simp only at h
      split at h
      · rename_i hh; obtain ⟨rfl, has, hd, hz, hs⟩ := hh; cases h; rw [has]
        exact .natCases rfl (hg _ _ _ hd) (hg _ _ _ hz) (hg _ _ _ hs)
      · cases h
    · cases h
  rw [if_neg h6] at h
  by_cases h7 : n = "List.nil"
  · subst h7; rw [if_pos rfl] at h
    split at h
    · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; cases h; exact .nil rfl
    · cases h
  rw [if_neg h7] at h
  by_cases h8 : n = "bnew"
  · subst h8; rw [if_pos rfl] at h
    split at h
    · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; cases h; exact .bnew rfl
    · cases h
  rw [if_neg h8] at h
  by_cases h9 : n ∈ primList
  · rw [if_pos h9] at h
    rcases hp : primInfo (primOf n) with ⟨n', ps, r⟩
    rw [hp] at h; simp only at h
    split at h
    · rename_i hh; obtain ⟨rfl, rfl, h0, h1', h2', hl⟩ := hh; cases h
      exact .prim rfl hp h9 h0 h1' h2' (chkL_sound (fun e s he => hg Γ e s he) hl)
    · cases h
  rw [if_neg h9] at h
  split at h
  · rename_i hh; obtain ⟨hres, rfl⟩ := hh
    split at h
    · rename_i ps r hs
      split at h
      · rename_i hl; cases h; exact .call rfl hres hs (chkL_sound (fun e s he => hg Γ e s he) hl)
      · cases h
    · cases h
  · cases h

theorem chk_sound {sig : Sig} : ∀ (f : Nat) {Γ : List Sh} {e : X} {s : Sh}, chk sig f Γ e = some s → Wf sig Γ e s
  | 0, _, _, _, h => by simp [chk] at h
  | f + 1, Γ, e, s, h => by
    unfold chk at h
    split at h
    · exact .bv rfl h
    · rename_i nd t v b
      split at h
      · rename_i hnd; subst hnd
        rcases hv : chk sig f Γ v with _ | sv
        · rw [hv] at h; simp at h
        rw [hv] at h; simp only [Option.bind] at h
        split at h
        · rename_i ht; subst ht; exact .lt rfl (chk_sound f hv) (chk_sound f h)
        · cases h
      · cases h
    · split at h
      · rename_i n ls as hs
        rw [spine_eq hs]
        exact node_sound (fun Γ e s he => chk_sound f he) h
      · cases h

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (k, v) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk; cases h; simp at hk; subst hk; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- the program check: every def has a signature, a non-reserved name, and a well-formed body -/
def pwfChk (sig : Sig) (f : Nat) (P : Prog) : Bool :=
  P.all fun (n, body) => match sig n with
    | some (ps, r) => !decide (n ∈ Typed.reserved) &&
        match strip ps.length body with
        | some b => chk sig f ps.reverse b == some r
        | none => false
    | none => false

/-- signatures with all reserved names mapped to `none` -/
theorem pwfChk_sound {sig : Sig} {f : Nat} {P : Prog} (h : pwfChk sig f P = true)
    (hres : ∀ {n ps r}, sig n = some (ps, r) → n ∉ Typed.reserved) : PWf sig P where
  defs := by
    intro n body hl
    have hm := lookup_mem hl
    have := List.all_eq_true.mp h _ hm
    simp only at this
    split at this
    · rename_i ps r hs
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at this
      obtain ⟨-, hb⟩ := this
      split at hb
      · rename_i b hst
        exact ⟨ps, r, b, hs, hst, chk_sound f (by simpa using hb)⟩
      · cases hb
    · cases this
  sig_res := hres
  sig_fun := by intro n ps r ps' r' h1 h2; rw [h1] at h2; cases h2; exact ⟨rfl, rfl⟩

end Bridge.Check
