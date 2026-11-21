import Lean
namespace Round14
inductive Frame where
  | expr (minp : Nat) (tail : Bool)
  | bin (minp : Nat)
  | reduce (op : Nat)
  | defs
  deriving DecidableEq
structure State (T V D : Type) where
  rest : List T
  vals : List V
  out : List D
  nx : Nat
structure Cfg (S : Type) where
  fs : List Frame
  st : S
inductive Path {A : Type} (r : A → A → Prop) : A → A → Prop where
  | refl (a) : Path r a a
  | cons {a b c} : r a b → Path r b c → Path r a c
variable {S H P O T V : Type}
abbrev Handler (S : Type) := Frame → S → Option (List Frame × S)
def stepF (dispatch : Handler S) (c : Cfg S) : Option (Cfg S) := do
  let f :: ks := c.fs | none
  let (todo, s) ← dispatch f c.st
  return ⟨todo ++ ks, s⟩
def Edge (d : Handler S) (a b : Cfg S) := stepF d a = some b
abbrev Run (d : Handler S) := Path (Edge d)
def BinBranchSpec (d : Handler S) (take : S → Option (Nat × Nat × S))
    (rhs : Nat → Nat → S → Option S) (join : Nat → S → Option S) : Prop :=
  ∀ (ks : List Frame) (s u v w : S) (p op q budget : Nat),
    take s = some (op,q,u) → p ≤ q →
    rhs budget (q+1) u = some v → join op v = some w →
    Run d ⟨.bin p :: ks,s⟩ ⟨.bin p :: ks,w⟩
def ExprReflection (d : Handler S) (segment : List Frame → Cfg S → Cfg S → Prop)
    (expr : Nat → Nat → Bool → S → Option S)
    (adequate : Nat → Cfg S → Cfg S → Prop) : Prop :=
  ∀ ks s u p t b, segment ks ⟨.expr p t :: ks,s⟩ ⟨ks,u⟩ →
    adequate b ⟨.expr p t :: ks,s⟩ ⟨ks,u⟩ → expr b p t s = some u
structure Bridge (d : Handler S) (mh : H → H → Prop) (finish : H → O → Prop)
    (rep : H → Cfg S → Prop) (accept : Cfg S → P → Prop)
    (ser : P → O) where
  handler : ∀ h h' f ks s, mh h h' → rep h ⟨f::ks,s⟩ →
    ∃ c, Run d ⟨f::ks,s⟩ c ∧ rep h' c
  nonempty : ∀ h h' c, mh h h' → rep h c → c.fs ≠ []
  final : ∀ h o c, rep h c → finish h o →
    ∃ p e, Run d c e ∧ accept e p ∧ o = ser p
theorem Path.trans {A} {r : A → A → Prop} {a b c : A}
    (h : Path r a b) (k : Path r b c) : Path r a c := by
  induction h with
  | refl => exact k
  | cons s _ ih => exact .cons s (ih k)
theorem parserSound
    {d : Handler S} {mh : H → H → Prop} {fin : H → O → Prop}
    {rep : H → Cfg S → Prop} {acc : Cfg S → P → Prop} {ser : P → O}
    (B : Bridge d mh fin rep acc ser) (parse : T → O) (empty : O)
    (init : T → Cfg S) (parses : T → P → Prop)
    (load : ∀ ts, parse ts ≠ empty → ∃ h z, rep h (init ts) ∧
      Path mh h z ∧ fin z (parse ts))
    (reflects : ∀ ts e p, Run d (init ts) e → acc e p → parses ts p)
    (ts : T) (ok : parse ts ≠ empty) :
    ∃ p, parses ts p ∧ parse ts = ser p := by
  obtain ⟨h,z,start,path,last⟩ := load ts ok
  have lift : ∀ {a b}, Path mh a b → ∀ c, rep a c →
      ∃ e, Run d c e ∧ rep b e := by
    intro a b hp
    induction hp with
    | refl => intro c hc; exact ⟨c,.refl _,hc⟩
    | cons step _ ih =>
      intro c hc
      obtain ⟨fs,s⟩ := c
      cases fs with
      | nil => exact False.elim (B.nonempty _ _ _ step hc rfl)
      | cons f ks =>
        obtain ⟨u,pre,hu⟩ := B.handler _ _ _ _ _ step hc
        obtain ⟨e,post,he⟩ := ih u hu
        exact ⟨e,pre.trans post,he⟩
  obtain ⟨c,pre,hc⟩ := lift path _ start
  obtain ⟨p,e,post,ha,bytes⟩ := B.final _ _ _ hc last
  exact ⟨p,reflects ts e p (pre.trans post) ha,bytes⟩
end Round14
