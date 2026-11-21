/- Harvest/H8/DoDesugar: nano-style desugaring rules for do-notation, proved equal to what Lean 4.34.1's own do-elaborator
produces. The right-hand `Id.run do ...` blocks are elaborated by Lean (Lean/Elab/Do), so each theorem is a statement about
Lean's actual output, checked by the kernel. Candidate rules are total, first-order functions over a small `Stmt` list. -/
namespace H8

/-- a statement list over one mutable `Nat`-like state `σ`; the nano candidate semantic of a straight-line do block -/
inductive St (σ : Type) | set (f : σ → σ) | unless_ (c : σ → Bool) (f : σ → σ) | ifSet (c : σ → Bool) (f g : σ → σ)

def St.run {σ} : St σ → σ → σ
  | .set f, s => f s
  | .unless_ c f, s => if c s then s else f s
  | .ifSet c f g, s => if c s then f s else g s

def runAll {σ} (l : List (St σ)) (s : σ) : σ := l.foldl (fun s i => i.run s) s

/-- `let mut x := a; x := f x; x := g x; x` -/
theorem reassign_lean {σ} (a : σ) (f g : σ → σ) :
    (Id.run do let mut x := a; x := f x; x := g x; return x) = runAll [.set f, .set g] a := rfl

/-- `unless c x do x := f x` is `if c x then x else f x` -/
theorem unless_lean {σ} (a : σ) (c : σ → Bool) (f : σ → σ) :
    (Id.run do
      let mut x := a
      unless c x do x := f x
      return x) = runAll [.unless_ c f] a := by
  simp only [runAll, St.run, List.foldl]; split <;> rfl

/-- `if c x then x := f x else x := g x` (statement form, Id) -/
theorem if_stmt_lean {σ} (a : σ) (c : σ → Bool) (f g : σ → σ) :
    (Id.run do
      let mut x := a
      if c x then x := f x else x := g x
      return x) = runAll [.ifSet c f g] a := by
  simp only [runAll, St.run, List.foldl]; split <;> rfl

/-- `if let some y := o then x := f y` : `Option` pattern (the only `if let` shape nano's `match` desugaring needs) -/
def ifLet {σ α} (o : Option α) (f : α → σ → σ) (s : σ) : σ := match o with | some y => f y s | none => s
theorem ifLet_lean {σ α} (a : σ) (o : Option α) (f : α → σ → σ) :
    (Id.run do
      let mut x := a
      if let some y := o then x := f y x
      return x) = ifLet o f a := by
  cases o <;> rfl

/-- `let y ← e` in `Id` is `let y := e` (so a nano `let` is a valid reading of an `Id` bind) -/
theorem bind_id_lean {α β} (e : α) (k : α → β) : (Id.run do let y ← (pure e : Id α); return k y) = k e := rfl

end H8
