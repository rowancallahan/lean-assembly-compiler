/- Harvest/H6/Desugar: value equations behind the term forms (fun, application, parentheses, tuple, anonymous constructor,
ascription, show, have). A nano desugaring rule that rewrites the form to the right-hand side keeps Lean's value because the two
sides are DEFINITIONALLY equal (checked by the kernel with `rfl`), so no elaborator argument is needed once Lean accepts the form.
Not covered: that Lean's elaborator *accepts* the form (type inference, expected types: elaborator-only). -/
namespace H6
variable {α β γ : Type} (a : α) (b : β) (c : γ) (v : α) (body : α → β) (e : α)

/-- `fun x => b` applied: beta -/
theorem fun_app : (fun x => body x) v = body v := rfl
/-- parentheses and type ascription are transparent -/
theorem paren_ascr : (e : α) = e := rfl
/-- `show T from e` -/
theorem show_from : (show α from e) = e := rfl
/-- `have x := v; b` (non-dependent let) and `let` agree with beta -/
theorem have_beta : (have x := v; body x) = body v := rfl
theorem let_beta : (let x := v; body x) = body v := rfl
/-- tuples nest to the right; `⟨a, b⟩` at a product type is the pair -/
theorem tuple_nest : (a, b, c) = (a, (b, c)) := rfl
theorem anon_pair : (⟨a, b⟩ : α × β) = (a, b) := rfl
theorem anon_triple : (⟨a, b, c⟩ : α × β × γ) = (a, b, c) := rfl
/-- unit: `()` -/
theorem unit_tuple : (() : Unit) = Unit.unit := rfl
/-- pattern let on a tuple = projections (nano's pair `let (x, y) := p`) -/
theorem let_pair (p : α × β) (f : α → β → γ) : (let (x, y) := p; f x y) = f p.1 p.2 := rfl
/-- `f <| x`, `x |> f`, `f $ x`, `(f ∘ g) x` are plain application -/
theorem pipe_app (f : α → β) (g : β → γ) : (f <| a) = f a ∧ (a |> f) = f a ∧ (g ∘ f) a = g (f a) := ⟨rfl, rfl, rfl⟩
/-- `(· + 1)`-style sections: the cdot function is the lambda -/
theorem cdot_fun (n : UInt64) : (· + 1 : UInt64 → UInt64) n = n + 1 := rfl
/-- application is left-nested: `f a b = (f a) b` -/
theorem app_curry (f : α → β → γ) : f a b = (f a) b := rfl
end H6
