/- Nano/V2Self: the driver.  The compiler is `asm ∘ mexp ∘ inl ∘ parse ∘ lex`.  As Lean it is `chainS`; as nano source it
still needs buffer-to-buffer stage interfaces (the front end reads only the program INPUT with `rd`/`len` and extends only
the OUTPUT with `put`; a stage output cannot be re-read) — see Testing/notes/NANO_V2_CHECKPOINT.md. -/
import Legacy.Nano.V2Self.Legacy.Asm
import Legacy.Nano.V2Self.Legacy.Expand
import Legacy.Nano.V2Self.Legacy.Lex
import Legacy.Nano.V2Self.Legacy.Inl
import Legacy.Nano.V2Self.Legacy.Parse
import Legacy.Nano.V2Self.Legacy.Bridge
import Legacy.Nano.V2S.InlT
import Legacy.Nano.V2S.Parse
import Legacy.Nano.V2S.Lex

/-- the five stages, linked (Lean-level driver) -/
def chainS (src : List UInt8) : List UInt8 := a5 (e2 (j8 (r16 (l15 src))))

/-- the same chain on the `Nano.V2S` stages, with the tail-only inliner -/
def chainT (src : List UInt8) : List UInt8 :=
  Nano.V2S.asmV (Nano.V2S.mexpV (Nano.V2S.inlTV (Nano.V2S.p2bV (Nano.V2S.lexV src))))

/-- assembler and expander are proved equal (Bridge.lean); lexer, inliner and parser are tested equal
(Testing/nano/v2self/diff_test.lean), their equalities are the hypotheses -/
theorem chainS_eq (hl : ∀ x, l15 x = Nano.V2S.lexV x) (hp : ∀ x, r16 x = Nano.V2S.p2bV x)
    (hi : ∀ x, j8 x = Nano.V2S.inlTV x) (src : List UInt8) : chainS src = chainT src := by
  unfold chainS chainT; rw [hl, hp, hi, e2_eq, a5_eq]
