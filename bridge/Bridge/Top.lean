/- Bridge.Top: the end-to-end statement in the trimmed model.  For a program `p` whose emitted Exprs `o` nano
produces (`emitAll`), every result `out` that nano's meaning `Sem` computes on input `inp` is what the term
`m inp` DENOTES, in every model of an env holding the bridge prelude and the program's defs (`Env`):
`⟦m⟧ (enc inp) = enc out`.  Composes `eval_emit` (Nano/Expr/Correct.lean) with `Asm.ev_denotes_assembled`.
Hypotheses still open: `Open` (bin ops other than `+`, `ite` conditions, the 9 prelude ops) and the program's
`PWf` (checked per program by `Check.pwfChk`, see CheckExamples).

STATUS: proved, no sorry. -/
import Bridge.Assembly

namespace Bridge.Top
open ExprSpec ParSpec NanoMain Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.Asm

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

/-- **Sem ⇒ Denotes** for whole programs -/
theorem sem_denotes (L : SetLaws O) {sig : Sig} {junk : S}
    {ds : List DefI} {ks ws : List Nat} {p : List DefA} {st : Sd} {o : List (String × X × X)}
    {inp : List UInt8} {κ : Nat} {out : List UInt8} {dm : DefI}
    (E : Env env sig (progOf o)) (Op : Open M sig (progOf o) junk) (hP : PWf sig (progOf o))
    (hsig : sig "m" = some ([.ls], .ls))
    (he : emitAll ds ks ws 0 p st = some o) (hnd : (o.map (·.1)).Nodup) (hin : inp.length < 2 ^ 64)
    (hm : ds[p.length - 1]? = some dm) (hmn : dm.name = [109]) (hmp : dm.params = [.inp]) (hmr : dm.res = .ls)
    (hs : Sem κ p inp = .ok out) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l out) := by
  have hev := eval_emit he hnd hin hm hmn hmp hmr hs
  have hw : Wf sig [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) hsig (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact ev_denotes_assembled L E Op hP hev hw (.cons (.ls _) .nil) _ hD

end Bridge.Top
