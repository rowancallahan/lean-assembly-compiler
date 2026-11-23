/- Bridge.TopC: the end-to-end statement for the COMPILER ITSELF (trimmed model).  Whenever C's meaning on `inp`
has a result `mC inp` (C's Lean function `m`), the term `m inp` of C's own emitted Expr denotes the encoding of
that result: `⟦m⟧ (enc inp) = enc (mC inp)`, in every model of an env holding the bridge prelude and C's defs.
`PWf` and the def form are kernel-checked (CheckC, CheckForm); still open: `Open` (bin ops other than `+`, ite
conditions, prelude ops) and swapping the trimmed model for con-leche's.  With `NanoMain.self_expr_C`
(Nano/Expr/CExprTop.lean, needs the Sail build) this reaches the machine code: the RISC-V code C emits for its own
text writes `mC a`, and `⟦m⟧ (enc a) = enc (mC a)`.

STATUS: proved, no sorry. -/
import Bridge.Final9
import Bridge.CheckForm

namespace Bridge.TopC
open ExprSpec ParSpec NanoMain Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.Asm Bridge.CheckC Bridge.CheckEx

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

theorem C_denotes (L : SetLaws O) {junk : S} (E : Env env (sigOf oC) (ExprSpec.progOf oC))
    (Op : Open M (sigOf oC) (ExprSpec.progOf oC) junk) (inp : List UInt8) (hin : inp.length < 2 ^ 64)
    (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l (mC inp)) := by
  have hev := C_expr inp hin hs
  have hw : Wf (sigOf oC) [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) c_sig_m (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact ev_denotes_assembled L E Op cPWf hev hw (.cons (.ls _) .nil) _ hD

/-- **the same, with `+` and UInt64 `==` discharged** (`Final`): what remains is `Final.Open2` -/
theorem C_denotes_final (L : SetLaws O) {junk : S} (E : Final.Env2 env (sigOf oC) (ExprSpec.progOf oC))
    (Op : Final.Open2 M (sigOf oC) (ExprSpec.progOf oC) junk) (hbl : HasTy env "br_litN" [] Final.brLitNTy)
    (inp : List UInt8) (hin : inp.length < 2 ^ 64) (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l (mC inp)) := by
  have hev := C_expr inp hin hs
  have hw : Wf (sigOf oC) [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) c_sig_m (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact Final.ev_denotes_final L E Op hbl cPWf hev hw (.cons (.ls _) .nil) _ hD

/-- **the same, with `+`, UInt64 `==` and UInt64 `<` discharged** (`Final3`): what remains is `Final3.Open3` -/
theorem C_denotes_final3 (L : SetLaws O) {junk : S} (E : Final3.Env3 env (sigOf oC) (ExprSpec.progOf oC))
    (Op : Final3.Open3 M (sigOf oC) (ExprSpec.progOf oC) junk) (hbl : HasTy env "br_litN" [] Final.brLitNTy)
    (inp : List UInt8) (hin : inp.length < 2 ^ 64) (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l (mC inp)) := by
  have hev := C_expr inp hin hs
  have hw : Wf (sigOf oC) [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) c_sig_m (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact Final3.ev_denotes_final3 L E Op hbl cPWf hev hw (.cons (.ls _) .nil) _ hD

/-- **the current headline**: `+`, UInt64 `==`/`<`, and the prelude ops `len'`, `len`, `bsize`, `bnew`, `bpush`
discharged; what remains is `Final4.Open4` -/
theorem C_denotes_final4 (L : SetLaws O) {junk : S} (E : Final4.Env4 env (sigOf oC) (ExprSpec.progOf oC))
    (Op : Final4.Open4 M (sigOf oC) (ExprSpec.progOf oC) junk) (hbl : HasTy env "br_litN" [] Final.brLitNTy)
    (inp : List UInt8) (hin : inp.length < 2 ^ 64) (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l (mC inp)) := by
  have hev := C_expr inp hin hs
  have hw : Wf (sigOf oC) [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) c_sig_m (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact Final4.ev_denotes_final4 L E Op hbl cPWf hev hw (.cons (.ls _) .nil) _ hD

/-- **the current headline**: `+`, UInt64 `==`/`<` and all nine prelude ops discharged; what remains is
`Final5.Open5` (the bin ops −,×,&,|,<<,>> and 3 Nat-operand ites) -/
theorem C_denotes_final5 (L : SetLaws O) {junk : S} (E : Final5.Env5 env (sigOf oC) (ExprSpec.progOf oC))
    (Op : Final5.Open5 M (sigOf oC) (ExprSpec.progOf oC) junk) (hbl : HasTy env "br_litN" [] Final.brLitNTy)
    (inp : List UInt8) (hin : inp.length < 2 ^ 64) (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l (mC inp)) := by
  have hev := C_expr inp hin hs
  have hw : Wf (sigOf oC) [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) c_sig_m (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact Final5.ev_denotes_final5 L E Op hbl cPWf hev hw (.cons (.ls _) .nil) _ hD

/-- **the current headline**: `+`, `-`, `*`, UInt64 `==`/`<` and all nine prelude ops discharged; what remains is
`Final6.Open6` (the bin ops &, |, <<, >> and 3 Nat-operand ites) -/
theorem C_denotes_final6 (L : SetLaws O) {junk : S} (E : Final6.Env6 env (sigOf oC) (ExprSpec.progOf oC))
    (Op : Final6.Open6 M (sigOf oC) (ExprSpec.progOf oC) junk) (hbl : HasTy env "br_litN" [] Final.brLitNTy)
    (inp : List UInt8) (hin : inp.length < 2 ^ 64) (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l (mC inp)) := by
  have hev := C_expr inp hin hs
  have hw : Wf (sigOf oC) [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) c_sig_m (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact Final6.ev_denotes_final6 L E Op hbl cPWf hev hw (.cons (.ls _) .nil) _ hD

/-- **the current headline**: `+ - * <<< >>>`, UInt64 `==`/`<`, all nine prelude ops discharged; what remains is
`Final7.Open7`: `&&&`, `|||` and the 3 Nat-operand ites of C -/
theorem C_denotes_final7 (L : SetLaws O) {junk : S} (E : Final7.Env7 env (sigOf oC) (ExprSpec.progOf oC))
    (Op : Final7.Open7 M (sigOf oC) (ExprSpec.progOf oC) junk) (hbl : HasTy env "br_litN" [] Final.brLitNTy)
    (inp : List UInt8) (hin : inp.length < 2 ^ 64) (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l (mC inp)) := by
  have hev := C_expr inp hin hs
  have hw : Wf (sigOf oC) [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) c_sig_m (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact Final7.ev_denotes_final7 L E Op hbl cPWf hev hw (.cons (.ls _) .nil) _ hD

/-- **the current headline**: all seven bin ops `+ - * &&& ||| <<< >>>`, UInt64 `==`/`<`, all nine prelude ops
discharged; what remains is `Final8.Open8`: the 3 Nat-operand ites of C -/
theorem C_denotes_final8 (L : SetLaws O) {junk : S} (E : Final8.Env8 env (sigOf oC) (ExprSpec.progOf oC))
    (Op : Final8.Open8 M (sigOf oC) (ExprSpec.progOf oC) junk) (hbl : HasTy env "br_litN" [] Final.brLitNTy)
    (inp : List UInt8) (hin : inp.length < 2 ^ 64) (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l (mC inp)) := by
  have hev := C_expr inp hin hs
  have hw : Wf (sigOf oC) [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) c_sig_m (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact Final8.ev_denotes_final8 L E Op hbl cPWf hev hw (.cons (.ls _) .nil) _ hD

/-- **the current headline**: all seven bin ops, UInt64 `==`/`<`, Nat `==`, all nine prelude ops discharged; what
remains is `Final9.Open9`: ites on Nat `<` and on `dropHead`-affected UInt64 `<` — forms that do not occur in C -/
theorem C_denotes_final9 (L : SetLaws O) {junk : S} (E : Final9.Env9 env (sigOf oC) (ExprSpec.progOf oC))
    (Op : Final9.Open9 M (sigOf oC) (ExprSpec.progOf oC) junk) (hbl : HasTy env "br_litN" [] Final.brLitNTy)
    (inp : List UInt8) (hin : inp.length < 2 ^ 64) (hs : Sem κC Cert.PC.all inp = .ok (mC inp)) :
    O.app (M.cval "m" []) (encM M (.l inp)) = encM M (.l (mC inp)) := by
  have hev := C_expr inp hin hs
  have hw : Wf (sigOf oC) [.ls] (.app (.c "m" []) (.bv 0)) .ls :=
    .call (n := "m") (as := [.bv 0]) rfl (by simp [Typed.reserved]) c_sig_m (.cons (.bv rfl rfl) .nil)
  have hD : D O M.cval (ρE (encM M) junk [.l inp]) (trM (.app (.c "m" []) (.bv 0)))
      (O.app (M.cval "m" []) (encM M (.l inp))) := .app .const .bvar
  exact Final9.ev_denotes_final9 L E Op hbl cPWf hev hw (.cons (.ls _) .nil) _ hD

end Bridge.TopC
