/- Bridge.CheckExamples: the `Wf` checker on real emitted programs (non-vacuity of `Wf`/`PWf`).
* `#guard`: `pwfChk` accepts the emitted Exprs of `exSum` (a fuel loop with CONTINUE) and `exPair` (lets, pairs,
  Prod.casesOn, `<`-ite with `decLt`) from Nano/Expr/Eval.lean.
* `pairPWf`: a KERNEL proof (`decide +kernel` on the literal emitted Expr of `exPair`, axioms: propext) that the
  program is well formed (`PWf`).  The literal is `emitXs exPair` printed by `#eval`; `pair_emit` checks by
  `#guard` that it is what `emitXs` produces.  (Kernel reduction of `emitXs` itself gets stuck on `String.toUTF8`,
  so a per-program proof goes through the literal Expr, as the C_lean tooling does.)

STATUS: proved, no sorry. -/
import Bridge.Check

namespace Bridge.CheckEx
open ExprSpec ParSpec Bridge.Check Bridge.Typed

def piInv : X → Option (List Sh × Sh)
  | .pi t b => do let s ← shInv t; let (ps, r) ← piInv b; some (s :: ps, r)
  | t => do let r ← shInv t; some ([], r)

/-- signatures read off the emitted def types (`piX params (shTy res)`) -/
def sigOf (o : List (String × X × X)) : Sig := fun n =>
  if n ∈ Bridge.Typed.reserved then none else ((o.lookup n).bind fun (t, _) => piInv t)

theorem sigOf_res {o : List (String × X × X)} {n ps r} (h : sigOf o n = some (ps, r)) : n ∉ Bridge.Typed.reserved := by
  intro hn; simp [sigOf, hn] at h

def progOf (o : List (String × X × X)) : Prog := o.map fun (n, _, v) => (n, v)

def test (src : String) : Bool :=
  match emitXs src.toUTF8.toList with
  | .ok o => pwfChk (sigOf o) 10000 (progOf o)
  | .error _ => false

#guard test exSum
#guard test exPair

def pairO : List (String × X × X) :=
[("f",
  ExprSpec.X.pi
    (ExprSpec.X.c "UInt64" [])
    (ExprSpec.X.pi
      (ExprSpec.X.c "UInt64" [])
      (ExprSpec.X.app
        (ExprSpec.X.app (ExprSpec.X.c "Prod" [0, 0]) (ExprSpec.X.c "UInt64" []))
        (ExprSpec.X.c "UInt64" []))),
  ExprSpec.X.lam
    (ExprSpec.X.c "UInt64" [])
    (ExprSpec.X.lam
      (ExprSpec.X.c "UInt64" [])
      (ExprSpec.X.lt
        true
        (ExprSpec.X.c "UInt64" [])
        (ExprSpec.X.app
          (ExprSpec.X.app
            (ExprSpec.X.app
              (ExprSpec.X.app
                (ExprSpec.X.app
                  (ExprSpec.X.app (ExprSpec.X.c "HAdd.hAdd" [0, 0, 0]) (ExprSpec.X.c "UInt64" []))
                  (ExprSpec.X.c "UInt64" []))
                (ExprSpec.X.c "UInt64" []))
              (ExprSpec.X.app
                (ExprSpec.X.app (ExprSpec.X.c "instHAdd" [0]) (ExprSpec.X.c "UInt64" []))
                (ExprSpec.X.c "instAddUInt64" [])))
            (ExprSpec.X.bv 1))
          (ExprSpec.X.bv 0))
        (ExprSpec.X.app
          (ExprSpec.X.app
            (ExprSpec.X.app
              (ExprSpec.X.app
                (ExprSpec.X.app (ExprSpec.X.c "Prod.casesOn" [1, 0, 0]) (ExprSpec.X.c "UInt64" []))
                (ExprSpec.X.c "UInt64" []))
              (ExprSpec.X.lam
                (ExprSpec.X.app
                  (ExprSpec.X.app (ExprSpec.X.c "Prod" [0, 0]) (ExprSpec.X.c "UInt64" []))
                  (ExprSpec.X.c "UInt64" []))
                (ExprSpec.X.app
                  (ExprSpec.X.app (ExprSpec.X.c "Prod" [0, 0]) (ExprSpec.X.c "UInt64" []))
                  (ExprSpec.X.c "UInt64" []))))
            (ExprSpec.X.app
              (ExprSpec.X.app
                (ExprSpec.X.app
                  (ExprSpec.X.app (ExprSpec.X.c "Prod.mk" [0, 0]) (ExprSpec.X.c "UInt64" []))
                  (ExprSpec.X.c "UInt64" []))
                (ExprSpec.X.bv 0))
              (ExprSpec.X.bv 2)))
          (ExprSpec.X.lam
            (ExprSpec.X.c "UInt64" [])
            (ExprSpec.X.lam
              (ExprSpec.X.c "UInt64" [])
              (ExprSpec.X.app
                (ExprSpec.X.app
                  (ExprSpec.X.app
                    (ExprSpec.X.app
                      (ExprSpec.X.app
                        (ExprSpec.X.c "ite" [1])
                        (ExprSpec.X.app
                          (ExprSpec.X.app (ExprSpec.X.c "Prod" [0, 0]) (ExprSpec.X.c "UInt64" []))
                          (ExprSpec.X.c "UInt64" [])))
                      (ExprSpec.X.app
                        (ExprSpec.X.app
                          (ExprSpec.X.app
                            (ExprSpec.X.app (ExprSpec.X.c "LT.lt" [0]) (ExprSpec.X.c "UInt64" []))
                            (ExprSpec.X.c "instLTUInt64" []))
                          (ExprSpec.X.bv 1))
                        (ExprSpec.X.bv 0)))
                    (ExprSpec.X.app
                      (ExprSpec.X.app (ExprSpec.X.c "UInt64.decLt" []) (ExprSpec.X.bv 1))
                      (ExprSpec.X.bv 0)))
                  (ExprSpec.X.app
                    (ExprSpec.X.app
                      (ExprSpec.X.app
                        (ExprSpec.X.app (ExprSpec.X.c "Prod.mk" [0, 0]) (ExprSpec.X.c "UInt64" []))
                        (ExprSpec.X.c "UInt64" []))
                      (ExprSpec.X.bv 1))
                    (ExprSpec.X.bv 0)))
                (ExprSpec.X.app
                  (ExprSpec.X.app
                    (ExprSpec.X.app
                      (ExprSpec.X.app (ExprSpec.X.c "Prod.mk" [0, 0]) (ExprSpec.X.c "UInt64" []))
                      (ExprSpec.X.c "UInt64" []))
                    (ExprSpec.X.bv 0))
                  (ExprSpec.X.bv 1))))))))),
 ("m",
  ExprSpec.X.pi
    (ExprSpec.X.app (ExprSpec.X.c "List" [0]) (ExprSpec.X.c "UInt8" []))
    (ExprSpec.X.app (ExprSpec.X.c "List" [0]) (ExprSpec.X.c "UInt8" [])),
  ExprSpec.X.lam
    (ExprSpec.X.app (ExprSpec.X.c "List" [0]) (ExprSpec.X.c "UInt8" []))
    (ExprSpec.X.app
      (ExprSpec.X.app
        (ExprSpec.X.app
          (ExprSpec.X.app
            (ExprSpec.X.app (ExprSpec.X.c "Prod.casesOn" [1, 0, 0]) (ExprSpec.X.c "UInt64" []))
            (ExprSpec.X.c "UInt64" []))
          (ExprSpec.X.lam
            (ExprSpec.X.app
              (ExprSpec.X.app (ExprSpec.X.c "Prod" [0, 0]) (ExprSpec.X.c "UInt64" []))
              (ExprSpec.X.c "UInt64" []))
            (ExprSpec.X.app (ExprSpec.X.c "List" [0]) (ExprSpec.X.c "UInt8" []))))
        (ExprSpec.X.app
          (ExprSpec.X.app
            (ExprSpec.X.c "f" [])
            (ExprSpec.X.app
              (ExprSpec.X.app (ExprSpec.X.c "rd" []) (ExprSpec.X.bv 0))
              (ExprSpec.X.app
                (ExprSpec.X.app
                  (ExprSpec.X.app (ExprSpec.X.c "OfNat.ofNat" [0]) (ExprSpec.X.c "UInt64" []))
                  (ExprSpec.X.nat 0))
                (ExprSpec.X.app (ExprSpec.X.c "UInt64.instOfNat" []) (ExprSpec.X.nat 0)))))
          (ExprSpec.X.app
            (ExprSpec.X.app
              (ExprSpec.X.app (ExprSpec.X.c "OfNat.ofNat" [0]) (ExprSpec.X.c "UInt64" []))
              (ExprSpec.X.nat 2))
            (ExprSpec.X.app (ExprSpec.X.c "UInt64.instOfNat" []) (ExprSpec.X.nat 2)))))
      (ExprSpec.X.lam
        (ExprSpec.X.c "UInt64" [])
        (ExprSpec.X.lam
          (ExprSpec.X.c "UInt64" [])
          (ExprSpec.X.app
            (ExprSpec.X.app
              (ExprSpec.X.c "put" [])
              (ExprSpec.X.app
                (ExprSpec.X.app
                  (ExprSpec.X.c "put" [])
                  (ExprSpec.X.app (ExprSpec.X.c "List.nil" [0]) (ExprSpec.X.c "UInt8" [])))
                (ExprSpec.X.bv 1)))
            (ExprSpec.X.bv 0))))))]

#guard (match emitXs exPair.toUTF8.toList with | .ok o => decide (o = pairO) | .error _ => false)

theorem pairChk : pwfChk (sigOf pairO) 200 (progOf pairO) = true := by decide +kernel

/-- **`exPair`'s emitted program is well formed** (kernel-checked) -/
theorem pairPWf : PWf (sigOf pairO) (progOf pairO) := pwfChk_sound pairChk sigOf_res

end Bridge.CheckEx
