import ConLeche.MainTheorem
/-! The tiny stream as con-leche reads it: `preparePrelude builtinPrelude (parseChunks tiny.ndjson).decls`, printed by `Repr` (Testing/denotes_real/Gen). -/
set_option maxRecDepth 100000
def Bridge.Real.dsTiny : Array ConLeche.Declaration :=
#[ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "Eq",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.bvar 0)
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.bvar 1)
                       (ConLeche.Expr.sort (ConLeche.Level.zero))
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq") "refl",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.bvar 0)
                     (ConLeche.Expr.app
                       (ConLeche.Expr.app
                         (ConLeche.Expr.app
                           (ConLeche.Expr.const
                             (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                             [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                           (ConLeche.Expr.bvar 1))
                         (ConLeche.Expr.bvar 0))
                       (ConLeche.Expr.bvar 0))
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       2
       0,
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.bvar 0)
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.bvar 1)
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.const
                                   (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                                   [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                                 (ConLeche.Expr.bvar 2))
                               (ConLeche.Expr.bvar 1))
                             (ConLeche.Expr.bvar 0))
                           (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 0) (ConLeche.Expr.bvar 1))
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq") "refl")
                                 [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                               (ConLeche.Expr.bvar 2))
                             (ConLeche.Expr.bvar 1)))
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 3)
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.const
                                     (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                                     [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                                   (ConLeche.Expr.bvar 4))
                                 (ConLeche.Expr.bvar 3))
                               (ConLeche.Expr.bvar 0))
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 1))
                               (ConLeche.Expr.bvar 0))
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       5
       4
       [{ ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq") "refl",
          nfields := 0,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.bvar 0)
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.bvar 1)
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.const
                                   (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                                   [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                                 (ConLeche.Expr.bvar 2))
                               (ConLeche.Expr.bvar 1))
                             (ConLeche.Expr.bvar 0))
                           (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.lam
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 0) (ConLeche.Expr.bvar 1))
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq") "refl")
                                 [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                               (ConLeche.Expr.bvar 2))
                             (ConLeche.Expr.bvar 1)))
                         (ConLeche.Expr.bvar 0)
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false }]]
    2,
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "Nat",
         levelParams := [],
         type := ConLeche.Expr.sort (ConLeche.Level.succ (ConLeche.Level.zero)) }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero",
         levelParams := [],
         type := ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [] }
       0
       0,
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ",
         levelParams := [],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                   (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                   { pw := ConLeche.PropWhen.never } }
       0
       1,
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.app
                       (ConLeche.Expr.bvar 0)
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero")
                         []))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                           (ConLeche.Expr.app
                             (ConLeche.Expr.bvar 3)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                                 [])
                               (ConLeche.Expr.bvar 1)))
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                         (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 0))
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       3
       3
       [{ ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero",
          nfields := 0,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.app
                       (ConLeche.Expr.bvar 0)
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero")
                         []))
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                           (ConLeche.Expr.app
                             (ConLeche.Expr.bvar 3)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                                 [])
                               (ConLeche.Expr.bvar 1)))
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.bvar 1)
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false },
        { ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ",
          nfields := 1,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.app
                       (ConLeche.Expr.bvar 0)
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero")
                         []))
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                           (ConLeche.Expr.app
                             (ConLeche.Expr.bvar 3)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                                 [])
                               (ConLeche.Expr.bvar 1)))
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.lam
                         (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 1) (ConLeche.Expr.bvar 0))
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.const
                                     (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "rec")
                                     [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                                   (ConLeche.Expr.bvar 3))
                                 (ConLeche.Expr.bvar 2))
                               (ConLeche.Expr.bvar 1))
                             (ConLeche.Expr.bvar 0)))
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false }]]
    0,
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "Empty",
         levelParams := [],
         type := ConLeche.Expr.sort (ConLeche.Level.succ (ConLeche.Level.zero)) }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Empty") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Empty") [])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Empty") [])
                     (ConLeche.Expr.app (ConLeche.Expr.bvar 1) (ConLeche.Expr.bvar 0))
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       1
       1
       []]
    0,
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "False",
         levelParams := [],
         type := ConLeche.Expr.sort (ConLeche.Level.zero) }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "False") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "False") [])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "False") [])
                     (ConLeche.Expr.app (ConLeche.Expr.bvar 1) (ConLeche.Expr.bvar 0))
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       1
       1
       []]
    0,
  ConLeche.Declaration.quotDecl
    (ConLeche.QuotKind.type)
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "Quot",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.bvar 0)
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.bvar 1)
                      (ConLeche.Expr.sort (ConLeche.Level.zero))
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } },
  ConLeche.Declaration.quotDecl
    (ConLeche.QuotKind.ctor)
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot") "mk",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.bvar 0)
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.bvar 1)
                      (ConLeche.Expr.sort (ConLeche.Level.zero))
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.bvar 1)
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot")
                          [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                        (ConLeche.Expr.bvar 2))
                      (ConLeche.Expr.bvar 1))
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } },
  ConLeche.Declaration.quotDecl
    (ConLeche.QuotKind.lift)
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot") "lift",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u", ConLeche.Name.str (ConLeche.Name.anonymous) "v"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.bvar 0)
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.bvar 1)
                      (ConLeche.Expr.sort (ConLeche.Level.zero))
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")))
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.bvar 2)
                        (ConLeche.Expr.bvar 1)
                        { pw := ConLeche.PropWhen.never })
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.forallE
                          (ConLeche.Expr.bvar 3)
                          (ConLeche.Expr.forallE
                            (ConLeche.Expr.bvar 4)
                            (ConLeche.Expr.forallE
                              (ConLeche.Expr.app
                                (ConLeche.Expr.app (ConLeche.Expr.bvar 4) (ConLeche.Expr.bvar 1))
                                (ConLeche.Expr.bvar 0))
                              (ConLeche.Expr.app
                                (ConLeche.Expr.app
                                  (ConLeche.Expr.app
                                    (ConLeche.Expr.const
                                      (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                                      [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")])
                                    (ConLeche.Expr.bvar 4))
                                  (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 2)))
                                (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 1)))
                              { pw := ConLeche.PropWhen.never })
                            { pw := ConLeche.PropWhen.never })
                          { pw := ConLeche.PropWhen.never })
                        (ConLeche.Expr.forallE
                          (ConLeche.Expr.app
                            (ConLeche.Expr.app
                              (ConLeche.Expr.const
                                (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot")
                                [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                              (ConLeche.Expr.bvar 4))
                            (ConLeche.Expr.bvar 3))
                          (ConLeche.Expr.bvar 3)
                          { pw := ConLeche.PropWhen.never })
                        { pw := ConLeche.PropWhen.never })
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } },
  ConLeche.Declaration.quotDecl
    (ConLeche.QuotKind.ind)
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot") "ind",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.bvar 0)
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.bvar 1)
                      (ConLeche.Expr.sort (ConLeche.Level.zero))
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.const
                            (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot")
                            [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                          (ConLeche.Expr.bvar 1))
                        (ConLeche.Expr.bvar 0))
                      (ConLeche.Expr.sort (ConLeche.Level.zero))
                      { pw := ConLeche.PropWhen.never })
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.bvar 2)
                        (ConLeche.Expr.app
                          (ConLeche.Expr.bvar 1)
                          (ConLeche.Expr.app
                            (ConLeche.Expr.app
                              (ConLeche.Expr.app
                                (ConLeche.Expr.const
                                  (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot") "mk")
                                  [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                                (ConLeche.Expr.bvar 3))
                              (ConLeche.Expr.bvar 2))
                            (ConLeche.Expr.bvar 0)))
                        { pw := ConLeche.PropWhen.never })
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.const
                              (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot")
                              [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                            (ConLeche.Expr.bvar 3))
                          (ConLeche.Expr.bvar 2))
                        (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                        { pw := ConLeche.PropWhen.never })
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } },
  ConLeche.Declaration.axiomDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot") "sound",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.bvar 0)
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.bvar 1)
                      (ConLeche.Expr.sort (ConLeche.Level.zero))
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.bvar 1)
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.bvar 2)
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 1))
                          (ConLeche.Expr.bvar 0))
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.app
                              (ConLeche.Expr.const
                                (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                                [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                              (ConLeche.Expr.app
                                (ConLeche.Expr.app
                                  (ConLeche.Expr.const
                                    (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot")
                                    [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                                  (ConLeche.Expr.bvar 4))
                                (ConLeche.Expr.bvar 3)))
                            (ConLeche.Expr.app
                              (ConLeche.Expr.app
                                (ConLeche.Expr.app
                                  (ConLeche.Expr.const
                                    (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot") "mk")
                                    [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                                  (ConLeche.Expr.bvar 4))
                                (ConLeche.Expr.bvar 3))
                              (ConLeche.Expr.bvar 2)))
                          (ConLeche.Expr.app
                            (ConLeche.Expr.app
                              (ConLeche.Expr.app
                                (ConLeche.Expr.const
                                  (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Quot") "mk")
                                  [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                                (ConLeche.Expr.bvar 4))
                              (ConLeche.Expr.bvar 3))
                            (ConLeche.Expr.bvar 1)))
                        { pw := ConLeche.PropWhen.never })
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } },
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "And",
         levelParams := [],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort (ConLeche.Level.zero))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.sort (ConLeche.Level.zero))
                     (ConLeche.Expr.sort (ConLeche.Level.zero))
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "And") "intro",
         levelParams := [],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort (ConLeche.Level.zero))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.sort (ConLeche.Level.zero))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.bvar 1)
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.bvar 1)
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app
                             (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "And") [])
                             (ConLeche.Expr.bvar 3))
                           (ConLeche.Expr.bvar 2))
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       2
       2,
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "And") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort (ConLeche.Level.zero))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.sort (ConLeche.Level.zero))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app
                             (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "And") [])
                             (ConLeche.Expr.bvar 1))
                           (ConLeche.Expr.bvar 0))
                         (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 2)
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.bvar 2)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.bvar 2)
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.app
                                     (ConLeche.Expr.app
                                       (ConLeche.Expr.const
                                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "And") "intro")
                                         [])
                                       (ConLeche.Expr.bvar 4))
                                     (ConLeche.Expr.bvar 3))
                                   (ConLeche.Expr.bvar 1))
                                 (ConLeche.Expr.bvar 0)))
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "And") [])
                               (ConLeche.Expr.bvar 3))
                             (ConLeche.Expr.bvar 2))
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       4
       4
       [{ ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "And") "intro",
          nfields := 2,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.sort (ConLeche.Level.zero))
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.sort (ConLeche.Level.zero))
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app
                             (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "And") [])
                             (ConLeche.Expr.bvar 1))
                           (ConLeche.Expr.bvar 0))
                         (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.lam
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 2)
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.bvar 2)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.bvar 2)
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.app
                                     (ConLeche.Expr.app
                                       (ConLeche.Expr.const
                                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "And") "intro")
                                         [])
                                       (ConLeche.Expr.bvar 4))
                                     (ConLeche.Expr.bvar 3))
                                   (ConLeche.Expr.bvar 1))
                                 (ConLeche.Expr.bvar 0)))
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.lam
                           (ConLeche.Expr.bvar 3)
                           (ConLeche.Expr.lam
                             (ConLeche.Expr.bvar 3)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 1))
                               (ConLeche.Expr.bvar 0))
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false }]]
    2,
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "Bool",
         levelParams := [],
         type := ConLeche.Expr.sort (ConLeche.Level.succ (ConLeche.Level.zero)) }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "false",
         levelParams := [],
         type := ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") [] }
       0
       0,
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "true",
         levelParams := [],
         type := ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") [] }
       0
       0,
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") [])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.app
                       (ConLeche.Expr.bvar 0)
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "false")
                         []))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.app
                         (ConLeche.Expr.bvar 1)
                         (ConLeche.Expr.const
                           (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "true")
                           []))
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") [])
                         (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 0))
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       3
       3
       [{ ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "false",
          nfields := 0,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") [])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.app
                       (ConLeche.Expr.bvar 0)
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "false")
                         []))
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.app
                         (ConLeche.Expr.bvar 1)
                         (ConLeche.Expr.const
                           (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "true")
                           []))
                       (ConLeche.Expr.bvar 1)
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false },
        { ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "true",
          nfields := 0,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") [])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.app
                       (ConLeche.Expr.bvar 0)
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "false")
                         []))
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.app
                         (ConLeche.Expr.bvar 1)
                         (ConLeche.Expr.const
                           (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Bool") "true")
                           []))
                       (ConLeche.Expr.bvar 0)
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false }]]
    0,
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "outParam",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
      (ConLeche.Expr.bvar 0)
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.regular 1),
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "v",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "w"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.sort
                       (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"))))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.app
                         (ConLeche.Expr.const
                           (ConLeche.Name.str (ConLeche.Name.anonymous) "outParam")
                           [ConLeche.Level.succ
                              (ConLeche.Level.succ
                                (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")))])
                         (ConLeche.Expr.sort
                           (ConLeche.Level.succ
                             (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")))))
                       (ConLeche.Expr.sort
                         (ConLeche.Level.max
                           (ConLeche.Level.max
                             (ConLeche.Level.succ
                               (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                             (ConLeche.Level.succ
                               (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"))))
                           (ConLeche.Level.succ
                             (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")))))
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "mk",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "v",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "w"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.sort
                       (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"))))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.app
                         (ConLeche.Expr.const
                           (ConLeche.Name.str (ConLeche.Name.anonymous) "outParam")
                           [ConLeche.Level.succ
                              (ConLeche.Level.succ
                                (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")))])
                         (ConLeche.Expr.sort
                           (ConLeche.Level.succ
                             (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")))))
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 2)
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.bvar 2)
                             (ConLeche.Expr.bvar 2)
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd")
                                 [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                  ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"),
                                  ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")])
                               (ConLeche.Expr.bvar 3))
                             (ConLeche.Expr.bvar 2))
                           (ConLeche.Expr.bvar 1))
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       3
       1,
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u_1",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "u",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "v",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "w"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.sort
                       (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"))))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.sort
                         (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w"))))
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.const
                                   (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd")
                                   [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                    ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"),
                                    ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")])
                                 (ConLeche.Expr.bvar 2))
                               (ConLeche.Expr.bvar 1))
                             (ConLeche.Expr.bvar 0))
                           (ConLeche.Expr.sort
                             (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.forallE
                               (ConLeche.Expr.bvar 3)
                               (ConLeche.Expr.forallE
                                 (ConLeche.Expr.bvar 3)
                                 (ConLeche.Expr.bvar 3)
                                 { pw := ConLeche.PropWhen.never })
                               { pw := ConLeche.PropWhen.never })
                             (ConLeche.Expr.app
                               (ConLeche.Expr.bvar 1)
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.app
                                     (ConLeche.Expr.app
                                       (ConLeche.Expr.const
                                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "mk")
                                         [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                          ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"),
                                          ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")])
                                       (ConLeche.Expr.bvar 4))
                                     (ConLeche.Expr.bvar 3))
                                   (ConLeche.Expr.bvar 2))
                                 (ConLeche.Expr.bvar 0)))
                             { pw := ConLeche.PropWhen.never })
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.const
                                     (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd")
                                     [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                      ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"),
                                      ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")])
                                   (ConLeche.Expr.bvar 4))
                                 (ConLeche.Expr.bvar 3))
                               (ConLeche.Expr.bvar 2))
                             (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       5
       5
       [{ ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "mk",
          nfields := 1,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.sort
                       (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"))))
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.sort
                         (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w"))))
                       (ConLeche.Expr.lam
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.const
                                   (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd")
                                   [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                    ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"),
                                    ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")])
                                 (ConLeche.Expr.bvar 2))
                               (ConLeche.Expr.bvar 1))
                             (ConLeche.Expr.bvar 0))
                           (ConLeche.Expr.sort
                             (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.lam
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.forallE
                               (ConLeche.Expr.bvar 3)
                               (ConLeche.Expr.forallE
                                 (ConLeche.Expr.bvar 3)
                                 (ConLeche.Expr.bvar 3)
                                 { pw := ConLeche.PropWhen.never })
                               { pw := ConLeche.PropWhen.never })
                             (ConLeche.Expr.app
                               (ConLeche.Expr.bvar 1)
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.app
                                     (ConLeche.Expr.app
                                       (ConLeche.Expr.const
                                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "mk")
                                         [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                          ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"),
                                          ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")])
                                       (ConLeche.Expr.bvar 4))
                                     (ConLeche.Expr.bvar 3))
                                   (ConLeche.Expr.bvar 2))
                                 (ConLeche.Expr.bvar 0)))
                             { pw := ConLeche.PropWhen.never })
                           (ConLeche.Expr.lam
                             (ConLeche.Expr.forallE
                               (ConLeche.Expr.bvar 4)
                               (ConLeche.Expr.forallE
                                 (ConLeche.Expr.bvar 4)
                                 (ConLeche.Expr.bvar 4)
                                 { pw := ConLeche.PropWhen.never })
                               { pw := ConLeche.PropWhen.never })
                             (ConLeche.Expr.app (ConLeche.Expr.bvar 1) (ConLeche.Expr.bvar 0))
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false }]]
    3,
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "hAdd",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u",
                      ConLeche.Name.str (ConLeche.Name.anonymous) "v",
                      ConLeche.Name.str (ConLeche.Name.anonymous) "w"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort
                  (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.sort
                    (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"))))
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.anonymous) "outParam")
                        [ConLeche.Level.succ
                           (ConLeche.Level.succ
                             (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")))])
                      (ConLeche.Expr.sort
                        (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")))))
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.const
                              (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd")
                              [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                               ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"),
                               ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")])
                            (ConLeche.Expr.bvar 2))
                          (ConLeche.Expr.bvar 1))
                        (ConLeche.Expr.bvar 0))
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.bvar 3)
                        (ConLeche.Expr.forallE
                          (ConLeche.Expr.bvar 3)
                          (ConLeche.Expr.bvar 3)
                          { pw := ConLeche.PropWhen.never })
                        { pw := ConLeche.PropWhen.never })
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.sort
        (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
      (ConLeche.Expr.lam
        (ConLeche.Expr.sort
          (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"))))
        (ConLeche.Expr.lam
          (ConLeche.Expr.app
            (ConLeche.Expr.const
              (ConLeche.Name.str (ConLeche.Name.anonymous) "outParam")
              [ConLeche.Level.succ
                 (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")))])
            (ConLeche.Expr.sort
              (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")))))
          (ConLeche.Expr.lam
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.const
                    (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd")
                    [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                     ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"),
                     ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "w")])
                  (ConLeche.Expr.bvar 2))
                (ConLeche.Expr.bvar 1))
              (ConLeche.Expr.bvar 0))
            (ConLeche.Expr.proj (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") 0 (ConLeche.Expr.bvar 0))
            { pw := ConLeche.PropWhen.never })
          { pw := ConLeche.PropWhen.never })
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.abbrev),
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "Add",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   { pw := ConLeche.PropWhen.never } }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") "mk",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.bvar 0)
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.bvar 1)
                         (ConLeche.Expr.bvar 2)
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     (ConLeche.Expr.app
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.anonymous) "Add")
                         [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                       (ConLeche.Expr.bvar 1))
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       1
       1,
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u_1",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.app
                         (ConLeche.Expr.const
                           (ConLeche.Name.str (ConLeche.Name.anonymous) "Add")
                           [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                         (ConLeche.Expr.bvar 0))
                       (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                       { pw := ConLeche.PropWhen.never })
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 1)
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.bvar 2)
                             (ConLeche.Expr.bvar 3)
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.app
                           (ConLeche.Expr.bvar 1)
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") "mk")
                                 [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                               (ConLeche.Expr.bvar 2))
                             (ConLeche.Expr.bvar 0)))
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.app
                           (ConLeche.Expr.const
                             (ConLeche.Name.str (ConLeche.Name.anonymous) "Add")
                             [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                           (ConLeche.Expr.bvar 2))
                         (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       3
       3
       [{ ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") "mk",
          nfields := 1,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.app
                         (ConLeche.Expr.const
                           (ConLeche.Name.str (ConLeche.Name.anonymous) "Add")
                           [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                         (ConLeche.Expr.bvar 0))
                       (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                       { pw := ConLeche.PropWhen.never })
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 1)
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.bvar 2)
                             (ConLeche.Expr.bvar 3)
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.app
                           (ConLeche.Expr.bvar 1)
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") "mk")
                                 [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                               (ConLeche.Expr.bvar 2))
                             (ConLeche.Expr.bvar 0)))
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.lam
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 2)
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.bvar 3)
                             (ConLeche.Expr.bvar 4)
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.app (ConLeche.Expr.bvar 1) (ConLeche.Expr.bvar 0))
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false }]]
    1,
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") "add",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort
                  (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const
                      (ConLeche.Name.str (ConLeche.Name.anonymous) "Add")
                      [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                    (ConLeche.Expr.bvar 0))
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.bvar 1)
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.bvar 2)
                      (ConLeche.Expr.bvar 3)
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.sort
        (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
      (ConLeche.Expr.lam
        (ConLeche.Expr.app
          (ConLeche.Expr.const
            (ConLeche.Name.str (ConLeche.Name.anonymous) "Add")
            [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
          (ConLeche.Expr.bvar 0))
        (ConLeche.Expr.proj (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") 0 (ConLeche.Expr.bvar 0))
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.abbrev),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "instHAdd",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort
                  (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"))))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const
                      (ConLeche.Name.str (ConLeche.Name.anonymous) "Add")
                      [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                    (ConLeche.Expr.bvar 0))
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd")
                          [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"),
                           ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"),
                           ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                        (ConLeche.Expr.bvar 1))
                      (ConLeche.Expr.bvar 1))
                    (ConLeche.Expr.bvar 1))
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.sort
        (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"))))
      (ConLeche.Expr.lam
        (ConLeche.Expr.app
          (ConLeche.Expr.const
            (ConLeche.Name.str (ConLeche.Name.anonymous) "Add")
            [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
          (ConLeche.Expr.bvar 0))
        (ConLeche.Expr.app
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.const
                  (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "mk")
                  [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"),
                   ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"),
                   ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                (ConLeche.Expr.bvar 1))
              (ConLeche.Expr.bvar 1))
            (ConLeche.Expr.bvar 1))
          (ConLeche.Expr.lam
            (ConLeche.Expr.bvar 1)
            (ConLeche.Expr.lam
              (ConLeche.Expr.bvar 2)
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") "add")
                        [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                      (ConLeche.Expr.bvar 3))
                    (ConLeche.Expr.bvar 2))
                  (ConLeche.Expr.bvar 1))
                (ConLeche.Expr.bvar 0))
              { pw := ConLeche.PropWhen.never })
            { pw := ConLeche.PropWhen.never }))
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.regular 1),
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")) }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit") "unit",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.const
                   (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit")
                   [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")] }
       0
       0,
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u_1",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const
                       (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit")
                       [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.app
                       (ConLeche.Expr.bvar 0)
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit") "unit")
                         [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")]))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit")
                         [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                       (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       2
       2
       [{ ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit") "unit",
          nfields := 0,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const
                       (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit")
                       [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                     { pw := ConLeche.PropWhen.never })
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.app
                       (ConLeche.Expr.bvar 0)
                       (ConLeche.Expr.const
                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit") "unit")
                         [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")]))
                     (ConLeche.Expr.bvar 0)
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false }]]
    0,
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "PProd",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "v"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")))
                     (ConLeche.Expr.sort
                       (ConLeche.Level.max
                         (ConLeche.Level.max
                           (ConLeche.Level.succ (ConLeche.Level.zero))
                           (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                         (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v"))))
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd") "mk",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "v"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.bvar 1)
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.bvar 1)
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app
                             (ConLeche.Expr.const
                               (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                               [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")])
                             (ConLeche.Expr.bvar 3))
                           (ConLeche.Expr.bvar 2))
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       2
       2,
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u_1",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "u",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "v"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")))
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app
                             (ConLeche.Expr.const
                               (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                               [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")])
                             (ConLeche.Expr.bvar 1))
                           (ConLeche.Expr.bvar 0))
                         (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 2)
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.bvar 2)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.bvar 2)
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.app
                                     (ConLeche.Expr.app
                                       (ConLeche.Expr.const
                                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd") "mk")
                                         [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                          ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")])
                                       (ConLeche.Expr.bvar 4))
                                     (ConLeche.Expr.bvar 3))
                                   (ConLeche.Expr.bvar 1))
                                 (ConLeche.Expr.bvar 0)))
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                                 [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                  ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")])
                               (ConLeche.Expr.bvar 3))
                             (ConLeche.Expr.bvar 2))
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       4
       4
       [{ ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd") "mk",
          nfields := 2,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")))
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app
                             (ConLeche.Expr.const
                               (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                               [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")])
                             (ConLeche.Expr.bvar 1))
                           (ConLeche.Expr.bvar 0))
                         (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.lam
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 2)
                           (ConLeche.Expr.forallE
                             (ConLeche.Expr.bvar 2)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.bvar 2)
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.app
                                     (ConLeche.Expr.app
                                       (ConLeche.Expr.const
                                         (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd") "mk")
                                         [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                                          ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "v")])
                                       (ConLeche.Expr.bvar 4))
                                     (ConLeche.Expr.bvar 3))
                                   (ConLeche.Expr.bvar 1))
                                 (ConLeche.Expr.bvar 0)))
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.lam
                           (ConLeche.Expr.bvar 3)
                           (ConLeche.Expr.lam
                             (ConLeche.Expr.bvar 3)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 1))
                               (ConLeche.Expr.bvar 0))
                             { pw := ConLeche.PropWhen.never })
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false }]]
    2,
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                  { pw := ConLeche.PropWhen.never })
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.sort
                    (ConLeche.Level.max
                      (ConLeche.Level.succ (ConLeche.Level.zero))
                      (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.forallE
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
        { pw := ConLeche.PropWhen.never })
      (ConLeche.Expr.lam
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.app
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.const
                  (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "rec")
                  [ConLeche.Level.succ
                     (ConLeche.Level.max
                       (ConLeche.Level.succ (ConLeche.Level.zero))
                       (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))])
                (ConLeche.Expr.lam
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.sort
                    (ConLeche.Level.max
                      (ConLeche.Level.succ (ConLeche.Level.zero))
                      (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                  { pw := ConLeche.PropWhen.never }))
              (ConLeche.Expr.const
                (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit")
                [ConLeche.Level.max
                   (ConLeche.Level.succ (ConLeche.Level.zero))
                   (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))]))
            (ConLeche.Expr.lam
              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
              (ConLeche.Expr.lam
                (ConLeche.Expr.sort
                  (ConLeche.Level.max
                    (ConLeche.Level.succ (ConLeche.Level.zero))
                    (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const
                      (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                      [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                       ConLeche.Level.max
                         (ConLeche.Level.succ (ConLeche.Level.zero))
                         (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])
                    (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 1)))
                  (ConLeche.Expr.bvar 0))
                { pw := ConLeche.PropWhen.never })
              { pw := ConLeche.PropWhen.never }))
          (ConLeche.Expr.bvar 0))
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.abbrev),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "brecOn") "go",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                  { pw := ConLeche.PropWhen.never })
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.const
                              (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                              [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                            (ConLeche.Expr.bvar 2))
                          (ConLeche.Expr.bvar 0))
                        (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 1))
                        { pw := ConLeche.PropWhen.never })
                      { pw := ConLeche.PropWhen.never })
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                          [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                           ConLeche.Level.max
                             (ConLeche.Level.succ (ConLeche.Level.zero))
                             (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])
                        (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 1)))
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.const
                            (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                            [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                          (ConLeche.Expr.bvar 2))
                        (ConLeche.Expr.bvar 1)))
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.forallE
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
        { pw := ConLeche.PropWhen.never })
      (ConLeche.Expr.lam
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.lam
          (ConLeche.Expr.forallE
            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
            (ConLeche.Expr.forallE
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.const
                    (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                    [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                  (ConLeche.Expr.bvar 2))
                (ConLeche.Expr.bvar 0))
              (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 1))
              { pw := ConLeche.PropWhen.never })
            { pw := ConLeche.PropWhen.never })
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.const
                    (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "rec")
                    [ConLeche.Level.max
                       (ConLeche.Level.succ (ConLeche.Level.zero))
                       (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])
                  (ConLeche.Expr.lam
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                          [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                           ConLeche.Level.max
                             (ConLeche.Level.succ (ConLeche.Level.zero))
                             (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])
                        (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 0)))
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.const
                            (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                            [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                          (ConLeche.Expr.bvar 3))
                        (ConLeche.Expr.bvar 0)))
                    { pw := ConLeche.PropWhen.never }))
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd") "mk")
                          [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                           ConLeche.Level.max
                             (ConLeche.Level.succ (ConLeche.Level.zero))
                             (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])
                        (ConLeche.Expr.app
                          (ConLeche.Expr.bvar 2)
                          (ConLeche.Expr.const
                            (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero")
                            [])))
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit")
                        [ConLeche.Level.max
                           (ConLeche.Level.succ (ConLeche.Level.zero))
                           (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))]))
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.bvar 0)
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero")
                          []))
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit") "unit")
                        [ConLeche.Level.max
                           (ConLeche.Level.succ (ConLeche.Level.zero))
                           (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])))
                  (ConLeche.Expr.const
                    (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PUnit") "unit")
                    [ConLeche.Level.max
                       (ConLeche.Level.succ (ConLeche.Level.zero))
                       (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])))
              (ConLeche.Expr.lam
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.lam
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                        [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                         ConLeche.Level.max
                           (ConLeche.Level.succ (ConLeche.Level.zero))
                           (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])
                      (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 0)))
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                          [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                        (ConLeche.Expr.bvar 3))
                      (ConLeche.Expr.bvar 0)))
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.const
                            (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd") "mk")
                            [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                             ConLeche.Level.max
                               (ConLeche.Level.succ (ConLeche.Level.zero))
                               (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])
                          (ConLeche.Expr.app
                            (ConLeche.Expr.bvar 4)
                            (ConLeche.Expr.app
                              (ConLeche.Expr.const
                                (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                                [])
                              (ConLeche.Expr.bvar 1))))
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.const
                              (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                              [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"),
                               ConLeche.Level.max
                                 (ConLeche.Level.succ (ConLeche.Level.zero))
                                 (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))])
                            (ConLeche.Expr.app (ConLeche.Expr.bvar 4) (ConLeche.Expr.bvar 1)))
                          (ConLeche.Expr.app
                            (ConLeche.Expr.app
                              (ConLeche.Expr.const
                                (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                                [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                              (ConLeche.Expr.bvar 4))
                            (ConLeche.Expr.bvar 1))))
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.bvar 2)
                          (ConLeche.Expr.app
                            (ConLeche.Expr.const
                              (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                              [])
                            (ConLeche.Expr.bvar 1)))
                        (ConLeche.Expr.bvar 0)))
                    (ConLeche.Expr.bvar 0))
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never }))
            (ConLeche.Expr.bvar 1))
          { pw := ConLeche.PropWhen.never })
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.abbrev),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "brecOn",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                  { pw := ConLeche.PropWhen.never })
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.const
                              (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                              [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                            (ConLeche.Expr.bvar 2))
                          (ConLeche.Expr.bvar 0))
                        (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 1))
                        { pw := ConLeche.PropWhen.never })
                      { pw := ConLeche.PropWhen.never })
                    (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 1))
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.forallE
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
        { pw := ConLeche.PropWhen.never })
      (ConLeche.Expr.lam
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.lam
          (ConLeche.Expr.forallE
            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
            (ConLeche.Expr.forallE
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.const
                    (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                    [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                  (ConLeche.Expr.bvar 2))
                (ConLeche.Expr.bvar 0))
              (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 1))
              { pw := ConLeche.PropWhen.never })
            { pw := ConLeche.PropWhen.never })
          (ConLeche.Expr.proj
            (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
            0
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.const
                    (ConLeche.Name.str
                      (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "brecOn")
                      "go")
                    [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                  (ConLeche.Expr.bvar 2))
                (ConLeche.Expr.bvar 1))
              (ConLeche.Expr.bvar 0)))
          { pw := ConLeche.PropWhen.never })
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.abbrev),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "casesOn",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                  { pw := ConLeche.PropWhen.never })
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.app
                      (ConLeche.Expr.bvar 1)
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero")
                        []))
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                        (ConLeche.Expr.app
                          (ConLeche.Expr.bvar 3)
                          (ConLeche.Expr.app
                            (ConLeche.Expr.const
                              (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                              [])
                            (ConLeche.Expr.bvar 0)))
                        { pw := ConLeche.PropWhen.never })
                      (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 2))
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.forallE
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
        { pw := ConLeche.PropWhen.never })
      (ConLeche.Expr.lam
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.lam
          (ConLeche.Expr.app
            (ConLeche.Expr.bvar 1)
            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero") []))
          (ConLeche.Expr.lam
            (ConLeche.Expr.forallE
              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
              (ConLeche.Expr.app
                (ConLeche.Expr.bvar 3)
                (ConLeche.Expr.app
                  (ConLeche.Expr.const
                    (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                    [])
                  (ConLeche.Expr.bvar 0)))
              { pw := ConLeche.PropWhen.never })
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const
                      (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "rec")
                      [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                    (ConLeche.Expr.bvar 3))
                  (ConLeche.Expr.bvar 1))
                (ConLeche.Expr.lam
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.lam
                    (ConLeche.Expr.app (ConLeche.Expr.bvar 4) (ConLeche.Expr.bvar 0))
                    (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 1))
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never }))
              (ConLeche.Expr.bvar 2))
            { pw := ConLeche.PropWhen.never })
          { pw := ConLeche.PropWhen.never })
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.abbrev),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "add") "match_1",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u_1"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                    (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                    (ConLeche.Expr.forallE
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 0))
                          (ConLeche.Expr.const
                            (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero")
                            []))
                        { pw := ConLeche.PropWhen.never })
                      (ConLeche.Expr.forallE
                        (ConLeche.Expr.forallE
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                          (ConLeche.Expr.forallE
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                            (ConLeche.Expr.app
                              (ConLeche.Expr.app (ConLeche.Expr.bvar 5) (ConLeche.Expr.bvar 1))
                              (ConLeche.Expr.app
                                (ConLeche.Expr.const
                                  (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                                  [])
                                (ConLeche.Expr.bvar 0)))
                            { pw := ConLeche.PropWhen.never })
                          { pw := ConLeche.PropWhen.never })
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app (ConLeche.Expr.bvar 4) (ConLeche.Expr.bvar 3))
                          (ConLeche.Expr.bvar 2))
                        { pw := ConLeche.PropWhen.never })
                      { pw := ConLeche.PropWhen.never })
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.forallE
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.forallE
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
          (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
          { pw := ConLeche.PropWhen.never })
        { pw := ConLeche.PropWhen.never })
      (ConLeche.Expr.lam
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.lam
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
          (ConLeche.Expr.lam
            (ConLeche.Expr.forallE
              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
              (ConLeche.Expr.app
                (ConLeche.Expr.app (ConLeche.Expr.bvar 3) (ConLeche.Expr.bvar 0))
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero") []))
              { pw := ConLeche.PropWhen.never })
            (ConLeche.Expr.lam
              (ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app (ConLeche.Expr.bvar 5) (ConLeche.Expr.bvar 1))
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                        [])
                      (ConLeche.Expr.bvar 0)))
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never })
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "casesOn")
                        [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")])
                      (ConLeche.Expr.lam
                        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app (ConLeche.Expr.bvar 5) (ConLeche.Expr.bvar 4))
                          (ConLeche.Expr.bvar 0))
                        { pw := ConLeche.PropWhen.never }))
                    (ConLeche.Expr.bvar 2))
                  (ConLeche.Expr.app (ConLeche.Expr.bvar 1) (ConLeche.Expr.bvar 3)))
                (ConLeche.Expr.lam
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app (ConLeche.Expr.bvar 1) (ConLeche.Expr.bvar 4))
                    (ConLeche.Expr.bvar 0))
                  { pw := ConLeche.PropWhen.never }))
              { pw := ConLeche.PropWhen.never })
            { pw := ConLeche.PropWhen.never })
          { pw := ConLeche.PropWhen.never })
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.abbrev),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "add") "_f",
      levelParams := [],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                        [ConLeche.Level.succ (ConLeche.Level.zero)])
                      (ConLeche.Expr.lam
                        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                        (ConLeche.Expr.forallE
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                          { pw := ConLeche.PropWhen.never })
                        { pw := ConLeche.PropWhen.never }))
                    (ConLeche.Expr.bvar 0))
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
      (ConLeche.Expr.lam
        (ConLeche.Expr.app
          (ConLeche.Expr.app
            (ConLeche.Expr.const
              (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
              [ConLeche.Level.succ (ConLeche.Level.zero)])
            (ConLeche.Expr.lam
              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
              (ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                { pw := ConLeche.PropWhen.never })
              { pw := ConLeche.PropWhen.never }))
          (ConLeche.Expr.bvar 0))
        (ConLeche.Expr.lam
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str
                          (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "add")
                          "match_1")
                        [ConLeche.Level.succ (ConLeche.Level.zero)])
                      (ConLeche.Expr.lam
                        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                        (ConLeche.Expr.lam
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                          (ConLeche.Expr.forallE
                            (ConLeche.Expr.app
                              (ConLeche.Expr.app
                                (ConLeche.Expr.const
                                  (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                                  [ConLeche.Level.succ (ConLeche.Level.zero)])
                                (ConLeche.Expr.lam
                                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                                  (ConLeche.Expr.forallE
                                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                                    { pw := ConLeche.PropWhen.never })
                                  { pw := ConLeche.PropWhen.never }))
                              (ConLeche.Expr.bvar 0))
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                            { pw := ConLeche.PropWhen.never })
                          { pw := ConLeche.PropWhen.never })
                        { pw := ConLeche.PropWhen.never }))
                    (ConLeche.Expr.bvar 0))
                  (ConLeche.Expr.bvar 2))
                (ConLeche.Expr.lam
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.lam
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                          [ConLeche.Level.succ (ConLeche.Level.zero)])
                        (ConLeche.Expr.lam
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                          (ConLeche.Expr.forallE
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                            { pw := ConLeche.PropWhen.never })
                          { pw := ConLeche.PropWhen.never }))
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "zero")
                        []))
                    (ConLeche.Expr.bvar 1)
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never }))
              (ConLeche.Expr.lam
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.lam
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.lam
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "below")
                          [ConLeche.Level.succ (ConLeche.Level.zero)])
                        (ConLeche.Expr.lam
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                          (ConLeche.Expr.forallE
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                            { pw := ConLeche.PropWhen.never })
                          { pw := ConLeche.PropWhen.never }))
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                          [])
                        (ConLeche.Expr.bvar 0)))
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                        [])
                      (ConLeche.Expr.app
                        (ConLeche.Expr.proj
                          (ConLeche.Name.str (ConLeche.Name.anonymous) "PProd")
                          0
                          (ConLeche.Expr.bvar 0))
                        (ConLeche.Expr.bvar 2)))
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never }))
            (ConLeche.Expr.bvar 1))
          { pw := ConLeche.PropWhen.never })
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.abbrev),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "add",
      levelParams := [],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
      (ConLeche.Expr.lam
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.app
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.const
                  (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "brecOn")
                  [ConLeche.Level.succ (ConLeche.Level.zero)])
                (ConLeche.Expr.lam
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never }))
              (ConLeche.Expr.bvar 0))
            (ConLeche.Expr.const
              (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "add") "_f")
              []))
          (ConLeche.Expr.bvar 1))
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.regular 1),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "instAddNat",
      levelParams := [],
      type := ConLeche.Expr.app
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") [ConLeche.Level.zero])
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []) }
    (ConLeche.Expr.app
      (ConLeche.Expr.app
        (ConLeche.Expr.const
          (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Add") "mk")
          [ConLeche.Level.zero])
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "add") []))
    (ConLeche.ReducibilityHint.regular 2),
  ConLeche.Declaration.indDecl
    [ConLeche.ConstantInfo.indInfo
       { name := ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                     (ConLeche.Expr.sort
                       (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       { eta := false,
         etaCtor := ConLeche.Name.anonymous,
         etaParams := 0,
         etaFields := 0,
         unitlike := false,
         unitParams := 0,
         ruleK := false,
         sortZ := ConLeche.PropWhen.ifAllZero [],
         all := [],
         nparams := 0,
         ctors := [] },
     ConLeche.ConstantInfo.ctorInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "mk",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.bvar 1)
                       (ConLeche.Expr.app
                         (ConLeche.Expr.app
                           (ConLeche.Expr.const
                             (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat")
                             [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                           (ConLeche.Expr.bvar 2))
                         (ConLeche.Expr.bvar 1))
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       2
       1,
     ConLeche.ConstantInfo.recInfo
       { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "rec",
         levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u_1",
                         ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
         type := ConLeche.Expr.forallE
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.forallE
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                     (ConLeche.Expr.forallE
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app
                             (ConLeche.Expr.const
                               (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat")
                               [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                             (ConLeche.Expr.bvar 1))
                           (ConLeche.Expr.bvar 0))
                         (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 2)
                           (ConLeche.Expr.app
                             (ConLeche.Expr.bvar 1)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.const
                                     (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "mk")
                                     [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                                   (ConLeche.Expr.bvar 3))
                                 (ConLeche.Expr.bvar 2))
                               (ConLeche.Expr.bvar 0)))
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.app
                             (ConLeche.Expr.app
                               (ConLeche.Expr.const
                                 (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat")
                                 [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                               (ConLeche.Expr.bvar 3))
                             (ConLeche.Expr.bvar 2))
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 2) (ConLeche.Expr.bvar 0))
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never } }
       4
       4
       [{ ctor := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "mk",
          nfields := 1,
          ctorParams := 0,
          fire := ConLeche.RecRuleFire.inert,
          rhs := ConLeche.Expr.lam
                   (ConLeche.Expr.sort
                     (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                   (ConLeche.Expr.lam
                     (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                     (ConLeche.Expr.lam
                       (ConLeche.Expr.forallE
                         (ConLeche.Expr.app
                           (ConLeche.Expr.app
                             (ConLeche.Expr.const
                               (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat")
                               [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                             (ConLeche.Expr.bvar 1))
                           (ConLeche.Expr.bvar 0))
                         (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u_1")))
                         { pw := ConLeche.PropWhen.never })
                       (ConLeche.Expr.lam
                         (ConLeche.Expr.forallE
                           (ConLeche.Expr.bvar 2)
                           (ConLeche.Expr.app
                             (ConLeche.Expr.bvar 1)
                             (ConLeche.Expr.app
                               (ConLeche.Expr.app
                                 (ConLeche.Expr.app
                                   (ConLeche.Expr.const
                                     (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "mk")
                                     [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                                   (ConLeche.Expr.bvar 3))
                                 (ConLeche.Expr.bvar 2))
                               (ConLeche.Expr.bvar 0)))
                           { pw := ConLeche.PropWhen.never })
                         (ConLeche.Expr.lam
                           (ConLeche.Expr.bvar 3)
                           (ConLeche.Expr.app (ConLeche.Expr.bvar 1) (ConLeche.Expr.bvar 0))
                           { pw := ConLeche.PropWhen.never })
                         { pw := ConLeche.PropWhen.never })
                       { pw := ConLeche.PropWhen.never })
                     { pw := ConLeche.PropWhen.never })
                   { pw := ConLeche.PropWhen.never },
          k := false,
          eta := false,
          paramsBlind := false }]]
    2,
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "ofNat",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort
                  (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                  (ConLeche.Expr.forallE
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat")
                          [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                        (ConLeche.Expr.bvar 1))
                      (ConLeche.Expr.bvar 0))
                    (ConLeche.Expr.bvar 2)
                    { pw := ConLeche.PropWhen.never })
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.sort
        (ConLeche.Level.succ (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u"))))
      (ConLeche.Expr.lam
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
        (ConLeche.Expr.lam
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.const
                (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat")
                [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
              (ConLeche.Expr.bvar 1))
            (ConLeche.Expr.bvar 0))
          (ConLeche.Expr.proj (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") 0 (ConLeche.Expr.bvar 0))
          { pw := ConLeche.PropWhen.never })
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.abbrev),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "instOfNatNat",
      levelParams := [],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") [ConLeche.Level.zero])
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                  (ConLeche.Expr.bvar 0))
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
      (ConLeche.Expr.app
        (ConLeche.Expr.app
          (ConLeche.Expr.app
            (ConLeche.Expr.const
              (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "mk")
              [ConLeche.Level.zero])
            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
          (ConLeche.Expr.bvar 0))
        (ConLeche.Expr.bvar 0))
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.regular 1),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "f",
      levelParams := [],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
      (ConLeche.Expr.app
        (ConLeche.Expr.app
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.const
                    (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "hAdd")
                    [ConLeche.Level.zero, ConLeche.Level.zero, ConLeche.Level.zero])
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instHAdd") [ConLeche.Level.zero])
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instAddNat") [])))
          (ConLeche.Expr.bvar 0))
        (ConLeche.Expr.app
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.const
                (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "ofNat")
                [ConLeche.Level.zero])
              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
            (ConLeche.Expr.lit (ConLeche.Literal.natVal 1)))
          (ConLeche.Expr.app
            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instOfNatNat") [])
            (ConLeche.Expr.lit (ConLeche.Literal.natVal 1)))))
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.regular 3),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "rfl",
      levelParams := [ConLeche.Name.str (ConLeche.Name.anonymous) "u"],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
                (ConLeche.Expr.forallE
                  (ConLeche.Expr.bvar 0)
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const
                          (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                          [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
                        (ConLeche.Expr.bvar 1))
                      (ConLeche.Expr.bvar 0))
                    (ConLeche.Expr.bvar 0))
                  { pw := ConLeche.PropWhen.never })
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.sort (ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")))
      (ConLeche.Expr.lam
        (ConLeche.Expr.bvar 0)
        (ConLeche.Expr.app
          (ConLeche.Expr.app
            (ConLeche.Expr.const
              (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq") "refl")
              [ConLeche.Level.param (ConLeche.Name.str (ConLeche.Name.anonymous) "u")])
            (ConLeche.Expr.bvar 1))
          (ConLeche.Expr.bvar 0))
        { pw := ConLeche.PropWhen.never })
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.regular 1),
  ConLeche.Declaration.thmDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "f_eq",
      levelParams := [],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                        [ConLeche.Level.succ (ConLeche.Level.zero)])
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "f") [])
                      (ConLeche.Expr.bvar 0)))
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const
                      (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                      [])
                    (ConLeche.Expr.bvar 0)))
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
      (ConLeche.Expr.app
        (ConLeche.Expr.app
          (ConLeche.Expr.const
            (ConLeche.Name.str (ConLeche.Name.anonymous) "rfl")
            [ConLeche.Level.succ (ConLeche.Level.zero)])
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
        (ConLeche.Expr.app
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "f") [])
          (ConLeche.Expr.bvar 0)))
      { pw := ConLeche.PropWhen.never }),
  ConLeche.Declaration.thmDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "f_body",
      levelParams := [],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                        [ConLeche.Level.succ (ConLeche.Level.zero)])
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "f") [])
                      (ConLeche.Expr.bvar 0)))
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.app
                              (ConLeche.Expr.const
                                (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "hAdd")
                                [ConLeche.Level.zero, ConLeche.Level.zero, ConLeche.Level.zero])
                              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.const
                              (ConLeche.Name.str (ConLeche.Name.anonymous) "instHAdd")
                              [ConLeche.Level.zero])
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instAddNat") [])))
                      (ConLeche.Expr.bvar 0))
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.const
                            (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "ofNat")
                            [ConLeche.Level.zero])
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                        (ConLeche.Expr.lit (ConLeche.Literal.natVal 1)))
                      (ConLeche.Expr.app
                        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instOfNatNat") [])
                        (ConLeche.Expr.lit (ConLeche.Literal.natVal 1))))))
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
      (ConLeche.Expr.app
        (ConLeche.Expr.app
          (ConLeche.Expr.const
            (ConLeche.Name.str (ConLeche.Name.anonymous) "rfl")
            [ConLeche.Level.succ (ConLeche.Level.zero)])
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
        (ConLeche.Expr.app
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "f") [])
          (ConLeche.Expr.bvar 0)))
      { pw := ConLeche.PropWhen.never }),
  ConLeche.Declaration.thmDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "add_one",
      levelParams := [],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                        [ConLeche.Level.succ (ConLeche.Level.zero)])
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                    (ConLeche.Expr.app
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.app
                              (ConLeche.Expr.app
                                (ConLeche.Expr.const
                                  (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "hAdd")
                                  [ConLeche.Level.zero, ConLeche.Level.zero, ConLeche.Level.zero])
                                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                          (ConLeche.Expr.app
                            (ConLeche.Expr.app
                              (ConLeche.Expr.const
                                (ConLeche.Name.str (ConLeche.Name.anonymous) "instHAdd")
                                [ConLeche.Level.zero])
                              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instAddNat") [])))
                        (ConLeche.Expr.bvar 0))
                      (ConLeche.Expr.app
                        (ConLeche.Expr.app
                          (ConLeche.Expr.app
                            (ConLeche.Expr.const
                              (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "ofNat")
                              [ConLeche.Level.zero])
                            (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                          (ConLeche.Expr.lit (ConLeche.Literal.natVal 1)))
                        (ConLeche.Expr.app
                          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instOfNatNat") [])
                          (ConLeche.Expr.lit (ConLeche.Literal.natVal 1))))))
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const
                      (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") "succ")
                      [])
                    (ConLeche.Expr.bvar 0)))
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
      (ConLeche.Expr.app
        (ConLeche.Expr.app
          (ConLeche.Expr.const
            (ConLeche.Name.str (ConLeche.Name.anonymous) "rfl")
            [ConLeche.Level.succ (ConLeche.Level.zero)])
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
        (ConLeche.Expr.app
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const
                      (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "HAdd") "hAdd")
                      [ConLeche.Level.zero, ConLeche.Level.zero, ConLeche.Level.zero])
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
              (ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instHAdd") [ConLeche.Level.zero])
                  (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instAddNat") [])))
            (ConLeche.Expr.bvar 0))
          (ConLeche.Expr.app
            (ConLeche.Expr.app
              (ConLeche.Expr.app
                (ConLeche.Expr.const
                  (ConLeche.Name.str (ConLeche.Name.str (ConLeche.Name.anonymous) "OfNat") "ofNat")
                  [ConLeche.Level.zero])
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
              (ConLeche.Expr.lit (ConLeche.Literal.natVal 1)))
            (ConLeche.Expr.app
              (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "instOfNatNat") [])
              (ConLeche.Expr.lit (ConLeche.Literal.natVal 1))))))
      { pw := ConLeche.PropWhen.never }),
  ConLeche.Declaration.thmDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "outParam_eq",
      levelParams := [],
      type := ConLeche.Expr.app
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const
                      (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                      [ConLeche.Level.succ (ConLeche.Level.succ (ConLeche.Level.succ (ConLeche.Level.zero)))])
                    (ConLeche.Expr.sort (ConLeche.Level.succ (ConLeche.Level.succ (ConLeche.Level.zero)))))
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const
                      (ConLeche.Name.str (ConLeche.Name.anonymous) "outParam")
                      [ConLeche.Level.succ (ConLeche.Level.succ (ConLeche.Level.zero))])
                    (ConLeche.Expr.sort (ConLeche.Level.succ (ConLeche.Level.zero)))))
                (ConLeche.Expr.sort (ConLeche.Level.succ (ConLeche.Level.zero))) }
    (ConLeche.Expr.app
      (ConLeche.Expr.app
        (ConLeche.Expr.const
          (ConLeche.Name.str (ConLeche.Name.anonymous) "rfl")
          [ConLeche.Level.succ (ConLeche.Level.succ (ConLeche.Level.succ (ConLeche.Level.zero)))])
        (ConLeche.Expr.sort (ConLeche.Level.succ (ConLeche.Level.succ (ConLeche.Level.zero)))))
      (ConLeche.Expr.app
        (ConLeche.Expr.const
          (ConLeche.Name.str (ConLeche.Name.anonymous) "outParam")
          [ConLeche.Level.succ (ConLeche.Level.succ (ConLeche.Level.zero))])
        (ConLeche.Expr.sort (ConLeche.Level.succ (ConLeche.Level.zero))))),
  ConLeche.Declaration.defnDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "g",
      levelParams := [],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
      (ConLeche.Expr.app
        (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "f") [])
        (ConLeche.Expr.app
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "f") [])
          (ConLeche.Expr.bvar 0)))
      { pw := ConLeche.PropWhen.never })
    (ConLeche.ReducibilityHint.regular 4),
  ConLeche.Declaration.thmDecl
    { name := ConLeche.Name.str (ConLeche.Name.anonymous) "g_eq",
      levelParams := [],
      type := ConLeche.Expr.forallE
                (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
                (ConLeche.Expr.app
                  (ConLeche.Expr.app
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const
                        (ConLeche.Name.str (ConLeche.Name.anonymous) "Eq")
                        [ConLeche.Level.succ (ConLeche.Level.zero)])
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "g") [])
                      (ConLeche.Expr.bvar 0)))
                  (ConLeche.Expr.app
                    (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "f") [])
                    (ConLeche.Expr.app
                      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "f") [])
                      (ConLeche.Expr.bvar 0))))
                { pw := ConLeche.PropWhen.never } }
    (ConLeche.Expr.lam
      (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") [])
      (ConLeche.Expr.app
        (ConLeche.Expr.app
          (ConLeche.Expr.const
            (ConLeche.Name.str (ConLeche.Name.anonymous) "rfl")
            [ConLeche.Level.succ (ConLeche.Level.zero)])
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "Nat") []))
        (ConLeche.Expr.app
          (ConLeche.Expr.const (ConLeche.Name.str (ConLeche.Name.anonymous) "g") [])
          (ConLeche.Expr.bvar 0)))
      { pw := ConLeche.PropWhen.never })]