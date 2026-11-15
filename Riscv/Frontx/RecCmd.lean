/- `frontx_rec f [from eq] measure μ`: a non-tail recursive function compiled with REAL calls (`Compiler/Rec.lean`).

The equation `f [B] xs = body` (unfolding equation, or `from eq`) must be an `if`/`dite` tree whose leaves contain
either no recursive call or all the calls `f [B] cⱼ` (`j < m`; each argument a term in the parameters; the byte
array `B`, if any, passed unchanged).  Generated, all proved automatically:

* the pieces (non-recursive definitions, compiled by `frontx_compile`'s translator with their variables from `S`
  on): `f.rec.go [B] xs : Bool` (the leaf makes the calls), `f.rec.a{j}_{k} [B] xs` (component `k` of call `j`'s
  argument), `f.rec.comb [B] xs r₀ … r_{m-1}` (the body, calls replaced by the `r`s; `Nat` `r`s unbounded);
* `f.rec.combEq : f [B] xs = comb [B] xs (if go [B] xs then f [B] c₀ else 0) …`;
* `f.rec.L`, `f.rec.GO`, `f.rec.ARG`, `f.rec.COMB` (the pieces as `Mach.BStmt`s, with copies in), `f.rec.mu`,
  and the hypotheses of `rec_ok`: `f.rec.goSpec`, `f.rec.argSpec`, `f.rec.combSpec`, `f.rec.dec`.

`frontx_rec_entry g [from eq]` for `g xs := f [xs] a₁ … aₚ` (`aᵢ` a closed `Nat` or `xs.size`): the program
`g.P = [f's function, main]`, `g.callOk` (from `rec_ok`; stack need `8 (N + 1) (|xs| + 1)`: needs
`μ (entry arguments) ≤ |xs|`), `g.wf`, `g.code` and the machine theorem `g.implements1`.

The generated statements and tactic scripts are built as text and parsed. -/
import Riscv.Frontx.Translate
import Riscv.Frontx.Rec

namespace Proven.Frontx
open Lean Meta Elab Term Command Tactic

/-- the recursive calls `f …` (full applications) in `e`, in order, without repetitions -/
partial def collectCalls (fn : Name) (n : Nat) (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.getAppFn.isConstOf fn && e.getAppNumArgs == n then (if acc.contains e then acc else acc.push e)
  else match e with
    | .app f a => collectCalls fn n a (collectCalls fn n f acc)
    | .lam _ t b _ | .forallE _ t b _ => collectCalls fn n b (collectCalls fn n t acc)
    | .letE _ t v b _ => collectCalls fn n b (collectCalls fn n v (collectCalls fn n t acc))
    | .mdata _ b => collectCalls fn n b acc
    | .proj _ _ b => collectCalls fn n b acc
    | _ => acc

/-- `go`: the `if`/`dite` tree of `e`, each leaf replaced by `true` (it has all the calls) or `false` (none) -/
partial def goOf (fn : Name) (n : Nat) (calls : Array Expr) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  let has (x : Expr) := (x.find? fun s => s.getAppFn.isConstOf fn).isSome
  if (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && !has (e.getArg! 1) then
    let a := e.getAppArgs
    let br (l : Expr) : MetaM Expr := do
      if e.isAppOfArity ``ite 5 then goOf fn n calls l
      else
        let l ← if l.isLambda then pure l else etaExpand l
        lambdaTelescope l fun hs b => do mkLambdaFVars hs (← goOf fn n calls b)
    let c := if e.isAppOfArity ``ite 5 then ``ite else ``dite
    return mkAppN (Lean.mkConst c [1]) #[mkConst ``Bool, a[1]!, a[2]!, ← br a[3]!, ← br a[4]!]
  let here := collectCalls fn n e #[]
  if here.isEmpty then return Lean.mkConst ``Bool.false
  unless here.size == calls.size && calls.all here.contains do
    throwError "frontx_rec: a leaf has some but not all of the recursive calls{indentExpr e}"
  return Lean.mkConst ``Bool.true

/-- the syntax with every source position replaced by `ref`'s (synthetic) -/
partial def reposition (ref : Syntax) : Syntax → Syntax
  | .node _ k args => .node (SourceInfo.fromRef ref) k (args.map (reposition ref))
  | .atom _ v => .atom (SourceInfo.fromRef ref) v
  | .ident _ r v pre => .ident (SourceInfo.fromRef ref) r v pre
  | .missing => .missing

def parseAs (cat : Name) (s : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) cat s with
  | .ok stx => return reposition (← getRef) stx
  | .error err => throwError "frontx_rec: generated text does not parse ({err}):\n{s}"

def elabProp (s : String) : TermElabM Expr := do
  let e ← elabTerm (← parseAs `term s) (some (mkSort 0))
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "frontx_rec: statement has metavariables:\n{s}"
  return e

def elabOf (s : String) (ty : Expr) : TermElabM Expr := do
  let e ← elabTerm (← parseAs `term s) (some ty)
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

def thmS (name : Name) (ty tac : String) : TermElabM Unit := do
  addThm name (← elabProp ty) ⟨← parseAs `tactic tac⟩

def sep (xs : List String) (s : String) : String := s.intercalate xs
def tupleTy (ts : List String) : String := " × ".intercalate (ts.map (s!"({·})"))
/-- the components of `a : t₁ × t₂ × …` -/
def projsOf (p : Nat) (a : String) : List String :=
  if p == 1 then [a] else (List.range p).map fun k => if k + 1 == p then a ++ String.join (List.replicate k ".2")
    else a ++ String.join (List.replicate k ".2") ++ ".1"
/-- an `rcases` pattern for the tuple -/
def tupPat (xs : List String) : String := match xs with
  | [x] => x
  | _ => xs.foldr (fun x acc => if acc == "" then x else s!"⟨{x}, {acc}⟩") ""
def orAlts (v : String) (n : Nat) : String := sep ((List.range n).map (s!"{v} = {·}")) " ∨ "
def rflPat (n : Nat) : String := sep (List.replicate n "rfl") " | "

def tyRepName : Ty → String
  | .bv => "id" | .u8 => "Proven.Frontx.r8" | .u32 => "Proven.Frontx.r32" | .u64 => "Proven.Frontx.r64"
  | .nat => "Proven.Frontx.rN" | .bool => "Proven.Frontx.rB"

syntax "frontx_rec " ident (" from " ident)? " measure " term : command
elab_rules : command
  | `(frontx_rec $f:ident $[from $e?]? measure $μ:term) => liftTermElabM do
  let t0 ← IO.monoMsNow
  let fn ← realizeGlobalConstNoOverloadWithInfo f
  let info ← getConstInfo fn
  let (eqN, eqTy) ← match e? with
    | some e => do let n ← realizeGlobalConstNoOverloadWithInfo e; pure (n, (← getConstInfo n).type)
    | none => do
      let some eqn ← getUnfoldEqnFor? fn (nonRec := true) | throwError "frontx_rec: no unfolding equation for {fn}"
      pure (eqn, (← getConstInfo eqn).type)
  let R := fn ++ `rec
  -- the measure, as a definition
  let μTy ← forallTelescope info.type fun xs _ => mkForallFVars xs (Lean.mkConst ``Nat)
  let μE ← elabTerm μ (some μTy)
  synthesizeSyntheticMVarsNoPostponing
  let μE ← instantiateMVars μE
  addDef (R ++ `mu) (← inferType μE) μE
  let (hasB, p, m, rty, tys, pieceNs, slotsMax) ← forallTelescope info.type fun xs resTy => do
    let some rty ← classify resTy | throwError "frontx_rec: unsupported result type{indentExpr resTy}"
    if rty == .bool then throwError "frontx_rec: a Bool result is not supported"
    let hasB ← if xs.size > 0 then pure ((← whnfR (← inferType xs[0]!)).isConstOf ``ByteArray) else pure false
    let bs := if hasB then #[xs[0]!] else #[]
    let sc := if hasB then xs.extract 1 xs.size else xs
    let mut tys := #[]
    for x in sc do
      let some t ← classify (← inferType x) | throwError "frontx_rec: unsupported parameter{indentExpr x}"
      tys := tys.push (t, toString (← ppExpr (← inferType x)))
    let p := sc.size
    let some (_, _, body) := (← instantiateForall eqTy xs).eq? | throwError "frontx_rec: bad equation"
    let calls := collectCalls fn xs.size body #[]
    if calls.isEmpty then throwError "frontx_rec: no recursive call"
    for c in calls do
      if c.hasLooseBVars then throwError "frontx_rec: a call argument depends on a bound variable{indentExpr c}"
      if hasB && c.getArg! 0 != xs[0]! then throwError "frontx_rec: the byte array must be passed unchanged{indentExpr c}"
    let m := calls.size
    let S := 8 + 2 * p + m
    let goB ← goOf fn xs.size calls body
    addDef (R ++ `go) (← mkForallFVars xs (Lean.mkConst ``Bool)) (← mkLambdaFVars xs goB)
    let mut pieceNs := #[R ++ `go]
    for j in [0:m] do
      for k in [0:p] do
        let a := calls[j]!.getArg! (k + bs.size)
        let n := R ++ Name.mkSimple s!"a{j}_{k}"
        addDef n (← mkForallFVars xs (← inferType a)) (← mkLambdaFVars xs a)
        pieceNs := pieceNs.push n
    let rDecls := (List.range m).toArray.map fun j => (Name.mkSimple s!"r{j}", fun _ => pure resTy)
    withLocalDeclsD rDecls fun rs => do
      let cb := body.replace fun s => (calls.idxOf? s).map (rs[·]!)
      if (cb.find? (·.isConstOf fn)).isSome then throwError "frontx_rec: a recursive call is left in{indentExpr cb}"
      addDef (R ++ `comb) (← mkForallFVars (xs ++ rs) resTy) (← mkLambdaFVars (xs ++ rs) cb)
    pieceNs := pieceNs.push (R ++ `comb)
    for n in pieceNs do
      let nb := if n == R ++ `comb then (List.range m).toArray.map (xs.size + ·) else #[]
      compileCmd (mkIdent n) none (start := S) (noBound := nb)
    let mut slotsMax := 0
    for n in pieceNs do
      let some v := (← getConstInfo (n ++ `slots)).value? | throwError "frontx_rec: no slots"
      let some k := (← whnf v).rawNatLit? <|> (← whnf v).nat? | throwError "frontx_rec: slots{indentExpr v}"
      slotsMax := max slotsMax k
    return (hasB, p, m, rty, tys, pieceNs, slotsMax)
  let S := 8 + 2 * p + m
  let N := max slotsMax (S - 8 + 1)
  if N > 16 then throwError "frontx_rec: {N} locals (at most 16)"
  -- names and text pieces
  let nm (n : Name) : String := toString n
  let fS := nm fn
  let Rn (s : String) : String := nm (R ++ Name.mkSimple s)
  let argN (j k : Nat) : String := Rn s!"a{j}_{k}"
  let bS := if hasB then " B" else ""
  let bBind := if hasB then " (B : ByteArray)" else ""
  let bIntro := if hasB then " B" else ""
  let xs := (List.range p).map (s!"x{·}")
  let xsS := String.join (xs.map (" " ++ ·))
  let αS := tupleTy (tys.toList.map (·.2))
  let reps := tys.toList.map (tyRepName ·.1)
  let resRep := tyRepName rty
  let valsOf (ps : List String) : String := "[" ++ sep ((reps.zip ps).map fun (r, x) => s!"{r} ({x})") ", " ++ "]"
  let okOf (ps : List String) : String :=
    let cs := (if hasB then ["B.size < 2 ^ 64"] else []) ++
      ((tys.toList.zip ps).filterMap fun ((t, _), x) => if t == .nat then some s!"({x}) < 2 ^ 64" else none)
    if cs.isEmpty then "True" else sep cs " ∧ "
  let app (fnS : String) (ps : List String) : String := s!"{fnS}{bS}" ++ String.join (ps.map (s!" ({·})"))
  let callTup (j : Nat) (ps : List String) : String :=
    let cs := (List.range p).map fun k => app (argN j k) ps
    if p == 1 then cs.head! else "(" ++ sep cs ", " ++ ")"
  let csOf (ps : List String) : String :=
    let cs := (List.range m).map fun j => callTup j ps
    s!"(fun j => List.getD [{sep cs ", "}] j ({cs.head!}))"
  let pa := projsOf p "a"
  let pat := tupPat xs
  let SL := toString S
  let argIs := (List.range m).foldl (fun acc j => acc ++ (List.range p).map (argN j)) []
  -- `combEq`
  let rsTerms := (List.range m).map fun j =>
    s!"(if {app (Rn "go") xs} then {app fS ((List.range p).map fun k => app (argN j k) xs)} else 0)"
  thmS (R ++ `combEq)
    s!"∀{bBind}{String.join ((xs.zip (tys.toList.map (·.2))).map fun (x, t) => s!" ({x} : {t})")}, {app fS xs} = {app (Rn "comb") xs} {sep rsTerms " "}"
    s!"(
  intro{bIntro}{xsS}
  rw [{nm eqN}{bS}{xsS}]
  unfold {sep ([Rn "comb", Rn "go"] ++ argIs) " "}
  split <;> simp_all)"
  -- the pieces as statements
  let copies (n : Nat) (src : Nat) : List String := (List.range n).map fun k => s!"({S + (src - 8) + k}, Proven.BExp.var {src + k})"
  let copiesP := copies p 8
  let copiesR := (List.range m).map fun j => s!"({S + p + j}, Proven.BExp.var {8 + p + j})"
  let stmtOf (n : String) (cp : List String) : String :=
    s!"Proven.Mach.Riscv.toMS (Proven.Frontx.initS [{sep cp ", "}] (Proven.Frontx.prog {n}.lay {n}.tree {SL}))"
  let mstmt := Lean.mkConst ``Mach.BStmt
  addDef (R ++ `L) (Lean.mkConst ``Mach.RecLay) (mkAppN (Lean.mkConst ``Mach.RecLay.mk) #[toExpr p, toExpr m, toExpr N, toExpr S])
    (compile := true)
  addDef (R ++ `GO) mstmt (← elabOf (stmtOf (Rn "go") copiesP) mstmt) (compile := true)
  addDef (R ++ `COMB) mstmt (← elabOf (stmtOf (Rn "comb") (copiesP ++ copiesR)) mstmt) (compile := true)
  let rows := (List.range m).map fun j => "[" ++ sep ((List.range p).map fun k => stmtOf (argN j k) copiesP) ", " ++ "]"
  let argTy ← mkArrow (Lean.mkConst ``Nat) (← mkArrow (Lean.mkConst ``Nat) mstmt)
  addDef (R ++ `ARG) argTy (← elabOf s!"fun j k => List.getD (List.getD [{sep rows ", "}] j []) k (Proven.Mach.bskip {SL})" argTy) (compile := true)
  -- the specs: heap `H0 ++ X` (`H0 = [blk B]` or `[]`), word heap `[]`, globals `g`
  let H0 := if hasB then "[Proven.Frontx.blk B]" else "([] : Proven.Heap)"
  let hgB := if hasB then "(hg : g 1 = Proven.Frontx.rN B.size)" else "(hg : True)"
  let repTac (n : String) (withR : Bool) : String :=
    let hs := (List.range p).map fun k => s!"have e{k} := hE.2 {k} (by decide)"
    let rs := if withR then (List.range m).map fun j => s!"have q{j} := hr {j} (by decide)" else []
    let all := (List.range p).map (s!"e{·}") ++ (if withR then (List.range m).map (s!"q{·}") else [])
    let lems := sep (["Proven.Frontx.seqSet", "Proven.BEnv.set", "Proven.BExp.denote", "e1", "hg"] ++ all ++ argIs) ", "
    "(" ++ sep ([s!"unfold {n}.Rep", "have e1 := hE.1 1 (by decide)"] ++ hs ++ rs ++
      [s!"try simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.reduceAdd, Proven.Mach.RecLay.rv, {Rn "L"}] at {sep all " "}",
       s!"and_intros <;> first | rfl | omega | (simp [{lems}]; done) | (simp [{lems}] <;> split <;> rfl)"]) "; " ++ ")"
  let liftS (n : String) (cp : List String) (nr : Nat) (withR : Bool) : String :=
    s!"Proven.Frontx.piece_lift (l := [{sep cp ", "}]) (E := E) (H0 := {H0}) (X := X) (W := []) (S := {SL}) (by decide) ({n}.exec{bS}{xsS}{String.join (List.replicate nr " _")} _ (by {repTac n withR}))"
  let hyps (extra : String) : String :=
    s!"∀{bBind} (X : Proven.Heap) (g : Proven.Mach.BEnv) {hgB} (a : {αS}) (E : Proven.Mach.BEnv), {okOf pa} → {extra}Proven.Mach.Hold {p} g E {valsOf pa} →"
  let st (s : String) := s!"Proven.Mach.BExec {s} ⟨E, {H0} ++ X, []⟩ ⟨E', {H0} ++ X, []⟩"
  thmS (R ++ `goSpec)
    s!"{hyps ""} ∃ E', {st (Rn "GO")} ∧ (E' {SL} ≠ 0 ↔ {app (Rn "go") pa} = true) ∧ ∀ v, v < {SL} → E' v = E v"
    s!"(
  rintro{bIntro} X g hg {pat} E hok hE
  obtain ⟨E', h1, h2, h3⟩ := {liftS (Rn "go") copiesP 0 false}
  exact ⟨E', h1, by rw [h2]; exact Proven.Frontx.rB_ne _, h3⟩)"
  let alts := (List.range m).foldl (fun acc j => acc ++ (List.range p).map fun k =>
    s!"(exact {liftS (argN j k) copiesP 0 false})") []
  thmS (R ++ `argSpec)
    s!"∀{bBind} (X : Proven.Heap) (g : Proven.Mach.BEnv) {hgB} (j k : Nat), j < {m} → k < {p} → ∀ (a : {αS}) (E : Proven.Mach.BEnv), {okOf pa} → {app (Rn "go") pa} = true → Proven.Mach.Hold {p} g E {valsOf pa} → ∃ E', {st s!"({Rn "ARG"} j k)"} ∧ E' {SL} = List.getD ((fun a : {αS} => {valsOf pa}) ({csOf pa} j)) k 0 ∧ ∀ v, v < {SL} → E' v = E v"
    s!"(
  rintro{bIntro} X g hg j k hj hk {pat} E hok hgo hE
  rcases (show {orAlts "j" m} by omega) with {rflPat m} <;>
  rcases (show {orAlts "k" p} by omega) with {rflPat p} <;>
  first {String.join (alts.map (s!"\n    | " ++ ·))})"
  let resOf (ps : List String) : String := s!"{resRep} ({app fS ps})"
  thmS (R ++ `combSpec)
    s!"{hyps ""} (∀ j, j < {m} → E (Proven.Mach.RecLay.rv {Rn "L"} j) = if {app (Rn "go") pa} then (fun a : {αS} => {resOf pa}) ({csOf pa} j) else 0) → ∃ E', {st (Rn "COMB")} ∧ E' {SL} = {resOf pa} ∧ ∀ v, v < {SL} → E' v = E v"
    s!"(
  rintro{bIntro} X g hg {pat} E hok hE hr
  rw [{Rn "combEq"}]
  exact {liftS (Rn "comb") (copiesP ++ copiesR) m true})"
  let μa := app (Rn "mu") pa
  thmS (R ++ `dec)
    s!"∀{bBind} (a : {αS}), {okOf pa} → {app (Rn "go") pa} = true → ∀ j, j < {m} → (fun a : {αS} => {okOf pa}) ({csOf pa} j) ∧ (fun a : {αS} => {μa}) ({csOf pa} j) < {μa}"
    s!"(
  rintro{bIntro} {pat} hok hgo j hj
  rcases (show {orAlts "j" m} by omega) with {rflPat m} <;>
  simp_all [{sep ([Rn "go", Rn "mu"] ++ argIs) ", "}] <;> omega)"
  logInfo m!"frontx_rec: {fn}: {m} call(s), {p} parameter(s), {N} locals, pieces from variable {S}; {(← IO.monoMsNow) - t0} ms"

/-- the natural number literal a definition reduces to -/
def natOf (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e.rawNatLit? <|> e.nat? with
  | some n => return n
  | none => throwError "frontx_rec_entry: not a numeral{indentExpr e}"

syntax "frontx_rec_entry " ident (" from " ident)? : command
elab_rules : command
  | `(frontx_rec_entry $g:ident $[from $e?]?) => liftTermElabM do
  let gN ← realizeGlobalConstNoOverloadWithInfo g
  let info ← getConstInfoDefn gN
  let eqN? ← e?.mapM fun e => realizeGlobalConstNoOverloadWithInfo e
  let val ← match eqN? with
    | none => pure info.value
    | some eqN => forallTelescope (← getConstInfo eqN).type fun xs ty => do
        let some (_, _, rhs) := ty.eq? | throwError "frontx_rec_entry: `from` needs an equation"
        mkLambdaFVars xs rhs
  let (fN, hasB, argsS, a0S, βS, k) ← lambdaTelescope val fun xs body => do
    unless xs.size == 1 && (← whnfR (← inferType xs[0]!)).isConstOf ``ByteArray do
      throwError "frontx_rec_entry: expected one ByteArray parameter"
    let .const fN _ := body.getAppFn | throwError "frontx_rec_entry: the body must apply a `frontx_rec` function"
    unless (← getEnv).contains (fN ++ `rec ++ `L) do throwError "frontx_rec_entry: {fN} was not compiled by frontx_rec"
    let args := body.getAppArgs
    let hasB := args.size > 0 && args[0]! == xs[0]!
    let mut argsS := #[]
    let mut a0S := #[]
    for a in (if hasB then args.extract 1 args.size else args) do
      let some ty ← classify (← inferType a) | throwError "frontx_rec_entry: unsupported argument{indentExpr a}"
      if a.isAppOfArity ``ByteArray.size 1 && a.appArg! == xs[0]! then
        argsS := argsS.push "Proven.Mach.BExp.var 1"
        a0S := a0S.push "xs.size"
      else
        if a.hasFVar then throwError "frontx_rec_entry: argument is neither closed nor `xs.size`{indentExpr a}"
        let aS := toString (← ppExpr a)
        argsS := argsS.push s!"Proven.Mach.BExp.const ({tyRepName ty} ({aS}))"
        a0S := a0S.push s!"({aS})"
    let β ← inferType body
    let k ← natOf (← elabOf s!"(Proven.Frontx.Res.k ({← ppExpr β}) : Nat)" (Lean.mkConst ``Nat))
    return (fN, hasB, argsS, a0S, toString (← ppExpr β), k)
  let R := fN ++ `rec
  let nm (n : Name) : String := toString n
  let Rn (s : String) : String := nm (R ++ Name.mkSimple s)
  let some Lv := (← getConstInfo (R ++ `L)).value? | throwError "frontx_rec_entry: no layout"
  let La := Lv.getAppArgs
  let (p, m, N) := (← natOf La[0]!, ← natOf La[1]!, ← natOf La[2]!)
  let fr := 8 * (N + 1)
  let gS := nm gN
  let PS := nm (gN ++ `P)
  let F := s!"(Proven.Mach.recFn {Rn "L"} 0 {Rn "GO"} {Rn "ARG"} {Rn "COMB"})"
  let argsL := "[" ++ ", ".intercalate argsS.toList ++ "]"
  addDef (gN ++ `P) (Lean.mkConst ``Mach.Prog)
    (← elabOf s!"[{F}, Proven.Frontx.recMain 0 {argsL} {k}]" (Lean.mkConst ``Mach.Prog)) (compile := true)
  -- the call, from `rec_ok`
  let tys ← forallTelescope (← getConstInfo fN).type fun xs _ => do
    (if hasB then xs.extract 1 xs.size else xs).mapM fun x => do
      let t ← inferType x
      return ((← classify t).get!, toString (← ppExpr t))
  let αS := tupleTy (tys.toList.map (·.2))
  let pa := projsOf p "a"
  let reps := tys.toList.map (tyRepName ·.1)
  let bS := if hasB then " xs" else ""
  let app (fnS : String) (ps : List String) : String := s!"{fnS}{bS}" ++ String.join (ps.map (s!" ({·})"))
  let valsS := s!"(fun a : {αS} => [" ++ ", ".intercalate ((reps.zip pa).map fun (r, x) => s!"{r} ({x})") ++ "])"
  let okList := (if hasB then ["xs.size < 2 ^ 64"] else []) ++
      ((tys.toList.zip pa).filterMap fun ((t, _), x) => if t == .nat then some s!"({x}) < 2 ^ 64" else none)
  let okS := s!"(fun a : {αS} => {if okList.isEmpty then "True" else " ∧ ".intercalate okList})"
  let argN (j kk : Nat) : String := Rn s!"a{j}_{kk}"
  let callTup (j : Nat) : String :=
    let cs := (List.range p).map fun kk => app (argN j kk) pa
    if p == 1 then cs.head! else "(" ++ ", ".intercalate cs ++ ")"
  let csL := (List.range m).map callTup
  let csS := s!"(fun (a : {αS}) (j : Nat) => List.getD [{", ".intercalate csL}] j ({csL.head!}))"
  let rty ← forallTelescope (← getConstInfo fN).type fun _ r => do return (← classify r).get!
  let resS := s!"(fun a : {αS} => {tyRepName rty} ({app (nm fN) pa}))"
  let a0 := if p == 1 then a0S[0]! else "(" ++ ", ".intercalate a0S.toList ++ ")"
  let specArgs := if hasB then " xs [out] env h1" else " [Proven.Frontx.blk xs, out] env trivial"
  let decArgs := if hasB then " xs" else ""
  let H := if hasB then "([Proven.Frontx.blk xs] ++ [out])" else "(([] : Proven.Heap) ++ [Proven.Frontx.blk xs, out])"
  let needS := s!"{fr} * (xs.size + 1)"
  let unf := match eqN? with
    | some eqN => s!"rw [{nm eqN} xs]"
    | none => s!"unfold {gS}"
  thmS (gN ++ `callOk)
    s!"∀ (xs : ByteArray) (out : List (BitVec 8)) (env : Proven.Mach.BEnv), env 1 = Proven.Frontx.rN xs.size → xs.size < 2 ^ 32 → Proven.Mach.CExec {PS} ({needS}) (.call 4 0 {argsL}) ⟨env, [Proven.Frontx.blk xs, out], []⟩ ⟨env.set 4 (Proven.Frontx.Res.repr ({gS} xs)), [Proven.Frontx.blk xs, out], []⟩"
    s!"(
  intro xs out env h1 hs
  {unf}
  have hc := Proven.Mach.rec_ok {PS} 0 {Rn "L"} {Rn "GO"} {Rn "COMB"} {Rn "ARG"} (by decide) rfl (by decide) {H} [] env {valsS} {okS} (fun a : {αS} => {app (Rn "go") pa}) {csS} (fun a : {αS} => {app (Rn "mu") pa}) {resS} (fun _ => rfl) ({Rn "dec"}{decArgs}) ({Rn "goSpec"}{specArgs}) ({Rn "argSpec"}{specArgs}) ({Rn "combSpec"}{specArgs}) {a0} (by first | omega | (dsimp only; omega) | (simp; omega) | simp) ⟨env, [Proven.Frontx.blk xs, out], []⟩ {argsL} 4 (fun _ _ => rfl) rfl rfl (by simp [Proven.Mach.BExp.denote, h1, Proven.Frontx.rN])
  exact hc.mono (Nat.mul_le_mul (Nat.le_of_eq rfl) (by first | (simp [{Rn "mu"}]; done) | (simp [{Rn "mu"}]; omega))))"
  -- well-formedness, code, machine theorem
  let pieces := #[R ++ `go, R ++ `comb] ++ ((List.range m).foldl (fun acc j =>
    acc ++ (List.range p).map fun kk => R ++ Name.mkSimple s!"a{j}_{kk}") []).toArray
  let defs := [PS, "Proven.Mach.recFn", "Proven.Mach.recBody", "Proven.Mach.callsC", "Proven.Mach.stage",
    "Proven.Mach.bskip", Rn "GO", Rn "ARG", Rn "COMB", Rn "L", "Proven.Frontx.recMain", "Proven.Mach.RecLay.rv",
    "Proven.Mach.RecLay.av", "Proven.Frontx.prog", "Proven.Frontx.comp", "Proven.Frontx.skip", "Proven.Frontx.tmps",
    "Proven.Frontx.copies", "Proven.Frontx.initS", "Proven.Mach.Riscv.toMS", "Proven.Mach.Riscv.toMB",
    "Proven.Frontx.Lay.res", "Proven.Frontx.Lay.fl", "Proven.Frontx.Lay.tmp", "Proven.Frontx.Lay.cv",
    "Proven.Mach.Riscv.store8", "Proven.Mach.Riscv.glF"] ++
    (pieces.toList.foldl (fun acc n => acc ++ [nm (n ++ `tree), nm (n ++ `lay)]) [])
  let wfT := s!"wf_calls [{", ".intercalate defs}]"
  thmS (gN ++ `wf) s!"Proven.Mach.Riscv.WfProg1 {PS} 4 1"
    s!"(
  refine ⟨fun f hf => ?_, ?_⟩
  · simp only [{PS}, List.length_cons, List.length_nil] at hf
    rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl
    · {wfT}
    · {wfT}
  · {wfT})"
  addDef (gN ++ `code) (← elabOf "List (BitVec 32)" (mkSort 1)) (← elabOf s!"Proven.Mach.Riscv.callsCode1 {PS} 4 1"
    (← elabOf "List (BitVec 32)" (mkSort 1))) (compile := true)
  let spaceS := s!"(fun n => {fr} * (n + 1) + 8 + 24)"
  thmS (gN ++ `implements1)
    s!"Proven.Implements1With (fun xs : ByteArray => xs.data.toList) Proven.Frontx.Res.enc {nm (gN ++ `code)} {gS} {spaceS}"
    s!"exact Proven.Frontx.implements1_rec {gS} {PS} 1 0 {argsL} (by decide) rfl {nm (gN ++ `wf)} (fun n => {fr} * (n + 1)) {nm (gN ++ `callOk)}"
  logInfo m!"frontx_rec_entry: {gN}: {βS} result, frame {fr} bytes, space {fr} (n + 1) + 32"

end Proven.Frontx
