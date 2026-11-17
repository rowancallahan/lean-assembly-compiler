/- `wp_compileS` (branch nano-closeB): `wp_compile` (`Riscv/Frontx/WpCmd.lean`, unchanged) with a different
UNTRUSTED register choice for programs with `mop`: first "every local in its stack slot" with the seven colouring
modes (`pickSpillW`, as nano-closeA's `pickSpill` for `frontx_implements_listCS`), then `pickC`'s full search.  The
generated theorems are the same (`goodE`, `pg`, `pgGood` with the same `decide +kernel` checks, `compiles`,
`computes`); only the choice that the kernel then checks differs. -/
import Riscv.Frontx.WpCmd

namespace Proven.WA
open Lean Meta Elab Term Command Proven.Mach Proven.Mach.Riscv

/-- (untrusted) every local spilled, the first colouring mode `optB` accepts; else `pickC` -/
def pickSpillW (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) (M : Nat := 4096) :
    Option (List (Nat × Reg) × List Nat) :=
  let spl := List.range N
  let r := [0, 1, 2, 3, 4, 5, 6].findSome? fun mode =>
    match colorB N bv wv p spl mode with
    | some g => let t := tabulate g M
      if (rvwF.optB scB (tblG t) (fun j => spl.contains j) N bv wv p).isSome then some (t, spl) else none
    | none => none
  match r with
  | some r => some r
  | none => pickC N bv wv p M

syntax "wp_compileS " ident (&" reflect_only")? " max " term (" invariant " term " measure " term)* : command

set_option hygiene false in
elab_rules : command
  | `(wp_compileS $f:ident $[reflect_only%$ro]? max $N:term $[invariant $Ps measure $μs]*) => do
    let fn ← liftCoreM <| realizeGlobalConstNoOverload f
    let (R, stages, ls, names, propLoops) ← liftTermElabM do
      waPagedRef.set true
      try
        let info ← getConstInfo fn
        let ba := Lean.mkConst ``ByteArray
        let R ← forallTelescope info.type fun xs b => do
          unless xs.size == 1 && (← isDefEq (← inferType xs[0]!) ba) do
            throwError "wp_compile: expected a function of one ByteArray"
          let some R ← slOf? b | throwError "wp_compile: unsupported result type {b}"
          return R
        let mut hints := #[]
        for (P, μ) in Ps.zip μs do
          let Pe ← instantiateMVars (← elabTerm P none); let μe ← instantiateMVars (← elabTerm μ none)
          synthesizeSyntheticMVarsNoPostponing
          hints := hints.push (← instantiateMVars Pe, ← instantiateMVars μe)
        waHintsRef.set hints
        let names ← IO.mkRef (#[] : Array Name)
        let loops ← IO.mkRef (#[] : Array LoopRec)
        let mut hoisted : Array Expr := #[]
        let mut res : Option (Term × Array LoopRec) := none
        for _ in [0:16] do
          names.set #[]; loops.set #[]
          match ← reifyEntry fn R hoisted names loops with
          | .inl k => hoisted := hoisted.push k
          | .inr p => res := some p; break
        let some (prog, ls) := res | throwError "wp_compile: too many hoisted arrays"
        let pty ← elabTerm (← `(Pg [Sl.ar AK.ba] $(← slSyn R))) none
        let progE ← elabTermEnsuringType prog pty
        synthesizeSyntheticMVarsNoPostponing
        addFn (fn ++ `wa) (← instantiateMVars progE)
        let mut propLoops : Array Bool := #[]
        for h : k in [0:ls.size] do
          let l := ls[k]
          addFn (fn ++ Name.mkSimple s!"g{k}") l.g
          addFn (fn ++ Name.mkSimple s!"P{k}") l.P
          addFn (fn ++ Name.mkSimple s!"μ{k}") l.μ
          propLoops := propLoops.push (l.g.find? (·.isConstOf ``dite)).isSome
        logInfo m!"wp_compile: {fn}: {hoisted.size} hoisted, {ls.size} loops, unfolded {← names.get}"
        waPagedRef.set false
        return (R, ← waStagesRef.get, ls, ← names.get, propLoops)
      catch e =>
        waPagedRef.set false
        throw e
    if ro.isSome then return
    let fI := mkIdent fn
    let wa := mkIdent (fn ++ `wa)
    let unf : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      (names.push fn).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    let xsI := mkIdent `xs
    let gsAll : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← (List.range ls.size).toArray.mapM fun k =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent (fn ++ Name.mkSimple s!"g{k}")):ident)
    -- the functions of the `++` / `push` loops unfold to `appendGo` / `pushGo` (and those to `++` / `push`)
    let gAuto : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← (ls.toList.zipIdx.filter fun (l, _) =>
        l.un == ``appendGo || l.un == ``pushGo).toArray.mapM fun (_, k) =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent (fn ++ Name.mkSimple s!"g{k}")):ident)
    let unf := unf ++ gAuto
    -- the proof of `GoodE`, stage by stage
    let rec good : List Stage → CommandElabM Term
      | [] => throwError "wp_compile: no result"
      | .retS :: _ => match R with
        | .sc _ => `(⟨by simp only [$unf,*, foldl_foldGo, ← getElem!_pos, dite_eq_ite]; wp_dsimp; try rfl, by wp_okt,
            rfl⟩)
        | .ar _ => `(⟨by simp only [$unf,*, foldl_foldGo]; wp_dsimp; (try rfl); (try (simp only [$gsAll,*]; wp_dif)), rfl⟩)
      | .letS :: rest => do `(⟨by (try simp only [$unf,*]); wp_okt, _, $(← good rest), rfl⟩)
      | .loopS k _ :: rest => do
        let l := ls[k]!
        let g := mkIdent (fn ++ Name.mkSimple s!"g{k}")
        let P := mkIdent (fn ++ Name.mkSimple s!"P{k}")
        let μ := mkIdent (fn ++ Name.mkSimple s!"μ{k}")
        let st ← liftTermElabM (introState l.Δ #[mkIdent `hP])
        let st2 ← liftTermElabM (introState l.Δ #[mkIdent `s', mkIdent `hP, mkIdent `h])
        let st3 ← liftTermElabM (introState l.Δ #[mkIdent `hP])
        let okall ← `(tactic| ($(← liftMacroM (seqT st)); simp only [$P:ident] at hP; (try simp only [$unf,*] at *); wp_dsimp; wp_close))
        let step ← `(tactic| ($(← liftMacroM (seqT st2)); wp_step $P $μ))
        let unI := mkIdent l.un
        let simpG ← `(tactic| simp only [$g:ident, $unf,*, $gsAll,*, Nat.toUInt32, ← getElem!_pos, dite_eq_ite, decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq, bne_iff_ne])
        let heq ← if propLoops[k]! then
            `(tactic| ($(← liftMacroM (seqT st3)); simp only [$P:ident] at hP; simp only [$g:ident]; wp_dif; rw [$unI:ident]; wp_dsimp; $simpG:tactic; wp_dif))
          else
            `(tactic| ($(← liftMacroM (seqT st3)); simp only [$g:ident]; rw [$unI:ident]; wp_dsimp; $simpG:tactic))
        let p0 ← `(tactic| (simp only [$P:ident]; (try simp only [$unf,*]); wp_dsimp; wp_close))
        let sq (t : TSyntax `tactic) : CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) :=
          `(Lean.Parser.Tactic.tacticSeq| $t:tactic)
        `(⟨by (try simp only [$unf,*]); wp_okt, _, $P $xsI, _, _, by $(← sq p0), by $(← sq okall), by $(← sq step),
            (runsE_of (runs_of _ _ ($g $xsI) ($P $xsI) ($μ $xsI) (by $(← sq heq)) (by $(← sq step)) _
              (by $(← sq p0)))).choose_spec,
            $(← good rest), rfl⟩)
    let pf ← good stages.toList
    let goodN := mkIdent (`_root_ ++ fn ++ `goodE)
    elabCommand (← `(set_option maxRecDepth 100000 in set_option maxHeartbeats 4000000 in
      theorem $goodN:ident : ∀ (xs : ByteArray), xs.size ≤ $N → ∃ E, ($wa).GoodE [inLocP] 9 (xs, ()) ($fI xs) E := by
        intro xs hx
        have hds : xs.data.size = xs.size := rfl
        exact ⟨_, $pf⟩))
    let pgI := mkIdent (`_root_ ++ fn ++ `pg)
    let pgGoodI := mkIdent (`_root_ ++ fn ++ `pgGood)
    let compilesI := mkIdent (`_root_ ++ fn ++ `compiles)
    let computesI := mkIdent (`_root_ ++ fn ++ `computes)
    -- programs with `mop` (`*`, `/`, `%` by variables): the checked words with a register choice
    let progT ← match R with
      | .sc _ => `(pgProgS $wa (Proven.Frontx.Res.k (BitVec 64)))
      | .ar _ => `(pgProgA $wa)
    let nT ← match R with
      | .sc _ => `(pgNS $wa (Proven.Frontx.Res.k (BitVec 64)))
      | .ar _ => `(pgNA $wa)
    let chT ← if ← liftTermElabM (evalBoolW (← `(MS.hasMop $progT))) then
        let some (t, sp) ← liftTermElabM (evalChoiceW (← `(natChoice (Proven.WA.pickSpillW $nT [0, 3] [2] $progT))))
          | throwError "wp_compile: no register choice passed optB"
        let ts ← t.toArray.mapM fun (a, b) => `(($(quote a), $(quote b)))
        let ss : Array Term := sp.toArray.map fun j => quote j
        `(some ([$ts,*], [$ss,*]))
      else `(none)
    elabCommand (← `(def $pgI:ident : PgProg := ⟨$(← liftTermElabM (slSyn R)), $wa, $N, $chT⟩))
    match R with
    | .sc _ =>
      elabCommand (← `(set_option maxRecDepth 100000 in
        theorem $pgGoodI:ident : ($pgI).Good :=
          ⟨by decide +kernel, by decide +kernel, by decide +kernel, total_of $pgI $fI $goodN⟩))
    | .ar _ =>
      elabCommand (← `(set_option maxRecDepth 100000 in
        theorem $pgGoodI:ident : ($pgI).Good :=
          ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, total_of $pgI $fI $goodN⟩))
    elabCommand (← `(theorem $compilesI:ident : compile $pgI = some ⟨Proven.Top.wordBytes ($pgI).code, 8192, ($pgI).events⟩ :=
      compile_some $pgGoodI))
    elabCommand (← `(theorem $computesI:ident : Proven.Top.Computes $pgI
        (fun a : {xs : ByteArray // xs.size ≤ $N} => $fI a.1) (fun a => a.1.data.toList) (outEnc ($pgI).R) :=
      computes_of $pgI $fI $goodN))


end Proven.WA
