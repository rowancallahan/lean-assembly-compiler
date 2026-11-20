/- Paged front end (NOTES section 35): `wp_compile`, `wa_compile`'s reflection (`WaCmd.lean`) in paged mode, with the
proofs for the paged back end (`Pg.GoodE`, `WpProg.lean`) and the compiler of `PgTop.lean`.  Untrusted: what counts
are the kernel-checked theorems it generates.

`wp_compile f max N (invariant P measure μ)*` for `f : ByteArray → β` (β a scalar, `ByteArray` or `Array` of
scalars) reads the body of `f` as `wa_compile` does, and in paged mode also:
* a loop's `ByteArray` state that the loop changes starts as a copy of the array it is given
  (`F.extract m 0 m.size`, `ByteArray.extract_zero_size`);
* `let t := a.extract lo hi` is a fresh array (`F.extract`);
* `a ++ b` is a loop pushing `b[i]` onto a copy of `a` (`appendGo`, `append_appendGo'`);
* `Prop` parameters of a loop function are not state; the loop's function `g` rebuilds them from the invariant
  (`if h : … then fn … h … else default`);
* `ByteArray.get!` is `getB` with a bounds check.
It generates `f.wa`, `f.goodE : ∀ xs, xs.size ≤ N → ∃ E, f.wa.GoodE [inLocP] 9 (xs, ()) (f xs) E`, the program
`f.pg : PgProg` (inputs up to `N` bytes), `f.pgGood : f.pg.Good`, `f.compiles : compile f.pg = some …` and
`f.computes : Computes f.pg …` — with `compile_correct` / `compile_runs` (`PgTop.lean`) the statements of
`Compiler/AllocSpec.lean` for `f`. -/
import Legacy.Riscv.Frontx.WaCmd
import Legacy.Riscv.Frontx.PgTop

namespace Proven.WA
open Lean Meta Elab Term Command

theorem append_appendGo' (a b : ByteArray) : a ++ b = appendGo b 0 a := by
  rw [appendGo_eq, ByteArray.extract_zero_size]

theorem push_pushGo' (a : ByteArray) (x : UInt8) : a.push x = pushGo x 0 a := (pushGo_eq x a).symm

theorem ba_extract_zero_ge (a : ByteArray) (n : Nat) (h : a.size ≤ n) : a.extract 0 n = a := by
  apply ByteArray.ext; simp [ByteArray.data_extract]; omega

theorem ba_extract_zero_eq (a : ByteArray) (n : Nat) (h : n = a.size) : a.extract 0 n = a := by
  subst h; exact ByteArray.extract_zero_size

theorem ba_size_set! (a : ByteArray) (i : Nat) (x : UInt8) : (a.set! i x).size = a.size := by
  cases a with
  | mk bs => simp [ByteArray.set!, ByteArray.size]

theorem ba_size_ite_set {c : Prop} [Decidable c] (a : ByteArray) (i : Nat) (x : UInt8) :
    (if c then a.set! i x else a).size = a.size := by split <;> simp [ba_size_set!]

/-- the simp set of the meanings, paged -/
macro "wp_dsimp" : tactic => `(tactic| simp (config := { failIfUnchanged := false }) only [T.okP, T.out, T.den, E.ok,
  E.den, A.den, A.okP, AK.set, AK.push, Args.okP, Args.den, Arg.den, Ini.okP, Ini.den, Inis.okP, Inis.den, F.okP,
  F.den, Vals.app, Mem.get, AK.size, AK.get, Op2.den, Cmp.den, WA.cast, Ty.small, Op2.exact, Op2.side, cast.side,
  Proven.Frontx.ediv_hdiv, Proven.Frontx.emod_hmod, Int.zero_sub, Int.ofNat_eq_natCast, decide_eq_true_eq, AK.el,
  size_ite_set, size_set', Array.size_replicate, u8_lt64, u16_lt64, u32_lt64, u64_lt64, u8_lt64', u16_lt64',
  u32_lt64', u64_lt64', Proven.WP.P, ByteArray.size_push, ByteArray.size_extract, ByteArray.extract_zero_size,
  ByteArray.get!_eq', ba_size_set!, ba_size_ite_set, ba_extract_zero_ge, ba_extract_zero_eq, append_appendGo', pushGo_eq, Array.size_push] at *)

/-- numerals, `≤`, `<`, `+`, `-` at a type that is `Nat` only up to unfolding (`Ty.nat.T`, `(Sl.sc .nat).T`) restated
at `Nat` (a definitional change), so that `omega` reads them -/
def setArgN (t : Expr) (i : Nat) (x : Expr) : Expr :=
  let args := t.getAppArgs
  mkAppN t.getAppFn (args.set! i x)

def natTypes (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => do
    let fix (i : Nat) : MetaM TransformStep := do
      let T := t.getArg! i
      if T.isConstOf ``Nat then return .done t
      if T.hasLooseBVars then return .done t
      if ← withDefault (isDefEq T (mkConst ``Nat)) then
        return .done (setArgN t i (mkConst ``Nat))
      return .done t
    if t.isAppOfArity ``OfNat.ofNat 3 then
      let T := t.getArg! 0
      let n := t.getArg! 1
      -- a numeral whose value is itself a `Nat` numeral: its raw literal
      let n := if n.isAppOfArity ``OfNat.ofNat 3 && (n.getArg! 0).isConstOf ``Nat then n.getArg! 1 else n
      if (T.isConstOf ``Nat && n == t.getArg! 1) || T.hasLooseBVars then return .done t
      if ← withDefault (isDefEq T (mkConst ``Nat)) then
        return .done (mkApp3 (mkConst ``OfNat.ofNat [0]) (mkConst ``Nat) n (mkApp (mkConst ``instOfNatNat) n))
      return .done t
    if t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 then return ← fix 0
    if t.isAppOfArity ``HAdd.hAdd 6 || t.isAppOfArity ``HSub.hSub 6 || t.isAppOfArity ``HMul.hMul 6 ||
        t.isAppOfArity ``HMod.hMod 6 || t.isAppOfArity ``HDiv.hDiv 6 then
      let mut t' := t
      let mut all := true
      for i in [0:3] do
        let Ti := t.getArg! i
        if Ti.isConstOf ``Nat then continue
        if !Ti.hasLooseBVars && (← withDefault (isDefEq Ti (mkConst ``Nat))) then t' := setArgN t' i (mkConst ``Nat)
        else all := false
      return .done (if all then t' else t)
    return .done t)

open Lean Elab Tactic in
elab "nat_types" : tactic => withMainContext do
  let mut g ← getMainGoal
  g ← g.replaceTargetDefEq (← natTypes (← instantiateMVars (← g.getType)))
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' ← natTypes ty
    if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
  replaceMainGoal [g]

/-- `Ty.nat.T` comparisons as `Nat` comparisons (for `omega`), then `wa_close` -/
macro "wp_close" : tactic => `(tactic| ((try dsimp only [Ty.T, AK.T, Sl.T, AK.el] at *); (try nat_types); wa_close))

macro "wp_okt" : tactic => `(tactic| (wp_dsimp <;> wp_close))

set_option hygiene false in
macro "wp_step " P:ident μ:ident : tactic => `(tactic| (
  simp only [$P:ident, $μ:ident] at hP ⊢
  wp_dsimp
  split at h <;> first
    | (injection h with h; subst h; wp_dsimp; (try nat_types); first | omega | (wa_facts; omega) | wp_close)
    | cases h))

/-- a side condition (sizes, bounds): conjunctions split, then `omega` -/
macro "wp_side" : tactic => `(tactic| (
  (try simp only [ByteArray.size_push, ba_size_set!, ba_size_ite_set, ByteArray.size_extract, AK.size, AK.push,
    gt_iff_lt, ge_iff_le] at *)
  (try nat_types)
  repeat' (apply And.intro)
  all_goals (first | omega | (wa_facts; omega))))

/-- the equation of a loop function whose `g` rebuilds proof arguments: `dif_pos` on both sides -/
macro "wp_dif" : tactic => `(tactic| (
  repeat (first | (rw [dif_pos (by wp_side)]) | split)))

syntax "wp_compile " ident (&" reflect_only")? " max " term (" invariant " term " measure " term)* : command

set_option hygiene false in
elab_rules : command
  | `(wp_compile $f:ident $[reflect_only%$ro]? max $N:term $[invariant $Ps measure $μs]*) => do
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
    elabCommand (← `(set_option maxRecDepth 100000 in set_option maxHeartbeats 4000000 in set_option backward.isDefEq.respectTransparency false in
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
        let some (t, sp) ← liftTermElabM (evalChoiceW (← `(natChoice (Proven.Mach.Riscv.pickC $nT [0, 3] [2] $progT))))
          | throwError "wp_compile: no register choice passed optB"
        let ts ← t.toArray.mapM fun (a, b) => `(($(quote a), $(quote b)))
        let ss : Array Term := sp.toArray.map fun j => quote j
        `(some ([$ts,*], [$ss,*]))
      else `(none)
    elabCommand (← `(def $pgI:ident : PgProg := ⟨$(← liftTermElabM (slSyn R)), $wa, $N, $chT⟩))
    match R with
    | .sc _ =>
      elabCommand (← `(set_option maxRecDepth 100000 in set_option backward.isDefEq.respectTransparency false in
        theorem $pgGoodI:ident : ($pgI).Good :=
          ⟨by decide +kernel, by decide +kernel, by decide +kernel, total_of $pgI $fI $goodN⟩))
    | .ar _ =>
      elabCommand (← `(set_option maxRecDepth 100000 in set_option backward.isDefEq.respectTransparency false in
        theorem $pgGoodI:ident : ($pgI).Good :=
          ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, total_of $pgI $fI $goodN⟩))
    elabCommand (← `(theorem $compilesI:ident : compile $pgI = some ⟨Proven.Top.wordBytes ($pgI).code, 8192, ($pgI).events⟩ :=
      compile_some $pgGoodI))
    elabCommand (← `(theorem $computesI:ident : Proven.Top.Computes $pgI
        (fun a : {xs : ByteArray // xs.size ≤ $N} => $fI a.1) (fun a => a.1.data.toList) (outEnc ($pgI).R) :=
      computes_of $pgI $fI $goodN))

end Proven.WA
