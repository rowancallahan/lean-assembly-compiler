/- Nano/V2Self/Proof/ParRun: LAYER 2 of the parser proof (Testing/notes/NANO_V2_PARINV_DESIGN.md): Par1's task machine with ABSTRACT data.
`Frame` has one constructor per task code of Par1's dispatcher `C.v96` (code in the comment), carrying exactly the task's `a`/`b` data
(names instead of token positions, `Sh` instead of shape codes, `Callee` instead of `j` / `512 + prim`).  `stepF f st` = the handler of `f`:
`some (k, st')` where `k` = the tasks it pushes, TOP FIRST (the machine pushes `k.reverse`), `none` = the machine fails (status 0).
Abstract state `St` ↔ machine cells: toks ↔ cursor h3, nx h11, binds (table d9, machine order: row i = index i) h4, defs / cur (table d7) h12,
vals (operand stack d3, TOP FIRST) h8, arena (d5, creation order) h9, ty h25, stash h29, arm h30, sslot h32, out = the emitted words, acc = status 2.
No capacities (the machine only fails more often).  Reads of the machine that are only meaningful under an invariant (operand stack deep
enough, `ty` set, …) are `none` here; `WF` (ParRunWF) states the invariant that makes them `some`. -/
import Nano.V2Self.Proof.ParSpec
namespace ParRun
open ParSpec

/-- an arena node as Par1 stores it (d5 + 8 u): +0 tag, +1 a, +2 b, +3 shape code (`none` = code 0, only the CONTINUE state tuple),
+4 pending bit, +5/+6/+7 first child / child count / next sibling = `kids` -/
inductive RN
  | mk (tag a b : Nat) (sh : Option Sh) (pend : Bool) (kids : List RN)

namespace RN
def tag : RN → Nat | mk t .. => t
def a : RN → Nat | mk _ a .. => a
def b : RN → Nat | mk _ _ b .. => b
def sh : RN → Option Sh | mk _ _ _ s .. => s
def pend : RN → Bool | mk _ _ _ _ p _ => p
def kids : RN → List RN | mk _ _ _ _ _ k => k
/-- the width-0 INPUT LOCAL (`v205`/`v209`: tag 2, b = 0) -/
def isInp (n : RN) : Bool := n.tag == 2 && n.b == 0
end RN

/-- binding row (d9 + 4 i): name, slot, shape code (`none` = 0: a binder whose type is not parsed yet), input flag -/
structure Bd where
  name : List Nat
  slot : Nat
  sh : Option Sh
  inp : Bool

/-- def row (d7 + 8 j): +0 name, +1 npw, +2 non-input parameter count, +3 result code, +4 loop flag, +5.. parameter codes (+6 = their count) -/
structure DefR where
  name : List Nat
  npw : Nat
  nni : Nat
  res : Option Sh
  loop : Bool
  params : List Sh

def DefR.fresh (x : List Nat) : DefR := { name := x, npw := 0, nni := 0, res := none, loop := false, params := [] }

/-- the `a` of call tasks: a def row `j` (< 512) or a prim `p` (encoded `512 + p`) -/
inductive Callee | df (j : Nat) | pr (p : Nat)
  deriving DecidableEq

inductive Frame
  | expr (minp md : Nat)                     -- 1  (a = minp, b = mode: 0 not tail, 1 tail, 2 operand (no if/let))
  | binLoop (minp : Nat)                     -- 2
  | prim (md : Nat)                          -- 3  primary (b = mode)
  | rparen                                   -- 4  expect `)`
  | mkBin (op : Nat)                         -- 5
  | ifCmp (tl : Bool)                        -- 6
  | ifThen (cmp : Nat) (tl : Bool)           -- 7
  | ifElse                                   -- 8
  | mkIte (cmp : Nat)                        -- 9
  | letSemi (x : List Nat) (tl : Bool)       -- 11
  | letEnd (slot depth : Nat)                -- 12
  | parenClose                               -- 40
  | letStart (tl : Bool)                     -- 41
  | mkPair                                   -- 42
  | argAtom                                  -- 43
  | args (c : Callee) (k : Nat)              -- 44
  | mkCallN (c : Callee) (depth : Nat)       -- 45
  | selfArgs                                 -- 46
  | argCheck (c : Callee) (k : Nat)          -- 47
  | mkCall (c : Callee) (n : Nat)            -- 48
  | shiftNum (op : Nat)                      -- 49
  | letPairX (tl : Bool)                     -- 50
  | letPairY (x : List Nat) (tl : Bool)      -- 51
  | stash (x : List Nat)                     -- 52
  | letPairSemi (y : List Nat) (tl : Bool)   -- 53
  | mkCont (f k : Nat)                       -- 54
  | argName                                  -- 55
  | defs                                     -- 60
  | tyAtom                                   -- 61
  | tyCross                                  -- 62
  | tyPair (l : Sh)                          -- 63
  | binders                                  -- 66
  | group (start : Nat)                      -- 67
  | assign (i sz : Nat)                      -- 68 (b = number of names in the binder group)
  | plainBody                                -- 70
  | afterColon                               -- 73
  | stateTy                                  -- 74
  | armsStart                                -- 75
  | armBind (step : Bool) (i : Nat)          -- 76
  | zeroDone                                 -- 77
  | mkLoop                                   -- 79
  | defEnd                                   -- 80
  | flat (n : RN)                            -- 81
  | flatL (ns : List RN)                     -- 82 (a = first node, b = ns.length)
  | defClose                                 -- 83
  | tupRest                                  -- 90

/-- the task code of a frame (the `c` cell) -/
def Frame.code : Frame → Nat
  | .expr .. => 1 | .binLoop _ => 2 | .prim _ => 3 | .rparen => 4 | .mkBin _ => 5 | .ifCmp _ => 6 | .ifThen .. => 7 | .ifElse => 8
  | .mkIte _ => 9 | .letSemi .. => 11 | .letEnd .. => 12 | .parenClose => 40 | .letStart _ => 41 | .mkPair => 42 | .argAtom => 43
  | .args .. => 44 | .mkCallN .. => 45 | .selfArgs => 46 | .argCheck .. => 47 | .mkCall .. => 48 | .shiftNum _ => 49 | .letPairX _ => 50
  | .letPairY .. => 51 | .stash _ => 52 | .letPairSemi .. => 53 | .mkCont .. => 54 | .argName => 55 | .defs => 60 | .tyAtom => 61
  | .tyCross => 62 | .tyPair _ => 63 | .binders => 66 | .group _ => 67 | .assign .. => 68 | .plainBody => 70 | .afterColon => 73
  | .stateTy => 74 | .armsStart => 75 | .armBind .. => 76 | .zeroDone => 77 | .mkLoop => 79 | .defEnd => 80 | .flat _ => 81
  | .flatL _ => 82 | .defClose => 83 | .tupRest => 90

structure St where
  toks : List Tok
  nx : Nat
  binds : List Bd
  defs : List DefR
  cur : DefR
  vals : List RN
  arena : List RN
  ty : Option Sh
  stash : List Nat
  arm : Bool
  sslot : Nat
  out : List UInt64
  acc : Bool

def init (toks : List Tok) : St :=
  { toks, nx := 0, binds := [], defs := [], cur := DefR.fresh [], vals := [], arena := [], ty := none, stash := [], arm := false,
    sslot := 0, out := [2], acc := false }

/-! ## helpers (machine subroutines) -/
/-- `v9`: width of a shape code (code 0 counts 1) -/
def cw : Option Sh → Nat | some s => s.width | none => 1

/-- `v7`: the innermost (last) binding with this name -/
def findB (bs : List Bd) (x : List Nat) : Option Bd := bs.reverse.find? fun b => b.name == x

/-- `v8`: the index of the last def row with this name among `ds` -/
def findD (ds : List DefR) (x : List Nat) : Option Nat :=
  (ds.reverse.findIdx? fun d => d.name == x).map fun i => ds.length - 1 - i

/-- the row table as `v104` sees it: finished rows and the current one (index `defs.length`) -/
def rows (st : St) : List DefR := st.defs ++ [st.cur]

/-- `v91` / `v92` / `v90`: prim arity, result code, parameter code -/
def primAr (p : Nat) : Nat := if p = 5 then 0 else if p = 8 then 3 else if p = 2 ∨ p = 4 ∨ p = 7 ∨ p = 9 then 2 else 1
def primRes (p : Nat) : Sh := if p = 1 then .nt else if p = 4 then .ls else if p = 5 ∨ p = 8 ∨ p = 9 then .bf else .uw
def primPar (p j : Nat) : Sh := if j = 0 then (if p < 5 then .ls else .bf) else .uw

def arity (st : St) : Callee → Nat
  | .df j => ((rows st)[j]?.map fun d => d.params.length).getD 0
  | .pr p => primAr p
def parCode (st : St) : Callee → Nat → Option Sh
  | .df j, i => (rows st)[j]?.bind fun d => d.params[i]?
  | .pr p, i => some (primPar p i)

/-- `v5`: a node from the top `n` operands (first child = deepest), appended to the arena and pushed -/
def mkNode (st : St) (tag a b : Nat) (sh : Option Sh) (pend : Bool) (n : Nat) : Option St :=
  if n ≤ st.vals.length then
    let nd := RN.mk tag a b sh pend (st.vals.take n).reverse
    some { st with vals := nd :: st.vals.drop n, arena := st.arena ++ [nd] }
  else none

/-- a leaf node -/
def leaf (st : St) (tag a b : Nat) (sh : Sh) : St :=
  let nd := RN.mk tag a b (some sh) false []
  { st with vals := nd :: st.vals, arena := st.arena ++ [nd] }

/-- the LOC node of a binding (`v104`/`v120`): fuel bindings (code 4) are not values -/
def locOf (st : St) (bd : Bd) : Option St :=
  if bd.sh = some .nt then none else
  let nd := RN.mk 2 bd.slot (if bd.inp then 0 else cw bd.sh) bd.sh false []
  some { st with vals := nd :: st.vals, arena := st.arena ++ [nd] }

/-- the mode cell of a non-operand expression task -/
def bm (tl : Bool) : Nat := if tl then 1 else 0

/-- `v203`: a List (code 3) appears in the list -/
def hasLs (l : List (Option Sh)) : Bool := l.any (· == some .ls)

/-- `v210`: argument i is the input local iff parameter i is the FIRST List parameter -/
def inpMatch : List Sh → Bool → List RN → Bool
  | _, _, [] => true
  | w :: ws, g, k :: ks => ((w == .ls && !g) == k.isInp) && inpMatch ws (g || w == .ls) ks
  | [], _, _ :: _ => false

/-- `v209` on one node; `ds` = the finished rows (the last one is the def the arena belongs to) -/
def nodeOK (ds : List DefR) (n : RN) : Bool :=
  let m := (n.kids.filter RN.isInp).length
  let p0 := match n.kids with | k :: _ => k.isInp | [] => false
  let r := if m = 0 then (if n.tag = 9 then !(n.a < 4) else true)
    else if n.tag = 8 then true
    else if n.tag = 6 then n.sh.isNone
    else if n.tag = 9 then (if n.a < 4 then m = 1 && p0 else false)
    else false
  let r2 := if n.tag = 8 then
      (match ds[n.a]? with | some d => d.params.length = n.kids.length && inpMatch d.params false n.kids | none => false)
    else if n.tag = 6 then
      (if n.sh.isNone then (match ds.getLast? with
        | some d => d.params.length = n.kids.length + 1 && inpMatch d.params.tail false n.kids | none => false) else true)
    else true
  r && r2

/-! ## the handlers -/
def stepF : Frame → St → Option (List Frame × St)
  | .expr m md, st => some ([.prim md, .binLoop m], st)
  | .prim md, st =>
    if md = 2 ∧ (st.toks.head? = some (.k 32) ∨ st.toks.head? = some (.k 2)) then none else
    let tl := md == 1
    match st.toks with
    | .k 32 :: r => some ([.expr 0 2, .ifCmp tl], { st with toks := r })
    | .k 2 :: r => some ([.letStart tl], { st with toks := r })
    | .num v :: r => some ([], leaf { st with toks := r } 1 v 0 .uw)
    | .k 6 :: r => some ([.expr 0 (bm tl), .parenClose], { st with toks := r })
    | .id x :: r =>
      let st := { st with toks := r }
      match findB st.binds x with
      | some bd => (locOf st bd).map fun st => ([], st)
      | none =>
        match findD (rows st) x with
        | none => none
        | some j =>
          if j = st.defs.length then (if tl && st.arm then some ([.selfArgs], st) else none)
          else some ([.args (.df j) (arity st (.df j)), .mkCallN (.df j) st.vals.length], st)
    | .k 30 :: .k 31 :: r => some ([], leaf { st with toks := r } 9 5 0 .ls)
    | .k t :: r =>
      if t ≠ 30 ∧ 38 < t ∧ t < 48 then some ([.args (.pr (t - 38)) (primAr (t - 38)), .mkCallN (.pr (t - 38)) st.vals.length], { st with toks := r })
      else none
    | _ => none
  | .binLoop m, st =>
    match st.toks with
    | .k t :: r =>
      match opInfo t with
      | none => some ([], st)
      | some (op, p) =>
        if p < m then some ([], st) else
        match st.vals with
        | top :: _ =>
          if top.pend then none else
          if t = 28 ∨ t = 29 then some ([.shiftNum op, .binLoop m], { st with toks := r })
          else some ([.expr (p + 1) 2, .mkBin op, .binLoop m], { st with toks := r })
        | [] => none
    | _ => some ([], st)
  | .shiftNum op, st =>
    match st.toks with
    | .num v :: r => some ([.mkBin op], leaf { st with toks := r } 1 v 0 .uw)
    | _ => none
  | .mkBin op, st =>
    match st.vals with
    | y :: x :: _ => if x.sh = some .uw ∧ y.sh = some .uw then (mkNode st 3 op 0 (some .uw) false 2).map fun st => ([], st) else none
    | _ => none
  | .parenClose, st =>
    match st.toks with
    | .k 7 :: r => some ([], { st with toks := r })
    | .k 15 :: r => some ([.expr 0 0, .tupRest, .mkPair], { st with toks := r })
    | _ => none
  | .tupRest, st =>
    match st.toks with
    | .k 7 :: r => some ([], { st with toks := r })
    | .k 15 :: r => some ([.expr 0 0, .tupRest, .mkPair], { st with toks := r })
    | _ => none
  | .mkPair, st =>
    match st.vals with
    | y :: x :: _ =>
      match x.sh, y.sh with
      | some l, some r =>
        if x.pend || y.pend then none else
        if l = .nt ∨ r = .nt then none else
        (mkNode { st with ty := some (.p l r) } 6 2 0 (some (.p l r)) false 2).map fun st => ([], st)
      | _, _ => none
    | _ => none
  | .rparen, st =>
    match st.toks with
    | .k 7 :: r => some ([], { st with toks := r })
    | _ => none
  | .ifCmp tl, st =>
    match st.toks with
    | .k 23 :: r => some ([.expr 0 2, .ifThen 1 tl], { st with toks := r })
    | .k 20 :: r => some ([.expr 0 2, .ifThen 2 tl], { st with toks := r })
    | _ => none
  | .ifThen c tl, st =>
    match st.toks with
    | .k 33 :: r => some ([.expr 0 (bm tl), .ifElse, .expr 0 (bm tl), .mkIte c], { st with toks := r })
    | _ => none
  | .ifElse, st =>
    match st.toks with
    | .k 34 :: r => some ([], { st with toks := r })
    | _ => none
  | .mkIte c, st =>
    match st.vals with
    | e :: t :: b :: a :: _ =>
      if a.sh = some .uw ∧ b.sh = some .uw ∧ t.sh = e.sh then
        (mkNode st 4 c 0 e.sh (t.pend || e.pend) 4).map fun st => ([], st)
      else none
    | _ => none
  | .letStart tl, st =>
    match st.toks with
    | .id x :: .k 9 :: r => some ([.expr 0 0, .letSemi x tl], { st with toks := r })
    | .k 6 :: r => some ([.letPairX tl], { st with toks := r })
    | _ => none
  | .letSemi x tl, st =>
    match st.toks, st.vals with
    | .k 13 :: r, v :: _ =>
      if v.sh = some .nt then none else
      some ([.expr 0 (bm tl), .letEnd st.nx st.binds.length],
        { st with toks := r, nx := st.nx + cw v.sh, binds := st.binds ++ [⟨x, st.nx, v.sh, false⟩] })
    | _, _ => none
  | .letEnd s d, st =>
    match st.vals with
    | body :: v :: _ => (mkNode { st with binds := st.binds.take d } 5 s (cw v.sh) body.sh body.pend 2).map fun st => ([], st)
    | _ => none
  | .letPairX tl, st =>
    match st.toks with
    | .id x :: .k 15 :: r => some ([.letPairY x tl], { st with toks := r })
    | _ => none
  | .letPairY x tl, st =>
    match st.toks with
    | .id y :: .k 7 :: .k 9 :: r => some ([.expr 0 0, .stash x, .letPairSemi y tl], { st with toks := r })
    | _ => none
  | .stash x, st => some ([], { st with stash := x })
  | .letPairSemi y tl, st =>
    match st.toks, st.vals with
    | .k 13 :: r, v :: _ =>
      match v.sh with
      | some (.p l rr) =>
        some ([.expr 0 (bm tl), .letEnd st.nx st.binds.length],
          { st with toks := r, nx := st.nx + cw v.sh,
                    binds := st.binds ++ [⟨st.stash, st.nx, some l, false⟩, ⟨y, st.nx + l.width, some rr, false⟩] })
      | _ => none
    | _, _ => none
  | .args c k, st => match k with
    | 0 => some ([], st)
    | k + 1 => some ([.argAtom, .args c k], st)
  | .argAtom, st =>
    match st.toks with
    | .k 6 :: r => some ([.expr 0 0, .parenClose], { st with toks := r })
    | .num _ :: _ => some ([.prim 0], st)
    | .id x :: r =>
      match findB st.binds x with
      | some bd => (locOf { st with toks := r } bd).map fun st => ([], st)
      | none => some ([.argName], st)
    | _ => some ([.argName], st)
  | .argName, st =>
    match st.toks with
    | .id x :: r =>
      match findD st.defs x with
      | some j =>
        match st.defs[j]? with
        | some d => if d.params.length = 0 then (mkNode { st with toks := r } 8 j 0 d.res false 0).map fun st => ([], st) else none
        | none => none
      | none => none
    | .k 30 :: .k 31 :: r => some ([], leaf { st with toks := r } 9 5 0 .ls)
    | .k 43 :: r => some ([], leaf { st with toks := r } 9 5 0 .bf)
    | _ => none
  | .mkCallN c d, st => some ([.argCheck c (st.vals.length - d), .mkCall c (st.vals.length - d)], st)
  | .argCheck c k, st => match k with
    | 0 => some ([], st)
    | k + 1 =>
      match st.vals[k]?, parCode st c (arity st c - (k + 1)) with
      | some v, some w =>
        if v.sh = some w ∨ (w = .nt ∧ (v.tag = 1 ∨ (v.tag = 9 ∧ v.a = 1))) then some ([.argCheck c k], st) else none
      | _, _ => none
  | .mkCall c n, st => match c with
    | .df j => match (rows st)[j]? with
      | some d => (mkNode st 8 j n d.res false n).map fun st => ([], st)
      | none => none
    | .pr p => (mkNode st 9 p 0 (some (primRes p)) false n).map fun st => ([], st)
  | .selfArgs, st =>
    match st.toks with
    | .id x :: r =>
      match findB st.binds x with
      | some bd =>
        if bd.sh = some .nt then
          let f := st.defs.length
          let j := st.cur.params.length - 1
          some ([.args (.df f) j, .argCheck (.df f) j, .mkCont f j], { st with toks := r })
        else none
      | none => none
    | _ => none
  | .mkCont f k, st =>
    match (rows st)[f]? with
    | some d =>
      let st1 := if k = 1 then some st else mkNode st 6 k 0 none false k
      (st1.bind fun st => mkNode st 11 0 0 d.res true 1).map fun st => ([], st)
    | none => none
  -- types
  | .tyAtom, st =>
    match st.toks with
    | .k 6 :: r => some ([.tyAtom, .rparen, .tyCross], { st with toks := r })
    | .k 3 :: r => some ([.tyCross], { st with toks := r, ty := some .uw })
    | .k 36 :: r => some ([.tyCross], { st with toks := r, ty := some .bf })
    | .k 35 :: r => some ([.tyCross], { st with toks := r, ty := some .nt })
    | .k 37 :: .k 38 :: r => some ([.tyCross], { st with toks := r, ty := some .ls })
    | _ => none
  | .tyCross, st =>
    match st.toks with
    | .k 16 :: r => match st.ty with
      | some l => some ([.tyAtom, .tyPair l], { st with toks := r })
      | none => none
    | _ => some ([], st)
  | .tyPair l, st =>
    match st.ty with
    | some r => if l = .nt ∨ r = .nt then none else some ([], { st with ty := some (.p l r) })
    | none => none
  -- defs
  | .defs, st =>
    if !(st.arena.all (nodeOK st.defs)) then none else
    match st.toks with
    | [] => some ([], { st with acc := true })
    | .k 1 :: .id x :: r =>
      match findD st.defs x with
      | some _ => none
      | none =>
        let st := { st with toks := r, cur := DefR.fresh x, binds := [], vals := [], arena := [], nx := 0, arm := false }
        match r with
        | .k 8 :: r2 => some ([.tyAtom, .afterColon], { st with toks := r2 })
        | _ => some ([.binders], st)
    | _ => none
  | .binders, st =>
    match st.toks with
    | .k 6 :: r => some ([.group st.binds.length], { st with toks := r })
    | .k 8 :: r => some ([.tyAtom, .plainBody], { st with toks := r })
    | _ => none
  | .group a, st =>
    match st.toks with
    | .id x :: r => some ([.group a], { st with toks := r, binds := st.binds ++ [⟨x, 0, none, false⟩] })
    | .k 8 :: r => if a < st.binds.length then some ([.tyAtom, .rparen, .assign a (st.binds.length - a), .binders], { st with toks := r }) else none
    | _ => none
  | .assign a sz, st =>
    if a = st.binds.length then some ([], st) else
    match st.ty, st.binds[a]? with
    | some w, some bd =>
      if w = .nt then none else
      let n1 := w == .ls && sz == 1 && !((st.binds.take a).any Bd.inp)
      some ([.assign (a + 1) sz],
        { st with binds := st.binds.set a ⟨bd.name, st.nx, some w, n1⟩,
                  nx := if n1 then st.nx else st.nx + w.width,
                  cur := { st.cur with params := st.cur.params ++ [w], nni := if n1 then st.cur.nni else st.cur.nni + 1 } })
    | _, _ => none
  | .plainBody, st =>
    if st.ty = some .nt then none else
    let st := { st with cur := { st.cur with npw := st.nx, res := st.ty, loop := false } }
    match st.toks with
    | .k 9 :: r => some ([.expr 0 0, .defEnd], { st with toks := r })
    | _ => none
  | .afterColon, st =>
    match st.toks with
    | .k 9 :: r =>
      if st.ty = some .nt then none else
      let st := { st with cur := { st.cur with npw := st.nx, res := st.ty, loop := false } }
      some ([.expr 0 0, .defEnd], { st with toks := r })
    | .k 17 :: r =>
      if st.ty = some .nt then
        let c := { st.cur with npw := 1, loop := true, params := st.cur.params ++ [.nt], nni := st.cur.nni + 1 }
        some ([.tyAtom, .stateTy], { st with toks := r, cur := c })
      else none
    | _ => none
  | .stateTy, st =>
    match st.ty with
    | some w =>
      let n1 := w == .ls && !(hasLs (st.cur.params.map some))
      match st.toks with
      | .k 17 :: r =>
        if w = .nt then none else
        let c := { st.cur with npw := if n1 then st.cur.npw else st.cur.npw + w.width, params := st.cur.params ++ [w],
                               nni := if n1 then st.cur.nni else st.cur.nni + 1 }
        some ([.tyAtom, .stateTy], { st with toks := r, cur := c })
      | _ => if st.cur.params.length = 1 then none else some ([.armsStart], st)
    | none => none
  | .armsStart, st =>
    if st.ty = some .nt then none else
    let st := { st with cur := { st.cur with res := st.ty }, nx := st.cur.npw }
    match st.toks with
    | .k 18 :: .num 0 :: .k 15 :: r => some ([.armBind false 1], { st with toks := r, sslot := 1 })
    | _ => none
  | .armBind stp b, st =>
    match st.cur.params[b]?, st.toks with
    | some w, .id x :: t :: r =>
      let n1 := w == .ls && !(hasLs ((st.cur.params.take b).map some))
      match findB st.binds x with
      | some _ => none
      | none =>
        let st := { st with toks := r, binds := st.binds ++ [⟨x, st.sslot, some w, n1⟩],
                            sslot := if n1 then st.sslot else st.sslot + w.width }
        if b + 1 < st.cur.params.length then (if t = .k 15 then some ([.armBind stp (b + 1)], st) else none)
        else if t = .k 19 then
          (if stp then some ([.expr 0 1, .mkLoop, .defEnd], st) else some ([.expr 0 0, .zeroDone], st))
        else none
    | _, _ => none
  | .zeroDone, st =>
    match st.vals with
    | z :: _ =>
      if z.sh = st.cur.res then
        match st.toks with
        | .k 18 :: .id nb :: .k 10 :: .num 1 :: .k 15 :: r =>
          some ([.armBind true 1], { st with toks := r, binds := [⟨nb, 0, some .nt, false⟩], arm := true, sslot := 1 })
        | _ => none
      else none
    | [] => none
  | .mkLoop, st =>
    match st.vals with
    | s :: _ => if s.sh = st.cur.res then (mkNode st 10 0 0 st.cur.res false 2).map fun st => ([], st) else none
    | [] => none
  | .defEnd, st =>
    match st.vals with
    | [z] =>
      if z.sh = st.cur.res ∧ !z.isInp then
        some ([.flat z, .defClose], { st with out := st.out ++
          [20, st.defs.length.toUInt64, st.cur.npw.toUInt64, st.nx.toUInt64, (if st.cur.loop then 1 else 0), (cw st.cur.res).toUInt64] })
      else none
    | _ => none
  | .flat n, st =>
    let ks := n.kids
    let ni := (ks.filter RN.isInp).length
    if n.tag = 6 ∧ ks.length - ni = 1 then some ([.flatL ks], st) else
    let w1 : List UInt64 := [n.tag.toUInt64]
    let w2 : List UInt64 := if n.tag = 6 then [(ks.length - ni).toUInt64] else if n.tag < 10 then [n.a.toUInt64] else []
    let w3 : List UInt64 := if n.tag = 2 ∨ n.tag = 5 then [n.b.toUInt64] else if n.tag = 8 then [(n.b - ni).toUInt64] else []
    some ([.flatL (if n.tag = 9 ∧ n.a < 4 then ks.tail else ks)], { st with out := st.out ++ (w1 ++ w2 ++ w3) })
  | .flatL ns, st =>
    match ns with
    | [] => some ([], st)
    | n :: r => if n.isInp then some ([.flatL r], st) else some ([.flat n, .flatL r], st)
  | .defClose, st => some ([.defs], { st with out := st.out ++ [21], defs := st.defs ++ [st.cur] })

/-! ## runs -/
def stepS : List Frame × St → Option (List Frame × St)
  | (f :: fs, st) => (stepF f st).map fun (k, st') => (k ++ fs, st')
  | ([], _) => none

/-- reflexive-transitive closure of `stepS` -/
inductive Star : List Frame × St → List Frame × St → Prop
  | refl (c) : Star c c
  | step {c d e} : stepS c = some d → Star d e → Star c e

/-- fuel-iterated run to the empty task stack (for evaluation) -/
def run : Nat → List Frame → St → Option St
  | 0, _, _ => none
  | _ + 1, [], st => some st
  | n + 1, f :: fs, st => (stepF f st).bind fun (k, st') => run n (k ++ fs) st'

/-- `v99`'s post-checks: at least one def, the last is `m` with exactly the input parameter and a `List UInt8` result -/
def mainOK (st : St) : Bool :=
  match st.defs.getLast? with
  | some d => d.name == [109] && d.nni == 0 && d.params.head? == some .ls && d.res == some .ls
  | none => false

/-- the abstract parser: tokens ↦ emitted words -/
def Accepts (toks : List Tok) (o : List UInt64) : Prop :=
  ∃ st, Star ([.defs], init toks) ([], st) ∧ st.acc ∧ mainOK st ∧ st.out = o

def runParse (fuel : Nat) (ts : List UInt64) : Option (List UInt64) :=
  (tokens ts).bind fun toks => (run fuel [.defs] (init toks)).bind fun st => if st.acc && mainOK st then some st.out else none

end ParRun
