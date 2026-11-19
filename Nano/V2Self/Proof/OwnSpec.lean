/- Nano/V2Self/Proof/OwnSpec: the OWNERSHIP discipline `Linear` of a resolved program (`List ParSpec.DefA`), the
specification of the ownership stage `C.o…` (Nano/V2Self/C/Own.lean) between the parser (Par1) and the code generator
(Gen).  Why: Gen's BPUSH / BSET / PUT update a buffer IN PLACE, so a program whose meaning (`NanoMain.Sem`, pure)
reads a buffer after it was passed to a mutating use is miscompiled (Testing/notes/NANO_V2_MAIN.md "FINDING").
`Linear p` rules out every such program.  Notes: Testing/notes/NANO_V2_OWN.md.

The resolved AST has no types, so `Linear p` asks for KINDS (an existential witness, one list per def):
slot kinds `K` (0 word, 1 owned buffer, 2 read-only buffer = a borrowed parameter); a def's parameter kinds are the first
`npw` entries of its `K`; result kinds (0/1) are computed.  Kinds are STATIC per slot: every write of a slot agrees with
its kind (a `let` value's kinds = the slot kinds; CALL arguments / CONTINUE payloads fit the parameter / state kinds), so
"kind 0 ⇒ the slot holds a word" is an invariant of `NanoMain.ev` (no scoping assumption needed).
The walk follows `NanoMain.ev`'s evaluation order and threads DEAD flags `F` (one per slot):
* a LOCAL word of an OWNED slot in a TRANSFER position (`let` value, pair field, def / branch / `let`-body result,
  CALL argument for an owned parameter, CONTINUE payload for an owned state, buffer argument of PUT / BSET / BPUSH)
  CONSUMES the slot: it must be live and becomes dead;
* BORROWS: the buffer argument of BSIZE / BGET, a CALL argument for a read-only parameter (the slot stays live);
* a READ-ONLY slot may only be borrowed, or passed on to a read-only CONTINUE state;
* inside an argument list (operands of BIN / IF conditions, pair fields, CALL / PRIM arguments, CONTINUE payload) the
  direct LOCAL arguments are PINNED: live when reached, consumed (resp. re-checked live, for borrows) only after all the
  other arguments ran — so `f h (bget h 0)` is fine, `bset b 0 (bsize (bpush b 1))` and `f b b` are not;
  consumptions are applied before the borrow re-checks (an owned and a borrowed copy of one buffer in one call fail);
* `if` branches start from the same flags, the union of deaths continues; a `let` slot must not be dead when written;
* a fuel loop must be the whole def body; both arms start with all flags clear (each iteration rebinds the states);
* word destinations (BIN / IF operands, indices, values) accept only words.
Entries: an expression's value is a list of entries, one per word: a plain kind 0/1, or, for a LOCAL word of slot `s` of
kind `k`, the tagged entry `k + 4 * (s + 1)` (the parent decides whether it is a transfer, a borrow or a pin). -/
import Nano.V2Self.Proof.ParSpec
namespace OwnSpec
open ParSpec

/-- context of one def: parameter / result kinds of the earlier defs, this def's slot kinds, its parameter width -/
structure Cx where
  ps : List (List Nat)
  rs : List (List Nat)
  K : List Nat
  npw : Nat

/-- destination kinds: 0 word, 1 owned transfer, 2 borrow, 3 read-only only; anything else (4) = no such argument -/
def dest (ds : Option (List Nat)) (o : Nat) : Nat :=
  match ds with | none => 1 | some l => l.getD o 4

/-- prim argument destinations (Gen's numbering: ISIZE 1, RD 2, LEN 3, PUT 4, BNEW 5, BSIZE 6, BGET 7, BSET 8, BPUSH 9) -/
def dsP : Nat → List Nat
  | 2 => [0] | 4 => [1, 0] | 6 => [2] | 7 => [2, 0] | 8 => [1, 0, 0] | 9 => [1, 0] | _ => []

/-- prim result kind -/
def rk (p : Nat) : Nat := if p = 4 ∨ p = 5 ∨ p = 8 ∨ p = 9 then 1 else 0

/-- CONTINUE destinations: the state kinds (slots 1 .. npw-1), a read-only state takes read-only slots only -/
def stD (K : List Nat) (npw : Nat) : List Nat :=
  ((K.drop 1).take (npw - 1)).map fun k => if k = 2 then 3 else k

/-- the tagged entries of `LOCAL s w` -/
def locE (K : List Nat) (s w : Nat) : List Nat :=
  (List.range w).map fun j => K.getD (s + j) 0 + 4 * (s + j + 1)

def dead (F : List Bool) (s : Nat) : Bool := F.getD s true

/-- one entry reaching destination `d` (checked when its argument is complete) -/
def ok1 (F : List Bool) (e d : Nat) : Bool :=
  if e < 4 then (e == 0 && d < 4) || (e == 1 && (d == 1 || d == 2))
  else if e % 4 = 0 then d < 4
  else if e % 4 = 1 then (d == 1 || d == 2) && !dead F (e / 4 - 1)
  else if e % 4 = 2 then d == 2 || d == 3
  else false

def okAll (ds : Option (List Nat)) (F : List Bool) (o : Nat) : List Nat → Bool
  | [] => true
  | e :: r => ok1 F e (dest ds o) && okAll ds F (o + 1) r

def consume1 (F : List Bool) (s : Nat) : Option (List Bool) :=
  if dead F s then none else some (F.set s true)

/-- an entry is an owned pin -/
def own (e : Nat) : Bool := 4 ≤ e && e % 4 == 1

/-- end of an argument list, pass 1: owned pins at transfer destinations are consumed -/
def finC (ds : Option (List Nat)) : List Bool → Nat → List Nat → Option (List Bool)
  | F, _, [] => some F
  | F, o, e :: r =>
    if own e && dest ds o == 1 then (consume1 F (e / 4 - 1)).bind fun F1 => finC ds F1 (o + 1) r
    else finC ds F (o + 1) r

/-- pass 2: owned pins at borrow destinations are still live -/
def finB (ds : Option (List Nat)) (F : List Bool) : Nat → List Nat → Bool
  | _, [] => true
  | o, e :: r => (!(own e && dest ds o == 2) || !dead F (e / 4 - 1)) && finB ds F (o + 1) r

/-- plain kinds of entries -/
def strip (es : List Nat) : List Nat := es.map fun e => if e < 4 then e else min (e % 4) 1

def fin (ds : Option (List Nat)) (F : List Bool) (es : List Nat) : Option (List Bool × List Nat) :=
  if (match ds with | none => true | some l => es.length == l.length) then
    (finC ds F 0 es).bind fun F2 => if finB ds F2 0 es then some (F2, strip es) else none
  else none

/-- a TRANSFER of a whole value (`let` value, branch / body result): owned LOCAL words are consumed -/
def tr : List Bool → List Nat → Option (List Bool × List Nat)
  | F, [] => some (F, [])
  | F, e :: r =>
    if e < 4 then (if e ≤ 1 then (tr F r).map fun x => (x.1, e :: x.2) else none)
    else if e % 4 = 0 then (tr F r).map fun x => (x.1, 0 :: x.2)
    else if e % 4 = 1 then (consume1 F (e / 4 - 1)).bind fun F1 => (tr F1 r).map fun x => (x.1, 1 :: x.2)
    else none

/-- branch join: a CONTINUE (no entries) takes the other side -/
def join (a b : List Nat) : Option (List Nat) :=
  if a = [] then some b else if b = [] then some a
  else if a.length = b.length then some (List.zipWith max a b) else none

def orF (a b : List Bool) : List Bool := List.zipWith (· || ·) a b

def notDeadR (F : List Bool) (s : Nat) : Nat → Bool
  | 0 => true
  | w + 1 => !dead F (s + w) && notDeadR F s w

/-- the two word operands of BIN / an IF condition, as the argument list `[a, b]` (`lstA` unfolded) -/
def two (a0 b0 : List Bool × List Nat) : Option (List Bool × List Nat) :=
  if okAll (some [0, 0]) a0.1 0 a0.2 && okAll (some [0, 0]) b0.1 a0.2.length b0.2 then fin (some [0, 0]) b0.1 (a0.2 ++ b0.2)
  else none

mutual
/-- the walk of one node: flags in, flags and entries out (`none` = rejected) -/
def chk (c : Cx) : Nd → List Bool → Option (List Bool × List Nat)
  | .const _, F => some (F, [0])
  | .loc s w, F => if s + w ≤ c.K.length then some (F, locE c.K s w) else none
  | .bin _ a b, F => (chk c a F).bind fun a0 => (chk c b a0.1).bind fun b0 =>
    (two a0 b0).map fun y => (y.1, [0])
  | .ite _ a b t e, F =>
    (chk c a F).bind fun a0 => (chk c b a0.1).bind fun b0 => (two a0 b0).bind fun y =>
    (chk c t y.1).bind fun t0 => (tr t0.1 t0.2).bind fun t1 =>
    (chk c e y.1).bind fun e0 => (tr e0.1 e0.2).bind fun e1 =>
    (join t1.2 e1.2).map fun k => (orF t1.1 e1.1, k)
  | .letE s w v b, F =>
    (chk c v F).bind fun v0 => (tr v0.1 v0.2).bind fun v1 =>
    if c.npw ≤ s ∧ s + w ≤ c.K.length ∧ v1.2 = (c.K.drop s).take w ∧ notDeadR v1.1 s w = true then chk c b v1.1 else none
  | .pair cs, F => (lstA c cs none F []).bind fun x => fin none x.1 x.2
  | .call i as, F =>
    match c.ps[i]?, c.rs[i]? with
    | some P, some R => (lstA c as (some P) F []).bind fun x => (fin (some P) x.1 x.2).map fun y => (y.1, R)
    | _, _ => none
  | .prim p as, F => (lstA c as (some (dsP p)) F []).bind fun x => (fin (some (dsP p)) x.1 x.2).map fun y => (y.1, [rk p])
  | .loop _ _, _ => none
  | .cont e, F =>
    match e with
    | .pair cs => (lstA c cs (some (stD c.K c.npw)) F []).bind fun x => (fin (some (stD c.K c.npw)) x.1 x.2).map fun y => (y.1, [])
    | e' => (chk c e' F).bind fun x =>
      if okAll (some (stD c.K c.npw)) x.1 0 x.2 then (fin (some (stD c.K c.npw)) x.1 x.2).map fun y => (y.1, []) else none
/-- an argument list: children left to right, each checked against its destinations when complete -/
def lstA (c : Cx) : List Nd → Option (List Nat) → List Bool → List Nat → Option (List Bool × List Nat)
  | [], _, F, es => some (F, es)
  | n :: r, ds, F, es =>
    (chk c n F).bind fun x => if okAll ds x.1 es.length x.2 then lstA c r ds x.1 (es ++ x.2) else none
end

/-- one def with slot kinds `K`: its result kinds -/
def defOk (ps rs : List (List Nat)) (K : List Nat) (d : DefA) : Option (List Nat) :=
  if K.length = d.nslots ∧ d.npw ≤ d.nslots then
    let c : Cx := ⟨ps, rs, K, d.npw⟩
    let F0 := List.replicate d.nslots false
    let r := match d.body with
      | .loop z s =>
        (chk c z F0).bind fun z0 => (tr z0.1 z0.2).bind fun z1 =>
        (chk c s F0).bind fun s0 => (tr s0.1 s0.2).bind fun s1 => join z1.2 s1.2
      | b => (chk c b F0).bind fun x => (tr x.1 x.2).map fun (y : List Bool × List Nat) => y.2
    r.bind fun k => if k.length = d.nres then some k else none
  else none

/-- the program, defs in order, with per-def slot kinds `Ks` -/
def progOk : List (List Nat) → List (List Nat) → List (List Nat) → List DefA → Bool
  | _, _, [], [] => true
  | ps, rs, K :: Ks, d :: ds =>
    match defOk ps rs K d with
    | some R => progOk (ps ++ [K.take d.npw]) (rs ++ [R]) Ks ds
    | none => false
  | _, _, _, _ => false

/-- **the ownership discipline**: some slot kinds make every def pass the walk -/
def Linear (p : List DefA) : Prop := ∃ Ks, progOk [] [] Ks p = true

end OwnSpec
