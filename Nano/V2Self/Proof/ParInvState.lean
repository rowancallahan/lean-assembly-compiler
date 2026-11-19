/- Nano/V2Self/Proof/ParInvState: Layer 3 — the full machine ↔ Layer-2 invariant `Rep h ts st fs` (box C; box D builds on it).
`h` = Par1's heap, `ts` = the token words, `st : ParRun.St` and `fs : List ParRun.Frame` (TOP FIRST) = box B's abstract machine.
Every `St` field has its cells (see ParRun's header); frames ↔ task records (code, a, b) per constructor (`FrameArgs`).
Preservation lemmas have the shape `Rep h ts st (f :: fs) → bget (step h) 0 ≠ 0 → ∃ k st', stepF f st = some (k, st') ∧
Rep (step h) ts st' (k ++ fs)` (machine success ⇒ Layer-2 success, soundness direction only). -/
import Nano.V2Self.Proof.ParInvOps
namespace ParInv
open C BufL ParSpec ParRun

/-- a Bool as the machine's 0/1 word -/
def b01 (b : Bool) : UInt64 := if b then 1 else 0

/-- the `a` word of a call task: a def row j, or `512 + p` for prim p -/
def calleeW : Callee → UInt64
  | .df j => j.toUInt64
  | .pr p => (512 + p).toUInt64

/-- the identifier token at `pos` spells `x` -/
def NameAt (h : Buf) (pos : UInt64) (x : List Nat) : Prop := ∃ nm, NameOK h pos nm ∧ nm.map UInt64.toNat = x

/-- the `a` / `b` words of a task record for each frame (the code is `Frame.code`) -/
def FrameArgs (h : Buf) (arena : List RN) : Frame → UInt64 → UInt64 → Prop
  | .expr m md, a, b => a.toNat = m ∧ b.toNat = md
  | .binLoop m, a, _ => a.toNat = m
  | .prim md, _, b => b.toNat = md
  | .rparen, _, _ => True
  | .mkBin op, a, _ => a.toNat = op
  | .ifCmp tl, _, b => b = b01 tl
  | .ifThen c tl, a, b => a.toNat = c ∧ b = b01 tl
  | .ifElse, _, _ => True
  | .mkIte c, a, _ => a.toNat = c
  | .letSemi x tl, a, b => NameAt h a x ∧ b = b01 tl
  | .letEnd s d, a, b => a = s.toUInt64 ∧ b.toNat = d
  | .parenClose, _, _ => True
  | .letStart tl, _, b => b = b01 tl
  | .mkPair, _, _ => True
  | .argAtom, _, _ => True
  | .args c k, a, b => a = calleeW c ∧ b.toNat = k
  | .mkCallN c d, a, b => a = calleeW c ∧ b.toNat = d
  | .selfArgs, _, _ => True
  | .argCheck c k, a, b => a = calleeW c ∧ b.toNat = k
  | .mkCall c n, a, b => a = calleeW c ∧ b.toNat = n
  | .shiftNum op, a, _ => a.toNat = op
  | .letPairX tl, _, b => b = b01 tl
  | .letPairY x tl, a, b => NameAt h a x ∧ b = b01 tl
  | .stash x, a, _ => NameAt h a x
  | .letPairSemi y tl, a, b => NameAt h a y ∧ b = b01 tl
  | .mkCont f k, a, b => a.toNat = f ∧ b.toNat = k
  | .argName, _, _ => True
  | .defs, _, _ => True
  | .tyAtom, _, _ => True
  | .tyCross, _, _ => True
  | .tyPair l, a, _ => ShapeCode h a l
  | .binders, _, _ => True
  | .group s, a, _ => a.toNat = s
  | .assign i sz, a, b => a.toNat = i ∧ b.toNat = sz
  | .plainBody, _, _ => True
  | .afterColon, _, _ => True
  | .stateTy, _, _ => True
  | .armsStart, _, _ => True
  | .armBind stp i, a, b => a = b01 stp ∧ b.toNat = i
  | .zeroDone, _, _ => True
  | .mkLoop, _, _ => True
  | .defEnd, _, _ => True
  | .flat n, a, _ => ∃ ids, RNRep h a n ids ∧ ∀ v ∈ ids, v.toNat < arena.length
  | .flatL ns, a, b => b.toNat = ns.length ∧ ∃ ids, KidsR h a ns ids ∧ ∀ v ∈ ids, v.toNat < arena.length
  | .defClose, _, _ => True
  | .tupRest, _, _ => True

/-- the task stack (count h[5], records of 3 words at d1 + 3i, bottom first) ↔ `fs` (TOP FIRST) -/
def TasksRep (h : Buf) (arena : List RN) (fs : List Frame) : Prop :=
  (bget h 5).toNat = fs.length ∧ fs.length ≤ 4096 ∧
  ∀ k (hk : k < fs.length), let t := taskAt h (fs.length - 1 - k)
    t.code = (fs[k]'hk).code.toUInt64 ∧ FrameArgs h arena (fs[k]'hk) t.a t.b

/-- binding table (count h[4], rows of 4 words at d9 + 4i): name position, slot, shape code (0 = untyped), input flag -/
def BindsRep (h : Buf) (bs : List Bd) : Prop :=
  (bget h 4).toNat = bs.length ∧ bs.length ≤ 1024 ∧
  ∀ i (hi : i < bs.length), let r := d9 + 4 * i.toUInt64; let bd := bs[i]'hi
    NameAt h (bget h r) bd.name ∧ bget h (r + 1) = bd.slot.toUInt64 ∧ ShOpt h (bget h (r + 2)) bd.sh ∧ bget h (r + 3) = b01 bd.inp

/-- def row j (8 words at d7 + 8j) ↔ `d`; parameter codes at d7 + 4096 + start + i -/
def RowRep (h : Buf) (j : Nat) (d : DefR) : Prop :=
  let r := d7 + 8 * j.toUInt64
  NameAt h (bget h r) d.name ∧ bget h (r + 1) = d.npw.toUInt64 ∧ (bget h (r + 2)).toNat = d.nni ∧ ShOpt h (bget h (r + 3)) d.res ∧
  bget h (r + 4) = b01 d.loop ∧ (bget h (r + 6)).toNat = d.params.length ∧ (bget h (r + 5)).toNat + d.params.length ≤ 4096 ∧
  ∀ i (hi : i < d.params.length), ShapeCode h (bget h (d7 + 4096 + bget h (r + 5) + i.toUInt64)) (d.params[i]'hi)

def RowZero (h : Buf) (j : Nat) : Prop := ∀ k : UInt64, k.toNat < 8 → bget h (d7 + 8 * j.toUInt64 + k) = 0

/-- the shape table: h[26] rows allocated (≤ 8192); every row from h[26] on has a zero left cell, so no shape code refers to it -/
def ShRows (h : Buf) : Prop :=
  (bget h 26).toNat ≤ 8192 ∧ (∀ k : Nat, (bget h 26).toNat ≤ k → k < 8192 → bget h (d7 + 8192 + 3 * k.toUInt64) = 0) ∧
  -- every allocated row decodes, and has no Nat component (v10 may return an existing row: its code must be a `ShapeCode`)
  ∀ k : Nat, k < (bget h 26).toNat → ∃ l r, ShapeCode h (bget h (d7 + 8192 + 3 * k.toUInt64)) l ∧
    ShapeCode h (bget h (d7 + 8192 + 3 * k.toUInt64 + 1)) r ∧
    bget h (d7 + 8192 + 3 * k.toUInt64 + 2) = (l.width + r.width).toUInt64 ∧ l ≠ .nt ∧ r ≠ .nt

/-- the def table: finished rows, the current row (inside a def) or a zero row (between defs), zero rows above; h[27] = next free
parameter cell, above every row's parameter list -/
def DefsRep (h : Buf) (st : St) (inDef : Bool) : Prop :=
  (bget h 12).toNat = st.defs.length ∧ st.defs.length ≤ 512 ∧ (bget h 27).toNat ≤ 4096 ∧
  (∀ j (hj : j < st.defs.length), RowRep h j (st.defs[j]'hj) ∧
      (bget h (d7 + 8 * j.toUInt64 + 5)).toNat + (st.defs[j]'hj).params.length ≤ (bget h 27).toNat) ∧
  (if inDef then (RowRep h st.defs.length st.cur ∧
      (bget h (d7 + 8 * st.defs.length.toUInt64 + 5)).toNat + st.cur.params.length = (bget h 27).toNat) ∧ st.defs.length < 512
    else st.defs.length < 512 → RowZero h st.defs.length) ∧
  (∀ j, st.defs.length < j → j < 512 → RowZero h j) ∧
  (∀ i : Nat, (bget h 27).toNat ≤ i → i < 4096 → bget h (d7 + 4096 + i.toUInt64) = 0) ∧
  ShRows h



/-- the emitted words follow the token sentinel 0 at the end of the heap -/
def OutRep (h : Buf) (ts : Buf) (out : List UInt64) : Prop :=
  h.length = 184384 + ts.length + 1 + out.length ∧ h.drop (184384 + ts.length + 1) = out

def _root_.ParRun.Frame.isDefs : Frame → Bool
  | .defs => true
  | _ => false

/-- inside a def: no `defs` frame on the stack (between defs — top frame `defs` — the current row is still zero) -/
def inDefF (fs : List Frame) : Bool := fs.all fun f => !f.isDefs

/-- **the invariant** -/
def Rep (h : Buf) (ts : Buf) (st : St) (fs : List Frame) : Prop :=
  TokensAt h ts ∧ ts.length < 2 ^ 24 ∧
  bget h 0 = (if st.acc then 2 else 1) ∧
  TokAt h (bget h 3) st.toks ∧
  bget h 11 = st.nx.toUInt64 ∧
  BindsRep h st.binds ∧
  DefsRep h st (inDefF fs) ∧
  ArenaRep h st.arena st.vals ∧
  (∀ s, st.ty = some s → ShapeCode h (bget h 25) s) ∧
  (∀ x, st.stash = some x → NameAt h (bget h 29) x) ∧
  bget h 30 = b01 st.arm ∧
  bget h 32 = st.sslot.toUInt64 ∧
  OutRep h ts st.out ∧
  TasksRep h st.arena fs

end ParInv
