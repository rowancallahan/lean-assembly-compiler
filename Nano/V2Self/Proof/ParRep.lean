/- Nano/V2Self/Proof/ParRep: how Par1's tables represent ParSpec's context `Cx` (definitions; the lookup lemmas `v7_lookup` / `v8_lookup` are in ParInv).
Shape codes: 1 UInt64, 2 Buf, 3 List UInt8 (value), 4 Nat (fuel), s ≥ 5: row s - 5 of the shape table at `d7 + 8192 + 3 (s - 5)` = (left code, right code, width).
Binding i (table d9, 4 words): name token position, slot, shape code, input flag.
Def i (table d7, 8 words): +0 name token position, +1 npw (parameter words), +2 number of NON-input parameters (the CALL argument count), +3 result shape code,
+4 loop flag, +5 start of its parameter-code list (cells `d7 + 4096 + start + j`), +6 source arity (all parameters incl. the input and, for loops, the fuel). -/
import Nano.V2Self.Proof.ParInv
namespace ParInv
open C BufL ParSpec

/-- the shape code `c` denotes the spec shape `s` in the shape table of `h` -/
inductive ShapeCode (h : Buf) : UInt64 → Sh → Prop
  | uw : ShapeCode h 1 .uw
  | bf : ShapeCode h 2 .bf
  | ls : ShapeCode h 3 .ls
  | nt : ShapeCode h 4 .nt
  | pr {c : UInt64} {l r : UInt64} {a b : Sh} :
      5 ≤ c.toNat → c.toNat < 5 + 8192 → bget h (d7 + 8192 + 3 * (c - 5)) = l → bget h (d7 + 8192 + 3 * (c - 5) + 1) = r →
      bget h (d7 + 8192 + 3 * (c - 5) + 2) = (a.width + b.width).toUInt64 →
      ShapeCode h l a → ShapeCode h r b → ShapeCode h c (.p a b)

/-- parameter / binding kind codes: the input is a List (3) with the input flag set, the fuel binder a Nat (4) -/
def PsCode (h : Buf) : Ps → UInt64 → UInt64 → Prop
  | .inp, c, f => c = 3 ∧ f = 1
  | .fuel, c, f => c = 4 ∧ f = 0
  | .sh s, c, f => ShapeCode h c s ∧ f = 0

/-- the binding table (depth h[4]) represents the spec environment (innermost entry LAST in the table; `ParSpec.Cx.env` has it FIRST) -/
def BindRep (h : Buf) (env : List (List Nat × Nat × Ps)) : Prop :=
  (bget h 4).toNat = env.length ∧
  ∀ (i : Nat) (hi : i < env.length),
    let e := env.reverse[i]'(by simpa using hi)
    ∃ pos nm, bget h (d9 + 4 * i.toUInt64) = pos ∧ NameOK h pos nm ∧ nm.map UInt64.toNat = e.1 ∧
      bget h (d9 + 4 * i.toUInt64 + 1) = e.2.1.toUInt64 ∧ PsCode h e.2.2 (bget h (d9 + 4 * i.toUInt64 + 2)) (bget h (d9 + 4 * i.toUInt64 + 3))

/-- the def table (count h[12]) represents the spec def list (earliest def first) -/
def DefRep (h : Buf) (defs : List DefI) : Prop :=
  (bget h 12).toNat = defs.length ∧
  ∀ (i : Nat) (hi : i < defs.length),
    let d := defs[i]
    ∃ pos nm, bget h (d7 + 8 * i.toUInt64) = pos ∧ NameOK h pos nm ∧ nm.map UInt64.toNat = d.name ∧
      bget h (d7 + 8 * i.toUInt64 + 1) = d.npw.toUInt64 ∧
      bget h (d7 + 8 * i.toUInt64 + 2) = (d.params.filter fun p => p != .inp).length.toUInt64 ∧
      (∃ s, ShapeCode h (bget h (d7 + 8 * i.toUInt64 + 3)) s ∧ s = d.res) ∧
      bget h (d7 + 8 * i.toUInt64 + 6) = d.params.length.toUInt64 ∧
      ∀ (j : Nat) (hj : j < d.params.length),
        ∃ f, PsCode h d.params[j] (bget h (d7 + 4096 + (bget h (d7 + 8 * i.toUInt64 + 5)) + j.toUInt64)) f

/-- the context relation: tables ↔ `Cx` -/
def CxRep (h : Buf) (cx : Cx) : Prop := BindRep h cx.env ∧ DefRep h cx.defs

end ParInv
