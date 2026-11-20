/- Machine bridge (Opus box E): the program level on the J machine.  `semAt P ds k` = the semantics of def k of the
resolved program `ds` (ParSpec.DefA list, callee before caller): `defS` of its body's `sv` in the context `scAt`
whose callees are the defs below k.  `progRun`: if every def's template sits at its start word `P.T k` and meets the
side conditions, every def satisfies the def contract `DefX` (strong induction on k = call-graph order). -/
import Nano.V2Self.Proof.Machine.NdDef
namespace Templates
open CallProbe ParSpec

abbrev SemD := List UInt64 → Nat → Hp → Option (List UInt64 × Hp)

def dflt : SemD := fun _ _ _ => none

/-- program-wide constants: κ, heap base, input, def start words -/
structure PC where
  κ : Nat
  hb : Nat
  c29 : UInt64
  inp : Nat → UInt64
  T : Nat → Nat

def dA (ds : List DefA) (n : Nat) : DefA := ds.getD n ⟨0, 0, 0, 0, 0, .const 0⟩

def semAt (P : PC) (ds : List DefA) (k : Nat) : SemD :=
  defS (dA ds k).npw (dA ds k).nslots (sv ⟨(dA ds k).npw, (dA ds k).nslots, P.κ, P.hb, P.c29, P.inp,
    fun n => if _h : n < k then semAt P ds n else dflt, fun n => (dA ds n).npw, fun n => (dA ds n).nres, P.T, k,
    (dA ds k).nres⟩ (dA ds k).body)
termination_by k

/-- the template context of def k -/
def scAt (P : PC) (ds : List DefA) (k : Nat) : SC :=
  ⟨(dA ds k).npw, (dA ds k).nslots, P.κ, P.hb, P.c29, P.inp,
    fun n => if _h : n < k then semAt P ds n else dflt, fun n => (dA ds n).npw, fun n => (dA ds n).nres, P.T, k,
    (dA ds k).nres⟩

theorem semAt_eq (P : PC) (ds : List DefA) (k : Nat) :
    semAt P ds k = defS (dA ds k).npw (dA ds k).nslots (sv (scAt P ds k) (dA ds k).body) := by
  rw [semAt]; rfl

/-- the per-def facts the node theorem needs -/
structure DefOK (P : PC) (ds : List DefA) (C : List J) (k : Nat) : Prop where
  p20 : (dA ds k).npw < 2 ^ 20
  pn : (dA ds k).npw ≤ (dA ds k).nslots
  ok : OkV (scAt P ds k) (dA ds k).body
  wd : wd (scAt P ds k) (dA ds k).body = (dA ds k).nres
  rd : ∀ j, rd (dA ds k).body j → j < (dA ds k).npw
  at_ : At C (P.T k) (defT (scAt P ds k) (dA ds k).body (P.T k) (dA ds k).nres)

end Templates
