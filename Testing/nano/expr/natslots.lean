import Nano.Parser.NumSpec
/-! natslots.lean SRC... : E's Nat-slot algorithm (linear passes, Testing/notes/EXPR.md §7), written over `Nd`, against
`NumSpec.slotNat` on every slot of every def. Prints the differing (program, def, slot) triples and a total. -/
open ParSpec

namespace NatE
mutual
/-- pass A: literal-only flag of a node, with the per-slot literal env threaded in pre-order -/
partial def isLA (ws : List Nat) (e : Nd) : StateM (Array Bool) Bool := do
  match e with
  | .const _ => pure true
  | .loc s w => pure (w == 1 && (← get).getD s false)
  | .bin op a b => do let x ← isLA ws a; let y ← isLA ws b; pure (!NumSpec.isShift op && x && y)
  | .ite _ a b t el => do let _ ← isLA ws a; let _ ← isLA ws b; let x ← isLA ws t; let y ← isLA ws el; pure (x && y)
  | .letE s w v b => do
    let lv ← isLA ws v
    let wd : List Bool ← words ws w lv v
    modify fun env => (List.range wd.length).foldl (fun env i => env.setIfInBounds (s + i) (wd.getD i false)) env
    isLA ws b
  | .pair cs => do for c in cs do let _ ← isLA ws c
                   pure false
  | .call _ as | .prim _ as => do for c in as do let _ ← isLA ws c
                                  pure false
  | .loop z s => do let _ ← isLA ws z; let _ ← isLA ws s; pure false
  | .cont c => do let _ ← isLA ws c; pure false
/-- the per-word literal flags of a value of width w (lv: its literal-only flag) -/
partial def words (ws : List Nat) (w : Nat) (lv : Bool) (v : Nd) : StateM (Array Bool) (List Bool) := do
  match v with
  | .pair cs => do
    let mut r : List Bool := []
    for c in cs do
      let env ← get
      let lc := (isLA ws c).run' env
      r := r ++ (← words ws 1 lc c)
    pure r
  | .loc s w' => do let env ← get; pure ((List.range w').map fun i => env.getD (s + i) false)
  | _ => pure (if w == 1 then [lv] else List.replicate w false)
end
end NatE

/-- E's algorithm state -/
structure St where
  env : Array Bool
  pairs : List (Nat × Nat)      -- (slot, group)
  seeds : List Nat              -- groups with demand UInt64
  ng : Nat                      -- next group id

open NatE

def isLS (ws : List Nat) (x : Nd) : StateM St Bool := do let st ← get; pure ((isLA ws x).run' st.env)
def newG : StateM St Nat := do let st ← get; set { st with ng := st.ng + 1 }; pure st.ng
def envSet (ws : List Nat) (s w : Nat) (v : Nd) : StateM St Unit := do
  let st ← get
  let (wd, env) := ((do let lv ← isLA ws v; words ws w lv v) : StateM (Array Bool) _).run st.env
  set { st with env := (List.range wd.length).foldl (fun env i => env.setIfInBounds (s + i) (wd.getD i false)) env }

mutual
partial def lit (ks ws : List Nat) (g : Nat) (e : Nd) : StateM St Unit := do
  match e with
  | .loc s _ => modify fun st => { st with pairs := (s, g) :: st.pairs }
  | .bin _ a b => do lit ks ws g a; lit ks ws g b
  | .ite _ a b t el => do cmp ks ws a b; lit ks ws g t; lit ks ws g el
  | .letE s w v b => do letG ks ws s w v; envSet ws s w v; lit ks ws g b
  | _ => pure ()
partial def col (ks ws : List Nat) (d : Nat) (e : Nd) : StateM St Unit := do
  if ← isLS ws e then
    let g ← newG
    if d == 1 then modify fun st => { st with seeds := g :: st.seeds }
    lit ks ws g e
  else match e with
  | .bin _ a b => do col ks ws 1 a; col ks ws 1 b
  | .ite _ a b t el => do cmp ks ws a b; col ks ws 1 t; col ks ws 1 el
  | .letE s w v b => do letG ks ws s w v; envSet ws s w v; col ks ws d b
  | .pair cs => for c in cs do col ks ws 1 c
  | .call id as => for (a, i) in as.zipIdx do col ks ws (if ks.getD id 0 == 1 && i == 0 then 2 else 1) a
  | .prim _ as => for a in as do col ks ws 1 a
  | .loop z s => do col ks ws 1 z; col ks ws 1 s
  | .cont c => col ks ws 1 c
  | _ => pure ()
partial def cmp (ks ws : List Nat) (a b : Nd) : StateM St Unit := do
  if (← isLS ws a) && (← isLS ws b) then let g ← newG; lit ks ws g a; lit ks ws g b
  else do col ks ws 1 a; col ks ws 1 b
partial def letG (ks ws : List Nat) (s _w : Nat) (v : Nd) : StateM St Unit := do
  match v with
  | .pair cs => for (c, i) in cs.zipIdx do
      if ← isLS ws c then let g ← newG; modify (fun st => { st with pairs := (s + i, g) :: st.pairs }); lit ks ws g c
      else col ks ws 0 c
  | _ => if ← isLS ws v then let g ← newG; modify (fun st => { st with pairs := (s, g) :: st.pairs }); lit ks ws g v
         else col ks ws 0 v
end

def natE (ks ws : List Nat) (df : DefA) : List Nat :=
  let st := ((col ks ws 1 df.body).run { env := Array.replicate (df.nslots + 8) false, pairs := [], seeds := [], ng := 0 }).2
  let n := df.nslots + 1
  let (_, ms) := (List.range (n + 2)).foldl (fun (mg, ms) _ =>
      let mg := st.pairs.foldl (fun mg (s, g) => if ms.contains s then mg.insert g else mg) mg
      let ms := st.pairs.foldl (fun ms (s, g) => if mg.contains g then ms.insert s else ms) ms
      (mg, ms)) (st.seeds, ([] : List Nat))
  (List.range n).filter fun s => st.pairs.any (·.1 == s) && !ms.contains s

def main (args : List String) : IO Unit := do
  let mut bad := 0
  let mut tot := 0
  for f in args do
    let src ← IO.FS.readBinFile f
    let some ws := lexAll (src.size + 1) src.toList | continue
    let some p := refParse ws | continue
    let ks := p.map (·.kind); let wss := p.map (·.nres)
    for df in p do
      let a := (List.range (df.nslots + 1)).filter (NumSpec.slotNat ks wss df)
      let b := natE ks wss df
      tot := tot + a.length
      if a != b then bad := bad + 1; IO.println s!"{f} def {df.id}: spec {a} E {b}"
  IO.println s!"nat slots {tot}, differing defs {bad}"
