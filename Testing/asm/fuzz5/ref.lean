/- Reference for fuzz5: the verbatim source functions of `Riscv/Frontx/IndExamples.lean` (fp-lean @0abeea5, core
`List.append`, con-leche `Level`), run by `lean --run`.  Stdin lines: `fn hex` (input bytes: one value, or two values
one after another); stdout: hex of the result bytes (tree/list/Pos: tag-byte format; Nat: 8 bytes LE mod 2^64; Bool:
1 byte).  The decoders here are written independently of `Compiler/IndDec.lean`; they assert that all bytes are used. -/
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
def BinTree.graftLeft (root newBranch : BinTree α) : BinTree α :=
  match root with
  | .leaf => newBranch
  | .branch l x r => .branch (l.graftLeft newBranch) x r
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs
def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs
def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs
def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs
inductive Level where
  | zero
  | succ (u : Level)
  | max (u v : Level)
  | imax (u v : Level)
  | param (n : String)
def levelHasParam : Level → Bool
  | .zero => false
  | .param _ => true
  | .succ u => levelHasParam u
  | .max u v | .imax u v => levelHasParam u || levelHasParam v
def Level.isNeverZero : Level → Bool
  | .zero => false
  | .param _ => false
  | .succ _ => true
  | .max l r => isNeverZero l || isNeverZero r
  | .imax _ r => isNeverZero r

instance : Inhabited (BinTree α) := ⟨.leaf⟩
instance : Inhabited Pos := ⟨.one⟩
instance : Inhabited Level := ⟨.zero⟩
abbrev D := StateM (ByteArray × Nat)
def byte : D UInt8 := do
  let (b, i) ← get
  assert! i < b.size
  set (b, i + 1); return b[i]!
def word : D Nat := do
  let mut v := 0
  for k in [0:8] do v := v + (← byte).toNat <<< (8 * k)
  return v
partial def dT : D (BinTree Nat) := do
  match (← byte) with
  | 0 => return .leaf
  | 1 => let l ← dT; let x ← word; let r ← dT; return .branch l x r
  | t => panic! s!"tree tag {t}"
partial def dP : D Pos := do
  match (← byte) with | 0 => return .one | 1 => return .succ (← dP) | t => panic! s!"pos tag {t}"
partial def dL : D (List Nat) := do
  match (← byte) with
  | 0 => return []
  | 1 => let x ← word; let t ← dL; return x :: t
  | t => panic! s!"list tag {t}"
partial def dV : D Level := do
  match (← byte) with
  | 0 => return .zero | 1 => return .succ (← dV)
  | 2 => let a ← dV; let b ← dV; return .max a b
  | 3 => let a ← dV; let b ← dV; return .imax a b
  | 4 => return .param ""
  | t => panic! s!"level tag {t}"
partial def eT : BinTree Nat → Array UInt8 → Array UInt8
  | .leaf, o => o.push 0
  | .branch l x r, o => let o := eT l (o.push 1); let o := (List.range 8).foldl (fun o k => o.push (UInt8.ofNat (x >>> (8 * k)))) o; eT r o
partial def eP : Pos → Array UInt8 → Array UInt8
  | .one, o => o.push 0 | .succ p, o => eP p (o.push 1)
partial def eL : List Nat → Array UInt8 → Array UInt8
  | [], o => o.push 0
  | x :: t, o => eL t ((List.range 8).foldl (fun o k => o.push (UInt8.ofNat (x >>> (8 * k)))) (o.push 1))
def natB (n : Nat) : Array UInt8 := (List.range 8).foldl (fun o k => o.push (UInt8.ofNat (n >>> (8 * k)))) #[]
def hex (a : Array UInt8) : String := String.join (a.toList.map fun b =>
  let d := "0123456789abcdef".toList; s!"{d[b.toNat / 16]!}{d[b.toNat % 16]!}")
def unhex (s : String) : ByteArray :=
  let cs := s.toList.toArray
  let v := fun (c : Char) => if c.toNat ≥ 97 then c.toNat - 87 else c.toNat - 48
  ⟨(Array.range (cs.size / 2)).map fun i => UInt8.ofNat (v cs[2*i]! * 16 + v cs[2*i+1]!)⟩
def run (fn : String) (bs : ByteArray) : String :=
  let fin {α} (a : α × ByteArray × Nat) (k : α → Array UInt8) : String :=
    if a.2.2 != a.2.1.size then panic! "trailing bytes" else hex (k a.1)
  let go {α β} (d : D α) (f : α → β) (k : β → Array UInt8) := fin ((do let a ← d; pure a : D α).run (bs, 0) |> fun (a, s) => (f a, s)) k
  match fn with
  | "bt_count" => go dT BinTree.count natB
  | "bt_mirror" => go dT BinTree.mirror (eT · #[])
  | "bt_graftleft" => go (do let a ← dT; let b ← dT; pure (a, b)) (fun p => p.1.graftLeft p.2) (eT · #[])
  | "pos_tonat" => go dP Pos.toNat natB
  | "pos_plus" => go (do let a ← dP; let b ← dP; pure (a, b)) (fun p => p.1.plus p.2) (eP · #[])
  | "nontail_sum_ln" => go dL NonTail.sum natB
  | "tail_sum_ln" => go dL Tail.sum natB
  | "tail_reverse_ln" => go dL Tail.reverse (eL · #[])
  | "list_append_ln" => go (do let a ← dL; let b ← dL; pure (a, b)) (fun p => List.append p.1 p.2) (eL · #[])
  | "level_hasparam" => go dV levelHasParam fun b => #[if b then 1 else 0]
  | "level_isneverzero" => go dV Level.isNeverZero fun b => #[if b then 1 else 0]
  | _ => panic! s!"unknown {fn}"
def main : IO Unit := do
  let h ← IO.getStdin
  repeat
    let l ← h.getLine
    if l.isEmpty then break
    match l.trimAscii.toString.splitOn " " with
    | [fn, x] => IO.println (run fn (unhex (if x == "-" then "" else x)))
    | _ => panic! "bad line"
