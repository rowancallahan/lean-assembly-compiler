import Nano.V2Self.C.Gen
/- Def map of g41's code: a copy of C.g39 that also returns `t` (def entry word offsets).  Prints `id word_offset`
per def, so a QEMU pc (base + 4·offset of `func`) can be traced to its def.  run: lean --run cg_map.lean AST.bin -/
def rdw (b : ByteArray) (i : Nat) : UInt64 :=
  (List.range 8).foldl (fun a k => a ||| ((b.get! (8*i+k)).toUInt64 <<< (8*k).toUInt64)) 0
def loop : Nat → Buf → Buf → Buf → Buf → Buf → Buf → Buf × Buf
  | 0, _, r, _, _, t, _ => (r, t)
  | n + 1, x, r, o, k, t, f =>
    if bget r 5 == 1 then (r, t) else if bget r 4 == 1 then (r, t) else
    if bget r 6 == 0 then
      if bget r 0 < bsize x then
        let (r1, (o1, (k1, t1))) := C.g38 x r o k t
        loop n x r1 o1 k1 t1 f
      else (C.g15 r 5 1, t)
    else
      let (r1, (o1, (k1, f1))) := C.g37 x r o k t f
      loop n x r1 o1 k1 t f1
def main (args : List String) : IO Unit := do
  let b ← IO.FS.readBinFile (args.headD "Testing/nano/v2self/self_S_ast.bin")
  let x : List UInt64 := (List.range (b.size / 8)).map (rdw b)
  let r := bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) C.g_999
  let (r1, t) := loop 16777216 x r (C.g34 bnew) bnew bnew bnew
  IO.println s!"err {bget r1 4}"
  for (a, i) in t.zipIdx do IO.println s!"{i} {a}"
