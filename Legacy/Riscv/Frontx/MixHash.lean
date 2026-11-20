/- `mixHash` (Lean 4.29.0 core, `Init/Prelude.lean`: `@[extern "lean_uint64_mix_hash"] opaque mixHash`): its C code,
`lean_uint64_mix_hash` in `include/lean/lean.h:1952` (Lean 4.29.0), written in Lean as `mixHashLean`.
`mixHashE` is the entry glue (the two words of the input, as in `Ops.ops64E`); `wa_compile` compiles `mixHashLean`
verbatim through it.  The fuzz (`fuzzRun`) compares `mixHashLean` with the native `mixHash`. -/
import Legacy.Riscv.Frontx.WaMul

-- outside `Proven`: `wa_compile` unfolds helpers outside `Proven` only (as `WaGlue` in `WaMul.lean`)
namespace MixHashPort

def mixHashLean (h k : UInt64) : UInt64 :=
  let m : UInt64 := 0xc6a4a7935bd1e995
  let r : UInt64 := 47
  let k1 := k * m
  let k2 := k1 ^^^ (k1 >>> r)
  let k3 := k2 ^^^ m
  let h1 := h ^^^ k3
  h1 * m

end MixHashPort

namespace Proven.WA.MixHash
open Proven.WA WaGlue MixHashPort

/-- `mixHashLean` against the native `mixHash` (C code): the edge values pairwise, then `n` random pairs
(xorshift64, fixed seed).  Throws on any mismatch. -/
def fuzzRun (n : Nat) : IO Unit := do
  let edges : List UInt64 := [0, 1, 9223372036854775808, 18446744073709551615, 0xc6a4a7935bd1e995]
  let mut tested := 0
  let mut bad := 0
  for h in edges do
    for k in edges do
      tested := tested + 1
      if mixHash h k != mixHashLean h k then
        bad := bad + 1
        IO.println s!"MISMATCH (edge) h={h} k={k} native={mixHash h k} lean={mixHashLean h k}"
  let mut s : UInt64 := 0x9E3779B97F4A7C15
  for _ in [0:n] do
    s := s ^^^ (s <<< 13)
    s := s ^^^ (s >>> 7)
    s := s ^^^ (s <<< 17)
    let h := s
    s := s ^^^ (s <<< 13)
    s := s ^^^ (s >>> 7)
    s := s ^^^ (s <<< 17)
    let k := s
    tested := tested + 1
    if mixHash h k != mixHashLean h k then
      bad := bad + 1
      IO.println s!"MISMATCH h={h} k={k} native={mixHash h k} lean={mixHashLean h k}"
  IO.println s!"mixHash fuzz: tested={tested} mismatches={bad}"
  unless bad == 0 do throw (IO.userError s!"{bad} mismatches")

#eval fuzzRun 1000000

/-- `mixHashLean` of the two little-endian words at bytes 0 and 8 (the input has at least 16 bytes) -/
def mixHashE (xs : ByteArray) : UInt64 := mixHashLean (rd64 xs 0) (rd64 xs 8)
wa_compile mixHashE

end Proven.WA.MixHash
