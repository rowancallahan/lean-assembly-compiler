/- Function-level equations for the certificate (gen_cert.py FUNEQ): `rw` with these instead of delta-unfolding the def,
so the kernel never whnf's a `let (a, b) := g19/g20 …` match (NANO_V2_CG.md "KERNEL TRAP").  RHS = the source text. -/
import Nano.V2Self.C.Gen
namespace Cert
open C

theorem g56_fun : g56 = fun r o t =>
  if bget r 5 == 1 then (r, o) else
  if bget r 4 == 1 then (r, o) else
  if 16777215 < bsize o then (g16 r, o) else
  let w := bsize t;
  if w == 0 then (g16 r, o) else
  let m := (if bget r 1 == 0 then (if bget r 2 == 1 then g_1 else g_0) else g_0);
  if m == 0 then (g16 r, o) else
  let (r1, o1) := g20 r o 0;
  let (r2, o2) := g35 r1 o1 (bget t (w - 1));
  (g15 r2 5 1, o2) := by
  delta g56
  exact rfl

end Cert
