/- The simp set `s3_norm`: normal forms of word facts shared by S3 certificate goals and their hypotheses. -/
import Lean
register_simp_attr s3_norm
/-- opt-in byte normal forms (`s3_compileB`, `s3_solveB`): `Compiler/S3/Cert.lean` -/
register_simp_attr s3_bytes
/-- the split depth of the S3 certificate tactic (`s3_solve n`), default 12 -/
register_option s3.depth : Nat := { defValue := 12, descr := "S3 certificate split depth" }
