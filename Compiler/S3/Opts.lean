/- Options of the S3 certificate tactics (opt-in; set by the generated certificate text of `s3_compileL`). -/
import Lean

register_option s3.limbCert : Bool := {
  defValue := false
  descr := "S3 certificates (limb mode): `s3_split` splits only the `if` conditions outside the alternatives of a \
    match before any variable (an `if` inside an unsplit match is otherwise split in every alternative's copy); \
    `s3_conj` also introduces the hypotheses of implications between conjunctions"
}
