/- Nano/V2Self/Proof/Tests/SelfInWitness: the input type `SelfIn` of the self-application theorems is INHABITED
(audit finding: non-vacuity).  The witness is the empty input: C's own text, run by `Sem` on `[]`, returns the empty
output and no buffer reaches its capacity (`Cert.CapFree.sem_nil`, Tests/SelfInPath). -/
import Nano.V2Self.Proof.Tests.SelfInPath
import Nano.V2Self.Proof.Main.SelfLink

open NanoMain

theorem selfIn_nonempty : Nonempty SelfIn :=
  ⟨⟨[], by decide, by rw [Cert.CapFree.sem_nil]; exact fun h => nomatch h⟩⟩

#print axioms selfIn_nonempty
