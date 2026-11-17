import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
@[simp] theorem u64_toUInt8_bv (y : UInt64) : (y.toUInt8).toBitVec.setWidth 64 = y.toBitVec &&& 255 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and]
  omega
@[simp] theorem u8_toUInt64_bv (a : UInt8) : a.toUInt64.toBitVec = a.toBitVec.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp
def a3 (bs : List UInt8) : List UInt8 := match bs with | a :: _ => Nano.mo 6 ((a.toUInt64 >>> 8).toUInt8) | [] => []
end P
open P
namespace Q
open Proven.S3
abbrev S : Proven.S3.Sig := ⟨[[[], [.w, (.d 0)]]], [([(.d 0)], (.d 0)), ([.w, .w], (.d 0))]⟩
def b0 : Proven.S3.Expr S [(.d 0)] (.d 0) :=
  (.cas (i := 0) .z (Alts.arms (.cons (.mk 0 0 .nil) (.cons (.let_ (σ := .w) (.lit 6) (.let_ (σ := .w) (.let_ (σ := .w) (.let_ (σ := .w) (.var (.s .z)) (.let_ (σ := .w) (.lit 8) (.bin (.op .lshr) (.s .z) .z))) (.let_ (σ := .w) (.lit 255) (.bin (.op .and) (.s .z) .z))) (.call ⟨1, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) .nil))))
def b1 : Proven.S3.Expr S [.w, .w] (.d 0) :=
  (.let_ (σ := (.d 0)) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s (.s .z)) (.cons .z .nil)))) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))
abbrev P : Proven.S3.Prog := ⟨S, (.cons b0 (.cons b1 .nil)), ⟨0, by decide⟩⟩
def φ : Fin P.S.fns.length → List Proven.S3.V → Proven.S3.V := fun f vs => match f.val with
  | 0 => Proven.S3.Enc.enc ((P.a3) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 1 => Proven.S3.Enc.enc ((Nano.mo) (Proven.S3.Enc.dec (vs.getD 0 default) : (UInt8)) (Proven.S3.Enc.dec (vs.getD 1 default) : (UInt8)))
  | _ => default
theorem body1 : P.body ⟨1, by decide⟩ = b1 := rfl
theorem phi1 : ∀ (x0 : (UInt8)) (x1 : (UInt8)), φ ⟨1, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((Nano.mo) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert1 : ∀ (x0 : (UInt8)) (x1 : (UInt8)), Proven.S3.Good P φ ⟨1, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  intro x0 x1
  (
  (apply Proven.S3.good_intro <;> rw [body1]) <;> (try rw [phi1]) <;> (try rw [Nano.mo.eq_def]) <;>
  s3_solve 12 [Proven.S3.evalO, Proven.S3.CallsOk, Proven.S3.Var.idx, Proven.S3.Alts.arms, Proven.S3.Vars.get, Proven.S3.Vars.idxs, Proven.S3.Prim.eval, Proven.Op.eval, Proven.S3.Cmp.eval, Proven.S3.Sig.nc, Proven.S3.Sig.fld, Proven.S3.Sig.dt, Proven.S3.lget, -Fin.isValue, b1, φ, *] with (first | assumption | (intros; assumption) | omega))
theorem cert1' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (UInt8)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (UInt8)) = v1 → Proven.S3.Good P φ ⟨1, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert1 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body0 : P.body ⟨0, by decide⟩ = b0 := rfl
theorem phi0 : ∀ (x0 : (List UInt8)), φ ⟨0, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((P.a3) x0) := by
  intro x0
  simp [φ]
theorem cert0 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨0, by decide⟩ [Proven.S3.Enc.enc x0] := by
  intro x0
  apply Proven.S3.good_intro <;> rw [body0] <;> (try rw [phi0]) <;> (try rw [P.a3.eq_def])
  · simp [s3_norm, Proven.S3.evalO, Proven.S3.CallsOk, Proven.S3.Var.idx, Proven.S3.Alts.arms, Proven.S3.Vars.get, Proven.S3.Vars.idxs, Proven.S3.Prim.eval, Proven.Op.eval, Proven.S3.Cmp.eval, Proven.S3.Sig.nc, Proven.S3.Sig.fld, Proven.S3.Sig.dt, Proven.S3.lget, -Fin.isValue, b0, φ, *]
    cases x0 <;> simp [s3_norm, Proven.S3.evalO, Proven.S3.CallsOk, Proven.S3.Var.idx, Proven.S3.Alts.arms, Proven.S3.Vars.get, Proven.S3.Vars.idxs, Proven.S3.Prim.eval, Proven.Op.eval, Proven.S3.Cmp.eval, Proven.S3.Sig.nc, Proven.S3.Sig.fld, Proven.S3.Sig.dt, Proven.S3.lget, -Fin.isValue, b0, φ, *]
    trace_state
    all_goals sorry
  all_goals sorry
theorem cert0' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨0, by decide⟩ [v0] := by
  intro v0 h0
  have := cert0 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem main_good : ∀ bs : List UInt8, Proven.S3.Good P φ P.main [Proven.S3.Enc.enc bs] := cert0
/-- **termination**: from `main` on every input, the call tree is well-founded (from the certificates, i.e. from Lean's own induction principles) -/
theorem wf : Proven.S3.WfCert P (fun f vs => f = P.main ∧ ∃ bs : List UInt8, vs = [Proven.S3.Enc.enc bs]) :=
  ⟨fun f vs ⟨hf, bs, hv⟩ => by subst hf hv; exact Proven.S3.acc_of_ev (main_good bs)⟩
/-- **the bridge**: the S3 program computes `main` on bytes -/
theorem computes : Proven.Top.Computes P (P.a3) id id :=
  Proven.S3.computes_of_main (P.a3) id id (P.a3) (fun _ => rfl) (fun bs => phi0 bs) main_good
/-- **the machine theorem**: the compiled code computes `main` (`Compiler/AllocSpec.lean`) -/
theorem correct (compiled : Proven.Top.Alloc.CompiledA) (h : Proven.S3.compile P = some compiled) (input : List UInt8) (startState : Proven.Top.riscv.State) (call : Proven.Top.Call) (hs : Proven.Top.StartCorrect Proven.Top.riscv startState call compiled.code (id input)) (ho : (id ((P.a3) input)).length ≤ call.outputLength) (hm : Proven.Top.Alloc.memoryNeeded compiled (id input) ≤ call.workLength) :
    ∃ finishState, Proven.Top.Runs Proven.Top.riscv startState finishState ∧
      (Proven.Top.riscv.observe finishState).programCounter = call.returnAddress ∧
      (Proven.Top.riscv.observe finishState).register Proven.Top.riscv.mapping.status ≠ Proven.Top.Alloc.oomFlag ∧
      Proven.Top.readMemory (Proven.Top.riscv.observe finishState) call.outputAddress (id ((P.a3) input)).length
        = some (id ((P.a3) input)) :=
  Proven.S3.compile_correct P compiled (P.a3) id id input startState call h computes hs ho hm
end Q
