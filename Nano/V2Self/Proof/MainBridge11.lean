/- Nano/V2Self/Proof/MainBridge11: the Sem ⇐ sv bridge in value mode, all nodes (`node_all`). -/
import Nano.V2Self.Proof.MainBridge10

namespace NanoMain
open Templates

theorem node_loop (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (z s : ParSpec.Nd) :
    NodeOK cx K oc D (ParSpec.Nd.loop z s) := by
  intro _ _ Γ ks F F' es env ew σ sp H vs H' _ hc
  simp [OwnSpec.chk] at hc

theorem node_cont (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) :
    NodeOK cx K oc D (ParSpec.Nd.cont e) := by
  intro _ _ Γ ks F F' es env ew σ sp H vs H' hT
  cases hT

mutual
/-- **value mode, every node**: E's `sv` succeeding gives `ev` succeeding with related results -/
theorem node_all (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K)
    (hCR : CallR cx K oc) : ∀ e : ParSpec.Nd, NodeOK cx K oc D e
  | .const c => node_const cx K oc D c
  | .loc s w => node_loc cx K oc D s w
  | .bin op a b => node_bin cx K oc D hW op a b (node_all cx K oc D hRs hW hX hCR a) (node_all cx K oc D hRs hW hX hCR b)
  | .ite c a b t e => node_ite cx K oc D hRs hW c a b t e (node_all cx K oc D hRs hW hX hCR a) (node_all cx K oc D hRs hW hX hCR b) (node_all cx K oc D hRs hW hX hCR t) (node_all cx K oc D hRs hW hX hCR e)
  | .letE s w v b => node_let cx K oc D hRs hW s w v b (node_all cx K oc D hRs hW hX hCR v) (node_all cx K oc D hRs hW hX hCR b)
  | .pair cs => node_pair cx K oc D hW cs (nodes_all cx K oc D hRs hW hX hCR cs)
  | .call i as => node_call cx K oc D hW hCR i as (nodes_all cx K oc D hRs hW hX hCR as)
  | .prim p as => node_prim cx K oc D hW hX p as (nodes_all cx K oc D hRs hW hX hCR as)
  | .loop z s => node_loop cx K oc D z s
  | .cont e => node_cont cx K oc D e
theorem nodes_all (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K)
    (hCR : CallR cx K oc) : ∀ cs : List ParSpec.Nd, ∀ n ∈ cs, NodeOK cx K oc D n
  | [] => fun _ h => by simp at h
  | c :: cs => fun n hn => by
    rcases List.mem_cons.1 hn with h | h
    · rw [h]; exact node_all cx K oc D hRs hW hX hCR c
    · exact nodes_all cx K oc D hRs hW hX hCR cs n h
end

end NanoMain
