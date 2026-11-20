/- Machine bridge (Opus box E), part (B) assembled: **Gen's code = the templates**.  For every AST node e serialized at
cursor i, a CG / CT / CGs derivation (GenRef) emits words that are `tm` / `tmT` / `tmL` `.map encG`, exit placeholders
(0) exactly where the templates jump to the node's end (value mode) or to the given exit target (tail mode). -/
import Nano.V2Self.Proof.Machine.NdCGw
import Nano.V2Self.Proof.Machine.NdCGt
namespace Templates
open CallProbe C GenRef ParSpec
section cg
variable {S : SC} {K : GenRef.Cx}

mutual
theorem cgV (hS : SK S K) : ∀ e : Nd, CGV S K e
  | .const v => cgV_const hS v
  | .loc s w => cgV_loc hS s w
  | .bin op a b => cgV_bin hS op a b (cgV hS a) (cgV hS b)
  | .ite cm a b t e => cgV_ite hS cm a b t e (cgV hS a) (cgV hS b) (cgV hS t) (cgV hS e)
  | .letE s w v b => cgV_letE hS s w v b (cgV hS v) (cgV hS b)
  | .pair cs => cgV_pair hS cs (cgL hS cs)
  | .call n as => cgV_call hS n as (cgL hS as)
  | .prim pn as => cgV_prim hS pn as (cgL hS as)
  | .loop z s => cgV_loop hS z s (cgT hS z) (cgT hS s)
  | .cont e => cgV_cont hS e
termination_by e => 3 * sizeOf e
theorem cgL (hS : SK S K) : ∀ cs : List Nd, CGL S K cs
  | [] => cgL_nil
  | x :: xs => cgL_cons hS x xs (cgV hS x) (cgL hS xs)
termination_by cs => 3 * sizeOf cs
theorem cgT (hS : SK S K) : ∀ e : Nd, CGT S K e
  | .ite cm a b t e => cgT_ite hS cm a b t e (cgV hS a) (cgV hS b) (cgT hS t) (cgT hS e)
  | .letE s w v b => cgT_letE hS s w v b (cgV hS v) (cgT hS b)
  | .cont e => cgT_cont hS e (cgV hS e)
  | .const v => cgT_const hS v (cgV hS _)
  | .loc s w => cgT_loc hS s w (cgV hS _)
  | .bin op a b => cgT_bin hS op a b (cgV hS _)
  | .pair cs => cgT_pair hS cs (cgV hS _)
  | .call n as => cgT_call hS n as (cgV hS _)
  | .prim pn as => cgT_prim hS pn as (cgV hS _)
  | .loop z s => cgT_loop hS z s (cgV hS _)
termination_by e => 3 * sizeOf e + 2
end

end cg
end Templates
