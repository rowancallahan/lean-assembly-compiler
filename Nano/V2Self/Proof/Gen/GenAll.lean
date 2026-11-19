/- Gen soundness on success, with the width facts: Gen's code relation (CG, DefsC) and the width pass's relation
(W, WDefs) are over the same AST spans (`Sk`, deterministic), so they describe the same defs. -/
import Nano.V2Self.Proof.Gen.GenTop
import Nano.V2Self.Proof.Gen.GenWidth
namespace GenRef
open C CallProbe

/- the span of the node at AST word i (and of n consecutive nodes) -/
mutual
inductive Sk (X : Buf) : Nat → Nat → Prop
  | const {i} : tg X i = 1 → Sk X i (i + 2)
  | local {i} : tg X i = 2 → Sk X i (i + 3)
  | bin {i i1 i2} : tg X i = 3 → Sk X (i + 2) i1 → Sk X i1 i2 → Sk X i i2
  | ite {i i1 i2 i3 i4} : tg X i = 4 → Sk X (i + 2) i1 → Sk X i1 i2 → Sk X i2 i3 → Sk X i3 i4 → Sk X i i4
  | lett {i i1 i2} : tg X i = 5 → Sk X (i + 3) i1 → Sk X i1 i2 → Sk X i i2
  | pair {i i'} : tg X i = 6 → Sks X (i + 2) (tg X (i + 1)).toNat i' → Sk X i i'
  | call {i i'} : tg X i = 8 → Sks X (i + 3) (tg X (i + 2)).toNat i' → Sk X i i'
  | prim {i i'} : tg X i = 9 → Sks X (i + 2) (g33 (tg X (i + 1))).toNat i' → Sk X i i'
  | loop {i i1 i2} : tg X i = 10 → Sk X (i + 1) i1 → Sk X i1 i2 → Sk X i i2
  | cont {i i1} : tg X i = 11 → Sk X (i + 1) i1 → Sk X i i1
inductive Sks (X : Buf) : Nat → Nat → Nat → Prop
  | nil {i} : Sks X i 0 i
  | cons {i i1 i2 n} : Sk X i i1 → Sks X i1 n i2 → Sks X i (n + 1) i2
end

theorem tgne {X : Buf} {i : Nat} {a b : UInt64} (ha : tg X i = a) (hb : tg X i = b) (h : a ≠ b) : False := h (ha ▸ hb)

mutual
theorem sk_det {X : Buf} : ∀ {i a b}, Sk X i a → Sk X i b → a = b
  | _, _, _, .const h1, .const _ => rfl
  | _, _, _, .local h1, .local _ => rfl
  | _, _, _, .bin _ a1 a2, .bin _ b1 b2 => by
    have := sk_det a1 b1; subst this; exact sk_det a2 b2
  | _, _, _, .ite _ a1 a2 a3 a4, .ite _ b1 b2 b3 b4 => by
    have := sk_det a1 b1; subst this
    have := sk_det a2 b2; subst this
    have := sk_det a3 b3; subst this
    exact sk_det a4 b4
  | _, _, _, .lett _ a1 a2, .lett _ b1 b2 => by
    have := sk_det a1 b1; subst this; exact sk_det a2 b2
  | _, _, _, .pair _ a1, .pair _ b1 => sks_det a1 b1
  | _, _, _, .call _ a1, .call _ b1 => sks_det a1 b1
  | _, _, _, .prim _ a1, .prim _ b1 => sks_det a1 b1
  | _, _, _, .loop _ a1 a2, .loop _ b1 b2 => by
    have := sk_det a1 b1; subst this; exact sk_det a2 b2
  | _, _, _, .cont _ a1, .cont _ b1 => sk_det a1 b1
  | _, _, _, .const h1, .local h2 | _, _, _, .const h1, .bin h2 _ _ | _, _, _, .const h1, .ite h2 _ _ _ _
  | _, _, _, .const h1, .lett h2 _ _ | _, _, _, .const h1, .pair h2 _ | _, _, _, .const h1, .call h2 _
  | _, _, _, .const h1, .prim h2 _ | _, _, _, .const h1, .loop h2 _ _ | _, _, _, .const h1, .cont h2 _
  | _, _, _, .local h1, .const h2 | _, _, _, .local h1, .bin h2 _ _ | _, _, _, .local h1, .ite h2 _ _ _ _
  | _, _, _, .local h1, .lett h2 _ _ | _, _, _, .local h1, .pair h2 _ | _, _, _, .local h1, .call h2 _
  | _, _, _, .local h1, .prim h2 _ | _, _, _, .local h1, .loop h2 _ _ | _, _, _, .local h1, .cont h2 _
  | _, _, _, .bin h1 _ _, .const h2 | _, _, _, .bin h1 _ _, .local h2 | _, _, _, .bin h1 _ _, .ite h2 _ _ _ _
  | _, _, _, .bin h1 _ _, .lett h2 _ _ | _, _, _, .bin h1 _ _, .pair h2 _ | _, _, _, .bin h1 _ _, .call h2 _
  | _, _, _, .bin h1 _ _, .prim h2 _ | _, _, _, .bin h1 _ _, .loop h2 _ _ | _, _, _, .bin h1 _ _, .cont h2 _
  | _, _, _, .ite h1 _ _ _ _, .const h2 | _, _, _, .ite h1 _ _ _ _, .local h2 | _, _, _, .ite h1 _ _ _ _, .bin h2 _ _
  | _, _, _, .ite h1 _ _ _ _, .lett h2 _ _ | _, _, _, .ite h1 _ _ _ _, .pair h2 _ | _, _, _, .ite h1 _ _ _ _, .call h2 _
  | _, _, _, .ite h1 _ _ _ _, .prim h2 _ | _, _, _, .ite h1 _ _ _ _, .loop h2 _ _ | _, _, _, .ite h1 _ _ _ _, .cont h2 _
  | _, _, _, .lett h1 _ _, .const h2 | _, _, _, .lett h1 _ _, .local h2 | _, _, _, .lett h1 _ _, .bin h2 _ _
  | _, _, _, .lett h1 _ _, .ite h2 _ _ _ _ | _, _, _, .lett h1 _ _, .pair h2 _ | _, _, _, .lett h1 _ _, .call h2 _
  | _, _, _, .lett h1 _ _, .prim h2 _ | _, _, _, .lett h1 _ _, .loop h2 _ _ | _, _, _, .lett h1 _ _, .cont h2 _
  | _, _, _, .pair h1 _, .const h2 | _, _, _, .pair h1 _, .local h2 | _, _, _, .pair h1 _, .bin h2 _ _
  | _, _, _, .pair h1 _, .ite h2 _ _ _ _ | _, _, _, .pair h1 _, .lett h2 _ _ | _, _, _, .pair h1 _, .call h2 _
  | _, _, _, .pair h1 _, .prim h2 _ | _, _, _, .pair h1 _, .loop h2 _ _ | _, _, _, .pair h1 _, .cont h2 _
  | _, _, _, .call h1 _, .const h2 | _, _, _, .call h1 _, .local h2 | _, _, _, .call h1 _, .bin h2 _ _
  | _, _, _, .call h1 _, .ite h2 _ _ _ _ | _, _, _, .call h1 _, .lett h2 _ _ | _, _, _, .call h1 _, .pair h2 _
  | _, _, _, .call h1 _, .prim h2 _ | _, _, _, .call h1 _, .loop h2 _ _ | _, _, _, .call h1 _, .cont h2 _
  | _, _, _, .prim h1 _, .const h2 | _, _, _, .prim h1 _, .local h2 | _, _, _, .prim h1 _, .bin h2 _ _
  | _, _, _, .prim h1 _, .ite h2 _ _ _ _ | _, _, _, .prim h1 _, .lett h2 _ _ | _, _, _, .prim h1 _, .pair h2 _
  | _, _, _, .prim h1 _, .call h2 _ | _, _, _, .prim h1 _, .loop h2 _ _ | _, _, _, .prim h1 _, .cont h2 _
  | _, _, _, .loop h1 _ _, .const h2 | _, _, _, .loop h1 _ _, .local h2 | _, _, _, .loop h1 _ _, .bin h2 _ _
  | _, _, _, .loop h1 _ _, .ite h2 _ _ _ _ | _, _, _, .loop h1 _ _, .lett h2 _ _ | _, _, _, .loop h1 _ _, .pair h2 _
  | _, _, _, .loop h1 _ _, .call h2 _ | _, _, _, .loop h1 _ _, .prim h2 _ | _, _, _, .loop h1 _ _, .cont h2 _
  | _, _, _, .cont h1 _, .const h2 | _, _, _, .cont h1 _, .local h2 | _, _, _, .cont h1 _, .bin h2 _ _
  | _, _, _, .cont h1 _, .ite h2 _ _ _ _ | _, _, _, .cont h1 _, .lett h2 _ _ | _, _, _, .cont h1 _, .pair h2 _
  | _, _, _, .cont h1 _, .call h2 _ | _, _, _, .cont h1 _, .prim h2 _ | _, _, _, .cont h1 _, .loop h2 _ _ =>
    (tgne h1 h2 (by decide)).elim
theorem sks_det {X : Buf} : ∀ {i n a b}, Sks X i n a → Sks X i n b → a = b
  | _, _, _, _, .nil, .nil => rfl
  | _, _, _, _, .cons a1 a2, .cons b1 b2 => by
    have := sk_det a1 b1; subst this; exact sks_det a2 b2
end

mutual
theorem cg_sk {K : Cx} : ∀ {d i h c i' E}, CG K d i h c i' E → Sk K.X i i'
  | _, _, _, _, _, _, .const ht => .const ht
  | _, _, _, _, _, _, .local ht _ => .local ht
  | _, _, _, _, _, _, .bin ht _ a b => .bin ht (cg_sk a) (cg_sk b)
  | _, _, _, _, _, _, .ite ht _ a b t e _ _ => .ite ht (cg_sk a) (cg_sk b) (cg_sk t) (cg_sk e)
  | _, _, _, _, _, _, .lett ht _ a b => .lett ht (cg_sk a) (cg_sk b)
  | _, _, _, _, _, _, .pair ht _ a => .pair ht (cgs_sk a)
  | _, _, _, _, _, _, .call ht _ _ a _ => .call ht (cgs_sk a)
  | _, _, _, _, _, _, .prim ht _ a => .prim ht (cgs_sk a)
  | _, _, _, _, _, _, .loop ht a b _ => .loop ht (ct_sk a) (ct_sk b)
theorem ct_sk {K : Cx} : ∀ {hd d i h c i' E}, CT K hd d i h c i' E → Sk K.X i i'
  | _, _, _, _, _, _, _, .val _ _ _ a => cg_sk a
  | _, _, _, _, _, _, _, .cont ht a _ => .cont ht (cg_sk a)
  | _, _, _, _, _, _, _, .ite ht _ a b t e _ _ => .ite ht (cg_sk a) (cg_sk b) (ct_sk t) (ct_sk e)
  | _, _, _, _, _, _, _, .lett ht _ a b => .lett ht (cg_sk a) (ct_sk b)
theorem cgs_sk {K : Cx} : ∀ {d i h n c i' E}, CGs K d i h n c i' E → Sks K.X i n i'
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons a b => .cons (cg_sk a) (cgs_sk b)
end

mutual
theorem w_sk {X D p q} : ∀ {top i w i'}, W X D p q top i w i' → Sk X i i'
  | _, _, _, _, .const ht => .const ht
  | _, _, _, _, .local ht => .local ht
  | _, _, _, _, .bin ht a b => .bin ht (w_sk a) (w_sk b)
  | _, _, _, _, .ite ht a b t e => .ite ht (w_sk a) (w_sk b) (w_sk t) (w_sk e)
  | _, _, _, _, .lett ht a b => .lett ht (w_sk a) (w_sk b)
  | _, _, _, _, .pair ht a hl => .pair ht (hl ▸ ws_sk a)
  | _, _, _, _, .call ht _ a hl _ => .call ht (hl ▸ ws_sk a)
  | _, _, _, _, .prim ht a hl _ => .prim ht (hl ▸ ws_sk a)
  | _, _, _, _, .loop ht a b => .loop ht (w_sk a) (w_sk b)
  | _, _, _, _, .cont ht a _ => .cont ht (w_sk a)
theorem ws_sk {X D p q} : ∀ {i ws i'}, Ws X D p q i ws i' → Sks X i ws.length i'
  | _, _, _, .nil => .nil
  | _, _, _, .cons a b => .cons (w_sk a) (ws_sk b)
end

/-- a CG node and a W node at the same AST word end at the same word -/
theorem cg_w_end {K d i h c i' E D p q top w i''} (hC : CG K d i h c i' E) (hW : W K.X D p q top i w i'') : i' = i'' :=
  sk_det (cg_sk hC) (w_sk hW)
theorem ct_w_end {K hd d i h c i' E D p q top w i''} (hC : CT K hd d i h c i' E) (hW : W K.X D p q top i w i'') : i' = i'' :=
  sk_det (ct_sk hC) (w_sk hW)
theorem cgs_ws_end {K d i h c i' E D p q ws i''} (hC : CGs K d i h ws.length c i' E) (hW : Ws K.X D p q i ws i'') :
    i' = i'' := sks_det (cgs_sk hC) (ws_sk hW)

/-- Gen's def chain and the width pass's def chain have the same headers -/
theorem chains {X u} : ∀ {T i o hs T' i' o'}, DefsC X u T i o hs T' i' o' → ∀ {D hs' D' i''}, WDefs X D i hs' D' i'' →
    i' = X.length → X.length ≤ i'' → hs = hs' ∧ i'' = i' := by
  intro T i o hs T' i' o' hC
  induction hC with
  | nil =>
    intro D hs' D' i'' hW he hle
    cases hW with
    | nil => exact ⟨rfl, rfl⟩
    | cons h20 _ _ _ =>
      exfalso; subst he
      have := tg_lt X _ (by rw [h20]; decide); omega
  | cons hD _ ih =>
    intro D hs' D' i'' hW he hle
    obtain ⟨h20, -, -, -, -, c, i1, E, hcg, h21, rfl, -⟩ := hD
    cases hW with
    | nil =>
      exfalso
      have := tg_lt X _ (by rw [h20]; decide); omega
    | cons _ hWb _ hWs =>
      have e := sk_det (cg_sk hcg) (w_sk hWb)
      subst e
      obtain ⟨a, b⟩ := ih hWs he hle
      exact ⟨by rw [a], b⟩

/-- **Gen soundness on success, with widths**: a nonempty g41 output is the LE bytes of the stubs, the defs' code (DefsC)
and the start code; the same defs (headers hs, (npw, nres) table D) satisfy the width relation (WDefs) -/
theorem gen41_full (c : List UInt8) (x : Buf) (hX : x.length < 2 ^ 31) (h : g41 c x ≠ []) :
    bget x 0 = 2 ∧ ∃ hs T o D, DefsC x g_999 bnew 1 (g34 bnew) hs T x.length o ∧ WDefs x [] 1 hs D x.length ∧ hs ≠ [] ∧
      tg x (hs.getLastD 0 + 2) = 0 ∧ tg x (hs.getLastD 0 + 5) = 1 ∧
      g41 c x = g40 16777216 c (startW (bset o 0 (g13 0 0 (bsize o))) (bget T (bsize T - 1))) 0 [] ∧
      o.length < 2 ^ 24 ∧ o.length + 32 < 2 ^ 18 := by
  obtain ⟨h0, hw, hs, T, o, hD, hne, h2, h5, he⟩ := gen41_ok c x hX h
  obtain ⟨hs', D, i', hW, hi'⟩ := g53_ok x hX hw
  obtain ⟨e1, e2⟩ := chains hD hW rfl hi'
  subst e1 e2
  exact ⟨h0, hs, T, o, D, hD, hW, hne, h2, h5, he⟩

end GenRef
