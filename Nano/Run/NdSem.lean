/- Machine bridge (Opus box E): the machine-level semantics of a resolved AST node (`ParSpec.Nd`), the J templates Gen
emits for it, and the side conditions (widths, scoping) the templates need.
* `SC` = the per-def context: npw p, nslots nl, κ, heap base hb, input (c29 = length, inp = bytes), callee semantics
  `fs`, callee npw / nres, callee start word `T`.
* `sv` / `st` : value / tail semantics (`SemW` / `SemT` of Proof/EVX*: environment, stack pointer, heap image ↦
  result words and the new heap image; `none` = out of memory / capacity / ill-formed).  It mirrors Gen's code exactly
  (checked pushes, BNEW's room check, the prologue's room check in `defS`).
* `tm` / `tmT` : the J instruction list of a node at word h (exit target X, loop head Hd in tail mode); `lnV` / `lnT`
  their lengths (independent of h, X, Hd).
* `wd` (width), `rd` (slots read before written), `wr` (slots written by lets), `OkV` / `OkT` (side conditions). -/
import Nano.Run.EVXP
import Nano.Parser.ParSpec
namespace Templates
open CallProbe ParSpec

structure SC where
  p : Nat
  nl : Nat
  κ : Nat
  hb : Nat
  c29 : UInt64
  inp : Nat → UInt64
  fs : Nat → List UInt64 → Nat → Hp → Option (List UInt64 × Hp)
  npwOf : Nat → Nat
  nresOf : Nat → Nat
  T : Nat → Nat
  /-- callable defs: ids below `nd` -/
  nd : Nat
  /-- this def's nres (the width of its root LOOP) -/
  q : Nat

/-! ## widths, reads, writes -/
mutual
def wd (K : SC) : Nd → Nat
  | .const _ => 1
  | .loc _ w => w
  | .bin _ _ _ => 1
  | .ite _ _ _ t _ => wd K t
  | .letE _ _ _ b => wd K b
  | .pair cs => wdL K cs
  | .call id _ => K.nresOf id
  | .prim _ _ => 1
  | .loop _ _ => K.q
  | .cont _ => 0
def wdT (K : SC) : Nd → Nat
  | .ite _ _ _ t _ => wdT K t
  | .letE _ _ _ b => wdT K b
  | .cont _ => 0
  | e => wd K e
def wdL (K : SC) : List Nd → Nat
  | [] => 0
  | c :: cs => wd K c + wdL K cs
end

mutual
def rd : Nd → Nat → Prop
  | .const _ => fun _ => False
  | .loc s w => fun k => s ≤ k ∧ k < s + w
  | .bin _ a b => fun k => rd a k ∨ rd b k
  | .ite _ a b t e => fun k => (rd a k ∨ rd b k) ∨ rd t k ∨ rd e k
  | .letE s w v b => fun k => rd v k ∨ (rd b k ∧ ¬ (s ≤ k ∧ k < s + w))
  | .pair cs => rdL cs
  | .call _ as => rdL as
  | .prim _ as => rdL as
  | .loop z s => fun k => rd z k ∨ rd s k ∨ k = 0
  | .cont e => rd e
def rdL : List Nd → Nat → Prop
  | [] => fun _ => False
  | c :: cs => fun k => rd c k ∨ rdL cs k
end

mutual
def wr (p : Nat) : Nd → Nat → Prop
  | .const _ => fun _ => False
  | .loc _ _ => fun _ => False
  | .bin _ a b => fun k => wr p a k ∨ wr p b k
  | .ite _ a b t e => fun k => (wr p a k ∨ wr p b k) ∨ wr p t k ∨ wr p e k
  | .letE s w v b => fun k => wr p v k ∨ (s ≤ k ∧ k < s + w) ∨ wr p b k
  | .pair cs => wrL p cs
  | .call _ as => wrL p as
  | .prim _ as => wrL p as
  | .loop z s => fun k => (wr p z k ∨ wr p s k) ∨ k < p
  | .cont e => wr p e
def wrL (p : Nat) : List Nd → Nat → Prop
  | [] => fun _ => False
  | c :: cs => fun k => wr p c k ∨ wrL p cs k
end

/-! ## semantics -/

/-- the prim closings' semantics (by Gen's prim number) -/
def primF1 (K : SC) (pn : Nat) : UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  if pn = 2 then rdF1 K.c29 K.inp else bsizeF K.hb
def primF2 (K : SC) (pn : Nat) : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  if pn = 7 then bgetF K.hb else bpushF K.hb

mutual
def sv (K : SC) : Nd → SemW
  | .const v => leafS (fun _ => v)
  | .loc s w => localS s w
  | .bin op a b => fin2S (pairS 1 (sv K a) (sv K b)) (aluF2 op)
  | .ite c a b t e => ifS c (pairS 1 (sv K a) (sv K b)) (sv K t) (sv K e)
  | .letE s w v b => letS s w (sv K v) (sv K b)
  | .pair cs => svL K cs
  | .call id as => callS (K.npwOf id) (svL K as) (K.fs id)
  | .prim pn as =>
    if pn = 1 ∨ pn = 3 then leafS (fun _ => K.c29)
    else if pn = 5 then one (bnewS K.κ)
    else if pn = 2 ∨ pn = 6 then fin1S (svL K as) (primF1 K pn)
    else if pn = 8 then fin3S (svL K as) (bsetF K.hb)
    else fin2S (svL K as) (primF2 K pn)
  | .loop z s => loopS K.p (st K z) (st K s)
  | .cont _ => fun _ _ _ => none
def st (K : SC) : Nd → SemT
  | .ite c a b t e => ifTS c (pairS 1 (sv K a) (sv K b)) (st K t) (st K e)
  | .letE s w v b => letTS s w (sv K v) (st K b)
  | .cont e => contS (sv K e)
  | e => exitS (sv K e)
def svL (K : SC) : List Nd → SemW
  | [] => nilS
  | c :: cs => pairS (wd K c) (sv K c) (svL K cs)
end

/-! ## templates -/

def primLen (K : SC) (pn : Nat) : Nat :=
  if pn = 1 ∨ pn = 3 then 4 else if pn = 5 then (bnewT 1 0 K.κ).length else if pn = 2 then 6 else if pn = 6 then 3
  else if pn = 7 then 10 else if pn = 8 then 9 else 12

def primT (K : SC) (pn q : Nat) : List J :=
  if pn = 1 ∨ pn = 3 then lenT 1 q else if pn = 5 then bnewT 1 q K.κ else if pn = 2 then rdT else if pn = 6 then bsizeT
  else if pn = 7 then bgetT else if pn = 8 then bsetT else bpushT 6 q

mutual
def lnV (K : SC) : Nd → Nat
  | .const v => (liT 5 v).length + 4
  | .loc _ w => 5 * w
  | .bin _ a b => lnV K a + lnV K b + 5
  | .ite _ a b t e => lnV K a + lnV K b + 6 + lnV K t + lnV K e
  | .letE _ w v b => lnV K v + 3 * w + lnV K b
  | .pair cs => lnL K cs
  | .call _ as => lnL K as + 1
  | .prim pn as => lnL K as + primLen K pn
  | .loop z s => 3 + lnT K z + 2 + lnT K s
  | .cont _ => 0
def lnT (K : SC) : Nd → Nat
  | .ite _ a b t e => lnV K a + lnV K b + 6 + lnT K t + lnT K e
  | .letE _ w v b => lnV K v + 3 * w + lnT K b
  | .cont e => lnV K e + 3 * (K.p - 1) + 1
  | e => lnV K e + 1
def lnL (K : SC) : List Nd → Nat
  | [] => 0
  | c :: cs => lnV K c + lnL K cs
end

mutual
def tm (K : SC) : Nd → Nat → List J
  | .const v, h => constT 1 h v
  | .loc s w, h => localT 1 K.p s h w
  | .bin op a b, h => tm K a h ++ tm K b (h + lnV K a) ++ binT op
  | .ite c a b t e, h => tm K a h ++ tm K b (h + lnV K a) ++ ifHeadG c (lnV K t) ++
      tm K t (h + lnV K a + lnV K b + 5) ++ [.jal 0 ((lnV K e : Int) + 1)] ++
      tm K e (h + lnV K a + lnV K b + 6 + lnV K t)
  | .letE s w v b, h => tm K v h ++ popN K.p s w ++ tm K b (h + lnV K v + 3 * w)
  | .pair cs, h => tmL K cs h
  | .call id as, h => tmL K as h ++ [.jal 1 ((K.T id : Int) - ((h + lnL K as : Nat) : Int))]
  | .prim pn as, h => tmL K as h ++ primT K pn (h + lnL K as)
  | .loop z s, h => loopHead K.p ((h + 3 + lnT K z : Nat) - ((h + 2 : Nat) : Int)) ++
      tmT K z (h + 3) (h + (3 + lnT K z + 2 + lnT K s)) h ++ loopDec K.p ++
      tmT K s (h + 3 + lnT K z + 2) (h + (3 + lnT K z + 2 + lnT K s)) h
  | .cont _, _ => []
def tmT (K : SC) : Nd → Nat → Nat → Nat → List J
  | .ite c a b t e, h, X, Hd => tm K a h ++ tm K b (h + lnV K a) ++ ifHeadG c (lnT K t) ++
      tmT K t (h + lnV K a + lnV K b + 5) X Hd ++ [.jal 0 ((lnT K e : Int) + 1)] ++
      tmT K e (h + lnV K a + lnV K b + 6 + lnT K t) X Hd
  | .letE s w v b, h, X, Hd => tm K v h ++ popN K.p s w ++ tmT K b (h + lnV K v + 3 * w) X Hd
  | .cont e, h, _, Hd => tm K e h ++ popN K.p 1 (K.p - 1) ++
      [.jal 0 ((Hd : Int) - ((h + lnV K e + 3 * (K.p - 1) : Nat) : Int))]
  | e, h, X, _ => tm K e h ++ [.jal 0 ((X : Int) - ((h + lnV K e : Nat) : Int))]
def tmL (K : SC) : List Nd → Nat → List J
  | [], _ => []
  | c :: cs, h => tm K c h ++ tmL K cs (h + lnV K c)
end

/-! ## template lengths -/

theorem primT_len (K : SC) (pn q : Nat) : (primT K pn q).length = primLen K pn := by
  unfold primT primLen
  by_cases h1 : pn = 1 ∨ pn = 3
  · simp [h1, lenT, pushA, push]
  · simp only [h1, if_false]
    by_cases h5 : pn = 5
    · simp [h5, bnewT_len]
    · simp only [h5, if_false]
      by_cases h2 : pn = 2
      · simp [h2, rdT]
      · simp only [h2, if_false]
        by_cases h6 : pn = 6
        · simp [h6, bsizeT]
        · simp only [h6, if_false]
          by_cases h7 : pn = 7
          · simp [h7, bgetT]
          · simp only [h7, if_false]
            by_cases h8 : pn = 8
            · simp [h8, bsetT]
            · simp [h8, bpushT]

mutual
theorem tm_len (K : SC) : ∀ (e : Nd) (h : Nat), (tm K e h).length = lnV K e
  | .const v, h => by simp [tm, lnV, constT, pushA, push]; try omega
  | .loc s w, h => by simp [tm, lnV, localT_len]; try omega
  | .bin op a b, h => by simp [tm, lnV, binT, tm_len K a, tm_len K b]; try omega
  | .ite c a b t e, h => by simp [tm, lnV, ifHeadG, tm_len K a, tm_len K b, tm_len K t, tm_len K e]; try omega
  | .letE s w v b, h => by simp [tm, lnV, popN_len, tm_len K v, tm_len K b]; try omega
  | .pair cs, h => by simp [tm, lnV, tmL_len K cs]; try omega
  | .call id as, h => by simp [tm, lnV, tmL_len K as]; try omega
  | .prim pn as, h => by simp [tm, lnV, tmL_len K as, primT_len]; try omega
  | .loop z s, h => by simp [tm, lnV, loopHead, loopDec, tmT_len K z, tmT_len K s]; try omega
  | .cont _, h => by simp [tm, lnV]; try omega
theorem tmT_len (K : SC) : ∀ (e : Nd) (h X Hd : Nat), (tmT K e h X Hd).length = lnT K e
  | .ite c a b t e, h, X, Hd => by
    simp [tmT, lnT, ifHeadG, tm_len K a, tm_len K b, tmT_len K t, tmT_len K e]; try omega
  | .letE s w v b, h, X, Hd => by simp [tmT, lnT, popN_len, tm_len K v, tmT_len K b]; try omega
  | .cont e, h, X, Hd => by simp [tmT, lnT, popN_len, tm_len K e]; try omega
  | .const v, h, X, Hd => by simp only [tmT, lnT]; simp [tm_len K (.const v)]
  | .loc s w, h, X, Hd => by simp only [tmT, lnT]; simp [tm_len K (.loc s w)]
  | .bin op a b, h, X, Hd => by simp only [tmT, lnT]; simp [tm_len K (.bin op a b)]
  | .pair cs, h, X, Hd => by simp only [tmT, lnT]; simp [tm_len K (.pair cs)]
  | .call id as, h, X, Hd => by simp only [tmT, lnT]; simp [tm_len K (.call id as)]
  | .prim pn as, h, X, Hd => by simp only [tmT, lnT]; simp [tm_len K (.prim pn as)]
  | .loop z s, h, X, Hd => by simp only [tmT, lnT]; simp [tm_len K (.loop z s)]
theorem tmL_len (K : SC) : ∀ (cs : List Nd) (h : Nat), (tmL K cs h).length = lnL K cs
  | [], h => by simp [tmL, lnL]
  | c :: cs, h => by simp [tmL, lnL, tm_len K c, tmL_len K cs]; try omega
end

end Templates
