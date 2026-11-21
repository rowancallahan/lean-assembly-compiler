/- Nano/Tests/MainCert: PER-PROGRAM MEANING CERTIFICATES.  For a concrete source text `x` and the Lean function `f`
written in it: `∀ inp, srcRun ⟨x⟩ inp = some (f inp)` — the meaning that `C_correctL` talks about IS the Lean function.
Method: the lexer run `C.s10 x = ts` (kernel; sound by `s10_sound`), the reference parse checked by a Boolean equality
`progEq (refParse ts) P = true` (kernel; `progEq_eq`), and `Sem κC P inp = .ok (f inp)` for symbolic `inp` (definitional
unfolding, or induction for loops). -/
import Nano.Main.Compile

namespace NanoMain
open ParSpec
mutual
def ndEq : Nd → Nd → Bool
  | .const a, .const b => a == b
  | .loc a b, .loc c d => a == c && b == d
  | .bin o a b, .bin o' a' b' => o == o' && ndEq a a' && ndEq b b'
  | .ite c a b t e, .ite c' a' b' t' e' => c == c' && ndEq a a' && ndEq b b' && ndEq t t' && ndEq e e'
  | .letE s w v b, .letE s' w' v' b' => s == s' && w == w' && ndEq v v' && ndEq b b'
  | .pair cs, .pair cs' => ndsEq cs cs'
  | .call i as, .call i' as' => i == i' && ndsEq as as'
  | .prim p as, .prim p' as' => p == p' && ndsEq as as'
  | .loop z s, .loop z' s' => ndEq z z' && ndEq s s'
  | .cont e, .cont e' => ndEq e e'
  | _, _ => false
def ndsEq : List Nd → List Nd → Bool
  | [], [] => true
  | a :: r, b :: r' => ndEq a b && ndsEq r r'
  | _, _ => false
end

mutual
theorem ndEq_eq : ∀ a b, ndEq a b = true → a = b
  | .const a, .const b, h => by simp [ndEq] at h; rw [h]
  | .loc a b, .loc c d, h => by simp [ndEq] at h; rw [h.1, h.2]
  | .bin o a b, .bin o' a' b', h => by
    simp only [ndEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, ndEq_eq a a' h.1.2, ndEq_eq b b' h.2]
  | .ite c a b t e, .ite c' a' b' t' e', h => by
    simp only [ndEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1.1.1, ndEq_eq a a' h.1.1.1.2, ndEq_eq b b' h.1.1.2, ndEq_eq t t' h.1.2, ndEq_eq e e' h.2]
  | .letE s w v b, .letE s' w' v' b', h => by
    simp only [ndEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1.1, h.1.1.2, ndEq_eq v v' h.1.2, ndEq_eq b b' h.2]
  | .pair cs, .pair cs', h => by simp only [ndEq] at h; rw [ndsEq_eq cs cs' h]
  | .call i as, .call i' as', h => by
    simp only [ndEq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, ndsEq_eq as as' h.2]
  | .prim p as, .prim p' as', h => by
    simp only [ndEq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, ndsEq_eq as as' h.2]
  | .loop z s, .loop z' s', h => by
    simp only [ndEq, Bool.and_eq_true] at h; rw [ndEq_eq z z' h.1, ndEq_eq s s' h.2]
  | .cont e, .cont e', h => by simp only [ndEq] at h; rw [ndEq_eq e e' h]
  | .const _, .loc _ _, h | .const _, .bin _ _ _, h | .const _, .ite _ _ _ _ _, h | .const _, .letE _ _ _ _, h
  | .const _, .pair _, h | .const _, .call _ _, h | .const _, .prim _ _, h | .const _, .loop _ _, h | .const _, .cont _, h
  | .loc _ _, .const _, h | .loc _ _, .bin _ _ _, h | .loc _ _, .ite _ _ _ _ _, h | .loc _ _, .letE _ _ _ _, h
  | .loc _ _, .pair _, h | .loc _ _, .call _ _, h | .loc _ _, .prim _ _, h | .loc _ _, .loop _ _, h | .loc _ _, .cont _, h
  | .bin _ _ _, .const _, h | .bin _ _ _, .loc _ _, h | .bin _ _ _, .ite _ _ _ _ _, h | .bin _ _ _, .letE _ _ _ _, h
  | .bin _ _ _, .pair _, h | .bin _ _ _, .call _ _, h | .bin _ _ _, .prim _ _, h | .bin _ _ _, .loop _ _, h | .bin _ _ _, .cont _, h
  | .ite _ _ _ _ _, .const _, h | .ite _ _ _ _ _, .loc _ _, h | .ite _ _ _ _ _, .bin _ _ _, h | .ite _ _ _ _ _, .letE _ _ _ _, h
  | .ite _ _ _ _ _, .pair _, h | .ite _ _ _ _ _, .call _ _, h | .ite _ _ _ _ _, .prim _ _, h | .ite _ _ _ _ _, .loop _ _, h
  | .ite _ _ _ _ _, .cont _, h
  | .letE _ _ _ _, .const _, h | .letE _ _ _ _, .loc _ _, h | .letE _ _ _ _, .bin _ _ _, h | .letE _ _ _ _, .ite _ _ _ _ _, h
  | .letE _ _ _ _, .pair _, h | .letE _ _ _ _, .call _ _, h | .letE _ _ _ _, .prim _ _, h | .letE _ _ _ _, .loop _ _, h
  | .letE _ _ _ _, .cont _, h
  | .pair _, .const _, h | .pair _, .loc _ _, h | .pair _, .bin _ _ _, h | .pair _, .ite _ _ _ _ _, h | .pair _, .letE _ _ _ _, h
  | .pair _, .call _ _, h | .pair _, .prim _ _, h | .pair _, .loop _ _, h | .pair _, .cont _, h
  | .call _ _, .const _, h | .call _ _, .loc _ _, h | .call _ _, .bin _ _ _, h | .call _ _, .ite _ _ _ _ _, h
  | .call _ _, .letE _ _ _ _, h | .call _ _, .pair _, h | .call _ _, .prim _ _, h | .call _ _, .loop _ _, h | .call _ _, .cont _, h
  | .prim _ _, .const _, h | .prim _ _, .loc _ _, h | .prim _ _, .bin _ _ _, h | .prim _ _, .ite _ _ _ _ _, h
  | .prim _ _, .letE _ _ _ _, h | .prim _ _, .pair _, h | .prim _ _, .call _ _, h | .prim _ _, .loop _ _, h | .prim _ _, .cont _, h
  | .loop _ _, .const _, h | .loop _ _, .loc _ _, h | .loop _ _, .bin _ _ _, h | .loop _ _, .ite _ _ _ _ _, h
  | .loop _ _, .letE _ _ _ _, h | .loop _ _, .pair _, h | .loop _ _, .call _ _, h | .loop _ _, .prim _ _, h | .loop _ _, .cont _, h
  | .cont _, .const _, h | .cont _, .loc _ _, h | .cont _, .bin _ _ _, h | .cont _, .ite _ _ _ _ _, h | .cont _, .letE _ _ _ _, h
  | .cont _, .pair _, h | .cont _, .call _ _, h | .cont _, .prim _ _, h | .cont _, .loop _ _, h => by simp [ndEq] at h
theorem ndsEq_eq : ∀ a b, ndsEq a b = true → a = b
  | [], [], _ => rfl
  | a :: r, b :: r', h => by
    simp only [ndsEq, Bool.and_eq_true] at h; rw [ndEq_eq a b h.1, ndsEq_eq r r' h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [ndsEq] at h
end

def defEq (a b : DefA) : Bool :=
  a.id == b.id && a.npw == b.npw && a.nslots == b.nslots && a.kind == b.kind && a.nres == b.nres && ndEq a.body b.body

theorem defEq_eq {a b : DefA} (h : defEq a b = true) : a = b := by
  obtain ⟨ai, an, as, ak, ar, ab⟩ := a; obtain ⟨bi, bn, bs, bk, br, bb⟩ := b
  simp only [defEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [h1, h2, h3, h4, h5, ndEq_eq _ _ h6]

def progEq : Option (List DefA) → List DefA → Bool
  | some l, m => l.length == m.length && (l.zip m).all fun (a, b) => defEq a b
  | none, _ => false

theorem progEq_eq : ∀ {o : Option (List DefA)} {m : List DefA}, progEq o m = true → o = some m
  | none, _, h => by simp [progEq] at h
  | some l, m, h => by
    simp only [progEq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨hl, ha⟩ := h
    congr 1
    induction l generalizing m with
    | nil => cases m <;> simp_all
    | cons a l ih =>
      cases m with
      | nil => simp at hl
      | cons b m =>
        simp at hl
        have h1 : defEq a b = true := ha (a, b) (by simp)
        rw [defEq_eq h1, ih m hl (fun x hx => ha x (List.mem_cons_of_mem _ hx))]

/-- **the certificate rule** -/
theorem cert_of {x : List UInt8} {ts : List UInt64} {p : List DefA} (f : List UInt8 → List UInt8) (hx : x.length < 2 ^ 32)
    (hl : C.s10 x = ts) (hts : ts ≠ []) (hp : progEq (refParse ts) p = true) (hs : ∀ inp, Sem κC p inp = .ok (f inp)) :
    ∀ inp, srcRun ⟨x⟩ inp = some (f inp) := by
  intro inp
  have hpo := pOf_eq (LexSpec.s10_sound x hx ts hl hts) (progEq_eq hp)
  simp [srcRun, hpo, hs inp, Except.toOption]

/-- the certificate rule for inputs of bounded length (fuel loops count input bytes in a 64-bit word) -/
theorem cert_of' {x : List UInt8} {ts : List UInt64} {p : List DefA} (f : List UInt8 → List UInt8) (hx : x.length < 2 ^ 32)
    (hl : C.s10 x = ts) (hts : ts ≠ []) (hp : progEq (refParse ts) p = true)
    (hs : ∀ inp, inp.length < 2 ^ 64 → Sem κC p inp = .ok (f inp)) :
    ∀ inp, inp.length < 2 ^ 64 → srcRun ⟨x⟩ inp = some (f inp) := by
  intro inp hi
  have hpo := pOf_eq (LexSpec.s10_sound x hx ts hl hts) (progEq_eq hp)
  simp [srcRun, hpo, hs inp hi, Except.toOption]

end NanoMain

/-! ## example 1: ParSpec's `ex1` (two defs, a call, prims) -/
namespace NanoMain.Ex1
open ParSpec
def a (p q : UInt64) : UInt64 := p + q * 3
def m (x : List UInt8) : List UInt8 := put [] (a (rd x 0) 2)

def P : List DefA :=
  [{ id := 0, npw := 2, nslots := 2, kind := 0, nres := 1, body := .bin 1 (.loc 0 1) (.bin 3 (.loc 1 1) (.const 3)) },
   { id := 1, npw := 0, nslots := 0, kind := 0, nres := 1,
     body := .prim 4 [.prim 5 [], .call 0 [.prim 2 [.const 0], .const 2]] }]

theorem cert : ∀ inp, srcRun ⟨ex1.toUTF8.toList⟩ inp = some (m inp) :=
  cert_of (p := P) m (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (fun _ => rfl)

end NanoMain.Ex1

/-! ## example 2: ParSpec's `ex3` (fuel loop, CONTINUE, `len'`, `len`) -/
namespace NanoMain.Ex3
open ParSpec
def g : Nat → List UInt8 → UInt64 → UInt64
  | 0, _, p => p
  | n + 1, x, p => if p < len x then g n x (p + 1) else p
def m (x : List UInt8) : List UInt8 := put [] (g (len' x) x 0)
def Z : Nd := .loc 1 1
def S : Nd := .ite 2 (.loc 1 1) (.prim 3 []) (.cont (.bin 1 (.loc 1 1) (.const 1))) (.loc 1 1)
def P : List DefA :=
  [{ id := 0, npw := 2, nslots := 2, kind := 1, nres := 1, body := .loop Z S },
   { id := 1, npw := 0, nslots := 0, kind := 0, nres := 1, body := .prim 4 [.prim 5 [], .call 0 [.prim 1 [], .const 0]] }]
theorem stepS (cx : Ctx) (n p : UInt64) :
    ev cx S [.w n, .w p] = if p < len cx.inp then .ok (.inr [.w (p + 1)]) else .ok (.inl [.w p]) := by
  by_cases h : p < len cx.inp
  · have h' : p < UInt64.ofNat cx.inp.length := h
    simp [S, ev, val, evL, prim, binop, h, h', bind, Except.bind, pure, Except.pure]
  · have h' : ¬ p < UInt64.ofNat cx.inp.length := h
    simp [S, ev, val, evL, prim, binop, h, h', bind, Except.bind, pure, Except.pure]
theorem zeroZ (cx : Ctx) (n p : UInt64) : ev cx Z [.w n, .w p] = .ok (.inl [.w p]) := rfl
theorem loop (cx : Ctx) : ∀ n p F, loopRun (fun e => ev cx Z e) (fun e => ev cx S e) n [.w F, .w p] = .ok [.w (g n cx.inp p)]
  | 0, p, F => rfl
  | n + 1, p, F => by
    have e1 : setSlots [W.w F, W.w p] 0 [.w (UInt64.ofNat n)] = .ok [.w (UInt64.ofNat n), .w p] := rfl
    have e2 : setSlots [W.w (UInt64.ofNat n), W.w p] 1 [.w (p + 1)] = .ok [.w (UInt64.ofNat n), .w (p + 1)] := rfl
    simp only [loopRun, e1, bind, Except.bind, stepS]
    by_cases h : p < len cx.inp
    · simp only [h, if_true, e2]; rw [loop cx n (p + 1)]; simp [g, h]
    · simp only [h, if_false, pure, Except.pure]; simp [g, h]
theorem f0 (inp : List UInt8) (hl : inp.length < 2 ^ 64) :
    defMean inp κC [] (P[0]'(by decide)) [.w (UInt64.ofNat inp.length), .w 0] = .ok [.w (g inp.length inp 0)] := by
  have := loop ⟨inp, κC, []⟩ (UInt64.ofNat inp.length).toNat 0 (UInt64.ofNat inp.length)
  have ht : (UInt64.ofNat inp.length).toNat = inp.length := by simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hl]
  rw [ht] at this
  unfold defMean
  rw [if_pos ⟨rfl, by decide⟩]
  have hb : (P[0]'(by decide)).body = .loop Z S := rfl
  have hn : (P[0]'(by decide)).nslots - (P[0]'(by decide)).npw = 0 := rfl
  have hr : (P[0]'(by decide)).nres = 1 := rfl
  rw [hb, hn, hr, List.replicate_zero, List.append_nil]
  have e : ev ⟨inp, κC, []⟩ (.loop Z S) [.w (UInt64.ofNat inp.length), .w 0] =
      bind (loopRun (fun e => ev ⟨inp, κC, []⟩ Z e) (fun e => ev ⟨inp, κC, []⟩ S e)
        (UInt64.ofNat inp.length).toNat [.w (UInt64.ofNat inp.length), .w 0]) (fun v => pure (Sum.inl v)) := rfl
  rw [e, ht, this]
  rfl

theorem sem (inp : List UInt8) (hl : inp.length < 2 ^ 64) : Sem κC P inp = .ok (m inp) := by
  have h0 := f0 inp hl
  have hm : means inp κC [] P = [defMean inp κC [] (P[0]'(by decide)), defMean inp κC [defMean inp κC [] (P[0]'(by decide))] (P[1]'(by decide))] := rfl
  unfold Sem; rw [hm]
  simp only [List.getLast?_cons_cons, List.getLast?_singleton]
  generalize defMean inp κC [] (P[0]'(by decide)) = F at h0 ⊢
  have h0' : F [.w inp.length.toUInt64, .w 0] = .ok [.w (g inp.length inp 0)] := h0
  unfold defMean
  rw [if_pos ⟨rfl, by decide⟩]
  have hb : (P[1]'(by decide)).body = .prim 4 [.prim 5 [], .call 0 [.prim 1 [], .const 0]] := rfl
  have hn : (P[1]'(by decide)).nslots - (P[1]'(by decide)).npw = 0 := rfl
  rw [hb, hn, List.replicate_zero, List.append_nil]
  simp only [ev, evL, val, prim, bind, Except.bind, pure, Except.pure, List.getElem?_cons_zero, List.append_nil,
    List.cons_append, List.nil_append, h0']
  rfl

/-- **certificate**: ParSpec's `ex3` text (a fuel loop with CONTINUE) means `m` -/
theorem cert : ∀ inp, inp.length < 2 ^ 64 → srcRun ⟨ex3.toUTF8.toList⟩ inp = some (m inp) :=
  cert_of' (p := P) m (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) sem

end NanoMain.Ex3
