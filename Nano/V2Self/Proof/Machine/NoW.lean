/- Machine bridge (Opus box E): no instruction of the whole program writes a2 / a3 (x12 / x13), so the start
code's a2 / a3 survive the call to main.  `ok i` = the destination register of `i` is not 12 or 13. -/
import Nano.V2Self.Proof.Machine.StartCode
namespace Templates
open CallProbe ParSpec

/-- registers no instruction of C writes: a2, a3 (work, output base) and the ABI-saved sp, gp, tp, s1, s2..s11 -/
def keepR (r : Nat) : Bool := r == 2 || r == 3 || r == 4 || r == 9 || r == 12 || r == 13 || (18 ≤ r && r ≤ 27)

def nk (d : Nat) : Bool := !keepR d

def dstOk : J → Bool
  | .addi d _ _ | .ld d _ _ | .jal d _ | .jalr d _ | .alu _ d _ _ | .slli d _ _ | .lbu d _ _ | .srli d _ _ => nk d
  | _ => true

theorem liB_ok (d v : Nat) (h : nk d = true) : ∀ k, (liB d v k).all dstOk = true
  | 0 => rfl
  | k + 1 => by simp only [liB, List.all_append, liB_ok d v h k, liJ]; simp [dstOk, h]

theorem liT_ok (d : Nat) (v : UInt64) (h : nk d = true) : (liT d v).all dstOk = true := by
  unfold liT; split <;> simp [dstOk, h, liB_ok d v.toNat h]

theorem popN_ok (p k0 : Nat) : ∀ w, (popN p k0 w).all dstOk = true
  | 0 => rfl
  | w + 1 => by simp [nk, keepR, popN, popSlot, dstOk, popN_ok p k0 w]

theorem localT_ok (tgt p : Nat) : ∀ k q w, (localT tgt p k q w).all dstOk = true
  | _, _, 0 => rfl
  | k, q, w + 1 => by simp [nk, keepR, localT, pushA, push, dstOk, localT_ok tgt p (k + 1) (q + 5) w]

theorem copy_ok (p q : Nat) : ∀ k, (copy p q k).all dstOk = true
  | 0 => rfl
  | k + 1 => by simp [nk, keepR, copy, copyJ, dstOk, copy_ok p q k]

theorem bnewT_ok (tgt q κ : Nat) : (bnewT tgt q κ).all dstOk = true := by
  simp [nk, keepR, bnewT, pushA, push, dstOk, liT_ok]

theorem primT_ok (K : SC) (pn q : Nat) : (primT K pn q).all dstOk = true := by
  unfold primT
  repeat' split
  all_goals simp [nk, keepR, lenT, pushA, push, rdT, bsizeT, bgetT, bsetT, bpushT, dstOk, bnewT_ok]

theorem cmpJ_ok (c : Nat) : dstOk (cmpJ c) = true := by unfold cmpJ; split <;> rfl

mutual
theorem tm_ok (K : SC) : ∀ (e : Nd) (h : Nat), (tm K e h).all dstOk = true
  | .const v, h => by simp [nk, keepR, tm, constT, pushA, push, dstOk, liT_ok]
  | .loc s w, h => by simp [nk, keepR, tm, localT_ok]
  | .bin op a b, h => by simp [nk, keepR, tm, binT, dstOk, tm_ok K a, tm_ok K b]
  | .ite c a b t e, h => by
    simp [nk, keepR, tm, ifHeadG, cmpJ_ok, dstOk, tm_ok K a, tm_ok K b, tm_ok K t, tm_ok K e]
    simpa [dstOk, nk, keepR] using cmpJ_ok c
  | .letE s w v b, h => by simp [nk, keepR, tm, popN_ok, tm_ok K v, tm_ok K b]
  | .pair cs, h => by simp [nk, keepR, tm, tmL_ok K cs]
  | .call id as, h => by simp [nk, keepR, tm, dstOk, tmL_ok K as]
  | .prim pn as, h => by simp [nk, keepR, tm, tmL_ok K as, primT_ok]
  | .loop z s, h => by simp [nk, keepR, tm, loopHead, loopDec, dstOk, tmT_ok K z, tmT_ok K s]
  | .cont _, h => by simp [nk, keepR, tm]
theorem tmT_ok (K : SC) : ∀ (e : Nd) (h X Hd : Nat), (tmT K e h X Hd).all dstOk = true
  | .ite c a b t e, h, X, Hd => by
    simp [nk, keepR, tmT, ifHeadG, cmpJ_ok, dstOk, tm_ok K a, tm_ok K b, tmT_ok K t, tmT_ok K e]
    simpa [dstOk, nk, keepR] using cmpJ_ok c
  | .letE s w v b, h, X, Hd => by simp [nk, keepR, tmT, popN_ok, tm_ok K v, tmT_ok K b]
  | .cont e, h, X, Hd => by simp [nk, keepR, tmT, popN_ok, dstOk, tm_ok K e]
  | .const v, h, X, Hd => by simp only [tmT]; simp [nk, keepR, dstOk, tm_ok K (.const v)]
  | .loc s w, h, X, Hd => by simp only [tmT]; simp [nk, keepR, dstOk, tm_ok K (.loc s w)]
  | .bin op a b, h, X, Hd => by simp only [tmT]; simp [nk, keepR, dstOk, tm_ok K (.bin op a b)]
  | .pair cs, h, X, Hd => by simp only [tmT]; simp [nk, keepR, dstOk, tm_ok K (.pair cs)]
  | .call id as, h, X, Hd => by simp only [tmT]; simp [nk, keepR, dstOk, tm_ok K (.call id as)]
  | .prim pn as, h, X, Hd => by simp only [tmT]; simp [nk, keepR, dstOk, tm_ok K (.prim pn as)]
  | .loop z s, h, X, Hd => by simp only [tmT]; simp [nk, keepR, dstOk, tm_ok K (.loop z s)]
theorem tmL_ok (K : SC) : ∀ (cs : List Nd) (h : Nat), (tmL K cs h).all dstOk = true
  | [], h => by simp [nk, keepR, tmL]
  | c :: cs, h => by simp [nk, keepR, tmL, tm_ok K c, tmL_ok K cs]
end

theorem defsJ_ok (P : PC) (ds : List DefA) : ∀ k n, (defsJ P ds k n).all dstOk = true
  | _, 0 => rfl
  | k, n + 1 => by
    simp [nk, keepR, defsJ, defT, proA, pushA, push, epi, dstOk, copy_ok, tm_ok, defsJ_ok P ds (k + 1) n]

theorem stubJ_ok (S : Nat) : (stubJ S).all dstOk = true := by simp [nk, keepR, stubJ, dstOk]
theorem startJ_ok (S w : Nat) : (startJ S w).all dstOk = true := by simp [nk, keepR, startJ, dstOk]

theorem wr_keep {s : St} {d r : Nat} {v : UInt64} (h : nk d = true) (hr : keepR r = true) :
    (CallProbe.wr s d v).x r = s.x r := by
  unfold CallProbe.wr; split; · rfl
  simp only [upd]; rw [if_neg]; simp [nk, keepR] at h hr; omega

theorem step_keep {C : List J} (hC : C.all dstOk = true) {a c : Nat × St} (h : step C a = some c) {r : Nat}
    (hr : keepR r = true) : c.2.x r = a.2.x r := by
  obtain ⟨pc, s⟩ := a
  simp only [step] at h
  cases hi : C[pc]? with
  | none => simp [hi] at h
  | some i =>
    have ok : dstOk i = true := List.all_eq_true.mp hC i (List.mem_of_getElem? hi)
    rw [hi] at h
    cases i <;> simp at h <;> (try (obtain ⟨_, rfl⟩ := h)) <;> (try subst h) <;> simp only [dstOk] at ok <;>
      first | rfl | exact wr_keep ok hr

theorem star_keep {C : List J} (hC : C.all dstOk = true) {a c : Nat × St} (h : Star C a c) {r : Nat}
    (hr : keepR r = true) : c.2.x r = a.2.x r := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [step_keep hC hs hr, ih]

end Templates
