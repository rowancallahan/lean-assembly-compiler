/- Opus box E: E's semantics with the failure kind (`Fail`: capacity, room, stuck), for the capacity / out-of-memory
exits.  Each combinator `…X` returns `Except Fail`; `oX` forgets the kind and gives back the `Option` combinator. -/
import Nano.Run.NdProg
namespace Templates
open CallProbe ParSpec

inductive Fail | cap | room | stuck
  deriving DecidableEq

abbrev SemWX := Env → Nat → Hp → Except Fail (List UInt64 × Hp)
abbrev SemTX := Env → Nat → Hp → Except Fail (TRes × Hp)
abbrev Sem1X := Env → Nat → Hp → Except Fail (UInt64 × Hp)

def ofO {α : Type} (f : Fail) : Option α → Except Fail α
  | some a => .ok a
  | none => .error f

def toO {α : Type} : Except Fail α → Option α
  | .ok a => some a
  | .error _ => none

@[simp] theorem toO_ofO {α : Type} (f : Fail) (o : Option α) : toO (ofO f o) = o := by cases o <;> rfl
@[simp] theorem toO_ok {α : Type} (a : α) : toO (.ok a : Except Fail α) = some a := rfl
@[simp] theorem toO_err {α : Type} (f : Fail) : toO (.error f : Except Fail α) = none := rfl

theorem toO_bind {α β : Type} (x : Except Fail α) (f : α → Except Fail β) :
    toO (x.bind f) = (toO x).bind fun a => toO (f a) := by cases x <;> rfl
theorem toO_map {α β : Type} (x : Except Fail α) (f : α → β) : toO (x.map f) = (toO x).map f := by cases x <;> rfl

/-! ## the combinators -/

def oneF (S : Sem1X) : SemWX := fun env sp H => (S env sp H).map fun r => ([r.1], r.2)
def nilF : SemWX := fun _ _ H => .ok ([], H)
def pairF (wa : Nat) (SA SB : SemWX) : SemWX :=
  fun env sp H => (SA env sp H).bind fun r1 => (SB env (sp - 8 * wa) r1.2).bind fun r2 => .ok (r1.1 ++ r2.1, r2.2)
def ifF (cmp : Nat) (SP ST SE : SemWX) : SemWX :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b] => if cmpF cmp a b then ST env sp r.2 else SE env sp r.2
    | _ => .error .stuck
def letF (k0 w : Nat) (SV SB : SemWX) : SemWX :=
  fun env sp H => (SV env sp H).bind fun r => SB (setW env k0 w r.1) sp r.2
def leafF (V : Env → UInt64) : SemWX := fun env sp H => if H.top + 8 ≤ sp then .ok ([V env], H) else .error .room
def localF (k : Nat) : Nat → SemWX
  | 0 => nilF
  | w + 1 => pairF 1 (leafF (fun env => env k)) (localF (k + 1) w)
def fin1F (SP : SemWX) (F : UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : SemWX :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a] => (F a (sp - 8) r.2).map fun x => ([x.1], x.2)
    | _ => .error .stuck
def fin2F (SP : SemWX) (F : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : SemWX :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b] => (F a b (sp - 16) r.2).map fun x => ([x.1], x.2)
    | _ => .error .stuck
def fin3F (SP : SemWX) (F : UInt64 → UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : SemWX :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b, c] => (F a b c (sp - 24) r.2).map fun x => ([x.1], x.2)
    | _ => .error .stuck
def exitF (S : SemWX) : SemTX := fun env sp H => (S env sp H).map fun r => (.inl r.1, r.2)
def contF (S : SemWX) : SemTX := fun env sp H => (S env sp H).map fun r => (.inr r.1, r.2)
def ifTF (cmp : Nat) (SP : SemWX) (ST SE : SemTX) : SemTX :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b] => if cmpF cmp a b then ST env sp r.2 else SE env sp r.2
    | _ => .error .stuck
def letTF (k0 w : Nat) (SV : SemWX) (SB : SemTX) : SemTX :=
  fun env sp H => (SV env sp H).bind fun r => SB (setW env k0 w r.1) sp r.2
def exitOnlyF (r : TRes × Hp) : Except Fail (List UInt64 × Hp) :=
  match r.1 with | .inl vs => .ok (vs, r.2) | .inr _ => .error .stuck
def loopGoF (p : Nat) (SZ SS : SemTX) (sp : Nat) : Nat → Env → Hp → Except Fail (List UInt64 × Hp)
  | n, env, H =>
    if env 0 = 0 then (SZ env sp H).bind exitOnlyF
    else match n with
      | 0 => .error .stuck
      | n + 1 => (SS (decE env) sp H).bind fun r => match r.1 with
        | .inl vs => .ok (vs, r.2)
        | .inr st => loopGoF p SZ SS sp n (setW (decE env) 1 (p - 1) st) r.2
def loopF (p : Nat) (SZ SS : SemTX) : SemWX := fun env sp H => loopGoF p SZ SS sp (env 0).toNat env H
abbrev SemDX := List UInt64 → Nat → Hp → Except Fail (List UInt64 × Hp)
def defSF (p nl : Nat) (Sb : SemWX) : SemDX :=
  fun args sp H => if H.top + 16 + 8 * (nl - p) ≤ sp then Sb (argEnv p args) (sp - 16 - 8 * (nl - p)) H else .error .room
def callF (pa : Nat) (SA : SemWX) (Sd : SemDX) : SemWX :=
  fun env sp H => (SA env sp H).bind fun r => Sd r.1 (sp - 8 * pa) r.2

/-! ## forgetting the kind -/

def oW (S : SemWX) : SemW := fun env sp H => toO (S env sp H)
def oT (S : SemTX) : SemT := fun env sp H => toO (S env sp H)
def o1 (S : Sem1X) : Env → Nat → Hp → Option (UInt64 × Hp) := fun env sp H => toO (S env sp H)

theorem oW_one (S : Sem1X) : oW (oneF S) = one (o1 S) := by
  funext env sp H; simp [oW, oneF, one, o1, toO_map]
theorem oW_nil : oW nilF = nilS := rfl
theorem oW_pair (wa : Nat) (SA SB : SemWX) : oW (pairF wa SA SB) = pairS wa (oW SA) (oW SB) := by
  funext env sp H; simp only [oW, pairF, pairS, toO_bind, toO_ok]
theorem oW_if (cmp : Nat) (SP ST SE : SemWX) : oW (ifF cmp SP ST SE) = ifS cmp (oW SP) (oW ST) (oW SE) := by
  funext env sp H; simp only [oW, ifF, ifS, toO_bind]; congr 1; funext r; obtain ⟨l, H'⟩ := r; rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> dsimp only <;>
    first | rfl | (by_cases hc : cmpF cmp a b <;> simp [hc])
theorem oW_let (k0 w : Nat) (SV SB : SemWX) : oW (letF k0 w SV SB) = letS k0 w (oW SV) (oW SB) := by
  funext env sp H; simp only [oW, letF, letS, toO_bind]
theorem oW_leaf (V : Env → UInt64) : oW (leafF V) = leafS V := by
  funext env sp H; simp only [oW, leafF, leafS]; split <;> rfl
theorem oW_local (k : Nat) : ∀ w, oW (localF k w) = localS k w
  | 0 => rfl
  | w + 1 => by simp only [localF, localS, oW_pair, oW_leaf, oW_local (k + 1) w]
theorem oW_fin1 (SP : SemWX) (F : UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) :
    oW (fin1F SP F) = fin1S (oW SP) (fun a sp H => toO (F a sp H)) := by
  funext env sp H; simp only [oW, fin1F, fin1S, toO_bind]; congr 1; funext r; obtain ⟨l, H'⟩ := r; rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp [toO_map]
theorem oW_fin2 (SP : SemWX) (F : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) :
    oW (fin2F SP F) = fin2S (oW SP) (fun a b sp H => toO (F a b sp H)) := by
  funext env sp H; simp only [oW, fin2F, fin2S, toO_bind]; congr 1; funext r; obtain ⟨l, H'⟩ := r; rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp [toO_map]
theorem oW_fin3 (SP : SemWX) (F : UInt64 → UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) :
    oW (fin3F SP F) = fin3S (oW SP) (fun a b c sp H => toO (F a b c sp H)) := by
  funext env sp H; simp only [oW, fin3F, fin3S, toO_bind]; congr 1; funext r; obtain ⟨l, H'⟩ := r; rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp [toO_map]
theorem oT_exit (S : SemWX) : oT (exitF S) = exitS (oW S) := by funext env sp H; simp [oT, oW, exitF, exitS, toO_map]
theorem oT_cont (S : SemWX) : oT (contF S) = contS (oW S) := by funext env sp H; simp [oT, oW, contF, contS, toO_map]
theorem oT_if (cmp : Nat) (SP : SemWX) (ST SE : SemTX) : oT (ifTF cmp SP ST SE) = ifTS cmp (oW SP) (oT ST) (oT SE) := by
  funext env sp H; simp only [oT, oW, ifTF, ifTS, toO_bind]; congr 1; funext r; obtain ⟨l, H'⟩ := r; rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> dsimp only <;>
    first | rfl | (by_cases hc : cmpF cmp a b <;> simp [hc])
theorem oT_let (k0 w : Nat) (SV : SemWX) (SB : SemTX) : oT (letTF k0 w SV SB) = letTS k0 w (oW SV) (oT SB) := by
  funext env sp H; simp only [oT, oW, letTF, letTS, toO_bind]
theorem toO_loopGo (p : Nat) (SZ SS : SemTX) (sp : Nat) :
    ∀ n env H, toO (loopGoF p SZ SS sp n env H) = loopGo p (oT SZ) (oT SS) sp n env H := by
  intro n
  induction n with
  | zero =>
    intro env H; unfold loopGoF loopGo
    split
    · simp only [toO_bind, oT]; congr 1; funext r; obtain ⟨t, H'⟩ := r; rcases t with vs | st <;> rfl
    · rfl
  | succ n ih =>
    intro env H; unfold loopGoF loopGo
    split
    · simp only [toO_bind, oT]; congr 1; funext r; obtain ⟨t, H'⟩ := r; rcases t with vs | st <;> rfl
    · simp only [toO_bind, oT]; congr 1; funext r; obtain ⟨t, H'⟩ := r; rcases t with vs | st
      · rfl
      · exact ih _ _
theorem oW_loop (p : Nat) (SZ SS : SemTX) : oW (loopF p SZ SS) = loopS p (oT SZ) (oT SS) := by
  funext env sp H; simp only [oW, loopF, loopS, toO_loopGo]
def oD (S : SemDX) : SemD := fun args sp H => toO (S args sp H)
theorem oD_def (p nl : Nat) (Sb : SemWX) : oD (defSF p nl Sb) = defS p nl (oW Sb) := by
  funext args sp H; simp only [oD, defSF, defS, oW]; split <;> rfl
theorem oW_call (pa : Nat) (SA : SemWX) (Sd : SemDX) : oW (callF pa SA Sd) = callS pa (oW SA) (oD Sd) := by
  funext env sp H; simp only [oW, callF, callS, oD, toO_bind]

/-! ## the prims: only BPUSH's full buffer is `cap`, BNEW's missing room is `room`; the rest cannot fail on a well-formed heap -/

def bpushFF (hb : Nat) : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp) :=
  fun buf v sp H => match bufInfo hb H buf with
    | none => .error .stuck
    | some lc => if lc.1.toNat < lc.2.toNat then ofO .stuck (bpushF hb buf v sp H) else .error .cap

theorem toO_bpush (hb : Nat) (buf v : UInt64) (sp : Nat) (H : Hp) : toO (bpushFF hb buf v sp H) = bpushF hb buf v sp H := by
  unfold bpushFF; split
  · rename_i h; simp [bpushF, h]
  · rename_i lc h; split
    · simp
    · rename_i hl; simp [bpushF, h, hl]

def bnewF (κ : Nat) : (Nat → UInt64) → Nat → Hp → Except Fail (UInt64 × Hp) :=
  fun env sp H => ofO .room (bnewS κ env sp H)

/-- the prims of two operands with their kinds -/
def primF2F (K : SC) (pn : Nat) : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp) :=
  if pn = 7 then fun a b sp H => ofO .stuck (bgetF K.hb a b sp H) else bpushFF K.hb

theorem toO_primF2 (K : SC) (pn : Nat) : (fun a b sp H => toO (primF2F K pn a b sp H)) = primF2 K pn := by
  funext a b sp H; unfold primF2F primF2; split
  · simp
  · exact toO_bpush _ _ _ _ _

/-! ## E's semantics with kinds; the callees' semantics `fsX` -/

mutual
def svF (K : SC) (fsX : Nat → SemDX) : Nd → SemWX
  | .const v => leafF (fun _ => v)
  | .loc s w => localF s w
  | .bin op a b => fin2F (pairF 1 (svF K fsX a) (svF K fsX b)) (fun a b sp H => ofO .stuck (aluF2 op a b sp H))
  | .ite c a b t e => ifF c (pairF 1 (svF K fsX a) (svF K fsX b)) (svF K fsX t) (svF K fsX e)
  | .letE s w v b => letF s w (svF K fsX v) (svF K fsX b)
  | .pair cs => svLF K fsX cs
  | .call id as => callF (K.npwOf id) (svLF K fsX as) (fsX id)
  | .prim pn as =>
    if pn = 1 ∨ pn = 3 then leafF (fun _ => K.c29)
    else if pn = 5 then oneF (bnewF K.κ)
    else if pn = 2 ∨ pn = 6 then fin1F (svLF K fsX as) (fun a sp H => ofO .stuck (primF1 K pn a sp H))
    else if pn = 8 then fin3F (svLF K fsX as) (fun a b c sp H => ofO .stuck (bsetF K.hb a b c sp H))
    else fin2F (svLF K fsX as) (primF2F K pn)
  | .loop z s => loopF K.p (stF K fsX z) (stF K fsX s)
  | .cont _ => fun _ _ _ => .error .stuck
def stF (K : SC) (fsX : Nat → SemDX) : Nd → SemTX
  | .ite c a b t e => ifTF c (pairF 1 (svF K fsX a) (svF K fsX b)) (stF K fsX t) (stF K fsX e)
  | .letE s w v b => letTF s w (svF K fsX v) (stF K fsX b)
  | .cont e => contF (svF K fsX e)
  | e => exitF (svF K fsX e)
def svLF (K : SC) (fsX : Nat → SemDX) : List Nd → SemWX
  | [] => nilF
  | c :: cs => pairF (wd K c) (svF K fsX c) (svLF K fsX cs)
end

mutual
theorem oW_sv (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) :
    ∀ e : Nd, oW (svF K fsX e) = sv K e
  | .const v => by simp only [svF, sv, oW_leaf]
  | .loc s w => by simp only [svF, sv, oW_local]
  | .bin op a b => by
    simp only [svF, sv, oW_fin2, oW_pair, oW_sv K fsX hf a, oW_sv K fsX hf b, toO_ofO]
  | .ite c a b t e => by simp only [svF, sv, oW_if, oW_pair, oW_sv K fsX hf a, oW_sv K fsX hf b, oW_sv K fsX hf t,
      oW_sv K fsX hf e]
  | .letE s w v b => by simp only [svF, sv, oW_let, oW_sv K fsX hf v, oW_sv K fsX hf b]
  | .pair cs => by simp only [svF, sv, oW_svL K fsX hf cs]
  | .call id as => by simp only [svF, sv, oW_call, oW_svL K fsX hf as, hf]
  | .prim pn as => by
    simp only [svF, sv]
    split
    · exact oW_leaf _
    split
    · simp only [oW_one]; congr; funext env sp H; simp [o1, bnewF]
    split
    · simp only [oW_fin1, oW_svL K fsX hf as]; congr; funext a sp H; simp
    split
    · simp only [oW_fin3, oW_svL K fsX hf as]; congr; funext a b c sp H; simp
    · simp only [oW_fin2, oW_svL K fsX hf as, toO_primF2]
  | .loop z s => by simp only [svF, sv, oW_loop, oT_st K fsX hf z, oT_st K fsX hf s]
  | .cont _ => by funext env sp H; simp [oW, svF, sv]
theorem oT_st (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) :
    ∀ e : Nd, oT (stF K fsX e) = st K e
  | .ite c a b t e => by simp only [stF, st, oT_if, oW_pair, oW_sv K fsX hf a, oW_sv K fsX hf b, oT_st K fsX hf t,
      oT_st K fsX hf e]
  | .letE s w v b => by simp only [stF, st, oT_let, oW_sv K fsX hf v, oT_st K fsX hf b]
  | .cont e => by simp only [stF, st, oT_cont, oW_sv K fsX hf e]
  | .const v => by simp only [stF, st, oT_exit, oW_sv K fsX hf (.const v)]
  | .loc s w => by simp only [stF, st, oT_exit, oW_sv K fsX hf (.loc s w)]
  | .bin op a b => by simp only [stF, st, oT_exit, oW_sv K fsX hf (.bin op a b)]
  | .pair cs => by simp only [stF, st, oT_exit, oW_sv K fsX hf (.pair cs)]
  | .call id as => by simp only [stF, st, oT_exit, oW_sv K fsX hf (.call id as)]
  | .prim pn as => by simp only [stF, st, oT_exit, oW_sv K fsX hf (.prim pn as)]
  | .loop z s => by simp only [stF, st, oT_exit, oW_sv K fsX hf (.loop z s)]
theorem oW_svL (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) :
    ∀ cs : List Nd, oW (svLF K fsX cs) = svL K cs
  | [] => by simp only [svLF, svL, oW_nil]
  | c :: cs => by simp only [svLF, svL, oW_pair, oW_sv K fsX hf c, oW_svL K fsX hf cs]
end

def dfltF : SemDX := fun _ _ _ => .error .stuck

/-- def k's semantics with kinds -/
def semAtF (P : PC) (ds : List DefA) (k : Nat) : SemDX :=
  defSF (dA ds k).npw (dA ds k).nslots (svF (scAt P ds k) (fun n => if _h : n < k then semAtF P ds n else dfltF)
    (dA ds k).body)
termination_by k

/-- **forgetting the kind gives E's semantics** -/
theorem oD_semAt (P : PC) (ds : List DefA) (k : Nat) : oD (semAtF P ds k) = semAt P ds k := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rw [semAtF, semAt_eq, oD_def, oW_sv]
    intro n
    show (if _h : n < k then semAt P ds n else dflt) = oD (if _h : n < k then semAtF P ds n else dfltF)
    split
    · rename_i h; exact (ih n h).symm
    · rfl

end Templates
