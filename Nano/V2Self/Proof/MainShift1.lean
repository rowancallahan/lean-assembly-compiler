/- Nano/V2Self/Proof/MainShift1: shift invariance of E's kinded semantics (box D, for E's `ShiftInv`), layer 1.
Two runs, the second with heap base `hb + δ`, stack pointer `sp + δ` and a heap shifted by `δ` (buffers hold only data
words, so cells shift uniformly).  Word slots agree, buffer handles differ by `δ`.  The stack pointers agree up to `δ`,
or both lie below their heap tops ("dead": every room check fails on both sides; this absorbs `sp - c` underflow).
Every combinator maps related inputs to the same outcome kind with related results. -/
import Nano.V2Self.Proof.SemX
import Nano.V2Self.Proof.MainTy

namespace NanoMain
open Templates

/-- heap cells shifted by `δ` above the base -/
def HR (δ hb : Nat) (H H' : Hp) : Prop := H'.top = H.top + δ ∧ ∀ a, hb ≤ a → H'.m (a + δ) = H.m a

/-- the heap bounds both runs keep -/
def Bnd (hb : Nat) (H : Hp) : Prop := 0 < hb ∧ hb ≤ H.top ∧ H.top ≤ 2 ^ 32

/-- stack pointers: shifted, or both below their heap tops -/
def SpR (δ : Nat) (H : Hp) (sp sp' : Nat) : Prop := (sp' = sp + δ ∧ sp ≤ 2 ^ 32) ∨ (sp < H.top ∧ sp' < H.top + δ)

/-- related outcomes: the same failure, or related results on related heaps (the top never decreases) -/
def OutR {α : Type} (R : α → α → Prop) (δ hb : Nat) (H : Hp) : Except Fail (α × Hp) → Except Fail (α × Hp) → Prop
  | .error f, .error f' => f = f'
  | .ok (v, H1), .ok (v', H1') => R v v' ∧ HR δ hb H1 H1' ∧ Bnd hb H1 ∧ H.top ≤ H1.top
  | _, _ => False

/-- a simulation of two semantics under the shift -/
def Sim {α : Type} (δ hb : Nat) (RE : Env → Env → Prop) (R : α → α → Prop)
    (S S' : Env → Nat → Hp → Except Fail (α × Hp)) : Prop :=
  ∀ env env' sp sp' H H', RE env env' → HR δ hb H H' → Bnd hb H → SpR δ H sp sp' →
    OutR R δ hb H (S env sp H) (S' env' sp' H')

theorem spR_sub {δ : Nat} {H H1 : Hp} {sp sp' : Nat} (c : Nat) (h : SpR δ H sp sp') (hH : H.top ≤ H1.top)
    (h0 : 0 < H1.top) : SpR δ H1 (sp - c) (sp' - c) := by
  rcases h with ⟨rfl, h2⟩ | ⟨h1, h2⟩
  · by_cases hc : c ≤ sp
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr ⟨by omega, by omega⟩
  · exact .inr ⟨by omega, by omega⟩

theorem spR_mono {δ : Nat} {H H1 : Hp} {sp sp' : Nat} (h : SpR δ H sp sp') (hH : H.top ≤ H1.top) : SpR δ H1 sp sp' := by
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨by omega, by omega⟩

/-- room checks agree -/
theorem room_iff {δ : Nat} {H H' : Hp} {sp sp' c : Nat} (hH : H'.top = H.top + δ) (h : SpR δ H sp sp') :
    (H.top + c ≤ sp ↔ H'.top + c ≤ sp') := by
  rcases h with ⟨rfl, -⟩ | ⟨h1, h2⟩ <;> constructor <;> intro <;> omega

/-! ## sequencing -/
theorem bind_sim {α β : Type} {δ hb : Nat} {RA : α → α → Prop} {RB : β → β → Prop}
    {x x' : Except Fail (α × Hp)} {H : Hp} (hx : OutR RA δ hb H x x')
    {g g' : α × Hp → Except Fail (β × Hp)}
    (hg : ∀ a a' H1 H1', RA a a' → HR δ hb H1 H1' → Bnd hb H1 → H.top ≤ H1.top →
      OutR RB δ hb H (g (a, H1)) (g' (a', H1'))) :
    OutR RB δ hb H (x.bind g) (x'.bind g') := by
  match x, x', hx with
  | .error f, .error f', hx => simp only [OutR] at hx; subst hx; exact rfl
  | .ok (a, H1), .ok (a', H1'), hx =>
    obtain ⟨h1, h2, h3, h4⟩ := hx
    exact hg a a' H1 H1' h1 h2 h3 h4

theorem out_trans {α : Type} {δ hb : Nat} {R : α → α → Prop} {H H1 : Hp} {r r' : Except Fail (α × Hp)}
    (h : OutR R δ hb H1 r r') (hH : H.top ≤ H1.top) : OutR R δ hb H r r' := by
  match r, r', h with
  | .error f, .error f', h => exact h
  | .ok (a, H2), .ok (a', H2'), h => exact ⟨h.1, h.2.1, h.2.2.1, Nat.le_trans hH h.2.2.2⟩

/-! ## related words -/
def WR (δ : Nat) : Kd → UInt64 → UInt64 → Prop
  | .w, u, u' => u' = u
  | .b, u, u' => u'.toNat = u.toNat + δ

def LR (δ : Nat) : List Kd → List UInt64 → List UInt64 → Prop
  | [], [], [] => True
  | k :: ks, v :: vs, v' :: vs' => WR δ k v v' ∧ LR δ ks vs vs'
  | _, _, _ => False

theorem LR.app {δ : Nat} : ∀ {ka kb a a' b b'}, LR δ ka a a' → LR δ kb b b' → LR δ (ka ++ kb) (a ++ b) (a' ++ b')
  | [], _, [], [], _, _, _, hb => by simpa using hb
  | _ :: _, _, _ :: _, _ :: _, _, _, ha, hb => ⟨ha.1, LR.app ha.2 hb⟩
  | [], _, _ :: _, _, _, _, ha, _ => by simp [LR] at ha
  | [], _, [], _ :: _, _, _, ha, _ => by simp [LR] at ha
  | _ :: _, _, [], _, _, _, ha, _ => by simp [LR] at ha
  | _ :: _, _, _ :: _, [], _, _, ha, _ => by simp [LR] at ha

theorem LR.split {δ : Nat} : ∀ {ka kb v v'}, LR δ (ka ++ kb) v v' →
    ∃ a b a' b', v = a ++ b ∧ v' = a' ++ b' ∧ LR δ ka a a' ∧ LR δ kb b b'
  | [], _, v, v', h => ⟨[], v, [], v', rfl, rfl, trivial, h⟩
  | k :: ka, kb, x :: v, x' :: v', h => by
    obtain ⟨a, b, a', b', rfl, rfl, h1, h2⟩ := LR.split (ka := ka) h.2
    exact ⟨x :: a, b, x' :: a', b', rfl, rfl, ⟨h.1, h1⟩, h2⟩
  | _ :: _, _, [], _, h => by simp [LR] at h
  | _ :: _, _, _ :: _, [], h => by simp [LR] at h

theorem LR.ww {δ : Nat} {v v' : List UInt64} (h : LR δ [.w, .w] v v') : ∃ a b, v = [a, b] ∧ v' = [a, b] := by
  rcases v with _ | ⟨a, _ | ⟨b, _ | ⟨c, v⟩⟩⟩ <;> rcases v' with _ | ⟨a', _ | ⟨b', _ | ⟨c', v'⟩⟩⟩ <;>
    simp only [LR, WR, and_true, false_and, and_false] at h
  exact ⟨_, _, rfl, by rw [h.1, h.2]⟩

theorem LR.len {δ : Nat} : ∀ {ks v v'}, LR δ ks v v' → v.length = ks.length ∧ v'.length = ks.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, h => by have := LR.len h.2; simp [this]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by simp [LR] at h

theorem LR.one {δ : Nat} {k : Kd} {v v' : List UInt64} (h : LR δ [k] v v') : ∃ a a', v = [a] ∧ v' = [a'] ∧ WR δ k a a' := by
  rcases v with _ | ⟨a, _ | ⟨b, v⟩⟩ <;> rcases v' with _ | ⟨a', _ | ⟨b', v'⟩⟩ <;> simp only [LR, and_true, and_false] at h
  exact ⟨a, a', rfl, rfl, h⟩
theorem LR.two {δ : Nat} {k1 k2 : Kd} {v v' : List UInt64} (h : LR δ [k1, k2] v v') :
    ∃ a a' b b', v = [a, b] ∧ v' = [a', b'] ∧ WR δ k1 a a' ∧ WR δ k2 b b' := by
  rcases v with _ | ⟨a, _ | ⟨b, _ | ⟨c, v⟩⟩⟩ <;> rcases v' with _ | ⟨a', _ | ⟨b', _ | ⟨c', v'⟩⟩⟩ <;>
    simp only [LR, and_true, and_false] at h
  exact ⟨a, a', b, b', rfl, rfl, h.1, h.2⟩
theorem LR.three {δ : Nat} {k1 k2 k3 : Kd} {v v' : List UInt64} (h : LR δ [k1, k2, k3] v v') :
    ∃ a a' b b' c c', v = [a, b, c] ∧ v' = [a', b', c'] ∧ WR δ k1 a a' ∧ WR δ k2 b b' ∧ WR δ k3 c c' := by
  rcases v with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, v⟩⟩⟩⟩ <;> rcases v' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨d', v'⟩⟩⟩⟩ <;>
    simp only [LR, and_true, and_false] at h
  exact ⟨a, a', b, b', c, c', rfl, rfl, h.1, h.2.1, h.2.2⟩

/-! ## the combinators -/
section
variable {δ hb : Nat} {RE : Env → Env → Prop}

theorem leafF_sim {k : Kd} {V V' : Env → UInt64} (hV : ∀ env env', RE env env' → WR δ k (V env) (V' env')) :
    Sim δ hb RE (LR δ [k]) (leafF V) (leafF V') := by
  intro env env' sp sp' H H' he hH hB hS
  simp only [leafF]
  have := room_iff (c := 8) hH.1 hS
  by_cases h : H.top + 8 ≤ sp
  · rw [if_pos h, if_pos (this.1 h)]; exact ⟨⟨hV env env' he, trivial⟩, hH, hB, Nat.le_refl _⟩
  · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]; exact rfl

theorem nilF_sim : Sim δ hb RE (LR δ []) nilF nilF :=
  fun _ _ _ _ _ _ _ hH hB _ => ⟨trivial, hH, hB, Nat.le_refl _⟩

theorem pairF_sim {wa : Nat} {ka kb : List Kd} {SA SA' SB SB' : SemWX} (hA : Sim δ hb RE (LR δ ka) SA SA')
    (hB : Sim δ hb RE (LR δ kb) SB SB') : Sim δ hb RE (LR δ (ka ++ kb)) (pairF wa SA SB) (pairF wa SA' SB') := by
  intro env env' sp sp' H H' he hH hBd hS
  simp only [pairF]
  refine bind_sim (hA env env' sp sp' H H' he hH hBd hS) fun a a' H1 H1' ha hH1 hB1 ht => ?_
  refine out_trans (bind_sim (hB env env' _ _ H1 H1' he hH1 hB1 (spR_sub _ hS ht (by have := hB1; unfold Bnd at this; omega)))
    fun b b' H2 H2' hb' hH2 hB2 ht2 => ⟨LR.app ha hb', hH2, hB2, ht2⟩) ht

theorem letF_sim {k0 w : Nat} {vs ks : List Kd} {RE2 : Env → Env → Prop} {SV SV' SB SB' : SemWX}
    (hV : Sim δ hb RE (LR δ vs) SV SV') (hB : Sim δ hb RE2 (LR δ ks) SB SB')
    (hE : ∀ env env' r r', RE env env' → LR δ vs r r' → RE2 (setW env k0 w r) (setW env' k0 w r')) :
    Sim δ hb RE (LR δ ks) (letF k0 w SV SB) (letF k0 w SV' SB') := by
  intro env env' sp sp' H H' he hH hBd hS
  simp only [letF]
  exact bind_sim (hV env env' sp sp' H H' he hH hBd hS) fun a a' H1 H1' ha hH1 hB1 ht =>
    out_trans (hB _ _ sp sp' H1 H1' (hE env env' a a' he ha) hH1 hB1 (spR_mono hS ht)) ht

theorem ifF_sim {c : Nat} {ks : List Kd} {SP SP' ST ST' SE SE' : SemWX} (hP : Sim δ hb RE (LR δ [.w, .w]) SP SP')
    (hT : Sim δ hb RE (LR δ ks) ST ST') (hE : Sim δ hb RE (LR δ ks) SE SE') :
    Sim δ hb RE (LR δ ks) (ifF c SP ST SE) (ifF c SP' ST' SE') := by
  intro env env' sp sp' H H' he hH hBd hS
  simp only [ifF]
  refine bind_sim (hP env env' sp sp' H H' he hH hBd hS) fun a a' H1 H1' ha hH1 hB1 ht => ?_
  obtain ⟨x, y, rfl, rfl⟩ := LR.ww ha
  simp only
  split
  · exact out_trans (hT _ _ sp sp' H1 H1' he hH1 hB1 (spR_mono hS ht)) ht
  · exact out_trans (hE _ _ sp sp' H1 H1' he hH1 hB1 (spR_mono hS ht)) ht

/-- a one-word closing: related arguments, related outcome -/
def Sim1 (δ hb : Nat) (k1 k : Kd) (F F' : UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : Prop :=
  ∀ a a' sp sp' H H', WR δ k1 a a' → HR δ hb H H' → Bnd hb H → SpR δ H sp sp' → OutR (WR δ k) δ hb H (F a sp H) (F' a' sp' H')
def Sim2 (δ hb : Nat) (k1 k2 k : Kd) (F F' : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : Prop :=
  ∀ a a' b b' sp sp' H H', WR δ k1 a a' → WR δ k2 b b' → HR δ hb H H' → Bnd hb H → SpR δ H sp sp' →
    OutR (WR δ k) δ hb H (F a b sp H) (F' a' b' sp' H')
def Sim3 (δ hb : Nat) (k1 k2 k3 k : Kd) (F F' : UInt64 → UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : Prop :=
  ∀ a a' b b' c c' sp sp' H H', WR δ k1 a a' → WR δ k2 b b' → WR δ k3 c c' → HR δ hb H H' → Bnd hb H →
    SpR δ H sp sp' → OutR (WR δ k) δ hb H (F a b c sp H) (F' a' b' c' sp' H')

theorem out_one {δ hb : Nat} {k : Kd} {H : Hp} {r r' : Except Fail (UInt64 × Hp)} (h : OutR (WR δ k) δ hb H r r') :
    OutR (LR δ [k]) δ hb H (r.map fun x => ([x.1], x.2)) (r'.map fun x => ([x.1], x.2)) := by
  match r, r', h with
  | .error f, .error f', h => exact h
  | .ok (a, H1), .ok (a', H1'), h => exact ⟨⟨h.1, trivial⟩, h.2⟩

theorem fin1F_sim {k1 k : Kd} {SP SP' : SemWX} {F F'} (hP : Sim δ hb RE (LR δ [k1]) SP SP') (hF : Sim1 δ hb k1 k F F') :
    Sim δ hb RE (LR δ [k]) (fin1F SP F) (fin1F SP' F') := by
  intro env env' sp sp' H H' he hH hBd hS
  simp only [fin1F]
  refine bind_sim (hP env env' sp sp' H H' he hH hBd hS) fun v v' H1 H1' hv hH1 hB1 ht => ?_
  obtain ⟨a, a', rfl, rfl, hw⟩ := LR.one hv
  simp only
  exact out_trans (out_one (hF a a' _ _ H1 H1' hw hH1 hB1 (spR_sub 8 hS ht (by unfold Bnd at hB1; omega)))) ht

theorem fin2F_sim {k1 k2 k : Kd} {SP SP' : SemWX} {F F'} (hP : Sim δ hb RE (LR δ [k1, k2]) SP SP')
    (hF : Sim2 δ hb k1 k2 k F F') : Sim δ hb RE (LR δ [k]) (fin2F SP F) (fin2F SP' F') := by
  intro env env' sp sp' H H' he hH hBd hS
  simp only [fin2F]
  refine bind_sim (hP env env' sp sp' H H' he hH hBd hS) fun v v' H1 H1' hv hH1 hB1 ht => ?_
  obtain ⟨a, a', b, b', rfl, rfl, h1, h2⟩ := LR.two hv
  simp only
  exact out_trans (out_one (hF a a' b b' _ _ H1 H1' h1 h2 hH1 hB1
      (spR_sub 16 hS ht (by unfold Bnd at hB1; omega)))) ht

theorem fin3F_sim {k1 k2 k3 k : Kd} {SP SP' : SemWX} {F F'} (hP : Sim δ hb RE (LR δ [k1, k2, k3]) SP SP')
    (hF : Sim3 δ hb k1 k2 k3 k F F') : Sim δ hb RE (LR δ [k]) (fin3F SP F) (fin3F SP' F') := by
  intro env env' sp sp' H H' he hH hBd hS
  simp only [fin3F]
  refine bind_sim (hP env env' sp sp' H H' he hH hBd hS) fun v v' H1 H1' hv hH1 hB1 ht => ?_
  obtain ⟨a, a', b, b', c, c', rfl, rfl, h1, h2, h3⟩ := LR.three hv
  simp only
  exact out_trans (out_one (hF a a' b b' c c' _ _ H1 H1' h1 h2 h3 hH1 hB1
      (spR_sub 24 hS ht (by unfold Bnd at hB1; omega)))) ht

theorem oneF_sim {k : Kd} {S S' : Sem1X} (h : Sim δ hb RE (WR δ k) S S') : Sim δ hb RE (LR δ [k]) (oneF S) (oneF S') :=
  fun env env' sp sp' H H' he hH hBd hS => out_one (h env env' sp sp' H H' he hH hBd hS)

/-- a def / callee simulation on related argument lists -/
def SimD (δ hb : Nat) (ps rs : List Kd) (D D' : SemDX) : Prop :=
  ∀ args args' sp sp' H H', LR δ ps args args' → HR δ hb H H' → Bnd hb H → SpR δ H sp sp' →
    OutR (LR δ rs) δ hb H (D args sp H) (D' args' sp' H')

theorem callF_sim {pa : Nat} {ps rs : List Kd} {SA SA' : SemWX} {Sd Sd' : SemDX} (hA : Sim δ hb RE (LR δ ps) SA SA')
    (hD : SimD δ hb ps rs Sd Sd') : Sim δ hb RE (LR δ rs) (callF pa SA Sd) (callF pa SA' Sd') := by
  intro env env' sp sp' H H' he hH hBd hS
  simp only [callF]
  exact bind_sim (hA env env' sp sp' H H' he hH hBd hS) fun v v' H1 H1' hv hH1 hB1 ht =>
    out_trans (hD v v' _ _ H1 H1' hv hH1 hB1 (spR_sub _ hS ht (by unfold Bnd at hB1; omega))) ht

theorem localF_sim : ∀ (w k : Nat) (ks : List Kd) (hl : ks.length = w),
    (∀ i (hi : i < w), ∀ env env', RE env env' → WR δ (ks[i]'(by omega)) (env (k + i)) (env' (k + i))) →
    Sim δ hb RE (LR δ ks) (localF k w) (localF k w)
  | 0, k, [], _, _ => by simp only [localF]; exact nilF_sim
  | w + 1, k, kk :: ks, hl, h => by
    simp only [localF]
    have := pairF_sim (wa := 1) (ka := [kk]) (kb := ks)
      (leafF_sim (V := fun env => env k) (V' := fun env => env k) (fun env env' he => by simpa using h 0 (by omega) env env' he))
      (localF_sim w (k + 1) ks (by simpa using hl) (fun i hi env env' he => by
        have := h (i + 1) (by omega) env env' he
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this))
    simpa using this
  | 0, _, _ :: _, hl, _ => by simp at hl
  | _ + 1, _, [], hl, _ => by simp at hl

end

end NanoMain
