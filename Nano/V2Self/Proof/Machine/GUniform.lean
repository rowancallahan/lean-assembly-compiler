/- Every uniform target (`JTarget`: one fixed-size block of machine words per J instruction) is a general one
(`GTarget`): `tbytes` (the code bytes of a J program), `JTarget.uimg` (its image: those bytes, the uniform layout,
every pc an anchor), `JTarget.toG`, `rel_toG` / `rel_ofG`, and `laws_toG : T.Laws → T.toG.Laws`.  RISC-V and rv2arm
reach the host lift and the top theorems (proved over `GTarget` only) through this file. -/
import Nano.V2Self.Proof.Machine.GTarget
namespace JT
open Proven.Top SimW CallProbe

variable {T : JTarget}

/-- the code bytes of a J program on `T`: its words, 4 bytes each, little-endian -/
def tbytes (T : JTarget) (C : List J) : List UInt8 :=
  (C.flatMap T.enc).flatMap fun w => [wbyte w 0, wbyte w 1, wbyte w 2, wbyte w 3]

theorem flat_len {α β : Type} (f : α → List β) (n : Nat) (hf : ∀ a, (f a).length = n) :
    ∀ L : List α, (L.flatMap f).length = n * L.length
  | [] => by simp
  | a :: L => by simp only [List.flatMap_cons, List.length_append, hf, flat_len f n hf L, List.length_cons, Nat.mul_succ]; omega

theorem flat_get {α β : Type} (f : α → List β) (n : Nat) (hf : ∀ a, (f a).length = n) :
    ∀ (L : List α) (i r : Nat) (hi : i < L.length), r < n → (L.flatMap f)[n * i + r]? = (f L[i])[r]?
  | [], _, _, hi, _ => absurd hi (by simp)
  | a :: L, 0, r, _, hr => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add]
    rw [List.getElem?_append_left (by rw [hf]; exact hr)]; rfl
  | a :: L, i + 1, r, hi, hr => by
    simp only [List.flatMap_cons]
    rw [List.getElem?_append_right (by rw [hf, Nat.mul_succ]; omega), hf,
      show n * (i + 1) + r - n = n * i + r by rw [Nat.mul_succ]; omega]
    exact flat_get f n hf L i r (by simp at hi; omega) hr

theorem tbytes_len (L : T.Laws) (C : List J) : (tbytes T C).length = 4 * T.blockLen * C.length := by
  unfold tbytes
  rw [flat_len _ 4 (fun _ => rfl), flat_len _ _ L.enc_len, Nat.mul_assoc]

theorem tbytes_get (L : T.Laws) (C : List J) (i : Nat) (hi : i < C.length) (k : Nat) (hk : k < T.blockLen)
    (b : Nat) (hb : b < 4) :
    (tbytes T C)[4 * T.blockLen * i + 4 * k + b]? = (T.enc C[i])[k]?.map (wbyte · b) := by
  unfold tbytes
  have hl : T.blockLen * i + k < (C.flatMap T.enc).length := by
    rw [flat_len _ _ L.enc_len]
    have := Nat.mul_le_mul_left T.blockLen (show i + 1 ≤ C.length by omega)
    rw [Nat.mul_succ] at this; omega
  rw [show 4 * T.blockLen * i + 4 * k + b = 4 * (T.blockLen * i + k) + b by rw [Nat.mul_assoc, Nat.mul_add],
    flat_get _ 4 (fun _ => rfl) _ _ _ hl hb, ← flat_get T.enc _ L.enc_len C i k hi hk,
    List.getElem?_eq_getElem hl]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

/-! ## every uniform target is a general one -/

/-- the image of a uniform target: its blocks' bytes, the uniform layout, every pc an anchor -/
def JTarget.uimg (T : JTarget) (C : List J) : Img := ⟨tbytes T C, CallProbe.LinkLay.lin (T.blockLen - 1), fun _ => True⟩

def JTarget.toG (T : JTarget) : GTarget where
  M := T.M
  reg := T.reg
  scratch := T.scratch
  lay K C I := I = T.uimg C ∧ T.lay K C
  m0 := T.m0
  inv K C _ s := T.inv K C s
  valid C I := I = T.uimg C ∧ T.valid C
  loader := T.loader


/-- the uniform code relation (words of blocks) from the bytes -/
theorem ucode_of (L : T.Laws) {K : LayW} {C : List J} {o : MachineState}
    (h : ∀ a (h : a < (tbytes T C).length), o.memory (UInt64.ofNat (K.base + a)) = some (tbytes T C)[a]) :
    ∀ i (h : i < C.length) k (hk : k < (T.enc C[i]).length) b, b < 4 →
      o.memory (UInt64.ofNat (T.addr K.base i + 4 * k + b)) = some (wbyte (T.enc C[i])[k] b) := by
  intro i hi k hk b hb
  rw [L.enc_len] at hk
  have hlt : 4 * T.blockLen * i + 4 * k + b < (tbytes T C).length := by
    rw [tbytes_len L C]
    have := Nat.mul_le_mul_left (4 * T.blockLen) (show i + 1 ≤ C.length by omega)
    rw [Nat.mul_succ] at this; omega
  have e := tbytes_get L C i hi k hk b hb
  rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem (by rw [L.enc_len]; exact hk)] at e
  rw [JTarget.addr, show K.base + 4 * T.blockLen * i + 4 * k + b = K.base + (4 * T.blockLen * i + 4 * k + b) by omega,
    h _ hlt]
  exact e

/-- the bytes from the uniform code relation -/
theorem bytes_of (L : T.Laws) {K : LayW} {C : List J} {o : MachineState}
    (h : ∀ i (h : i < C.length) k (hk : k < (T.enc C[i]).length) b, b < 4 →
      o.memory (UInt64.ofNat (T.addr K.base i + 4 * k + b)) = some (wbyte (T.enc C[i])[k] b)) :
    ∀ a (h : a < (tbytes T C).length), o.memory (UInt64.ofNat (K.base + a)) = some (tbytes T C)[a] := by
  intro a ha
  have hp := L.blk_pos
  have hn := tbytes_len L C
  have hq : 0 < 4 * T.blockLen := by omega
  have hi : a / (4 * T.blockLen) < C.length := by
    rw [Nat.div_lt_iff_lt_mul hq, Nat.mul_comm]; omega
  have hr := Nat.mod_lt a hq
  have hk : a % (4 * T.blockLen) / 4 < T.blockLen := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
  have hb := Nat.mod_lt (a % (4 * T.blockLen)) (show 0 < 4 by decide)
  have ea : 4 * T.blockLen * (a / (4 * T.blockLen)) + 4 * (a % (4 * T.blockLen) / 4) + a % (4 * T.blockLen) % 4 = a := by
    have := Nat.div_add_mod a (4 * T.blockLen); have := Nat.div_add_mod (a % (4 * T.blockLen)) 4; omega
  have e := tbytes_get L C _ hi _ hk _ hb
  rw [ea, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem (by rw [L.enc_len]; exact hk)] at e
  have := h _ hi _ (by rw [L.enc_len]; exact hk) _ hb
  rw [JTarget.addr, show K.base + 4 * T.blockLen * (a / (4 * T.blockLen)) + 4 * (a % (4 * T.blockLen) / 4) +
    a % (4 * T.blockLen) % 4 = K.base + a by omega] at this
  rw [this]; exact e.symm

theorem uoff (L : T.Laws) (C : List J) (pc : Nat) : (T.uimg C).off pc = 4 * T.blockLen * pc := by
  have := L.blk_pos
  show 4 * (T.blockLen - 1 + 1) * pc = _; rw [show T.blockLen - 1 + 1 = T.blockLen by omega]

theorem rel_toG (L : T.Laws) {K : LayW} {C : List J} {s0 : T.M.State} {p : Nat × CallProbe.St} {s : T.M.State}
    (h : T.Rel K C s0 p s) : T.toG.Rel K C (T.uimg C) s0 p s where
  cfg := h.cfg
  pc := (h.pc : _ = UInt64.ofNat (T.addr K.base p.1)).trans (by rw [uoff L]; rfl)
  code := bytes_of L h.code
  x0 := h.x0
  bb := h.bb
  lk := h.ww
  x := h.x
  keep := h.keep
  w := h.w
  bw := h.bw
  fr := h.fr
  inv := h.inv

theorem rel_ofG (L : T.Laws) {K : LayW} {C : List J} {s0 : T.M.State} {p : Nat × CallProbe.St} {s : T.M.State}
    (h : T.toG.Rel K C (T.uimg C) s0 p s) : T.Rel K C s0 p s where
  cfg := h.cfg
  pc := (h.pc : (T.M.observe s).programCounter = _).trans (by rw [uoff L]; rfl)
  code := ucode_of L h.code
  x0 := h.x0
  bb := h.bb
  ww := h.lk
  x := h.x
  keep := h.keep
  w := h.w
  bw := h.bw
  fr := h.fr
  inv := h.inv

/-- **a uniform target's laws give the general laws** -/
theorem laws_toG (L : T.Laws) : T.toG.Laws where
  reg_map := L.reg_map
  kept_map := L.kept_map
  ram := L.ram
  lay_init K C I hK hv := by
    obtain ⟨rfl, hv⟩ := hv
    exact ⟨rfl, L.lay_init K C (by rw [← tbytes_len L C]; exact hK) hv⟩
  m0_obs := L.m0_obs
  inv_init K C I s call x sc hld hv hb hm0 hlo hhi hib hil hob hol := by
    obtain ⟨rfl, hv⟩ := hv
    exact L.inv_init K C s call _ x sc hld (tbytes_len L C) hb hm0 hlo hhi hib hil hob hol
  entry C I hv := by obtain ⟨rfl, -⟩ := hv; exact ⟨trivial, by rw [uoff L]; rfl⟩
  seg := by
    intro K C I s0 a z s n hl hR _ hrun _
    obtain ⟨rfl, hl⟩ := hl
    cases hrun with
    | head hS hs hrest =>
      obtain ⟨s', r, R⟩ := L.step_ok hl (rel_ofG L hR) hS hs
      exact ⟨0, _, s', Nat.zero_le _, hrest, trivial, r, rel_toG L R⟩
  addi_ok := by
    intro K C I s0 pc st s rd rs imm hl hR _ _ hc h1 h2 h3 h4
    obtain ⟨rfl, hl⟩ := hl
    obtain ⟨s', r, R⟩ := L.addi_ok hl (rel_ofG L hR) hc h1 h2 h3 h4
    exact ⟨s', r, rel_toG L R⟩
  ret_ok := by
    intro K C I s0 pc st s hl hR _ hc h4
    obtain ⟨rfl, hl⟩ := hl
    exact L.ret_ok hl (rel_ofG L hR) hc h4
  off_le C I hv n hn := by
    obtain ⟨rfl, -⟩ := hv
    rw [uoff L]; show _ ≤ (tbytes T C).length
    rw [tbytes_len L]; exact Nat.mul_le_mul_left _ hn
  vis_ret C I pc hv _ := by obtain ⟨rfl, -⟩ := hv; exact trivial
  vis_err C I pc imm hv _ _ := by obtain ⟨rfl, -⟩ := hv; exact ⟨trivial, trivial, trivial⟩

end JT
