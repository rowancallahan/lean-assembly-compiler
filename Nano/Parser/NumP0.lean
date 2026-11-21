/- Nano/Parser/NumP0: basics for the soundness proof of the numeral check `C.u10` (Nano/Parser/NumC.lean) against
`NumSpec.numOkP`: buffers as list prefixes, reading the serialization, node headers / children, skipping nodes (`u12`). -/
import Nano.Parser.NumC
import Nano.Parser.NumSpec
import Nano.Ownership.OwnP0
import Nano.Run.NdProgW
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-! ## words and buffers -/
theorem toU (n : Nat) : n.toUInt64 = u n := rfl


theorem u20_eq (b : Buf) {j : Nat} (hj : j < 2 ^ 64) (hb : b.length < 2 ^ 64) (v : UInt64) : u20 b (u j) v = OwnP.wr b j v := by
  unfold u20 wr
  by_cases h : j < b.length
  · simp only [bsize_u, u_lt hj hb, h, if_true, bset_u b hj]
  · simp only [bsize_u, u_lt hj hb, h, if_false, bpush]

theorem wr_prefix {L b : Buf} (h : L <+: b) (v : UInt64) : L ++ [v] <+: OwnP.wr b L.length v := by
  obtain ⟨r, rfl⟩ := h
  unfold wr
  cases r with
  | nil => simp
  | cons a r => simp [List.set_append_right, List.prefix_append]

theorem wr_len_le (b : Buf) (j : Nat) (v : UInt64) : (OwnP.wr b j v).length ≤ max b.length (j + 1) := by
  unfold wr; split <;> simp <;> omega

theorem prefix_getD {L b : Buf} (h : L <+: b) {k : Nat} (hk : k < L.length) : b.getD k 0 = L.getD k 0 := by
  obtain ⟨r, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem bget_pre {L b : Buf} (h : L <+: b) {k : Nat} (hk : k < L.length) (hk' : k < 2 ^ 64) : bget b (u k) = L.getD k 0 := by
  rw [bget_u b hk', prefix_getD h hk]

theorem drop_getD {x l r : Buf} {i : Nat} (h : x.drop i = l ++ r) (k : Nat) : x.getD (i + k) 0 = (l ++ r).getD k 0 := by
  rw [← h]; simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- read word k of `l` where `x.drop i = l ++ r` -/
theorem rd {x l r : Buf} {i : Nat} (h : x.drop i = l ++ r) {k : Nat} (hk : k < l.length) (hb : i + k < 2 ^ 64) :
    bget x (u (i + k)) = l.getD k 0 := by
  rw [bget_u x hb, drop_getD h k]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem drop_len {x l r : Buf} {i : Nat} (h : x.drop i = l ++ r) (hl : 0 < l.length) : i + l.length ≤ x.length := by
  have := congrArg List.length h; simp at this; omega

theorem drop_shift {x l1 l2 r : Buf} {i : Nat} (h : x.drop i = l1 ++ (l2 ++ r)) : x.drop (i + l1.length) = l2 ++ r := by
  rw [← List.drop_drop, h]; simp

/-! ## node headers and children -/
def kids : Nd → List Nd
  | .bin _ a b => [a, b] | .ite _ a b t e => [a, b, t, e] | .letE _ _ v b => [v, b] | .pair cs => cs
  | .call _ as => as | .prim _ as => as | .loop z s => [z, s] | .cont e => [e] | _ => []

def hdr : Nd → List UInt64
  | .const v => [1, v] | .loc s w => [2, u s, u w] | .bin op _ _ => [3, u op] | .ite c _ _ _ _ => [4, u c]
  | .letE s w _ _ => [5, u s, u w] | .pair cs => [6, u cs.length] | .call i as => [8, u i, u as.length]
  | .prim p _ => [9, u p] | .loop _ _ => [10] | .cont _ => [11]

theorem serL_append : ∀ l1 l2 : List Nd, serL (l1 ++ l2) = serL l1 ++ serL l2
  | [], _ => rfl
  | c :: l, l2 => by simp [serL, serL_append l l2]

theorem ser_hdr (e : Nd) : e.ser = hdr e ++ serL (kids e) := by
  cases e <;> simp [Nd.ser, hdr, kids, serL, toU]

theorem hdr_pos (e : Nd) : 1 ≤ (hdr e).length := by cases e <;> simp [hdr]

theorem ser_len_kids (e : Nd) : (serL (kids e)).length + 1 ≤ e.ser.length := by
  rw [ser_hdr e]; have := hdr_pos e; simp; omega

theorem ser_pos (e : Nd) : 1 ≤ e.ser.length := by rw [ser_hdr]; have := hdr_pos e; simp; omega

theorem len_le_serL : ∀ cs : List Nd, cs.length ≤ (serL cs).length
  | [] => by simp
  | c :: cs => by have := ser_pos c; have := len_le_serL cs; simp [serL]; omega

theorem mem_serL_len : ∀ {cs : List Nd} {c : Nd}, c ∈ cs → c.ser.length ≤ (serL cs).length
  | _ :: _, _, .head _ => by simp [serL]
  | _ :: _, _, .tail _ h => by have := mem_serL_len h; simp [serL]; omega

theorem kid_len {e c : Nd} (h : c ∈ kids e) : c.ser.length < e.ser.length := by
  have := mem_serL_len h; have := ser_len_kids e; omega

/-- node bounds the checker needs (`NB` with every `p`), children inherit them -/
def NBk (np : Nat) (e : Nd) : Prop := NB np e

theorem nbl_iff {np : Nat} : ∀ cs : List Nd, NBL np cs ↔ ∀ c ∈ cs, NB np c
  | [] => by simp [NBL]
  | c :: cs => by simp [NBL, nbl_iff cs]

theorem nb_kids {np : Nat} {e : Nd} (h : NB np e) : ∀ c ∈ kids e, NB np c := by
  cases e <;> simp only [NB, kids] at h ⊢ <;> simp_all [nbl_iff]

/-! ## skipping nodes: `u12` -/
theorem u12_succ (n : Nat) (x : Buf) (i k : UInt64) : u12 (n + 1) x i k =
    if k == 0 then i
    else
      let t := bget x i;
      if t == 1 then u12 n x (i + 2) (k - 1)
      else if t == 2 then u12 n x (i + 3) (k - 1)
      else if t == 3 then u12 n x (i + 2) (k + 1)
      else if t == 4 then u12 n x (i + 2) (k + 3)
      else if t == 5 then u12 n x (i + 3) (k + 1)
      else if t == 6 then u12 n x (i + 2) (k - 1 + bget x (i + 1))
      else if t == 8 then u12 n x (i + 3) (k - 1 + bget x (i + 2))
      else if t == 9 then u12 n x (i + 2) (k - 1 + g33 (bget x (i + 1)))
      else if t == 10 then u12 n x (i + 1) (k + 1)
      else if t == 11 then u12 n x (i + 1) k
      else 0 := rfl

theorem u_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) : (u a == u b) = false := by
  rw [u_beq ha hb]; simp [h]

/-- one node: skip its header, its children join the pending nodes -/
theorem u12_node {np : Nat} {x : Buf} {e : Nd} {r : Buf} {i k : Nat} (hx : x.drop i = e.ser ++ r) (hnb : NB np e)
    (hl : x.length < 2 ^ 64) (hk : k + 1 + (kids e).length < 2 ^ 64) (n : Nat) :
    u12 (n + 1) x (u i) (u (k + 1)) = u12 n x (u (i + (hdr e).length)) (u (k + (kids e).length)) := by
  have hil := drop_len hx (ser_pos e)
  have hk0 : (u (k + 1) == u 0) = false := u_ne (by omega) (by omega) (by omega)
  rw [u12_succ, show (0 : UInt64) = u 0 from rfl, hk0]
  simp only [Bool.false_eq_true, if_false]
  rw [ser_hdr e, List.append_assoc] at hx
  have hil2 : i + (hdr e).length ≤ x.length := by
    have := drop_len hx (hdr_pos e); omega
  have r0 := rd hx (k := 0) (by have := hdr_pos e; omega) (by have := hdr_pos e; omega)
  rw [Nat.add_zero] at r0
  rw [r0]
  have hsub : u (k + 1) - 1 = u k := by rw [show (1 : UInt64) = u 1 from rfl, u_sub (by omega) (by omega)]; rfl
  have hsub' : u (k + 1) - u 1 = u k := hsub
  have ha : ∀ m : Nat, u i + (OfNat.ofNat m : UInt64) = u (i + m) := fun m => by rw [lit, u_add]
  cases e with
  | const v => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub']
  | loc s w => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub']
  | bin op a b => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub']
  | ite c a b t el => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub']
  | letE s w v b => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub']
  | pair cs =>
    have r1 := rd hx (k := 1) (by simp [hdr]) (by simp [hdr] at hil2; omega)
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at r1
    simp only [hdr, kids, List.getD_cons_zero]; simp; rw [ha 1, r1]; simp only [lit, u_add, hsub']
  | call id as =>
    have r2 := rd hx (k := 2) (by simp [hdr]) (by simp [hdr] at hil2; omega)
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at r2
    simp only [hdr, kids, List.getD_cons_zero]; simp; rw [ha 2, r2]; simp only [lit, u_add, hsub']
  | prim pn as =>
    have r1 := rd hx (k := 1) (by simp [hdr]) (by simp [hdr] at hil2; omega)
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at r1
    obtain ⟨hp, hpa, -⟩ := hnb
    have hg : g33 (u pn) = u as.length := by
      rw [hpa]; simp only [toU]; unfold u; simp
    simp only [hdr, kids, List.getD_cons_zero]; simp; rw [ha 1, r1, hg]; simp only [lit, u_add, hsub']
  | loop z s => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub']
  | cont e => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub']

theorem u12_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 64) : ∀ (n : Nat) (es : List Nd) (r : Buf) (i : Nat),
    x.drop i = serL es ++ r → (∀ e ∈ es, NB np e) →
    u12 n x (u i) (u es.length) = 0 ∨ u12 n x (u i) (u es.length) = u (i + (serL es).length)
  | 0, _, _, _, _, _ => Or.inl rfl
  | n + 1, [], r, i, _, _ => Or.inr (by rw [u12_succ]; simp [serL, show u 0 = 0 from rfl])
  | n + 1, e :: es, r, i, hx, hnb => by
    have hx' : x.drop i = e.ser ++ (serL es ++ r) := by rw [hx]; simp [serL]
    have hil := drop_len hx (by simp [serL]; have := ser_pos e; omega)
    have h1 := len_le_serL (kids e ++ es)
    rw [serL_append] at h1
    have h2 := ser_len_kids e
    simp only [serL, List.length_append] at hil h1
    have hk : es.length + 1 + (kids e).length < 2 ^ 64 := by omega
    rw [List.length_cons, u12_node hx' (hnb e (by simp)) hl hk n]
    have hx2 : x.drop (i + (hdr e).length) = serL (kids e ++ es) ++ r := by
      rw [serL_append, List.append_assoc]; apply drop_shift; rw [hx', ser_hdr e]; simp
    have ih := u12_ok hl n (kids e ++ es) r _ hx2 (by
      intro c hc; rcases List.mem_append.1 hc with hc | hc
      · exact nb_kids (hnb e (by simp)) c hc
      · exact hnb c (by simp [hc]))
    rw [List.length_append, Nat.add_comm (kids e).length] at ih
    rcases ih with ih | ih
    · exact Or.inl ih
    · right; rw [ih]; congr 1; rw [serL_append]; simp [serL, ser_hdr e]; omega

/-- `u15`: the end of the node at i -/
theorem u15_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 64) {e : Nd} {r : Buf} {i : Nat} (hx : x.drop i = e.ser ++ r)
    (hnb : NB np e) : u15 x (u i) = 0 ∨ (u15 x (u i) = u (i + e.ser.length) ∧ i ≠ 0) := by
  unfold u15
  have hil := drop_len hx (ser_pos e)
  by_cases h0 : i = 0
  · subst h0; left; rfl
  · have : (u i == u 0) = false := u_ne (by omega) (by omega) h0
    rw [show (0 : UInt64) = u 0 from rfl, this]; simp only [Bool.false_eq_true, if_false]
    have := u12_ok hl 16777216 [e] r i (by simpa [serL] using hx) (by simpa using hnb)
    simp only [List.length_singleton, serL, List.append_nil] at this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h0⟩

end NumP
