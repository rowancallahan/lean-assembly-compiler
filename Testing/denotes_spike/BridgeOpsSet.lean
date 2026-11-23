/- Set-level lemmas for the BridgeOps equations (pattern of `add_u64` / `ite_bool` in DenotesSpike.lean).
Heads (`LEN`, `GETD`, ...) are the sets the model gives the head constants applied to their type/instance arguments;
every hypothesis is exactly what `transfer` yields from the named theorem of BridgeOps.lean.
Check with `lake env lean` inside the con-leche checkout (4.35.0-rc3). -/
import ConLeche.Denotes
import ConLeche.SetModel.Ops

namespace BridgeOpsSet
open ConLeche ConLeche.SetModel SetTheory

universe w
variable {V : Type w} [SetTheory V]

/-! ## encodings (as in DenotesSpike): `nat k = ⟦succ^k zero⟧`, `u x = ⟦ofNat⟧ (nat x.toNat)`, lists = constructor terms -/
section
variable (Z S : V)

noncomputable def nat : Nat → V
  | 0 => Z
  | k + 1 => app S (nat k)

theorem add_nat (ADD : V) (hz : ∀ x, app (app ADD x) Z = x)
    (hs : ∀ x y, app (app ADD x) (app S y) = app S (app (app ADD x) y)) :
    ∀ a b, app (app ADD (nat Z S a)) (nat Z S b) = nat Z S (a + b) := by
  intro a b
  induction b with
  | zero => exact hz _
  | succ b ih => rw [nat, hs, ih]; rfl

/-- `ofNat` wraps: from `ofNat (n + N) = ofNat n` (UInt8: `bo_wrap8`, UInt64: `br_wrap`) get `ofNat k = ofNat (k % N)`. -/
theorem wrap_mod (ADD OF : V) (N : Nat) (hN : 0 < N) (hz : ∀ x, app (app ADD x) Z = x)
    (hs : ∀ x y, app (app ADD x) (app S y) = app S (app (app ADD x) y))
    (hwrap : ∀ x, app OF (app (app ADD x) (nat Z S N)) = app OF x) :
    ∀ k, app OF (nat Z S k) = app OF (nat Z S (k % N)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h : k < N
    · rw [Nat.mod_eq_of_lt h]
    · have hk : k = (k - N) + N := by omega
      have h1 : app OF (nat Z S k) = app OF (nat Z S (k - N)) := by
        have e : app OF (nat Z S k) = app OF (nat Z S ((k - N) + N)) := by rw [← hk]
        have e2 : nat Z S ((k - N) + N) = app (app ADD (nat Z S (k - N))) (nat Z S N) := (add_nat Z S ADD hz hs _ _).symm
        rw [e, e2, hwrap]
      have h3 : k % N = (k - N) % N := Nat.mod_eq_sub_mod (by omega)
      rw [h1, ih (k - N) (by omega), h3]

/-! ### control -/

/-- ite (`bo_ite_t/f`): as in DenotesSpike. -/
theorem ite_bool (ITE_T ITE_F : V) (R t e : V)
    (ht : app (app (app ITE_T R) t) e = t) (hf : app (app (app ITE_F R) t) e = e) (c : Bool) :
    app (app (app (if c then ITE_T else ITE_F) R) t) e = if c then t else e := by
  cases c <;> simpa

/-- `Nat.casesOn` (`bo_nat_z`, `bo_nat_s`): `CASES` = `⟦@Nat.casesOn⟧`, `M` the motive. -/
theorem nat_cases (CASES : V)
    (hz : ∀ M z s, app (app (app (app CASES M) Z) z) s = z)
    (hs : ∀ M n z s, app (app (app (app CASES M) (app S n)) z) s = app s n) (_M z s : V) :
    ∀ k, app (app (app (app CASES M) (nat Z S k)) z) s = (match k with | 0 => z | k + 1 => app s (nat Z S k)) := by
  intro k; cases k with
  | zero => exact hz _ _ _
  | succ k => exact hs _ _ _ _

/-- `Prod.casesOn` (`bo_prod`): `PAIR a b` the encoding of `(a, b)` (constructor, free). -/
theorem prod_cases (CASES PAIR : V → V → V) (A B M f : V)
    (h : ∀ a b, app (app (CASES A B) (PAIR a b)) f = app (app f a) b) (a b : V) :
    app (app (CASES A B) (PAIR a b)) f = app (app f a) b := h a b

/-! ### lists -/

variable {α : Type} (NIL CONS : V) (enc : α → V)

/-- the list encoding: constructor terms, `CONS = ⟦@List.cons T⟧`, `NIL = ⟦@List.nil T⟧` -/
noncomputable def lst : List α → V
  | [] => NIL
  | a :: l => app (app CONS (enc a)) (lst l)

/-- `List.length` (`bo_length_nil/cons`) -/
theorem length_nat (LEN : V) (hn : app LEN NIL = Z)
    (hc : ∀ a l, app LEN (app (app CONS a) l) = app S (app LEN l)) :
    ∀ l : List α, app LEN (lst NIL CONS enc l) = nat Z S l.length := by
  intro l; induction l with
  | nil => exact hn
  | cons a l ih => simp only [lst, hc, ih, List.length_cons, nat]

/-- `len'` (`bo_len'`) -/
theorem len'_set (LENp LEN : V) (hu : ∀ xs, app LENp xs = app LEN xs) (hn : app LEN NIL = Z)
    (hc : ∀ a l, app LEN (app (app CONS a) l) = app S (app LEN l)) (l : List α) :
    app LENp (lst NIL CONS enc l) = nat Z S l.length := by
  rw [hu]; exact length_nat Z S NIL CONS enc LEN hn hc l

/-- `len` and `bsize` (`bo_len`, `bo_bsize`, `bo_toUInt64`): result `u64 (l.length.toUInt64)`.
`OF` = `⟦UInt64.ofNat⟧`, `TOU` = `⟦Nat.toUInt64⟧`, `ADD` = `⟦Nat.add⟧`; no size bound needed (the `% 2^64` is absorbed by `wrap_mod`). -/
theorem len64_set (LEN64 LEN TOU OF ADD : V) (hu : ∀ xs, app LEN64 xs = app TOU (app LEN xs))
    (htou : ∀ n, app TOU n = app OF n) (hn : app LEN NIL = Z)
    (hc : ∀ a l, app LEN (app (app CONS a) l) = app S (app LEN l))
    (hz : ∀ x, app (app ADD x) Z = x)
    (hs : ∀ x y, app (app ADD x) (app S y) = app S (app (app ADD x) y))
    (hwrap : ∀ x, app OF (app (app ADD x) (nat Z S UInt64.size)) = app OF x) (l : List α) :
    app LEN64 (lst NIL CONS enc l) = app OF (nat Z S (l.length.toUInt64).toNat) := by
  rw [hu, htou, length_nat Z S NIL CONS enc LEN hn hc,
    wrap_mod Z S ADD OF UInt64.size (by decide) hz hs hwrap, UInt64.toNat_ofNat']

/-- `List.getD` (`bo_getD_*`) at a canonical index and any default encoding -/
theorem getD_set (GETD : V) (hn : ∀ n d, app (app (app GETD NIL) n) d = d)
    (h0 : ∀ a l d, app (app (app GETD (app (app CONS a) l)) Z) d = a)
    (hs : ∀ a l n d, app (app (app GETD (app (app CONS a) l)) (app S n)) d = app (app (app GETD l) n) d)
    (dflt : α) : ∀ (l : List α) (k : Nat),
      app (app (app GETD (lst NIL CONS enc l)) (nat Z S k)) (enc dflt) = enc (l.getD k dflt) := by
  intro l; induction l with
  | nil => intro k; simp [lst, hn]
  | cons a l ih =>
    intro k; cases k with
    | zero => simp [lst, nat, h0]
    | succ k => simp only [lst, nat, hs, ih]; simp

/-- `List.set` (`bo_set_*`) -/
theorem set_set (SET : V) (hn : ∀ n v, app (app (app SET NIL) n) v = NIL)
    (h0 : ∀ a l v, app (app (app SET (app (app CONS a) l)) Z) v = app (app CONS v) l)
    (hs : ∀ a l n v, app (app (app SET (app (app CONS a) l)) (app S n)) v =
      app (app CONS a) (app (app (app SET l) n) v)) (v : α) :
    ∀ (l : List α) (k : Nat), app (app (app SET (lst NIL CONS enc l)) (nat Z S k)) (enc v) =
      lst NIL CONS enc (l.set k v) := by
  intro l; induction l with
  | nil => intro k; simp [lst, hn]
  | cons a l ih =>
    intro k; cases k with
    | zero => simp [lst, nat, h0]
    | succ k => simp only [lst, nat, hs, ih, List.set_cons_succ]

/-- `++` (`bo_app_nil/cons`) -/
theorem append_set (APP : V) (hn : ∀ l, app (app APP NIL) l = l)
    (hc : ∀ a l m, app (app APP (app (app CONS a) l)) m = app (app CONS a) (app (app APP l) m)) :
    ∀ (xs ys : List α), app (app APP (lst NIL CONS enc xs)) (lst NIL CONS enc ys) = lst NIL CONS enc (xs ++ ys) := by
  intro xs ys; induction xs with
  | nil => exact hn _
  | cons a l ih => simp only [lst, hc, ih, List.cons_append]

end

/-! ### the prelude ops.  `u OF x = ⟦OF⟧ (nat x.toNat)` is the scalar encoding (`OF` = ofNat of UInt8 / UInt64). -/
section Ops
variable (Z S : V)

/-- index conversion: `⟦UInt64.toNat⟧ (u64 i) = nat i.toNat`, from `bo_toNat_ofNat` and `k % 2^64 = k` at the set level. -/
theorem idx_set (TONAT OF MOD : V) (htn : ∀ n, app TONAT (app OF n) = app (app MOD n) (nat Z S UInt64.size))
    (hmod : ∀ k, k < UInt64.size → app (app MOD (nat Z S k)) (nat Z S UInt64.size) = nat Z S k) (i : UInt64) :
    app TONAT (app OF (nat Z S i.toNat)) = nat Z S i.toNat := by
  rw [htn, hmod _ i.toNat_lt_size]

/-- **rd** (`bo_rd` + getD + `bo_u8to64`).  Input list of bytes `u8 x = OF8 (nat x.toNat)`, index `u64 i`, result `u64`.
`D` = `⟦(0 : UInt8)⟧` = `OF8 (nat 0)` (`br_lit`-style). Hypotheses `hmod256` is the `%` fact for the byte widening. -/
theorem rd_set {NIL CONS OF8 OF RD GETD TO64 TONAT MOD : V}
    (hrd : ∀ xs i, app (app RD xs) i = app TO64 (app (app (app GETD xs) (app TONAT i)) (app OF8 Z)))
    (hgn : ∀ n d, app (app (app GETD NIL) n) d = d)
    (hg0 : ∀ a l d, app (app (app GETD (app (app CONS a) l)) Z) d = a)
    (hgs : ∀ a l n d, app (app (app GETD (app (app CONS a) l)) (app S n)) d = app (app (app GETD l) n) d)
    (hconv : ∀ n, app TO64 (app OF8 n) = app OF (app (app MOD n) (nat Z S 256)))
    (hmod256 : ∀ k, k < 256 → app (app MOD (nat Z S k)) (nat Z S 256) = nat Z S k)
    (htn : ∀ n, app TONAT (app OF n) = app (app MOD n) (nat Z S UInt64.size))
    (hmod : ∀ k, k < UInt64.size → app (app MOD (nat Z S k)) (nat Z S UInt64.size) = nat Z S k)
    (xs : List UInt8) (i : UInt64) :
    app (app RD (lst NIL CONS (fun x : UInt8 => app OF8 (nat Z S x.toNat)) xs)) (app OF (nat Z S i.toNat)) =
      app OF (nat Z S ((xs.getD i.toNat 0).toUInt64).toNat) := by
  rw [hrd, idx_set Z S TONAT OF MOD htn hmod]
  have hg := getD_set Z S NIL CONS (fun x : UInt8 => app OF8 (nat Z S x.toNat)) GETD hgn hg0 hgs (0 : UInt8) xs i.toNat
  have h0 : app OF8 Z = app OF8 (nat Z S (0 : UInt8).toNat) := rfl
  rw [h0, hg, hconv, hmod256 _ (UInt8.toNat_lt _)]
  simp [UInt8.toNat_toUInt64]

/-- **bget** (`bo_bget`): as `rd` without the widening; `D = OF (nat 0)`. -/
theorem bget_set {NIL CONS OF BGET GETD TONAT MOD : V}
    (hb : ∀ xs i, app (app BGET xs) i = app (app (app GETD xs) (app TONAT i)) (app OF Z))
    (hgn : ∀ n d, app (app (app GETD NIL) n) d = d)
    (hg0 : ∀ a l d, app (app (app GETD (app (app CONS a) l)) Z) d = a)
    (hgs : ∀ a l n d, app (app (app GETD (app (app CONS a) l)) (app S n)) d = app (app (app GETD l) n) d)
    (htn : ∀ n, app TONAT (app OF n) = app (app MOD n) (nat Z S UInt64.size))
    (hmod : ∀ k, k < UInt64.size → app (app MOD (nat Z S k)) (nat Z S UInt64.size) = nat Z S k)
    (b : List UInt64) (i : UInt64) :
    app (app BGET (lst NIL CONS (fun x : UInt64 => app OF (nat Z S x.toNat)) b)) (app OF (nat Z S i.toNat)) =
      app OF (nat Z S (b.getD i.toNat 0).toNat) := by
  rw [hb, idx_set Z S TONAT OF MOD htn hmod]
  exact getD_set Z S NIL CONS (fun x : UInt64 => app OF (nat Z S x.toNat)) GETD hgn hg0 hgs (0 : UInt64) b i.toNat

/-- **bset** (`bo_bset`) -/
theorem bset_set {NIL CONS OF BSET SET TONAT MOD : V}
    (hb : ∀ b i v, app (app (app BSET b) i) v = app (app (app SET b) (app TONAT i)) v)
    (hn : ∀ n v, app (app (app SET NIL) n) v = NIL)
    (h0 : ∀ a l v, app (app (app SET (app (app CONS a) l)) Z) v = app (app CONS v) l)
    (hs : ∀ a l n v, app (app (app SET (app (app CONS a) l)) (app S n)) v =
      app (app CONS a) (app (app (app SET l) n) v))
    (htn : ∀ n, app TONAT (app OF n) = app (app MOD n) (nat Z S UInt64.size))
    (hmod : ∀ k, k < UInt64.size → app (app MOD (nat Z S k)) (nat Z S UInt64.size) = nat Z S k)
    (b : List UInt64) (i v : UInt64) :
    app (app (app BSET (lst NIL CONS (fun x : UInt64 => app OF (nat Z S x.toNat)) b)) (app OF (nat Z S i.toNat)))
        (app OF (nat Z S v.toNat)) =
      lst NIL CONS (fun x : UInt64 => app OF (nat Z S x.toNat)) (b.set i.toNat v) := by
  rw [hb, idx_set Z S TONAT OF MOD htn hmod]
  exact set_set Z S NIL CONS (fun x : UInt64 => app OF (nat Z S x.toNat)) SET hn h0 hs v b i.toNat

/-- **bpush** (`bo_bpush`, `bo_app_*`): `b ++ [v]`, with `[v] = CONS v NIL`. -/
theorem bpush_set {NIL CONS OF BPUSH APP : V}
    (hb : ∀ b v, app (app BPUSH b) v = app (app APP b) (app (app CONS v) NIL))
    (hn : ∀ l, app (app APP NIL) l = l)
    (hc : ∀ a l m, app (app APP (app (app CONS a) l)) m = app (app CONS a) (app (app APP l) m))
    (b : List UInt64) (v : UInt64) :
    app (app BPUSH (lst NIL CONS (fun x : UInt64 => app OF (nat Z S x.toNat)) b)) (app OF (nat Z S v.toNat)) =
      lst NIL CONS (fun x : UInt64 => app OF (nat Z S x.toNat)) (b ++ [v]) := by
  rw [hb]
  have := append_set NIL CONS (fun x : UInt64 => app OF (nat Z S x.toNat)) APP hn hc b [v]
  simpa [lst] using this

/-- **put** (`bo_put`, `bo_u64to8`, `bo_wrap8`): `o ++ [b.toUInt8]`.  `TO8 = ⟦UInt64.toUInt8⟧`, `OF` = UInt64.ofNat,
`OF8` = UInt8.ofNat. -/
theorem put_set {NIL CONS OF OF8 PUT APP TO8 ADD : V}
    (hp : ∀ o b, app (app PUT o) b = app (app APP o) (app (app CONS (app TO8 b)) NIL))
    (hto8 : ∀ n, app TO8 (app OF n) = app OF8 n)
    (hn : ∀ l, app (app APP NIL) l = l)
    (hc : ∀ a l m, app (app APP (app (app CONS a) l)) m = app (app CONS a) (app (app APP l) m))
    (hz : ∀ x, app (app ADD x) Z = x)
    (hs : ∀ x y, app (app ADD x) (app S y) = app S (app (app ADD x) y))
    (hwrap8 : ∀ x, app OF8 (app (app ADD x) (nat Z S 256)) = app OF8 x)
    (o : List UInt8) (b : UInt64) :
    app (app PUT (lst NIL CONS (fun x : UInt8 => app OF8 (nat Z S x.toNat)) o)) (app OF (nat Z S b.toNat)) =
      lst NIL CONS (fun x : UInt8 => app OF8 (nat Z S x.toNat)) (o ++ [b.toUInt8]) := by
  rw [hp, hto8]
  have := append_set NIL CONS (fun x : UInt8 => app OF8 (nat Z S x.toNat)) APP hn hc o [b.toUInt8]
  have hw := wrap_mod Z S ADD OF8 256 (by decide) hz hs hwrap8 b.toNat
  have hv : (b.toUInt8).toNat = b.toNat % 256 := UInt64.toNat_toUInt8 b
  rw [hw, ← hv]
  simpa [lst] using this

end Ops
end BridgeOpsSet

#print axioms BridgeOpsSet.wrap_mod
#print axioms BridgeOpsSet.len64_set
#print axioms BridgeOpsSet.rd_set
#print axioms BridgeOpsSet.bget_set
#print axioms BridgeOpsSet.bset_set
#print axioms BridgeOpsSet.bpush_set
#print axioms BridgeOpsSet.put_set
#print axioms BridgeOpsSet.nat_cases
