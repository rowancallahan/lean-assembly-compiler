/- Nano/V2Self/Proof/Cert/OutSpec: the four defs of C that build the OUTPUT byte list (`put`, `[]`), as WORD-level shadows
(`bpush`, `bnew`: the meaning `Sem` keeps whole words in the output buffer and takes the low bytes at the very end).
The shadows are the source text with `put ↦ bpush`, `[] ↦ bnew`; `*_map`: their low bytes are the Lean defs. -/
import Nano.V2Self.C.Gen
import Nano.V2Self.C.Own
import Nano.V2Self.C.Par1
import Nano.V2Self.C.Lex2

namespace Cert.Sh

def g40 : Nat → List UInt8 → Buf → UInt64 → Buf → Buf
  | 0, c, w, i, o => o
  | n + 1, c, w, i, o =>
    if i < bsize w then
      let v := bget w i;
      g40 n c w (i + 1) (bpush (bpush (bpush (bpush o v) (v >>> 8)) (v >>> 16)) (v >>> 24))
    else o

def g42 (c : List UInt8) (x : Buf) (u : UInt64) : Buf :=
  if 2147483647 < bsize x then bnew else
  if bget x 0 == 2 then
    let (x2, w) := C.g53 x;
    if w == 0 then bnew else
    let r := bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) u;
    let (r1, o) := C.g39 16777216 x2 r (C.g34 bnew) bnew bnew bnew;
    if bget r1 4 == 1 then bnew else if 16777215 < bsize o then bnew else if 262143 < bsize o then bnew else
    g40 16777216 c o 0 bnew
  else bnew

def g41 (c : List UInt8) (x : Buf) : Buf := g42 c x C.g_999

def m (x : List UInt8) : Buf := g41 x (C.o41 (C.y16 (C.s10 x)))

/-- the driver of `build_self_S.py` as a Lean function -/
def mLean (x : List UInt8) : List UInt8 := C.g41 x (C.o41 (C.y16 (C.s10 x)))

theorem g40_map : ∀ (n : Nat) (c : List UInt8) (w : Buf) (i : UInt64) (o : Buf),
    (g40 n c w i o).map UInt64.toUInt8 = C.g40 n c w i (o.map UInt64.toUInt8)
  | 0, c, w, i, o => by simp [g40, C.g40]
  | n + 1, c, w, i, o => by
    simp only [g40, C.g40]
    by_cases h : i < bsize w
    · simp only [h, if_true]; rw [g40_map n]; simp [bpush, put]
    · simp only [h, if_false]

theorem g42_map (c : List UInt8) (x : Buf) (u : UInt64) : (g42 c x u).map UInt64.toUInt8 = C.g42 c x u := by
  unfold g42 C.g42
  -- keep the fuel opaque: `simp` must not unfold the loops
  generalize hN : (16777216 : Nat) = N; revert N; apply id; intro N hN
  by_cases h0 : 2147483647 < bsize x
  · simp only [h0, if_true]; rfl
  simp only [h0, if_false]
  by_cases h1 : (bget x 0 == 2) = true
  · simp only [h1, if_true]
    rcases C.g53 x with ⟨x2, w⟩
    simp only []
    by_cases h2 : (w == 0) = true
    · simp only [h2, if_true]; rfl
    · simp only [h2]
      rcases C.g39 N x2 (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) u)
        (C.g34 bnew) bnew bnew bnew with ⟨r1, o⟩
      simp only []
      by_cases h3 : (bget r1 4 == 1) = true
      · simp only [h3, if_true]; rfl
      · simp only [h3]
        by_cases h4 : 16777215 < bsize o
        · simp only [h4, if_true]; rfl
        · simp only [h4]
          by_cases h5 : 262143 < bsize o
          · simp only [h5, if_true]; rfl
          · simp only [h5]; exact g40_map _ _ _ _ _
  · simp only [h1]; rfl

theorem m_map (x : List UInt8) : (m x).map UInt64.toUInt8 = mLean x := by
  unfold m mLean g41 C.g41; exact g42_map _ _ _

end Cert.Sh
