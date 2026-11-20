/- Nano/V2Self: the assembler stage (Nano/V2S/Asm.lean) in the nano subset.  Equal to `Nano.V2S.asmV` by `rfl`
(Nano/V2Self/Legacy/Bridge.lean). -/
import Nano.V2Self.Prelude

def k3 : UInt64 := 3
def k19 : UInt64 := 19
def k35 : UInt64 := 35
def k51 : UInt64 := 51
def k99 : UInt64 := 99
def k103 : UInt64 := 103
def k48 : UInt64 := 48
def k118 : UInt64 := 118
def k240 : UInt64 := 240
def k64 : UInt64 := 64
def k2 : UInt64 := 2
def k15 : UInt64 := 15
def k1 : UInt64 := 1
def k7 : UInt64 := 7
def k0 : UInt64 := 0
def k128 : UInt64 := 128

def a0 (p q t : UInt64) : UInt64 :=
  if p == 3 || p == 4 then ((q &&& k1) <<< 7) ||| k3
  else if p == 0 || p == 1 || p == 5 || p == 6 || p == 8 then ((q &&& k1) <<< 7) ||| k19
  else if p == 11 then k35
  else if p == 16 then ((t &&& k1) <<< 7) ||| k35
  else if p == 14 || p == 24 || p == 32 || p == 40 then ((q &&& k1) <<< 7) ||| k51
  else if p == 7 then k99
  else if p == 48 then ((q &&& k1) <<< 7) ||| k103
  else k19

def a1 (p q s t : UInt64) : UInt64 :=
  if p == 11 then ((t &&& k3) <<< 2) ||| k48 ||| ((s &&& k1) <<< 7)
  else if p == 16 then ((t >>> 1) &&& k15) ||| ((s &&& k1) <<< 7)
  else if p == 7 then k118 ||| ((s &&& k1) <<< 7)
  else (q >>> 1) ||| ((p &&& k7) <<< 4) ||| ((s &&& k1) <<< 7)

def a2 (p q s t : UInt64) : UInt64 :=
  if p == 3 || p == 8 then (s >>> 1) ||| ((t &&& k1) <<< 7)
  else if p == 11 || p == 16 then (s >>> 1) ||| ((q &&& k15) <<< 4)
  else (s >>> 1) ||| ((t &&& k15) <<< 4)

def a3 (p q t : UInt64) : UInt64 :=
  if p == 3 || p == 8 then t >>> 1
  else if p == 0 then
    let u := if t < k128 then k0 else k240;
    (t >>> 4) ||| u
  else if p == 11 then ((t >>> 2) <<< 1) ||| (q >>> 4)
  else if p == 16 then q >>> 4
  else if p == 32 then (t >>> 4) ||| k64
  else if p == 40 then (t >>> 4) ||| k2
  else t >>> 4

def a4 : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, o => o
  | n + 1, x, i, o =>
    if i + 4 ≤ len x then
      let p := rd x i;
      let q := rd x (i + 1);
      let s := rd x (i + 2);
      let t := rd x (i + 3);
      a4 n x (i + 4) (put (put (put (put o (a0 p q t)) (a1 p q s t)) (a2 p q s t)) (a3 p q t))
    else o

def a5 (x : List UInt8) : List UInt8 := a4 (len' x) x 0 []
