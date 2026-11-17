/- Nano/V2Self/C: assembler stage on Buf (from Nano/V2Self/Asm.lean) -/
import Nano.V2Self.C.Base
namespace C

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
def k7 : UInt64 := 7
def k128 : UInt64 := 128

def a0 (p q t : UInt64) : UInt64 :=
  let v100 := (if p == 3 then k1 else k0); let v101 := (if p == 4 then k1 else k0); let v102 := v100 ||| v101; if v102 == k1 then ((q &&& k1) <<< 7) ||| k3
  else let v103 := (if p == 0 then k1 else k0); let v104 := (if p == 1 then k1 else k0); let v105 := v103 ||| v104; let v106 := (if p == 5 then k1 else k0); let v107 := v105 ||| v106; let v108 := (if p == 6 then k1 else k0); let v109 := v107 ||| v108; let v110 := (if p == 8 then k1 else k0); let v111 := v109 ||| v110; if v111 == k1 then ((q &&& k1) <<< 7) ||| k19
  else if p == 11 then k35
  else if p == 16 then ((t &&& k1) <<< 7) ||| k35
  else let v112 := (if p == 14 then k1 else k0); let v113 := (if p == 24 then k1 else k0); let v114 := v112 ||| v113; let v115 := (if p == 32 then k1 else k0); let v116 := v114 ||| v115; let v117 := (if p == 40 then k1 else k0); let v118 := v116 ||| v117; if v118 == k1 then ((q &&& k1) <<< 7) ||| k51
  else if p == 7 then k99
  else if p == 48 then ((q &&& k1) <<< 7) ||| k103
  else k19

def a1 (p q s t : UInt64) : UInt64 :=
  if p == 11 then ((t &&& k3) <<< 2) ||| k48 ||| ((s &&& k1) <<< 7)
  else if p == 16 then ((t >>> 1) &&& k15) ||| ((s &&& k1) <<< 7)
  else if p == 7 then k118 ||| ((s &&& k1) <<< 7)
  else (q >>> 1) ||| ((p &&& k7) <<< 4) ||| ((s &&& k1) <<< 7)

def a2 (p q s t : UInt64) : UInt64 :=
  let v119 := (if p == 3 then k1 else k0); let v120 := (if p == 8 then k1 else k0); let v121 := v119 ||| v120; if v121 == k1 then (s >>> 1) ||| ((t &&& k1) <<< 7)
  else let v122 := (if p == 11 then k1 else k0); let v123 := (if p == 16 then k1 else k0); let v124 := v122 ||| v123; if v124 == k1 then (s >>> 1) ||| ((q &&& k15) <<< 4)
  else (s >>> 1) ||| ((t &&& k15) <<< 4)

def a3 (p q t : UInt64) : UInt64 :=
  let v125 := (if p == 3 then k1 else k0); let v126 := (if p == 8 then k1 else k0); let v127 := v125 ||| v126; if v127 == k1 then t >>> 1
  else if p == 0 then
    let u := if t < k128 then k0 else k240;
    (t >>> 4) ||| u
  else if p == 11 then ((t >>> 2) <<< 1) ||| (q >>> 4)
  else if p == 16 then q >>> 4
  else if p == 32 then (t >>> 4) ||| k64
  else if p == 40 then (t >>> 4) ||| k2
  else t >>> 4

def a4 : Nat → Buf → UInt64 → Buf → Buf
  | 0, x, i, o => o
  | n + 1, x, i, o =>
    let v128 := (if bsize x < i + 4 then k0 else k1); if v128 == k1 then
      let p := bget x i;
      let q := bget x (i + 1);
      let s := bget x (i + 2);
      let t := bget x (i + 3);
      a4 n x (i + 4) (q0 (q0 (q0 (q0 o (a0 p q t)) (a1 p q s t)) (a2 p q s t)) (a3 p q t))
    else o

def a5 (x : Buf) : Buf := a4 16777216 x 0 bnew

end C
