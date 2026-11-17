/- Nano/V2Self/C: lexer stage, program input in, Buf out (from Nano/V2Self/Lex.lean) -/
import Nano.V2Self.C.Base
namespace C

def l16 (c : UInt64) : UInt64 := let v130 := (if c < 65 then k0 else k1); let v131 := (if 90 < c then k0 else k1); let v132 := v130 * v131; let v133 := (if c < 97 then k0 else k1); let v134 := (if 122 < c then k0 else k1); let v135 := v133 * v134; let v136 := v132 ||| v135; let v137 := (if c == 95 then k1 else k0); let v138 := v136 ||| v137; let v139 := (if c < 48 then k0 else k1); let v140 := (if 57 < c then k0 else k1); let v141 := v139 * v140; let v142 := v138 ||| v141; if v142 == k1 then 1 else 0

def l0 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, p, g => p
  | n + 1, x, p, g => let v143 := (if p < len x then k1 else k0); let v144 := (if l16 (rd x p) == 1 then k1 else k0); let v145 := v143 * v144; let v146 := (if g == 0 then k0 else k1); let v147 := v145 * v146; if v147 == k1 then l0 n x (p + 1) (g - 1) else p

def l1 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, i, e, g => 1
  | n + 1, x, i, e, g => let v148 := (if i < e then k1 else k0); let v149 := (if g == 0 then k0 else k1); let v150 := v148 * v149; if v150 == k1 then let v151 := (if rd x i < 48 then k0 else k1); let v152 := (if 57 < rd x i then k0 else k1); let v153 := v151 * v152; if v153 == k1 then l1 n x (i + 1) e (g - 1) else 0 else 1

def l2 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, i, e, g => 1
  | n + 1, x, i, e, g =>
    let v154 := (if i < e then k1 else k0); let v155 := (if g == 0 then k0 else k1); let v156 := v154 * v155; if v156 == k1 then let v157 := (if rd x i < 48 then k0 else k1); let v158 := (if 57 < rd x i then k0 else k1); let v159 := v157 * v158; let v160 := (if rd x i == 95 then k1 else k0); let v161 := v159 ||| v160; if v161 == k1 then l2 n x (i + 1) e (g - 1) else 0 else 1

def l3 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, i, e, a, g => a
  | n + 1, x, i, e, a, g => let v162 := (if i < e then k1 else k0); let v163 := (if g == 0 then k0 else k1); let v164 := v162 * v163; if v164 == k1 then l3 n x (i + 1) e (a * 10 + (rd x i - 48)) (g - 1) else a

def l4 (x : List UInt8) (p e g : UInt64) : UInt64 := let v165 := (if p < e then k0 else k1); if v165 == k1 then 0
  else
    let c := rd x p;
    let r0 := let v166 := (if c < 97 then k0 else k1); let v167 := (if 122 < c then k0 else k1); let v168 := v166 * v167; let v169 := (if l2 (len' x) x (p + 1) e g == 1 then k1 else k0); let v170 := v168 * v169; if v170 == k1 then 16 else 0;
    let r1 := let v171 := (if e - p == 5 then k1 else k0); let v172 := (if c == 73 then k1 else k0); let v173 := v171 * v172; let v174 := (if rd x (p + 1) == 110 then k1 else k0); let v175 := v173 * v174; let v176 := (if rd x (p + 2) == 116 then k1 else k0); let v177 := v175 * v176; let v178 := (if rd x (p + 3) == 54 then k1 else k0); let v179 := v177 * v178; let v180 := (if rd x (p + 4) == 52 then k1 else k0); let v181 := v179 * v180; if v181 == k1 then 6 else r0;
    let r2 := let v182 := (if e - p == 6 then k1 else k0); let v183 := (if c == 85 then k1 else k0); let v184 := v182 * v183; let v185 := (if rd x (p + 1) == 73 then k1 else k0); let v186 := v184 * v185; let v187 := (if rd x (p + 2) == 110 then k1 else k0); let v188 := v186 * v187; let v189 := (if rd x (p + 3) == 116 then k1 else k0); let v190 := v188 * v189; let v191 := (if rd x (p + 4) == 54 then k1 else k0); let v192 := v190 * v191; let v193 := (if rd x (p + 5) == 52 then k1 else k0); let v194 := v192 * v193; if v194 == k1 then 5 else r1;
    let r3 := let v195 := (if e - p == 3 then k1 else k0); let v196 := (if c == 108 then k1 else k0); let v197 := v195 * v196; let v198 := (if rd x (p + 1) == 101 then k1 else k0); let v199 := v197 * v198; let v200 := (if rd x (p + 2) == 116 then k1 else k0); let v201 := v199 * v200; if v201 == k1 then 4 else r2;
    let r4 := let v202 := (if e - p == 3 then k1 else k0); let v203 := (if c == 100 then k1 else k0); let v204 := v202 * v203; let v205 := (if rd x (p + 1) == 101 then k1 else k0); let v206 := v204 * v205; let v207 := (if rd x (p + 2) == 102 then k1 else k0); let v208 := v206 * v207; if v208 == k1 then 3 else r3;
    let v209 := (if c < 48 then k0 else k1); let v210 := (if 57 < c then k0 else k1); let v211 := v209 * v210; if v211 == k1 then if l1 (len' x) x p e g == 1 then 7 else 0 else r4

def l5 (x : List UInt8) (p g : UInt64) : UInt64 := if p < len x then
    let c := rd x p;
    if c == 32 then 2
    else if c == 10 then
      if p + 1 < len x then
        let d := rd x (p + 1);
        let v212 := (if d == 32 then k1 else k0); let v213 := (if d == 10 then k1 else k0); let v214 := v212 ||| v213; if v214 == k1 then 2
        else let v215 := (if d == 100 then k1 else k0); let v216 := (if p + 3 < len x then k1 else k0); let v217 := v215 * v216; let v218 := (if rd x (p + 2) == 101 then k1 else k0); let v219 := v217 * v218; let v220 := (if rd x (p + 3) == 102 then k1 else k0); let v221 := v219 * v220; if v221 == k1 then
          let v222 := (if p + 4 < len x then k1 else k0); let v223 := (if l16 (rd x (p + 4)) == 1 then k1 else k0); let v224 := v222 * v223; if v224 == k1 then 0 else 2
        else 0
      else 1
    else if c == 40 then 8
    else if c == 41 then 9
    else if c == 43 then 12
    else if c == 45 then let v225 := (if p + 1 < len x then k1 else k0); let v226 := (if rd x (p + 1) == 45 then k1 else k0); let v227 := v225 * v226; if v227 == k1 then 0 else 13
    else if c == 42 then 14
    else if c == 59 then 15
    else if c == 58 then let v228 := (if p + 1 < len x then k1 else k0); let v229 := (if rd x (p + 1) == 61 then k1 else k0); let v230 := v228 * v229; if v230 == k1 then 11 else 10
    else if l16 c == 1 then l4 x p (l0 (len' x) x p g) g
    else 0
  else 1

def l6 (x : List UInt8) (p g : UInt64) : UInt64 := let c := rd x p;
  let v231 := (if c == 58 then k1 else k0); let v232 := (if p + 1 < len x then k1 else k0); let v233 := v231 * v232; let v234 := (if rd x (p + 1) == 61 then k1 else k0); let v235 := v233 * v234; if v235 == k1 then p + 2
  else if l16 c == 1 then l0 (len' x) x p g
  else p + 1

def l7 (k : UInt64) : UInt64 := if k == 5 then 1 else if k == 6 then 2 else 0

def l8 (t c : UInt64) : UInt64 := if c == 0 then t else if t == 0 then c else if t == c then c else 3

def l9 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, p, t, r => if p < len x then 4 else t
  | f + 1, x, p, t, r =>
    let g := r - 1;
    let k := l5 x p g;
    if k == 0 then 4
    else if k == 1 then t
    else l9 f x (l6 x p g) (l8 t (l7 k)) g

def l10 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → Buf → Buf
  | 0, x, i, e, g, o => q0 o 0
  | n + 1, x, i, e, g, o => let v236 := (if i < e then k1 else k0); let v237 := (if g == 0 then k0 else k1); let v238 := v236 * v237; if v238 == k1 then l10 n x (i + 1) e (g - 1) (q0 (q0 o 1) (rd x i)) else q0 o 0

def l11 (v : UInt64) (o : Buf) : Buf := q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o v) (v >>> 8)) (v >>> 16)) (v >>> 24)) (v >>> 32)) (v >>> 40)) (v >>> 48))
    (v >>> 56)

def l12 (x : List UInt8) (k p e g : UInt64) (o : Buf) : Buf := if k == 7 then l11 (l3 (len' x) x p e 0 g) (q0 o 5)
  else if k == 16 then l10 (len' x) x p e g (q0 o 14)
  else q0 o (k - 2)

def l13 : Nat → List UInt8 → UInt64 → UInt64 → Buf → Buf
  | 0, x, p, r, o => o
  | f + 1, x, p, r, o =>
    let g := r - 1;
    let k := l5 x p g;
    let v239 := (if k == 0 then k1 else k0); let v240 := (if k == 1 then k1 else k0); let v241 := v239 ||| v240; if v241 == k1 then o
    else if k == 2 then l13 f x (l6 x p g) g o
    else l13 f x (l6 x p g) g (l12 x k p (l6 x p g) g o)

def l14 : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, i => 1
  | n + 1, x, i =>
    if i + 1 < len x then
      let a := rd x i;
      let b := rd x (i + 1);
      let v242 := (if l16 a == 1 then k1 else k0); let v243 := (if a == 41 then k1 else k0); let v244 := v242 ||| v243; let v245 := (if b == 40 then k1 else k0); let v246 := v244 * v245; if v246 == k1 then 0
      else let v247 := (if a == 41 then k1 else k0); let v248 := (if l16 b == 1 then k1 else k0); let v249 := v247 * v248; if v249 == k1 then 0
      else l14 n x (i + 1)
    else 1

def l15 (x : List UInt8) : Buf := if l14 (len' x) x 0 == 1 then
    let t := l9 (len' x) x 0 0 (len x);
    let v250 := (if t == 1 then k1 else k0); let v251 := (if t == 2 then k1 else k0); let v252 := v250 ||| v251; if v252 == k1 then l13 (len' x) x 0 (len x) (q0 bnew t) else bnew
  else bnew

end C
