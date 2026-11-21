# Nano round 12 — parser implementation for Opus

> Relayed ADVICE from Astra (not owner decisions). Not yet run through nano's front end; the Sonnet box folds it in.

The code below replaces the parser driver and task machine from the supplied Par0.lean at 59cef70. Keep Base, k0/k1, the layout block, y5, y8, y10 and y14. Put the block inside namespace C. Remove the old y9/y11/y12/y13 driver. The new driver v97 pops exactly one task per unit of fuel. Use y13 for parser fragments and legacy single-def tests. Use y16 for a program whose last definition must be m : List UInt8 → List UInt8.

**Integration status.** I type-checked the implementation on Lean 4.35 and ran the tests below with hand-encoded tokens and an Array UInt64 implementation of the five buffer operations. The supplied text omits the Lex2 token enumeration and the declaration types from Base. The new terminal numbers and primitive signatures below are explicit integration assumptions. This has not run through S's ownership checker, frame limiter, or the real lexer. It is a parser implementation for integration, not a claim that the self-build passed.

## Wire up these adapters first

- Existing token numbers come from Par0. In the test vocabulary 40 comma, 41 product, 42 type arrow, 43 equation bar, 44 clause arrow, 45 Buf, 46 List UInt8, 47 Nat. Tokens 60 through 68 denote primitives 1 through 9. Change k40–k44, v94, v0 and the type-token advance in v128/v129 as applicable to Lex2. Specifically search for the successful type scan's “+ (k1)” if List UInt8 occupies several tokens. Consume the entire spelling. v95 is unused. With split tokens for clause arrows, adjust the corresponding consumes as well. The m test assumes an identifier contains a marker, ASCII 109 and a zero terminator after its tag.
- v90/v91/v92 implement primitive argument types, source arity, and result type. Test assumptions are ISIZE(bytes)→Nat, RD(bytes,word)→word, LEN(bytes)→word, PUT(bytes,word)→bytes, BNEW()→buf, BSIZE(buf)→word, BGET(buf,word)→word, BSET(buf,word,word)→buf, BPUSH(buf,word)→buf. Match Base's actual order, especially PUT. A one-token dedicated primitive is consumed by v93. If Lex2 emits an identifier record for a primitive, adapt the name resolution path and ARGATOM's nullary BNEW path to consume that whole record.
- Shape IDs 1/2/3/4 mean word/buf/bytes/Nat. The implementation assumes a slot for each base type. Interned shapes starting at 5 record both child shapes and the sum of their widths. Adjust v9 if the downstream ABI uses wider descriptors. Binary tuples can nest. Destructure a product with a let to project it. Dot projection syntax is omitted.
- The input contract is a well-formed Lex2 token buffer, including complete literal and identifier payloads. The parser performs type/shape checks for the constructs described here. Use the existing front end for additional subset restrictions such as affine usage. Pair-shape equality is stronger than a total-width check.
- Run the real front end first on v104 (the ATOM dispatcher), v99 (entry), and the grouped-parameter handler. Those have the greatest risk of exceeding local-slot limits. Test compound/nested let right-hand sides and whether your lexer requires an explicit semicolon after every let in layout syntax. Lean's acceptance alone does not check these rules.

## Heap and task effects

h[0] is running=1, accepted=2, rejected=0. h[3,4,5,7,8,9,11,12] are token cursor, live bindings, task depth, token length, operand depth, node count, next unused local slot, and current def ID respectively. h[21,22] are lookup results, h[25..27] hold current type, product count and signature-word count, h[29] temporarily saves the first destructuring binder, h[30] enables successor self-calls, h[31] carries a scalar result across a heap move, h[32] is the clause-parameter slot cursor.

d1 holds three words per task (code,a,b). d3 holds node IDs. d5 holds eight words per node (tag, payload1, payload2, shape, pending bit, first child, child count, next sibling). v5 consumes the last n operand IDs in source order, links their siblings, allocates the parent, and pushes its ID. Each syntactic occurrence gets its own record, including local reads. Sharing nodes would invalidate the sibling representation. d9 holds four words per binding (identifier token position, slot, shape, spare). d7 stores eight words per definition in its first 4096 words, signature entries in its next 4096 and interned shapes in the remainder. The supplied real layout has room for this partition. Recompute or check these splits when generating smaller layouts. The output grows after the token stream and an EOF sentinel. After each definition is serialized, its nodes can be reused.

In the table, task lists are in execution order. v1 pushes them in reverse. Unlisted code values reject. A failed handler clears h[0]; the runner tests status before dispatching again.

| Code | Heap/stack action |
|---|---|
| 1, 2, 3 | EXPR schedules ATOM then OPS. OPS stops at a looser operator. Otherwise it checks the left pending bit, schedules a strict right operand then reduction and another OPS. ATOM builds a leaf or schedules the appropriate form. |
| 4, 5, 49 | Require right parenthesis; reduce two scalar operands to BIN; for a shift consume a literal before reduction. |
| 6–9 | Consume comparator and parse strict RHS; consume then and schedule inherited branches; consume else; reduce four nodes to IF, propagating the union of branch bits. |
| 40, 42 | After the first parenthesized expression, close a group or parse the second field and right delimiter. Combine two strict children in PAIR, interning their product shape. |
| 41, 50–53 | Parse scalar or pair let binder. Pair tasks read two names and delimiters before parsing the value. Task 52 saves the first name after the value returns. Task 53 installs both component bindings at adjacent offsets. |
| 11, 12 | Install scalar binding after its strict value; finish LET using value and body, restore saved binding depth, propagate the body's bit. Slots are allocated monotonically across branches. |
| 43, 44, 55 | Parse one argument atom; repeat for exactly the callee's source arity; resolve a nullary atom. Parenthesized arguments admit compound expressions. |
| 45, 47, 48 | Determine actual operand count from saved base; check each argument's shape against its signature; replace argument nodes by CALL or PRIM. Nat fuel accepts a numeral or ISIZE. |
| 46, 54 | Resolve predecessor binder, then parse and validate all state arguments. A single state stays as-is. Multiple states are packed into one PAIR for CONTINUE. Mark the result pending. |
| 60–63 | At EOF finish, otherwise open a fresh DEF; parse atomic/grouped type; optionally parse product RHS; intern the product shape. |
| 66–68, 70 | Open parameter group or result type; collect names; install each shape and flattened slot; store result metadata and schedule body then FINISH. |
| 73–77, 79 | Distinguish nullary typed definition from Nat-fuel declaration; collect arrow-domain shapes; require zero equation; bind clause state names; after zero body bind successor predecessor and state names; combine zero and successor roots in LOOP. |
| 80–83 | FINISH checks one operand and the declared result shape, writes DEF header, schedules preorder walk; emit one node and payload; walk child/sibling sequence in order; emit ENDDEF and reopen declaration parsing. Only a successful whole-program return exposes the bytes. |

CONTINUE has its final wire tag in the private arena but stays provisional until FINISH. Grouping preserves its bit. A let body and either if branch propagate it. Strict tasks reject or disable it. The successor result shape is the function result even when the next-state shape differs. Task 47 has already checked each state argument against the corresponding formal. Task 79 consumes the pending step root when constructing LOOP. This is where a whole successor expression is committed. Trailing tokens still have to form another declaration or EOF.

## Implementation

```lean
def v85 : Nat → Buf → UInt64 → UInt64 → Buf
  | 0, h, a, b => bset h 0 0
  | n + 1, h, a, b =>
    let z := bget h 7;
    if a < z then
      if b < z then
        let x := bget h (d11+a);
        let y := bget h (d11+b);
        if x == y then
          if x == 0 then bset h 31 1 else
          if bget h (d11+a+1) == bget h (d11+b+1) then v85 n h (a+2) (b+2) else bset h 31 0
        else bset h 31 0
      else bset h 0 0
    else bset h 0 0

def v86 : Nat → Buf → UInt64 → Buf
  | 0, h, a => bset h 0 0
  | n + 1, h, a =>
    if a < bget h 7 then
      if bget h (d11+a) == 0 then bset h 3 (a+1) else v86 n h (a+2)
    else bset h 0 0

def v87 (h : Buf) (p : UInt64) : Buf :=
  let z9 := bget h (d11 + (p + 1)) ||| ((bget h (d11 + (p + 2))) <<< 8) ||| ((bget h (d11 + (p + 3))) <<< 16) ||| ((bget h (d11 + (p + 4))) <<< 24)
  ||| ((bget h (d11 + (p + 5))) <<< 32) ||| ((bget h (d11 + (p + 6))) <<< 40) ||| ((bget h (d11 + (p + 7))) <<< 48) ||| ((bget h (d11 + (p + 8))) <<< 56);
  bset h 31 z9

def v91 (p : UInt64) : UInt64 := if p == 5 then 0 else if p == 8 then 3 else if p == 2 then 2 else if p == 4 then 2 else if p == 7 then 2 else if p == 9 then 2 else 1
def v92 (p : UInt64) : UInt64 := if p == 1 then 4 else if p == 4 then 3 else if p == 5 then 2 else if p == 8 then 2 else if p == 9 then 2 else 1
def v90 (p j : UInt64) : UInt64 := if j == 0 then if p < 5 then 3 else 2 else 1
def v0 (h : Buf) (p : UInt64) : Buf :=
  let t := bget h (d11 + p);
  let z9 := if 59 < t then if t < 69 then t - 59 else 0 else 0;
  bset h 31 z9
def v94 (h : Buf) (p : UInt64) : Buf :=
  let t := bget h (d11 + p);
  let z9 := if t == 3 then 1 else if t == 45 then 2 else if t == 46 then 3 else if t == 47 then 4 else 0;
  bset h 31 z9
def v95 (h : Buf) (p : UInt64) : UInt64 := 1
def k40 : UInt64 := 40
def k41 : UInt64 := 41
def k42 : UInt64 := 42
def k43 : UInt64 := 43
def k44 : UInt64 := 44

-- Retain y0, y2, y7, y8, y10, y14, y15 and the generated layout constants.
-- k40..k49 and v0 are token/prelude adapters specified in the note.

def v1 (h : Buf) (c a b : UInt64) : Buf :=
  if (3 * (bget h 5) + 2) < d2 then
    let j := d1 + 3 * (bget h 5);
    let h := bset h (j) (c);
    let h := bset h (j + 1) (a);
    let h := bset h (j + 2) (b);
    let z40 := ((bget h 5) + 1);
    let h := bset h (5) z40;
    h
  else
    bset h 0 0

def v2 : Nat → Buf → UInt64 → UInt64 → UInt64 → Buf
  | 0, h, j, z, c => bset h 0 0
  | n + 1, h, j, z, c =>
    if c == 0 then h else
    let x := bget h (d3 + j);
    let y := bget h (d3 + j + 1);
    let h := bset h (d5 + 8*x + 7) y;
    v2 n h (j + 1) z (c - 1)

def v5 (h : Buf) (c a b w t n : UInt64) : Buf :=
  if 8 * (bget h 9) + 7 < d6 then
    if n < (bget h 8) + 1 then
      let j := (bget h 8) - n;
      if j < d4 then
        let x := bget h (d3 + j);
        let z := (bget h 9);
        let q := d5 + 8*z;
        let h := bset h (q) (c);
        let h := bset h (q + 1) (a);
        let h := bset h (q + 2) (b);
        let h := bset h (q + 3) (w);
        let h := bset h (q + 4) (t);
        let h := bset h (q + 5) (x);
        let h := bset h (q + 6) (n);
        let h := if n == 0 then h else v2 16777216 h j z (n - 1);
        let h := bset h (d3 + j) (z);
        let h := bset h (8) (j + 1);
        let h := bset h (9) (z + 1);
        h
      else
        bset h 0 0
    else
      bset h 0 0
  else
    bset h 0 0

def v6 (h : Buf) (x s w : UInt64) : Buf :=
  if 4 * (bget h 4) + 3 < d10 then
    let j := d9 + 4 * (bget h 4);
    let h := bset h (j) (x);
    let h := bset h (j + 1) (s);
    let h := bset h (j + 2) (w);
    let z40 := ((bget h 4) + 1);
    let h := bset h (4) z40;
    h
  else
    bset h 0 0

def v7 : Nat → Buf → UInt64 → UInt64 → Buf
  | 0, h, j, x => bset h 0 0
  | n + 1, h, j, x =>
    if j == 0 then bset h 21 0 else
    let s := bget h (d9 + 4*(j - 1));
    let h := v85 16777216 h (s + 1) (x + 1);
    let z40 := h;
    if bget h 31 == 1 then bset h 21 j else v7 n z40 (j - 1) x

def v8 : Nat → Buf → UInt64 → UInt64 → Buf
  | 0, h, j, x => bset h 0 0
  | n + 1, h, j, x =>
    if j == 0 then bset h 22 0 else
    let s := bget h (d7 + 8*(j - 1));
    let h := v85 16777216 h (s + 1) (x + 1);
    let z40 := h;
    if bget h 31 == 1 then bset h 22 j else v8 n z40 (j - 1) x

def v9 (h : Buf) (s : UInt64) : Buf :=
  let z9 := if s < 5 then 1 else bget h ((d7 + 8192) + 3*(s - 5) + 2);
  bset h 31 z9

def v10 : Nat → Buf → UInt64 → UInt64 → UInt64 → Buf
  | 0, h, x, y, j => bset h 0 0
  | n + 1, h, x, y, j =>
    let b := d7 + 8192 + 3*j;
    if j == bget h 26 then
      if 8192 + 3*j + 2 < d8 then
        let h := v9 h x;
        let z21 := bget h 31;
        let h := v9 h y;
        let z22 := bget h 31;
        let w := z21 + z22;
        bset (bset (bset (bset (bset h b x) (b + 1) y) (b + 2) w) 26 (j + 1)) 25 (j + 5)
      else bset h 0 0
    else if bget h b == x then
      let z40 := h;
      if bget h (b + 1) == y then bset h 25 (j + 5) else v10 n z40 x y (j + 1)
    else v10 n h x y (j + 1)

def v14 (h : Buf) (x j : UInt64) : Buf :=
  let z9 := if x < 512 then bget h ((d7 + 4096) + (bget h (d7 + 8 * (x) + 5)) + j) else v90 (x - 512) j;
  bset h 31 z9

def v15 (h : Buf) (a : UInt64) : Buf :=
  let z9 := if a < 512 then (bget h (d7 + 8 * (a) + 2)) else v91 (a - 512);
  bset h 31 z9

def v93 (h : Buf) (x b : UInt64) : Buf :=
  let h := v0 h x;
  let z21 := bget h 31;
  let j := z21;
  if j == 0 then
    bset h 0 0
  else
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let z40 := ((bget h 8));
    let h := v1 h 45 (512 + j) z40;
    let h := v1 h 44 (512 + j) (v91 j);
    h

def v100 (h : Buf) (a b : UInt64) : Buf :=
  let h := v1 h 2 (a) (0);
  let h := v1 h 3 (0) (b);
  h

def v101 (h : Buf) (a b : UInt64) : Buf :=
  let t := bget h (d11 + (bget h 3) + 0);
  let o := y8 t;
  let r := y10 t;
  if o == 0 then
    h
  else
    if r < a then
      h
    else
      if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 4)) == 0 then
        let z40 := ((bget h 3) + 1);
        let h := bset h (3) z40;
        if o == 6 then let h := v1 h 2 (a) (0);
          let h := v1 h 49 (o) (0);
          h else if o == 7 then let h := v1 h 2 (a) (0);
          let h := v1 h 49 (o) (0);
          h else let h := v1 h 2 (a) (0);
          let h := v1 h 5 (o) (0);
          let h := v1 h 1 (r + 1) (0);
          h
      else
        bset h 0 0

def v102 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 5 then
    let z40 := (bget h 3);
    let h := v87 h z40;
    let z21 := bget h 31;
    let v := z21;
    let z40 := ((bget h 3) + 9);
    let h := bset h (3) z40;
    let h := v5 h (1) (v) (0) (1) (0) (0);
    let h := v1 h 5 (a) (0);
    h
  else
    bset h 0 0

def v103 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3)) == 1 then
    if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 2))) + 3)) == 1 then
      v5 h (3) (a) (0) (1) (0) (2)
    else
      bset h 0 0
  else
    bset h 0 0

def v104 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 32 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let h := v1 h 6 (0) (b);
    let h := v1 h 1 (0) (0);
    h
  else
    if (bget h (d11 + (bget h 3) + 0)) == 2 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      let h := v1 h 41 (0) (b);
      h
    else
      if (bget h (d11 + (bget h 3) + 0)) == 5 then
        let z40 := (bget h 3);
        let h := v87 h z40;
        let z21 := bget h 31;
        let v := z21;
        let z40 := ((bget h 3) + 9);
        let h := bset h (3) z40;
        v5 h (1) (v) (0) (1) (0) (0)
      else
        if (bget h (d11 + (bget h 3) + 0)) == 6 then
          let z40 := ((bget h 3) + 1);
          let h := bset h (3) z40;
          let h := v1 h 40 (0) (0);
          let h := v1 h 1 (0) (b);
          h
        else
          if (bget h (d11 + (bget h 3) + 0)) == 14 then
            let x := (bget h 3);
            let z40 := (bget h 3);
            let h := v0 h z40;
            let z21 := bget h 31;
            let u := (z21);
            let z40 := (bget h 4);
            let h := v7 16777216 h z40 x;
            let z40 := ((bget h 12) + 1);
            let h := v8 16777216 h z40 x;
            let z40 := ((bget h 3) + 1);
            let h := v86 16777216 h z40;
            if (bget h 21) == 0 then
              if (bget h 22) == 0 then
                if u == 0 then
                  bset h 0 0
                else
                  let z40 := ((bget h 8));
                  let h := v1 h 45 (512 + u) z40;
                  let h := v1 h 44 (512 + u) (v91 u);
                  h
              else
                let j := (bget h 22) - 1;
                if j == (bget h 12) then
                  if b == 1 then
                    if (bget h 30) == 1 then
                      let h := v1 h 46 (0) (0);
                      h
                    else
                      bset h 0 0
                  else
                    bset h 0 0
                else
                  let z40 := ((bget h 8));
                  let h := v1 h 45 (j) z40;
                  let z40 := ((bget h (d7 + 8 * (j) + 2)));
                  let h := v1 h 44 (j) z40;
                  h
            else
              let j := d9 + 4*((bget h 21) - 1);
              let s := bget h (j + 1);
              let w := bget h (j + 2);
              if w == 4 then
                bset h 0 0
              else
                let h := v9 h (w);
                let z21 := bget h 31;
                v5 h (2) (s) ((z21)) (w) (0) (0)
          else
            let z40 := (bget h 3);
            v93 h z40 b

def v105 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 7 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    h
  else
    if (bget h (d11 + (bget h 3) + 0)) == k40 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      let h := v1 h 42 (0) (0);
      let h := v1 h 4 (0) (0);
      let h := v1 h 1 (0) (0);
      h
    else
      bset h 0 0

def v106 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 7 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    h
  else
    bset h 0 0

def v107 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 2))) + 4)) == 0 then
    if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 4)) == 0 then
      let z40 := (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 2))) + 3));
      let z41 := (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3));
      let h := v10 16777216 h z40 z41 0;
      let z40 := ((bget h 25));
      v5 h (6) (2) (0) z40 (0) (2)
    else
      bset h 0 0
  else
    bset h 0 0

def v108 (h : Buf) (a b : UInt64) : Buf :=
  let t := bget h (d11 + (bget h 3) + 0);
  let c := if t == 23 then k1 else if t == 20 then 2 else k0;
  if c == 0 then
    bset h 0 0
  else
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let h := v1 h 7 (c) (b);
    let h := v1 h 1 (0) (0);
    h

def v109 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 33 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let h := v1 h 9 (a) (0);
    let h := v1 h 1 (0) (b);
    let h := v1 h 8 (0) (0);
    let h := v1 h 1 (0) (b);
    h
  else
    bset h 0 0

def v110 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 34 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    h
  else
    bset h 0 0

def v111 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 4))) + 3)) == 1 then
    if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 3))) + 3)) == 1 then
      if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 2))) + 3)) == (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3)) then
        let w := (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3));
        let t := (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 2))) + 4)) ||| (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 4));
        v5 h (4) (a) (0) (w) (t) (4)
      else
        bset h 0 0
    else
      bset h 0 0
  else
    bset h 0 0

def v112 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 14 then
    let x := (bget h 3);
    let z40 := ((bget h 3) + 1);
    let h := v86 16777216 h z40;
    if (bget h (d11 + (bget h 3) + 0)) == 9 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      let h := v1 h 11 (x) (b);
      let h := v1 h 1 (0) (0);
      h
    else
      bset h 0 0
  else
    if (bget h (d11 + (bget h 3) + 0)) == 6 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      let h := v1 h 50 (0) (b);
      h
    else
      bset h 0 0

def v113 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 14 then
    let x := (bget h 3);
    let z40 := ((bget h 3) + 1);
    let h := v86 16777216 h z40;
    if (bget h (d11 + (bget h 3) + 0)) == k40 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      let h := v1 h 51 (x) (b);
      h
    else
      bset h 0 0
  else
    bset h 0 0

def v114 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 14 then
    let y := (bget h 3);
    let z40 := ((bget h 3) + 1);
    let h := v86 16777216 h z40;
    if (bget h (d11 + (bget h 3) + 0)) == 7 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      if (bget h (d11 + (bget h 3) + 0)) == 9 then
        let z40 := ((bget h 3) + 1);
        let h := bset h (3) z40;
        let h := v1 h 53 (y) (b);
        let h := v1 h 52 (a) (b);
        let h := v1 h 1 (0) (0);
        h
      else
        bset h 0 0
    else
      bset h 0 0
  else
    bset h 0 0

def v115 (h : Buf) (a b : UInt64) : Buf :=
  let h := bset h (29) (a);
  h

def v116 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 13 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let s := (bget h 11);
    let w := (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3));
    let j := (bget h 4);
    let h := v1 h 12 (s) (j);
    let h := v1 h 1 (0) (b);
    let h := v9 h (w);
    let z21 := bget h 31;
    let h := bset h (11) (s + (z21));
    v6 h a s w
  else
    bset h 0 0

def v117 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 13 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let s := (bget h 11);
    let w := (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3));
    let j := (bget h 4);
    let h := v1 h 12 (s) (j);
    let h := v1 h 1 (0) (b);
    let h := v9 h (w);
    let z21 := bget h 31;
    let h := bset h (11) (s + (z21));
    if 4 < w then
      let x := (bget h 29);
      let l := (bget h ((d7 + 8192) + 3*(w - 5)));
      let r := (bget h ((d7 + 8192) + 3*(w - 5) + 1));
      let h := v9 h (l);
      let z21 := bget h 31;
      let z := s + (z21);
      let h := v6 h x s l;
      v6 h a z r
    else
      bset h 0 0
  else
    bset h 0 0

def v118 (h : Buf) (a b : UInt64) : Buf :=
  let w := (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3));
  let t := (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 4));
  let z40 := ((bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 2))) + 3)));
  let h := v9 h z40;
  let z21 := bget h 31;
  let z := (z21);
  let h := bset h (4) (b);
  v5 h (5) (a) (z) (w) (t) (2)

def v119 (h : Buf) (a b : UInt64) : Buf :=
  if b == 0 then
    h
  else
    let h := v1 h 44 (a) (b - 1);
    let h := v1 h 43 (0) (0);
    h

def v120 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 6 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let h := v1 h 40 (0) (0);
    let h := v1 h 1 (0) (0);
    h
  else
    if (bget h (d11 + (bget h 3) + 0)) == 5 then
      let h := v1 h 3 (0) (0);
      h
    else
      if (bget h (d11 + (bget h 3) + 0)) == 14 then
        let z40 := (bget h 4);
        let z41 := (bget h 3);
        let h := v7 16777216 h z40 z41;
        if (bget h 21) == 0 then
          let h := v1 h 55 (0) (0);
          h
        else
          let z40 := ((bget h 3) + 1);
          let h := v86 16777216 h z40;
          let j := d9 + 4*((bget h 21) - 1);
          let s := bget h (j + 1);
          let w := bget h (j + 2);
          if w == 4 then
            bset h 0 0
          else
            let h := v9 h (w);
            let z21 := bget h 31;
            v5 h (2) (s) ((z21)) (w) (0) (0)
      else
        let h := v1 h 55 (0) (0);
        h

def v121 (h : Buf) (a b : UInt64) : Buf :=
  let n := (bget h 8) - b;
  let h := v1 h 48 (a) (n);
  let h := v1 h 47 (a) (n);
  h

def v122 (h : Buf) (a b : UInt64) : Buf :=
  if b == 0 then
    h
  else
    let j := (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - b))) + 3));
    let h := v15 h a;
    let z21 := bget h 31;
    let z := (z21) - b;
    let h := v14 h (a) (z);
    let z21 := bget h 31;
    let w := (z21);
    if j == w then
      let h := v1 h 47 (a) (b - 1);
      h
    else
      if w == 4 then
        if bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - b))) + 0) == 1 then
          let h := v1 h 47 (a) (b - 1);
          h
        else
          if bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - b))) + 0) == 9 then
            if bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - b))) + 1) == 1 then
              let h := v1 h 47 (a) (b - 1);
              h
            else
              bset h 0 0
          else
            bset h 0 0
      else
        bset h 0 0

def v123 (h : Buf) (a b : UInt64) : Buf :=
  if a < 512 then
    let z40 := ((bget h (d7 + 8 * (a) + 3)));
    v5 h (8) (a) (b) z40 (0) (b)
  else
    v5 h (9) (a - 512) (0) (v92 (a - 512)) (0) (b)

def v124 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 14 then
    let z40 := (bget h 4);
    let z41 := (bget h 3);
    let h := v7 16777216 h z40 z41;
    if (bget h 21) == 0 then
      bset h 0 0
    else
      if bget h (d9 + 4*((bget h 21) - 1) + 2) == 4 then
        let z40 := ((bget h 3) + 1);
        let h := v86 16777216 h z40;
        let f := bget h 12;
        let j := bget h (d7+8*f+2) - 1;
        let h := v1 h 54 f j;
        let h := v1 h 47 f j;
        let h := v1 h 44 f j;
        h
      else
        bset h 0 0
  else
    bset h 0 0

def v125 (h : Buf) (a b : UInt64) : Buf :=
  let w := bget h (d7+8*a+3);
  let h := if b == 1 then h else v5 h 6 b 0 0 0 b;
  v5 h 11 0 0 w 1 1

def v126 (h : Buf) (a b : UInt64) : Buf :=
  let p := bget h 3;
  let t := bget h (d11+p);
  if t == 14 then
    let f := bget h 12;
    let h := v8 16777216 h f p;
    let j := bget h 22;
    if j == 0 then bset h 0 0 else
    if bget h (d7+8*(j-1)+2) == 0 then
      let w := bget h (d7+8*(j-1)+3);
      let h := v86 16777216 h (p+1);
      v5 h 8 (j-1) 0 w 0 0
    else bset h 0 0
  else
    let h := v0 h p;
    if bget h 31 == 5 then
      let h := bset h 3 (p+1);
      v5 h 9 5 0 2 0 0
    else bset h 0 0

def v127 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h 3) == (bget h 7) then
    let h := bset h (0) (2);
    h
  else
    if (bget h (d11 + (bget h 3) + 0)) == 1 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      if (bget h (d11 + (bget h 3) + 0)) == 14 then
        let x := (bget h 3);
        let z40 := (bget h 12);
        let h := v8 16777216 h z40 x;
        if (bget h 22) == 0 then
          if (bget h 12) < 512 then
            let z40 := ((bget h 3) + 1);
            let h := v86 16777216 h z40;
            let z40 := (d7 + 8 * ((bget h 12)) + 0);
            let h := bset h z40 (x);
            let z40 := (d7 + 8 * ((bget h 12)) + 5);
            let z41 := ((bget h 27));
            let h := bset h z40 z41;
            let z40 := (d7 + 8 * ((bget h 12)) + 2);
            let h := bset h z40 (0);
            let h := bset h (4) (0);
            let h := bset h (8) (0);
            let h := bset h (9) (0);
            let h := bset h (11) (0);
            let h := bset h (30) (0);
            if (bget h (d11 + (bget h 3) + 0)) == 8 then
              let z40 := ((bget h 3) + 1);
              let h := bset h (3) z40;
              let h := v1 h 73 (0) (0);
              let h := v1 h 61 (0) (0);
              h
            else
              let h := v1 h 66 (0) (0);
              h
          else
            bset h 0 0
        else
          bset h 0 0
      else
        bset h 0 0
    else
      bset h 0 0

def v128 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 6 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let h := v1 h 62 (0) (0);
    let h := v1 h 4 (0) (0);
    let h := v1 h 61 (0) (0);
    h
  else
    let z40 := (bget h 3);
    let h := v94 h z40;
    let z21 := bget h 31;
    let w := z21;
    if w == 0 then
      bset h 0 0
    else
      let z40 := ((bget h 3) + (k1));
      let h := bset h (3) z40;
      let h := bset h (25) (w);
      let h := v1 h 62 (0) (0);
      h

def v129 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == k41 then
    let x := (bget h 25);
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let h := v1 h 63 (x) (0);
    let h := v1 h 61 (0) (0);
    h
  else
    h

def v130 (h : Buf) (a b : UInt64) : Buf :=
  let z40 := (bget h 25);
  v10 16777216 h a z40 0

def v131 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 6 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let z40 := ((bget h 4));
    let h := v1 h 67 z40 (0);
    h
  else
    if (bget h (d11 + (bget h 3) + 0)) == 8 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      let h := v1 h 70 (0) (0);
      let h := v1 h 61 (0) (0);
      h
    else
      bset h 0 0

def v132 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 14 then
    let x := (bget h 3);
    let z40 := ((bget h 3) + 1);
    let h := v86 16777216 h z40;
    let h := v6 h x 0 0;
    let h := v1 h 67 (a) (0);
    h
  else
    if (bget h (d11 + (bget h 3) + 0)) == 8 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      if a < (bget h 4) then
        let h := v1 h 66 (0) (0);
        let h := v1 h 68 (a) (0);
        let h := v1 h 4 (0) (0);
        let h := v1 h 61 (0) (0);
        h
      else
        bset h 0 0
    else
      bset h 0 0

def v133 (h : Buf) (a b : UInt64) : Buf :=
  if a == (bget h 4) then
    h
  else
    let w := (bget h 25);
    let z40 := ((bget h 11));
    let h := bset h (d9 + 4*a + 1) z40;
    let h := bset h (d9 + 4*a + 2) (w);
    let h := v9 h (w);
    let z21 := bget h 31;
    let z40 := ((bget h 11) + (z21));
    let h := bset h (11) z40;
    let h :=
    let j := (bget h 27);
        if j < 4096 then
          let h := bset h ((d7 + 4096) + j) (w);
          let h := bset h (27) (j + 1);
          let z40 := (d7 + 8 * ((bget h 12)) + 2);
          let z41 := ((bget h (d7 + 8 * ((bget h 12)) + 2)) + 1);
          let h := bset h z40 z41;
          h
        else
          bset h 0 0;
    let h := v1 h 68 (a + 1) (0);
    h

def v134 (h : Buf) (a b : UInt64) : Buf :=
  let z40 := (d7 + 8 * ((bget h 12)) + 1);
  let z41 := ((bget h 11));
  let h := bset h z40 z41;
  let z40 := (d7 + 8 * ((bget h 12)) + 3);
  let z41 := ((bget h 25));
  let h := bset h z40 z41;
  let z40 := (d7 + 8 * ((bget h 12)) + 4);
  let h := bset h z40 (0);
  if (bget h (d11 + (bget h 3) + 0)) == 9 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    let h := v1 h 80 (0) (0);
    let h := v1 h 1 (0) (0);
    h
  else
    bset h 0 0

def v200 (h : Buf) (w : UInt64) : Buf :=
  let f := d7 + 8 * bget h 12;
  let j := bget h 27;
  let a := bget h (f+2);
  if j < 4096 then
    let h := bset h (d7+4096+j) w;
    let h := bset h 27 (j+1);
    bset h (f+2) (a+1)
  else bset h 0 0

def v135 (h : Buf) (a b : UInt64) : Buf :=
  let p := bget h 3;
  let f := d7 + 8 * bget h 12;
  let w := bget h 25;
  if bget h (d11+p) == 9 then v134 h 0 0 else
  if w == 4 then
    if bget h (d11+p) == k42 then
      let h := bset h 3 (p+1);
      let h := bset h (f+1) 1;
      let h := bset h (f+4) 1;
      let h := v200 h 4;
      let h := v1 h 74 0 0;
      v1 h 61 0 0
    else bset h 0 0
  else bset h 0 0

def v136 (h : Buf) (a b : UInt64) : Buf :=
  let p := bget h 3;
  let f := d7 + 8 * bget h 12;
  let w := bget h 25;
  if bget h (d11+p) == k42 then
    let q := bget h (f+1);
    let h := v9 h w;
    let z := bget h 31;
    let h := bset h (f+1) (q+z);
    let h := v200 h w;
    let h := bset h 3 (p+1);
    let h := v1 h 74 0 0;
    v1 h 61 0 0
  else if bget h (f+2) == 1 then bset h 0 0 else v1 h 75 0 0

def v137 (h : Buf) (a b : UInt64) : Buf :=
  let z40 := (d7 + 8 * ((bget h 12)) + 3);
  let z41 := ((bget h 25));
  let h := bset h z40 z41;
  let z40 := ((bget h (d7 + 8 * ((bget h 12)) + 1)));
  let h := bset h (11) z40;
  if (bget h (d11 + (bget h 3) + 0)) == k43 then
    let z40 := ((bget h 3) + 1);
    let h := bset h (3) z40;
    if (bget h (d11 + (bget h 3) + 0)) == 5 then
      let z40 := (bget h 3);
      let h := v87 h z40;
      let z21 := bget h 31;
      if z21 == 0 then
        let z40 := ((bget h 3) + 9);
        let h := bset h (3) z40;
        if (bget h (d11 + (bget h 3) + 0)) == k40 then
          let z40 := ((bget h 3) + 1);
          let h := bset h (3) z40;
          let h := bset h 32 1;
            let h := v1 h 76 (0) (1);
          h
        else
          bset h 0 0
      else
        bset h 0 0
    else
      bset h 0 0
  else
    bset h 0 0

def v138 (h : Buf) (a b : UInt64) : Buf :=
  let p := bget h 3;
  let f := d7 + 8 * bget h 12;
  let j := bget h (f+5);
  let z := bget h (f+2);
  let w := bget h (d7+4096+j+b);
  let s := bget h 32;
  if bget h (d11+p) == 14 then
    let h := v86 16777216 h (p+1);
    let h := v6 h p s w;
    let h := v9 h w;
    let q := bget h 31;
    let h := bset h 32 (s+q);
    let x := bget h 3;
    let t := bget h (d11+x);
    let h := bset h 3 (x+1);
    if b+1 < z then
      if t == k40 then v1 h 76 a (b+1) else bset h 0 0
    else if t == k44 then
      if a == 0 then
        let h := v1 h 77 0 0;
        v1 h 1 0 0
      else
        let h := v1 h 80 0 0;
        let h := v1 h 79 0 0;
        v1 h 1 0 1
    else bset h 0 0
  else bset h 0 0

def v139 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3)) == (bget h (d7 + 8 * ((bget h 12)) + 3)) then
    if (bget h (d11 + (bget h 3) + 0)) == k43 then
      let z40 := ((bget h 3) + 1);
      let h := bset h (3) z40;
      if (bget h (d11 + (bget h 3) + 0)) == 14 then
        let x := (bget h 3);
        let z40 := ((bget h 3) + 1);
        let h := v86 16777216 h z40;
        let h := bset h (4) (0);
        let h := v6 h x 0 4;
        if (bget h (d11 + (bget h 3) + 0)) == 10 then
          let z40 := ((bget h 3) + 1);
          let h := bset h (3) z40;
          if (bget h (d11 + (bget h 3) + 0)) == 5 then
            let z40 := (bget h 3);
            let h := v87 h z40;
            let z21 := bget h 31;
            if z21 == 1 then
              let z40 := ((bget h 3) + 9);
              let h := bset h (3) z40;
              let h := bset h (30) (1);
              if (bget h (d11 + (bget h 3) + 0)) == k40 then
                let z40 := ((bget h 3) + 1);
                let h := bset h (3) z40;
                let h := bset h 32 1;
                let h := v1 h 76 (1) (1);
                h
              else
                bset h 0 0
            else
              bset h 0 0
          else
            bset h 0 0
        else
          bset h 0 0
      else
        bset h 0 0
    else
      bset h 0 0
  else
    bset h 0 0

def v140 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3)) == (bget h (d7 + 8 * ((bget h 12)) + 3)) then
    let z40 := ((bget h (d7 + 8 * ((bget h 12)) + 3)));
    v5 h (10) (0) (0) z40 (0) (2)
  else
    bset h 0 0

def v141 (h : Buf) (a b : UInt64) : Buf :=
  if (bget h 8) == 1 then
    if (bget h ((d5 + 8 * (bget h (d3 + (bget h 8) - 1))) + 3)) == (bget h (d7 + 8 * ((bget h 12)) + 3)) then
      let z := (bget h (d3 + (bget h 8) - 1));
      let q := (bget h (d7 + 8 * ((bget h 12)) + 1));
      let w := (bget h 11);
      let t := (bget h (d7 + 8 * ((bget h 12)) + 4));
      let z40 := ((bget h (d7 + 8 * ((bget h 12)) + 3)));
      let h := v9 h z40;
      let z21 := bget h 31;
      let r := (z21);
      let h := bpush h (20);
      let z40 := ((bget h 12));
      let h := bpush h z40;
      let h := bpush h (q);
      let h := bpush h (w);
      let h := bpush h (t);
      let h := bpush h (r);
      let h := v1 h 83 (0) (0);
      let h := v1 h 81 (z) (0);
      h
    else
      bset h 0 0
  else
    bset h 0 0

def v142 (h : Buf) (a b : UInt64) : Buf :=
  let t := (bget h ((d5 + 8*a) + 0));
  let x := (bget h ((d5 + 8*a) + 1));
  let y := (bget h ((d5 + 8*a) + 2));
  let z := (bget h ((d5 + 8*a) + 5));
  let n := (bget h ((d5 + 8*a) + 6));
  let h := bpush h (t);
  let z40 := h;
  let h := if t < 10 then bpush h x else z40;
  let h := if t == 2 then bpush h y else if t == 5 then bpush h y else if t == 8 then bpush h y else h;
  let h := v1 h 82 (z) (n);
  h

def v143 (h : Buf) (a b : UInt64) : Buf :=
  if b == 0 then
    h
  else
    let x := (bget h ((d5 + 8*a) + 7));
    let h := v1 h 82 (x) (b - 1);
    let h := v1 h 81 (a) (0);
    h

def v144 (h : Buf) (a b : UInt64) : Buf :=
  let h := bpush h (21);
  let z40 := ((bget h 12) + 1);
  let h := bset h (12) z40;
  let h := v1 h 60 (0) (0);
  h

def v96 (h : Buf) (c a b : UInt64) : Buf :=
  if c == 1 then v100 h a b else 
    if c == 2 then v101 h a b else 
    if c == 49 then v102 h a b else 
    if c == 5 then v103 h a b else 
    if c == 3 then v104 h a b else 
    if c == 40 then v105 h a b else 
    if c == 4 then v106 h a b else 
    if c == 42 then v107 h a b else 
    if c == 6 then v108 h a b else 
    if c == 7 then v109 h a b else 
    if c == 8 then v110 h a b else 
    if c == 9 then v111 h a b else 
    if c == 41 then v112 h a b else 
    if c == 50 then v113 h a b else 
    if c == 51 then v114 h a b else 
    if c == 52 then v115 h a b else 
    if c == 11 then v116 h a b else 
    if c == 53 then v117 h a b else 
    if c == 12 then v118 h a b else 
    if c == 44 then v119 h a b else 
    if c == 43 then v120 h a b else 
    if c == 45 then v121 h a b else 
    if c == 47 then v122 h a b else 
    if c == 48 then v123 h a b else 
    if c == 46 then v124 h a b else 
    if c == 54 then v125 h a b else 
    if c == 55 then v126 h a b else 
    if c == 60 then v127 h a b else 
    if c == 61 then v128 h a b else 
    if c == 62 then v129 h a b else 
    if c == 63 then v130 h a b else 
    if c == 66 then v131 h a b else 
    if c == 67 then v132 h a b else 
    if c == 68 then v133 h a b else 
    if c == 70 then v134 h a b else 
    if c == 73 then v135 h a b else 
    if c == 74 then v136 h a b else 
    if c == 75 then v137 h a b else 
    if c == 76 then v138 h a b else 
    if c == 77 then v139 h a b else 
    if c == 79 then v140 h a b else 
    if c == 80 then v141 h a b else 
    if c == 81 then v142 h a b else 
    if c == 82 then v143 h a b else 
    let z40 := h;
    if c == 83 then v144 h a b else bset z40 0 0

def v97 : Nat → Buf → Buf
  | 0, h => bset h 0 0
  | n + 1, h =>
    if bget h 0 == 1 then
      let g := bget h 5;
      if g == 0 then bset h 0 0 else
      let j := d1 + 3*(g - 1);
      let c := bget h j;
      let a := bget h (j + 1);
      let b := bget h (j + 2);
      let h := bset h 5 (g - 1);
      v97 n (v96 h c a b)
    else h

def v98 : Nat → Buf → UInt64 → Buf → Buf
  | 0, h, j, o => bnew
  | n + 1, h, j, o =>
    if j < bsize h then
      let v := bget h j;
      v98 n h (j + 1) (bpush o v)
    else o

def v99 (x : Buf) (b : UInt64) : Buf :=
  let c := bsize x;
  let h := y14 16777216 x 0 (y15 bnew);
  if bsize h == d11 + c then
    let h := bset h (7) (c);
    let h := bset h (0) (1);
    let h := bpush h 0;
    let h := bpush h (2);
    let h := v97 16777216 (v1 h 60 0 0);
    if (bget h 0) == 2 then
      if 0 < (bget h 12) then
        if b == 0 then v98 16777216 h (d11 + c + 1) bnew else
          let j := d7 + 8*((bget h 12)-1);
          let x := bget h j;
          let u := bget h (j+5);
          if bget h (d11+x+2) == 109 then
            if bget h (d11+x+3) == 0 then
              if bget h (j+2) == 1 then
                if bget h (d7+4096+u) == 3 then
                  if bget h (j+3) == 3 then v98 16777216 h (d11+c+1) bnew else bnew
                else bnew
              else bnew
            else bnew
          else bnew
      else
        bnew
    else
      bnew
  else
    bnew

def y13 (x : Buf) : Buf := v99 x 0

def y16 (x : Buf) : Buf := v99 x 1
```

## Regression programs

These are source spellings of the hand-tokenized tests. ACCEPT/REJECT refers to fragment entry y13 except that the main identity also passed y16. Each row stands alone.

| Part | Definition or body | Expected |
|---|---|---|
| Pair | `def f (x : UInt64) : UInt64 × UInt64 := (x,x)` | accept |
| Pair | `def f (x : UInt64 × UInt64) : UInt64 := let (a,b) := x; b` | accept, second component is the next slot |
| Pair | `def f (x : UInt64) : UInt64 := let (a,b) := x; a` | reject |
| Pair | `def f (x : UInt64) : UInt64 := (x,x)` | reject |
| Call | `def f (x : List UInt8) : List UInt8 := x` followed by `def m (x : List UInt8) : List UInt8 := f x` | accept |
| Main | `def m (x : List UInt8) : List UInt8 := x` | accept |
| Call | Change the preceding helper f to word → word while retaining the bytes main | reject |
| Primitive | `def f (x : Buf) : UInt64 := bsize (bpush x 1)` | accept |
| Loop | Under `def f : Nat → UInt64 → UInt64`, use `\| 0,s => s` then `\| n+1,s => f n s` | accept |
| Loop | Successor body `let x := s; f n x` | accept |
| Loop | Successor body `f n s + 1` | reject |
| Loop | Successor body `(if s == s then f n s else s) + 1` | reject |
| Loop | Successor body `f s s` | reject |

Also exercised the multi-state case `def f : Nat → UInt64 → UInt64 → UInt64 | 0,a,b => a | n+1,a,b => f n b a`. The step subtree was exactly `11 6 2 2 2 1 2 1 1` (continue, pair of two children, local slot 2 width 1, local slot 1 width 1). Codegen must evaluate both children before overwriting either state slot.

For integration, compare these token-level successes against real Lex2 first. Then compare complete AST words with the typed reference on the same valid programs, and run the actual S front end on the replacement file. Those three checks address different boundaries.
