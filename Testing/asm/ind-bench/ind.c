/* C references for the `frontx_ind` benchmarks: the same work as the generated code, bytes in -> bytes out
   (decode the prefix encoding into nodes in the work block, run the function, encode / store the result). */
typedef unsigned long u64;
typedef struct N { u64 tag, x; struct N *l, *r; } N;
static N *hp;
static const unsigned char *in;
static u64 rd8(void) { u64 v = 0; for (int i = 7; i >= 0; i--) v = v << 8 | in[i]; in += 8; return v; }
/* Tree Unit: leaf = 0; node = 1, left, key (8 bytes), right */
static N *decT(void) { N *n = hp++; n->tag = *in++; n->l = n->r = 0;
  if (n->tag == 1) { n->l = decT(); n->x = rd8(); n->r = decT(); } return n; }
static unsigned char *out;
static void wr8(u64 v) { for (int i = 0; i < 8; i++) { *out++ = v; v >>= 8; } }
static void encT(N *n) { *out++ = n->tag; if (n->tag == 1) { encT(n->l); wr8(n->x); encT(n->r); } }
static int contains(N *t, u64 k) { while (t->tag == 1) { if (k < t->x) t = t->l; else if (t->x < k) t = t->r; else return 1; } return 0; }
static N *insert(N *t, u64 k) {  /* persistent: copies the path, like the Lean function */
  N *n = hp++;
  if (t->tag != 1) { n->tag = 1; n->x = k; n->l = hp++; n->r = hp++; n->l->tag = n->r->tag = 0; return n; }
  *n = *t;
  if (k < t->x) n->l = insert(t->l, k); else if (t->x < k) n->r = insert(t->r, k); else n->x = k;
  return n; }
/* List Nat: nil = 0; cons = 1, x, tail */
static N *decL(void) { N *n = hp++; n->tag = *in++; if (n->tag == 1) { n->x = rd8(); n->l = decL(); } return n; }
static void encL(N *n) { *out++ = n->tag; if (n->tag == 1) { wr8(n->x); encL(n->l); } }
static int elem(u64 a, N *l) { for (; l->tag == 1; l = l->l) if (a == l->x) return 1; return 0; }
static N *erase(N *l, u64 a) { if (l->tag != 1) return l; if (l->x == a) return l->l;
  N *n = hp++; *n = *l; n->l = erase(l->l, a); return n; }
u64 c_contains5(const unsigned char *i, u64 len, N *w, unsigned char *o) { in = i; hp = w; *o = contains(decT(), 5); return 0; }
u64 c_insert5(const unsigned char *i, u64 len, N *w, unsigned char *o) { in = i; hp = w; out = o; encT(insert(decT(), 5)); return out - o; }
u64 c_elem5(const unsigned char *i, u64 len, N *w, unsigned char *o) { in = i; hp = w; *o = elem(5, decL()); return 0; }
u64 c_erase5(const unsigned char *i, u64 len, N *w, unsigned char *o) { in = i; hp = w; out = o; encL(erase(decL(), 5)); return out - o; }
/* con-leche packed-data word functions (ScalarExamples.lean), the argument the 64-bit word at byte 0 */
static u64 w0(const unsigned char *i, u64 n) { u64 v = 0; for (int k = 7; k >= 0; k--) v = v << 8 | (k < n ? i[k] : 0); return v; }
u64 c_satpred(const unsigned char *i, u64 n, N *w, unsigned char *o) {
  u64 x = w0(i, n); u64 r = x == 32767 ? 32767 : x == 0 ? 0 : x - 1; for (int k = 0; k < 8; k++) o[k] = r >> 8 * k; return 0; }
u64 c_bvarofdata(const unsigned char *i, u64 n, N *w, unsigned char *o) {
  u64 r = w0(i, n) / 65536 % 32768; for (int k = 0; k < 8; k++) o[k] = r >> 8 * k; return 0; }
u64 c_packdata(const unsigned char *i, u64 n, N *w, unsigned char *o) {
  u64 h = n > 0 ? i[0] : 0, b = n > 1 ? i[1] : 0, f = n > 2 ? i[2] : 0; int lp = n > 3 && i[3] != 0;
  u64 r = h * 4294967296 + b * 65536 + f * 2 + (lp ? 1 : 0); for (int k = 0; k < 8; k++) o[k] = r >> 8 * k; return 0; }

/* section 21: programs of several functions */
static N *mk(u64 tag, u64 x, N *l, N *r) { N *n = hp++; n->tag = tag; n->x = x; n->l = l; n->r = r; return n; }
/* Pos: one = 0; succ = 1, child */
static N *decP(void) { N *n = hp++; n->tag = *in++; n->l = n->r = 0; if (n->tag == 1) n->l = decP(); return n; }
static void encP(N *n) { while (n->tag == 1) { *out++ = 1; n = n->l; } *out++ = 0; }
static N *plus(N *a, N *k) { return a->tag == 0 ? mk(1, 0, k, 0) : mk(1, 0, plus(a->l, k), 0); }
static N *mul(N *a, N *k) { return a->tag == 0 ? k : plus(mul(a->l, k), k); }
u64 c_posmul(const unsigned char *i, u64 len, N *w, unsigned char *o) {
  in = i; hp = w; out = o; N *a = decP(); N *k = decP(); encP(mul(a, k)); return out - o; }
/* List Nat: nil = 0; cons = 1, head (8 bytes), tail; `NonTail.reverse xs ++ [x]` (non-tail, persistent append) */
static N *app(N *a, N *b) { return a->tag != 1 ? b : mk(1, a->x, app(a->l, b), 0); }
static N *rev(N *l) { return l->tag != 1 ? mk(0, 0, 0, 0) : app(rev(l->l), mk(1, l->x, mk(0, 0, 0, 0), 0)); }
u64 c_reverse(const unsigned char *i, u64 len, N *w, unsigned char *o) {
  in = i; hp = w; out = o; encL(rev(decL())); return out - o; }
/* Level: zero 0, succ 1 (l), max 2 (l r), imax 3 (l r), param 4 (the name is not in the format) */
static N *decLv(void) { N *n = hp++; n->tag = *in++; n->l = n->r = 0;
  if (n->tag >= 1 && n->tag <= 3) n->l = decLv(); if (n->tag == 2 || n->tag == 3) n->r = decLv(); return n; }
static void encLv(N *n) { *out++ = n->tag; if (n->tag >= 1 && n->tag <= 3) encLv(n->l); if (n->tag == 2 || n->tag == 3) encLv(n->r); }
static N *combining(N *l, N *r) {
  if (l->tag == 0) return r; if (r->tag == 0) return l;
  if (l->tag == 1 && r->tag == 1) return mk(1, 0, combining(l->l, r->l), 0);
  return mk(2, 0, l, r); }
static N *simplify(N *l) {
  switch (l->tag) {
  case 0: return mk(0, 0, 0, 0);
  case 4: return mk(4, 0, 0, 0);
  case 1: return mk(1, 0, simplify(l->l), 0);
  case 2: return combining(simplify(l->l), simplify(l->r));
  default: { N *ls = simplify(l->l), *rs = simplify(l->r);
    if (ls->tag == 0 || (ls->tag == 1 && ls->l->tag == 0)) return rs;
    if (rs->tag == 0) return mk(0, 0, 0, 0);
    if (rs->tag == 1) return combining(ls, rs);
    return mk(3, 0, ls, rs); } } }
u64 c_simplify(const unsigned char *i, u64 len, N *w, unsigned char *o) {
  in = i; hp = w; out = o; encLv(simplify(decLv())); return out - o; }
