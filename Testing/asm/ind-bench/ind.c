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
