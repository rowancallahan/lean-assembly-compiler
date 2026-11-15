/* Hand-written C (gcc -O2, rv64i freestanding) of the frontx_ind examples on linked structures.
   core_*: the function alone on an already built structure; e2e_*: decode the same byte format `ours` takes, run, encode the result. */
typedef unsigned long u64; typedef unsigned char u8;
extern char heap[]; static char *hp;
void reset(void) { hp = heap; }
static void *al(u64 n) { void *r = hp; hp += n; return r; }
static u64 ld8(const u8 **p) { u64 v = 0; for (int i = 0; i < 8; i++) v |= (u64)(*p)[i] << (8 * i); *p += 8; return v; }
static void st8(u8 **o, u64 v) { for (int i = 0; i < 8; i++) (*o)[i] = v >> (8 * i); *o += 8; }
/* BinTree Nat: 0 | 1 l x r */
typedef struct T { struct T *l, *r; u64 x; } T;
static T *dt(const u8 **p) { if (!*(*p)++) return 0; T *t = al(sizeof(T)); t->l = dt(p); t->x = ld8(p); t->r = dt(p); return t; }
static void et(T *t, u8 **o) { if (!t) { *(*o)++ = 0; return; } *(*o)++ = 1; et(t->l, o); st8(o, t->x); et(t->r, o); }
static T *mk(T *l, u64 x, T *r) { T *t = al(sizeof(T)); t->l = l; t->x = x; t->r = r; return t; }
static u64 count(T *t) { return t ? 1 + count(t->l) + count(t->r) : 0; }
static T *mirror(T *t) { return t ? mk(mirror(t->r), t->x, mirror(t->l)) : 0; }
/* List Nat: 0 | 1 x tl */
typedef struct L { struct L *tl; u64 x; } L;
static L *dl(const u8 **p) { if (!*(*p)++) return 0; L *c = al(sizeof(L)); c->x = ld8(p); c->tl = dl(p); return c; }
static void el(L *l, u8 **o) { for (; l; l = l->tl) { *(*o)++ = 1; st8(o, l->x); } *(*o)++ = 0; }
static L *cons(u64 x, L *t) { L *c = al(sizeof(L)); c->x = x; c->tl = t; return c; }
static u64 nsum(L *l) { return l ? l->x + nsum(l->tl) : 0; }
static L *rev(L *xs) { L *a = 0; for (; xs; xs = xs->tl) a = cons(xs->x, a); return a; }
static L *app(L *xs, L *ys) { return xs ? cons(xs->x, app(xs->tl, ys)) : ys; }
/* Level (names dropped): 0 zero | 1 succ u | 2 max u v | 3 imax u v | 4 param */
typedef struct V { int tag; struct V *l, *r; } V;
static V *dv(const u8 **p) { V *v = al(sizeof(V)); v->tag = *(*p)++; v->l = v->r = 0;
  if (v->tag >= 1 && v->tag <= 3) v->l = dv(p); if (v->tag == 2 || v->tag == 3) v->r = dv(p); return v; }
static int hasp(V *v) { switch (v->tag) { case 0: return 0; case 4: return 1; case 1: return hasp(v->l); default: return hasp(v->l) || hasp(v->r); } }
/* entries: core_X(root, root2) -> word; e2e_X(in, n, out) */
void *build_count(const u8 *in) { return dt(&in); } void *build_mirror(const u8 *in) { return dt(&in); }
void *build_nontail(const u8 *in) { return dl(&in); } void *build_reverse(const u8 *in) { return dl(&in); }
void *build_hasparam(const u8 *in) { return dv(&in); }
void *build_append(const u8 *in) { return dl(&in); }  /* first list; second is built by build_append2 from the cursor after it */
void *build_append2(const u8 *in) { dl(&in); return dl(&in); }
u64 core_count(void *t, void *u) { return count(t); }
void *core_mirror(void *t, void *u) { return mirror(t); }
u64 core_nontail(void *t, void *u) { return nsum(t); }
void *core_reverse(void *t, void *u) { return rev(t); }
void *core_append(void *t, void *u) { return app(t, u); }
u64 core_hasparam(void *t, void *u) { return hasp(t); }
u64 e2e_count(const u8 *in, u64 n, u8 *out) { u64 r = count(dt(&in)); st8(&out, r); return 8; }
u64 e2e_mirror(const u8 *in, u64 n, u8 *out) { u8 *o = out; et(mirror(dt(&in)), &o); return o - out; }
u64 e2e_nontail(const u8 *in, u64 n, u8 *out) { u64 r = nsum(dl(&in)); st8(&out, r); return 8; }
u64 e2e_reverse(const u8 *in, u64 n, u8 *out) { u8 *o = out; el(rev(dl(&in)), &o); return o - out; }
u64 e2e_append(const u8 *in, u64 n, u8 *out) { L *a = dl(&in); L *b = dl(&in); u8 *o = out; el(app(a, b), &o); return o - out; }
u64 e2e_hasparam(const u8 *in, u64 n, u8 *out) { *out = hasp(dv(&in)); return 1; }
