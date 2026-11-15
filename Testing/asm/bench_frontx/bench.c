/* natural C versions of the Frontx entry points.  f(xs, n, out) writes the result into out (Res.enc layout) and
   returns the list length (lists) or 0.  Compiled freestanding for RV64 (-O2) and natively for the x86 sanity run. */
typedef unsigned char u8; typedef unsigned int u32; typedef unsigned long u64;
#define F(name) u64 c_##name(const u8 *xs, u64 n, u8 *out)
static void st(u8 *o, u64 v, int k) { for (int i = 0; i < k; i++) o[i] = v >> (8 * i); }
F(crcraw) { u32 c = 0xFFFFFFFF; for (u64 i = 0; i < n; i++) { c ^= xs[i]; for (int b = 0; b < 8; b++) c = (c & 1) ? (c >> 1) ^ 0xEDB88320 : c >> 1; } st(out, c, 4); return 0; }
static u32 d64(u8 c) { return c >= 65 && c <= 90 ? c - 65 : c >= 97 && c <= 122 ? c - 71 : c >= 48 && c <= 57 ? c + 4 : c == 43 ? 62 : c == 47 ? 63 : 64; }
F(b64all) { u32 s = 0; for (u64 i = 0; i < n; i++) s += d64(xs[i]); st(out, s, 4); return 0; }
F(findnl) { u64 j = 0; while (j < n && xs[j] != 10) j++; st(out, j, 8); return 0; }
static u64 at(const u8 *xs, u64 n, u64 i) { return i < n ? xs[i] : 0; }
F(be32at0) { st(out, at(xs, n, 0) << 24 | at(xs, n, 1) << 16 | at(xs, n, 2) << 8 | at(xs, n, 3), 8); return 0; }
F(tailsum) { u64 s = 0; for (u64 i = 0; i < n; i++) s += xs[i]; st(out, s, 8); return 0; }
F(nontailsum) { return c_tailsum(xs, n, out); }
F(taillength) { st(out, n, 8); return 0; }
F(booklength) { st(out, n, 8); return 0; }
F(take5) { u64 k = n < 5 ? n : 5; for (u64 i = 0; i < k; i++) out[i] = xs[i]; return k; }
F(drop5) { u64 j = 0; for (u64 i = 5; i < n; i++) out[j++] = xs[i]; return j; }
F(filterall) { u64 j = 0; for (u64 i = 0; i < n; i++) if (xs[i] > 3) out[j++] = xs[i]; return j; }
F(inceach) { for (u64 i = 0; i < n; i++) out[i] = xs[i] + 1; return n; }
F(twice) { for (u64 i = 0; i < n; i++) out[i] = out[n + i] = xs[i]; return 2 * n; }
F(headof) { out[0] = n > 0; out[1] = n > 0 ? xs[0] : 0; return 0; }
F(finalof) { out[0] = n > 0; out[1] = n > 0 ? xs[n - 1] : 0; return 0; }
F(findfirstgt3) { for (u64 i = 0; i < n; i++) if (xs[i] > 3) { out[0] = 1; out[1] = xs[i]; return 0; } out[0] = out[1] = 0; return 0; }
