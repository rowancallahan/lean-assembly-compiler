/* Natural C versions of the benchmarked functions. Uniform signature (in, n, scr, out) so the same driver calls all.
   Compiled freestanding with -fno-tree-loop-distribute-patterns (no memcpy/memset calls). */
typedef unsigned char u8; typedef unsigned long u64; typedef long i64;
#define NI __attribute__((noinline))

/* ---- sorting ---- */
static NI void ms_buf(u8 *buf, u64 n, u8 *scr) {         /* stable bottom-up merge sort of buf[0..n), result in buf */
  u8 *src = buf, *dst = scr;
  for (u64 w = 1; w < n; w *= 2) {
    for (u64 lo = 0; lo < n; lo += 2 * w) {
      u64 mid = lo + w < n ? lo + w : n, hi = mid + w < n ? mid + w : n, i = lo, j = mid, k = lo;
      while (i < mid && j < hi) dst[k++] = src[j] < src[i] ? src[j++] : src[i++];
      while (i < mid) dst[k++] = src[i++];
      while (j < hi) dst[k++] = src[j++];
    }
    u8 *t = src; src = dst; dst = t;
  }
  if (src != buf) for (u64 i = 0; i < n; i++) buf[i] = src[i];
}
NI void c_msort(const u8 *in, u64 n, u8 *scr, u8 *out) { for (u64 i = 0; i < n; i++) out[i] = in[i]; ms_buf(out, n, scr); }
static NI void ins_buf(u8 *a, u64 n) {
  for (u64 i = 1; i < n; i++) { u8 v = a[i]; u64 j = i; while (j > 0 && a[j - 1] > v) { a[j] = a[j - 1]; j--; } a[j] = v; }
}
NI void c_insertion(const u8 *in, u64 n, u8 *scr, u8 *out) { for (u64 i = 0; i < n; i++) out[i] = in[i]; ins_buf(out, n); }

/* ---- simple array loops ---- */
NI u64 c_sum(const u8 *in, u64 n, u8 *scr, u8 *out) { u64 s = 0; for (u64 i = 0; i < n; i++) s += in[i]; return s; }
NI void c_take(const u8 *in, u64 n, u8 *scr, u8 *out) { for (u64 i = 0; i < n; i++) out[i] = in[i]; }   /* take n (= len) */
NI void c_inc(const u8 *in, u64 n, u8 *scr, u8 *out) { for (u64 i = 0; i < n; i++) out[i] = in[i] + 1; }   /* map (+1) */

/* ---- loops on numbers ---- */
NI u64 c_gcd(u64 a, u64 b) { while (a && b) { if (a < b) b -= a; else a -= b; } return a ? a : b; }
NI u64 c_sumdown(u64 n, u64 acc) { while (n) { acc += n; n--; } return acc; }

/* ---- the pipe examples (asm/pipe-words), natural C ---- */
NI void c_revinc5(const u8 *in, u64 n, u8 *scr, u8 *out) { u64 k = n < 5 ? n : 5; for (u64 i = 0; i < k; i++) out[i] = in[k - 1 - i] + 1; }
NI void c_mapsum(const u8 *in, u64 n, u8 *scr, u8 *out) { u8 s = 0; for (u64 i = 0; i < n; i++) s += in[i] < 10 ? in[i] ^ 0x20 : in[i] - 1; out[0] = s; }
NI void c_revtake5(const u8 *in, u64 n, u8 *scr, u8 *out) { u64 k = n < 5 ? n : 5; for (u64 i = 0; i < k; i++) out[i] = in[n - 1 - i]; }
NI void c_mapsort(const u8 *in, u64 n, u8 *scr, u8 *out) { for (u64 i = 0; i < n; i++) out[i] = in[i] & 0x7f; ms_buf(out, n, scr); }
NI void c_sort(const u8 *in, u64 n, u8 *scr, u8 *out) { c_msort(in, n, scr, out); }
NI void c_sum64(const u8 *in, u64 n, u8 *scr, u8 *out) { u64 s = 0; for (u64 i = 0; i < n; i++) s += in[i]; for (int i = 0; i < 8; i++) out[i] = s >> (8 * i); }
NI void c_hash64(const u8 *in, u64 n, u8 *scr, u8 *out) { u64 a = 5381; for (u64 i = 0; i < n; i++) a = (a ^ in[i]) + (a << 5); for (int i = 0; i < 8; i++) out[i] = a >> (8 * i); }
NI void c_sortdesc(const u8 *in, u64 n, u8 *scr, u8 *out) {   /* sort, reverse, drop 2, 3 -> 0 */
  c_msort(in, n, scr, scr + n + 64);                          /* sorted copy in the upper scratch */
  u8 *s = scr + n + 64;
  for (u64 i = 0; i + 2 < n; i++) { u8 v = s[n - 3 - i]; out[i] = v != 3 ? v : 0; }
}
NI void c_mid(const u8 *in, u64 n, u8 *scr, u8 *out) {         /* (sorted.drop 1).take 3 */
  c_msort(in, n, scr, scr + n + 64); u8 *s = scr + n + 64;
  for (u64 i = 0; i < 3 && 1 + i < n; i++) out[i] = s[1 + i];
}
NI void c_foldsorted(const u8 *in, u64 n, u8 *scr, u8 *out) {  /* (sorted.reverse.take 4).foldl (fun a x => (a - x) ^ 1) 7 */
  c_msort(in, n, scr, scr + n + 64); u8 *s = scr + n + 64; u8 a = 7;
  for (u64 t = 0; t < 4 && t < n; t++) a = (u8)(a - s[n - 1 - t]) ^ 1;
  out[0] = a;
}
NI void c_twosort(const u8 *in, u64 n, u8 *scr, u8 *out) {     /* sort (map f (reverse (take 10 (sort (drop 3 xs))))) */
  u64 m = n > 3 ? n - 3 : 0, k = m < 10 ? m : 10;
  c_msort(in + 3, m, scr, scr + n + 64); u8 *s = scr + n + 64;
  for (u64 i = 0; i < k; i++) { u8 x = s[k - 1 - i]; out[i] = x >= 0x80 ? x | 1 : 0xff - x; }
  ms_buf(out, k, scr);
}

/* ---- expressions (Proven/Reify.lean demo, demo2) ---- */
NI u64 c_demo(u64 a, u64 b, u64 c, u64 d) { return ((a + b) ^ (c & 0xff)) - (d | 0x1234); }
NI u64 c_demo2(u64 a, u64 b, u64 c, u64 d) {
  if (((u64)(a < b) ^ (u64)((i64)a < (i64)c)) == 0) return (a << (d & 63)) + (b >> (c & 63));
  return (u64)(c == d) - (u64)((i64)c >> (a & 63));
}
