/* gcc -O2 references for NOTES section 22 (rv64im: the M extension, as our words use it). */
typedef unsigned long u64;
typedef unsigned char u8;
static u64 rd32(const u8 *p) { return (u64)p[0] | (u64)p[1] << 8 | (u64)p[2] << 16 | (u64)p[3] << 24; }
/* Nat.gcd m n = if m = 0 then n else gcd (n % m) m */
u64 c_gcd(const u8 *xs, u64 n) {
  u64 a = n >= 4 ? rd32(xs) : 0, b = n >= 8 ? rd32(xs + 4) : 0;
  while (a != 0) { u64 t = b % a; b = a; a = t; }
  return b;
}
/* kraftSumFast (countLengthsFast xs 15) 15 */
u64 c_kraft(const u8 *xs, u64 n) {
  u64 count[16];
  for (int j = 0; j < 16; j++) ((volatile u64 *)count)[j] = 0;
  for (u64 i = 0; i < n; i++) { u64 l = xs[i]; if (0 < l && l <= 15) count[l]++; }
  u64 acc = 0;
  for (u64 b = 0; b <= 15; b++) acc += count[b] * (1UL << (15 - b));
  return acc;
}
