#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned char u8; typedef unsigned long u64;
#define X(n) u64 c_##n(const u8*, u64, u8*);
X(crcraw) X(b64all) X(findnl) X(be32at0) X(tailsum) X(nontailsum) X(taillength) X(booklength) X(take5) X(drop5) X(filterall) X(inceach) X(twice) X(headof) X(finalof) X(findfirstgt3)
int main(int argc, char **argv) {
  u64 n = atol(argv[2]), reps = atol(argv[3]), s = 88172645463325252UL, acc = 0; int scan = !strcmp(argv[4], "scan");
  u8 *xs = malloc(n + 1), *out = malloc(2 * n + 16);
  for (u64 i = 0; i < n; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; xs[i] = scan ? (s >> 33) & 3 : (s >> 33); }
  u64 (*f)(const u8*, u64, u8*) = 0;
#define S(n) if (!strcmp(argv[1], #n)) f = c_##n;
  S(crcraw) S(b64all) S(findnl) S(be32at0) S(tailsum) S(nontailsum) S(taillength) S(booklength) S(take5) S(drop5) S(filterall) S(inceach) S(twice) S(headof) S(finalof) S(findfirstgt3)
  for (u64 r = 0; r < reps; r++) { xs[0] ^= r & 0; acc += f(xs, n, out) + out[0]; __asm__ volatile("" ::: "memory"); }
  printf("%lu\n", acc);
}
