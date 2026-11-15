// usage: driver code.bin input.bin -> writes output bytes to stdout. Runs the tiny-compiled code (a0=in, a1=n, a2=out).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
static long rd(const char *f, unsigned char *b) { FILE *h = fopen(f, "rb"); if (!h) exit(2); long n = fread(b, 1, 1 << 20, h); fclose(h); return n; }
int main(int c, char **v) {
  unsigned char *code = mmap(0, 1 << 20, 7, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  static unsigned char in[1 << 20], out[1 << 20];
  long cl = rd(v[1], code), n = rd(v[2], in);
  __builtin___clear_cache((char *)code, (char *)code + cl);
  register long a0 asm("a0") = (long)in, a1 asm("a1") = n, a2 asm("a2") = (long)out;
  asm volatile("jalr ra, %3, 0" : "+r"(a0), "+r"(a1), "+r"(a2) : "r"(code) : "ra", "t0", "t1", "t3", "memory");
  fwrite(out, 1, a2 - (long)out, stdout);
  return 0;
}
