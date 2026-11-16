// usage: driver code.bin args.bin -> runs nano code (a0 = args, a1 = out word); prints the 8 result bytes; checks sp restored
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
static long rd(const char *f, unsigned char *b) { FILE *h = fopen(f, "rb"); if (!h) exit(2); long n = fread(b, 1, 1 << 20, h); fclose(h); return n; }
int main(int c, char **v) {
  unsigned char *code = mmap(0, 1 << 20, 7, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  static unsigned char in[1 << 20]; static unsigned long out;
  long cl = rd(v[1], code); rd(v[2], in);
  __builtin___clear_cache((char *)code, (char *)code + cl);
  register long a0 asm("a0") = (long)in, a1 asm("a1") = (long)&out;
  long sp0, sp1;
  asm volatile("mv %0, sp\n jalr ra, %4, 0\n mv %1, sp" : "=&r"(sp0), "=&r"(sp1), "+r"(a0), "+r"(a1) : "r"(code) : "ra", "t0", "t1", "memory");
  if (sp0 != sp1) { fprintf(stderr, "sp not restored\n"); return 3; }
  if (getenv("DBG")) fprintf(stderr, "in0=%lu out=%lu\n", *(unsigned long*)in, out);
  fwrite(&out, 8, 1, stdout);
  return 0;
}
