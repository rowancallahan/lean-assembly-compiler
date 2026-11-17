// usage: driver code.bin args.bin [workbytes] -> runs nano code in the StartCorrect convention (a0 = args, a1 = length, a2 = work base,
// sp = work top, a3 = output, deliberately UNALIGNED); prints the 8 result bytes; checks sp, a0 (not the oom flag), guard bytes
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
static long rd(const char *f, unsigned char *b) { FILE *h = fopen(f, "rb"); if (!h) exit(2); long n = fread(b, 1, 1 << 20, h); fclose(h); return n; }
int main(int c, char **v) {
  unsigned char *code = mmap(0, 1 << 20, 7, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  static unsigned char in[(1 << 20) + 1]; static unsigned char ob[32]; static unsigned long wk[1 << 16];
  long cl = rd(v[1], code); long il = rd(v[2], in + 1);  /* args at an odd address */
  long wb = c > 3 ? atol(v[3]) : 8 * (1 << 16);
  __builtin___clear_cache((char *)code, (char *)code + cl);
  memset(ob, 0x55, sizeof ob);
  unsigned char *args = in + 1;
  register long a0 asm("a0") = (long)args, a1 asm("a1") = il, a2 asm("a2") = (long)((char *)wk + 8 * (1 << 16) - wb), a3 asm("a3") = (long)(ob + 1);
  long top = (long)wk + 8 * (1 << 16), sp1;
  asm volatile("mv t4, sp\n mv sp, %[top]\n jalr ra, %[code], 0\n mv %[sp1], sp\n mv sp, t4"
               : [sp1] "=&r"(sp1), "+r"(a0), "+r"(a1), "+r"(a2), "+r"(a3)
               : [top] "r"(top), [code] "r"(code) : "ra", "t0", "t1", "t3", "t4", "t6", "memory");
  if (sp1 != top) { fprintf(stderr, "sp not restored\n"); return 3; }
  if (a0 == -1) { fprintf(stderr, "oom flag\n"); return 4; }
  if (ob[0] != 0x55 || ob[9] != 0x55) { fprintf(stderr, "output guard\n"); return 5; }
  fwrite(ob + 1, 8, 1, stdout);
  return 0;
}
