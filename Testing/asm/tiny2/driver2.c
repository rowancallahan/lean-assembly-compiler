// usage: driver2 code.bin x -> runs the RV64 code as uint64_t f(uint64_t x) (x in a0, result in a0; x16, x17 clobbered), prints the result
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
int main(int c, char **v) {
  unsigned char *code = mmap(0, 1 << 16, 7, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  FILE *h = fopen(v[1], "rb"); long n = fread(code, 1, 1 << 16, h); fclose(h);
  __builtin___clear_cache((char *)code, (char *)code + n);
  register unsigned long long a0 asm("a0") = strtoull(v[2], 0, 10);
  asm volatile("jalr ra, %1, 0" : "+r"(a0) : "r"(code) : "ra", "x16", "x17", "memory");
  printf("%llu\n", a0);
  return 0;
}
