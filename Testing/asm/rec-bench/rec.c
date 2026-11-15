unsigned long sumrec(const unsigned char *b, unsigned long n, unsigned long i) { return i < n ? b[i] + sumrec(b, n, i + 1) : 0; }
unsigned long fib(unsigned long n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
