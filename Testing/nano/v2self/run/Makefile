# nanorun: run the nano compiler C and the programs it compiles on any host (UNPROVEN glue, see README.md)
# From this directory:   make            builds ./nanorun
#                        make demo       compiles demo.lean with the compiler, then runs the result on demo.in
#                        make selfcheck  compiles the compiler's own source and compares with B2.bin
B2 = ../B2.bin

nanorun: nanorun.c
	cc -O2 nanorun.c -o nanorun

# (a) compile a nano program: the compiler binary B2 reads the source text and writes machine code
demo.bin: nanorun demo.lean
	./nanorun $(B2) demo.lean demo.bin

# (b) run it: the compiled code reads demo.in and writes demo.out
demo: demo.bin
	printf 'hello' > demo.in
	./nanorun demo.bin demo.in demo.out
	od -An -c demo.out

selfcheck: nanorun
	./nanorun $(B2) ../self_S_input.txt B3.bin
	cmp B3.bin $(B2) && echo "fixed point: B3 == B2"

clean:
	rm -f nanorun demo.bin demo.in demo.out B3.bin
