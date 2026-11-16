#!/bin/bash
# Paged arrays (NOTES section 30): axioms of the paged-array theorems.  Machine theorems (`…implements1`, `implements1_wa*`)
# must depend on exactly the axioms of `implements1_of_execO` (the Sail model set of expected-axioms.txt);
# source-level theorems (`Pg.comp_ok`, `runs_of`, `….good`) on propext / Classical.choice / Quot.sound at most.
set -eo pipefail
H=$(cd "$(dirname "$0")" && pwd); R=$(cd "$H/../.." && pwd); cd "$R"
export PATH=$HOME/.elan/bin:$PATH
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
lake env lean "$H/axioms_paged.lean" > "$T/out.txt" 2>&1 || { cat "$T/out.txt"; exit 1; }
tr -d '\n' < "$T/out.txt" | sed "s/'Proven/\n'Proven/g; s/ //g" | grep -v '^$' > "$T/got.txt"
ref=$(grep "^'Proven.Mach.Riscv.implements1_of_execO'" "$T/got.txt" | sed 's/^[^:]*://')
grep -qxF "'Proven.Mach.Riscv.implements1_of_execO'dependsonaxioms:$ref" "$H/expected-axioms.txt" \
  || { echo "implements1_of_execO axioms differ from expected-axioms.txt"; exit 1; }
fail=0
while read -r l; do
  n=${l%%\'depends*}; n=${n#\'}; ax=${l#*axioms:}
  case "$n" in
    *implements1*|*pg_core|*pg_of_*|*copy_implements|*lz_implements) [ "$ax" = "$ref" ] && echo "  ok $n (Sail model set)" || { echo "  BAD $n: $ax"; fail=1; } ;;
    *) for a in $(echo "$ax" | tr -d '[]' | tr ',' ' '); do
         case "$a" in propext|Classical.choice|Quot.sound) ;; *) echo "  BAD $n: $a"; fail=1 ;; esac
       done; [ $fail = 0 ] && echo "  ok $n ($ax)" ;;
  esac
done < <(grep -v "implements1_of_execO" "$T/got.txt")
[ $fail = 0 ] && echo "PAGED AXIOMS OK" || exit 1
