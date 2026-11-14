#!/bin/bash
# usage: run_tries.sh [files...]  (default: all *.lean here); prints "name<TAB>OK|ERR<TAB>first error line"
cd "$(dirname "$0")/../../.." ; export PATH=~/.elan/bin:$PATH
for f in ${@:-Testing/notes/book_tries/*.lean}; do
  n=$(basename $f .lean)
  o=$(lake env lean $f 2>&1); 
  if echo "$o" | grep -q 'error'; then printf '%s\tERR\t%s\n' $n "$(echo "$o" | grep -m1 -A2 'error' | tr '\n' ' ' | cut -c1-300)"; else printf '%s\tOK\t\n' $n; fi
done
