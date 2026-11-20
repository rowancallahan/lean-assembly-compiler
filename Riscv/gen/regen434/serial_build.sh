# usage: serial_build.sh <lakedir> <modlist> <outtsv>
cd "$1"; source ~/.elan/env
/usr/bin/time -f "Sail	%e	%M	%x" -a -o "$3" lake build Sail > "$3.log" 2>&1
while read m; do
  /usr/bin/time -f "$m	%e	%M	%x" -a -o "$3" lake build "$m" >> "$3.log" 2>&1
done < "$2"
echo DONE >> "$3"
