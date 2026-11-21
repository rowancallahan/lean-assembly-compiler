#!/usr/bin/env bash
# supervisor.sh: hourly: refresh the two compilers from origin (combined-2, syntax-1), restart campaigns on a new head,
# write Testing/notes/LEAN_DIFF.md from the campaign logs, commit + push branch lean-diff. UNPROVEN glue. Paths: /tmp/claude-0.
R=/home/user/lean-assembly-compiler; D=$R/Testing/nano/v2self/fuzz/lean_diff; O=/tmp/claude-0/camp2
while :; do
  [ -n "$NOSLEEP" ] || sleep 3600; NOSLEEP=
  cd $R && git fetch -q origin main keep_round1_syntax-1 || continue
  for p in "cur main" "syn keep_round1_syntax-1"; do set -- $p
    h=$(git rev-parse origin/$2); [ "$(cat $O/$1.head 2>/dev/null)" = "$h" ] && continue
    (cd /tmp/claude-0/wt_$1 && git checkout -q --detach $h) && git show $h:Testing/nano/v2self/B2.bin > /tmp/claude-0/ld/$1.new && mv /tmp/claude-0/ld/$1.new /tmp/claude-0/ld/$1.bin
    gcc_ok=1; echo $h > $O/$1.head
    pkill -f "campaign.py $1 " ; sleep 1
    (cd $O && ARMC=/tmp/claude-0/wt_$1/Testing/nano/v2self/native_arm OUT=$O J=2 nohup python3 $D/campaign.py $1 /tmp/claude-0/ld/$1.bin $RANDOM$RANDOM 150 >> $O/$1.log 2>&1 &)
  done
  python3 $D/report.py $O > $R/Testing/notes/LEAN_DIFF.md
  cd $R && git add Testing/notes/LEAN_DIFF.md Testing/nano/v2self/fuzz/lean_diff && git commit -q -m "LEAN_DIFF: hourly tally" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01MfKuVYxHRXmZCfK6uNURXy" && git push -q origin HEAD:keep_round1_lean-diff
done
