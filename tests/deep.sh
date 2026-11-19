#!/bin/bash
# Milestone 42: deep vectors (scripts/deep_vectors.py) at the default stack
# (the expected verdict) and at small stacks (GRUSZKA_STACK_MB): a verdict
# every time, never a crash; at a small stack a good vector is accepted or
# declined, a bad one rejected or declined. Usage: tests/deep.sh BIN
D=$(cd "$(dirname "$0")/.." && pwd)
CAP=${CAP:-$D/scripts/capped}
BIN=${1:-$D/target/release/gruszka}
T=$(mktemp -d)
python3 $D/scripts/deep_vectors.py $T || exit 1
bad=0
for f in $T/*.ndjson; do
  b=$(basename $f .ndjson)
  for st in default 4 16 64; do
    if [ $st = default ]; then r=$("$CAP" 6000 120 $BIN $f 1 2>/dev/null | tail -1); rc=$?
    else r=$(GRUSZKA_STACK_MB=$st "$CAP" 6000 120 $BIN $f 1 2>/dev/null | tail -1); rc=$?; fi
    v=${r%%:*}
    ok=0
    case "$b:$st:$v" in
      *_bad:default:rejected|*_good:default:accepted) ok=1;;
      *_bad:*:rejected|*_bad:*:declined|*_good:*:accepted|*_good:*:declined) [ $st != default ] && ok=1;;
    esac
    echo "deep $b stack=$st: ${r:-crash (exit $rc)}"
    [ $ok = 1 ] || { echo "DEEP WRONG: $b stack=$st"; bad=1; }
  done
done
rm -rf $T
echo "deep: wrong=$bad"
exit $bad
