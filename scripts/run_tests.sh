#!/bin/bash
# Runs every Arena small test (ndjson, packed in-process) and tabulates
# good/bad x accepted/rejected/declined. Usage: run_tests.sh [BIN] [OUT]
X=${ARENA_TESTS:?set ARENA_TESTS to the Arena tests directory}
BIN=${1:-$(cd "$(dirname "$0")/.." && pwd)/target/release/gruszka}
OUT=${2:-/dev/stdout}
: > /tmp/sk-res.$$
cd $X
for f in $(find good bad -name '*.ndjson' | grep -v /perf/ | sort); do
  exp=${f%%/*}
  r=$(~/PycharmProjects/pestka/bin/capped 4000 60 $BIN $f 1 2>/dev/null | tail -1)
  code=$?
  case "$r" in accepted*) v=accepted;; rejected*) v=rejected;; declined*) v=declined;; *) v="crash($code)";; esac
  echo "$exp $v $f :: $r" >> /tmp/sk-res.$$
done
{
echo "== summary"; awk '{print $1, $2}' /tmp/sk-res.$$ | sort | uniq -c
echo "== WRONG (bad accepted)"; grep '^bad accepted' /tmp/sk-res.$$
echo "== good not accepted"; grep '^good' /tmp/sk-res.$$ | grep -v ' accepted '
echo "== bad declined/crash"; grep '^bad' /tmp/sk-res.$$ | grep -v ' rejected '
} > $OUT
rm /tmp/sk-res.$$
