#!/bin/bash
# Milestone 26: subset checks (--only, README "Checking part of a file"),
# Pestka's tests/only.sh mirrored, plus INDEX lies of Gruszka's own and a
# sweep over the adversarial vectors. Each case gives the exit status and
# the last line it expects, the same on one worker and on four.
#
# deps.ndjson (Pestka's tests/only): axioms A : Prop and a : A, then
# theorems good : A := a, badDep : A := A (ill typed), useBad : A :=
# badDep, bad : A := A (ill typed), last : A := good and good.twice : A :=
# good. A full check rejects it at badDep. useBad is checked: the proof of
# badDep, before it, is admitted unchecked.
#
# INDEX damaged by tests/only/indexbad.py ends a subset check that relies
# on the damaged entry as index invalid, and leaves a full check's verdict
# as it was.
#
# The sweep: for every tests/adv/bad_*.ndjson that a full check rejects at
# a named declaration X, `--only X` must reject at X too, and `--only` the
# file's last declaration must not be `checked` when X is an inductive
# block, a quotient record or has universe parameters named twice (those
# are checked or verified before the last target); it may be `checked`
# when X is an axiom, definition, theorem or opaque admitted unchecked
# (the documented trust), or unsafe or partial (skipped).
#
# Usage: tests/only.sh [BIN]; SUSZ names a susz 0.1.2 binary (packs with
# INDEX). Prints ONLYDONE bad=N; exit 1 on a failure.
D=$(cd "$(dirname "$0")/.." && pwd)
S=${GRUSZKA_WORK:-${TMPDIR:-/tmp}/gruszka-work}
BIN=${1:-$D/target/release/gruszka}
case "$BIN" in /*) ;; *) BIN=$PWD/$BIN;; esac
SUSZ=${SUSZ:-$(command -v susz || echo $S/m26/susz-0.1.2)}
P=${PESTKA:-$D/../pestka}  # a pestka checkout, for its test files
CAP=$D/scripts/capped
IB=$D/tests/only/indexbad.py
tmp=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp"' EXIT
fail=0
run() {
  # run WANT PATTERN ARGS...: status WANT and a last line matching PATTERN,
  # on one worker and on four.
  want=$1 pat=$2
  shift 2
  for w in 1 4; do
    "$CAP" 2000 20 "$BIN" "$@" "$w" >"$tmp/out" 2>&1
    got=$?
    last=$(tail -1 "$tmp/out")
    if [ "$got" -ne "$want" ] || ! printf '%s\n' "$last" | grep -Eq "$pat"; then
      echo "FAIL $* [$w]: status $got, expected $want; $last"
      fail=1
      return 1
    fi
  done
  echo "ok   $(printf '%s ' "$@" | sed "s|$tmp/||g; s|$D/||g")-> $last"
}
pack() { "$SUSZ" pack "$@" --threads 1 >/dev/null 2>&1; }
deps="$tmp/deps.susz"
pack "$D/tests/only/deps.ndjson" "$deps" || { echo "FAIL cannot pack deps.ndjson"; exit 1; }
pack "$D/tests/only/deps.ndjson" "$tmp/deps-n.susz" --no-index
run 1 '^rejected: badDep: ' "$deps"
run 0 '^checked: good \(subset; 2 earlier declarations admitted unchecked\)$' --only good "$deps"
run 0 '^checked: a \(subset; 1 earlier declarations admitted unchecked\)$' --only a "$deps"
run 1 '^rejected: bad: ' --only bad "$deps"
run 1 '^rejected: badDep: ' --only badDep "$deps"
run 0 '^checked: useBad \(subset; 4 earlier declarations admitted unchecked\)$' --only useBad "$deps"
run 0 '^checked: last,good \(2 declarations; subset; 5 earlier declarations admitted unchecked\)$' --only last,good "$deps"
run 0 '^checked: good\.\* \(subset; 7 earlier declarations admitted unchecked\)$' --only 'good.*' "$deps"
run 1 '^rejected: bad: ' --only useBad,bad "$deps"
run 0 '^checked: good \(subset; 2 earlier ' "$deps" --only good
run 0 '^checked: good,good \(subset; 2 earlier ' --only good,,good "$deps"
run 2 '^declined: not found: nope, A\.x: ' --only nope,A,A.x "$deps"
run 2 '^declined: not found: a\.\*: ' --only 'a.*' "$deps"
run 2 '^declined: .*has no INDEX section.*--no-index' --only good "$tmp/deps-n.susz"
run 2 '^declined: --only checks part of a Susz file' --only good "$D/tests/only/deps.ndjson"
run 2 '^declined: usage: ' --only
run 2 '^declined: --only needs at least one name$' --only , "$deps"
damage() {
  # damage MODE [NAME]: deps.susz with INDEX damaged.
  python3 -I "$IB" "$1" "$deps" "$tmp/bad.susz" $2 || { echo "FAIL indexbad $1"; fail=1; return 1; }
}
full_same() { run 1 '^rejected: badDep: ' "$tmp/bad.susz"; }
damage garbage && run 2 '^index invalid: INDEX @ [0-9]+: ' --only good "$tmp/bad.susz" && full_same
damage offset && run 2 '^index invalid: INDEX @ [0-9]+: entry [0-9]+: offset ' --only a "$tmp/bad.susz" && full_same
damage decl useBad && run 2 '^index invalid: INDEX @ [0-9]+: a name INDEX gives declaration [0-9]+ is not declared by it$' --only useBad "$tmp/bad.susz" &&
  run 0 '^checked: good ' --only good "$tmp/bad.susz" && full_same
damage kind a && run 2 '^index invalid: INDEX @ [0-9]+: entry 1: kind 1, its record.s is 0$' --only a "$tmp/bad.susz" && full_same
# Gruszka's own lies: a name sent to a later declaration (reading stops
# there, past the real one), a wrong proof block, unsorted keys, a
# declaration out of range, one entry too many, front coding off by one
damage later useBad && run 2 '^index invalid: INDEX @ [0-9]+: a name INDEX gives declaration 5 is not declared by it$' --only useBad "$tmp/bad.susz" && full_same
damage decl last && run 2 '^index invalid: INDEX @ [0-9]+: a name INDEX gives declaration 5 is not declared by it$' --only last "$tmp/bad.susz"
damage block good && run 2 '^index invalid: INDEX @ [0-9]+: entry 2: a block of 4 bytes at 0, its record.s is 3 bytes at 0$' --only good "$tmp/bad.susz" && full_same
damage order && run 2 '^index invalid: INDEX @ [0-9]+: name 1: keys out of order$' --only good "$tmp/bad.susz" && full_same
damage range && run 2 '^index invalid: INDEX @ [0-9]+: name 0: declaration 8 out of range$' --only good "$tmp/bad.susz" && full_same
damage count && run 2 '^index invalid: INDEX @ [0-9]+: decl-count 9, the file has 8 declarations$' --only good "$tmp/bad.susz" && full_same
damage shared && run 2 '^index invalid: INDEX @ [0-9]+: name 1: shared 1 is not the full common prefix$' --only good "$tmp/bad.susz" && full_same
# small.ndjson (Pestka's tests/export/wellformed): inductive types,
# structures and literals before the targets, checked as the environment
# is built; the counts are Pestka's
small="$tmp/small.susz"
pack "$P/tests/export/wellformed/small.ndjson" "$small" || { echo "FAIL cannot pack small.ndjson"; exit 1; }
run 0 '^accepted$' "$small"
run 0 '^checked: Small\.instReprPoint \(subset; 305 earlier declarations admitted unchecked\)$' --only Small.instReprPoint "$small"
run 0 '^checked: Nat\.ne_of_beq_eq_false \(subset; 294 earlier ' --only Nat.ne_of_beq_eq_false "$small"
run 0 '^checked: Small\.\* \(20 declarations; subset; 288 earlier ' --only 'Small.*' "$small"
run 0 '^checked: HMod\.mk \(subset; 134 earlier ' --only HMod.mk "$small"
run 0 '^checked: _private\.Init\.Prelude\.0\.Nat\.ne_of_beq_eq_false\.match_1_1 \(subset' --only _private.Init.Prelude.0.Nat.ne_of_beq_eq_false.match_1_1 "$small"
# an ill-typed declaration of Pestka's tests/export/illtyped, asked for by
# name, is rejected as a full check rejects it
for f in fin swap finAfterGood swapAfterGood idTwoAfterGood; do
  s="$tmp/$f.susz"
  pack "$P/tests/export/illtyped/$f.ndjson" "$s" || { echo "FAIL cannot pack $f.ndjson"; fail=1; continue; }
  "$BIN" "$s" 1 >"$tmp/full" 2>&1
  name=$(tail -1 "$tmp/full" | sed -nE 's/^rejected: ([^:]+): .*/\1/p')
  [ -n "$name" ] || { echo "FAIL $f: the full check names no declaration"; fail=1; continue; }
  run 1 "^$(tail -1 "$tmp/full" | sed 's/[].[*^$()+?{}|\\]/\\&/g')\$" --only "$name" "$s"
done
# the sweep over the adversarial vectors
n_sweep=0 n_skip=0 n_trust=0 n_other=0 n_built=0
for f in "$D"/tests/adv/bad_*.ndjson; do
  b=$(basename "$f" .ndjson)
  s="$tmp/$b.susz"
  pack "$f" "$s" || { n_skip=$((n_skip + 1)); continue; }
  full=$("$CAP" 2000 20 "$BIN" "$s" 1 2>/dev/null | tail -1)
  x=$(printf '%s\n' "$full" | sed -nE 's/^rejected: ([^: ]+): .*/\1/p')
  keys=$(python3 -I "$IB" keys "$s")
  if [ -z "$x" ] || ! printf '%s\n' "$keys" | grep -qxF "$x"; then
    n_skip=$((n_skip + 1)); continue
  fi
  n_sweep=$((n_sweep + 1))
  # the rejected declaration asked for: rejected at it (declined when it
  # is unsafe or partial, which a subset check does not check)
  r=$("$CAP" 2000 20 "$BIN" --only "$x" "$s" 1 2>/dev/null | tail -1)
  case "$r" in
    "rejected: $x: "*) skipped=0;;
    "declined: $x is unsafe or partial, which Gruszka does not check") skipped=1;;
    "declined: not found: "*) n_sweep=$((n_sweep - 1)); n_skip=$((n_skip + 1)); continue;;
    *) echo "FAIL sweep $b: --only $x: $r (full: $full)"; fail=1; continue;;
  esac
  last=$(printf '%s\n' "$keys" | tail -1)
  [ -n "$last" ] && [ "$last" != "$x" ] || continue
  # X's INDEX kind: 0 axiom, 1 definition, 2 theorem, 3 opaque, 4
  # quotient, 5 inductive, 6 theorem with a proof block
  kind=$(python3 -I "$IB" kindof "$s" "$x")
  for w in 1 4; do
    # (5 s: an admitted ill-typed definition may make a reduction run
    # forever, as in Pestka: bad_omega_first)
    r=$("$CAP" 2000 5 "$BIN" --only "$last" "$s" $w 2>/dev/null | tail -1)
    case "$r" in
      "rejected: $x: "*) [ $w = 1 ] && case "$kind" in 4|5) n_built=$((n_built + 1));; esac;;
      checked:*)
        # only through a declaration admitted unchecked or skipped
        case "$skipped$kind:$full" in
          *": universe parameters named twice") echo "FAIL sweep $b w$w: --only $last checked past $x: $r"; fail=1;;
          1*|0[01236]:*) [ $w = 1 ] && n_trust=$((n_trust + 1));;
          *) echo "FAIL sweep $b w$w: --only $last checked, but $x (kind $kind) is checked before the last target: $r"; fail=1;;
        esac;;
      *) [ $w = 1 ] && { n_other=$((n_other + 1)); echo "note sweep $b: full $full; --only $last: $r"; };;
    esac
  done
done
echo "sweep: $n_sweep vectors (skipped $n_skip: no named rejection, or a name INDEX keys differently); --only LAST: $n_built rejected at an earlier inductive block or quotient, $n_trust checked through a declaration admitted unchecked or skipped, $n_other another verdict"
echo "ONLYDONE bad=$fail"
exit $fail
