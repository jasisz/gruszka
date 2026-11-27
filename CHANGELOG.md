# Changelog

## 0.2.4

Soundness fixes, found by an audit of the premises of every shortcut
against the official Lean kernel (4.35 and pre-release 55bd690). Two
hand-made exports could get a closed proof of `False`, without axioms,
accepted by 0.2.3; Lean's own kernel rejects both, so no export of a
real Lean build can contain them, and no result checked from one is
affected. Verdicts on both Arenas' tests are unchanged; on mathlib at
4 workers instructions (+0.05%), time and memory are unchanged.

- Nat operations with universe levels unfold. The kernel computes on
  literals only `Nat.add`, `Nat.sub`, ... as constants with no levels
  (`mk_constant(Nat.add)`); Gruszka recognised them by name, so with a
  `Nat.add.{u}` defined otherwise `Nat.add.{0} 0 0` was computed natively
  and `False` was proved. This covered whnf, lazy delta, the bits fusion
  of `shiftRight` and the ground machine; a row gets a native operation
  now only when its declaration has no universe parameters.
- `Nat.zero` and `Nat.succ` with universe levels are constructors, not
  literals: with `inductive Nat.{v}`, `Nat.zero.{0}` was read as the
  literal 0, which proved `False` together with an unlevelled `Nat.add`.
- A nested occurrence counts only where it is in the syntax, as Lean's
  `elim_nested_inductive` replaces it before checking positivity: a
  field whose whnf only reveals the nested type (`(fun x => L x) T`,
  through a definition or a `let`) is rejected. It was accepted.
- Levels are compared term by term (a max of guarded terms): the cases
  of independent `imax`es add up instead of multiplying. Twenty
  independent triples (the beta's `109_levelImaxNested` twenty times
  under one `max`) ran past 20 s; they take milliseconds.
- A cut made in a round of the R strategy belongs to the step that made
  it: a lazy delta loop nested in the unfolding (through a K recursor's
  check) took it, and a valid file was rejected.

## 0.2.3

Soundness fixes, found by our own conformance testing against the official
Lean kernel (pre-release 55bd690). Two hand-made exports could get a closed
proof of `False`, without axioms, accepted by 0.2.2; Lean's own kernel
rejects both, so no export of a real Lean build can contain them, and no
result checked from one is affected. Verdicts, instructions, time and
memory on Init are unchanged.

- A definition is taken as a `casesOn` only when each minor wrapper binds
  exactly the arguments the recursor's rule passes it: the fields and one
  induction hypothesis per recursive field. Before, at least as many
  lambdas as fields were enough, so a wrapper that left the hypotheses to
  the minor (`fun motive t z s => Nat.rec motive z (fun n => s n) t`) was
  reduced as if they were dropped, which proved `0 = 1` with the standard
  prelude. Valid exports of that shape, rejected before, are accepted.
- `Nat.log2` unfolds from its definition. It was computed natively by its
  name, which the official kernel does not do (its built-ins are
  `Nat.succ` and the 14 binary operations), so with `Nat.log2` defined
  otherwise in the export a proof of `False` was accepted.
- A nested inductive whose container's parameter is a function type
  (`inductive T | mk : List (Nat → T) → T`) is reflexive, as Lean computes
  it on the auxiliary constructors after instantiating them; it was
  rejected with "isRec / isReflexive do not match the declaration".
- Undeclared universe parameters are looked for once per level node: on a
  level built as a DAG the walk was exponential (a 2.8 KB export took more
  than 20 s).
- README: a full check type-checks unsafe and partial declarations in an
  arena of their own; the sentence saying they are skipped was about
  `--only`.

## 0.2.2

Passes lean-kernel-arena-beta: all 213 good and 137 bad tests, exported by
Lean `pr-release-16595-55bd690` (the kernel renovation, lean4#16595), Init
and Std included. 0.2.1 could not read most of them: their inductive types
no longer carry `isReflexive`, and susz 0.4.0 refused to pack them. The
renovation tests that are ahead of that toolchain pass too. At 4 workers
on Init, Std, mathlib and the CFSG slices LyOm, run349 and run124, the
verdicts are the same as 0.2.1's, instructions and ticks are within +0.5%
(mathlib +0.36% instructions, +0.73% ticks), and peak memory differs by
less than the spread between two runs of the same build.

Changes:

- Reads susz 0.5.0 files whose inductive blocks do not carry `isReflexive`
  (Susz kind 8, the NOREFL section). Gruszka computes isReflexive as before
  and compares it with the file only where the file gives it.
- `Quot` may be declared in `Sort (max 1 u)` (lean4#15023), so that a
  quotient of a proposition is a type, as well as in `Sort u` as before.
  Proof irrelevance follows the declared type.
- Complete level comparison: levels are equal (or `≥`) when they are for
  every assignment of the parameters. When Lean's normal forms differ and
  an `imax` is left, the parameters that decide it are split on (`p = 0`
  and `p = p' + 1`), with a memo, ticking at every step. A normal form no
  longer keeps an `imax` that became a `max`.
- Eta for partial applications: a constructor of a structure missing
  fields (lean4#15373), and a recursor of a structure or with rule K that
  stops at or before its major premise (lean4#15374), are compared by
  applying both sides to a new variable.
- Unit-like types (lean4#15372): a structure with eta whose fields are all
  proofs or of unit-like types, or a function type into one. Any two of its
  elements are definitionally equal.

## 0.2.1

Six of the seven slowest CFSG declarations of the 0.2.0 run are checked in
well under a second. Times are for each declaration's slice of the CFSG
export, one worker, Apple M2 Pro, release build; the 0.2.0 column is from
the full run on r7a.16xlarge with 64 workers.

| declaration | 0.2.0 (AWS, 64 workers) | 0.2.1 (M2, 1 worker) |
| --- | ---: | ---: |
| `bound_of` | 943 s | 0.58 s |
| `covHA_sound` | 179 s | 0.58 s |
| `tits_star_check_0` | 85 s | 0.58 s |
| `piv_eq` | 82 s | 0.58 s |
| `cnt_ok` | 68.5 s | 0.57 s |
| `u52ne_f_normK` | 52 s | 0.57 s |
| `e6SimpleCheck` | 196 s | 69.5 s (unchanged) |

Init, Std, mathlib and the CFSG slices used as corpora stay within 1% in
instructions and memory. The whole of CFSG has not been rerun with 0.2.1.

Changes:

- The meeting race (M) takes the steps of its two sides in turn, each
  within a budget that doubles when it runs out (milestone 61). A side
  whose first step is a whole computation (`Bool.and` over a `List.all`
  under a binder) no longer keeps the other side, which meets it in one
  step, from moving.
- Delta in a round (R) gives the arguments of a pair it comes to with the
  same head half of what is left of the round (milestone 62). Past that it
  unfolds both sides, and the next, twice as long, round tries the
  arguments first again. The pair the race was started on keeps Lean's
  order.
- In the `knobs` build only: counters for work redone after region
  rollbacks and variants of keeping region results (`SK_REDO_CLASS`,
  `SK_REGION_FRONT=3/4`). No rule passed the thresholds for
  `e6SimpleCheck`; see milestone 63 in docs/architecture.md.

## 0.2.0

Checks all of CFSG (`cfsg-5437cdc.susz`, 39,656,013 declarations) on
AWS r7a.16xlarge (AMD EPYC 9R14, 64 vCPU, 493 GB), 64 workers, PGO trained
on Init, `-C target-cpu=native`: accepted, wall 1:25:28, peak RSS
275.8 GiB, CPU time (user + sys) 319,930 s (88.9 h), no swap. Axioms used:
`propext`, `Classical.choice`, `Quot.sound` (`sorryAx` unused).

Gruszka 0.1.1 on r7a.8xlarge with 32 workers took 3:11:28, 183.7 GiB and
362,793 s of CPU time. 0.2.0 uses 12% less CPU time and is 2.24× faster
on twice the workers; its peak memory is 50% higher, because each worker
keeps its own arenas. All 64 workers stayed busy until about 30 s before
the end. The slowest declaration,
`CertificateChecks.KernelSpor.SuzMcF.bound_of`, took about 943 s.

Changes:

- Lean kernel renovation (lean4export 3.2, lean4#16595): the five
  inductive flags (impredicative, K, projections, eta, large elimination)
  are checked by Lean's new rules and then used by recursors, projections,
  structure eta and iota. Exports without the flags are checked by the old
  rules, as before; a file mixing flagged and unflagged blocks is rejected.
- Susz 0.4.0 (reads the flagged blocks), from crates.io.
- Nat multiplication is done whole by the bignum library instead of a
  loop of Gruszka's own for a short factor (CFSG slice run124, 4 workers:
  −38.8% instructions, peak memory +7%).
- The spine table (milestone 56) and the frame table (milestone 58) move
  their entries by tag when they grow, without rehashing the values.
- On Linux, reserved ranges ask for transparent huge pages (fewer page
  walks on large certificates).
- Derived rules: a definition unfolded often in a session gets a rule per
  constructor form, so a step down a list is one rule, not four
  unfoldings.
- Inside a region, whnf loop states made of older values keep the loop's
  result through a rollback, so repeated lookups into a large list are not
  walked again.
- Fix: a theorem's proof block decoded inside a region keeps its literals
  after the region is rolled back (a valid file could be declined).
- Measured and off by default, in the `knobs` build only: `SK_NAT_IDENT=1`
  (operations whose result is an operand return it) and `SK_NAT_BITS=1`
  (bits of an unforced shift read from the digits).

## 0.1.x

Releases before 0.2.0 are the tags `v0.1.1` and `v0.1.2`.
