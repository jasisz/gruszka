# Changelog

## Unreleased

Reads susz 0.5.0 files whose inductive blocks do not carry `isReflexive`
(Susz kind 8, the NOREFL section): Lean since the kernel renovation
(lean4#16595) no longer has the field, so its exports leave it out.
Gruszka computes isReflexive as before and compares it with the file only
where the file gives it.

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
