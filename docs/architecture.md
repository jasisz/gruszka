# Inside Gruszka

This document describes how the kernel is built, from its data and values
through checking, inductive groups and the soundness measures. For an
overview of Gruszka and instructions for running it, see the
[README](../README.md).

Gruszka reads [Susz](https://github.com/jasisz/susz). Mathlib's 38 million
environment terms are loaded into memory in about a second, at 13 bytes
each, while the 67 million terms inside proofs remain as bytes until their
theorem is checked.

Declarations are arranged in namespace order: they are grouped by the first
two components of their namespace, groups follow their order of first
appearance, and declarations within a group remain in file order.
`SK_ORDER=file` keeps file order throughout. Each worker starts with a
contiguous part of the chosen order and takes chunks from the front; when it
runs out, it takes the back half of the largest remaining part. The verdict
does not depend on this order (see Soundness measures).

## The idea

Terms are never built. Every expression examined by the kernel is a Susz
id: either a MAIN expression held in columns for the whole run, or an
expression from a proof block, decoded into the worker's arena at ids above
MAIN when a declaration needs it. Everything the checker creates is a
*value* in the worker's arena, represented by
weak-head forms with closures over environments of values (normalization by
evaluation). Type inference returns values as well. There is no term
substitution, no instantiation of universe parameters into terms, and no
reference counting. A worker keeps its arena for a *session* of
declarations and clears it when the session ends (see Sessions).

## Data

**Environment (shared, read-only).** MAIN expressions are stored in columns:
a kind byte with binder information folded in, three u32 fields (`a`, `b`,
`p`), and the exact loose-bound-variable range (u32). This range allows
closed terms to drop their environment and answers both "closed" and "uses
variable i". Names remain Susz name ids, with equality determined by value
through the reader's canonical names, so two records with the same name
denote the same constant. A u32 column maps every name id to its constant
row. Levels are interned once in a global table with canonical parameter
names, and terms store global level ids. Literals are copied out of the file
(big Nat as `BigUint`). Each declaration row contains its name, universe
parameters, type, declaring index and the kind-specific facts stated by the
file. Those facts remain untrusted until the declaration has been checked,
while proof blocks stay as `BlockRef`s.

**Worker (one per thread).** Its persistent state consists of a level
interner layered on the global table (Lean's simplifying `max`/`imax`,
normalization, equivalence, `is_geq`), interned level lists and level
substitutions, and memos keyed by level ids. These ids stay valid until the
level tables pass their bound (`SK_LVL_FLUSH`). Then the tables, every memo
keyed by them and the current session are dropped together. The block
arena, values, linked-list environments, spines, free-variable types, and
every cache keyed by value or arena ids are session state. They are cleared
together when a session ends, so a stale id cannot survive.

## Values

- `Clo { term, env, ls }`: a lambda or Pi term with its environment and its
  universe substitution `ls` (the constant whose body it came from and the
  levels it was used at). A `Clo` marked `infer` stands for *the type of*
  a lambda: a Pi whose codomain is the inferred type of the body.
- `Thunk { term, env, ls }`: an argument, evaluated on demand and memoized.
- `Neu { head, spine }`: a free variable, a constant (with its level list)
  or a stuck value, applied to a spine of arguments and projections.
- `Sort`, `Lit`.

All values are hash-consed by structure: the same term, environment and
substitution, or the same head and spine, produce the same value.
Environments and spine nodes are hash-consed as well, so reaching the same
computation twice yields the same id. Definitional equality then gets an
O(1) identity test, and per-value memos (forced thunk, `whnf`,
`whnf_core`, type) are shared. Without this sharing, two unfoldings of the
same definition produce equal but separate graphs, and comparing them can
take as long as running the definition. In Init, that was the difference
between seconds and divergence.

## Sessions

A worker keeps its arena, and every table keyed by arena ids, from one
declaration to the next for a *session* (milestone 10). Within a session a
value id always means the same computation. Its memos and every cache keyed
by ids remain facts about that value when a later declaration of the
session meets it again. A session ends, and all of this is emptied at once,
in these cases:

- its tables pass `SESSION_MIB`, 8 MiB;
- the next declaration is not strictly later in file order than the last
  one checked in the session (`d <= sess_last`), for example when namespace
  order goes back or a worker takes part of another worker's range;
- the level tables pass their bound, because values hold level ids;
- the previous declaration failed (reject, decline, cancellation or panic)
  or met a Bool or Nat constructor that was not declared yet.

A session only moves forward, so every fact used in a declaration D' was
found in D' or in an earlier declaration D of the same session. Every
constant a value of D mentions was declared before D, the environment only
grows, and a definition's value never changes, so evaluation and reduction
give the same results in D'. Check-mode inference results carry the
declaration's interned list of universe parameters in their key. Free
variables belong to the session: a binder takes the first variable of its
type that is not in scope, so two binders in scope at once never share one.

Quotient records, inductive groups, and unsafe or partial axioms,
definitions and opaque constants run in a *scratch arena*. The session's
tables are set aside, the declaration starts from empty tables, and
afterwards its tables are emptied and the session's tables come back. A
scratch declaration adds nothing to the session or to the facts kept across
declarations. An inductive check sees its own constants in stages, so a
stuck reduction found there may not hold once all of them are visible.
Unsafe and partial declarations may use constants that safe ones may not.

## Checking

**Inference** is `infer(term, env, ls, check) -> value`. A bound variable's
type is the type of its environment value. Under a binder, the checker
pushes a fresh free variable whose type is the domain (itself a value). For
an application, it whnf's the function's type to a Pi and continues with
the codomain at the argument's thunk; in check mode, it first compares the
argument's type with the domain. A lambda is checked under a fresh variable,
and its type is the lazy `infer` closure. For constants, inference checks
visibility (the declaring index must precede the current declaration, or be
part of it for inductive groups and unsafe recursion), safety and the number
of levels; in check mode, it also verifies that every universe parameter is
declared. Projections follow Lean's `infer_proj`, including the rule about
data out of propositions. They also treat a structure as a proposition when
its inductive type lives in Prop at generic parameters (Arena test
`proj-of-subst-prop`, where the instance is a Prop only through equalities
that are not transitive).

**Definitional equality** follows Lean's `is_def_eq_core`, operating on
values:

- identity, including `(term, env, ls)` identity for unforced thunks and
  closures, with both outcomes cached for the session;
- congruence of closures and thunks: the same term and substitution, with
  equal environment entries wherever the term uses them;
- quick checks: sorts by level equivalence, literals, binders (domains, then
  bodies under a shared fresh variable);
- `whnf_core` with *cheap projections* (the structure of a projection is
  only `whnf_core`'d), then proof irrelevance;
- lazy delta by definitional height: unfold the higher one, and with the
  same head and regular hints compare arguments first (failures cached).
  Nat offsets (`succ`) and literal folding run only when neither side has
  free variables, as in Lean. The free-variable test is exact, so it only
  counts environment entries the term uses;
- projections of the same field: first the structures by lazy delta, then
  their fields (Lean's lazy_delta_proj_reduction); congruence of other
  neutral terms; then full projection reduction and a retry, lambda eta,
  structure eta, string literal expansion (whnf'd, as Pestka does), and
  unit-like types.

**Reduction.** `eval` performs beta and zeta reduction and builds thunks,
looping rather than recursing in tail positions. `whnf_core` handles
projections, iota and quotients, again looping over consecutive head steps,
while `whnf` adds Nat operations on literals (GMP via `num-bigint`) and
delta. Delta unfolds definitions and theorems. Another theorem's proof block
is decoded on demand at the current end of the arena. Iota handles recursor
rules, K-like recursors (the major is replaced by the nullary constructor
when the types agree), structure eta of the major (not for propositions),
and Nat and String literal majors.

**What is not computed** follows Pestka. A call walks its function's lambdas
as (term, environment) pairs and creates a value only for the result. For a
casesOn recognized by its value, only the major premise is reduced before
the selected minor premise is applied to the fields; similarly, a
matcher-like definition over a casesOn evaluates only the major premise and
the chosen alternative. Arguments in proof positions are not compared once
the preceding arguments are equal. Before unfolding, the same applies to
arguments that the definition's body never reads. Binders take the first
variable of their type that is not in scope, allowing a binder opened again
to find its caches. Literal Nat arithmetic in whnf ignores free variables
elsewhere in the value, as Lean's whnf does.

**Names in heavy declarations.** After a declaration has created 1 M values
or performed 10 K unfoldings, inference and definitional equality are also
remembered under *names*. A name represents the substituted, unreduced term
denoted by a value or (term, environment), using an id from a hash-consed
table. The worker keeps that table across declarations until it holds 2 M
names or the level tables are dropped, while the memos keyed by names are
cleared for every declaration. Environment entries unused by the term do
not participate, and closed MAIN terms are leaves. Two values with one name
stand for the same term, so a type or equality established for one also
holds for the other. This is Pestka's identity "value = substituted term",
paid for only where it saves work.

**Declarations.** The checker handles axioms, definitions, theorems (which
require a Prop type), opaques, the quotient package (with each type compared
structurally with the one Lean builds after Eq's shape is checked), and
inductive groups.

**Inductive groups** are checked as Lean's `inductive.cpp` checks them, with
nothing in the record trusted. Gruszka first checks the parameters and
universe of every type, then its nested occurrences. Lean replaces each
`J Ds` (J an earlier inductive, Ds mentioning the group) with an auxiliary
type that copies the constructors of J's mutual group, repeating the process
until no new type appears. Gruszka never builds this auxiliary type: it *is*
the triple (J, levels, Ds), its constructors are J's at those parameters,
and every later check runs on the enlarged group in the restored form used
by the file. Constructor checks then cover the parameters, the universe of
every field, strict positivity and the return type. The resulting facts are
compared with the record's: isRec, isReflexive, numNested, the K flag, large
elimination and the recursor's universe parameters. Finally, the type of
each recursor (`I.rec`, and `I.rec_k` for the auxiliary types) is walked as a
value against the expected telescope (parameters, motives, minor premises
with fields and induction hypotheses, indices, major premise, result) and
compared structurally with the one generated by Lean's kernel (binder names
and infos aside, as `Expr.eqv`; outParam-style annotations consumed, and the
motive universe named as Lean names it). Structurally, each rule must be the
canonical one: lambdas over parameters, motives, minor premises and fields,
followed by the minor premise applied to those fields and to one recursor
call per recursive field. Nested occurrences are merged and matched as
terms, as Lean does, rather than up to definitional equality. Iota only ever
uses a fully applied rule.

**The quotient package.** The names `Quot`, `Quot.mk`, `Quot.lift` and
`Quot.ind` are reserved for the package. A constant with one of those names
that is not the corresponding quotient record causes the file to be
rejected, and each record's type is compared with the one Lean builds after
Eq's shape has been checked. The whole file, including the prelude, is
treated as hostile.

## Checking part of a file

`--only NAMES` (milestone 26) follows Pestka's subset check (Pestka's
`docs/susz.md`, decision `SubsetAdmitsUnchecked`) and produces the same
output. `main.rs` decodes all of INDEX with the susz crate's checked reader
(`susz::index::parse`), scans the name table once for the requested keys
(`Foo.*` means a longer key beginning with Foo's), and declines names that
have no matching key. The declarations belonging to those keys become the
targets. `env::load_part` then uses the reader's iterator to read MAIN one
record at a time, rather than `decode`'s visitor, which cannot stop while
retaining its state. Reading ends at the last target's record. As each
target is encountered, its INDEX entry is matched to its record: the offset
from the start of MAIN, its kind, its proof block (offset from the start of
PROOFS and length), and every requested key naming a name declared by that
record (`canon_decl`). A disagreement is `index invalid`, while a structural
error in the portion read rejects as it would in a full check. Nothing after
that portion is read, so nothing there (the trailer's counts and
the PROOFS fill included) is checked. The iterator path costs about twice as much per
record as the visitor's fast path (late mathlib target: 2.3 s to read 99% of
MAIN, against 1.24 s for a full load). A visitor that read all of MAIN and
dropped everything after the last target would be faster beyond about half
of the file, but it would also encounter and reject errors past that point,
which Pestka does not.

The driver checks only the targets and, before the last target, every safe
inductive block and quotient record. As usual, workers process them in
namespace order. Every other declaration read receives a verdict without a
check: axioms, definitions, theorems and opaque constants are admitted as
stated and counted in the `checked:` line, while unsafe and partial
declarations are skipped and not counted (an unsafe or partial target is
declined). Declarations in both groups still reject when their universe
parameters are named twice. As in a full check, the verdict is the first
failure in file order, so a bad inductive block before a target takes
precedence over the target.
An admitted theorem's block is decoded only if a target unfolds it. Facts
kept across declarations come from checked declarations and, as always, are
stamped and weakening-safe (see Soundness measures).

`tests/only.sh` (in `gates.sh`) runs Pestka's fixtures and a collection of
INDEX lies: Pestka's `indexbad.py` modes, a name sent to a later declaration,
a wrong proof block, unsorted keys, a declaration out of range, a wrong
declaration count, and front coding off by one. It also sweeps over the bad
adversarial vectors. A declaration rejected by a full check is rejected
when requested, and the file's last declaration is never `checked` past an
inductive block, quotient record or duplicate universe parameter that a
full check rejects.

## Soundness measures

- *Declared before* is enforced at every constant lookup and delta step
  (row index against the current declaration), not only for blocks (rule
  P). A forward reference in MAIN is unknown.
- Caches keyed by arena ids live for one session and only move forward in
  file order (see Sessions). Caches keyed by level ids, level lists and
  level substitutions do not depend on any declaration and last until the
  level tables are dropped. A few facts keyed only by MAIN ids or by closed
  names are kept across sessions. The shared table `Shared.checked`, read
  by every worker, holds closed terms checked at ls = 0 in a safe
  declaration, kept with that declaration's level parameters and reused
  only by a declaration whose parameters include them. It also holds the
  lambda body and type codomain of each checked safe definition (milestone
  29), reused only where the declaration's type opens the same domains.
  Each worker also keeps the definitional equalities it found true between
  closed MAIN thunks or closures, and the outcomes of equalities between
  closed names. All of these
  remain valid as the environment grows (weakening). Each is stamped with
  the declaration that produced it and used only when that declaration is
  earlier than the current one (`d < cur_decl`). No fact travels backward
  in file order, whatever order a worker checks declarations in. Unknown
  constants and errors are never cached. A value lives only as long as its
  session or scratch declaration: every value and anything at an id at or
  above MAIN dies with it. `SK_POISON=1` shifts those id spaces at every
  new session and scratch declaration, so a stale id points elsewhere and
  is caught.
- Closedness is checked for every type, value, recursor type and rule. A
  loose bound variable met during evaluation is an error, not a crash.
- Reduction is total on garbage: lookups are bounds checked; a failed
  foreign block or unknown constant only stops that reduction (or declines);
  deep recursion declines at a stack budget; and panics are caught and
  declined. Once a declaration fails, workers on later declarations are
  cancelled. Regardless of the number of workers, the verdict is the
  earliest non-accepted declaration in file order.
- Where the kernel deliberately reduces less than Lean (big literals inside
  open Nat operations), it can only reject, never accept.

## Layout

- `src/env.rs`: loading Susz into columns, constants, known names.
- `src/level.rs`: universe levels.
- `src/tc.rs`: values, eval, whnf, definitional equality, inference,
  declarations.
- `src/induct.rs`: inductive groups, nested inductives, recursors.
- `src/quot.rs`: quotient package.
- `src/show.rs`: printing, for messages and traces.
- `src/main.rs`: CLI (`--only`: INDEX lookup, targets), parallel driver,
  diagnostics.
- `scripts/`: soundness gates (`gates.sh`: small tests, adversarial vectors
  at 1 and 4 workers in file and namespace order; `gates_all.sh`: every
  gate, poisoned corpora and Pestka parity in both orders), test runner, perf
  runner, measurement under the shared lock (`measure.sh`, `withlock.sh`),
  the PGO build (`build-pgo.sh`), adversarial vectors, ndjson pretty
  printer; `tests/only.sh`: subset checks.

## Why Gruszka

Dried pears are a classic susz, a pear has pits inside, and pear trees get
rust.
