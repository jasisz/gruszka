-- Nested occurrences are replaced in the syntax before positivity
-- (Lean's elim_nested_inductive, then check_positivity on the result):
-- a field whose whnf is a nested occurrence that is not in its syntax is
-- rejected. Exported with the 4.35 toolchain:
--   lean -o nested_whnf.olean nested_whnf.lean
--   LEAN_PATH=.:$(lean --print-libdir) leanexport nested_whnf -- M T
--   LEAN_PATH=.:$(lean --print-libdir) leanexport nested_whnf -- TF
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u

inductive L (α : Type u) : Type u where
  | nil : L α
  | cons : α → L α → L α

def M (x : Type) : Type := L x

-- good_nested_occurrence_literal: both fields are the occurrence itself
inductive T : Type where
  | mk : L T → L T → T

-- good_nested_occurrence_under_delta_binder: the occurrence under a
-- binder in an argument of a definition (`id`) that whnf unfolds
inductive TF : Type where
  | mk : id (Nat → L TF) → TF

-- Rewritten from T's export (the second field's domain, in T.mk, the
-- recursor's minor premise and the rule), the elaborator would not keep
-- them:
--   bad_nested_occurrence_revealed_by_whnf: `(fun x => L x) T`, whose
--     whnf is `L T`: the redex is no occurrence, `L T` after whnf is not
--     a type of the block (H01, conformance hunt 2026-11-26)
--   bad_nested_occurrence_revealed_by_delta: `M T`, unfolding to `L T`
--   bad_nested_occurrence_revealed_by_zeta: `let x := T; L x`
--   good_nested_occurrence_under_redex: `(fun x => x) (L T)`, the
--     occurrence in the syntax, replaced before the beta step
