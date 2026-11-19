-- Source of tests/adv/{good,bad}_m48_*.ndjson (milestone 48): two applications
-- of the same regular definition whose arguments differ at length while
-- unfolding decides (dovetail_*), and an `ite` coming to a constant without
-- arguments on the other side (lookahead_*). Built with Lean v4.35.0 (lean -o
-- M48.olean M48.lean), exported one declaration per vector (olean-export M48
-- -c DECL -o FILE); without skipKernelTC Lean gives the same verdicts.
--   good_m48_dovetail_false     goodDoveFalse    (false && A) && B, CFSG Batch27581.p2
--   bad_m48_dovetail_true       badDoveTrue      the same under true: the arguments decide
--   good_m48_dovetail_pick      goodDovePick     the differing argument is not used
--   bad_m48_dovetail_pick       badDovePick
--   bad_m48_dovetail_pick_slow  badDovePickSlow  both ways say false
--   good_m48_dovetail_same      goodDoveSame     equal arguments, shown slowly
--   good_m48_lookahead_const    goodLookConst    CFSG Batch27011.optI_eq
--   bad_m48_lookahead_const     badLookConst
--   good_m48_pad_env            goodPadEnv       a loop's closure against the same closure written
--                                                with the predicate inline (CFSG HNSchreier
--                                                orbitTreeCheck_certificate); before, one nested
--                                                comparison a step: declined at a 16 MiB stack
--   bad_m48_pad_env             badPadEnv
--   good_m48_pad_env_reads      goodPadEnvReads  the inline term reads a binder: compared as before
--   bad_m48_pad_env_reads       badPadEnvReads
--   good_m48_proj_shape         goodProjShape    projections of a stuck application, same field
--   bad_m48_proj_shape          badProjShape     fields 1 and 2 of one value: the shape decides
--                                                before the arguments (CFSG HNSchreier.matG_sU)
--   bad_m48_proj_shape_args     badProjShapeArgs
--   good_m48_nat_open_fold      goodNatOpenFold  an open side against a Nat operation on literals:
--                                                the operation is folded (CFSG TripleCoverSuz.gen_of_le)
--   bad_m48_nat_open_fold       badNatOpenFold
--   bad_m48_nat_open_shift      badNatOpenShift  `x + 7 = 2` against `3^12000 <<< 297 = 0`
--                                                (m48 before: past 2 GB, unfolding the shift)
-- (the pad_env vectors: Lean's own check ran past 500 s and was stopped; their
-- verdicts follow from computing the loops, as Gruszka m47 gives them)
import Lean
open Lean Meta Elab Tactic

/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

def m48fold (n : Nat) (k : Nat) : Nat := (List.range 400).foldl (fun acc i => acc + i * n + k) 0
def m48pick (x _y : Nat) : Nat := x
def m48cA : List Nat := List.range 300
def m48cB : List Nat := (List.range 300).reverse

set_option debug.skipKernelTC true in
theorem goodDoveFalse (n : Nat) : ((false && Nat.beq (m48fold n 0) 1) && true) = ((false && Nat.beq (m48fold n 1) 1) && true) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badDoveTrue (n : Nat) : ((true && Nat.beq (m48fold n 0) 1) && true) = ((true && Nat.beq (m48fold n 1) 1) && true) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem goodDovePick (n : Nat) : m48pick 0 (m48fold n 0) = m48pick 0 (m48fold n 1) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badDovePick (n : Nat) : m48pick 0 (m48fold n 0) = m48pick 1 (m48fold n 0) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badDovePickSlow (n : Nat) : m48pick (m48fold n 0) 0 = m48pick (m48fold n 1) 0 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem goodDoveSame (n : Nat) : m48pick (m48fold n 0) 5 = m48pick (m48fold n 0 + 0) 5 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem goodLookConst : (if true = true then m48cA else m48cB) = m48cA := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badLookConst : (if true = true then m48cA else m48cB) = m48cB := by unchecked_rfl

def m48allInK (lo hi : Nat) (p : Nat → Bool) : Bool := Nat.allTR (hi - lo) (fun k _ => p (lo + k))

set_option debug.skipKernelTC true in
theorem goodPadEnv (w : Nat) (g : Nat → Nat → Bool) : m48allInK 0 100000 (fun i => g w i) = decide (Nat.allTR (100000 - 0) (fun k _ => (fun i => g w i) (0 + k)) = true) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badPadEnv (w : Nat) (g : Nat → Nat → Bool) : m48allInK 0 2000 (fun i => g w i) = decide (Nat.allTR (2000 - 0) (fun k _ => (fun i => g w i) (1 + k)) = true) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem goodPadEnvReads (w : Nat) (g : Nat → Nat → Bool) : m48allInK 0 2000 (fun i => g w i) = decide (Nat.allTR (2000 - 0) (fun k _ => (fun _i => g w k) (0 + k)) = true) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badPadEnvReads (w : Nat) (g : Nat → Nat → Bool) : m48allInK 0 2000 (fun i => g w i) = decide (Nat.allTR (2000 - 0) (fun k _ => (fun _i => g w (k + 1)) (0 + k)) = true) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem goodProjShape (n : Nat) (f : Nat → Nat × Nat) : (f (m48fold n 0)).1 = (f (m48fold n 0 + 0)).1 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badProjShape (n : Nat) (f : Nat → Nat × Nat) : (f (m48fold n 0)).1 = (f (m48fold n 0)).2 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badProjShapeArgs (n : Nat) (f : Nat → Nat × Nat) : (f (m48fold n 0)).1 = (f (m48fold n 1)).1 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem goodNatOpenFold (x : Nat) : x * 0 + 23 = 3 ^ 12000 >>> 19015 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badNatOpenFold (x : Nat) : x * 0 + 23 = 3 ^ 12000 >>> 19014 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badNatOpenShift (x : Nat) : (x + 7 = 2) = ((3 ^ 12000 <<< 297) = 0) := by unchecked_rfl
