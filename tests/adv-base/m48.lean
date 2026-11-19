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

