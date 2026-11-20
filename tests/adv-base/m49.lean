-- Source of tests/adv/{good,bad}_m49_*.ndjson (milestone 49). Built with Lean
-- v4.35.0 (lean -o M49.olean M49.lean), exported one declaration per vector
-- (olean-export M49 -c DECL -o FILE); without skipKernelTC Lean gives the same
-- verdicts (all four in 3.8 s).
--   good_m49_proj_loop    goodProjLoop    `(forIn l s f).1` against `Id.run (do let r <- forIn l s g;
--                                         pure r.1)`, f a constant, g its body written inline, the
--                                         state open: the two loops meet as projections of forIn
--                                         (CFSG KernelRouteP.wordG_treeWord_of); before, the
--                                         projected structures were compared reduced, one loop
--                                         step at a time (past 20 s)
--   bad_m49_proj_loop     badProjLoop
--   good_m49_dove_unfold  goodDoveUnfold  a `dite` on `i < a.size` against the same on a name of a;
--                                         unfolding first unfolded the `dite` out of its budget and
--                                         computed a (6000 pushes) through its major premise
--                                         (CFSG HSLoc.treeElems_getD); before: past 2 GB
--   bad_m49_dove_unfold   badDoveUnfold
import Lean
open Lean Meta Elab Tactic

/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

def m49step (_ : Nat) (s : List Nat × Nat) : Id (ForInStep (List Nat × Nat)) :=
  if 0 < s.2 then ForInStep.yield (s.1 ++ [s.2], s.2 - 1) else ForInStep.done s

set_option debug.skipKernelTC true in
theorem goodProjLoop (k : Nat) : (forIn (List.range' 0 100000) ([], k) m49step).1 =
    Id.run (do
      let r ← forIn (List.range' 0 100000) (([] : List Nat), k) (fun (_ : Nat) (s : List Nat × Nat) =>
        if 0 < s.2 then ForInStep.yield (s.1 ++ [s.2], s.2 - 1) else ForInStep.done s)
      pure r.1) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badProjLoop (k : Nat) : (forIn (List.range' 0 300) ([], k) m49step).1 =
    Id.run (do
      let r ← forIn (List.range' 0 300) (([] : List Nat), k) (fun (_ : Nat) (s : List Nat × Nat) =>
        if 0 < s.2 then ForInStep.yield (s.1 ++ [s.2 + 1], s.2 - 1) else ForInStep.done s)
      pure r.1) := by unchecked_rfl

def m49arr (p : Nat × Nat) : Array Nat := Array.ofFn (n := p.1) (fun i => i.val + p.2)
def m49P : Nat × Nat := Id.run do
  let mut s : Nat × Nat := (0, 0)
  for _ in [0:2000] do
    s := (s.1 + 3, s.2)
  return s
def m49named : Array Nat := m49arr m49P
def m49Q : Nat × Nat := (300, 0)
def m49namedQ : Array Nat := m49arr m49Q

def m49w (a : Array Nat) (i : Nat) (_junk : Nat) : Nat := if h : i < a.size then a[i] else 0

set_option debug.skipKernelTC true in
theorem goodDoveUnfold (i : Nat) : m49w (m49arr (m49P.1, m49P.2)) i 0 = m49w m49named i 1 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badDoveUnfold (i : Nat) : m49w (m49arr (m49Q.1 + 1, m49Q.2)) i 0 = m49w m49namedQ i 1 := by unchecked_rfl
