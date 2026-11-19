-- Source of tests/adv/{good,bad}_m41_trap_*.ndjson (milestone 41): synthetic
-- conversion traps (Lake project Traps, Lean v4.35.0, lake env lean4export
-- MODULE -- DECL, one declaration per vector). s1: Sum.lean (s1good, s1bad,
-- s1goodR), SumSimp.lean (s1simp); s2: Arr.lean; s3: KProof.lean; s4: Proj.lean.
import Lean
open Lean Meta Elab Tactic

/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

/-- `g n a = a + 2^n`, by 2^n unit steps (no literal shortcut applies to the
recursion itself). -/
noncomputable def g (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a + 1) (fun _ ih a => ih (ih a)) n

/-- 2^19 unit steps; value 524288. -/
noncomputable def slow : Nat := g 19 0
