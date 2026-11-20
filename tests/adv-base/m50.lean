-- Source of tests/adv/{good,bad}_m50_*.ndjson (milestone 50). Built with Lean
-- v4.35.0 (lean -o M50.olean M50.lean), exported one declaration per vector
-- (olean-export M50 -c DECL -o FILE); without skipKernelTC Lean gives the same
-- verdicts (all four in 1.1 s).
--   good_m50_nat_open_eta      goodNatOpenEta     `Nat.ble 131072 = fun m => Nat.ble 131072 m`: the left
--                                                 side unfolds to Nat.ble's recursion, so the right one
--                                                 must too; a Nat operation over a large literal and a
--                                                 free variable was never unfolded and the two sides
--                                                 never met (CFSG KernelCensus.Fi22K.T2.walkT2)
--   bad_m50_nat_open_eta       badNatOpenEta
--   good_m50_nat_open_eta_len  goodNatOpenEtaLen  the same over a closed computation, `0 + 4096 *
--                                                 m50L.length`, as in walkT2
--   bad_m50_nat_open_eta_len   badNatOpenEtaLen
import Lean
open Lean Meta Elab Tactic

/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

set_option debug.skipKernelTC true in
theorem goodNatOpenEta : Nat.ble 131072 = fun m => Nat.ble 131072 m := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badNatOpenEta : Nat.ble 131072 = fun m => !(Nat.ble 131072 m) := by unchecked_rfl

def m50L : List Nat := List.replicate 32 7

set_option debug.skipKernelTC true in
theorem goodNatOpenEtaLen : Nat.ble (0 + 4096 * m50L.length) = fun m => Nat.ble (0 + 4096 * m50L.length) m := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badNatOpenEtaLen : Nat.ble (0 + 4096 * m50L.length) = fun m => !(Nat.ble (0 + 4096 * m50L.length) m) := by unchecked_rfl
