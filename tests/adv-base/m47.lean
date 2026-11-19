-- Source of tests/adv/{good,bad}_m47_*.ndjson (milestone 47): Lean's bound
-- on Nat literals the kernel computes (LEAN_NAT_MAX_SIZE, 128 MiB; counts of
-- Nat.shiftLeft and Nat.pow in 32 bits). Past the bound the kernel refuses
-- the declaration; the operation is never unfolded from its definition.
-- Built with Lean v4.35.0 (lean -o M47.olean M47.lean) and exported one
-- declaration per vector (olean-export M47 -c DECL -o FILE).
--   bad_m47_shift_256mib     badShift256MiB   true, but the result is 256 MiB
--   bad_m47_shift_count      badShiftCount    true, but the count is past 32 bits
--   good_m47_shift_zero      goodShiftZero    0 <<< _ reads no count
--   bad_m47_pow_count        badPowCount      true, but the count is past 32 bits
--   good_m47_shift_2p24      goodShift2p24    a count past 2^24 is computed (CFSG HNSchreier)
--   bad_m47_shift_2p24       badShift2p24
import Lean
open Lean Meta Elab Tactic

/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

set_option debug.skipKernelTC true in
theorem badShift256MiB : (1 <<< 2147483648) % 2 = 0 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badShiftCount : (2 <<< 4294967296) % 2 = 0 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem goodShiftZero : 0 <<< 4294967296 = 0 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badPowCount : 1 ^ 4294967296 = 1 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem goodShift2p24 : (1 <<< 16777217) % 7 = 4 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badShift2p24 : (1 <<< 16777217) % 7 = 5 := by unchecked_rfl
