-- Source of tests/adv/{good,bad}_m41_*.ndjson (milestone 41): conversion
-- order. Built with Lean v4.35.0 (lean -o M41.olean m41.lean) and exported
-- one declaration per vector (olean-export M41 -c DECL -o FILE).
--   good_m41_natwait_sum      goodNatWaitSum
--   bad_m41_natwait_sum       badNatWaitSum
--   good_m41_natwait_congr    goodNatWaitCongr
--   bad_m41_natwait_congr     badNatWaitCongr
--   good_m41_headfirst        goodHeadFirst
--   bad_m41_headfirst         badHeadFirst
--   good_m41_pfirst_k         goodProofFirstK
--   good_m41_pfirst_lvl       goodProofFirstLvl
--   bad_m41_pfirst_type       badProofFirstType
--   bad_m41_pfirst_stuck      badProofFirstStuck
import Lean
open Lean Meta Elab Tactic

/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

/-- A closed number that takes the kernel some thousands of steps. -/
def work (n : Nat) : Nat := (List.range n).foldl (fun a b => (a + b * b) % 1000003) 7

/-! NatFoldWaits: a Nat operation whose operands are not literals waits
while the other side unfolds (CFSG's totalC: `List.sum` against `+`) -/

set_option debug.skipKernelTC true in
theorem goodNatWaitSum : [work 400, 1].sum = work 400 + (1 + 0) := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badNatWaitSum : [work 400, 1].sum = work 400 + (2 + 0) := by unchecked_rfl

-- the same operation on both sides: operands first, the fold after
set_option debug.skipKernelTC true in
theorem goodNatWaitCongr : work 400 + (0 + 1) = Nat.add (work 400) 1 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badNatWaitCongr : work 400 + (0 + 1) = Nat.add (work 401) 1 := by unchecked_rfl

/-! CommonHeadFirst: lazy delta past its budget tries to unfold each side
towards the other's head (CFSG's inv_get: an array literal's entry against
the expensive application it holds) -/

def arr : Array Nat := #[work 400, work 401]

set_option debug.skipKernelTC true in
theorem goodHeadFirst : arr[0]! = work 400 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badHeadFirst : arr[0]! = work 401 := by unchecked_rfl

/-! ProofsComparedBeforeReduced: a recursor into Prop applied up to its
major is a proof, compared by its type before whnf_core (whose K check
would compute the major's type). Gruszka skips proof positions of a
constant's spine, so the proofs are compared here as the arguments of a
primitive projection (`b.1 x`), whose spine is compared position by
position. -/

structure Box (A : Sort u) where
  fn : A → Nat

/-- `b.1 x` with a primitive projection, not `Box.fn`. -/
elab "fnproj% " b:term:max x:term:max : term => do
  let b ← Term.elabTerm b none
  let x ← Term.elabTerm x none
  return .app (.proj ``Box 0 b) x

def L : List Nat := List.range 300

theorem lenMap : (L.map (· + 1)).length = L.length := List.length_map _

set_option debug.skipKernelTC true in
theorem goodProofFirstK (P : Prop) (p q : P) (b : Box P) :
    fnproj% b (Eq.rec (motive := fun _ _ => P) p lenMap : P) = fnproj% b q := by unchecked_rfl

-- the motive's universe is a parameter of the recursor, zero here
set_option debug.skipKernelTC true in
theorem goodProofFirstLvl (c : Bool) (b : Box True) :
    fnproj% b (Bool.rec (motive := fun _ => True) trivial trivial c : True) = fnproj% b trivial := by
  unchecked_rfl

-- recursors into Type (the parameter set to 1) are not proofs: 1 is not 2
set_option debug.skipKernelTC true in
theorem badProofFirstType (b : Box Nat) :
    fnproj% b (Bool.rec (motive := fun _ => Nat) 0 1 true) =
      fnproj% b (Bool.rec (motive := fun _ => Nat) 0 2 true) := by
  unchecked_rfl

-- nor on a stuck major
set_option debug.skipKernelTC true in
theorem badProofFirstStuck (c : Bool) (b : Box Nat) :
    fnproj% b (Bool.rec (motive := fun _ => Nat) 0 1 c) =
      fnproj% b (Bool.rec (motive := fun _ => Nat) 0 2 c) := by
  unchecked_rfl
