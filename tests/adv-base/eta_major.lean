-- Source of tests/adv/{good,bad}_m33_eta_major_*.ndjson: structure eta on a
-- recursor's major premise before it is reduced (lean4#15351, #15371).
-- Built as the Arena builds a leanfile test (Lean v4.34.1, module Test,
-- lake env lean4export Test -- DECL > file), one declaration per vector:
--   good_m33_eta_major_prod_loop     goodProdLoop
--   good_m33_eta_major_and_loop      goodAndLoop
--   good_m33_eta_major_and_var       goodAndVar
--   good_m33_eta_major_nested_aux    goodNestedAux
--   good_m33_eta_major_proj_of_ctor  goodProjCtorMajor
--   bad_m33_eta_major_two_ctors      badBoolVar
--   bad_m33_eta_major_indexed        badIdxVar
--   bad_m33_eta_major_recursive      badRecVar
--   bad_m33_eta_major_and_wrong      badAndWrong
--   bad_m33_eta_major_proj_of_ctor   badProjCtorMajor
import Lean
open Lean Meta Elab Tactic

set_option linter.defProp false

/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

theorem tautext {A B : Prop} (a : A) (b : B) : A = B := propext ⟨fun _ => b, fun _ => a⟩
def True' : Prop := ∀ A : Prop, A → A
def delta : True' → True' := fun z => z (True' → True') id z
def omega : True' := fun _ a => cast (tautext id a) delta
def Omega : True' := delta omega

def loopAcc : Acc (fun _ _ : Nat => False) 0 := Omega _ (Acc.intro 0 fun _ h => h.elim)
noncomputable def loopPair : Nat × Nat :=
  Acc.rec (motive := fun _ _ => Nat × Nat) (fun _ _ _ => (0, 0)) loopAcc

/-! good: eta on the major fires before whnf -/

-- a Type structure whose major has no whnf
set_option debug.skipKernelTC true in
theorem goodProdLoop : Prod.rec (motive := fun _ => Nat) (fun _ _ => 1) loopPair = 1 := by unchecked_rfl

-- And (Prop, eliminates into every sort) whose major has no whnf
set_option debug.skipKernelTC true in
theorem goodAndLoop : And.rec (motive := fun _ => Nat) (fun _ _ => 1) (Omega _ (⟨.intro, .intro⟩ : True ∧ True)) = 1 := by unchecked_rfl

-- And on a variable major
set_option debug.skipKernelTC true in
theorem goodAndVar (P Q : Prop) (A : Type) (f : P → Q → A) (x : P ∧ Q) :
    (And.rec f ⟨x.1, x.2⟩ : A) = And.rec f x := by unchecked_rfl

-- a nested auxiliary recursor: its major is the structure-like `SL Nest`,
-- whose universe count equals the recursor's; it eliminates into every sort
inductive SL (α : Type u) where
  | mk : α → SL α
inductive Nest : Type where
  | nest : SL Nest → Nest
  | other
set_option debug.skipKernelTC true in
theorem goodNestedAux (s : SL Nest) :
    @Nest.rec_1 (fun _ => Nat) (fun _ => Nat) (fun _ _ => 0) 0 (fun _ _ => 3) s = 3 := by unchecked_rfl

/-! bad: eta must not fire; each equation holds only if it does -/

-- two constructors
set_option debug.skipKernelTC true in
theorem badBoolVar (b : Bool) : Bool.rec (motive := fun _ => Nat) 0 1 b = 0 := by unchecked_rfl

-- an indexed family with one constructor
inductive Idx : Nat → Type where
  | mk : Idx 0
set_option debug.skipKernelTC true in
theorem badIdxVar (n : Nat) (i : Idx n) : Idx.rec (motive := fun _ _ => Nat) 5 i = 5 := by unchecked_rfl

-- a recursive type with one constructor
inductive Rc : Type where
  | mk : Rc → Rc
set_option debug.skipKernelTC true in
theorem badRecVar (r : Rc) : Rc.rec (motive := fun _ => Nat) (fun _ _ => 7) r = 7 := by unchecked_rfl

-- eta fires on And, but the minor gives 1, not 2
set_option debug.skipKernelTC true in
theorem badAndWrong (h : True ∧ True) : And.rec (motive := fun _ => Nat) (fun _ _ => 1) h = 2 := by unchecked_rfl

/-! a major that is a projection of a constructor application (as
structural recursion leaves them: `(PProd.mk a b).1`): not itself a
constructor application, so eta comes first -/

/-- `(x, 0).1` as a primitive projection, not `Prod.fst`. -/
elab "projmk% " x:term : term => do
  let x ← Term.elabTerm x none
  let p ← mkAppM ``Prod.mk #[x, mkNatLit 0]
  return .proj ``Prod 0 p

set_option debug.skipKernelTC true in
theorem goodProjCtorMajor (x : Nat × Nat) :
    Prod.rec (motive := fun _ => Nat) (fun a _ => a) (projmk% x) = x.1 := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem badProjCtorMajor (x : Nat × Nat) :
    Prod.rec (motive := fun _ => Nat) (fun a _ => a) (projmk% x) = x.2 := by unchecked_rfl
