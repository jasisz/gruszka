import Traps.Common
set_option debug.skipKernelTC true
structure S where
  fn : Nat → Nat
  tag : Nat
-- reducing `gC c` to a constructor evaluates `slow` (decides `slow = c`), then
-- sticks on the free `c`
noncomputable def gC (c : Nat) : S :=
  if slow = c then ⟨fun x => x + c, 0⟩ else ⟨fun x => x + c, 1⟩
noncomputable def gC' (c : Nat) : S := gC c
theorem s4good (c x : Nat) : (gC c).fn x = (gC' c).fn x := by unchecked_rfl
theorem s4bad (c x : Nat) : (gC c).fn x = (gC' c).fn (x + 1) := by unchecked_rfl
-- true propositionally, not definitionally (stuck on `c`): must be rejected
theorem s4stuck (c x : Nat) : (gC c).fn x = x + c := by unchecked_rfl
