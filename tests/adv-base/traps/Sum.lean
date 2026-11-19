import Traps.Common
set_option debug.skipKernelTC true
-- cheap: unfold List.sum/foldr until both sides are `slow + (1 + 0)`
theorem s1good : [slow, 1].sum = slow + (1 + 0) := by unchecked_rfl
theorem s1bad : [slow, 1].sum = slow + (2 + 0) := by unchecked_rfl
-- symmetric orientation
theorem s1goodR : slow + (1 + 0) = [slow, 1].sum := by unchecked_rfl
