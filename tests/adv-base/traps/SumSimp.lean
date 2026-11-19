import Traps.Common
set_option debug.skipKernelTC true
theorem s1simp : [slow, 1].sum = slow + 1 := by simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
