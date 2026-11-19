import Traps.Common
set_option debug.skipKernelTC true
noncomputable def f (i : Nat) : Nat := g 19 i
noncomputable def arr : Array Nat := #[f 0, f 1]
theorem s2good : arr[0]! = f 0 := by unchecked_rfl
theorem s2bad : arr[0]! = f 1 := by unchecked_rfl
-- f wrapped so that its definitional height exceeds the getElem! chain
noncomputable def t0 (i : Nat) : Nat := g 19 i
noncomputable def t1 (i : Nat) : Nat := t0 i
noncomputable def t2 (i : Nat) : Nat := t1 i
noncomputable def t3 (i : Nat) : Nat := t2 i
noncomputable def t4 (i : Nat) : Nat := t3 i
noncomputable def t5 (i : Nat) : Nat := t4 i
noncomputable def t6 (i : Nat) : Nat := t5 i
noncomputable def t7 (i : Nat) : Nat := t6 i
noncomputable def t8 (i : Nat) : Nat := t7 i
noncomputable def t9 (i : Nat) : Nat := t8 i
noncomputable def t10 (i : Nat) : Nat := t9 i
noncomputable def t11 (i : Nat) : Nat := t10 i
noncomputable def t12 (i : Nat) : Nat := t11 i
noncomputable def t13 (i : Nat) : Nat := t12 i
noncomputable def t14 (i : Nat) : Nat := t13 i
noncomputable def t15 (i : Nat) : Nat := t14 i
noncomputable def t16 (i : Nat) : Nat := t15 i
noncomputable def t17 (i : Nat) : Nat := t16 i
noncomputable def t18 (i : Nat) : Nat := t17 i
noncomputable def t19 (i : Nat) : Nat := t18 i
noncomputable def ft (i : Nat) : Nat := t19 i
noncomputable def arrT : Array Nat := #[ft 0, ft 1]
theorem s2tall : arrT[0]! = ft 0 := by unchecked_rfl
theorem s2tallbad : arrT[0]! = ft 1 := by unchecked_rfl
