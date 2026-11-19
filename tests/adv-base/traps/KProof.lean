import Traps.Common
set_option debug.skipKernelTC true
-- two proofs of `True`; one is a K-like `Eq.rec` whose major `h : slow = 524288`
-- is a hypothesis. Proof irrelevance settles it at once; K-reduction first
-- compares the indices `slow =?= 524288`.
theorem s3good (h : slow = 524288) :
    @Eq True (@Eq.rec Nat slow (fun _ _ => True) True.intro 524288 h) True.intro := by
  unchecked_rfl
-- data control: here the K step is genuinely needed (the value is a Nat)
theorem s3data (h : slow = 524288) :
    @Eq.rec Nat slow (fun _ _ => Nat) 7 524288 h = 7 := by unchecked_rfl
-- BAD: indices differ, Eq.rec is stuck, must be rejected
theorem s3bad (h : slow = 524289) :
    @Eq.rec Nat slow (fun _ _ => Nat) 7 524289 h = 7 := by unchecked_rfl
