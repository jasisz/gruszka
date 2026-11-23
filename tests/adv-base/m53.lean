-- Source of tests/adv/good_m53_block_literal_region.ndjson (milestone 53
-- review). Built with Lean v4.32.0 (lean -o BlkLit.olean BlkLit.lean),
-- exported with olean-export BlkLit -c t1 -c t2 -c t3.
--   T's proof is a block whose literal 1234567 appears nowhere in MAIN.
--   Under the region gate (SK_REGION_AT=1 SK_REGION_MIN=16
--   SK_REGION_POISON=1, knobs release-da) t1's whnf decodes the block inside
--   a region; the rollback cut `wlits`, where the block's literals were,
--   while `blk` and `block_roots` kept the term: t2's unfolding of `T 2`
--   read literal 9 after its region was rolled back (declined, internal
--   error; without poison the slot is reused by the next literal made).
--   Block literals now live in `blits` (ids from BLIT_BASE).
def R (_ _ : Nat) : Prop := False

theorem T (_ : Nat) : Acc R (2 * 617283 + 1) := Acc.intro 1234567 (fun _ h => False.elim h)

def g (k : Nat) : Nat := (List.replicate 40 k).foldl (· + ·) 0

def f (k : Nat) : Nat := @Acc.rec Nat R (fun _ _ => Nat) (fun x _ _ => g k + x) _ (T k)

theorem t1 : f 1 = 1234607 := by decide +kernel
theorem t2 : f 2 = 1234647 := by decide +kernel
theorem t3 : f 3 = 1234687 := by decide +kernel
