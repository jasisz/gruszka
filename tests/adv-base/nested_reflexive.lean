-- Nested inductives whose isReflexive is decided by an auxiliary
-- constructor: the container's parameter is a field domain, and the
-- nested argument put in for it is a Pi mentioning the block.
-- Exported one type at a time with the 4.35 toolchain:
--   lean -o nested_reflexive.olean nested_reflexive.lean
--   LEAN_PATH=.:$(lean --print-libdir) leanexport nested_reflexive -- <Name>

-- isReflexive = true: List.cons's `head : α` becomes `Nat → TL`
inductive TL where
  | mk : List (Nat → TL) → TL

-- a second, non-reflexive nested field beside the reflexive one
inductive TM where
  | mk : List (Nat → TM) → List TM → TM

-- two levels: Array.mk's `toList : List α` is again nested,
-- List.cons's `head : α` becomes `Bool → TA`
inductive TA where
  | mk : Array (Bool → TA) → TA

-- isReflexive = false: Prod.mk's `fst : α` becomes `Nat → Nat`, a Pi
-- without the block in it
inductive TP where
  | mk : Prod (Nat → Nat) TP → TP

-- Vectors (tests/adv): good_nested_reflexive_list (TL),
-- good_nested_reflexive_beside_plain (TM), good_nested_reflexive_array
-- (TA), good_nested_pi_arg_not_reflexive (TP); the bad twins flip the
-- block's isReflexive on the last line: bad_nested_reflexive_said_false
-- (TL), bad_nested_pi_arg_said_reflexive (TP). The official replay
-- recomputes the flag and accepts both twins; Gruszka and Pestka compare
-- it with the export and reject them.
