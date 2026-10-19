/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sum
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Precision
import Azurite.AzRat.Parse

/-!
# Tests for the correctly rounded sum

Expected values computed by hand (the exact sum, then one rounding).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def S (xs : List AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  sumPrecRound xs p m

/-! ## Special values -/

#guard S [] 10 == (zero, .eq)
#guard S [zero, zero] 10 == (zero, .eq)
#guard S [nan, one] 10 == (nan, .eq)
#guard S [one, infinity true] 10 == (infinity true, .eq)
#guard S [infinity false, zero, one] 10 == (infinity false, .eq)
#guard S [infinity true, one, infinity false] 10 == (nan, .eq)
#guard S [one] 3 == (setPrec one 3, .eq)
#guard S [F "1/3" 53] 10 == setPrecRound (F "1/3" 53) 10 .Nearest

/-! ## Two terms agree with addition -/

#guard S [one, F "1/3" 53] 20 == addPrecRound one (F "1/3" 53) 20 .Nearest
#guard S [F "7/3" 10, F "-5/7" 30] 4 .Floor == addPrecRound (F "7/3" 10) (F "-5/7" 30) 4 .Floor
#guard S [F "7/3" 10, F "-5/7" 30] 4 .Ceiling
  == addPrecRound (F "7/3" 10) (F "-5/7" 30) 4 .Ceiling
#guard S [F "-1" 1, F "1/4" 1] 1 == addPrecRound (F "-1" 1) (F "1/4" 1) 1 .Nearest

/-! ## Exact sums -/

#guard S [one, one, one] 2 == (F "3" 2, .eq)
#guard S [one, one, one] 1 .Floor == (two, .lt)
#guard S [one, one, one] 1 .Ceiling == (F "4" 1, .gt)
#guard S [F "3" 2, F "-1" 1, F "-1" 1, F "-1" 1] 3 == (zero, .eq)
-- `Σ_{i<10} 2^-i = 1023/512`, ten bits exactly
#guard S ((List.range 10).map fun i => P (-i)) 10 == (F "1023/512" 10, .eq)
#guard S ((List.range 10).map fun i => P (-i)) 5 == (setPrec two 5, .gt)
#guard S ((List.range 10).map fun i => P (-i)) 5 .Floor == (F "31/16" 5, .lt)
-- order does not matter
#guard S [F "1/3" 53, F "2/3" 53, F "-1" 53] 53 == S [F "-1" 53, F "1/3" 53, F "2/3" 53] 53

/-! ## A boundary inside the bracket -/

#guard S [one, P (-100)] 1 == (one, .lt)
#guard S [one, P (-100)] 1 .Ceiling == (two, .gt)
#guard S [one, P (-100)] 1 .Floor == (one, .lt)
#guard S [one, -P (-100)] 1 == (one, .gt)
#guard S [one, -P (-100)] 1 .Floor == (oneHalf, .lt)
#guard S [one, oneHalf] 1 == (two, .gt)                       -- a tie, to even
#guard S [one, oneHalf, P (-200)] 1 == (two, .gt)             -- just above the tie
#guard S [one, oneHalf, -P (-200)] 1 == (one, .lt)            -- just below the tie
#guard S [one, oneHalf, P (-200), -P (-200)] 1 == (two, .gt)  -- exactly the tie again

/-! ## Huge exponent gaps: no wide intermediate is ever formed -/

private def big : AzFloat := P 1000000000
private def tiny : AzFloat := P (-1000000000)

#guard S [big, tiny] 2 == (setPrec big 2, .lt)
#guard S [big, tiny] 2 .Ceiling == (F "3/2" 2 <<< (1000000000 : Nat), .gt)
#guard S [big, -tiny] 2 == (setPrec big 2, .gt)
#guard S [big, -tiny] 2 .Floor == (F "3/2" 2 <<< (999999999 : Nat), .lt)
#guard S [big, tiny, -big] 5 == (setPrec tiny 5, .eq)
#guard S [big, -big] 5 == (zero, .eq)
#guard S [big, tiny, -big, -tiny] 5 == (zero, .eq)
#guard S [tiny, big, -big, tiny] 5 == (setPrec (P (-999999999)) 5, .eq)
-- the sign of a cancelling remainder decides a boundary case
#guard S [one, P (-1000), P (-500), -P (-500)] 1 == (one, .lt)
#guard S [one, P (-1000), P (-500), -P (-500), -P (-1000)] 1 == (one, .eq)

/-! ## `sumFloat64` -/

private def inf : Float := 1.0 / 0.0
private def maxF : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF

-- exact sums
#guard sumFloat64 [] == 0.0
#guard sumFloat64 [1.0, 2.0, 3.0] == 6.0
#guard sumFloat64 [0.1, 0.2] == 0.1 + 0.2
#guard sumFloat64 [1.0, -1.0] == 0.0
#guard (sumFloat64 [-0.0]).toBits == 0 -- exact zero is +0.0
-- the native sum loses the small terms; the correctly rounded sum keeps them
#guard sumFloat64 [1.0e16, 1.0, 1.0] == 1.0e16 + 2.0
#guard sumFloat64 [1.0e100, 1.0, -1.0e100] == 1.0
#guard sumFloat64 [1.0, 1.0e-20, -1.0] == 1.0e-20
-- rounding of the exact sum: 1 + 2^-53 + 2^-60 rounds up (above the midpoint)
#guard sumFloat64 [1.0, 2.0 ^ (-53.0), 2.0 ^ (-60.0)] == 1.0 + 2.0 ^ (-52.0)
-- an exact tie rounds to even: 1 + 2^-53 stays 1
#guard sumFloat64 [1.0, 2.0 ^ (-53.0)] == 1.0
-- 1 + 2^-53 + 2^-53 = 1 + 2^-52 exactly
#guard sumFloat64 [1.0, 2.0 ^ (-53.0), 2.0 ^ (-53.0)] == 1.0 + 2.0 ^ (-52.0)
-- special values
#guard (sumFloat64 [1.0, 0.0 / 0.0]).isNaN
#guard (sumFloat64 [inf, -inf]).isNaN
#guard sumFloat64 [inf, 1.0] == inf
#guard sumFloat64 [-inf, 1.0, -inf] == -inf
#guard sumFloat64 [maxF, maxF] == inf
#guard sumFloat64 [maxF, maxF, -maxF] == maxF
-- overflow at the IEEE threshold: maxF + 2^970 is a tie, rounds to even (= 2^1024 = ∞)
#guard sumFloat64 [maxF, 2.0 ^ 970.0] == inf
#guard sumFloat64 [maxF, 2.0 ^ 969.0] == maxF
