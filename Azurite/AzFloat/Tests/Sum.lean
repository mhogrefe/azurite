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
import Azurite.AzFloat.ToString

/-!
# Tests for the correctly rounded sum

Expected values computed by hand (the exact sum, then one rounding), shown as the decimal output
of the result (`D`: the shortest round-tripping decimal and the comparison tag).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def S (xs : List AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  sumPrecRound xs p m

/-! ## Special values -/

#guard D (S [] 10) == ("0.0", .eq)
#guard D (S [zero, zero] 10) == ("0.0", .eq)
#guard D (S [nan, one] 10) == ("NaN", .eq)
#guard D (S [one, infinity true] 10) == ("Infinity", .eq)
#guard D (S [infinity false, zero, one] 10) == ("-Infinity", .eq)
#guard D (S [infinity true, one, infinity false] 10) == ("NaN", .eq)
#guard D (S [one] 3) == ("1.0", .eq)
#guard D (S [F "1/3" 53] 10) == ("0.3335", .gt)

/-! ## Two terms agree with addition -/

#guard S [one, F "1/3" 53] 20 == addPrecRound one (F "1/3" 53) 20 .Nearest
#guard S [F "7/3" 10, F "-5/7" 30] 4 .Floor == addPrecRound (F "7/3" 10) (F "-5/7" 30) 4 .Floor
#guard S [F "7/3" 10, F "-5/7" 30] 4 .Ceiling
  == addPrecRound (F "7/3" 10) (F "-5/7" 30) 4 .Ceiling
#guard S [F "-1" 1, F "1/4" 1] 1 == addPrecRound (F "-1" 1) (F "1/4" 1) 1 .Nearest

/-! ## Exact sums -/

#guard D (S [one, one, one] 2) == ("3.0", .eq)
#guard D (S [one, one, one] 1 .Floor) == ("2.0", .lt)
#guard D (S [one, one, one] 1 .Ceiling) == ("4.0", .gt)
#guard D (S [F "3" 2, F "-1" 1, F "-1" 1, F "-1" 1] 3) == ("0.0", .eq)
-- `Σ_{i<10} 2^-i = 1023/512`, ten bits exactly
#guard D (S ((List.range 10).map fun i => P (-i)) 10) == ("1.998", .eq)
#guard D (S ((List.range 10).map fun i => P (-i)) 5) == ("2.0", .gt)
#guard D (S ((List.range 10).map fun i => P (-i)) 5 .Floor) == ("1.94", .lt)
-- order does not matter
#guard S [F "1/3" 53, F "2/3" 53, F "-1" 53] 53 == S [F "-1" 53, F "1/3" 53, F "2/3" 53] 53

/-! ## A boundary inside the bracket -/

#guard D (S [one, P (-100)] 1) == ("1.0", .lt)
#guard D (S [one, P (-100)] 1 .Ceiling) == ("2.0", .gt)
#guard D (S [one, P (-100)] 1 .Floor) == ("1.0", .lt)
#guard D (S [one, -P (-100)] 1) == ("1.0", .gt)
#guard D (S [one, -P (-100)] 1 .Floor) == ("0.5", .lt)
#guard D (S [one, oneHalf] 1) == ("2.0", .gt)                       -- a tie, to even
#guard D (S [one, oneHalf, P (-200)] 1) == ("2.0", .gt)             -- just above the tie
#guard D (S [one, oneHalf, -P (-200)] 1) == ("1.0", .lt)            -- just below the tie
#guard D (S [one, oneHalf, P (-200), -P (-200)] 1) == ("2.0", .gt)  -- exactly the tie again

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
#guard D (S [one, P (-1000), P (-500), -P (-500)] 1) == ("1.0", .lt)
#guard D (S [one, P (-1000), P (-500), -P (-500), -P (-1000)] 1) == ("1.0", .eq)

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
