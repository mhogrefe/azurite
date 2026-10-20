/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddMulRat
import Azurite.AzFloat.Precision
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse

/-!
# Tests for the fused multiply-add and multiply-subtract with a rational factor

Expected values computed by hand (the exact `x ± y·z`, then one rounding).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def A (x y : AzFloat) (z : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  addMulRatPrecRound x y (Q z) p m
private def S (x y : AzFloat) (z : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  subMulRatPrecRound x y (Q z) p m

/-! ## Special values -/

#guard A nan one "1/3" 10 == (nan, .eq)
#guard A one nan "1/3" 10 == (nan, .eq)
#guard A one (infinity true) "0" 10 == (nan, .eq)                  -- ∞ · 0
#guard A (infinity true) (infinity true) "-1" 10 == (nan, .eq)     -- ∞ − ∞
#guard S (infinity true) (infinity true) "1" 10 == (nan, .eq)      -- ∞ − ∞
#guard A one (infinity true) "-2/3" 10 == (infinity false, .eq)
#guard A one (infinity false) "-2/3" 10 == (infinity true, .eq)
#guard S one (infinity true) "2/3" 10 == (infinity false, .eq)
#guard A (infinity false) (infinity true) "-1" 10 == (infinity false, .eq)
#guard A (infinity true) one "1/3" 10 == (infinity true, .eq)
#guard A (infinity true) zero "1/3" 10 == (infinity true, .eq)
#guard A zero zero "1/3" 10 == (zero, .eq)
#guard A (F "7" 3) zero "5/3" 10 == (setPrec (F "7" 3) 10, .eq)
#guard A zero (F "3" 2) "1/3" 5 == (F "1" 5, .eq)
#guard A zero one "-1/3" 5 == addRatPrecRound zero (Q "-1/3") 5 .Nearest
#guard S zero one "1/3" 5 == addRatPrecRound zero (Q "-1/3") 5 .Nearest

/-! ## Agreement with the float–rational addition when `y = 1` -/

#guard A one one "1/3" 5 == addRatPrecRound one (Q "1/3") 5 .Nearest
#guard A (F "-5/4" 4) one "7/9" 20 == addRatPrecRound (F "-5/4" 4) (Q "7/9") 20 .Nearest
#guard S (F "-5/4" 4) one "7/9" 20 .Floor == subRatPrecRound (F "-5/4" 4) (Q "7/9") 20 .Floor
#guard A (F "3" 2) (F "3" 2) "1/3" 5 == addRatPrecRound (F "3" 2) (Q "1") 5 .Nearest

/-! ## Exact results -/

#guard A (F "1/2" 3) (F "3/4" 3) "5/3" 10 == (F "7/4" 10, .eq)
#guard S (F "1/2" 3) (F "3/4" 3) "5/3" 10 == (F "-3/4" 10, .eq)
#guard A (F "1" 5) (F "-6" 5) "1/3" 5 == (F "-1" 5, .eq)
#guard A (F "1" 5) (F "6" 5) "-1/2" 5 == (F "-2" 5, .eq)

/-! ## One rounding, not two -/

-- `x = −1`, `y = 1 + 2^-52`, `z = 1 + 2^-52`: `x + y·z = 2^-51 + 2^-104`, which rounds at 53
-- bits to `2^-51` from above; rounding the product first would give `2^-51` as exact (`.eq`).
private def y53 : AzFloat := F "4503599627370497/4503599627370496" 53
#guard A (F "-1" 53) y53 "4503599627370497/4503599627370496" 53 == (setPrec (P (-51)) 53, .lt)
#guard S (F "1" 53) y53 "4503599627370497/4503599627370496" 53 == (-setPrec (P (-51)) 53, .gt)
-- rounding tags at 3 bits
#guard A (F "1" 3) (F "1/2" 3) "1/4" 3 == (F "1" 3, .lt)      -- 9/8
#guard A (F "1" 3) (F "1/2" 3) "1/2" 3 == (F "5/4" 3, .eq)
#guard A (F "1" 3) (F "3/4" 3) "1/4" 3 == (F "5/4" 3, .gt)    -- 19/16
#guard A (F "1" 3) (F "1/2" 3) "1/4" 3 .Up == (F "5/4" 3, .gt)
#guard S (F "1" 3) (F "1/2" 3) "1/4" 3 == (F "7/8" 3, .eq)
#guard S (F "1" 3) (F "1/2" 3) "1/8" 3 == (F "1" 3, .gt)      -- 15/16
-- default precisions
#guard addMulRat (F "1" 3) (F "2" 10) (Q "3/2") == F "4" 10
#guard subMulRat (F "1" 3) (F "2" 10) (Q "3/2") == F "-2" 10

/-! ## `Float` versions -/

private def inf : Float := 1.0 / 0.0
private def eps : Float := 2.0 ^ (-52.0)
#guard addMulRatFloat64 1.0 2.0 (Q "3/2") == 4.0
#guard subMulRatFloat64 1.0 2.0 (Q "3/2") == -2.0
#guard addMulRatFloat64 0.0 3.0 (Q "1/3") == 1.0
#guard addMulRatFloat64 1.0 1.0 (Q "1/3") == 1.0 + 1.0 / 3.0 -- 4/3 correctly rounded
#guard addMulRatFloat64 0.0 1.0 (Q "1/10") == 0.1
#guard subMulRatFloat64 0.0 1.0 (Q "1/10") == -0.1
-- one rounding: `−1 + (1 + 2^-52)(1 + 2^-52) = 2^-51 + 2^-104` rounds to `2^-51`
#guard addMulRatFloat64 (-1.0) (1.0 + eps) (Q "4503599627370497/4503599627370496") == 2.0 ^ (-51.0)
-- special values
#guard (addMulRatFloat64 1.0 inf (Q "0")).isNaN
#guard (addMulRatFloat64 inf inf (Q "-1")).isNaN
#guard addMulRatFloat64 1.0 inf (Q "-2/3") == -inf
#guard addMulRatFloat64 (-inf) 2.0 (Q "1/3") == -inf
#guard (addMulRatFloat64 (0.0 / 0.0) 1.0 (Q "1")).isNaN
#guard addMulRatFloat64 1.0e308 1.0e308 (Q "10") == inf
#guard (subMulRatFloat64 1.0 2.0 (Q "1/2")).toBits == 0 -- exact zero is +0.0

