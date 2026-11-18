/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddMul
import Azurite.AzFloat.AddMulRat
import Azurite.AzFloat.Precision
import Azurite.AzFloat.Shift
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

/-!
# Tests for the fused multiply-add and multiply-subtract with a rational factor

Expected values computed by hand (the exact `x ± y·z`, then one rounding), shown as decimal output.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def A (x y : AzFloat) (z : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  addMulRatPrecRound x y (Q z) p m
private def S (x y : AzFloat) (z : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  subMulRatPrecRound x y (Q z) p m

/-! ## Special values -/

#guard D (A nan one "1/3" 10) == ("NaN", .eq)
#guard D (A one nan "1/3" 10) == ("NaN", .eq)
#guard D (A one (infinity true) "0" 10) == ("NaN", .eq)  -- ∞ · 0
#guard D (A (infinity true) (infinity true) "-1" 10) == ("NaN", .eq)  -- ∞ − ∞
#guard D (S (infinity true) (infinity true) "1" 10) == ("NaN", .eq)  -- ∞ − ∞
#guard D (A one (infinity true) "-2/3" 10) == ("-Infinity", .eq)
#guard D (A one (infinity false) "-2/3" 10) == ("Infinity", .eq)
#guard D (S one (infinity true) "2/3" 10) == ("-Infinity", .eq)
#guard D (A (infinity false) (infinity true) "-1" 10) == ("-Infinity", .eq)
#guard D (A (infinity true) one "1/3" 10) == ("Infinity", .eq)
#guard D (A (infinity true) zero "1/3" 10) == ("Infinity", .eq)
#guard D (A zero zero "1/3" 10) == ("0.0", .eq)
#guard D (A (X "7" 3) zero "5/3" 10) == ("7.0", .eq)
#guard D (A zero (X "3" 2) "1/3" 5) == ("1.0", .eq)
#guard A zero one "-1/3" 5 == addRatPrecRound zero (Q "-1/3") 5 .Nearest
#guard S zero one "1/3" 5 == addRatPrecRound zero (Q "-1/3") 5 .Nearest

/-! ## Agreement with the float–rational addition when `y = 1` -/

#guard A one one "1/3" 5 == addRatPrecRound one (Q "1/3") 5 .Nearest
#guard A (X "-1.25" 4) one "7/9" 20 == addRatPrecRound (X "-1.25" 4) (Q "7/9") 20 .Nearest
#guard S (X "-1.25" 4) one "7/9" 20 .Floor == subRatPrecRound (X "-1.25" 4) (Q "7/9") 20 .Floor
#guard A (X "3" 2) (X "3" 2) "1/3" 5 == addRatPrecRound (X "3" 2) (Q "1") 5 .Nearest

/-! ## Exact results -/

#guard D (A (X "0.5" 3) (X "0.75" 3) "5/3" 10) == ("1.75", .eq)
#guard D (S (X "0.5" 3) (X "0.75" 3) "5/3" 10) == ("-0.75", .eq)
#guard D (A (X "1" 5) (X "-6" 5) "1/3" 5) == ("-1.0", .eq)
#guard D (A (X "1" 5) (X "6" 5) "-1/2" 5) == ("-2.0", .eq)

/-! ## One rounding, not two -/

-- `x = −1`, `y = 1 + 2^-52`, `z = 1 + 2^-52`: `x + y·z = 2^-51 + 2^-104`, which rounds at 53
-- bits to `2^-51` from above; rounding the product first would give `2^-51` as exact (`.eq`).
private def y53 : AzFloat := X "1.0000000000000002" 53
#guard D (A (X "-1" 53) y53 "4503599627370497/4503599627370496" 53)
  == ("4.440892098500626e-16", .lt)
#guard D (S (X "1" 53) y53 "4503599627370497/4503599627370496" 53)
  == ("-4.440892098500626e-16", .gt)
-- rounding tags at 3 bits
#guard D (A (X "1" 3) (X "0.5" 3) "1/4" 3) == ("1.0", .lt)  -- 9/8
#guard D (A (X "1" 3) (X "0.5" 3) "1/2" 3) == ("1.2", .eq)
#guard D (A (X "1" 3) (X "0.75" 3) "1/4" 3) == ("1.2", .gt)  -- 19/16
#guard D (A (X "1" 3) (X "0.5" 3) "1/4" 3 .Up) == ("1.2", .gt)
#guard D (S (X "1" 3) (X "0.5" 3) "1/4" 3) == ("0.9", .eq)
#guard D (S (X "1" 3) (X "0.5" 3) "1/8" 3) == ("1.0", .gt)  -- 15/16
-- default precisions
#guard toString (addMulRat (X "1" 3) (X "2" 10) (Q "3/2")) == "4.0"
#guard toString (subMulRat (X "1" 3) (X "2" 10) (Q "3/2")) == "-2.0"

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


/-! ## Huge exponents

`y = ±m · 2^k` is kept apart from its exponent, so the cost does not depend on `k`: the fused
operation commutes with a common shift of `x` and `y`, agrees with the float–float fused
operation on a dyadic `z`, and a negligible term only decides the comparison. -/

private def hugeK : AzInt := AzInt.ofInt (2 ^ 40)
private def x0 : AzFloat := X "0.3333333333333333" 53
private def y0 : AzFloat := X "0.7142857142857143" 53
private def shiftRes (r : AzFloat × Ordering) (k : AzInt) : AzFloat × Ordering := (r.1 <<< k, r.2)
#guard addMulRatPrecRound (x0 <<< hugeK) (y0 <<< hugeK) (Q "3/11") 53 .Nearest
  == shiftRes (addMulRatPrecRound x0 y0 (Q "3/11") 53 .Nearest) hugeK
#guard subMulRatPrecRound (x0 <<< (-hugeK)) (y0 <<< (-hugeK)) (Q "3/11") 53 .Floor
  == shiftRes (subMulRatPrecRound x0 y0 (Q "3/11") 53 .Floor) (-hugeK)
#guard addMulRatPrecRound x0 (y0 <<< hugeK) (Q "3/8") 53 .Nearest
  == addMulPrecRound x0 (y0 <<< hugeK) (X "0.375" 2) 53 .Nearest
#guard addMulRatPrecRound x0 (y0 <<< (-hugeK)) (Q "-3/8") 53 .Ceiling
  == addMulPrecRound x0 (y0 <<< (-hugeK)) (X "-0.375" 2) 53 .Ceiling
-- `x` exactly representable, `y·z` negligible: the result is `x`, the comparison sees the sign
#guard D (addMulRatPrecRound (X "1" 53) (y0 <<< (-hugeK)) (Q "3/11") 53 .Nearest) == ("1.0", .lt)
#guard D (subMulRatPrecRound (X "1" 53) (y0 <<< (-hugeK)) (Q "3/11") 53 .Nearest) == ("1.0", .gt)
-- `x` negligible against a huge `y·z` with exactly representable product
#guard addMulRatPrecRound (X "1" 53) ((X "11" 53) <<< hugeK) (Q "3/11") 53 .Nearest
  == ((X "3" 53) <<< hugeK, .lt)
