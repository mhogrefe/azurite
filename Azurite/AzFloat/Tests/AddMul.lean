/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddMul
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Precision
import Azurite.AzFloat.Shift
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

/-!
# Tests for the fused multiply-add and multiply-subtract

Expected values computed by hand (the exact `x ± y·z`, then one rounding), shown as decimal output.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def A (x y z : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  addMulPrecRound x y z p m
private def S (x y z : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  subMulPrecRound x y z p m

/-! ## Special values -/

#guard D (A nan one one 10) == ("NaN", .eq)
#guard D (A one nan one 10) == ("NaN", .eq)
#guard D (A one one nan 10) == ("NaN", .eq)
#guard D (A one zero (infinity true) 10) == ("NaN", .eq)  -- 0 · ∞
#guard D (A (infinity true) one (infinity false) 10) == ("NaN", .eq)  -- ∞ − ∞
#guard D (S (infinity true) one (infinity true) 10) == ("NaN", .eq)  -- ∞ − ∞
#guard D (A (infinity true) one (infinity true) 10) == ("Infinity", .eq)
#guard D (A one (infinity true) negOne 10) == ("-Infinity", .eq)
#guard D (S one (infinity true) negOne 10) == ("Infinity", .eq)
#guard D (A (infinity false) zero one 10) == ("-Infinity", .eq)
#guard D (A zero zero zero 10) == ("0.0", .eq)
#guard D (A one zero (X "7" 3) 10) == ("1.0", .eq)
#guard D (S zero one one 10) == ("-1.0", .eq)

/-! ## Exact results -/

#guard D (A (X "1" 5) (X "2" 5) (X "3" 5) 5) == ("7.0", .eq)
#guard D (S (X "1" 5) (X "2" 5) (X "3" 5) 5) == ("-5.0", .eq)
#guard D (A (X "0.5" 3) (X "0.75" 3) (X "1.25" 3) 10) == ("1.438", .eq)

/-! ## One rounding, not two -/

-- `y = z = 1 + 2^-52`, `x = −(1 + 2^-51)`: `y·z = 1 + 2^-51 + 2^-104`, so `x + y·z = 2^-104`
-- exactly; rounding the product first (to 53 bits) would give `0`.
private def y53 : AzFloat := X "1.0000000000000002" 53   -- 1 + 2^-52
private def x53 : AzFloat := X "-1.0000000000000004" 53  -- −(1 + 2^-51)
#guard D (A x53 y53 y53 53) == ("4.930380657631324e-32", .eq)
#guard D (S (-x53) y53 y53 53) == ("-4.930380657631324e-32", .eq)
#guard toString (x53 + y53 * y53) == "0.0"
-- the rounding tag reports the direction
#guard D (A (X "1" 3) (X "1" 3) (X "0.125" 3) 3) == ("1.0", .lt)  -- 9/8 → 1 at 3 bits
#guard D (A (X "1" 3) (X "1" 3) (X "0.25" 3) 3) == ("1.2", .eq)
#guard D (A (X "1" 3) (X "1" 3) (X "0.1875" 3) 3) == ("1.2", .gt)  -- 19/16 → 5/4
#guard D (A (X "1" 3) (X "1" 3) (X "0.125" 3) 3 .Up) == ("1.2", .gt)
#guard D (S (X "1" 3) (X "1" 3) (X "0.125" 3) 3) == ("0.9", .eq)
#guard D (S (X "1" 3) (X "1" 3) (X "0.0625" 3) 3) == ("1.0", .gt)  -- 15/16 → 1 (3 bits: 7/8 or 1)
-- default precisions
#guard toString (addMul (X "1" 3) (X "2" 10) (X "3" 5)) == "7.0"
#guard toString (subMul (X "1" 3) (X "2" 10) (X "3" 5)) == "-5.0"

/-! ## `Float` versions (IEEE `fma`) -/

private def inf : Float := 1.0 / 0.0
private def eps : Float := 2.0 ^ (-52.0)
#guard addMulFloat64 1.0 2.0 3.0 == 7.0
#guard subMulFloat64 1.0 2.0 3.0 == -5.0
#guard addMulFloat64 (-(1.0 + 2.0 * eps)) (1.0 + eps) (1.0 + eps) == 2.0 ^ (-104.0)
#guard (-(1.0 + 2.0 * eps)) + (1.0 + eps) * (1.0 + eps) == 0.0
#guard subMulFloat64 (1.0 + 2.0 * eps) (1.0 + eps) (1.0 + eps) == -(2.0 ^ (-104.0))
#guard addMulFloat64 0.1 0.2 0.3 == addMulFloat64 0.1 0.3 0.2
#guard (addMulFloat64 1.0 0.0 inf).isNaN
#guard (addMulFloat64 inf 1.0 (-inf)).isNaN
#guard addMulFloat64 inf 0.0 1.0 == inf
#guard addMulFloat64 1.0e308 1.0e308 10.0 == inf
#guard (addMulFloat64 (-3.0) 1.0 3.0).toBits == 0 -- exact zero is +0.0
