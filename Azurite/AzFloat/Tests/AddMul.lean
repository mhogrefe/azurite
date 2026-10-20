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
import Azurite.AzRat.Parse

/-!
# Tests for the fused multiply-add and multiply-subtract

Expected values computed by hand (the exact `x ± y·z`, then one rounding).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def A (x y z : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  addMulPrecRound x y z p m
private def S (x y z : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  subMulPrecRound x y z p m

/-! ## Special values -/

#guard A nan one one 10 == (nan, .eq)
#guard A one nan one 10 == (nan, .eq)
#guard A one one nan 10 == (nan, .eq)
#guard A one zero (infinity true) 10 == (nan, .eq)          -- 0 · ∞
#guard A (infinity true) one (infinity false) 10 == (nan, .eq) -- ∞ − ∞
#guard S (infinity true) one (infinity true) 10 == (nan, .eq)  -- ∞ − ∞
#guard A (infinity true) one (infinity true) 10 == (infinity true, .eq)
#guard A one (infinity true) negOne 10 == (infinity false, .eq)
#guard S one (infinity true) negOne 10 == (infinity true, .eq)
#guard A (infinity false) zero one 10 == (infinity false, .eq)
#guard A zero zero zero 10 == (zero, .eq)
#guard A one zero (F "7" 3) 10 == (setPrec one 10, .eq)
#guard S zero one one 10 == (-setPrec one 10, .eq)

/-! ## Exact results -/

#guard A (F "1" 5) (F "2" 5) (F "3" 5) 5 == (F "7" 5, .eq)
#guard S (F "1" 5) (F "2" 5) (F "3" 5) 5 == (F "-5" 5, .eq)
#guard A (F "1/2" 3) (F "3/4" 3) (F "5/4" 3) 10 == (F "23/16" 10, .eq)

/-! ## One rounding, not two -/

-- `y = z = 1 + 2^-52`, `x = −(1 + 2^-51)`: `y·z = 1 + 2^-51 + 2^-104`, so `x + y·z = 2^-104`
-- exactly; rounding the product first (to 53 bits) would give `0`.
private def y53 : AzFloat := F "4503599627370497/4503599627370496" 53   -- 1 + 2^-52
private def x53 : AzFloat := F "-2251799813685249/2251799813685248" 53  -- −(1 + 2^-51)
#guard A x53 y53 y53 53 == (setPrec (P (-104)) 53, .eq)
#guard S (-x53) y53 y53 53 == (-setPrec (P (-104)) 53, .eq)
#guard (x53 + y53 * y53) == zero
-- the rounding tag reports the direction
#guard A (F "1" 3) (F "1" 3) (F "1/8" 3) 3 == (F "1" 3, .lt)     -- 9/8 → 1 at 3 bits
#guard A (F "1" 3) (F "1" 3) (F "1/4" 3) 3 == (F "5/4" 3, .eq)
#guard A (F "1" 3) (F "1" 3) (F "3/16" 3) 3 == (F "5/4" 3, .gt)  -- 19/16 → 5/4
#guard A (F "1" 3) (F "1" 3) (F "1/8" 3) 3 .Up == (F "5/4" 3, .gt)
#guard S (F "1" 3) (F "1" 3) (F "1/8" 3) 3 == (F "7/8" 3, .eq)
#guard S (F "1" 3) (F "1" 3) (F "1/16" 3) 3 == (F "1" 3, .gt)    -- 15/16 → 1 (3 bits: 7/8 or 1)
-- default precisions
#guard addMul (F "1" 3) (F "2" 10) (F "3" 5) == F "7" 10
#guard subMul (F "1" 3) (F "2" 10) (F "3" 5) == F "-5" 10

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
