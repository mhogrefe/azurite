/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.MulAddMul
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Precision
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse

/-!
# Tests for the sums and differences of two products

Expected values computed by hand (the exact `x·y ± z·w`, then one rounding).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def A (x y z w : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  mulAddMulPrecRound x y z w p m
private def S (x y z w : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  mulSubMulPrecRound x y z w p m

/-! ## Special values -/

#guard A nan one one one 10 == (nan, .eq)
#guard A one one one nan 10 == (nan, .eq)
#guard A zero (infinity true) one one 10 == (nan, .eq)              -- 0 · ∞
#guard A one one (infinity false) zero 10 == (nan, .eq)             -- ∞ · 0
#guard A (infinity true) one (infinity true) negOne 10 == (nan, .eq) -- ∞ − ∞
#guard S (infinity true) one (infinity true) one 10 == (nan, .eq)   -- ∞ − ∞
#guard A (infinity true) one (infinity true) one 10 == (infinity true, .eq)
#guard S (infinity true) one (infinity false) one 10 == (infinity true, .eq)
#guard A (infinity true) negOne one one 10 == (infinity false, .eq)
#guard A one one (infinity false) negOne 10 == (infinity true, .eq)
#guard A zero zero zero zero 10 == (zero, .eq)
#guard A one one negOne one 10 == (zero, .eq)
#guard S one one one one 10 == (zero, .eq)
#guard A (F "7" 3) one zero (F "5" 3) 10 == (setPrec (F "7" 3) 10, .eq)

/-! ## Exact results -/

#guard A (F "2" 5) (F "3" 5) (F "4" 5) (F "5" 5) 5 == (F "26" 5, .eq)
#guard S (F "2" 5) (F "3" 5) (F "4" 5) (F "5" 5) 5 == (F "-14" 5, .eq)
#guard A (F "1/2" 3) (F "3/4" 3) (F "5/4" 3) (F "3/2" 3) 10 == (F "9/4" 10, .eq)
#guard S (F "1/2" 3) (F "3/4" 3) (F "5/4" 3) (F "3/2" 3) 10 == (F "-3/2" 10, .eq)

/-! ## One rounding, not two or three -/

-- `x = y = 1 + 2^-52`, `z = 1 + 2^-51`, `w = 1`: `x·y − z·w = 2^-104` exactly; rounding the
-- first product to 53 bits would give `0`.
private def y53 : AzFloat := F "4503599627370497/4503599627370496" 53   -- 1 + 2^-52
private def z53 : AzFloat := F "2251799813685249/2251799813685248" 53   -- 1 + 2^-51
#guard S y53 y53 z53 one 53 == (setPrec (P (-104)) 53, .eq)
#guard A y53 y53 (-z53) one 53 == (setPrec (P (-104)) 53, .eq)
#guard (y53 * y53 - z53 * one) == zero
-- rounding tags at 3 bits
#guard A (F "1/2" 3) (F "1" 3) (F "1/2" 3) (F "5/4" 3) 3 == (F "1" 3, .lt)      -- 9/8
#guard A (F "1/2" 3) (F "1" 3) (F "3/4" 3) (F "1" 3) 3 == (F "5/4" 3, .eq)
#guard A (F "1" 3) (F "1" 3) (F "3/4" 3) (F "1/4" 3) 3 == (F "5/4" 3, .gt)      -- 19/16
#guard A (F "1/2" 3) (F "1" 3) (F "1/2" 3) (F "5/4" 3) 3 .Up == (F "5/4" 3, .gt)
#guard S (F "1" 3) (F "1" 3) (F "1/2" 3) (F "1/4" 3) 3 == (F "7/8" 3, .eq)
#guard S (F "1" 3) (F "1" 3) (F "1/4" 3) (F "1/4" 3) 3 == (F "1" 3, .gt)        -- 15/16
-- default precisions
#guard mulAddMul (F "1" 3) (F "2" 10) (F "3" 5) (F "4" 7) == F "14" 10
#guard mulSubMul (F "1" 3) (F "2" 10) (F "3" 5) (F "4" 7) == F "-10" 10

/-! ## `Float` versions -/

private def inf : Float := 1.0 / 0.0
private def eps : Float := 2.0 ^ (-52.0)
#guard mulAddMulFloat64 2.0 3.0 4.0 5.0 == 26.0
#guard mulSubMulFloat64 2.0 3.0 4.0 5.0 == -14.0
#guard mulSubMulFloat64 (1.0 + eps) (1.0 + eps) (1.0 + 2.0 * eps) 1.0 == 2.0 ^ (-104.0)
#guard (1.0 + eps) * (1.0 + eps) - (1.0 + 2.0 * eps) * 1.0 == 0.0
#guard mulAddMulFloat64 (1.0 + eps) (1.0 + eps) (-(1.0 + 2.0 * eps)) 1.0 == 2.0 ^ (-104.0)
#guard mulAddMulFloat64 0.1 0.2 0.3 0.4 == mulAddMulFloat64 0.3 0.4 0.2 0.1
#guard (mulAddMulFloat64 0.0 inf 1.0 1.0).isNaN
#guard (mulSubMulFloat64 inf 1.0 inf 1.0).isNaN
#guard mulAddMulFloat64 inf 1.0 inf 1.0 == inf
#guard mulAddMulFloat64 1.0e200 1.0e200 1.0 1.0 == inf
#guard mulSubMulFloat64 1.0e200 1.0e200 1.0e200 1.0e200 == 0.0
#guard (mulSubMulFloat64 3.0 2.0 2.0 3.0).toBits == 0 -- exact zero is +0.0
