/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.MulAddMul
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Precision
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

/-!
# Tests for the sums and differences of two products

Expected values computed by hand (the exact `x·y ± z·w`, then one rounding).
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def A (x y z w : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  mulAddMulPrecRound x y z w p m
private def S (x y z w : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  mulSubMulPrecRound x y z w p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## Special values -/

#guard D (A nan one one one 10) == ("NaN", .eq)
#guard D (A one one one nan 10) == ("NaN", .eq)
#guard D (A zero (infinity true) one one 10) == ("NaN", .eq) -- 0 · ∞
#guard D (A one one (infinity false) zero 10) == ("NaN", .eq) -- ∞ · 0
#guard D (A (infinity true) one (infinity true) negOne 10) == ("NaN", .eq) -- ∞ − ∞
#guard D (S (infinity true) one (infinity true) one 10) == ("NaN", .eq) -- ∞ − ∞
#guard D (A (infinity true) one (infinity true) one 10) == ("Infinity", .eq)
#guard D (S (infinity true) one (infinity false) one 10) == ("Infinity", .eq)
#guard D (A (infinity true) negOne one one 10) == ("-Infinity", .eq)
#guard D (A one one (infinity false) negOne 10) == ("Infinity", .eq)
#guard D (A zero zero zero zero 10) == ("0.0", .eq)
#guard D (A one one negOne one 10) == ("0.0", .eq)
#guard D (S one one one one 10) == ("0.0", .eq)
#guard D (A (X "7" 3) one zero (X "5" 3) 10) == ("7.0", .eq)

/-! ## Exact results -/

#guard D (A (X "2" 5) (X "3" 5) (X "4" 5) (X "5" 5) 5) == ("26.0", .eq)
#guard D (S (X "2" 5) (X "3" 5) (X "4" 5) (X "5" 5) 5) == ("-14.0", .eq)
#guard D (A (X "0.5" 3) (X "0.75" 3) (X "1.25" 3) (X "1.5" 3) 10) == ("2.25", .eq)
#guard D (S (X "0.5" 3) (X "0.75" 3) (X "1.25" 3) (X "1.5" 3) 10) == ("-1.5", .eq)

/-! ## One rounding, not two or three -/

-- `x = y = 1 + 2^-52`, `z = 1 + 2^-51`, `w = 1`: `x·y − z·w = 2^-104` exactly; rounding the
-- first product to 53 bits would give `0`.
private def y53 : AzFloat := X "1.0000000000000002" 53   -- 1 + 2^-52
private def z53 : AzFloat := X "1.0000000000000004" 53   -- 1 + 2^-51
#guard D (S y53 y53 z53 one 53) == ("4.930380657631324e-32", .eq)
#guard D (A y53 y53 (-z53) one 53) == ("4.930380657631324e-32", .eq)
#guard toString (y53 * y53 - z53 * one) == "0.0"
-- rounding tags at 3 bits
#guard D (A (X "0.5" 3) (X "1" 3) (X "0.5" 3) (X "1.25" 3) 3) == ("1.0", .lt) -- 9/8
#guard D (A (X "0.5" 3) (X "1" 3) (X "0.75" 3) (X "1" 3) 3) == ("1.2", .eq)
#guard D (A (X "1" 3) (X "1" 3) (X "0.75" 3) (X "0.25" 3) 3) == ("1.2", .gt) -- 19/16
#guard D (A (X "0.5" 3) (X "1" 3) (X "0.5" 3) (X "1.25" 3) 3 .Up) == ("1.2", .gt)
#guard D (S (X "1" 3) (X "1" 3) (X "0.5" 3) (X "0.25" 3) 3) == ("0.9", .eq)
#guard D (S (X "1" 3) (X "1" 3) (X "0.25" 3) (X "0.25" 3) 3) == ("1.0", .gt) -- 15/16
-- default precisions
#guard toString (mulAddMul (X "1" 3) (X "2" 10) (X "3" 5) (X "4" 7)) == "14.0"
#guard toString (mulSubMul (X "1" 3) (X "2" 10) (X "3" 5) (X "4" 7)) == "-1.0e1"

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
