/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.MulAddMulRat
import Azurite.AzFloat.Precision
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse

/-!
# Tests for a product plus or minus a product with a rational factor

Expected values computed by hand (the exact `x·y ± z·w`, then one rounding).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def A (x y z : AzFloat) (w : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  mulAddMulRatPrecRound x y z (Q w) p m
private def S (x y z : AzFloat) (w : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  mulSubMulRatPrecRound x y z (Q w) p m

/-! ## Special values -/

#guard A nan one one "1/3" 10 == (nan, .eq)
#guard A one one nan "1/3" 10 == (nan, .eq)
#guard A zero (infinity true) one "1/3" 10 == (nan, .eq)             -- 0 · ∞
#guard A one one (infinity true) "0" 10 == (nan, .eq)                -- ∞ · 0
#guard A (infinity true) one (infinity true) "-1" 10 == (nan, .eq)   -- ∞ − ∞
#guard S (infinity true) one (infinity true) "1" 10 == (nan, .eq)    -- ∞ − ∞
#guard A (infinity true) one (infinity true) "1" 10 == (infinity true, .eq)
#guard S (infinity true) one (infinity false) "1" 10 == (infinity true, .eq)
#guard A (infinity true) negOne one "1/3" 10 == (infinity false, .eq)
#guard A one one (infinity false) "-2/3" 10 == (infinity true, .eq)
#guard A zero zero zero "1/3" 10 == (zero, .eq)
#guard A (F "3" 2) (F "2" 2) (F "-18" 5) "1/3" 10 == (zero, .eq)
#guard S (F "3" 2) (F "2" 2) (F "18" 5) "1/3" 10 == (zero, .eq)
#guard A (F "7" 3) one zero "5/3" 10 == (setPrec (F "7" 3) 10, .eq)

/-! ## Agreement with the simpler operations -/

#guard A one one (F "3" 2) "1/3" 5 == addRatPrecRound one (Q "1") 5 .Nearest
#guard A (F "3" 2) (F "5" 3) one "7/9" 20 == addRatPrecRound (F "15" 4) (Q "7/9") 20 .Nearest
#guard S (F "3" 2) (F "5" 3) one "7/9" 20 .Floor
  == subRatPrecRound (F "15" 4) (Q "7/9") 20 .Floor

/-! ## Exact results -/

#guard A (F "2" 5) (F "3" 5) (F "4" 5) "5/4" 5 == (F "11" 5, .eq)
#guard S (F "2" 5) (F "3" 5) (F "4" 5) "5/4" 5 == (F "1" 5, .eq)
#guard A (F "1/2" 3) (F "3/4" 3) (F "3/4" 3) "5/3" 10 == (F "13/8" 10, .eq)
#guard S (F "1/2" 3) (F "3/4" 3) (F "3/4" 3) "5/3" 10 == (F "-7/8" 10, .eq)

/-! ## One rounding, not two or three -/

-- `x = y = 1 + 2^-52`, `z = −1`, `w = 1 + 2^-51`: `x·y + z·w = 2^-104` exactly; rounding the
-- product first would give `0`.
private def y53 : AzFloat := F "4503599627370497/4503599627370496" 53   -- 1 + 2^-52
#guard A y53 y53 negOne "2251799813685249/2251799813685248" 53 == (setPrec (P (-104)) 53, .eq)
#guard S y53 y53 one "2251799813685249/2251799813685248" 53 == (setPrec (P (-104)) 53, .eq)
-- rounding tags at 3 bits
#guard A (F "1/2" 3) (F "1" 3) (F "1/2" 3) "5/4" 3 == (F "1" 3, .lt)        -- 9/8
#guard A (F "1/2" 3) (F "1" 3) (F "3/4" 3) "1" 3 == (F "5/4" 3, .eq)
#guard A (F "1" 3) (F "1" 3) (F "3/4" 3) "1/4" 3 == (F "5/4" 3, .gt)        -- 19/16
#guard A (F "1/2" 3) (F "1" 3) (F "1/2" 3) "5/4" 3 .Up == (F "5/4" 3, .gt)
#guard S (F "1" 3) (F "1" 3) (F "1/2" 3) "1/4" 3 == (F "7/8" 3, .eq)
#guard S (F "1" 3) (F "1" 3) (F "1/4" 3) "1/4" 3 == (F "1" 3, .gt)          -- 15/16
-- default precisions
#guard mulAddMulRat (F "1" 3) (F "2" 10) (F "3" 5) (Q "4/3") == F "6" 10
#guard mulSubMulRat (F "1" 3) (F "2" 10) (F "3" 5) (Q "4/3") == F "-2" 10

/-! ## `Float` versions -/

private def inf : Float := 1.0 / 0.0
private def eps : Float := 2.0 ^ (-52.0)
#guard mulAddMulRatFloat64 2.0 3.0 4.0 (Q "5/4") == 11.0
#guard mulSubMulRatFloat64 2.0 3.0 4.0 (Q "5/4") == 1.0
#guard mulAddMulRatFloat64 1.0 0.0 1.0 (Q "1/10") == 0.1
#guard mulAddMulRatFloat64 (1.0 + eps) (1.0 + eps) (-1.0) (Q "2251799813685249/2251799813685248")
  == 2.0 ^ (-104.0)
#guard mulSubMulRatFloat64 (1.0 + eps) (1.0 + eps) 1.0 (Q "2251799813685249/2251799813685248")
  == 2.0 ^ (-104.0)
#guard (mulAddMulRatFloat64 0.0 inf 1.0 (Q "1")).isNaN
#guard (mulAddMulRatFloat64 1.0 1.0 inf (Q "0")).isNaN
#guard (mulSubMulRatFloat64 inf 1.0 inf (Q "1")).isNaN
#guard mulAddMulRatFloat64 inf 1.0 inf (Q "1") == inf
#guard mulAddMulRatFloat64 1.0e200 1.0e200 1.0 (Q "1") == inf
#guard (mulSubMulRatFloat64 3.0 2.0 4.0 (Q "3/2")).toBits == 0 -- exact zero is +0.0
