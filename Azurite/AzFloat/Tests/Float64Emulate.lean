/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Float64Emulate
import Azurite.AzFloat.Add
import Azurite.AzFloat.Div
import Azurite.AzFloat.Mul
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.Ln
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse

/-!
# Tests for the correctly rounded `Float` functions
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def inf : Float := 1.0 / 0.0
private def maxF : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF
private def minSub : Float := Float.ofBits 1
private def bits (f : Float) : UInt64 := f.toBits

/-! ## Subnormal results and the ternary -/

-- `minSub / 2` is a tie between 0 and `minSub`, exact at 53 bits, so to even: 0
#guard emulate₂ divPrecRound minSub 2.0 == 0.0
-- 3 · minSub / 2 is a tie between minSub and 2 · minSub; to even: 2 · minSub
#guard bits (emulate₂ divPrecRound (3.0 * minSub) 2.0) == 2
-- 3 · minSub / 4 = 0.75 · minSub rounds to minSub
#guard bits (emulate₂ divPrecRound (3.0 * minSub) 4.0) == 1
-- `a · b = 2^-1075 · (1 + 2^-53 − 2^-105)`: just above the tie between 0 and `minSub`.  Its
-- 53-bit rounding is exactly `2^-1075` (ternary `.lt`), which a second ties-to-even rounding would
-- send to 0; the ternary sends it up to `minSub`, as IEEE 754 requires.
private def a : Float := (1.0 + 2.0 ^ (-52.0)) * 2.0 ^ (-1000.0)
private def b : Float := (1.0 - 2.0 ^ (-53.0)) * 2.0 ^ (-75.0)
#guard bits (emulate₂ mulPrecRound a b) == 1
#guard emulate₂ mulPrecRound a b == a * b
#guard bits (toFloat64 (mulPrecRound (ofFloat64 a) (ofFloat64 b) 53 .Nearest).1) == 0
#guard bits (emulate₂ mulPrecRound (-a) b) == bits (-minSub)
#guard emulate₂ mulPrecRound (-a) b == -a * b
-- the smallest normal and its neighbors
private def minNormal : Float := Float.ofBits 0x0010000000000000
#guard emulate₂ mulPrecRound minNormal 1.0 == minNormal
#guard bits (emulate₂ divPrecRound minNormal 2.0) == 0x0008000000000000

/-! ## Elementary functions -/

#guard emulate₂ mulPrecRound 0.1 0.2 == 0.1 * 0.2
#guard emulate₂ divPrecRound 1.0 3.0 == 1.0 / 3.0
#guard emulate sqrtPrecRound 2.0 == Float.sqrt 2.0
#guard emulate sqrtPrecRound 1.0e-310 == Float.sqrt 1.0e-310
#guard emulate lnPrecRound 2.0 == Float.ofBits 0x3FE62E42FEFA39EF -- ln 2 correctly rounded
#guard emulate lnPrecRound 1.0 == 0.0
#guard (emulate lnPrecRound (-1.0)).isNaN
#guard emulate lnPrecRound 0.0 == -inf
#guard emulate lnPrecRound inf == inf
#guard emulateRat lnRatPrecRound (Q "2") == Float.ofBits 0x3FE62E42FEFA39EF
#guard emulateRat lnRatPrecRound (Q "1/2") == -Float.ofBits 0x3FE62E42FEFA39EF
#guard emulateRat lnRatPrecRound (Q "1") == 0.0
