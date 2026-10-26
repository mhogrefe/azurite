/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

-- This module is the root of the `AzuriteTests` library: `#guard`-based
-- test suites, kept out of the main `Azurite` library target.
-- Built (and thereby run, since `#guard` checks at elaboration time)
-- via `lake test`.
import Azurite.AzFloat.Tests.Add
import Azurite.AzFloat.Tests.AddMul
import Azurite.AzFloat.Tests.AddMulRat
import Azurite.AzFloat.Tests.AddSubRat
import Azurite.AzFloat.Tests.Agm
import Azurite.AzFloat.Tests.Basic
import Azurite.AzFloat.Tests.Constants
import Azurite.AzFloat.Tests.Div
import Azurite.AzFloat.Tests.DivRat
import Azurite.AzFloat.Tests.Exp
import Azurite.AzFloat.Tests.Exp2
import Azurite.AzFloat.Tests.Exp2M1
import Azurite.AzFloat.Tests.Exp2M1Rat
import Azurite.AzFloat.Tests.Exp2Rat
import Azurite.AzFloat.Tests.ExpConstants
import Azurite.AzFloat.Tests.ExpM1
import Azurite.AzFloat.Tests.ExpM1Rat
import Azurite.AzFloat.Tests.ExpRat
import Azurite.AzFloat.Tests.Float64
import Azurite.AzFloat.Tests.Float64Emulate
import Azurite.AzFloat.Tests.GaussConstant
import Azurite.AzFloat.Tests.Gelfond
import Azurite.AzFloat.Tests.GelfondSchneider
import Azurite.AzFloat.Tests.HexString
import Azurite.AzFloat.Tests.Lemniscate
import Azurite.AzFloat.Tests.Literals
import Azurite.AzFloat.Tests.Ln
import Azurite.AzFloat.Tests.Ln2
import Azurite.AzFloat.Tests.LnP1
import Azurite.AzFloat.Tests.LnRat
import Azurite.AzFloat.Tests.Log10
import Azurite.AzFloat.Tests.Log2
import Azurite.AzFloat.Tests.Log2P1
import Azurite.AzFloat.Tests.Log2Rat
import Azurite.AzFloat.Tests.LogBase
import Azurite.AzFloat.Tests.LogBaseFloat
import Azurite.AzFloat.Tests.LogBaseFloatP1
import Azurite.AzFloat.Tests.LogBaseP1
import Azurite.AzFloat.Tests.LogBasePow2
import Azurite.AzFloat.Tests.LogBasePow2P1
import Azurite.AzFloat.Tests.LogBasePow2Rat
import Azurite.AzFloat.Tests.LogBaseRat
import Azurite.AzFloat.Tests.LogBaseRatBase
import Azurite.AzFloat.Tests.LogBaseRatBaseP1
import Azurite.AzFloat.Tests.LogBaseRatFloat
import Azurite.AzFloat.Tests.LogBaseRatRat
import Azurite.AzFloat.Tests.Mul
import Azurite.AzFloat.Tests.MulAddMul
import Azurite.AzFloat.Tests.MulAddMulRat
import Azurite.AzFloat.Tests.MulRat
import Azurite.AzFloat.Tests.OfString
import Azurite.AzFloat.Tests.Pi
import Azurite.AzFloat.Tests.PiConstants
import Azurite.AzFloat.Tests.PowBase
import Azurite.AzFloat.Tests.PowBaseM1
import Azurite.AzFloat.Tests.PowBaseM1Rat
import Azurite.AzFloat.Tests.PowBaseRat
import Azurite.AzFloat.Tests.Precision
import Azurite.AzFloat.Tests.PrimeConstant
import Azurite.AzFloat.Tests.Product
import Azurite.AzFloat.Tests.ProuhetThueMorse
import Azurite.AzFloat.Tests.Ramanujan
import Azurite.AzFloat.Tests.Recip
import Azurite.AzFloat.Tests.Rem
import Azurite.AzFloat.Tests.RoundToInteger
import Azurite.AzFloat.Tests.Rsqrt
import Azurite.AzFloat.Tests.Sqrt
import Azurite.AzFloat.Tests.SqrtRat
import Azurite.AzFloat.Tests.Sum
import Azurite.AzFloat.Tests.ToString
import Azurite.AzNat.Tests.AtanhSplit
import Azurite.AzNat.Tests.CompareDouble
import Azurite.AzNat.Tests.Conversion
import Azurite.AzNat.Tests.Div
import Azurite.AzNat.Tests.DivNewton
import Azurite.AzNat.Tests.DivRound
import Azurite.AzNat.Tests.ExpSplit
import Azurite.AzNat.Tests.Gcd
import Azurite.AzNat.Tests.GetBits
import Azurite.AzNat.Tests.IsMultipleOfPow2
import Azurite.AzNat.Tests.JacobiSym
import Azurite.AzNat.Tests.LogBase
import Azurite.AzNat.Tests.LogBase2
import Azurite.AzNat.Tests.ModPow2
import Azurite.AzNat.Tests.OfLimbDigits
import Azurite.AzNat.Tests.OfLimbDigitsPow2
import Azurite.AzNat.Tests.RootInt
import Azurite.AzNat.Tests.SchonhageStrassen
import Azurite.AzNat.Tests.ShiftRightNearestTernary
import Azurite.AzNat.Tests.ShiftRightRound
import Azurite.AzNat.Tests.ToomCook
import Azurite.AzNat.Tests.TrailingZeros
import Azurite.AzRat.Tests.FromSci
import Azurite.AzRat.Tests.LogBase
import Azurite.AzRat.Tests.Pow2
import Azurite.AzRat.Tests.ToSci
import Azurite.Sci.Tests.Number
