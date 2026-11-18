/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acsc
import Azurite.AzFloat.AcscRat
import Azurite.AzFloat.AcscWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `arccsc q` of a rational, plain and with a period

`acscRat`: the special values (`arccsc (±1) = ±π/2`; `|q| < 1` gives `NaN`, including `0`;
`p = 0`), the correctly rounded 53-bit values at exact rationals, agreement with the float
`acsc` at representable arguments, oddness, the directed modes, 20- and 113-bit results, a
200-bit string, the rationals `±(1 + 2^(−200))` next to `±1`, and huge rationals `±2^5000`,
`±3·2^5000`.

`acscRatWithPeriod`: the special values (`NaN` for `|q| < 1`, also for `u = 0`; `±u/4` at `±1`;
`u = 0`; `±u/12` at `±2`, exact or correctly rounded; `p = 0`), the correctly rounded 53-bit
values in degrees, other periods, the directed modes, a 20-bit result, a 200-bit string, and
huge rationals.

References: an independent 1400-bit fixed-point evaluation of `arcsin (1/q)` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acscRatPrecRound (Q q) p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acscRatWithPeriodPrecRound (Q q) u p m
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "1" 53) == ("1.5707963267948966", .lt)
#guard D (T "1" 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (T "-1" 53) == ("-1.5707963267948966", .gt)
#guard D (T "-1" 53 .Floor) == ("-1.5707963267948968", .lt)
#guard D (T "0" 53) == ("NaN", .eq)
#guard D (T "1/2" 53) == ("NaN", .eq)
#guard D (T "-999999/1000000" 53) == ("NaN", .eq)
#guard D (T "3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "3" 53) == ("0.3398369094541219", .lt)
#guard D (T "-3" 53) == ("-0.3398369094541219", .gt)
#guard D (T "3/2" 53) == ("0.7297276562269663", .lt)
#guard D (T "-7/5" 53) == ("-0.7956029534845354", .lt)
#guard D (T "22/7" 53) == ("0.3238110152735501", .gt)
#guard D (T "1000001/1000000" 53) == ("1.5693821138217787", .lt)
#guard D (T "-1000001/1000000" 53) == ("-1.5693821138217787", .gt)
#guard D (T "1000000007/3" 53) == ("2.999999979e-9", .gt)
#guard D (T "355/113" 53) == ("0.3239460784201245", .lt)
#guard D (T "2" 53) == ("0.5235987755982989", .gt)
#guard D (T "-2" 53) == ("-0.5235987755982989", .lt)
#guard D (T "3" 53 .Floor) == ("0.3398369094541219", .lt)
#guard D (T "-3/2" 53 .Floor) == ("-0.7297276562269664", .lt)
#guard D (T "3" 53 .Ceiling) == ("0.339836909454122", .gt)
#guard D (T "-3/2" 53 .Ceiling) == ("-0.7297276562269663", .gt)
#guard D (T "3" 20) == ("0.339837", .gt)
#guard D (T "3/2" 113) == ("0.7297276562269663634547966598133207", .gt)

-- agreement with the float `acsc` at representable arguments, oddness
#guard T "2" 53 == acscPrecRound (X "2" 53) 53 .Nearest
#guard T "-3/2" 53 .Floor == acscPrecRound (X "-1.5" 53) 53 .Floor
#guard acscRat (Q "3") 53 == (T "3" 53).1
#guard (T "-22/7" 53 .Floor).1 == -(T "22/7" 53 .Ceiling).1
#guard toString (acscRat (Q "3") 200)
  == "0.339836909454121937096392513391764066388244690332458071431924"

-- rationals next to `±1`, and huge rationals
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def near1 : AzRat := 1 + pw 200
#guard D (acscRatPrecRound near1 53 .Nearest) == ("1.5707963267948966", .lt)
#guard D (acscRatPrecRound (-near1) 53 .Nearest) == ("-1.5707963267948966", .gt)
#guard D (acscRatPrecRound (-near1) 53 .Floor) == ("-1.5707963267948968", .lt)
#guard D (acscRatPrecRound (pw 5000)⁻¹ 53 .Nearest) == ("7.079811261048173e-1506", .lt)
#guard D (acscRatPrecRound (pw 5000)⁻¹ 53 .Ceiling) == ("7.079811261048174e-1506", .gt)
#guard D (acscRatPrecRound (-(pw 5000)⁻¹) 53 .Ceiling) == ("-7.079811261048173e-1506", .gt)
#guard D (acscRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Nearest) == ("2.3599370870160575e-1506", .lt)

-- with a period: special values
#guard D (R "0" 360 53) == ("NaN", .eq)
#guard D (R "1/2" 0 53) == ("NaN", .eq)
#guard D (R "3" 0 53) == ("0.0", .eq)
#guard D (R "-3" 0 53) == ("0.0", .eq)
#guard D (R "3" 360 0) == ("NaN", .eq)
#guard D (R "1" 360 53) == ("9.0e1", .eq)
#guard D (R "-1" 360 53) == ("-9.0e1", .eq)
#guard D (R "2" 360 53) == ("3.0e1", .eq)
#guard D (R "-2" 360 53) == ("-3.0e1", .eq)
#guard D (R "4/2" 7 53) == ("0.5833333333333334", .gt)
#guard D (R "-2" 7 53 .Floor) == ("-0.5833333333333334", .lt)

-- with a period: correctly rounded values
#guard D (R "3" 360 53) == ("19.47122063449069", .gt)
#guard D (R "-3" 360 53) == ("-19.47122063449069", .lt)
#guard D (R "3/2" 360 53) == ("41.810314895778596", .lt)
#guard D (R "-7/5" 360 53) == ("-45.584691402807024", .gt)
#guard D (R "22/7" 360 53) == ("18.55300453502066", .gt)
#guard D (R "1000000007/3" 360 53) == ("1.718873373360356e-7", .gt)
#guard D (R "3" 1 53) == ("0.05408672398469636", .lt)
#guard D (R "3" 7 53) == ("0.37860706789287457", .gt)
#guard D (R "3" 400 53) == ("21.634689593878544", .lt)
#guard D (R "-3" 360 53 .Floor) == ("-19.47122063449069", .lt)
#guard D (R "-3" 360 53 .Ceiling) == ("-19.471220634490688", .gt)
#guard D (R "3" 360 20) == ("19.47122", .gt)
#guard R "3/2" 360 53 == acscWithPeriodPrecRound (X "1.5" 53) 360 53 .Nearest
#guard acscRatWithPeriod (Q "3") 360 53 == (R "3" 360 53).1
#guard toString (acscRatWithPeriod (Q "3") 360 200)
  == "19.4712206344906913692459993399624359630068431009079482881711"
#guard D (acscRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Nearest)
  == ("4.0564330500725343e-1504", .gt)
#guard D (acscRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Floor) == ("4.056433050072534e-1504", .lt)
#guard D (acscRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Nearest)
  == ("-4.0564330500725343e-1504", .lt)
