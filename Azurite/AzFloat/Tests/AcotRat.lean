/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotRat
import Azurite.AzFloat.Acot
import Azurite.AzFloat.AcotWithPeriod
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccot q` of a rational, plain and with a period

`acotRat`: the special values (`π/2` at `0`, `±π/4` at `±1`, `p = 0`), the correctly rounded
53-bit values at exact rationals on both sides of `1`, the directed modes, 20- and 113-bit
results, agreement with the float `acot`, oddness, a 200-bit string, tiny and huge rationals.

`acotRatWithPeriod`: the special values (`u/4` at `0`; `±u/8` at `±1`; `u = 0`; `p = 0`), the
correctly rounded 53-bit values in degrees, other periods, the directed modes, a 20-bit result,
a 200-bit string, and tiny and huge rationals.

References: an independent 1400-bit fixed-point evaluation of `arctan (1/q)` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acotRatPrecRound (Q q) p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acotRatWithPeriodPrecRound (Q q) u p m
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("1.5707963267948966", .lt)
#guard D (T "0" 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (T "1" 53) == ("0.7853981633974483", .lt)
#guard D (T "1" 53 .Ceiling) == ("0.7853981633974484", .gt)
#guard D (T "-1" 53) == ("-0.7853981633974483", .gt)
#guard D (T "-1" 53 .Floor) == ("-0.7853981633974484", .lt)
#guard D (T "3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "3" 53) == ("0.3217505543966422", .lt)
#guard D (T "-3" 53) == ("-0.3217505543966422", .gt)
#guard D (T "3/2" 53) == ("0.5880026035475675", .lt)
#guard D (T "-7/5" 53) == ("-0.6202494859828215", .lt)
#guard D (T "22/7" 53) == ("0.3080527810237764", .gt)
#guard D (T "1/3" 53) == ("1.2490457723982544", .gt)
#guard D (T "-2/7" 53) == ("-1.2924966677897853", .lt)
#guard D (T "1/1000000" 53) == ("1.5707953267948966", .gt)
#guard D (T "1000000007/3" 53) == ("2.999999979e-9", .gt)
#guard D (T "355/113" 53) == ("0.3081690465737699", .gt)
#guard D (T "2" 53) == ("0.4636476090008061", .lt)
#guard D (T "-1/2" 53) == ("-1.1071487177940904", .gt)
#guard D (T "3" 53 .Floor) == ("0.3217505543966422", .lt)
#guard D (T "-3/2" 53 .Floor) == ("-0.5880026035475676", .lt)
#guard D (T "3" 53 .Ceiling) == ("0.32175055439664224", .gt)
#guard D (T "-3/2" 53 .Ceiling) == ("-0.5880026035475675", .gt)
#guard D (T "3" 20) == ("0.3217506", .gt)
#guard D (T "3/2" 113) == ("0.5880026035475675512456110806250855", .gt)

-- agreement with the float `acot` at representable arguments, oddness
#guard T "2" 53 == acotPrecRound (X "2" 53) 53 .Nearest
#guard T "-3/2" 53 .Floor == acotPrecRound (X "-1.5" 53) 53 .Floor
#guard T "1/4" 53 .Ceiling == acotPrecRound (X "0.25" 53) 53 .Ceiling
#guard acotRat (Q "3") 53 == (T "3" 53).1
#guard (T "-22/7" 53 .Floor).1 == -(T "22/7" 53 .Ceiling).1
#guard toString (acotRat (Q "3") 200) == "0.3217505543966421934014046143586613190207552955576561914\
  32803"

-- tiny and huge rationals
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard D (acotRatPrecRound (pw 5000) 53 .Nearest) == ("1.5707963267948966", .lt)
#guard D (acotRatPrecRound (-(pw 5000)) 53 .Nearest) == ("-1.5707963267948966", .gt)
#guard D (acotRatPrecRound (-(pw 5000)) 53 .Floor) == ("-1.5707963267948968", .lt)
#guard D (acotRatPrecRound (-(pw 5000)) 53 .Ceiling) == ("-1.5707963267948966", .gt)
#guard D (acotRatPrecRound (pw 5000)⁻¹ 53 .Nearest) == ("7.079811261048173e-1506", .gt)
#guard D (acotRatPrecRound (pw 5000)⁻¹ 53 .Floor) == ("7.079811261048172e-1506", .lt)
#guard D (acotRatPrecRound (-(pw 5000)⁻¹) 53 .Floor) == ("-7.079811261048173e-1506", .lt)
#guard D (acotRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Nearest) == ("2.3599370870160575e-1506", .lt)

-- with a period: special values
#guard D (R "0" 360 53) == ("9.0e1", .eq)
#guard D (R "0" 0 53) == ("0.0", .eq)
#guard D (R "0" 7 1) == ("2.0", .gt)
#guard D (R "3" 0 53) == ("0.0", .eq)
#guard D (R "-1/3" 0 53) == ("0.0", .eq)
#guard D (R "3" 360 0) == ("NaN", .eq)
#guard D (R "1" 360 53) == ("45.0", .eq)
#guard D (R "-1" 360 53) == ("-45.0", .eq)
#guard D (R "3/3" 7 53) == ("0.875", .eq)
#guard D (R "-1" 7 1 .Ceiling) == ("-0.5", .gt)

-- with a period: correctly rounded values
#guard D (R "3" 360 53) == ("18.43494882292201", .lt)
#guard D (R "-3" 360 53) == ("-18.43494882292201", .gt)
#guard D (R "3/2" 360 53) == ("33.690067525979785", .lt)
#guard D (R "-7/5" 360 53) == ("-35.53767779197438", .gt)
#guard D (R "22/7" 360 53) == ("17.650124219930124", .gt)
#guard D (R "1000000007/3" 360 53) == ("1.718873373360356e-7", .gt)
#guard D (R "1/3" 360 53) == ("71.56505117707799", .gt)
#guard D (R "-2/7" 360 53) == ("-74.05460409907714", .gt)
#guard D (R "2" 360 53) == ("26.56505117707799", .gt)
#guard D (R "3" 1 53) == ("0.05120819117478336", .lt)
#guard D (R "3" 7 53) == ("0.3584573382234835", .lt)
#guard D (R "3" 400 53) == ("20.483276469913346", .gt)
#guard D (R "-3" 360 53 .Floor) == ("-18.434948822922014", .lt)
#guard D (R "-3" 360 53 .Ceiling) == ("-18.43494882292201", .gt)
#guard D (R "3" 360 20) == ("18.43494", .lt)
#guard R "3/2" 360 53 == acotWithPeriodPrecRound (X "1.5" 53) 360 53 .Nearest
#guard acotRatWithPeriod (Q "3") 360 53 == (R "3" 360 53).1
#guard toString (acotRatWithPeriod (Q "3") 360 200) == "18.4349488229220106484278062795467053287957\
  8570035477897201398"
#guard D (acotRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Nearest) ==
  ("4.0564330500725343e-1504", .gt)
#guard D (acotRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Floor) == ("4.056433050072534e-1504", .lt)
#guard D (acotRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Nearest) ==
  ("-4.0564330500725343e-1504", .lt)
#guard D (acotRatWithPeriodPrecRound (pw 5000) 360 53 .Nearest) == ("9.0e1", .gt)
#guard D (acotRatWithPeriodPrecRound (pw 5000) 360 53 .Floor) == ("89.99999999999999", .lt)
#guard D (acotRatWithPeriodPrecRound (-(pw 5000)) 360 53 .Floor) == ("-9.0e1", .lt)
