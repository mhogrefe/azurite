/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosRatWithPeriod
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccos (q) u / (2π)` of a rational

The special values (`|q| > 1` gives `NaN`, also for `u = 0`; `u/4` at `0`; `0` at `1`; `u/2` at
`−1`; `u = 0`; `u/6` at `1/2` and `u/3` at `−1/2`, also for unreduced inputs, exact or
correctly rounded; `p = 0`), the correctly rounded 53-bit values in degrees at exact rationals,
other periods, agreement with the float function at representable arguments, the directed
modes, 20- and 113-bit results, a 200-bit string, and tiny rationals `±2^(−5000)` (values next
to `u/4`).  References: an independent 1400-bit fixed-point evaluation rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acosRatWithPeriodPrecRound (Q q) u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (R "3/2" 360 53) == ("NaN", .eq)
#guard D (R "-22/7" 0 53) == ("NaN", .eq)
#guard D (R "1/3" 0 53) == ("0.0", .eq)
#guard D (R "0" 0 53) == ("0.0", .eq)
#guard D (R "1/3" 360 0) == ("NaN", .eq)
#guard D (R "0" 360 53) == ("9.0e1", .eq)
#guard D (R "0" 7 1) == ("2.0", .gt)
#guard D (R "1" 360 53) == ("0.0", .eq)
#guard D (R "-1" 360 53) == ("1.8e2", .eq)
#guard D (R "1/2" 360 53) == ("6.0e1", .eq)
#guard D (R "-3/6" 360 53) == ("1.2e2", .eq)
#guard D (R "1/2" 7 53) == ("1.1666666666666667", .gt)
#guard D (R "-1/2" 7 53 .Floor) == ("2.333333333333333", .lt)
#guard D (R "2/4" 1 53 .Ceiling) == ("0.16666666666666669", .gt)

-- correctly rounded values at exact rationals
#guard D (R "1/3" 360 53) == ("70.52877936550931", .lt)
#guard D (R "-1/3" 360 53) == ("109.47122063449069", .gt)
#guard D (R "-7/10" 360 53) == ("134.4270040008057", .gt)
#guard D (R "3/4" 360 53) == ("41.409622109270856", .lt)
#guard D (R "-22/23" 360 53) == ("163.0425737058277", .gt)
#guard D (R "355/452" 360 53) == ("38.242475310840675", .lt)
#guard D (R "1/1000000007" 360 53) == ("89.99999994270422", .gt)
#guard D (R "1/3" 1 53) == ("0.19591327601530364", .gt)
#guard D (R "1/3" 7 53) == ("1.3713929321071254", .lt)
#guard D (R "1/3" 400 53) == ("78.36531040612145", .lt)
#guard D (R "-1/3" 360 53 .Floor) == ("109.47122063449068", .lt)
#guard D (R "-1/3" 360 53 .Ceiling) == ("109.47122063449069", .gt)
#guard D (R "1/3" 360 20) == ("70.5288", .gt)
#guard D (R "1/3" 360 113) == ("70.52877936550930863075400066003757", .gt)

-- agreement with the float function at representable arguments
#guard R "3/4" 360 53 == acosWithPeriodPrecRound (X "0.75" 53) 360 53 .Nearest
#guard R "-1/1024" 7 53 .Floor == acosWithPeriodPrecRound (X "-0.0009765625" 53) 7 53 .Floor
#guard acosRatWithPeriod (Q "1/3") 360 53 == (R "1/3" 360 53).1
#guard toString (acosRatWithPeriod (Q "1/3") 360 200) == "70.52877936550930863075400066003756403699\
  31568990920517118289"

-- tiny rationals: next to the float `u/4`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard D (acosRatWithPeriodPrecRound (pw 5000) 360 53 .Nearest) == ("9.0e1", .gt)
#guard D (acosRatWithPeriodPrecRound (pw 5000) 360 53 .Floor) == ("89.99999999999999", .lt)
#guard D (acosRatWithPeriodPrecRound (-(pw 5000)) 360 53 .Nearest) == ("9.0e1", .lt)
#guard D (acosRatWithPeriodPrecRound (-(pw 5000)) 360 53 .Ceiling) == ("90.00000000000001", .gt)
