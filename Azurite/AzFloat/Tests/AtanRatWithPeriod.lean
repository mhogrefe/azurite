/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanRatWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `arctan (q) u / (2π)` of a rational

The special values (`0` at `q = 0` and for `u = 0`; an eighth of a turn `±u/8` at `q = ±1`,
exact or rounded; `p = 0`), the correctly rounded 53-bit values in degrees (`u = 360`) at the
exact rationals `1/3`, `1/10`, `±22/7`, `−7/5`, `355/113`, `−1/1000`, `10³⁰`, `1 + 10⁻⁶`, other
periods (`1`, `7`, `400`, `2^64 − 1`), agreement with the float function at representable
arguments, the directed modes, 1-, 20- and 113-bit results, a 200-bit string, and the tiny
argument `±1/(3·2^1000)`.  References: an independent 1400-bit fixed-point evaluation rounded
with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanRatWithPeriodPrecRound (Q q) u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (R "0" 360 53) == ("0.0", .eq)
#guard D (R "0" 360 0) == ("0.0", .eq)
#guard D (R "1/3" 0 53) == ("0.0", .eq)
#guard D (R "-1" 0 53) == ("0.0", .eq)
#guard D (R "1/3" 360 0) == ("NaN", .eq)
#guard D (R "1" 360 53) == ("45.0", .eq)
#guard D (R "-1" 360 53) == ("-45.0", .eq)
#guard D (R "1" 1 53) == ("0.125", .eq)
#guard D (R "1" 360 2) == ("5.0e1", .gt)
#guard D (R "-1" 360 2 .Floor) == ("-5.0e1", .lt)

-- correctly rounded values at exact rationals
#guard D (R "1/3" 360 53) == ("18.43494882292201", .lt)
#guard D (R "1/10" 360 53) == ("5.710593137499642", .lt)
#guard D (R "22/7" 360 53) == ("72.34987578006988", .gt)
#guard D (R "-22/7" 360 53) == ("-72.34987578006988", .lt)
#guard D (R "-7/5" 360 53) == ("-54.46232220802562", .lt)
#guard D (R "355/113" 360 53) == ("72.34321425475248", .lt)
#guard D (R "-1/1000" 360 53) == ("-0.05729576041450061", .gt)
#guard D (R "1000000000000000000000000000000" 360 53) == ("9.0e1", .gt)
#guard D (R "1000001/1000000" 360 53) == ("45.00002864787543", .lt)
#guard D (R "1/3" 1 53) == ("0.05120819117478336", .lt)
#guard D (R "1/3" 400 53) == ("20.483276469913346", .gt)
#guard D (R "-1/3" 7 53) == ("-0.3584573382234835", .gt)
#guard D (R "3/4" 18446744073709551615 53) == ("1.8892487941576415e18", .lt)
#guard D (R "1/3" 360 53 .Floor) == ("18.43494882292201", .lt)
#guard D (R "-22/7" 360 53 .Floor) == ("-72.34987578006988", .lt)
#guard D (R "1/3" 360 53 .Ceiling) == ("18.434948822922014", .gt)
#guard D (R "-22/7" 360 53 .Ceiling) == ("-72.34987578006987", .gt)
#guard D (R "1/3" 360 20) == ("18.43494", .lt)
#guard D (R "1/3" 360 1) == ("2.0e1", .lt)
#guard D (R "1/3" 360 113) == ("18.434948822922010648427806279546704", .lt)

-- agreement with the float function at representable arguments
#guard R "1/2" 360 53 == atanWithPeriodPrecRound (X "0.5" 53) 360 53 .Nearest
#guard R "-3" 360 53 == atanWithPeriodPrecRound (X "-3" 53) 360 53 .Nearest
#guard R "1/1024" 7 53 .Floor == atanWithPeriodPrecRound (X "0.0009765625" 53) 7 53 .Floor
#guard R "1000000000000" 360 53 == atanWithPeriodPrecRound (X "1000000000000" 53) 360 53 .Nearest
#guard atanRatWithPeriod (Q "1/3") 360 53 == (R "1/3" 360 53).1
#guard toString (atanRatWithPeriod (Q "1/3") 360 200)
  == "18.43494882292201064842780627954670532879578570035477897201398"

-- tiny arguments (`±1/(3·2^1000)`)
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard D (atanRatWithPeriodPrecRound tinyQ 360 53 .Nearest) == ("1.7824022171113933e-300", .lt)
#guard D (atanRatWithPeriodPrecRound tinyQ 360 53 .Floor) == ("1.7824022171113933e-300", .lt)
#guard D (atanRatWithPeriodPrecRound (-tinyQ) 360 53 .Ceiling) == ("-1.7824022171113933e-300", .gt)
