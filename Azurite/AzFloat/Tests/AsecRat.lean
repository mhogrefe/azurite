/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asec
import Azurite.AzFloat.AsecRat
import Azurite.AzFloat.AsecWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `arcsec q` of a rational, plain and with a period

`asecRat`: the special values (`arcsec 1 = 0`; `arcsec (−1) = π`; `|q| < 1` gives `NaN`,
including `0`; `p = 0`), the correctly rounded 53-bit values at exact rationals, agreement with
the float `asec` at representable arguments, the directed modes, 20- and 113-bit results, a
200-bit string, the rationals `±(1 + 2^(−200))` next to `±1`, and a huge rational (next to
`π/2`).

`asecRatWithPeriod`: the special values (`NaN` for `|q| < 1`, also for `u = 0`; `0` at `1`;
`u/2` at `−1`; `u = 0`; `u/6` at `2` and `u/3` at `−2`, exact or correctly rounded; `p = 0`),
the correctly rounded 53-bit values in degrees, other periods, the directed modes, a 20-bit
result, a 200-bit string, and huge rationals `±2^5000` (values next to `u/4`).

References: an independent 1400-bit fixed-point evaluation of `arccos (1/q)` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asecRatPrecRound (Q q) p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  asecRatWithPeriodPrecRound (Q q) u p m
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "1" 53) == ("0.0", .eq)
#guard D (T "1" 0) == ("0.0", .eq)
#guard D (T "-1" 53) == ("3.141592653589793", .lt)
#guard D (T "-1" 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (T "0" 53) == ("NaN", .eq)
#guard D (T "1/2" 53) == ("NaN", .eq)
#guard D (T "-999999/1000000" 53) == ("NaN", .eq)
#guard D (T "3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "3" 53) == ("1.2309594173407747", .gt)
#guard D (T "-3" 53) == ("1.9106332362490186", .gt)
#guard D (T "3/2" 53) == ("0.8410686705679302", .lt)
#guard D (T "-7/5" 53) == ("2.366399280279432", .gt)
#guard D (T "22/7" 53) == ("1.2469853115213465", .lt)
#guard D (T "1000001/1000000" 53) == ("0.0014142129731178241", .gt)
#guard D (T "-1000001/1000000" 53) == ("3.1401784406166753", .lt)
#guard D (T "1000000007/3" 53) == ("1.5707963237948965", .lt)
#guard D (T "355/113" 53) == ("1.246850248374772", .lt)
#guard D (T "3" 53 .Floor) == ("1.2309594173407745", .lt)
#guard D (T "-3/2" 53 .Floor) == ("2.3005239830218627", .lt)
#guard D (T "3" 53 .Ceiling) == ("1.2309594173407747", .gt)
#guard D (T "-3/2" 53 .Ceiling) == ("2.300523983021863", .gt)
#guard D (T "3" 20) == ("1.230959", .lt)
#guard D (T "3/2" 113) == ("0.8410686705679302557765250318264307", .lt)

-- agreement with the float `asec` at representable arguments
#guard T "2" 53 == asecPrecRound (X "2" 53) 53 .Nearest
#guard T "-3/2" 53 .Floor == asecPrecRound (X "-1.5" 53) 53 .Floor
#guard asecRat (Q "3") 53 == (T "3" 53).1
#guard toString (asecRat (Q "3") 200)
  == "1.230959417340774682134929178247987375710340009355094839055549"

-- rationals next to `±1`, and a huge rational
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def near1 : AzRat := 1 + pw 200
#guard D (asecRatPrecRound near1 53 .Nearest) == ("1.1156177909894717e-30", .gt)
#guard D (asecRatPrecRound (-near1) 53 .Nearest) == ("3.141592653589793", .lt)
#guard D (asecRatPrecRound (-near1) 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (asecRatPrecRound (pw 5000)⁻¹ 53 .Nearest) == ("1.5707963267948966", .lt)
#guard D (asecRatPrecRound (-(pw 5000)⁻¹) 53 .Ceiling) == ("1.5707963267948968", .gt)

-- with a period: special values
#guard D (R "0" 360 53) == ("NaN", .eq)
#guard D (R "1/2" 0 53) == ("NaN", .eq)
#guard D (R "3" 0 53) == ("0.0", .eq)
#guard D (R "3" 360 0) == ("NaN", .eq)
#guard D (R "1" 360 53) == ("0.0", .eq)
#guard D (R "-1" 360 53) == ("1.8e2", .eq)
#guard D (R "2" 360 53) == ("6.0e1", .eq)
#guard D (R "-2" 360 53) == ("1.2e2", .eq)
#guard D (R "4/2" 7 53) == ("1.1666666666666667", .gt)
#guard D (R "-2" 7 53 .Floor) == ("2.333333333333333", .lt)

-- with a period: correctly rounded values
#guard D (R "3" 360 53) == ("70.52877936550931", .lt)
#guard D (R "-3" 360 53) == ("109.47122063449069", .gt)
#guard D (R "3/2" 360 53) == ("48.189685104221404", .gt)
#guard D (R "-7/5" 360 53) == ("135.58469140280704", .gt)
#guard D (R "22/7" 360 53) == ("71.44699546497934", .lt)
#guard D (R "1000000007/3" 360 53) == ("89.99999982811266", .gt)
#guard D (R "3" 1 53) == ("0.19591327601530364", .gt)
#guard D (R "3" 7 53) == ("1.3713929321071254", .lt)
#guard D (R "3" 400 53) == ("78.36531040612145", .lt)
#guard D (R "-3" 360 53 .Floor) == ("109.47122063449068", .lt)
#guard D (R "-3" 360 53 .Ceiling) == ("109.47122063449069", .gt)
#guard D (R "3" 360 20) == ("70.5288", .gt)
#guard R "3/2" 360 53 == asecWithPeriodPrecRound (X "1.5" 53) 360 53 .Nearest
#guard asecRatWithPeriod (Q "3") 360 53 == (R "3" 360 53).1
#guard toString (asecRatWithPeriod (Q "3") 360 200)
  == "70.5287793655093086307540006600375640369931568990920517118289"
#guard D (asecRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Nearest) == ("9.0e1", .gt)
#guard D (asecRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Floor) == ("89.99999999999999", .lt)
#guard D (asecRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Nearest) == ("9.0e1", .lt)
#guard D (asecRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Ceiling) == ("90.00000000000001", .gt)
