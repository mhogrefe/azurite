/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosRatWithPeriod
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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acosRatWithPeriodPrecRound (Q q) u p m

-- special values
#guard R "3/2" 360 53 == (nan, .eq)
#guard R "-22/7" 0 53 == (nan, .eq)
#guard R "1/3" 0 53 == (zero, .eq)
#guard R "0" 0 53 == (zero, .eq)
#guard R "1/3" 360 0 == (nan, .eq)
#guard R "0" 360 53 == (F "90" 53, .eq)
#guard R "0" 7 1 == (F "2" 1, .gt)
#guard R "1" 360 53 == (zero, .eq)
#guard R "-1" 360 53 == (F "180" 53, .eq)
#guard R "1/2" 360 53 == (F "60" 53, .eq)
#guard R "-3/6" 360 53 == (F "120" 53, .eq)
#guard R "1/2" 7 53 == (F "5254199565265579/4503599627370496" 53, .gt)
#guard R "-1/2" 7 53 .Floor == (F "2627099782632789/1125899906842624" 53, .lt)
#guard R "2/4" 1 53 .Ceiling == (F "3002399751580331/18014398509481984" 53, .gt)

-- correctly rounded values at exact rationals
#guard R "1/3" 360 53 == (F "155094426010451/2199023255552" 53, .lt)
#guard R "-1/3" 360 53 == (F "240729759988909/2199023255552" 53, .gt)
#guard R "-7/10" 360 53 == (F "591216215943907/4398046511104" 53, .gt)
#guard R "3/4" 360 53 == (F "728485776175255/17592186044416" 53, .lt)
#guard R "-22/23" 360 53 == (F "2868275289793329/17592186044416" 53, .gt)
#guard R "355/452" 360 53 == (F "2691074961869179/70368744177664" 53, .lt)
#guard R "1/1000000007" 360 53 == (F "791648371494741/8796093022208" 53, .gt)
#guard R "1/3" 1 53 == (F "7058519654875637/36028797018963968" 53, .gt)
#guard R "1/3" 7 53 == (F "3088102349008091/2251799813685248" 53, .lt)
#guard R "1/3" 400 53 == (F "5514468480371591/70368744177664" 53, .lt)
#guard R "-1/3" 360 53 .Floor == (F "7703352319645087/70368744177664" 53, .lt)
#guard R "-1/3" 360 53 .Ceiling == (F "240729759988909/2199023255552" 53, .gt)
#guard R "1/3" 360 20 == (F "144443/2048" 20, .gt)
#guard R "1/3" 360 113
  == (F "5721974367747343071631597295355091/81129638414606681695789005144064" 113, .gt)

-- agreement with the float function at representable arguments
#guard R "3/4" 360 53 == acosWithPeriodPrecRound (F "3/4" 53) 360 53 .Nearest
#guard R "-1/1024" 7 53 .Floor == acosWithPeriodPrecRound (F "-1/1024" 53) 7 53 .Floor
#guard acosRatWithPeriod (Q "1/3") 360 53 == (R "1/3" 360 53).1
#guard (toString (acosRatWithPeriod (Q "1/3") 360 200)).startsWith
  "70.52877936550930863075400066003756403699315689909205171"

-- tiny rationals: next to the float `u/4`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard acosRatWithPeriodPrecRound (pw 5000) 360 53 .Nearest == (F "90" 53, .gt)
#guard acosRatWithPeriodPrecRound (pw 5000) 360 53 .Floor
  == (F "6333186975989759/70368744177664" 53, .lt)
#guard acosRatWithPeriodPrecRound (-(pw 5000)) 360 53 .Nearest == (F "90" 53, .lt)
#guard acosRatWithPeriodPrecRound (-(pw 5000)) 360 53 .Ceiling
  == (F "6333186975989761/70368744177664" 53, .gt)
