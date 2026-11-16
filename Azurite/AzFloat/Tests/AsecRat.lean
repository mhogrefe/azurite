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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asecRatPrecRound (Q q) p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  asecRatWithPeriodPrecRound (Q q) u p m
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard T "1" 53 == (zero, .eq)
#guard T "1" 0 == (zero, .eq)
#guard T "-1" 53 == (piN, .lt)
#guard T "-1" 53 .Ceiling == (piC, .gt)
#guard T "0" 53 == (nan, .eq)
#guard T "1/2" 53 == (nan, .eq)
#guard T "-999999/1000000" 53 == (nan, .eq)
#guard T "3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "3" 53 == (F "1385937093311029/1125899906842624" 53, .gt)
#guard T "-3" 53 == (F "8604727130812765/4503599627370496" 53, .gt)
#guard T "3/2" 53 == (F "3787836551362729/4503599627370496" 53, .lt)
#guard T "-7/5" 53 == (F "2664328729219065/1125899906842624" 53, .gt)
#guard T "22/7" 53 == (F "2807961292152009/2251799813685248" 53, .lt)
#guard T "1000001/1000000" 53 == (F "6521906195206097/4611686018427387904" 53, .gt)
#guard T "-1000001/1000000" 53 == (F "3535526613759531/1125899906842624" 53, .lt)
#guard T "1000000007/3" 53 == (F "7074237738517641/4503599627370496" 53, .lt)
#guard T "355/113" 53 == (F "2807657156983717/2251799813685248" 53, .lt)
#guard T "3" 53 .Floor == (F "5543748373244115/4503599627370496" 53, .lt)
#guard T "-3/2" 53 .Floor == (F "5180319476347075/2251799813685248" 53, .lt)
#guard T "3" 53 .Ceiling == (F "1385937093311029/1125899906842624" 53, .gt)
#guard T "-3/2" 53 .Ceiling == (F "1295079869086769/562949953421312" 53, .gt)
#guard T "3" 20 == (F "645377/524288" 20, .lt)
#guard T "3/2" 113
  == (F "8734156432003856210285461333670863/10384593717069655257060992658440192" 113, .lt)

-- agreement with the float `asec` at representable arguments
#guard T "2" 53 == asecPrecRound (F "2" 53) 53 .Nearest
#guard T "-3/2" 53 .Floor == asecPrecRound (F "-3/2" 53) 53 .Floor
#guard asecRat (Q "3") 53 == (T "3" 53).1
#guard (toString (asecRat (Q "3") 200)).startsWith
  "1.23095941734077468213492917824798737571034000935509483"

-- rationals next to `±1`, and a huge rational
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def near1 : AzRat := 1 + pw 200
#guard asecRatPrecRound near1 53 .Nearest
  == (F "6369051672525773/5708990770823839524233143877797980545530986496" 53, .gt)
#guard asecRatPrecRound (-near1) 53 .Nearest == (piN, .lt)
#guard asecRatPrecRound (-near1) 53 .Ceiling == (piC, .gt)
#guard asecRatPrecRound (pw 5000)⁻¹ 53 .Nearest == (h piN (-1), .lt)
#guard asecRatPrecRound (-(pw 5000)⁻¹) 53 .Ceiling == (h piC (-1), .gt)

-- with a period: special values
#guard R "0" 360 53 == (nan, .eq)
#guard R "1/2" 0 53 == (nan, .eq)
#guard R "3" 0 53 == (zero, .eq)
#guard R "3" 360 0 == (nan, .eq)
#guard R "1" 360 53 == (zero, .eq)
#guard R "-1" 360 53 == (F "180" 53, .eq)
#guard R "2" 360 53 == (F "60" 53, .eq)
#guard R "-2" 360 53 == (F "120" 53, .eq)
#guard R "4/2" 7 53 == (F "5254199565265579/4503599627370496" 53, .gt)
#guard R "-2" 7 53 .Floor == (F "2627099782632789/1125899906842624" 53, .lt)

-- with a period: correctly rounded values
#guard R "3" 360 53 == (F "155094426010451/2199023255552" 53, .lt)
#guard R "-3" 360 53 == (F "240729759988909/2199023255552" 53, .gt)
#guard R "3/2" 360 53 == (F "6782095246202283/140737488355328" 53, .gt)
#guard R "-7/5" 360 53 == (F "149076944745807/1099511627776" 53, .gt)
#guard R "22/7" 360 53 == (F "5027635346137851/70368744177664" 53, .lt)
#guard R "1000000007/3" 360 53 == (F "791648370486783/8796093022208" 53, .gt)
#guard R "3" 1 53 == (F "7058519654875637/36028797018963968" 53, .gt)
#guard R "3" 7 53 == (F "3088102349008091/2251799813685248" 53, .lt)
#guard R "3" 400 53 == (F "5514468480371591/70368744177664" 53, .lt)
#guard R "-3" 360 53 .Floor == (F "7703352319645087/70368744177664" 53, .lt)
#guard R "-3" 360 53 .Ceiling == (F "240729759988909/2199023255552" 53, .gt)
#guard R "3" 360 20 == (F "144443/2048" 20, .gt)
#guard R "3/2" 360 53 == asecWithPeriodPrecRound (F "3/2" 53) 360 53 .Nearest
#guard asecRatWithPeriod (Q "3") 360 53 == (R "3" 360 53).1
#guard (toString (asecRatWithPeriod (Q "3") 360 200)).startsWith
  "70.52877936550930863075400066003756403699315689909205171"
#guard asecRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Nearest == (F "90" 53, .gt)
#guard asecRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Floor
  == (F "6333186975989759/70368744177664" 53, .lt)
#guard asecRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Nearest == (F "90" 53, .lt)
#guard asecRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Ceiling
  == (F "6333186975989761/70368744177664" 53, .gt)
