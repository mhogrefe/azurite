/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinRatWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsin (q) u / (2π)` of a rational

The special values (`0`; `|q| > 1` gives `NaN`, also for `u = 0`; `u = 0`; `±u/4` at `±1`;
`±u/12` at `±1/2`, also for an unreduced input, exact or correctly rounded; `p = 0`), the
correctly rounded 53-bit values in degrees at exact rationals, other periods, agreement with the
float function at representable arguments, the directed modes, 20- and 113-bit results, a
200-bit string, and the tiny argument `±1/(3·2^1000)`.  References: an independent 1400-bit
fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinRatWithPeriodPrecRound (Q q) u p m

-- special values
#guard R "0" 360 53 == (zero, .eq)
#guard R "0" 360 0 == (zero, .eq)
#guard R "3/2" 360 53 == (nan, .eq)
#guard R "-22/7" 0 53 == (nan, .eq)
#guard R "1/3" 0 53 == (zero, .eq)
#guard R "-1" 0 53 == (zero, .eq)
#guard R "1/3" 360 0 == (nan, .eq)
#guard R "1" 360 53 == (F "90" 53, .eq)
#guard R "-1" 360 53 == (F "-90" 53, .eq)
#guard R "1" 7 1 == (F "2" 1, .gt)
#guard R "1/2" 360 53 == (F "30" 53, .eq)
#guard R "-3/6" 360 53 == (F "-30" 53, .eq)
#guard R "1/2" 7 53 == (F "5254199565265579/9007199254740992" 53, .gt)
#guard R "-1/2" 7 53 .Ceiling == (F "-2627099782632789/4503599627370496" 53, .gt)
#guard R "1/2" 1 53 .Ceiling == (F "3002399751580331/36028797018963968" 53, .gt)

-- correctly rounded values at exact rationals
#guard R "1/3" 360 53 == (F "42817666989229/2199023255552" 53, .gt)
#guard R "-7/10" 360 53 == (F "-6252544958225503/140737488355328" 53, .gt)
#guard R "3/4" 360 53 == (F "854810967822185/17592186044416" 53, .gt)
#guard R "-22/23" 360 53 == (F "-5139914183183555/70368744177664" 53, .gt)
#guard R "999999/1000000" 360 53 == (F "6327485103946847/70368744177664" 53, .gt)
#guard R "1/1000000007" 360 53 == (F "4329146670215481/75557863725914323419136" 53, .lt)
#guard R "355/452" 360 53 == (F "3642112014120581/70368744177664" 53, .gt)
#guard R "1/3" 1 53 == (F "7794718399461421/144115188075855872" 53, .lt)
#guard R "1/3" 7 53 == (F "852547324941093/2251799813685248" 53, .gt)
#guard R "1/3" 400 53 == (F "6089623749579235/281474976710656" 53, .lt)
#guard R "1/3" 360 53 .Floor == (F "5480661374621311/281474976710656" 53, .lt)
#guard R "1/3" 360 53 .Ceiling == (F "42817666989229/2199023255552" 53, .gt)
#guard R "1/3" 360 20 == (F "638033/32768" 20, .gt)
#guard R "1/3" 360 113
  == (F "3159386179134516561978826335221339/162259276829213363391578010288128" 113, .gt)

-- agreement with the float function at representable arguments
#guard R "3/4" 360 53 == asinWithPeriodPrecRound (F "3/4" 53) 360 53 .Nearest
#guard R "-1/1024" 7 53 .Floor == asinWithPeriodPrecRound (F "-1/1024" 53) 7 53 .Floor
#guard asinRatWithPeriod (Q "1/3") 360 53 == (R "1/3" 360 53).1
#guard (toString (asinRatWithPeriod (Q "1/3") 360 200)).startsWith
  "19.47122063449069136924599933996243596300684310090794828"

-- tiny arguments (`±1/(3·2^1000)`)
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard asinRatWithPeriodPrecRound tinyQ 360 53 .Nearest
    == ((F "2687888034010621" 53) <<< AzInt.ofInt (-1047), .lt)
#guard (asinRatWithPeriodPrecRound (-tinyQ) 360 53 .Floor).2 == .lt
