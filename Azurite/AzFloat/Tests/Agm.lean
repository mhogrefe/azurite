/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Agm
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the arithmetic–geometric mean

Reference values (80-digit arithmetic): `AGM(1, 2) = 1.4567910310469068691864323832650819749…`,
`AGM(24, 6) = 13.458171481725615420766813156974399243…` (Gauss's example),
`AGM(1, 1/2) = AGM(1, 2)/2` (homogeneity), `AGM(3, 1/8) = 1.0320840202679989883163554605463546157…`.
At `p` bits a value in `[2^k, 2^(k+1))` is `m / 2^(p−1−k)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (x y : String) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  agmPrecRound (F x 200) (F y 200) p mode

-- `AGM(1, 2)`: `AGM · 2^52 = 6560803544579530.4454…`
#guard A "1" "2" 53 .Nearest == (F "6560803544579530/4503599627370496" 53, .lt)
#guard A "1" "2" 53 .Ceiling == (F "6560803544579531/4503599627370496" 53, .gt)
#guard A "2" "1" 53 .Nearest == (F "6560803544579530/4503599627370496" 53, .lt)
#guard A "1" "2" 100 .Nearest
  == (F "923351012456856332994951627423/633825300114114700748351602688" 100, .lt)
-- `AGM(24, 6)`: `AGM · 2^49 = 7576277008773464.7033…`
#guard A "24" "6" 53 .Nearest == (F "7576277008773465/562949953421312" 53, .gt)
#guard A "24" "6" 53 .Floor == (F "7576277008773464/562949953421312" 53, .lt)
#guard A "24" "6" 100 .Nearest
  == (F "1066266197298994740376158732865/79228162514264337593543950336" 100, .gt)
-- homogeneity: `AGM(1, 1/2) = AGM(1, 2)/2`
#guard A "1" "1/2" 53 .Nearest == (F "6560803544579530/9007199254740992" 53, .lt)
-- `AGM(3, 1/8)`: `AGM · 2^52 = 4648093209094003.6849…`
#guard A "3" "1/8" 53 .Nearest == (F "4648093209094004/4503599627370496" 53, .gt)
#guard A "3" "1/8" 100 .Nearest
  == (F "654160963889346498289348849516/633825300114114700748351602688" 100, .gt)
-- decimal output
#guard toString (agm (F "1" 60) (F "2" 60) 53) == "1.4567910310469068"
-- `AGM(x, x) = x`, exactly
#guard agmPrecRound (F "3" 10) (F "3" 10) 5 .Nearest == (F "3" 5, .eq)
#guard agmPrecRound (F "7/4" 10) (F "7/4" 10) 2 .Floor == (F "3/2" 2, .lt)
-- special values
#guard agmPrecRound zero (F "5" 10) 20 .Nearest == (zero, .eq)
#guard agmPrecRound (F "5" 10) zero 20 .Nearest == (zero, .eq)
#guard agmPrecRound zero zero 20 .Nearest == (zero, .eq)
#guard (agmPrecRound (F "-1" 10) (F "2" 10) 20 .Nearest).1.isNaN
#guard (agmPrecRound (F "1" 10) (F "-2" 10) 20 .Nearest).1.isNaN
#guard (agmPrecRound nan (F "2" 10) 20 .Nearest).1.isNaN
#guard agmPrecRound (infinity true) (F "2" 10) 20 .Nearest == (infinity true, .eq)
#guard agmPrecRound (F "2" 10) (infinity true) 20 .Nearest == (infinity true, .eq)
#guard (agmPrecRound (infinity true) zero 20 .Nearest).1.isNaN
#guard (agmPrecRound (infinity false) (F "2" 10) 20 .Nearest).1.isNaN

/-! ## The rational variants -/

-- `AGM(1, 2)` again, now from rationals and mixed
#guard agmRatPrecRound (Q "1") (Q "2") 53 .Nearest
  == (F "6560803544579530/4503599627370496" 53, .lt)
#guard agmRatPrecRound (Q "2") (Q "1") 53 .Ceiling
  == (F "6560803544579531/4503599627370496" 53, .gt)
#guard agmFloatRatPrecRound (F "1" 10) (Q "2") 53 .Nearest
  == (F "6560803544579530/4503599627370496" 53, .lt)
#guard agmFloatRatPrecRound (F "2" 10) (Q "1") 53 .Nearest
  == (F "6560803544579530/4503599627370496" 53, .lt)
-- non-dyadic rationals: `AGM(1, 1/3) = 0.6239…` is `AGM(3, 1)/3`; check consistency of the three
#guard (agmRatPrecRound (Q "1") (Q "1/3") 60 .Nearest).1
  == (agmFloatRatPrecRound (F "1" 10) (Q "1/3") 60 .Nearest).1
#guard (agmRatPrecRound (Q "1/3") (Q "1") 60 .Floor).1
  == (agmFloatRatPrecRound (F "1" 10) (Q "1/3") 60 .Floor).1
#guard agmRatPrecRound (Q "3") (Q "1/8") 53 .Nearest
  == (F "4648093209094004/4503599627370496" 53, .gt)
#guard agmFloatRatPrecRound (F "3" 10) (Q "1/8") 100 .Nearest
  == (F "654160963889346498289348849516/633825300114114700748351602688" 100, .gt)
-- equal arguments are exact
#guard agmRatPrecRound (Q "1/3") (Q "1/3") 53 .Nearest == ofAzRatRound (Q "1/3") 53 .Nearest
#guard agmFloatRatPrecRound (F "3/4" 10) (Q "3/4") 2 .Floor == (F "3/4" 2, .eq)
#guard agmFloatRatPrecRound (F "7/4" 10) (Q "7/4") 2 .Floor == (F "3/2" 2, .lt)
#guard agmFloatRatPrecRound (F "3" 10) (Q "3") 5 .Nearest == (F "3" 5, .eq)
-- special values
#guard agmRatPrecRound (Q "0") (Q "5") 20 .Nearest == (zero, .eq)
#guard (agmRatPrecRound (Q "-1") (Q "5") 20 .Nearest).1.isNaN
#guard agmFloatRatPrecRound zero (Q "5") 20 .Nearest == (zero, .eq)
#guard agmFloatRatPrecRound (F "5" 10) (Q "0") 20 .Nearest == (zero, .eq)
#guard (agmFloatRatPrecRound (F "5" 10) (Q "-1") 20 .Nearest).1.isNaN
#guard (agmFloatRatPrecRound (F "-5" 10) (Q "1") 20 .Nearest).1.isNaN
#guard agmFloatRatPrecRound (infinity true) (Q "1") 20 .Nearest == (infinity true, .eq)
#guard (agmFloatRatPrecRound (infinity true) (Q "0") 20 .Nearest).1.isNaN
#guard (agmFloatRatPrecRound nan (Q "1") 20 .Nearest).1.isNaN
