/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Agm
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (x y : String) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  agmPrecRound (F x 200) (F y 200) p mode

-- `AGM(1, 2)`: `AGM · 2^52 = 6560803544579530.4454…`
#guard D (A "1" "2" 53 .Nearest) == ("1.4567910310469068", .lt)
#guard D (A "1" "2" 53 .Ceiling) == ("1.456791031046907", .gt)
#guard D (A "2" "1" 53 .Nearest) == ("1.4567910310469068", .lt)
#guard D (A "1" "2" 100 .Nearest) == ("1.456791031046906869186432383265", .lt)
-- `AGM(24, 6)`: `AGM · 2^49 = 7576277008773464.7033…`
#guard D (A "24" "6" 53 .Nearest) == ("13.458171481725616", .gt)
#guard D (A "24" "6" 53 .Floor) == ("13.458171481725614", .lt)
#guard D (A "24" "6" 100 .Nearest) == ("13.45817148172561542076681315698", .gt)
-- homogeneity: `AGM(1, 1/2) = AGM(1, 2)/2`
#guard D (A "1" "1/2" 53 .Nearest) == ("0.7283955155234534", .lt)
-- `AGM(3, 1/8)`: `AGM · 2^52 = 4648093209094003.6849…`
#guard D (A "3" "1/8" 53 .Nearest) == ("1.032084020267999", .gt)
#guard D (A "3" "1/8" 100 .Nearest) == ("1.032084020267998988316355460547", .gt)
-- decimal output
#guard toString (agm (X "1" 60) (X "2" 60) 53) == "1.4567910310469068"
-- `AGM(x, x) = x`, exactly
#guard D (agmPrecRound (X "3" 10) (X "3" 10) 5 .Nearest) == ("3.0", .eq)
#guard D (agmPrecRound (X "1.75" 10) (X "1.75" 10) 2 .Floor) == ("1.5", .lt)
-- special values
#guard D (agmPrecRound zero (X "5" 10) 20 .Nearest) == ("0.0", .eq)
#guard D (agmPrecRound (X "5" 10) zero 20 .Nearest) == ("0.0", .eq)
#guard D (agmPrecRound zero zero 20 .Nearest) == ("0.0", .eq)
#guard (agmPrecRound (X "-1" 10) (X "2" 10) 20 .Nearest).1.isNaN
#guard (agmPrecRound (X "1" 10) (X "-2" 10) 20 .Nearest).1.isNaN
#guard (agmPrecRound nan (X "2" 10) 20 .Nearest).1.isNaN
#guard D (agmPrecRound (infinity true) (X "2" 10) 20 .Nearest) == ("Infinity", .eq)
#guard D (agmPrecRound (X "2" 10) (infinity true) 20 .Nearest) == ("Infinity", .eq)
#guard (agmPrecRound (infinity true) zero 20 .Nearest).1.isNaN
#guard (agmPrecRound (infinity false) (X "2" 10) 20 .Nearest).1.isNaN

/-! ## The rational variants -/

-- `AGM(1, 2)` again, now from rationals and mixed
#guard D (agmRatPrecRound (Q "1") (Q "2") 53 .Nearest) == ("1.4567910310469068", .lt)
#guard D (agmRatPrecRound (Q "2") (Q "1") 53 .Ceiling) == ("1.456791031046907", .gt)
#guard D (agmFloatRatPrecRound (X "1" 10) (Q "2") 53 .Nearest) == ("1.4567910310469068", .lt)
#guard D (agmFloatRatPrecRound (X "2" 10) (Q "1") 53 .Nearest) == ("1.4567910310469068", .lt)
-- non-dyadic rationals: `AGM(1, 1/3) = 0.6239…` is `AGM(3, 1)/3`; check consistency of the three
#guard (agmRatPrecRound (Q "1") (Q "1/3") 60 .Nearest).1
  == (agmFloatRatPrecRound (X "1" 10) (Q "1/3") 60 .Nearest).1
#guard (agmRatPrecRound (Q "1/3") (Q "1") 60 .Floor).1
  == (agmFloatRatPrecRound (X "1" 10) (Q "1/3") 60 .Floor).1
#guard D (agmRatPrecRound (Q "3") (Q "1/8") 53 .Nearest) == ("1.032084020267999", .gt)
#guard D (agmFloatRatPrecRound (X "3" 10) (Q "1/8") 100 .Nearest)
  == ("1.032084020267998988316355460547", .gt)
-- equal arguments are exact
#guard agmRatPrecRound (Q "1/3") (Q "1/3") 53 .Nearest == ofAzRatRound (Q "1/3") 53 .Nearest
#guard D (agmFloatRatPrecRound (X "0.75" 10) (Q "3/4") 2 .Floor) == ("0.8", .eq)
#guard D (agmFloatRatPrecRound (X "1.75" 10) (Q "7/4") 2 .Floor) == ("1.5", .lt)
#guard D (agmFloatRatPrecRound (X "3" 10) (Q "3") 5 .Nearest) == ("3.0", .eq)
-- special values
#guard D (agmRatPrecRound (Q "0") (Q "5") 20 .Nearest) == ("0.0", .eq)
#guard (agmRatPrecRound (Q "-1") (Q "5") 20 .Nearest).1.isNaN
#guard D (agmFloatRatPrecRound zero (Q "5") 20 .Nearest) == ("0.0", .eq)
#guard D (agmFloatRatPrecRound (X "5" 10) (Q "0") 20 .Nearest) == ("0.0", .eq)
#guard (agmFloatRatPrecRound (X "5" 10) (Q "-1") 20 .Nearest).1.isNaN
#guard (agmFloatRatPrecRound (X "-5" 10) (Q "1") 20 .Nearest).1.isNaN
#guard D (agmFloatRatPrecRound (infinity true) (Q "1") 20 .Nearest) == ("Infinity", .eq)
#guard (agmFloatRatPrecRound (infinity true) (Q "0") 20 .Nearest).1.isNaN
#guard (agmFloatRatPrecRound nan (Q "1") 20 .Nearest).1.isNaN
