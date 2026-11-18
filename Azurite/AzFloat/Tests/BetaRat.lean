/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Beta function of two rationals

The special values (zero arguments, negative integers, `p = 0`), positive rationals
(`B(1/2, 1/2) = π`, `B(1/3, 2/3) = 2π/√3`, `B(1/4, 3/4) = π√2`, `B(3/2, 5/2) = π/16`), the
rational values `B(a, n)` for a small integer `n` (`B(1/3, 1) = 3`, `B(1/3, 2) = 9/4`,
`B(−1/2, 2) = −4` exactly; `n = 64`, `65` on either side of the bound), the exact zeros where
`a + b` is a non-positive integer, negative rationals, other precisions, symmetry, and
agreement with the float function on exactly representable arguments.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def B (a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  betaRatPrecRound (Q a) (Q b) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (B "0" "1/2" 53) == ("Infinity", .eq)
#guard D (B "1/2" "0" 53) == ("Infinity", .eq)
#guard D (B "0" "0" 53) == ("Infinity", .eq)
#guard D (B "0" "-1/2" 0) == ("Infinity", .eq)
#guard D (B "0" "-2" 53) == ("NaN", .eq)
#guard D (B "-1" "1/2" 53) == ("NaN", .eq)
#guard D (B "1/2" "-3" 53) == ("NaN", .eq)
#guard D (B "-2" "1" 53) == ("NaN", .eq)
#guard D (B "1/2" "1/2" 0) == ("NaN", .eq)

-- positive rationals
#guard D (B "1/2" "1/2" 53) == ("3.141592653589793", .lt)
#guard D (B "1/2" "1/2" 53 .Floor) == ("3.141592653589793", .lt)
#guard D (B "1/2" "1/2" 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (B "1/3" "2/3" 53) == ("3.6275987284684357", .lt)
#guard D (B "1/3" "1/3" 53) == ("5.2999162508563495", .lt)
#guard D (B "1/4" "3/4" 53) == ("4.442882938158366", .lt)
#guard D (B "22/7" "1/10" 53) == ("8.611481080687849", .lt)
#guard D (B "3/2" "5/2" 53) == ("0.19634954084936207", .lt)
#guard D (B "100" "200" 53) == ("3.607285449794666e-84", .lt)
#guard D (B "10000000000" "1/2" 53) == ("0.000017724538509276716", .lt)
#guard D (B "1/10000000000" "7/3" 53) == ("9999999998.804817", .lt)

-- `B(a, n)` for a small positive integer `n`
#guard D (B "5/2" "1" 53) == ("0.4", .gt)
#guard D (B "1" "1/4" 53) == ("4.0", .eq)
#guard D (B "1/3" "1" 53) == ("3.0", .eq)
#guard D (B "1/3" "2" 53) == ("2.25", .eq)
#guard D (B "1/3" "3" 53 .Floor) == ("1.9285714285714284", .lt)
#guard D (B "-1/2" "2" 53) == ("-4.0", .eq)
#guard D (B "4" "4" 53) == ("0.007142857142857143", .lt)
#guard D (B "1/3" "64" 53) == ("0.6708993778174422", .lt)
#guard D (B "1/3" "65" 53) == ("0.6674232152380772", .lt)
#guard D (B "-7/3" "3" 53) == ("-1.9285714285714286", .lt)

-- `a + b` a non-positive integer: `B = 0` exactly
#guard D (B "1/3" "-1/3" 53) == ("0.0", .eq)
#guard D (B "-1/3" "-2/3" 53) == ("0.0", .eq)
#guard D (B "-3/2" "1/2" 53) == ("0.0", .eq)
#guard D (B "-7/3" "4/3" 53) == ("0.0", .eq)
#guard D (B "1/3" "-7/3" 53) == ("0.0", .eq)

-- negative rationals
#guard D (B "-1/3" "-1/3" 53) == ("-4.106780435878354", .lt)
#guard D (B "-1/3" "-1/3" 53 .Ceiling) == ("-4.1067804358783535", .gt)
#guard D (B "-3/2" "1/4" 53) == ("2.1850479619101", .gt)
#guard D (B "-7/3" "5/2" 53) == ("-0.31183909865716225", .gt)
#guard D (B "-3/2" "5/2" 53) == ("3.141592653589793", .lt)
#guard D (B "-999/1000" "1/2" 53) == ("500.1916114507184", .lt)
#guard D (B "-201/2" "1/3" 53) == ("0.28778237002795004", .lt)

-- other precisions
#guard D (B "1/3" "2/3" 1) == ("4.0", .gt)
#guard D (B "1/3" "2/3" 20) == ("3.627598", .lt)
#guard D (B "1/3" "2/3" 200)
  == ("3.62759872846843570118815651528431146456813249618548115113977", .gt)
#guard D (B "-1/3" "-1/3" 200 .Floor)
  == ("-4.106780435878354362066461873198077973734102852414381703529237", .lt)
#guard D (B "1/3" "1/3" 1000) == ("5.2999162508563498719410684989453161077156056146076725903807157\
  255063590051843237408164609800001507616580286238907625869481340728712263612760816178650094687900\
    2145459554561640420834103620591188509203405598697612078243976413801515374478300834222695864833\
    2052315432500622410659290833901356405723150308957", .gt)

-- symmetry
#guard B "1/3" "11/4" 53 == B "11/4" "1/3" 53
#guard B "-1/3" "-2/5" 100 .Floor == B "-2/5" "-1/3" 100 .Floor
#guard B "-7/3" "5/2" 53 .Ceiling == B "5/2" "-7/3" 53 .Ceiling
#guard B "1/3" "5" 53 .Up == B "5" "1/3" 53 .Up

-- agreement with the float function
#guard B "1/2" "1/2" 53 == betaPrecRound (X "0.5" 53) (X "0.5" 53) 53 .Nearest
#guard B "-9/4" "5/4" 53 == betaPrecRound (X "-2.25" 53) (X "1.25" 53) 53 .Nearest
#guard B "-5/2" "15/4" 100 .Floor == betaPrecRound (X "-2.5" 53) (X "3.75" 53) 100 .Floor
#guard B "3/4" "64" 53 == betaPrecRound (X "0.75" 53) (X "64" 53) 53 .Nearest
#guard B "3/4" "65" 53 == betaPrecRound (X "0.75" 53) (X "65" 53) 53 .Nearest

-- `betaRat`
#guard toString (betaRat (Q "1/3") (Q "2/3") 53) == "3.6275987284684357"
