/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.QGamma
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the `q`-gamma function

The four functions (the base and the argument each a float or a rational): the bases that are
not positive and finite, the base `1` (`Γ`), arguments that are not finite, `0` and the poles,
`p = 0`, the exact `q`-factorials (`Γ_{1/2}(5) = 315/64`, `Γ_3(5) = 2080`,
`Γ_{1/3}(4) = 52/27`), bases below and above `1`, near `1`, tiny and huge, negative arguments
with their signs, 200 bits of `Γ_{1/2}(1/2) = 1.57203272578632388277095566532729…` and of
`Γ_{1/3}(1/3) = 2.04228445308586249583913385636782…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- The float nearest to a rational at 53 bits. -/
private def F (s : String) : AzFloat := ofAzRat (Q s) 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def G (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qGammaPrecRound (F q) (F x) p m)
private def GR (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qGammaRatPrecRound (Q q) (Q x) p m)
private def GFR (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qGammaFloatRatPrecRound (F q) (Q x) p m)
private def GRF (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qGammaRatFloatPrecRound (Q q) (F x) p m)

/-! ### Floats -/

-- bases and arguments that are not finite, bases `≤ 0`, `p = 0`
#guard D (qGammaPrecRound nan (F "1/2") 53 .Nearest) == ("NaN", .eq)
#guard D (qGammaPrecRound (F "1/2") nan 53 .Nearest) == ("NaN", .eq)
#guard D (qGammaPrecRound (infinity true) (F "1/2") 53 .Nearest) == ("NaN", .eq)
#guard D (qGammaPrecRound (F "1/2") (infinity true) 53 .Nearest) == ("Infinity", .eq)
#guard D (qGammaPrecRound (F "1/2") (infinity false) 53 .Nearest) == ("NaN", .eq)
#guard D (qGammaPrecRound (F "1") (infinity true) 53 .Nearest) == ("Infinity", .eq)
#guard G "0" "1/2" 53 == ("NaN", .eq)
#guard G "-2" "1/2" 53 == ("NaN", .eq)
#guard G "1/2" "0" 53 == ("Infinity", .eq)
#guard G "1/2" "0" 0 == ("Infinity", .eq)
#guard G "1/2" "-3" 53 == ("NaN", .eq)
#guard G "1/2" "1/2" 0 == ("NaN", .eq)

-- the base `1`: `Γ`
#guard G "1" "5" 53 == ("24.0", .eq)
#guard G "1" "1/2" 53 == ("1.772453850905516", .gt)

-- the exact values: `q`-factorials
#guard G "1/2" "1" 53 == ("1.0", .eq)
#guard G "1/2" "2" 53 == ("1.0", .eq)
#guard G "1/2" "3" 53 == ("1.5", .eq)
#guard G "1/2" "5" 53 == ("4.921875", .eq)
#guard G "3" "5" 53 == ("2.08e3", .eq)
#guard G "2" "20" 53 == ("4.531889275955133e56", .lt)
#guard G "2" "20" 200
  == ("453188927595513350075389930779308072236776417524282593125.0", .eq)
#guard G "1/3" "3" 53 == ("1.3333333333333333", .lt)
#guard G "1/3" "4" 53 == ("1.9259259259259258", .lt)

-- bases below and above `1`
#guard G "1/2" "1/2" 53 == ("1.5720327257863238", .lt)
#guard G "1/2" "1/2" 53 .Ceiling == ("1.572032725786324", .gt)
#guard G "1/2" "1/2" 200
  == ("1.572032725786323882770955665327291782835922872281655214617908", .gt)
#guard G "3/4" "1/4" 53 == ("3.3077401968742084", .lt)
#guard G "2" "1/2" 53 == ("2.038674220005549", .gt)
#guard G "1/2" "1/1024" 53 == ("738.6069652401599", .gt)
#guard toString (qGamma (F "1/2") (F "1/2")) == "1.5720327257863238"

-- negative arguments: the signs
#guard G "2" "-5/2" 53 == ("-13.079411268190244", .lt)
#guard G "1/2" "-5/2" 53 == ("-0.05571562158855689", .gt)
#guard G "1/2" "-7/2" 53 == ("0.002701046941264692", .lt)
#guard G "1/2" "-41/2" 53 == ("-2.421668158835668e-72", .lt)

-- large arguments
#guard G "1/2" "201/2" 53 == ("2.5885934898050384e29", .gt)
#guard G "3" "201/2" 53 == ("2.200060711977467e2355", .gt)

-- bases near `1` (the limit is `Γ(1/2) = 1.7724…`), tiny and huge
#guard G "31/32" "1/2" 53 == ("1.7619709869361946", .lt)
#guard G "33/32" "1/2" 53 == ("1.7827450792985184", .gt)
#guard G "1/1267650600228229401496703205376" "1/2" 53 == ("1.0000000000000009", .gt)
#guard G "1267650600228229401496703205376" "1/2" 53 == ("194368031998.46735", .lt)

/-! ### Rationals -/

#guard GR "0" "1/2" 53 == ("NaN", .eq)
#guard GR "-1/2" "1/2" 53 == ("NaN", .eq)
#guard GR "1/3" "0" 53 == ("Infinity", .eq)
#guard GR "1/3" "-2" 53 == ("NaN", .eq)
#guard GR "1/3" "1/3" 0 == ("NaN", .eq)
#guard GR "1" "1/2" 53 == ("1.772453850905516", .gt)
#guard GR "1" "5" 53 == ("24.0", .eq)
-- exact rational values that are not dyadic
#guard GR "1/3" "4" 53 == ("1.9259259259259258", .lt)
#guard GR "1/3" "4" 53 .Ceiling == ("1.925925925925926", .gt)
#guard GR "2/3" "10" 53 == ("1436.6867860216196", .gt)
#guard GR "1/3" "1/3" 53 == ("2.0422844530858626", .gt)
#guard GR "1/3" "1/3" 200
  == ("2.042284453085862495839133856367828481043245244849889693120778", .lt)
#guard GR "3" "-7/2" 53 == ("114.28751978043962", .lt)
#guard GR "5/7" "22/7" 53 == ("1.8978369091152456", .lt)
#guard GR "7/5" "-22/7" 53 == ("5.716434534394363", .gt)
#guard toString (qGammaRat (Q "1/3") (Q "1/3") 53) == "2.0422844530858626"

/-! ### A float base and a rational argument -/

#guard GFR "-1" "1/3" 53 == ("NaN", .eq)
#guard GFR "1/2" "-2" 53 == ("NaN", .eq)
#guard GFR "1/2" "0" 53 == ("Infinity", .eq)
#guard GFR "1" "1/3" 53 == ("2.6789385347077475", .lt)
#guard GFR "1/2" "5" 53 == ("4.921875", .eq)
#guard GFR "1/2" "1/3" 53 == ("2.239875152316739", .lt)
#guard GFR "2" "-7/3" 53 == ("-14.757607254028446", .lt)
#guard toString (qGammaFloatRat (F "1/2") (Q "1/3") 53) == "2.239875152316739"

/-! ### A rational base and a float argument -/

#guard GRF "-1/3" "1/2" 53 == ("NaN", .eq)
#guard D (qGammaRatFloatPrecRound (Q "1/3") (infinity true) 53 .Nearest) == ("Infinity", .eq)
#guard D (qGammaRatFloatPrecRound (Q "1/3") nan 53 .Nearest) == ("NaN", .eq)
#guard GRF "1" "1/2" 53 == ("1.772453850905516", .gt)
#guard GRF "1/3" "4" 53 == ("1.9259259259259258", .lt)
#guard GRF "1/3" "1/2" 53 == ("1.4788603289115767", .gt)
#guard GRF "3" "-5/2" 53 == ("-55.92183525484479", .lt)
#guard toString (qGammaRatFloat (Q "1/3") (F "1/2") 53) == "1.4788603289115767"
