/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.DivRat
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Precision
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString

/-!
# Tests for the divisions between a float and a rational

Expected values computed by hand (the exact quotient, then rounding to the destination
precision).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

private def D (x : AzFloat) (s : String) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  divRatPrecRound x (Q s) p m

private def R (s : String) (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  ratDivPrecRound (Q s) x p m
/-- A result as its decimal output and its comparison tag. -/
private def Dd (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## `x / q`: special values -/

#guard Dd (D nan "1" 5) == ("NaN", .eq)
#guard Dd (D (infinity true) "-2" 5) == ("-Infinity", .eq)
#guard Dd (D (infinity false) "-2" 5) == ("Infinity", .eq)
#guard Dd (D (infinity true) "0" 5) == ("Infinity", .eq)
#guard Dd (D zero "0" 5) == ("NaN", .eq)
#guard Dd (D zero "7" 5) == ("0.0", .eq)
#guard Dd (D one "0" 5) == ("Infinity", .eq)
#guard Dd (D (X "-1" 1) "0" 5) == ("-Infinity", .eq)

/-! ## `x / q`: values -/

#guard Dd (D (X "3" 2) "3" 5) == ("1.0", .eq)
#guard Dd (D one "3" 53) == ("0.3333333333333333", .lt)
#guard Dd (D one "-3" 53) == ("-0.3333333333333333", .gt)
#guard Dd (D one "3" 1) == ("0.2", .lt)
#guard Dd (D (X "3" 2) "2/5" 4) == ("7.5", .eq) -- 7.5 = 111.1
#guard Dd (D (X "3" 2) "2/5" 3) == ("8.0", .gt) -- tie to even
#guard Dd (D (X "3" 2) "2/5" 3 .Floor) == ("7.0", .lt)
#guard Dd (D (X "-3" 2) "2/5" 3 .Down) == ("-7.0", .gt)
#guard D (powerOf2 (AzInt.ofInt 1000000000)) "3" 5 ==
  (X "0.33" 5 <<< (AzInt.ofInt 1000000000), .lt)

/-! ## `q / x`: special values -/

#guard Dd (R "1" nan 5) == ("NaN", .eq)
#guard Dd (R "5" (infinity false) 3) == ("0.0", .eq)
#guard Dd (R "0" (infinity true) 3) == ("0.0", .eq)
#guard Dd (R "0" zero 5) == ("NaN", .eq)
#guard Dd (R "5" zero 3) == ("Infinity", .eq)
#guard Dd (R "-5" zero 3) == ("-Infinity", .eq)
#guard Dd (R "0" one 5) == ("0.0", .eq)

/-! ## `q / x`: values -/

#guard Dd (R "1" one 5) == ("1.0", .eq)
#guard Dd (R "1" (X "3" 2) 53) == ("0.3333333333333333", .lt)
#guard Dd (R "2" (X "3" 2) 53) == ("0.6666666666666666", .lt)
#guard Dd (R "1" (X "-3" 2) 53) == ("-0.3333333333333333", .gt)
#guard Dd (R "-1" (X "-3" 2) 53) == ("0.3333333333333333", .lt)
#guard Dd (R "3/2" (X "3" 2) 4) == ("0.5", .eq)
#guard Dd (R "2/5" (X "3" 2) 4) == ("0.14", .gt) -- 0.0010001000..
#guard Dd (R "2/5" (X "3" 2) 4 .Ceiling) == ("0.14", .gt)
#guard Dd (R "2/5" (X "3" 2) 4 .Floor) == ("0.125", .lt)
#guard R "1" (powerOf2 (AzInt.ofInt 1000000000)) 5 ==
  (setPrec (powerOf2 (AzInt.ofInt (-1000000000))) 5, .eq)

/-! ## The `/` instances: nearest, at the float's precision -/

#guard toString (one / Q "3") == "0.2"
#guard toString (X "1" 5 / Q "3") == "0.33"
#guard toString (Q "1" / X "3" 2) == "0.4"
#guard toString (Q "3/2" / X "3" 2) == "0.5"
#guard toString (zero / Q "3") == "0.0"
#guard toString (Q "3" / zero) == "Infinity"
