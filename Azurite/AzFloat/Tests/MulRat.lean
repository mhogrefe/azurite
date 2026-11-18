/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.HexString
import Azurite.AzFloat.MulRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

/-!
# Tests for the multiplication of a float by a rational

Expected values computed by hand (the exact product, then rounding to the destination
precision), shown as the decimal output of the result (`D`: the decimal and the comparison tag).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

private def M (x : AzFloat) (s : String) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  mulRatPrecRound x (Q s) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## Special values -/

#guard D (M nan "1/3" 5) == ("NaN", .eq)
#guard D (M (infinity true) "-2/3" 5) == ("-Infinity", .eq)
#guard D (M (infinity false) "-2/3" 5) == ("Infinity", .eq)
#guard D (M (infinity true) "0" 5) == ("NaN", .eq)
#guard D (M zero "1/3" 5) == ("0.0", .eq)
#guard D (M one "0" 5) == ("0.0", .eq)

/-! ## Exact products -/

#guard D (M (X "3" 2) "1/3" 5) == ("1.0", .eq)
#guard D (M (X "-3" 2) "1/3" 1) == ("-1.0", .eq)
#guard D (M (X "6" 3) "5/3" 5) == ("1.0e1", .eq)
#guard D (M (X "3" 2) "1/6" 5) == ("0.5", .eq)
#guard D (M (X "15" 4) "7/5" 6) == ("21.0", .eq)
#guard D (M one "1/4" 3) == ("0.25", .eq)  -- dyadic `q`
#guard D (M (X "3" 2) "1/3" 1) == ("1.0", .eq)
#guard D (M (X "9" 4) "1/3" 1) == ("4.0", .gt)  -- exact 3, re-rounded
#guard D (M (X "9" 4) "1/3" 1 .Floor) == ("2.0", .lt)

/-! ## Rounded products -/

#guard D (M one "1/3" 53) == ("0.3333333333333333", .lt)
#guard D (M (X "2" 2) "1/3" 53) == ("0.6666666666666666", .lt)
#guard D (M (X "-1" 1) "1/3" 53) == ("-0.3333333333333333", .gt)
#guard D (M (X "-1" 1) "-1/3" 53) == ("0.3333333333333333", .lt)
#guard D (M (X "3" 2) "2/5" 4) == ("1.2", .gt)  -- 6/5 = 1.0011..
#guard D (M (X "3" 2) "2/5" 4 .Floor) == ("1.1", .lt)
#guard D (M (X "3" 2) "2/5" 4 .Down) == ("1.1", .lt)
#guard D (M (X "-3" 2) "2/5" 4 .Down) == ("-1.1", .gt)
#guard D (M (X "-3" 2) "2/5" 4 .Up) == ("-1.2", .lt)
#guard D (M one "1/3" 1) == ("0.2", .lt)  -- 1/3 to one bit
#guard D (M one "1/3" 1 .Ceiling) == ("0.5", .gt)

/-! ## Far exponents -/

#guard M (powerOf2 (AzInt.ofInt 1000000000)) "1/3" 5 ==
  (X "0.33" 5 <<< (AzInt.ofInt 1000000000), .lt)
#guard M (powerOf2 (AzInt.ofInt (-1000000000))) "-1/3" 5 ==
  (X "-0.33" 5 >>> (AzInt.ofInt 1000000000), .gt)

/-! ## The `*` instances: nearest, at the float's precision -/

#guard toString (one * Q "1/3") == "0.2"
#guard toString (Q "1/3" * X "3" 2) == "1.0"
#guard toString (X "1" 5 * Q "1/3") == "0.33"
#guard toString (Q "-2/7" * X "7" 3) == "-2.0"
#guard toString (zero * Q "1/3") == "0.0"
#guard toString (infinity true * Q "-1") == "-Infinity"
