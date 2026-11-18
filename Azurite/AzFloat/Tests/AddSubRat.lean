/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddSubRat
import Azurite.AzFloat.HexString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

/-!
# Tests for the addition of a float and a rational

Expected values computed by hand (the exact sum, then rounding to the destination precision),
shown as the decimal output of the result (`D`: the decimal and the comparison tag).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

private def H (x : AzFloat) : String := toHexString x

private def A (x : AzFloat) (s : String) (p : Nat) (m : RoundingMode := .Nearest) :
    AzFloat × Ordering :=
  addRatPrecRound x (Q s) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## Special values -/

#guard D (A nan "1/3" 5) == ("NaN", .eq)
#guard D (A (infinity true) "1/3" 5) == ("Infinity", .eq)
#guard D (A (infinity false) "-7" 5) == ("-Infinity", .eq)
#guard D (A zero "1/3" 10) == ("0.3335", .gt)
#guard D (A zero "0" 10) == ("0.0", .eq)
#guard D (A one "0" 5) == ("1.0", .eq)
#guard D (A one "-1" 5) == ("0.0", .eq)

/-! ## Exact (dyadic) cases -/

#guard D (A one "1/2" 2) == ("1.5", .eq)
#guard D (A one "1/4" 3) == ("1.2", .eq)
#guard D (A (X "10" 4) "5" 4) == ("15.0", .eq)
#guard D (A one "-1023/1024" 5) == ("0.001", .eq)  -- cancellation
#guard D (A (X "3" 2) "-3/2" 2) == ("1.5", .eq)
#guard D (A (X "3" 2) "-3/2" 1) == ("2.0", .gt)  -- tie to even
#guard H (A one "1/2" 2).1 == "0x1.8#2"

/-! ## Rounded cases -/

#guard D (A one "1/3" 53) == ("1.3333333333333333", .lt)
#guard D (A one "1/3" 53 .Ceiling) == ("1.3333333333333335", .gt)
#guard D (A one "1/3" 53 .Floor) == ("1.3333333333333333", .lt)
#guard D (A one "-2/3" 1) == ("0.2", .lt)  -- 1/3 to one bit
#guard D (A one "-2/3" 1 .Ceiling) == ("0.5", .gt)
#guard D (A (X "-1" 1) "2/3" 1) == ("-0.2", .gt)
#guard D (A one "1/3" 1) == ("1.0", .lt)  -- 4/3 to one bit
#guard D (A one "1/3" 1 .Up) == ("2.0", .gt)

/-! ## Near a midpoint: the first working precision is not enough -/

-- `1/2 + 1/(3·2^80)`: the sum `3/2 + 2^-80/3` is just above the one-bit midpoint
#guard D (A one "1813388729421943762059265/3626777458843887524118528" 1) == ("2.0", .gt)
#guard D (A one "1813388729421943762059265/3626777458843887524118528" 1 .Floor) == ("1.0", .lt)
#guard D (A one "1813388729421943762059265/3626777458843887524118528" 1 .Down) == ("1.0", .lt)
-- `1/2 − 1/(3·2^80)`: just below the midpoint
#guard D (A one "1813388729421943762059263/3626777458843887524118528" 1) == ("1.0", .lt)
#guard D (A one "1813388729421943762059263/3626777458843887524118528" 1 .Ceiling) == ("2.0", .gt)
-- exactly the midpoint (dyadic, exact): ties to even
#guard D (A one "1/2" 1) == ("2.0", .gt)
#guard D (A (X "3" 2) "1/2" 3) == ("3.5", .eq)
#guard D (A (X "3" 2) "1/2" 2) == ("4.0", .gt)
#guard D (A (X "3" 2) "1/2" 1) == ("4.0", .gt)

/-! ## Far apart exponents -/

#guard D (A (powerOf2 (AzInt.ofInt 1000)) "1/3" 5) == ("1.1e301", .lt)
#guard D (A (powerOf2 (AzInt.ofInt 1000)) "-1/3" 5) == ("1.1e301", .gt)
#guard D (A (powerOf2 (AzInt.ofInt (-1000))) "1/3" 5) == ("0.33", .lt)
#guard D (A (powerOf2 (AzInt.ofInt (-1000))) "-1/3" 5) == ("-0.33", .gt)

/-! ## Far apart exponents, beyond any exact computation -/

#guard A (powerOf2 (AzInt.ofInt 1000000000)) "1/3" 5 ==
  (setPrec (powerOf2 (AzInt.ofInt 1000000000)) 5, .lt)
#guard A (powerOf2 (AzInt.ofInt 1000000000)) "-1/3" 5 .Ceiling ==
  (setPrec (powerOf2 (AzInt.ofInt 1000000000)) 5, .gt)
#guard D (A (powerOf2 (AzInt.ofInt (-1000000000))) "1/3" 5) == ("0.33", .lt)
#guard D (A (powerOf2 (AzInt.ofInt (-1000000000))) "1/4" 3) == ("0.25", .lt)  -- dyadic `q`
#guard A (powerOf2 (AzInt.ofInt 1000000000)) "1/4" 3 ==
  (setPrec (powerOf2 (AzInt.ofInt 1000000000)) 3, .lt)

/-! ## Subtraction -/

#guard D (subRatPrecRound one (Q "1/2") 2 .Nearest) == ("0.5", .eq)
#guard D (subRatPrecRound one (Q "-1/3") 53 .Nearest) == ("1.3333333333333333", .lt)
#guard D (ratSubPrecRound (Q "1/2") one 2 .Nearest) == ("-0.5", .eq)
#guard D (ratSubPrecRound (Q "1/3") one 53 .Nearest) == ("-0.6666666666666666", .gt)
#guard D (ratSubPrecRound (Q "1/3") zero 5 .Nearest) == ("0.33", .lt)
#guard D (subRatPrecRound (infinity true) (Q "5") 5 .Nearest) == ("Infinity", .eq)
#guard D (ratSubPrecRound (Q "5") (infinity true) 5 .Nearest) == ("-Infinity", .eq)

/-! ## The `+` and `−` instances: nearest, at the float's precision (`1` for a special float) -/

#guard toString (one + Q "1/3") == "1.0"  -- 4/3 to one bit
#guard toString (X "1" 5 + Q "1/3") == "1.3"
#guard toString (Q "1/3" + X "1" 5) == "1.3"
#guard toString (zero + Q "1/3") == "0.2"
#guard toString (Q "1/3" + zero) == "0.2"
#guard toString (X "1" 5 - Q "1/3") == "0.66"
#guard toString (Q "1/3" - X "1" 5) == "-0.66"
#guard toString (X "1.75" 20 - Q "7/4") == "0.0"
#guard toString (infinity true + Q "-1") == "Infinity"
#guard toString (Q "5" - infinity true) == "-Infinity"
#guard toString (nan + Q "1") == "NaN"
