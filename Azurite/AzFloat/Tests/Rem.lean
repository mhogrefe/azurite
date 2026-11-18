/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Rem
import Azurite.AzFloat.Add
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString

/-!
# Tests for the remainder

Expected values computed by hand (`x − y · trunc (x / y)`, then one rounding).
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def M (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  remPrecRound x y p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## `shiftLeftMod` -/

#guard toString (AzNat.shiftLeftMod (AzNat.ofNat 5) 3 (AzNat.ofNat 7)) == "5" -- 40 mod 7
#guard toString (AzNat.shiftLeftMod (AzNat.ofNat 5) 100 (AzNat.ofNat 7)) == "3" -- 5·2^100 mod 7
#guard toString (AzNat.shiftLeftMod (AzNat.ofNat 5) 3 0) == "40"
#guard toString (AzNat.shiftLeftMod 0 1000000 (AzNat.ofNat 7)) == "0"

/-! ## Special values -/

#guard D (M nan one 10) == ("NaN", .eq)
#guard D (M one nan 10) == ("NaN", .eq)
#guard D (M (infinity true) one 10) == ("NaN", .eq)
#guard D (M (infinity false) (infinity true) 10) == ("NaN", .eq)
#guard D (M one zero 10) == ("NaN", .eq)
#guard D (M zero zero 10) == ("NaN", .eq)
#guard D (M (infinity true) zero 10) == ("NaN", .eq)
#guard D (M (X "2.4" 5) (infinity true) 10) == ("2.375", .eq) -- `x` at 10 bits
#guard D (M (X "7" 3) (infinity false) 10) == ("7.0", .eq)
#guard D (M zero (infinity true) 10) == ("0.0", .eq)
#guard D (M zero (X "2.4" 5) 10) == ("0.0", .eq)
#guard D (M zero (-X "2.4" 5) 10) == ("0.0", .eq)

/-! ## Exact remainders -/

#guard D (M (X "7" 3) (X "3" 2) 10) == ("1.0", .eq)
#guard D (M (X "-7" 3) (X "3" 2) 10) == ("-1.0", .eq) -- sign of the dividend
#guard D (M (X "7" 3) (X "-3" 2) 10) == ("1.0", .eq)
#guard D (M (X "-7" 3) (X "-3" 2) 10) == ("-1.0", .eq)
#guard D (M (X "6" 3) (X "3" 2) 10) == ("0.0", .eq)
#guard D (M (X "-6" 3) (X "3" 2) 10) == ("0.0", .eq)
#guard D (M (X "3" 2) (X "7" 3) 10) == ("3.0", .eq) -- `|x| < |y|`
#guard D (M (X "-3" 2) (X "7" 3) 10) == ("-3.0", .eq)
#guard D (M (X "5.5" 4) (X "1.5" 2) 10) == ("1.0", .eq) -- 5.5 mod 1.5
#guard D (M (X "5.5" 4) (X "0.25" 1) 10) == ("0.0", .eq)
#guard D (M (X "0.25" 1) (X "5.5" 4) 10) == ("0.25", .eq)
#guard D (M (X "2.4" 5) (X "1" 1) 5) == ("0.38", .eq) -- frac part, exact at 5 bits
#guard D (M (X "2.4" 5) (X "0.5" 1) 5) == ("0.38", .eq)
#guard D (M (X "-2.4" 5) (X "1" 1) 5) == ("-0.38", .eq)
-- the dividend's exponent far above the divisor's: shift-free reduction
#guard D (M (P 100) (X "3" 2) 10) == ("1.0", .eq) -- 2^100 mod 3 = 1
#guard D (M (P 101) (X "3" 2) 10) == ("2.0", .eq) -- 2^101 mod 3 = 2
#guard D (M (P 1000000) (X "7" 3) 10) == ("2.0", .eq) -- 2^1000000 mod 7 = 2^(10^6 mod 3) = 2
#guard D (M (-P 1000000) (X "7" 3) 10) == ("-2.0", .eq)
#guard D (M ((X "1" 60 <<< 100) + (X "1" 60 <<< 50)) (X "3" 2) 10) == ("2.0", .eq) -- 1 + 1
#guard D (M (X "1" 1) (P (-1000000)) 10) == ("0.0", .eq)
#guard M (P (-1000000)) (X "1" 1) 10 == (setPrec (P (-1000000)) 10, .eq)
-- the divisor's exponent above the dividend's with `|x| ≥ |y|`
#guard D (M (X "7" 3) (X "1.5" 2) 10) == ("1.0", .eq)
#guard D (M (X "3.25" 4) (X "1.5" 2) 10) == ("0.25", .eq)

/-! ## Rounded remainders -/

-- `37/16 mod 1 = 5/16`, a tie between `1/4` and `3/8` at 2 bits: to even, `1/4`
#guard D (M (X "2.3125" 6) (X "1" 1) 2) == ("0.25", .lt)
#guard D (M (X "2.3125" 6) (X "1" 1) 2 .Up) == ("0.4", .gt)
#guard D (M (X "-2.3125" 6) (X "1" 1) 2) == ("-0.25", .gt)
#guard D (M (X "-2.3125" 6) (X "1" 1) 2 .Floor) == ("-0.4", .lt)
#guard D (M (X "2.3125" 6) (X "1" 1) 4) == ("0.3", .eq)
#guard D (M (X "100" 7) (X "7" 3) 1) == ("2.0", .eq)
#guard D (M (X "100" 7) (X "7" 3) 2 .Down) == ("2.0", .eq)
#guard D (M (X "101" 7) (X "7" 3) 1) == ("4.0", .gt) -- 3 → 4 at 1 bit (tie, even)
#guard D (M (X "101" 7) (X "7" 3) 1 .Down) == ("2.0", .lt)

/-! ## `%` -/

#guard toString ((X "7" 3) % (X "3" 2)) == "1.0"
#guard toString ((X "-7" 3) % (X "3" 2)) == "-1.0"
#guard toString ((X "2.4" 5) % (X "1" 1)) == "0.38"
#guard toString ((X "2.3125" 6) % (X "1" 10)) == "0.3125"
#guard toString ((X "100" 7) % (X "7" 3)) == "2.0"
#guard toString ((X "6" 3) % (X "3" 2)) == "0.0"
#guard toString (nan % one) == "NaN"
#guard toString (one % zero) == "NaN"
#guard toString (one % (infinity true)) == "1.0"
#guard toString ((infinity true) % one) == "NaN"
