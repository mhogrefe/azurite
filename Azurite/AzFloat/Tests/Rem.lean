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

/-!
# Tests for the remainder

Expected values computed by hand (`x − y · trunc (x / y)`, then one rounding).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def M (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  remPrecRound x y p m

/-! ## `shiftLeftMod` -/

#guard (AzNat.shiftLeftMod (AzNat.ofNat 5) 3 (AzNat.ofNat 7)) == AzNat.ofNat 5   -- 40 mod 7
#guard (AzNat.shiftLeftMod (AzNat.ofNat 5) 100 (AzNat.ofNat 7)) == AzNat.ofNat 3 -- 5·2^100 mod 7
#guard (AzNat.shiftLeftMod (AzNat.ofNat 5) 3 0) == AzNat.ofNat 40
#guard (AzNat.shiftLeftMod 0 1000000 (AzNat.ofNat 7)) == 0

/-! ## Special values -/

#guard M nan one 10 == (nan, .eq)
#guard M one nan 10 == (nan, .eq)
#guard M (infinity true) one 10 == (nan, .eq)
#guard M (infinity false) (infinity true) 10 == (nan, .eq)
#guard M one zero 10 == (nan, .eq)
#guard M zero zero 10 == (nan, .eq)
#guard M (infinity true) zero 10 == (nan, .eq)
#guard M (F "7/3" 5) (infinity true) 10 == (setPrec (F "7/3" 5) 10, .eq)   -- `x` at 10 bits
#guard M (F "7" 3) (infinity false) 10 == (F "7" 10, .eq)
#guard M zero (infinity true) 10 == (zero, .eq)
#guard M zero (F "7/3" 5) 10 == (zero, .eq)
#guard M zero (-F "7/3" 5) 10 == (zero, .eq)

/-! ## Exact remainders -/

#guard M (F "7" 3) (F "3" 2) 10 == (F "1" 10, .eq)
#guard M (F "-7" 3) (F "3" 2) 10 == (F "-1" 10, .eq)      -- sign of the dividend
#guard M (F "7" 3) (F "-3" 2) 10 == (F "1" 10, .eq)
#guard M (F "-7" 3) (F "-3" 2) 10 == (F "-1" 10, .eq)
#guard M (F "6" 3) (F "3" 2) 10 == (zero, .eq)
#guard M (F "-6" 3) (F "3" 2) 10 == (zero, .eq)
#guard M (F "3" 2) (F "7" 3) 10 == (F "3" 10, .eq)        -- `|x| < |y|`
#guard M (F "-3" 2) (F "7" 3) 10 == (F "-3" 10, .eq)
#guard M (F "11/2" 4) (F "3/2" 2) 10 == (F "1" 10, .eq)    -- 5.5 mod 1.5
#guard M (F "11/2" 4) (F "1/4" 1) 10 == (zero, .eq)
#guard M (F "1/4" 1) (F "11/2" 4) 10 == (F "1/4" 10, .eq)
#guard M (F "7/3" 5) (F "1" 1) 5 == (F "7/3" 5 - F "2" 5, .eq)   -- frac part, exact at 5 bits
#guard M (F "7/3" 5) (F "1/2" 1) 5 == (F "7/3" 5 - F "2" 5, .eq)
#guard M (F "-7/3" 5) (F "1" 1) 5 == (F "-7/3" 5 + F "2" 5, .eq)
-- the dividend's exponent far above the divisor's: shift-free reduction
#guard M (P 100) (F "3" 2) 10 == (F "1" 10, .eq)           -- 2^100 mod 3 = 1
#guard M (P 101) (F "3" 2) 10 == (F "2" 10, .eq)           -- 2^101 mod 3 = 2
#guard M (P 1000000) (F "7" 3) 10 == (F "2" 10, .eq)       -- 2^1000000 mod 7 = 2^(10^6 mod 3) = 2
#guard M (-P 1000000) (F "7" 3) 10 == (F "-2" 10, .eq)
#guard M ((F "1" 60 <<< 100) + (F "1" 60 <<< 50)) (F "3" 2) 10 == (F "2" 10, .eq) -- 1 + 1
#guard M (F "1" 1) (P (-1000000)) 10 == (zero, .eq)
#guard M (P (-1000000)) (F "1" 1) 10 == (setPrec (P (-1000000)) 10, .eq)
-- the divisor's exponent above the dividend's with `|x| ≥ |y|`
#guard M (F "7" 3) (F "3/2" 2) 10 == (F "1" 10, .eq)
#guard M (F "13/4" 4) (F "3/2" 2) 10 == (F "1/4" 10, .eq)

/-! ## Rounded remainders -/

-- `37/16 mod 1 = 5/16`, a tie between `1/4` and `3/8` at 2 bits: to even, `1/4`
#guard M (F "37/16" 6) (F "1" 1) 2 == (F "1/4" 2, .lt)
#guard M (F "37/16" 6) (F "1" 1) 2 .Up == (F "3/8" 2, .gt)
#guard M (F "-37/16" 6) (F "1" 1) 2 == (F "-1/4" 2, .gt)
#guard M (F "-37/16" 6) (F "1" 1) 2 .Floor == (F "-3/8" 2, .lt)
#guard M (F "37/16" 6) (F "1" 1) 4 == (F "5/16" 4, .eq)
#guard M (F "100" 7) (F "7" 3) 1 == (F "2" 1, .eq)
#guard M (F "100" 7) (F "7" 3) 2 .Down == (F "2" 2, .eq)
#guard M (F "101" 7) (F "7" 3) 1 == (F "4" 1, .gt)          -- 3 → 4 at 1 bit (tie, even)
#guard M (F "101" 7) (F "7" 3) 1 .Down == (F "2" 1, .lt)

/-! ## `%` -/

#guard (F "7" 3) % (F "3" 2) == F "1" 3
#guard (F "-7" 3) % (F "3" 2) == F "-1" 3
#guard (F "7/3" 5) % (F "1" 1) == F "7/3" 5 - F "2" 5
#guard (F "37/16" 6) % (F "1" 10) == F "5/16" 10
#guard (F "100" 7) % (F "7" 3) == F "2" 7
#guard (F "6" 3) % (F "3" 2) == zero
#guard nan % one == nan
#guard one % zero == nan
#guard one % (infinity true) == one
#guard (infinity true) % one == nan
