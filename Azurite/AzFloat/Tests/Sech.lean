/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sech
import Azurite.AzFloat.Exp
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sech x`

The special values (`NaN`, `±∞ ↦ 0`, `sech 0 = 1`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `700` in three modes, 1-, 2-, 20-, 113-, 120- and 200-bit results,
200-bit strings, evenness, tiny arguments `±2^(−1000)`, `±2^(−2^30)` (the value is just below
`1`, at no cost), the neighbourhood of the last place (`2^(−26)`, `2^(−27)`), and large
arguments (`±2^20`, where `sech x` rounds like `2 exp (−|x|)`).  References: an independent
6000-bit fixed-point evaluation of `2/(e^x + e^(−x))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- `0.3333333333…` at 200 bits. -/
private def third200 : AzFloat :=
  X "0.3333333333333333333333333333333333333333333333333333333333334" 200
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := X "0.9999999999999999" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sechPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("0.0", .eq)
#guard D (A (infinity false) 53) == ("0.0", .eq)
#guard D (A (infinity false) 0) == ("0.0", .eq)
#guard D (A zero 53) == ("1.0", .eq)
#guard D (A zero 1 .Floor) == ("1.0", .eq)
#guard D (A zero 0) == ("NaN", .eq)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "1" 53) 53) == ("0.6480542736638853", .lt)
#guard D (A (X "-1" 53) 53) == ("0.6480542736638853", .lt)
#guard D (A (X "2" 53) 53) == ("0.26580222883407967", .lt)
#guard D (A (X "0.5" 53) 53) == ("0.8868188839700739", .gt)
#guard D (A (X "-0.3333333333333333" 53) 53) == ("0.9469052537634979", .lt)
#guard D (A (X "1.5" 53) 53) == ("0.4250960349422805", .gt)
#guard D (A (X "-1.4" 53) 53) == ("0.4649219924089817", .lt)
#guard D (A (X "3.142857142857143" 53) 53) == ("0.0861581295369795", .gt)
#guard D (A (X "10" 53) 53) == ("0.00009079985933781725", .gt)
#guard D (A (X "-100" 53) 53) == ("7.440151952041672e-44", .gt)
#guard D (A (X "0.001" 53) 53) == ("0.9999995000002083", .lt)
#guard D (A (X "-0.000000000001" 53) 53) == ("1.0", .gt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("1.0", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("1.0", .gt)
#guard D (A (X "-1.8669045833583425e-60" 53) 53) ==
  ("1.0", .gt)
#guard D (A (X "30" 53) 53) == ("1.871524593768035e-13", .gt)
#guard D (A (X "-37" 53) 53) == ("1.7066095251488132e-16", .gt)
#guard D (A (X "700" 53) 53) == ("1.971935308751954e-304", .lt)
#guard D (A (X "1" 53) 53 .Floor) == ("0.6480542736638853", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("0.6480542736638853", .lt)
#guard D (A (X "1.5" 53) 53 .Floor) == ("0.42509603494228043", .lt)
#guard D (A (X "-1.4" 53) 53 .Floor) == ("0.4649219924089817", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("0.9999995000002083", .lt)
#guard D (A (X "-100" 53) 53 .Floor) == ("7.440151952041671e-44", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("0.6480542736638855", .gt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("0.6480542736638855", .gt)
#guard D (A (X "1.5" 53) 53 .Ceiling) == ("0.4250960349422805", .gt)
#guard D (A (X "-1.4" 53) 53 .Ceiling) == ("0.46492199240898174", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("0.9999995000002084", .gt)
#guard D (A (X "-100" 53) 53 .Ceiling) == ("7.440151952041672e-44", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling) == ("1.0", .gt)
#guard D (A (X "1" 53) 20) == ("0.648054", .lt)
#guard D (A (X "1" 53) 1) == ("0.5", .lt)
#guard D (A (X "-1.5" 53) 2) == ("0.4", .lt)
#guard D (A (X "1.5" 53) 113) == ("0.42509603494228046092468090010712433", .lt)
#guard D (A third200 200) ==
  ("0.946905253763497926558952280139811647196865554127211019972439", .gt)
#guard D (A third200 10 .Floor) == ("0.946", .lt)
#guard D (A (X "10" 53) 120) == ("0.00009079985933781724408012950782047818705", .lt)
#guard sech (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString (sechPrecRound (X "1" 200) 200 .Nearest).1 == "0.6480542736638853995749773532261503\
  23108489312071942023037865"
#guard toString (sechPrecRound (X "-1.5" 200) 200 .Nearest).1 == "0.4250960349422804609246809001071\
  243390053536699153442494113308"

-- evenness
private def even (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool := A (-x) p m == A x p m
#guard even (X "1.5" 53) 53 .Nearest && even (X "1.5" 53) 53 .Floor
#guard even (X "100" 53) 20 .Ceiling && even (h (X "1" 53) (-1000)) 53 .Floor

-- tiny arguments: just below `1`
private def tinyOk (x : AzFloat) : Bool :=
  A x 53 == (X "1" 53, .gt) && A x 53 .Ceiling == (X "1" 53, .gt) && A x 53 .Floor == (dn, .lt)
    && A (-x) 53 .Floor == (dn, .lt) && A x 1 .Floor == (X "0.5" 1, .lt)
#guard tinyOk (h (X "1" 53) (-100))
#guard tinyOk (h (X "1" 53) (-1000))
#guard tinyOk (h (X "3" 53) (-1073741824))
-- `sech (2^(−26)) = 1 − 2^(−53) + …`: just above the float below `1`
#guard D (A (h (X "1" 53) (-26)) 53) == ("0.9999999999999999", .lt)
#guard D (A (h (X "1" 53) (-26)) 53 .Ceiling) == ("1.0", .gt)
#guard D (A (h (X "1" 53) (-27)) 53) == ("1.0", .gt)
#guard D (A (h (X "1" 53) (-27)) 53 .Floor) == ("0.9999999999999999", .lt)

-- large arguments: `sech x` rounds like `2 exp (−|x|)`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expPrecRound (-x) p m
  A x p m == (h r.1 1, r.2) && A (-x) p m == (h r.1 1, r.2)
#guard big (X "1048576" 53) 53 .Nearest && big (X "1048576" 53) 53 .Floor
#guard big (X "15432098.625" 53) 20 .Ceiling && big (X "1000" 53) 113 .Nearest
