/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cosh
import Azurite.AzFloat.Exp
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `cosh x`

The special values (`NaN`, `±∞ ↦ +∞`, `cosh 0 = 1`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `700` in three modes, 1-, 2-, 20-, 113-, 120- and 200-bit results,
200-bit strings, evenness, tiny arguments `±2^(−1000)`, `±2^(−2^30)` (the value is just above
`1`, at no cost), and large arguments (`±2^20`, where `cosh x` rounds like `exp |x| / 2`).
References: an independent 6000-bit fixed-point evaluation of `(e^x + e^(−x))/2` rounded with
exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := X "1.0000000000000002" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := coshPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("Infinity", .eq)
#guard D (A (infinity false) 53) == ("Infinity", .eq)
#guard D (A (infinity false) 0) == ("Infinity", .eq)
#guard D (A zero 53) == ("1.0", .eq)
#guard D (A zero 1 .Floor) == ("1.0", .eq)
#guard D (A zero 0) == ("NaN", .eq)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "1" 53) 53) == ("1.5430806348152437", .lt)
#guard D (A (X "-1" 53) 53) == ("1.5430806348152437", .lt)
#guard D (A (X "2" 53) 53) == ("3.7621956910836314", .lt)
#guard D (A (X "0.5" 53) 53) == ("1.1276259652063807", .lt)
#guard D (A (X "-0.3333333333333333" 53) 53) == ("1.0560718678299394", .gt)
#guard D (A (X "1.5" 53) 53) == ("2.352409615243247", .lt)
#guard D (A (X "-1.4" 53) 53) == ("2.1508984653931402", .lt)
#guard D (A (X "3.142857142857143" 53) 53) == ("11.606565803761965", .lt)
#guard D (A (X "10" 53) 53) == ("11013.232920103323", .lt)
#guard D (A (X "-100" 53) 53) == ("1.3440585709080678e43", .gt)
#guard D (A (X "0.001" 53) 53) == ("1.0000005000000416", .lt)
#guard D (A (X "-0.000000000001" 53) 53) == ("1.0", .lt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("1.0", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("1.0", .lt)
#guard D (A (X "-1.8669045833583425e-60" 53) 53)
  == ("1.0", .lt)
#guard D (A (X "30" 53) 53) == ("5343237290762.231", .gt)
#guard D (A (X "-37" 53) 53) == ("5859571186401306.0", .gt)
#guard D (A (X "700" 53) 53) == ("5.0711602736750225e303", .lt)
#guard D (A (X "1" 53) 53 .Floor) == ("1.5430806348152437", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("1.5430806348152437", .lt)
#guard D (A (X "1.5" 53) 53 .Floor) == ("2.352409615243247", .lt)
#guard D (A (X "-1.4" 53) 53 .Floor) == ("2.1508984653931402", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("1.0000005000000416", .lt)
#guard D (A (X "-100" 53) 53 .Floor) == ("1.3440585709080676e43", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("1.0", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("1.543080634815244", .gt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("1.543080634815244", .gt)
#guard D (A (X "1.5" 53) 53 .Ceiling) == ("2.3524096152432477", .gt)
#guard D (A (X "-1.4" 53) 53 .Ceiling) == ("2.1508984653931407", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("1.0000005000000418", .gt)
#guard D (A (X "-100" 53) 53 .Ceiling) == ("1.3440585709080678e43", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (A (X "1" 53) 20) == ("1.543081", .gt)
#guard D (A (X "1" 53) 1) == ("2.0", .gt)
#guard D (A (X "-1.5" 53) 2) == ("2.0", .lt)
#guard D (A (X "1.5" 53) 113) == ("2.3524096152432473257676679654416442", .gt)
#guard D (A (X "0.3333333333333333333333333333333333333333333333333333333333334" 200) 200) == ("1.0\
  56071867829939389526864708263983252525509287510443069879193\
  ", .lt)
#guard D (A (X "0.333333333333333333333333333333333333333333333333333333333333\
  4" 200) 10 .Floor) == ("1.055", .lt)
#guard D (A (X "10" 53) 120) == ("11013.23292010332313972137609043787997", .gt)
#guard cosh (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString (coshPrecRound (X "1" 200) 200 .Nearest).1 == "1.5430806348152437784779056207570616\
  82601529112365863704737402"
#guard toString (coshPrecRound (X "-1.5" 200) 200 .Nearest).1 == "2.3524096152432473257676679654416\
  44170173960748865373192758244"

-- evenness
private def even (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool := A (-x) p m == A x p m
#guard even (X "1.5" 53) 53 .Nearest && even (X "1.5" 53) 53 .Floor
#guard even (X "100" 53) 20 .Ceiling && even (h (X "1" 53) (-1000)) 53 .Ceiling

-- tiny arguments: just above `1`
private def tinyOk (x : AzFloat) : Bool :=
  A x 53 == (X "1" 53, .lt) && A x 53 .Floor == (X "1" 53, .lt) && A x 53 .Ceiling == (up, .gt)
    && A (-x) 53 .Ceiling == (up, .gt) && A x 1 .Ceiling == (X "2" 1, .gt)
#guard tinyOk (h (X "1" 53) (-100))
#guard tinyOk (h (X "1" 53) (-1000))
#guard tinyOk (h (X "3" 53) (-1073741824))
-- `cosh (2^(−26)) = 1 + 2^(−53) + …`: just above the midpoint
#guard D (A (h (X "1" 53) (-26)) 53) == ("1.0000000000000002", .gt)
#guard D (A (h (X "1" 53) (-26)) 53 .Floor) == ("1.0", .lt)
#guard D (A (h (X "1" 53) (-27)) 53) == ("1.0", .lt)

-- large arguments: `cosh x` rounds like `exp |x| / 2`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expPrecRound x p m
  A x p m == (h r.1 (-1), r.2) && A (-x) p m == (h r.1 (-1), r.2)
#guard big (X "1048576" 53) 53 .Nearest && big (X "1048576" 53) 53 .Floor
#guard big (X "15432098.625" 53) 20 .Ceiling && big (X "1000" 53) 113 .Nearest
