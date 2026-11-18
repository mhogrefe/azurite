/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asech
import Azurite.AzFloat.Ln
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `asech x`

The special values (`NaN`; `±∞ ↦ NaN`; `NaN` for `x < 0` and `x > 1`; `asech 0 = +∞`;
`asech 1 = 0`; `p = 0`), the correctly rounded 53-bit values from `2^(−200)` to `1 − 2^(−53)`
in three modes (next to `1` the value is `≈ √(2 (1 − x))`), 1-, 2-, 20-, 113-, 120- and
200-bit results, 200-bit strings, and tiny arguments
`2^(−2^30)`, `3·2^(−2^30)` (where `asech x` rounds like `ln (2/x)`).  References: an
independent 6000-bit fixed-point evaluation of `ln (1/x + √(1/x² − 1))` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def big1 : AzFloat := X "0.3333333333333333333333333333333333333333333333333333333333334\
  " 200
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asechPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("NaN", .eq)
#guard D (A (infinity false) 53) == ("NaN", .eq)
#guard D (A zero 53) == ("Infinity", .eq)
#guard D (A zero 0) == ("Infinity", .eq)
#guard D (A (X "1" 53) 53) == ("0.0", .eq)
#guard D (A (X "1" 200) 1 .Floor) == ("0.0", .eq)
#guard D (A (X "1" 53) 0) == ("0.0", .eq)
#guard D (A (X "2" 53) 53) == ("NaN", .eq)
#guard D (A (X "1.0000000000000002" 53) 53) == ("NaN", .eq)
#guard D (A (h (X "1" 53) 1000) 53) == ("NaN", .eq)
#guard D (A (X "-0.5" 53) 53) == ("NaN", .eq)
#guard D (A (X "-1" 53) 53) == ("NaN", .eq)
#guard D (A (X "-3" 53) 53) == ("NaN", .eq)
#guard D (A (h (X "-1" 53) (-1000)) 53) == ("NaN", .eq)
#guard D (A (X "0.5" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "0.5" 53) 53) == ("1.3169578969248168", .gt)
#guard D (A (X "0.3333333333333333" 53) 53) == ("1.762747174039086", .lt)
#guard D (A (X "0.2857142857142857" 53) 53) == ("1.9248473002384139", .gt)
#guard D (A (X "0.75" 53) 53) == ("0.7953654612239056", .lt)
#guard D (A (X "0.99" 53) 53) == ("0.14201444074607714", .gt)
#guard D (A (X "0.999999" 53) 53) == ("0.0014142141516494595", .gt)
#guard D (A (X "0.9999999999999999" 53) 53) == ("1.4901161193847656e-8", .lt)
#guard D (A (X "0.9999999999999998" 53) 53) == ("2.1073424255447017e-8", .lt)
#guard D (A (X "0.001" 53) 53) == ("7.600902209541989", .gt)
#guard D (A (X "0.000000000001" 53) 53) == ("28.324168296488494", .gt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("35.35050620855721", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("70.00786523655448", .gt)
#guard D (A (X "1.8669045833583425e-60" 53) 53)
  == ("138.2239710038809", .gt)
#guard D (A (X "0.5" 53) 53 .Floor) == ("1.3169578969248166", .lt)
#guard D (A (X "0.99" 53) 53 .Floor) == ("0.1420144407460771", .lt)
#guard D (A (X "0.9999999999999999" 53) 53 .Floor) == ("1.4901161193847656e-8", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("7.600902209541988", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("70.00786523655447", .lt)
#guard D (A (X "0.5" 53) 53 .Ceiling) == ("1.3169578969248168", .gt)
#guard D (A (X "0.99" 53) 53 .Ceiling) == ("0.14201444074607714", .gt)
#guard D (A (X "0.9999999999999999" 53) 53 .Ceiling) == ("1.490116119384766e-8", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("7.600902209541989", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling) == ("70.00786523655448", .gt)
#guard D (A (X "0.5" 53) 20) == ("1.316957", .lt)
#guard D (A (X "0.5" 53) 1) == ("1.0", .lt)
#guard D (A (X "0.75" 53) 2) == ("0.8", .lt)
#guard D (A (X "0.75" 53) 113) == ("0.7953654612239056305278909331478063", .lt)
#guard D (A big1 200)
  == ("1.76274717403908605046521864995958461805632065652327082150659", .lt)
#guard D (A big1 10 .Floor) == ("1.762", .lt)
#guard D (A (X "0.875" 53) 120) == ("0.5283553629664819497313951111948398535", .gt)
#guard asech (X "0.5" 53) == (A (X "0.5" 53) 53).1
#guard toString (asechPrecRound (X "0.5" 200) 200 .Nearest).1
  == "1.316957896924816708625046347307968444026981971467516479768473"
#guard toString (asechPrecRound (X "0.75" 200) 200 .Nearest).1
  == "0.795365461223905630527890933147806300976582563714367134653302"

-- tiny arguments: `asech x` rounds like `ln (2/x)`; for `x = 2^(−k)` that is `(k + 1) ln 2`
private def tiny (x y : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  A x p m == lnPrecRound y p m
#guard tiny (h (X "1" 53) (-1073741824)) (h (X "1" 53) 1073741825) 53 .Nearest
#guard tiny (h (X "1" 53) (-1073741824)) (h (X "1" 53) 1073741825) 53 .Floor
#guard tiny (h (X "1" 53) (-100000)) (h (X "1" 53) 100001) 113 .Ceiling
