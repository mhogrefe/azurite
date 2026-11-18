/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Csch
import Azurite.AzFloat.Exp
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `csch x`

The special values (`NaN`, `±∞ ↦ 0`, `csch 0 = +∞`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `700` in three modes, 1-, 2-, 20-, 113-, 120- and 200-bit results,
200-bit strings, oddness, tiny arguments `±2^(−1000)`, `±2^(−2^30)`, `±3·2^(−2^30)` (the value
is just inside `1/x`, at no cost), and large arguments (`±2^20`, where `csch x` rounds like
`±2 exp (−|x|)`).  References: an independent 6000-bit fixed-point evaluation of
`2/(e^x − e^(−x))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := X "0.9999999999999999" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cschPrecRound x p m

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("0.0", .eq)
#guard D (A (infinity false) 53) == ("0.0", .eq)
#guard D (A (infinity false) 0) == ("0.0", .eq)
#guard D (A zero 53) == ("Infinity", .eq)
#guard D (A zero 0) == ("Infinity", .eq)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "1" 53) 53) == ("0.8509181282393216", .gt)
#guard D (A (X "-1" 53) 53) == ("-0.8509181282393216", .lt)
#guard D (A (X "2" 53) 53) == ("0.2757205647717832", .lt)
#guard D (A (X "0.5" 53) 53) == ("1.9190347513349437", .gt)
#guard D (A (X "-0.3333333333333333" 53) 53) == ("-2.9451562666948146", .lt)
#guard D (A (X "1.5" 53) 53) == ("0.4696424405952246", .gt)
#guard D (A (X "-1.4" 53) 53) == ("-0.525126929342733", .gt)
#guard D (A (X "3.142857142857143" 53) 53) == ("0.08647970651862788", .lt)
#guard D (A (X "10" 53) 53) == ("0.00009079985971212217", .gt)
#guard D (A (X "-100" 53) 53) == ("-7.440151952041672e-44", .lt)
#guard D (A (X "0.001" 53) 53) == ("999.9998333333527", .lt)
#guard D (A (X "-0.000000000001" 53) 53) == ("-1.0e12", .gt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("1125899906842624.0", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("1.2676506002282294e30", .gt)
#guard D (A (X "-1.8669045833583425e-60" 53) 53)
  == ("-5.356460147529967e59", .gt)
#guard D (A (X "30" 53) 53) == ("1.871524593768035e-13", .gt)
#guard D (A (X "-37" 53) 53) == ("-1.7066095251488132e-16", .lt)
#guard D (A (X "700" 53) 53) == ("1.971935308751954e-304", .lt)
#guard D (A (X "1" 53) 53 .Floor) == ("0.8509181282393214", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-0.8509181282393216", .lt)
#guard D (A (X "1.5" 53) 53 .Floor) == ("0.46964244059522453", .lt)
#guard D (A (X "-1.4" 53) 53 .Floor) == ("-0.5251269293427331", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("999.9998333333527", .lt)
#guard D (A (X "-100" 53) 53 .Floor) == ("-7.440151952041672e-44", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("1.2676506002282293e30", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("0.8509181282393216", .gt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("-0.8509181282393214", .gt)
#guard D (A (X "1.5" 53) 53 .Ceiling) == ("0.4696424405952246", .gt)
#guard D (A (X "-1.4" 53) 53 .Ceiling) == ("-0.525126929342733", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("999.9998333333529", .gt)
#guard D (A (X "-100" 53) 53 .Ceiling) == ("-7.440151952041671e-44", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling)
  == ("1.2676506002282294e30", .gt)
#guard D (A (X "1" 53) 20) == ("0.850918", .lt)
#guard D (A (X "1" 53) 1) == ("1.0", .gt)
#guard D (A (X "-1.5" 53) 2) == ("-0.5", .lt)
#guard D (A (X "1.5" 53) 113) == ("0.46964244059522458472956443188701363", .gt)
#guard D (A (X "0.3333333333333333333333333333333333333333333333333333333333334" 200) 200)
  == ("2.945156266694814347645586003495165676460850560888490147110876", .lt)
#guard D (A (X "0.3333333333333333333333333333333333333333333333333333333333334" 200) 10 .Floor)
  == ("2.94", .lt)
#guard D (A (X "10" 53) 120) == ("0.0000907998597121221628337364936072913703", .lt)
#guard csch (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString ((cschPrecRound (X "1" 200) 200 .Nearest).1)
  == "0.8509181282393215451338427632871752841817246609103396169904214"
#guard toString ((cschPrecRound (X "-1.5" 200) 200 .Nearest).1)
  == "-0.4696424405952245847295644318870136153153233104478505088154448"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 53 .Nearest && odd (X "1.5" 53) 53 .Floor
#guard odd (X "100" 53) 20 .Ceiling && odd (X "0.001" 53) 113 .Floor
#guard odd (h (X "1" 53) (-1000)) 53 .Ceiling && odd (X "1048576" 53) 53 .Floor

-- tiny arguments: just inside `1/x`
private def tinyOk (k : Int) : Bool :=
  let x := h (X "1" 53) (-k)
  let y := h (X "1" 53) k
  A x 53 == (y, .gt) && A x 53 .Ceiling == (y, .gt) && A x 53 .Floor == (h dn k, .lt)
    && A (-x) 53 == (-y, .lt) && A (-x) 53 .Floor == (-y, .lt)
    && A (-x) 53 .Ceiling == (-(h dn k), .gt)
#guard tinyOk 100
#guard tinyOk 1000
#guard tinyOk 1073741824
private def t3 : AzFloat := h (X "3" 53) (-1073741824)
#guard A t3 53 == (h (X "0.3333333333333333" 53) 1073741824, .lt)
#guard A t3 53 .Ceiling == (h (X "0.33333333333333337" 53) 1073741824, .gt)
#guard A (-t3) 53 .Floor == (-(h (X "0.33333333333333337" 53) 1073741824), .lt)

-- large arguments: `csch x` rounds like `2 exp (−x)`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expPrecRound (-x) p m
  A x p m == (h r.1 1, r.2)
#guard big (X "1048576" 53) 53 .Nearest && big (X "1048576" 53) 53 .Floor
#guard big (X "15432098.625" 53) 20 .Ceiling && big (X "1000" 53) 113 .Nearest
