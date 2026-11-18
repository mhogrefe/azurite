/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pow
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `x^n` with an integer `n`

Special values (`x^0 = 1`, the powers of `0` and `±∞`, `NaN`), exact dyadic powers
(`(3/2)^10 = 59049/1024`, `(−3/2)^3`, `2^100`, `2^(−100)`, `(−1/2)^(−3) = −8`), correctly rounded
inexact powers (`(3/2)^(−3) = 8/27`, `(−3/2)^(−3) = −8/27`, `x^5` and `x^(−7)` for the
53-bit `x ≈ 1/3`), the directed modes and the comparison results; huge exponents through Ziv's
loop (the Malachite oracle's cases, each formerly forming `m^|n|` exactly, over 10 s) and the
Ziv path against the exact path.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def N (i : Int) : AzInt := AzInt.ofInt i
private def E (x : AzFloat) (i : Int) (p : Nat) (m : RoundingMode := .Nearest) :=
  powIntPrecRound x (N i) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard D (E nan 3 53) == ("NaN", .eq)
#guard D (E nan 0 53) == ("NaN", .eq)
#guard D (E pinf 0 53) == ("1.0", .eq)
#guard D (E zero 0 53) == ("1.0", .eq)
#guard D (E (X "1.5" 53) 0 53) == ("1.0", .eq)
#guard D (E (X "1.5" 53) 0 0) == ("NaN", .eq)
#guard D (E pinf 3 53) == ("Infinity", .eq)
#guard D (E pinf 2 53) == ("Infinity", .eq)
#guard D (E ninf 3 53) == ("-Infinity", .eq)
#guard D (E ninf 2 53) == ("Infinity", .eq)
#guard D (E pinf (-1) 53) == ("0.0", .eq)
#guard D (E ninf (-2) 53) == ("0.0", .eq)
#guard D (E zero 5 53) == ("0.0", .eq)
#guard D (E zero (-5) 53) == ("Infinity", .eq)
#guard D (E zero (-5) 0) == ("Infinity", .eq)
#guard D (E (X "1.5" 53) 3 0) == ("NaN", .eq)
#guard toString (powInt nan (N 2)) == "NaN"
#guard toString (powInt ninf (N 3)) == "-Infinity"
#guard toString (powInt zero (N (-1))) == "Infinity"

-- exact dyadic powers
#guard D (E (X "1.5" 53) 10 53) == ("57.6650390625", .eq)
#guard D (E (X "-1.5" 53) 3 53) == ("-3.375", .eq)
#guard D (E (X "-1.5" 53) 4 53) == ("5.0625", .eq)
#guard D (E (X "2" 53) 100 53) == ("1.2676506002282294e30", .eq)
#guard D (E (X "2" 53) (-100) 53) == ("7.888609052210118e-31", .eq)
#guard D (E (X "-0.5" 53) (-3) 53) == ("-8.0", .eq)
#guard D (E (X "-0.5" 53) (-4) 53) == ("16.0", .eq)
#guard D (E (X "1.5" 53) 10 4) == ("56.0", .lt)
#guard D (E (X "1.5" 53) 10 4 .Floor) == ("56.0", .lt)
#guard D (E (X "3" 2) 40 20) == ("1.215766e19", .lt)
#guard toString (powInt (X "1.5" 53) (N 10)) == "57.6650390625"
#guard toString (powInt (X "1" 1) (N 1000)) == "1.0"
#guard toString (powInt (X "-1" 1) (N 1001)) == "-1.0"

-- inexact rational powers, correctly rounded
#guard D (E (X "1.5" 53) (-3) 53) == ("0.2962962962962963", .lt)
#guard D (E (X "1.5" 53) (-3) 53 .Floor) == ("0.2962962962962963", .lt)
#guard D (E (X "1.5" 53) (-3) 53 .Ceiling) == ("0.29629629629629634", .gt)
#guard D (E (X "-1.5" 53) (-3) 53) == ("-0.2962962962962963", .gt)
#guard D (E (X "-1.5" 53) (-3) 53 .Floor) == ("-0.29629629629629634", .lt)
#guard D (E (X "-1.5" 53) (-3) 53 .Up) == ("-0.29629629629629634", .lt)
#guard D (E (X "-1.5" 53) (-4) 53 .Down) == ("0.19753086419753085", .lt)
private def third : AzFloat := X "0.3333333333333333" 53
private def thirdPow5 : AzRat :=
  (Q ("7807150576395835470198883438668591163552799368408133204130536781000490181519301/" ++
    "18971375900641885458197870183823426822679754287618550012224730563856487160207114" ++
    "24"))
private def thirdPowNeg7 : AzRat :=
  (Q ("61565634681866373769186000156474396570437092610102260418669208444133940267964391" ++
    "5803347910232576806887603562348544/281507245916169866694701407600756551143727107" ++
    "026502996800535943467187880362316312424430368609656410814508032221"))
#guard D (E third 5 53) == ("0.004115226337448558", .lt)
#guard D (E third 5 100 .Ceiling) == ("0.00411522633744855852857713515931", .gt)
#guard D (E third (-7) 53) == ("2187.000000000001", .gt)
#guard D (E third (-7) 150 .Floor) == ("2187.000000000000849820214199326262565262579535", .lt)
#guard D (E (-third) (-7) 150 .Ceiling) == ("-2187.000000000000849820214199326262565262579535", .gt)
#guard toString (powInt third (N (-7))) == "2187.000000000001"

-- the comparison results
#guard (E (X "1.5" 53) (-3) 53 .Floor).2 == .lt
#guard (E (X "1.5" 53) (-3) 53 .Ceiling).2 == .gt
#guard (E (X "-1.5" 53) (-3) 53 .Floor).2 == .lt
#guard (E (X "-1.5" 53) (-3) 53 .Ceiling).2 == .gt
#guard partialCompare (E (X "-1.5" 53) (-3) 53 .Floor).1 (E (X "-1.5" 53) (-3) 53 .Ceiling).1
  == some .lt

-- huge exponents: Ziv's loop instead of the exact `m^|n|`
private def H (s : String) (i : Int) (p : Nat) (m : RoundingMode := .Nearest) : String × Ordering :=
  let r := E (ofHexString s).get! i p m
  (toHexString r.1, r.2)
#guard H "0xd37634d.effc4816e65732919e1337bdf6#131" 1247529 19 == ("0x2.c41c8E+8646702#19", .gt)
#guard H "-0x2.c68E+15#13" 12805738 31 == ("0x2.0f3ffad0E+196800793#31", .lt)
#guard H "0x4.000000000000001fc0003ffffffffffffff00007E-10#163" 2096128 163 ==
  ("0x1.0000000000fde041ffc07de27f83f6a5bebb8f49cE-19913216#163", .gt)
#guard E (X "3" 2) 100000 10 == powIntExactPrecRound (X "3" 2) (N 100000) 10 .Nearest
#guard E (X "-3" 2) (-10001) 30 .Floor == powIntExactPrecRound (X "-3" 2) (N (-10001)) 30 .Floor
#guard E (X "-3" 2) 10001 30 .Ceiling == powIntExactPrecRound (X "-3" 2) (N 10001) 30 .Ceiling
-- odd part `1`: no powering over the bits of a huge `n`
#guard D (E (X "-1" 1) (2 ^ (2 ^ 20) + 1) 10) == ("-1.0", .eq)
#guard E (X "-0.5" 1) (2 ^ 20 + 1) 10 == (X "-1" 10 <<< AzInt.ofInt (-(2 ^ 20 + 1)), .eq)

-- a huge exponent through Ziv's loop: the starting precision is logarithmic in the size of `n`
-- (`powW₀`); reference from 700-digit decimal arithmetic
private def big10 : AzFloat × Ordering :=
  let sh : Int := (Q ("16014397907901874572694325517271509893986724198514539137838752")).num.toNat
  ((X "6652583142272300" 53) <<< AzInt.ofInt (sh), .gt)
private def big10Neg : AzFloat × Ordering :=
  let sh : Int := (Q ("16014397907901874572694325517271509893986724198514539137838857")).num.toNat
  ((X "6097604244814858" 53) <<< AzInt.ofInt (-sh), .gt)
#guard E (X "10" 53) (3 * 2 ^ 200) 53 == big10
#guard E (X "10" 53) (-(3 * 2 ^ 200)) 53 == big10Neg
#guard E (X "-10" 53) (3 * 2 ^ 200) 53 == big10
