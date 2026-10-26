/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowInt
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `x^n` with an integer `n`

Special values (`x^0 = 1`, the powers of `0` and `±∞`, `NaN`), exact dyadic powers
(`(3/2)^10 = 59049/1024`, `(−3/2)^3`, `2^100`, `2^(−100)`, `(−1/2)^(−3) = −8`), correctly rounded
inexact powers (`(3/2)^(−3) = 8/27`, `(−3/2)^(−3) = −8/27`, `x^5` and `x^(−7)` for the
53-bit `x ≈ 1/3`), the directed modes and the comparison results.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def N (i : Int) : AzInt := AzInt.ofInt i
private def E (x : AzFloat) (i : Int) (p : Nat) (m : RoundingMode := .Nearest) :=
  powIntPrecRound x (N i) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard E nan 3 53 == (nan, .eq)
#guard E nan 0 53 == (nan, .eq)
#guard E pinf 0 53 == (F "1" 53, .eq)
#guard E zero 0 53 == (F "1" 53, .eq)
#guard E (F "3/2" 53) 0 53 == (F "1" 53, .eq)
#guard E (F "3/2" 53) 0 0 == (nan, .eq)
#guard E pinf 3 53 == (infinity true, .eq)
#guard E pinf 2 53 == (infinity true, .eq)
#guard E ninf 3 53 == (infinity false, .eq)
#guard E ninf 2 53 == (infinity true, .eq)
#guard E pinf (-1) 53 == (zero, .eq)
#guard E ninf (-2) 53 == (zero, .eq)
#guard E zero 5 53 == (zero, .eq)
#guard E zero (-5) 53 == (infinity true, .eq)
#guard E zero (-5) 0 == (infinity true, .eq)
#guard E (F "3/2" 53) 3 0 == (nan, .eq)
#guard powInt nan (N 2) == nan
#guard powInt ninf (N 3) == infinity false
#guard powInt zero (N (-1)) == infinity true

-- exact dyadic powers
#guard E (F "3/2" 53) 10 53 == (F "59049/1024" 53, .eq)
#guard E (F "-3/2" 53) 3 53 == (F "-27/8" 53, .eq)
#guard E (F "-3/2" 53) 4 53 == (F "81/16" 53, .eq)
#guard E (F "2" 53) 100 53 == (F "1267650600228229401496703205376" 53, .eq)
#guard E (F "2" 53) (-100) 53 == (F "1/1267650600228229401496703205376" 53, .eq)
#guard E (F "-1/2" 53) (-3) 53 == (F "-8" 53, .eq)
#guard E (F "-1/2" 53) (-4) 53 == (F "16" 53, .eq)
#guard E (F "3/2" 53) 10 4 == ofAzRatRound (Q "59049/1024") 4 .Nearest
#guard E (F "3/2" 53) 10 4 .Floor == ofAzRatRound (Q "59049/1024") 4 .Floor
#guard E (F "3" 2) 40 20 == ofAzRatRound (Q "12157665459056928801") 20 .Nearest
#guard powInt (F "3/2" 53) (N 10) == F "59049/1024" 53
#guard powInt (F "1" 1) (N 1000) == one
#guard powInt (F "-1" 1) (N 1001) == -one

-- inexact rational powers, correctly rounded
#guard E (F "3/2" 53) (-3) 53 == ofAzRatRound (Q "8/27") 53 .Nearest
#guard E (F "3/2" 53) (-3) 53 .Floor == ofAzRatRound (Q "8/27") 53 .Floor
#guard E (F "3/2" 53) (-3) 53 .Ceiling == ofAzRatRound (Q "8/27") 53 .Ceiling
#guard E (F "-3/2" 53) (-3) 53 == ofAzRatRound (Q "-8/27") 53 .Nearest
#guard E (F "-3/2" 53) (-3) 53 .Floor == ofAzRatRound (Q "-8/27") 53 .Floor
#guard E (F "-3/2" 53) (-3) 53 .Up == ofAzRatRound (Q "-8/27") 53 .Up
#guard E (F "-3/2" 53) (-4) 53 .Down == ofAzRatRound (Q "16/81") 53 .Down
private def third : AzFloat := F "1/3" 53
private def thirdPow5 : AzRat :=
  (Q ("7807150576395835470198883438668591163552799368408133204130536781000490181519301/" ++
    "18971375900641885458197870183823426822679754287618550012224730563856487160207114" ++
    "24"))
private def thirdPowNeg7 : AzRat :=
  (Q ("61565634681866373769186000156474396570437092610102260418669208444133940267964391" ++
    "5803347910232576806887603562348544/281507245916169866694701407600756551143727107" ++
    "026502996800535943467187880362316312424430368609656410814508032221"))
#guard E third 5 53 == ofAzRatRound thirdPow5 53 .Nearest
#guard E third 5 100 .Ceiling == ofAzRatRound thirdPow5 100 .Ceiling
#guard E third (-7) 53 == ofAzRatRound thirdPowNeg7 53 .Nearest
#guard E third (-7) 150 .Floor == ofAzRatRound thirdPowNeg7 150 .Floor
#guard E (-third) (-7) 150 .Ceiling == ofAzRatRound (-thirdPowNeg7) 150 .Ceiling
#guard powInt third (N (-7)) == ofAzRat thirdPowNeg7 53

-- the comparison results
#guard (E (F "3/2" 53) (-3) 53 .Floor).2 == .lt
#guard (E (F "3/2" 53) (-3) 53 .Ceiling).2 == .gt
#guard (E (F "-3/2" 53) (-3) 53 .Floor).2 == .lt
#guard (E (F "-3/2" 53) (-3) 53 .Ceiling).2 == .gt
#guard partialCompare (E (F "-3/2" 53) (-3) 53 .Floor).1 (E (F "-3/2" 53) (-3) 53 .Ceiling).1
  == some .lt
