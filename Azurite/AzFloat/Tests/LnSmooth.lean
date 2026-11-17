/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnSmooth
import Azurite.AzFloat.Ln
import Azurite.AzFloat.EulerGamma

/-!
# Tests for the logarithm of integers with no prime factor above `7`

`lnSmoothBracket` against the correctly rounded `ln` of the same integer (the bracket must
contain it and be narrow), at several precisions; the factor search `smoothExps`, `isSmooth`,
`nextSmooth`; the single series `atanhInvBracket`.
-/

open Azurite Azurite.AzFloat

private def N (n : Nat) : AzFloat := ofAzNat (AzNat.ofNat n)

/-- The bracket of `ln (2^a 3^b 5^c 7^d)` at `k` bits contains `ln` rounded down and up at
`k − 8` bits or lies within their span, and is at most `2^(−k)` wide. -/
private def good (a b c d k : Nat) : Bool :=
  let B := lnSmoothBracket a b c d k
  let x := N (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d)
  let lo := (lnPrecRound x (k - 8) .Floor).1
  let hi := (lnPrecRound x (k - 8) .Ceiling).1
  le B.1 hi && le lo B.2 && lt B.1 B.2
    && le (subPrecRound B.2 B.1 32 .Ceiling).1 (powerOf2 (-(AzNat.ofNat k).toAzInt))

#guard good 1 0 0 0 64
#guard good 0 1 0 0 64
#guard good 0 0 1 0 64
#guard good 0 0 0 1 64
#guard good 1 0 0 0 300
#guard good 0 1 0 0 300
#guard good 0 0 1 0 300
#guard good 0 0 0 1 300
#guard good 6 0 0 0 90
#guard good 1 3 0 0 90
#guard good 3 2 1 1 200
#guard good 5 2 0 2 1000
#guard good 10 0 3 0 2500
#guard good 17 5 4 3 128
-- `ln 1`: every coefficient vanishes
#guard lnSmoothBracket 0 0 0 0 64 == (zero, zero)

-- the single series: `2 atanh (1/3) = ln 2`
#guard
  let A := atanhInvBracket 3 100
  le (A.1 <<< AzInt.ofInt 1) (lnPrecRound (N 2) 90 .Ceiling).1
    && le (lnPrecRound (N 2) 90 .Floor).1 (A.2 <<< AzInt.ofInt 1) && lt A.1 A.2
#guard atanhInvTerms 7 50 == 5

-- the factor search
#guard smoothExps 1 == (0, 0, 0, 0, 1)
#guard smoothExps 0 == (0, 0, 0, 0, 0)
#guard smoothExps 64 == (6, 0, 0, 0, 1)
#guard smoothExps 2520 == (3, 2, 1, 1, 1)
#guard smoothExps 22 == (1, 0, 0, 0, 11)
#guard smoothExps (2 ^ 40 * 3 ^ 20 * 13) == (40, 20, 0, 0, 13)
#guard (List.range 12).map isSmooth
  == [false, true, true, true, true, true, true, true, true, true, true, false]
#guard !isSmooth 11 && !isSmooth 13 && !isSmooth 121 && isSmooth 14700
#guard nextSmooth 1 == 1 && nextSmooth 11 == 12 && nextSmooth 52 == 54
#guard nextSmooth 715 == 720 && nextSmooth 14015 == 14112
#guard (List.range 3000).all fun n => n ≤ nextSmooth n ∧ (n = 0 ∨ isSmooth (nextSmooth n))

-- the dispatch of `lnNatBracket`: both paths enclose the same number
private def lnOverlap (n k : Nat) : Bool :=
  let a := lnNatBracket n k
  let b := lnBracketOf (N n) k
  le a.1 b.2 && le b.1 a.2
#guard lnOverlap 2 80 && lnOverlap 64 80 && lnOverlap 4096 300 && lnOverlap 54 80
#guard lnOverlap 11 80 && lnOverlap 143 200 && lnOverlap 14112 300
#guard lnNatBracket 1 80 == (zero, zero)
#guard lnNatBracket 11 80 == lnBracketOf (N 11) 80
