/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.ExtendedSRemS
import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.ToString

/-!
# BPR Example 8.25: a signed remainder sequence

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.3.1.

The signed remainder sequence (Algorithm 8.19) of

`P = 9X¹³ − 18X¹¹ − 33X¹⁰ + 102X⁸ + 7X⁷ − 36X⁶ − 122X⁵ + 49X⁴ + 93X³ − 42X² − 18X + 9`

and its derivative `P'`, computed over `AzRat` by `sRemSList`. The sequence drops
exactly one degree at each step (13, 12, …, 5) and then reaches `0`, so it
terminates at the degree-`5` polynomial `SRemS₈`, which is (up to a scalar) the
gcd of `P` and `P'`: `P` is not squarefree. Each term is pinned down by a
`#guard` on its `toString`.
-/

namespace Azurite.BPR.Chapter8.Example_8_25

open Azurite.AzPolynomial

/-- The example polynomial `P`, built with `parseAzPolynomial`. -/
def P : AzPolynomial AzRat :=
  (parseAzPolynomial (R := AzRat)
    "9*x^13-18*x^11-33*x^10+102*x^8+7*x^7-36*x^6-122*x^5+49*x^4+93*x^3-42*x^2-18*x+9").get!

/-- Its derivative `P'`. -/
def P' : AzPolynomial AzRat := P.derivative

/-- The signed remainder sequence `SRemS₀, …, SRemS₉` of `P` and `P'`
    (Algorithm 8.19), computed in a single pass by `sRemSList`. -/
def srs : List (AzPolynomial AzRat) := sRemSList P P' 10

-- `SRemS₀ = P` (degree 13).
#guard toString srs[0]! ==
  "9*x^13-18*x^11-33*x^10+102*x^8+7*x^7-36*x^6-122*x^5+49*x^4+93*x^3-42*x^2-18*x+9"
-- `SRemS₁ = P'` (degree 12).
#guard toString srs[1]! ==
  "117*x^12-198*x^10-330*x^9+816*x^7+49*x^6-216*x^5-610*x^4+196*x^3+279*x^2-84*x-18"
-- `SRemS₂` (degree 11).
#guard toString srs[2]! ==
  "36/13*x^11+99/13*x^10-510/13*x^8-42/13*x^7+252/13*x^6+976/13*x^5-441/13*x^4-930/13*x^3+462/13*x^2+216/13*x-9"
-- `SRemS₃` (degree 10).
#guard toString srs[3]! ==
  "-10989/16*x^10-2655/2*x^9+35373/8*x^8+3027/8*x^7+3483/4*x^6-39761/4*x^5+24463/16*x^4+76939/8*x^3-29649/8*x^2-8907/4*x+17019/16"
-- `SRemS₄` (degree 9).
#guard toString srs[4]! ==
  "-2228672/165649*x^9+11497792/496947*x^8-758720/496947*x^7+8858368/496947*x^6-72291808/1490841*x^5-14747008/1490841*x^4+81689728/1490841*x^3-7130848/496947*x^2-6742336/496947*x+910304/165649"
-- `SRemS₅` (degree 8).
#guard toString srs[5]! ==
  "-900202097355/4850565316*x^8+4790758416807/19402261264*x^7-871080009261/38804522528*x^6+15288527907631/38804522528*x^5-11178436305883/19402261264*x^4-5169096757231/38804522528*x^3+13117087511715/38804522528*x^2-871080009261/38804522528*x-1515244576329/38804522528"
-- `SRemS₆` (degree 7).
#guard toString srs[6]! ==
  "-3841677139249510908/543561530761725025*x^7+6180347358405238902/543561530761725025*x^6-2388192201565258842/543561530761725025*x^5+8963913324915525452/543561530761725025*x^4-14420810502945557438/543561530761725025*x^3+346154266213885278/108712306152345005*x^2+6180347358405238902/543561530761725025*x-2388192201565258842/543561530761725025"
-- `SRemS₇` (degree 6).
#guard toString srs[7]! ==
  "-6648854900739944448789496725/676140352527579535315696712*x^6+4693072116514804907890170825/676140352527579535315696712*x^5+15513994768393203713842159025/676140352527579535315696712*x^3-10950501605201211451743731925/676140352527579535315696712*x^2-6648854900739944448789496725/676140352527579535315696712*x+4693072116514804907890170825/676140352527579535315696712"
-- `SRemS₈` (degree 5) — the last nonzero term, i.e. a gcd of `P` and `P'`.
#guard toString srs[8]! ==
  "-200117670554781699308164692478544184/1807309302290980501324553958871415645*x^5+66705890184927233102721564159514728/258187043184425785903507708410202235*x^2-200117670554781699308164692478544184/1807309302290980501324553958871415645"
-- `SRemS₉ = 0`: the sequence terminates.
#guard toString srs[9]! == "0"

end Azurite.BPR.Chapter8.Example_8_25
