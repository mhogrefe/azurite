/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asec
import Azurite.AzFloat.Acos
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `asec`

The special values (`NaN`; `|x| < 1` gives `NaN`, including `0` and tiny arguments;
`asec (±∞) = π/2` in several modes; `asec 1 = 0` exactly; `asec (−1) = π`; `p = 0`), the
correctly rounded 53-bit values at `±2` (`π/3`, `2π/3`), `3/2`, `5/4`, the float nearest
`−7/5`, `100`, `−1000`, `10¹²`, `±(1 + 10⁻⁶)`, `22/7`, and the neighbours `±(1 + 2^(−52))` of
`±1`; agreement with `acos` of an exactly representable reciprocal; the directed modes; 1-, 2-,
20- and 113-bit results; 200-bit strings; `1 + 2^(−190)` at 200 bits (a result of size
`2^(−94)`); and huge arguments `±2^1000`, `±2^(2^30)` (results next to `π/2`, at no extra
cost).  References: an independent 1400-bit fixed-point evaluation of `arccos (1/x)` rounded
with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asecPrecRound x p m
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard A nan 53 == (nan, .eq)
#guard A zero 53 == (nan, .eq)
#guard A (F "1/2" 53) 53 == (nan, .eq)
#guard A (F "-9007199254740991/9007199254740992" 53) 53 == (nan, .eq)
#guard A (powerOf2 (AzInt.ofInt (-1073741824))) 53 == (nan, .eq)
#guard A (infinity true) 53 == (h piN (-1), .lt)
#guard A (infinity false) 53 == (h piN (-1), .lt)
#guard A (infinity false) 53 .Ceiling == (h piC (-1), .gt)
#guard A (F "1" 53) 53 == (zero, .eq)
#guard A (F "1" 200) 0 == (zero, .eq)
#guard A (F "-1" 53) 53 == (piN, .lt)
#guard A (F "-1" 53) 53 .Ceiling == (piC, .gt)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "2" 53) 53 == (F "2358079250676147/2251799813685248" 53, .gt)
#guard A (F "-2" 53) 53 == (F "2358079250676147/1125899906842624" 53, .gt)
#guard A (F "3/2" 53) 53 == (F "3787836551362729/4503599627370496" 53, .lt)
#guard A (F "5/4" 53) 53 == (F "5796142707547873/9007199254740992" 53, .lt)
#guard A (F "-7/5" 53) 53 == (F "2664328729219065/1125899906842624" 53, .gt)
#guard A (F "100" 53) 53 == (F "3514600502560509/2251799813685248" 53, .lt)
#guard A (F "-1000" 53) 53 == (F "7078741352406411/4503599627370496" 53, .lt)
#guard A (F "1000000000000" 53) 53 == (F "7074237752023937/4503599627370496" 53, .gt)
#guard A (F "1000001/1000000" 53) 53 == (F "6521906194937829/4611686018427387904" 53, .lt)
#guard A (F "-1000001/1000000" 53) 53 == (F "7071053227519193/2251799813685248" 53, .lt)
#guard A (F "22/7" 53) 53 == (F "2807961292152009/2251799813685248" 53, .lt)
#guard A (F "2" 53) 53 .Floor == (F "4716158501352293/4503599627370496" 53, .lt)
#guard A (F "-3/2" 53) 53 .Floor == (F "5180319476347075/2251799813685248" 53, .lt)
#guard A (F "2" 53) 53 .Ceiling == (F "2358079250676147/2251799813685248" 53, .gt)
#guard A (F "-3/2" 53) 53 .Ceiling == (F "1295079869086769/562949953421312" 53, .gt)
#guard A (F "2" 53) 20 == (F "549033/524288" 20, .lt)
#guard A (F "2" 53) 1 == (F "1" 1, .lt)
#guard A (F "3/2" 53) 113
  == (F "8734156432003856210285461333670863/10384593717069655257060992658440192" 113, .lt)
#guard A (F "-3/2" 53) 2 == (F "2" 2, .lt)
#guard A (F "2" 53) 53 == acosPrecRound (F "1/2" 53) 53 .Nearest
#guard A (F "-4" 53) 53 .Floor == acosPrecRound (F "-1/4" 53) 53 .Floor
#guard asec (F "2" 53) == (A (F "2" 53) 53).1
#guard (toString (asecPrecRound (F "2" 200) 200 .Nearest).1).startsWith
  "1.04719755119659774615421446109316762806572313312503527"
#guard (toString (asecPrecRound (F "-3/2" 200) 200 .Nearest).1).startsWith
  "2.30052398302186298268611835145307213749509061373526660"

-- next to `±1`
#guard A (F "4503599627370497/4503599627370496" 53) 53
  == (F "1592262918131443/75557863725914323419136" 53, .gt)
#guard A (F "-4503599627370497/4503599627370496" 53) 53
  == (F "7074237704575307/2251799813685248" 53, .lt)
#guard A (F "-4503599627370497/4503599627370496" 53) 53 .Ceiling
  == (F "1768559426143827/562949953421312" 53, .gt)
#guard A (F ("1569275433846670190958947355801916604025588861116008628225/"
    ++ "1569275433846670190958947355801916604025588861116008628224") 200) 200
  == (F ("1136276788042180458070828951474823657989790988021617205463999/"
    ++ "31828687130226345097944463881396533766429193"
    ++ "651030253916189694521162207808802136034115584") 200,
    .lt)

-- huge arguments: next to `π/2`
private def T : AzFloat := powerOf2 (AzInt.ofInt 1000)
#guard A T 53 == (h piN (-1), .lt)
#guard A T 53 .Ceiling == (h piC (-1), .gt)
#guard A (-T) 53 == (h piN (-1), .lt)
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard A huge 53 == (h piN (-1), .lt)
#guard A (-huge) 53 .Ceiling == (h piC (-1), .gt)
