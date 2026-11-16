/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acos
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acos`

The special values (`NaN`; `±∞` and `|x| > 1` give `NaN`; `arccos 1 = 0` exactly;
`arccos 0 = π/2` and `arccos (−1) = π` in every mode; `p = 0`), the correctly rounded 53-bit
values at `±1/2`, the floats nearest `1/3`, `−7/10`, `3/4`, `9/10`, `99/100`, `±(1 − 10⁻⁶)`,
`5/7`, small arguments of both signs, and the neighbours `±(1 − 2^(−53))` of `±1`; the directed
modes; 1-, 2-, 20- and 113-bit results; 200-bit strings; `1 − 2^(−190)` at 200 bits (a result
of size `2^(−94)`); and tiny arguments `±2^(−200)`, `±2^(−2^30)` (results next to `π/2`, at no
extra cost).  References: an independent 1400-bit fixed-point evaluation of
`π/2 − arctan (x/√(1 − x²))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acosPrecRound x p m
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (nan, .eq)
#guard A (infinity false) 53 == (nan, .eq)
#guard A (F "2" 53) 53 == (nan, .eq)
#guard A (F "-3/2" 53) 53 == (nan, .eq)
#guard A (F "9007199254740993/9007199254740992" 54) 53 == (nan, .eq)
#guard A (powerOf2 (AzInt.ofInt 1073741824)) 53 == (nan, .eq)
#guard A (F "1" 53) 53 == (zero, .eq)
#guard A (F "1" 200) 0 == (zero, .eq)
#guard A zero 53 == (h piN (-1), .lt)
#guard A zero 53 .Ceiling == (h piC (-1), .gt)
#guard A zero 0 == (nan, .eq)
#guard A (F "-1" 53) 53 == (piN, .lt)
#guard A (F "-1" 53) 53 .Ceiling == (piC, .gt)
#guard A (F "1/2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1/2" 53) 53 == (F "2358079250676147/2251799813685248" 53, .gt)
#guard A (F "-1/2" 53) 53 == (F "2358079250676147/1125899906842624" 53, .gt)
#guard A (F "1/3" 53) 53 == (F "1385937093311029/1125899906842624" 53, .gt)
#guard A (F "-7/10" 53) 53 == (F "5283158814414321/2251799813685248" 53, .lt)
#guard A (F "3/4" 53) 53 == (F "6509811378280789/9007199254740992" 53, .gt)
#guard A (F "9/10" 53) 53 == (F "1015622090769875/2251799813685248" 53, .lt)
#guard A (F "99/100" 53) 53 == (F "637437119322107/4503599627370496" 53, .gt)
#guard A (F "999999/1000000" 53) 53 == (F "3260954728126347/2305843009213693952" 53, .gt)
#guard A (F "-999999/1000000" 53) 53 == (F "3535526612963377/1125899906842624" 53, .lt)
#guard A (F "1/1024" 53) 53 == (F "7069839704818285/4503599627370496" 53, .lt)
#guard A (F "-1/1000000000" 53) 53 == (F "884279719566505/562949953421312" 53, .gt)
#guard A (F "5/7" 53) 53 == (F "3491160587180621/4503599627370496" 53, .gt)
#guard A (F "1/2" 53) 53 .Floor == (F "4716158501352293/4503599627370496" 53, .lt)
#guard A (F "-3/4" 53) 53 .Floor == (F "5446784907458243/2251799813685248" 53, .lt)
#guard A (F "1/2" 53) 53 .Ceiling == (F "2358079250676147/2251799813685248" 53, .gt)
#guard A (F "-3/4" 53) 53 .Ceiling == (F "1361696226864561/562949953421312" 53, .gt)
#guard A (F "1/2" 53) 20 == (F "549033/524288" 20, .lt)
#guard A (F "1/2" 53) 1 == (F "1" 1, .lt)
#guard A (F "3/4" 53) 113
  == (F "3752650764477129491985459529029319/5192296858534827628530496329220096" 113, .lt)
#guard A (F "-3/4" 53) 2 == (F "2" 2, .lt)
#guard acos (F "1/2" 53) == (A (F "1/2" 53) 53).1
#guard (toString (acosPrecRound (F "1/2" 200) 200 .Nearest).1).startsWith
  "1.04719755119659774615421446109316762806572313312503527"
#guard (toString (acosPrecRound (F "-3/4" 200) 200 .Nearest).1).startsWith
  "2.41885840577637762728426603063816952217195091295066555"

-- next to `±1`
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) (p : Nat) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some p
#guard same (A (F "9007199254740991/9007199254740992" 53) 53) (powerOf2 (AzInt.ofInt (-26)))
  .lt 53
#guard (A (F "9007199254740991/9007199254740992" 53) 53 .Ceiling).2 == .gt
#guard A (F "-9007199254740991/9007199254740992" 53) 53
  == (F "884279714809251/281474976710656" 53, .lt)
#guard A (F "-9007199254740991/9007199254740992" 53) 53 .Ceiling
  == (F "7074237718474009/2251799813685248" 53, .gt)
#guard A (F ("1569275433846670190958947355801916604025588861116008628223/"
    ++ "1569275433846670190958947355801916604025588861116008628224") 200) 200
  == (F ("1136276788042180458070828951474823657989790988021617205464361/"
    ++ "31828687130226345097944463881396533766429193"
    ++ "651030253916189694521162207808802136034115584") 200,
    .lt)

-- tiny arguments: next to `π/2`
private def t200 : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard A t200 53 == (h piN (-1), .lt)
#guard A t200 53 .Ceiling == (h piC (-1), .gt)
#guard A (-t200) 53 == (h piN (-1), .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard A tiny 53 == (h piN (-1), .lt)
#guard A (-tiny) 53 .Ceiling == (h piC (-1), .gt)
