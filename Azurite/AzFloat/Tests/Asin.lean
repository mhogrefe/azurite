/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asin
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `asin`

The special values (`NaN`; `±∞` and `|x| > 1` give `NaN`; `±1` give `±π/2` in every mode; `0`;
`p = 0`), the correctly rounded 53-bit values at `±1/2`, the floats nearest `1/3`, `−7/10`,
`3/4`, `9/10`, `99/100`, `1 − 10⁻⁶`, `1/√2`, `5/7`, small arguments, and the neighbour
`1 − 2^(−53)` of `1`; the directed modes; 1-, 2-, 20- and 113-bit results; 200-bit strings;
`2⁻⁴⁰`, `2⁻¹⁰⁰` at 200 bits, `1 − 2^(−190)` at 200 bits; and the tiny arguments `±2^(−2^30)`
(no cost in the exponent).  References: an independent 1400-bit fixed-point evaluation of
`arctan (x/√(1 − x²))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asinPrecRound x p m
private def piN : AzFloat := X "1.5707963267948966" 53
private def piC : AzFloat := X "1.5707963267948968" 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("NaN", .eq)
#guard D (A (infinity false) 53) == ("NaN", .eq)
#guard D (A (X "2" 53) 53) == ("NaN", .eq)
#guard D (A (X "-1.5" 53) 53) == ("NaN", .eq)
#guard D (A (X "1.0000000000000001" 54) 53) == ("NaN", .eq)
#guard D (A (powerOf2 (AzInt.ofInt 1073741824)) 53) == ("NaN", .eq)
#guard D (A zero 53) == ("0.0", .eq)
#guard D (A zero 0) == ("0.0", .eq)
#guard D (A (X "0.5" 53) 0) == ("NaN", .eq)
#guard D (A (X "1" 53) 53) == ("1.5707963267948966", .lt)
#guard D (A (X "1" 200) 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (A (X "-1" 53) 53) == ("-1.5707963267948966", .gt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-1.5707963267948968", .lt)

-- correctly rounded values
#guard D (A (X "0.5" 53) 53) == ("0.5235987755982989", .gt)
#guard D (A (X "-0.5" 53) 53) == ("-0.5235987755982989", .lt)
#guard D (A (X "0.3333333333333333" 53) 53) == ("0.3398369094541219", .gt)
#guard D (A (X "-0.7" 53) 53) == ("-0.775397496610753", .gt)
#guard D (A (X "0.75" 53) 53) == ("0.848062078981481", .lt)
#guard D (A (X "0.9" 53) 53) == ("1.1197695149986342", .lt)
#guard D (A (X "0.99" 53) 53) == ("1.4292568534704693", .lt)
#guard D (A (X "0.999999" 53) 53) == ("1.5693821131146521", .gt)
#guard D (A (X "0.0009765625" 53) 53) == ("0.0009765626552204957", .gt)
#guard D (A (X "0.001" 53) 53) == ("0.0010000001666667416", .lt)
#guard D (A (X "-0.000000001" 53) 53) == ("-1.0e-9", .gt)
#guard D (A (X "0.707106781186547" 53) 53) == ("0.7853981633974476", .gt)
#guard D (A (X "0.7142857142857143" 53) 53) == ("0.7956029534845354", .gt)
-- the neighbour `1 − 2^(−53)` of `1`
#guard D (A (X "0.9999999999999999" 53) 53) == ("1.5707963118937354", .lt)
#guard D (A (X "-0.9999999999999999" 53) 53 .Floor) == ("-1.5707963118937356", .lt)

-- directed modes and other precisions
#guard D (A (X "0.5" 53) 53 .Floor) == ("0.5235987755982988", .lt)
#guard D (A (X "-0.75" 53) 53 .Floor) == ("-0.8480620789814811", .lt)
#guard D (A (X "0.5" 53) 53 .Ceiling) == ("0.5235987755982989", .gt)
#guard D (A (X "-0.75" 53) 53 .Ceiling) == ("-0.848062078981481", .gt)
#guard D (A (X "0.5" 53) 20) == ("0.523599", .lt)
#guard D (A (X "0.5" 53) 1) == ("0.5", .lt)
#guard D (A (X "0.75" 53) 113) == ("0.8480620789814810080529443389984181", .gt)
#guard D (A (X "0.5" 53) 2) == ("0.5", .lt)
#guard asin (X "0.5" 53) == (A (X "0.5" 53) 53).1
#guard toString (asinPrecRound (X "0.5" 200) 200 .Nearest).1
  == "0.5235987755982988730771072305465838140328615665625176368291576"
#guard toString (asinPrecRound (X "0.75" 200) 200 .Nearest).1
  == "0.848062078981481008052944338998418080073366213263112642860718"

-- small arguments, arguments next to `1`, tiny arguments
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) (p : Nat) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some p
#guard same (A (powerOf2 (AzInt.ofInt (-40))) 53) (powerOf2 (AzInt.ofInt (-40))) .lt 53
#guard D (A (powerOf2 (AzInt.ofInt (-40))) 53 .Ceiling) == ("9.094947017729284e-13", .gt)
#guard same (A (powerOf2 (AzInt.ofInt (-100))) 200) (powerOf2 (AzInt.ofInt (-100))) .lt 200
#guard D (A (F ("1569275433846670190958947355801916604025588861116008628223/" ++
    "1569275433846670190958947355801916604025588861116008628224") 200) 200)
  == ("1.570796326794896619231321691604051672786921608471343333728434", .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard same (A tiny 53) tiny .lt 53
#guard (A tiny 53 .Ceiling).2 == .gt
#guard same (A (-tiny) 53) (-tiny) .gt 53
#guard (A (-tiny) 53 .Floor).2 == .lt
#guard (asinTiny? true tiny (AzInt.ofInt (-1073741823)) 1 53 .Nearest).isSome
