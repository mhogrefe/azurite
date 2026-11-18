/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acos
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acosPrecRound x p m
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("NaN", .eq)
#guard D (A (infinity false) 53) == ("NaN", .eq)
#guard D (A (X "2" 53) 53) == ("NaN", .eq)
#guard D (A (X "-1.5" 53) 53) == ("NaN", .eq)
#guard D (A (X "1.0000000000000001" 54) 53) == ("NaN", .eq)
#guard D (A (powerOf2 (AzInt.ofInt 1073741824)) 53) == ("NaN", .eq)
#guard D (A (X "1" 53) 53) == ("0.0", .eq)
#guard D (A (X "1" 200) 0) == ("0.0", .eq)
#guard D (A zero 53) == ("1.5707963267948966", .lt)
#guard D (A zero 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (A zero 0) == ("NaN", .eq)
#guard D (A (X "-1" 53) 53) == ("3.141592653589793", .lt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (A (X "0.5" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "0.5" 53) 53) == ("1.0471975511965979", .gt)
#guard D (A (X "-0.5" 53) 53) == ("2.0943951023931957", .gt)
#guard D (A (X "0.3333333333333333" 53) 53) == ("1.2309594173407747", .gt)
#guard D (A (X "-0.7" 53) 53) == ("2.3461938234056494", .lt)
#guard D (A (X "0.75" 53) 53) == ("0.7227342478134157", .gt)
#guard D (A (X "0.9" 53) 53) == ("0.45102681179626236", .lt)
#guard D (A (X "0.99" 53) 53) == ("0.1415394733244273", .gt)
#guard D (A (X "0.999999" 53) 53) == ("0.0014142136802445852", .gt)
#guard D (A (X "-0.999999" 53) 53) == ("3.1401784399095485", .lt)
#guard D (A (X "0.0009765625" 53) 53) == ("1.569819764139676", .lt)
#guard D (A (X "-0.000000001" 53) 53) == ("1.5707963277948966", .gt)
#guard D (A (X "0.7142857142857143" 53) 53) == ("0.7751933733103613", .gt)
#guard D (A (X "0.5" 53) 53 .Floor) == ("1.0471975511965976", .lt)
#guard D (A (X "-0.75" 53) 53 .Floor) == ("2.4188584057763776", .lt)
#guard D (A (X "0.5" 53) 53 .Ceiling) == ("1.0471975511965979", .gt)
#guard D (A (X "-0.75" 53) 53 .Ceiling) == ("2.418858405776378", .gt)
#guard D (A (X "0.5" 53) 20) == ("1.047197", .lt)
#guard D (A (X "0.5" 53) 1) == ("1.0", .lt)
#guard D (A (X "0.75" 53) 113) == ("0.7227342478134156111783773526413333", .lt)
#guard D (A (X "-0.75" 53) 2) == ("2.0", .lt)
#guard acos (X "0.5" 53) == (A (X "0.5" 53) 53).1
#guard toString ((acosPrecRound (X "0.5" 200) 200 .Nearest).1)
  == "1.047197551196597746154214461093167628065723133125035273658315"
#guard toString ((acosPrecRound (X "-0.75" 200) 200 .Nearest).1)
  == "2.41885840577637762728426603063816952217195091295066555334819"

-- next to `±1`
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) (p : Nat) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some p
#guard same (A (X "0.9999999999999999" 53) 53) (powerOf2 (AzInt.ofInt (-26)))
  .lt 53
#guard (A (X "0.9999999999999999" 53) 53 .Ceiling).2 == .gt
#guard D (A (X "-0.9999999999999999" 53) 53) == ("3.141592638688632", .lt)
#guard D (A (X "-0.9999999999999999" 53) 53 .Ceiling) == ("3.1415926386886324", .gt)
#guard D (A (F ("1569275433846670190958947355801916604025588861116008628223/" ++
  "1569275433846670190958947355801916604025588861116008628224") 200) 200)
  == ("3.569976931166309121620957675903727002658850594321232046014642e-29", .lt)

-- tiny arguments: next to `π/2`
private def t200 : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard D (A t200 53) == ("1.5707963267948966", .lt)
#guard D (A t200 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (A (-t200) 53) == ("1.5707963267948966", .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
#guard D (A tiny 53) == ("1.5707963267948966", .lt)
#guard D (A (-tiny) 53 .Ceiling) == ("1.5707963267948968", .gt)
