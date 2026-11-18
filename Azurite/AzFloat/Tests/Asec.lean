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
import Azurite.AzFloat.OfString

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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asecPrecRound x p m
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A zero 53) == ("NaN", .eq)
#guard D (A (X "0.5" 53) 53) == ("NaN", .eq)
#guard D (A (X "-0.9999999999999999" 53) 53) == ("NaN", .eq)
#guard D (A (powerOf2 (AzInt.ofInt (-1073741824))) 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("1.5707963267948966", .lt)
#guard D (A (infinity false) 53) == ("1.5707963267948966", .lt)
#guard D (A (infinity false) 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (A (X "1" 53) 53) == ("0.0", .eq)
#guard D (A (X "1" 200) 0) == ("0.0", .eq)
#guard D (A (X "-1" 53) 53) == ("3.141592653589793", .lt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "2" 53) 53) == ("1.0471975511965979", .gt)
#guard D (A (X "-2" 53) 53) == ("2.0943951023931957", .gt)
#guard D (A (X "1.5" 53) 53) == ("0.8410686705679302", .lt)
#guard D (A (X "1.25" 53) 53) == ("0.6435011087932844", .lt)
#guard D (A (X "-1.4" 53) 53) == ("2.366399280279432", .gt)
#guard D (A (X "100" 53) 53) == ("1.5607961601207294", .lt)
#guard D (A (X "-1000" 53) 53) == ("1.5717963269615634", .lt)
#guard D (A (X "1000000000000" 53) 53) == ("1.5707963267938967", .gt)
#guard D (A (X "1.000001" 53) 53) == ("0.0014142129730596528", .lt)
#guard D (A (X "-1.000001" 53) 53) == ("3.1401784406167335", .lt)
#guard D (A (X "3.142857142857143" 53) 53) == ("1.2469853115213465", .lt)
#guard D (A (X "2" 53) 53 .Floor) == ("1.0471975511965976", .lt)
#guard D (A (X "-1.5" 53) 53 .Floor) == ("2.3005239830218627", .lt)
#guard D (A (X "2" 53) 53 .Ceiling) == ("1.0471975511965979", .gt)
#guard D (A (X "-1.5" 53) 53 .Ceiling) == ("2.300523983021863", .gt)
#guard D (A (X "2" 53) 20) == ("1.047197", .lt)
#guard D (A (X "2" 53) 1) == ("1.0", .lt)
#guard D (A (X "1.5" 53) 113) == ("0.8410686705679302557765250318264307", .lt)
#guard D (A (X "-1.5" 53) 2) == ("2.0", .lt)
#guard A (X "2" 53) 53 == acosPrecRound (X "0.5" 53) 53 .Nearest
#guard A (X "-4" 53) 53 .Floor == acosPrecRound (X "-0.25" 53) 53 .Floor
#guard asec (X "2" 53) == (A (X "2" 53) 53).1
#guard toString (asecPrecRound (X "2" 200) 200 .Nearest).1
  == "1.047197551196597746154214461093167628065723133125035273658315"
#guard toString (asecPrecRound (X "-1.5" 200) 200 .Nearest).1
  == "2.30052398302186298268611835145307213749509061373526660119642"

-- next to `±1`
#guard D (A (X "1.0000000000000002" 53) 53) == ("2.1073424255447014e-8", .gt)
#guard D (A (X "-1.0000000000000002" 53) 53) == ("3.1415926325163688", .lt)
#guard D (A (X "-1.0000000000000002" 53) 53 .Ceiling) == ("3.141592632516369", .gt)
#guard D (A (F ("1569275433846670190958947355801916604025588861116008628225/" ++
    "1569275433846670190958947355801916604025588861116008628224") 200) 200)
  == ("3.569976931166309121620957675903727002658850594321232046013505e-29", .lt)

-- huge arguments: next to `π/2`
private def T : AzFloat := powerOf2 (AzInt.ofInt 1000)
#guard D (A T 53) == ("1.5707963267948966", .lt)
#guard D (A T 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (A (-T) 53) == ("1.5707963267948966", .lt)
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard D (A huge 53) == ("1.5707963267948966", .lt)
#guard D (A (-huge) 53 .Ceiling) == ("1.5707963267948968", .gt)
