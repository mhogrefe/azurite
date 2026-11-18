/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2
import Azurite.AzFloat.Atan
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `atan2 (y, x)`

The whole table of special values (`NaN`; `y = 0` against the sign of `x`, with `±∞`; `x = 0`;
`y = ±∞` against finite `x` and `±∞`; finite `y` against `±∞`; `p = 0`), with the directed modes
at the multiples of `π` and the constant `3π/4` at 1, 20 and 113 bits; the correctly rounded
53-bit values in all eight octants (`(±1, ±2)`, `(±2, ±1)`), on the diagonals, at inexact and
at very unequal arguments; agreement with `atan` for `x = 1`; the directed modes; 1-, 20- and
113-bit results; 200-bit strings; and extreme ratios in every octant (`2⁻²⁰⁰`, `2^1000`,
`2^(±2^30)`), which cost nothing extra.  References: an independent 1400-bit fixed-point
evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (y x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := atan2PrecRound y x p m
private def inf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
private def one' : AzFloat := X "1" 53
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- `NaN`
#guard D (A nan one' 53) == ("NaN", .eq)
#guard D (A one' nan 53) == ("NaN", .eq)
#guard D (A nan nan 53) == ("NaN", .eq)
#guard D (A inf nan 53) == ("NaN", .eq)
#guard D (A nan zero 53) == ("NaN", .eq)
-- `y = 0`
#guard D (A zero zero 53) == ("0.0", .eq)
#guard D (A zero (X "3" 53) 53) == ("0.0", .eq)
#guard D (A zero inf 53) == ("0.0", .eq)
#guard D (A zero zero 0) == ("0.0", .eq)
#guard D (A zero (X "-3" 53) 53) == ("3.141592653589793", .lt)
#guard D (A zero (X "-3" 53) 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (A zero ninf 53) == ("3.141592653589793", .lt)
#guard D (A zero ninf 53 .Ceiling) == ("3.1415926535897936", .gt)
-- `x = 0`
#guard D (A (X "2" 53) zero 53) == ("1.5707963267948966", .lt)
#guard D (A (X "-2" 53) zero 53) == ("-1.5707963267948966", .gt)
#guard D (A (X "-2" 53) zero 53 .Floor) == ("-1.5707963267948968", .lt)
-- `y = ±∞`
#guard D (A inf (X "5" 53) 53) == ("1.5707963267948966", .lt)
#guard D (A inf zero 53) == ("1.5707963267948966", .lt)
#guard D (A ninf (X "-5" 53) 53) == ("-1.5707963267948966", .gt)
#guard D (A ninf zero 53 .Floor) == ("-1.5707963267948968", .lt)
#guard D (A inf inf 53) == ("0.7853981633974483", .lt)
#guard D (A ninf inf 53) == ("-0.7853981633974483", .gt)
#guard D (A ninf inf 53 .Floor) == ("-0.7853981633974484", .lt)
#guard D (A inf ninf 53) == ("2.356194490192345", .lt)
#guard D (A inf ninf 53 .Ceiling) == ("2.3561944901923453", .gt)
#guard D (A ninf ninf 53) == ("-2.356194490192345", .gt)
#guard D (A ninf ninf 53 .Floor) == ("-2.3561944901923453", .lt)
#guard D (A inf ninf 1) == ("2.0", .lt)
#guard D (A inf ninf 20) == ("2.356194", .lt)
#guard D (A inf ninf 113) == ("2.356194490192344928846982537459627", .lt)
-- finite `y`, `x = ±∞`
#guard D (A (X "5" 53) inf 53) == ("0.0", .eq)
#guard D (A (X "-5" 53) inf 53) == ("0.0", .eq)
#guard D (A (X "5" 53) ninf 53) == ("3.141592653589793", .lt)
#guard D (A (X "-5" 53) ninf 53) == ("-3.141592653589793", .gt)
#guard D (A (X "-5" 53) ninf 53 .Floor) == ("-3.1415926535897936", .lt)
-- `p = 0`
#guard D (A one' one' 0) == ("NaN", .eq)
#guard D (A (X "5" 53) inf 0) == ("0.0", .eq)

-- correctly rounded values
#guard D (A (X "1" 53) (X "1" 53) 53) == ("0.7853981633974483", .lt)
#guard D (A (X "1" 53) (X "2" 53) 53) == ("0.4636476090008061", .lt)
#guard D (A (X "2" 53) (X "1" 53) 53) == ("1.1071487177940904", .lt)
#guard D (A (X "1" 53) (X "-2" 53) 53) == ("2.677945044588987", .lt)
#guard D (A (X "2" 53) (X "-1" 53) 53) == ("2.0344439357957027", .lt)
#guard D (A (X "-1" 53) (X "2" 53) 53) == ("-0.4636476090008061", .gt)
#guard D (A (X "-2" 53) (X "1" 53) 53) == ("-1.1071487177940904", .gt)
#guard D (A (X "-1" 53) (X "-2" 53) 53) == ("-2.677945044588987", .gt)
#guard D (A (X "-2" 53) (X "-1" 53) 53) == ("-2.0344439357957027", .gt)
#guard D (A (X "1" 53) (X "-1" 53) 53) == ("2.356194490192345", .lt)
#guard D (A (X "-1" 53) (X "-1" 53) 53) == ("-2.356194490192345", .gt)
#guard D (A (X "0.3333333333333333" 53) (X "1.4" 53) 53) == ("0.23374318086890142", .lt)
#guard D (A (X "-1.4" 53) (X "0.3333333333333333" 53) 53) == ("-1.3370531459259951", .gt)
#guard D (A (X "3.142857142857143" 53) (X "-0.001" 53) 53) == ("1.5711145086023408", .lt)
#guard D (A (X "0.001" 53) (X "-3.142857142857143" 53) 53) == ("3.141274471782349", .lt)
#guard D (A (X "1000000000000" 53) (X "3" 53) 53) == ("1.5707963267918965", .lt)
#guard D (A (X "3" 53) (X "1000000000000" 53) 53) == ("3.0e-12", .gt)
#guard D (A (X "3" 53) (X "-1000000000000" 53) 53) == ("3.1415926535867933", .gt)
#guard D (A (X "1" 53) (X "2" 53) 53 .Floor) == ("0.4636476090008061", .lt)
#guard D (A (X "-2" 53) (X "-1" 53) 53 .Floor) == ("-2.034443935795703", .lt)
#guard D (A (X "2" 53) (X "-1" 53) 53 .Floor) == ("2.0344439357957027", .lt)
#guard D (A (X "1" 53) (X "2" 53) 53 .Ceiling) == ("0.46364760900080615", .gt)
#guard D (A (X "-2" 53) (X "-1" 53) 53 .Ceiling) == ("-2.0344439357957027", .gt)
#guard D (A (X "2" 53) (X "-1" 53) 53 .Ceiling) == ("2.034443935795703", .gt)
#guard D (A (X "1" 53) (X "2" 53) 20) == ("0.463648", .gt)
#guard D (A (X "1" 53) (X "-2" 53) 1) == ("2.0", .lt)
#guard D (A (X "-2" 53) (X "1" 53) 113) == ("-1.107148717794090503017065460178537", .lt)

-- agreement with `atan` for `x = 1`
#guard A (X "0.3333333333333333" 53) one' 53
  == atanPrecRound (X "0.3333333333333333" 53) 53 .Nearest
#guard A (X "-3.142857142857143" 53) one' 53 .Floor
  == atanPrecRound (X "-3.142857142857143" 53) 53 .Floor
#guard atan2 (X "1" 53) (X "2" 53) == (A (X "1" 53) (X "2" 53) 53).1
#guard toString ((atan2PrecRound (X "1" 200) (X "-2" 200) 200 .Nearest).1)
  == "2.677945044588987122248387151818288482168632345088985557164012"
#guard toString ((atan2PrecRound (X "-2" 200) (X "1" 200) 200 .Nearest).1)
  == "-1.107148717794090503017065460178537040070047645401432646676539"

-- extreme ratios (`same`: equality of the values, the expected floats having precision `1`)
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some 53
private def t : AzFloat := powerOf2 (AzInt.ofInt (-200))
private def T : AzFloat := powerOf2 (AzInt.ofInt 1000)
#guard same (A t one' 53) t .gt
#guard D (A t one' 53 .Floor) == ("6.223015277861141e-61", .lt)
#guard D (A one' t 53) == ("1.5707963267948966", .lt)
#guard D (A t (-one') 53) == ("3.141592653589793", .lt)
#guard D (A (-t) (-one') 53) == ("-3.141592653589793", .gt)
#guard D (A (-t) (-one') 53 .Floor) == ("-3.1415926535897936", .lt)
#guard D (A T one' 53) == ("1.5707963267948966", .lt)
#guard same (A one' T 53) (powerOf2 (AzInt.ofInt (-1000))) .gt
#guard (A one' T 53 .Floor).2 == .lt
#guard D (A one' (-T) 53) == ("3.141592653589793", .lt)
#guard D (A (-one') (-T) 53 .Floor) == ("-3.1415926535897936", .lt)
#guard D (A T (-T) 53) == ("2.356194490192345", .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard same (A tiny one' 53) tiny .gt
#guard same (A one' huge 53) tiny .gt
#guard same (A (-tiny) huge 53 .Floor) (-(h tiny (-1073741824))) .lt
#guard same (A (-tiny) one' 53) (-tiny) .lt
#guard D (A huge tiny 53) == ("1.5707963267948966", .lt)
#guard D (A tiny (-huge) 53) == ("3.141592653589793", .lt)
#guard D (A (-huge) (-tiny) 53) == ("-1.5707963267948966", .gt)
