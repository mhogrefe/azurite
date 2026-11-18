/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gd
import Azurite.AzFloat.GdInv
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the inverse Gudermannian `gd⁻¹ x`

The special values (`NaN`, `±∞ ↦ NaN`, `0`, `p = 0`); the domain: the two doubles around `π/2`
(the one below gives `38.025…`, the one above `NaN`), `2`, huge arguments; the correctly rounded
53-bit values from `1/1024` to `201/128` and next to `π/2`; 200- and 300-bit results; directed
rounding and oddness; tiny arguments (the value is just outside `x`); and the round trip with
`gd`.  References: a 500-digit evaluation of `ln ((1 + sin x)/cos x)` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := gdInvPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("NaN", .eq)
#guard D (A (infinity false) 53) == ("NaN", .eq)
#guard D (A zero 53) == ("0.0", .eq)
#guard D (A zero 0) == ("0.0", .eq)
#guard D (A (X "1" 53) 0) == ("NaN", .eq)

-- the domain `|x| < π/2`: the doubles just below and just above `π/2`
private def below : AzFloat := X "1.5707963267948966" 53
private def above : AzFloat := X "1.5707963267948968" 53
#guard gdInvInDomain below (AzInt.ofInt 1) 53 && !gdInvInDomain above (AzInt.ofInt 1) 53
#guard D (A below 53) == ("38.025003373828866", .lt)
#guard D (A (-below) 53) == ("-38.025003373828866", .gt)
#guard D (A above 53) == ("NaN", .eq)
#guard D (A (-above) 53) == ("NaN", .eq)
#guard D (A (X "2" 53) 53) == ("NaN", .eq)
#guard D (A (X "-100" 53) 53) == ("NaN", .eq)
#guard A (h (X "1" 53) (2 ^ 40)) 53 == (nan, .eq)
#guard gdInvInDomain (X "1.5" 2) (AzInt.ofInt 1) 2 && !gdInvInDomain (X "2" 2) (AzInt.ofInt 2) 2
#guard gdInvInDomain (X "0.5" 53) (AzInt.ofInt 0) 53

-- correctly rounded 53-bit values
#guard D (A (X "0.0009765625" 53) 53) == ("0.000976562655220466", .lt)
#guard D (A (X "0.375" 53) 53) == ("0.38411126182973193", .gt)
#guard D (A (X "1" 53) 53) == ("1.2261911708835171", .gt)
#guard D (A (X "-1" 53) 53) == ("-1.2261911708835171", .lt)
#guard D (A (X "1.25" 53) 53) == ("1.8214683196993307", .gt)
#guard D (A (X "1.5" 53) 53) == ("3.340677542798311", .gt)
#guard D (A (X "1.5625" 53) 53) == ("5.485083861751334", .lt)
#guard D (A (X "1.5703125" 53) 53) == ("8.326930738131876", .lt)

-- other precisions, directed rounding, oddness
#guard D (A (X "1" 53) 200) == ("1.226191170883517070813060967471906752724248350220740279138617\
  ", .gt)
#guard D (A (X "1.5" 53) 300) == ("3.34067754279831100332081266903768876035632219977707950293668182\
  3958230014289251284006320843", .lt)
#guard D (A (X "0.015625" 53) 300) ==
    ("0.0156256358216854635974915984271426672099740962319759276596253\
  0305588614871493516353233467711", .lt)
#guard D (A (X "1" 53) 53 .Floor) == ("1.226191170883517", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("1.2261911708835171", .gt)
#guard (A (X "-1.25" 53) 53 .Floor).1 == -(A (X "1.25" 53) 53 .Ceiling).1
#guard toString (gdInv (X "1" 200))
  == "1.226191170883517070813060967471906752724248350220740279138617"

-- tiny arguments: the value is just outside `x`
#guard D (A (h (X "1" 53) (-1000)) 53) == ("9.332636185032189e-302", .lt)
#guard D (A (h (X "-1" 53) (-1000)) 53) == ("-9.332636185032189e-302", .gt)
#guard A (h (X "1" 53) (-(2 ^ 30))) 53 .Ceiling
  == (h (X "1.0000000000000002" 53) (-(2 ^ 30)), .gt)

-- round trip with `gd` at a higher intermediate precision
#guard toString ((gdPrecRound (A (X "1.25" 53) 200).1 53 .Nearest).1) == "1.25"
#guard toString ((A (gdPrecRound (X "3" 53) 200 .Nearest).1 53).1) == "3.0"

-- the dummy bracket next to `π/2` at a level too low to separate `x` from `π/2`
private def near : AzFloat := (piDiv2PrecRound 200 .Floor).1
#guard gdInvBracket near (AzInt.ofInt 1) 64 == (-one, one)
#guard gdInvBracket near (AzInt.ofInt 1) 400 != (-one, one)
#guard lt (X "138" 53) (A near 53).1 && lt (A near 53).1 (X "200" 53)
#guard D (A (piDiv2PrecRound 200 .Ceiling).1 53) == ("NaN", .eq)
#guard lnOfEncl (-one, one) 64 == (-one, one) && lnOfEncl (zero, one) 64 == (-one, one)
