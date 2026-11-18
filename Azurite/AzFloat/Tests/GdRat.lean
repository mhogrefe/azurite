/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gd
import Azurite.AzFloat.GdRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Gudermannian of a rational

`gd 0 = 0`, `p = 0`; the correctly rounded 53-bit values on every path — the series of
`tanh (|q|/2)` (`1/1000`, `−1/7000000`, `1/3`), the general path (`2/3`, `−7/5`), the series of
`e^(−|q|)` (`22/7`, `100/3`) and the huge path (`1000/3`, `10^40/7`); 200- and 300-bit results;
directed rounding and oddness; a tiny argument; agreement with the float function on dyadic
arguments.  References: a 400-digit evaluation of `2 arctan ((e^q − 1)/(e^q + 1))` rounded with
exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (q : String) (p : Nat) (m : RoundingMode := .Nearest) := gdRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A "0" 53) == ("0.0", .eq)
#guard D (A "0" 0) == ("0.0", .eq)
#guard D (A "1/3" 0) == ("NaN", .eq)

-- correctly rounded 53-bit values on every path
#guard D (A "1/1000" 53) == ("0.000999999833333375", .gt)
#guard D (A "-1/7000000" 53) == ("-1.4285714285714237e-7", .gt)
#guard D (A "1/3" 53) == ("0.32732661447167716", .gt)
#guard D (A "2/3" 53) == ("0.6221491267757672", .gt)
#guard D (A "-7/5" 53) == ("-1.0872498267763928", .lt)
#guard D (A "22/7" 53) == ("1.4845312444284462", .lt)
#guard D (A "100/3" 53) == ("1.57079632679489", .lt)
#guard D (A "1000/3" 53) == ("1.5707963267948966", .lt)
#guard D (A "10000000000000000000000000000000000000000/7" 53) == ("1.5707963267948966", .lt)
#guard A "-10000000000000000000000000000000000000000/7" 53 .Floor
  == (-(piDiv2PrecRound 53 .Ceiling).1, .lt)

-- other precisions, directed rounding, oddness
#guard D (A "1/3" 200) == ("0.3273266144716771413164643026330714462813186869844608960198133", .gt)
#guard D (A "22/7" 300) ==
  ("1.484531244428446243181576577097782647685908936010184926326397641662465158940507266700446552\
  ", .gt)
#guard D (A "1/3" 53 .Floor) == ("0.3273266144716771", .lt)
#guard (A "-1/3" 53 .Ceiling).1 == -(A "1/3" 53 .Floor).1
#guard (A "-22/7" 53).1 == -(A "22/7" 53).1

-- a tiny argument: the value is just inside `q`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard (gdRatPrecRound tinyQ 53 .Nearest) == (ofAzRat tinyQ 53, (ofAzRatRound tinyQ 53 .Nearest).2)
#guard (gdRatPrecRound tinyQ 53 .Ceiling).2 == .gt

-- agreement with the float function on dyadic arguments
#guard A "3/8" 53 == gdPrecRound (X "0.375" 53) 53 .Nearest
#guard A "3/4" 53 == gdPrecRound (X "0.75" 53) 53 .Nearest
#guard A "-2" 53 .Floor == gdPrecRound (X "-2" 53) 53 .Floor
#guard A "20" 100 == gdPrecRound (X "20" 53) 100 .Nearest
#guard A "200" 53 .Ceiling == gdPrecRound (X "200" 53) 53 .Ceiling
