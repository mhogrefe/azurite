/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cbrt
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Pow
import Azurite.AzFloat.Pow2Rat
import Azurite.AzFloat.PowBaseRat
import Azurite.AzFloat.PowRat
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `x^q` with a rational exponent

The special values (`x^0 = 1` even for `NaN`, `NaN^q`, the infinite bases by the sign and parity
of `q`, `0^q`, `1^q`, negative bases with non-integer exponents), the exact powers (`8^(1/3) = 2`,
`(27/8)^(2/3) = 9/4`, `4^(3/2) = 8`, `(1/4)^(−1/2) = 2`, `(3/2)^10`, `(−3/2)^3`), the integer
powers through the bracket (`3^40`, `(−3)^41` at 20 bits), the correctly rounded `(3/2)^(1/3)`,
`2^(1/3)` (against `cbrt`), `10^(2/7)`, `(5/4)^(−5/3)`, `3^(22/7)`, `7^(−401/6)` (references
from a 90-digit evaluation of `exp (q ln x)`), agreement with `pow2Rat` and `powBaseRat`, and the
directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x : AzFloat) (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  powRatPrecRound x (Q q) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard D (P nan "0" 53) == ("1.0", .eq)
#guard D (P pinf "0" 53) == ("1.0", .eq)
#guard D (P (X "-2.3333333333333335" 53) "0" 53) == ("1.0", .eq)
#guard D (P nan "2" 53) == ("NaN", .eq)
#guard D (P nan "1/2" 53) == ("NaN", .eq)
#guard D (P pinf "2" 53) == ("Infinity", .eq)
#guard D (P pinf "1/2" 53) == ("Infinity", .eq)
#guard D (P pinf "-2" 53) == ("0.0", .eq)
#guard D (P ninf "3" 53) == ("-Infinity", .eq)
#guard D (P ninf "2" 53) == ("Infinity", .eq)
#guard D (P ninf "1/2" 53) == ("Infinity", .eq)
#guard D (P ninf "-3" 53) == ("0.0", .eq)
#guard D (P zero "2" 53) == ("0.0", .eq)
#guard D (P zero "1/2" 53) == ("0.0", .eq)
#guard D (P zero "-2" 53) == ("Infinity", .eq)
#guard D (P (X "1" 53) "-5/2" 53) == ("1.0", .eq)
#guard D (P (X "-1" 53) "4" 53) == ("1.0", .eq)
#guard D (P (X "-1" 53) "3" 53) == ("-1.0", .eq)
#guard D (P (X "-1" 53) "1/2" 53) == ("NaN", .eq)
#guard D (P (X "-8" 53) "1/3" 53) == ("NaN", .eq)
#guard D (P (X "2" 53) "3" 0) == ("NaN", .eq)
#guard D (P zero "3" 0) == ("0.0", .eq)

-- exact powers
#guard D (P (X "8" 53) "1/3" 53) == ("2.0", .eq)
#guard D (P (X "3.375" 53) "2/3" 53) == ("2.25", .eq)
#guard D (P (X "4" 53) "3/2" 53) == ("8.0", .eq)
#guard D (P (X "0.25" 53) "-1/2" 53) == ("2.0", .eq)
#guard D (P (X "1024" 53) "-7/10" 53) == ("0.0078125", .eq)
#guard D (P (X "1.5" 53) "10" 53) == ("57.6650390625", .eq)
#guard D (P (X "-1.5" 53) "3" 53) == ("-3.375", .eq)
#guard D (P (X "2" 53) "100" 1) == ("1.0e30", .eq)

-- integer powers through the bracket
#guard D (P (X "3" 20) "40" 20) == ("1.215766e19", .lt)
#guard D (P (X "-3" 20) "41" 20) == ("-3.6473e19", .lt)
#guard P (X "3" 20) "40" 20 == powPrecRound (X "3" 20) (X "40" 20) 20 .Nearest
#guard (P (X "3" 53) "1000000000" 10).1
  == (powPrecRound (X "3" 53) (X "1000000000" 53) 10 .Nearest).1

-- correctly rounded irrational powers
#guard D (P (X "1.5" 53) "1/3" 53) == ("1.1447142425533319", .gt)
#guard D (P (X "1.5" 53) "1/3" 53 .Floor) == ("1.1447142425533317", .lt)
#guard D (P (X "2" 53) "1/3" 53) == ("1.2599210498948732", .gt)
#guard P (X "2" 53) "1/3" 53 == cbrtPrecRound (X "2" 53) 53 .Nearest
#guard D (P (X "10" 53) "2/7" 53) == ("1.93069772888325", .lt)
#guard D (P (X "10" 53) "2/7" 53 .Ceiling) == ("1.9306977288832503", .gt)
#guard D (P (X "1.25" 53) "-5/3" 53) == ("0.6894191008102027", .lt)
#guard D (P (X "3" 53) "22/7" 53) == ("31.588131944484545", .lt)
#guard D (P (X "7" 53) "-401/6" 53) == ("3.305833622237591e-57", .gt)
#guard P (X "2" 53) "22/7" 53 == pow2RatPrecRound (Q "22/7") 53 .Nearest
#guard P (X "3" 53) "22/7" 53 .Floor == powBaseRatPrecRound 3 (Q "22/7") 53 .Floor
#guard P (X "10" 53) "-401/6" 53 == powBaseRatPrecRound 10 (Q "-401/6") 53 .Nearest
#guard toString (powRat (X "2" 200) (Q "1/3") 200)
  == "1.259921049894873164767210607278228350570251464701507980081975"

-- a tiny rational argument (`±1/(3·2^1000)`): the value is `1 ± tiny`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (powRatPrecRound (X "3" 53) tinyQ 53 .Nearest) == ("1.0", .lt)
#guard D (powRatPrecRound (X "3" 53) tinyQ 53 .Floor) == ("1.0", .lt)
#guard D (powRatPrecRound (X "3" 53) tinyQ 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (powRatPrecRound (X "3" 53) (-tinyQ) 53 .Nearest) == ("1.0", .gt)
#guard D (powRatPrecRound (X "3" 53) (-tinyQ) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (powRatPrecRound (X "3" 53) (-tinyQ) 53 .Ceiling) == ("1.0", .gt)
#guard D (powRatPrecRound (X "0.3333333333333333" 53) tinyQ 53 .Nearest) == ("1.0", .gt)
-- a huge base: `(3·2^(3N))^(1/3) = ∛3 · 2^N`, `N = 2^28`
#guard powRatPrecRound ((X "3" 53) <<< AzInt.ofInt (3 * 2 ^ 28)) (Q "1/3") 53 .Nearest
  == ((powRatPrecRound (X "3" 53) (Q "1/3") 53 .Nearest).1 <<< AzInt.ofInt (2 ^ 28),
    (powRatPrecRound (X "3" 53) (Q "1/3") 53 .Nearest).2)

-- a huge rational exponent `(7·2^200 + 1)/3`; reference from 700-digit decimal arithmetic
private def hugeQ : AzRat := (AzNat.ofNat (7 * 2 ^ 200 + 1)).toAzRat * Q "1/3"
#guard powRatPrecRound (X "10" 53) hugeQ 53 .Nearest == ((X "4828934438682321" 53)
  <<< AzInt.ofInt (Q "12455642817257013556540030957877841028656341043289085996096797").num.toNat,
  .lt)
