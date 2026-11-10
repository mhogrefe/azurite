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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (x : AzFloat) (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  powRatPrecRound x (Q q) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard P nan "0" 53 == (F "1" 53, .eq)
#guard P pinf "0" 53 == (F "1" 53, .eq)
#guard P (F "-7/3" 53) "0" 53 == (F "1" 53, .eq)
#guard P nan "2" 53 == (nan, .eq)
#guard P nan "1/2" 53 == (nan, .eq)
#guard P pinf "2" 53 == (pinf, .eq)
#guard P pinf "1/2" 53 == (pinf, .eq)
#guard P pinf "-2" 53 == (zero, .eq)
#guard P ninf "3" 53 == (ninf, .eq)
#guard P ninf "2" 53 == (pinf, .eq)
#guard P ninf "1/2" 53 == (pinf, .eq)
#guard P ninf "-3" 53 == (zero, .eq)
#guard P zero "2" 53 == (zero, .eq)
#guard P zero "1/2" 53 == (zero, .eq)
#guard P zero "-2" 53 == (pinf, .eq)
#guard P (F "1" 53) "-5/2" 53 == (F "1" 53, .eq)
#guard P (F "-1" 53) "4" 53 == (F "1" 53, .eq)
#guard P (F "-1" 53) "3" 53 == (F "-1" 53, .eq)
#guard P (F "-1" 53) "1/2" 53 == (nan, .eq)
#guard P (F "-8" 53) "1/3" 53 == (nan, .eq)
#guard P (F "2" 53) "3" 0 == (nan, .eq)
#guard P zero "3" 0 == (zero, .eq)

-- exact powers
#guard P (F "8" 53) "1/3" 53 == (F "2" 53, .eq)
#guard P (F "27/8" 53) "2/3" 53 == (F "9/4" 53, .eq)
#guard P (F "4" 53) "3/2" 53 == (F "8" 53, .eq)
#guard P (F "1/4" 53) "-1/2" 53 == (F "2" 53, .eq)
#guard P (F "1024" 53) "-7/10" 53 == (F "1/128" 53, .eq)
#guard P (F "3/2" 53) "10" 53 == (F "59049/1024" 53, .eq)
#guard P (F "-3/2" 53) "3" 53 == (F "-27/8" 53, .eq)
#guard P (F "2" 53) "100" 1 == (F "1267650600228229401496703205376" 1, .eq)

-- integer powers through the bracket
#guard P (F "3" 20) "40" 20 == (F "12157660708133142528" 20, .lt)
#guard P (F "-3" 20) "41" 20 == (F "-36472999716585472000" 20, .lt)
#guard P (F "3" 20) "40" 20 == powPrecRound (F "3" 20) (F "40" 20) 20 .Nearest
#guard (P (F "3" 53) "1000000000" 10).1
  == (powPrecRound (F "3" 53) (F "1000000000" 53) 10 .Nearest).1

-- correctly rounded irrational powers
#guard P (F "3/2" 53) "1/3" 53 == (F "5155334636208885/4503599627370496" 53, .gt)
#guard P (F "3/2" 53) "1/3" 53 .Floor == (F "1288833659052221/1125899906842624" 53, .lt)
#guard P (F "2" 53) "1/3" 53 == (F "5674179970822795/4503599627370496" 53, .gt)
#guard P (F "2" 53) "1/3" 53 == cbrtPrecRound (F "2" 53) 53 .Nearest
#guard P (F "10" 53) "2/7" 53 == (F "2173772393090917/1125899906842624" 53, .lt)
#guard P (F "10" 53) "2/7" 53 .Ceiling == (F "8695089572363669/4503599627370496" 53, .gt)
#guard P (F "5/4" 53) "-5/3" 53 == (F "6209735211021863/9007199254740992" 53, .lt)
#guard P (F "3" 53) "22/7" 53 == (F "2222817175851729/70368744177664" 53, .lt)
#guard P (F "7" 53) "-401/6" 53
  == (F ("2920451216048091/"
      ++ "883423532389192164791648750371459257913741948437809479060803100646309888") 53, .gt)
#guard P (F "2" 53) "22/7" 53 == pow2RatPrecRound (Q "22/7") 53 .Nearest
#guard P (F "3" 53) "22/7" 53 .Floor == powBaseRatPrecRound 3 (Q "22/7") 53 .Floor
#guard P (F "10" 53) "-401/6" 53 == powBaseRatPrecRound 10 (Q "-401/6") 53 .Nearest
#guard toString (powRat (F "2" 200) (Q "1/3") 200)
  == "1.259921049894873164767210607278228350570251464701507980081975"

-- a tiny rational argument (`±1/(3·2^1000)`): the value is `1 ± tiny`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def aboveOne : AzFloat := F "4503599627370497/4503599627370496" 53
private def belowOne : AzFloat := F "9007199254740991/9007199254740992" 53
#guard powRatPrecRound (F "3" 53) tinyQ 53 .Nearest == (F "1" 53, .lt)
#guard powRatPrecRound (F "3" 53) tinyQ 53 .Floor == (F "1" 53, .lt)
#guard powRatPrecRound (F "3" 53) tinyQ 53 .Ceiling == (aboveOne, .gt)
#guard powRatPrecRound (F "3" 53) (-tinyQ) 53 .Nearest == (F "1" 53, .gt)
#guard powRatPrecRound (F "3" 53) (-tinyQ) 53 .Floor == (belowOne, .lt)
#guard powRatPrecRound (F "3" 53) (-tinyQ) 53 .Ceiling == (F "1" 53, .gt)
#guard powRatPrecRound (F "1/3" 53) tinyQ 53 .Nearest == (F "1" 53, .gt)
-- a huge base: `(3·2^(3N))^(1/3) = ∛3 · 2^N`, `N = 2^28`
#guard powRatPrecRound ((F "3" 53) <<< AzInt.ofInt (3 * 2 ^ 28)) (Q "1/3") 53 .Nearest
  == ((powRatPrecRound (F "3" 53) (Q "1/3") 53 .Nearest).1 <<< AzInt.ofInt (2 ^ 28),
    (powRatPrecRound (F "3" 53) (Q "1/3") 53 .Nearest).2)
