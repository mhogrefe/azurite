/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecPi
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsec (x) / π`

`asecPi`: the special values (`NaN`, `|x| < 1`, `1/2` at `±∞`, `0` at `1`, `1` at `−1`, the
correctly rounded `1/3` at `2` and `2/3` at `−2`, `p = 0`), the correctly rounded 53-bit values,
the directed modes, a 20-bit result, a 200-bit string, huge arguments (next to `1/2`).
`asecPiRat`: the special values, exact rationals, the directed modes, agreement with the float
function.  References: an independent 1400-bit fixed-point evaluation rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asecPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asecPiRatPrecRound (Q q) p m

-- special values
#guard P nan 53 == (nan, .eq)
#guard P zero 53 == (nan, .eq)
#guard P (F "1/2" 53) 53 == (nan, .eq)
#guard P (infinity true) 53 == (F "1/2" 53, .eq)
#guard P (infinity false) 53 == (F "1/2" 53, .eq)
#guard P (F "1" 53) 53 == (zero, .eq)
#guard P (F "-1" 53) 53 == (F "1" 53, .eq)
#guard P (F "3" 53) 0 == (nan, .eq)
#guard P (F "2" 53) 53 == (F "6004799503160661/18014398509481984" 53, .lt)
#guard P (F "2" 53) 53 .Ceiling == (F "3002399751580331/9007199254740992" 53, .gt)
#guard P (F "-2" 53) 53 == (F "6004799503160661/9007199254740992" 53, .lt)
#guard P (F "-2" 53) 53 .Ceiling == (F "3002399751580331/4503599627370496" 53, .gt)

-- correctly rounded values
#guard P (F "3" 53) 53 == (F "7058519654875637/18014398509481984" 53, .gt)
#guard P (F "-3" 53) 53 == (F "2738969713651587/4503599627370496" 53, .gt)
#guard P (F "3/2" 53) 53 == (F "2411411643094145/9007199254740992" 53, .gt)
#guard P (F "-7/5" 53) 53 == (F "3392328698215697/4503599627370496" 53, .gt)
#guard P (F "100" 53) 53 == (F "8949856687612233/18014398509481984" 53, .lt)
#guard P (F "3/2" 53) 53 .Floor == (F "4822823286188289/18014398509481984" 53, .lt)
#guard P (F "3/2" 53) 53 .Ceiling == (F "2411411643094145/9007199254740992" 53, .gt)
#guard P (F "3/2" 53) 20 == (F "561451/2097152" 20, .gt)
#guard asecPi (F "3/2" 53) == (P (F "3/2" 53) 53).1
#guard (toString (asecPiPrecRound (F "3/2" 200) 200 .Nearest).1).startsWith
  "0.2677204728012300107452337959412318914943660025783258458"
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard P huge 53 == (F "1/2" 53, .gt)
#guard P (-huge) 53 == (F "1/2" 53, .lt)
#guard (P huge 53 .Floor).2 == .lt

-- rationals
#guard PR "1" 53 == (zero, .eq)
#guard PR "-1" 53 == (F "1" 53, .eq)
#guard PR "1/2" 53 == (nan, .eq)
#guard PR "0" 53 == (nan, .eq)
#guard PR "3" 0 == (nan, .eq)
#guard PR "2" 53 == (F "6004799503160661/18014398509481984" 53, .lt)
#guard PR "-4/2" 53 .Ceiling == (F "3002399751580331/4503599627370496" 53, .gt)
#guard PR "3" 53 == (F "7058519654875637/18014398509481984" 53, .gt)
#guard PR "-7/5" 53 == (F "6784657396431393/9007199254740992" 53, .lt)
#guard PR "22/7" 53 == (F "3575207357253583/9007199254740992" 53, .lt)
#guard PR "3" 53 .Floor == (F "1764629913718909/4503599627370496" 53, .lt)
#guard PR "3" 53 .Ceiling == (F "7058519654875637/18014398509481984" 53, .gt)
#guard PR "3/2" 53 == P (F "3/2" 53) 53
#guard asecPiRat (Q "3") 53 == (PR "3" 53).1
