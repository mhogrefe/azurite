/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzFloat.PowRat
import Azurite.AzFloat.RatPow
import Azurite.AzFloat.RatPowRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `q^r` with rational base and exponent

The special values (`q^0 = 1`, `0^r`, `1^r`, `(−1)^n`, negative bases with non-integer
exponents, `p = 0`), the exact powers (`8^(1/3) = 2`, `(27/8)^(2/3) = 9/4`,
`(32/243)^(3/5) = 8/27` rounded, `(1/8)^(−2/3) = 4`, `1024^(−7/10) = 1/128`, `(3/2)^10`, `(−3/2)^3`,
`2^100` at 1 bit), the integer powers through the bracket (`3^40`, `(−3)^41` at 20 bits,
`(1 + 10^−6)^(10^6)`), the correctly rounded irrational powers `(1/3)^(1/3)`, `(2/3)^(5/7)`,
`(10/3)^(−7/3)`, `(22/7)^(355/113)`, `(3/2)^(1/3)`, `7^(−401/6)` in the three modes (references
from a 150-digit evaluation of `exp (r ln q)`), agreement with `ratPowPrecRound` and
`powRatPrecRound`, and `(1/3)^(1/3)` at 200 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (q r : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  ratPowRatPrecRound (Q q) (Q r) p m
private def pinf : AzFloat := infinity true
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (P "0" "0" 53) == ("1.0", .eq)
#guard D (P "5" "0" 53) == ("1.0", .eq)
#guard D (P "-7/3" "0" 53) == ("1.0", .eq)
#guard D (P "0" "2" 53) == ("0.0", .eq)
#guard D (P "0" "1/2" 53) == ("0.0", .eq)
#guard D (P "0" "-2" 53) == ("Infinity", .eq)
#guard D (P "0" "-1/2" 53) == ("Infinity", .eq)
#guard D (P "1" "-5/2" 53) == ("1.0", .eq)
#guard D (P "1" "1000000000000" 53) == ("1.0", .eq)
#guard D (P "-1" "4" 53) == ("1.0", .eq)
#guard D (P "-1" "3" 53) == ("-1.0", .eq)
#guard D (P "-1" "1/2" 53) == ("NaN", .eq)
#guard D (P "-8" "1/3" 53) == ("NaN", .eq)
#guard D (P "-27/8" "2/3" 53) == ("NaN", .eq)
#guard D (P "2" "3" 0) == ("NaN", .eq)
#guard D (P "0" "3" 0) == ("0.0", .eq)
#guard D (P "0" "-3" 0) == ("Infinity", .eq)
#guard D (P "0" "0" 0) == ("NaN", .eq)

-- exact powers
#guard D (P "8" "1/3" 53) == ("2.0", .eq)
#guard D (P "27/8" "2/3" 53) == ("2.25", .eq)
#guard D (P "32/243" "3/5" 53) == ("0.2962962962962963", .lt)
#guard D (P "1/8" "-2/3" 53) == ("4.0", .eq)
#guard D (P "4" "3/2" 53) == ("8.0", .eq)
#guard D (P "1/4" "-1/2" 53) == ("2.0", .eq)
#guard D (P "1024" "-7/10" 53) == ("0.0078125", .eq)
#guard D (P "3/2" "10" 53) == ("57.6650390625", .eq)
#guard D (P "-3/2" "3" 53) == ("-3.375", .eq)
#guard D (P "-3/2" "4" 53) == ("5.0625", .eq)
#guard D (P "2" "100" 1) == ("1.0e30", .eq)
#guard D (P "1/3" "2" 53) == ("0.1111111111111111", .lt)
#guard D (P "-1/3" "3" 53) == ("-0.037037037037037035", .gt)

-- integer powers through the bracket
#guard D (P "3" "40" 20) == ("1.215766e19", .lt)
#guard D (P "-3" "41" 20) == ("-3.6473e19", .lt)
#guard D (P "1000001/1000000" "1000000" 53) == ("2.7182804693193767", .lt)
#guard D (P "1000001/1000000" "1000000" 53 .Ceiling) == ("2.718280469319377", .gt)
#guard (P "3" "1000000000" 10).1 == (ratPowPrecRound (Q "3") (X "1000000000" 53) 10 .Nearest).1

-- correctly rounded irrational powers
#guard D (P "1/3" "1/3" 53) == ("0.6933612743506347", .lt)
#guard D (P "1/3" "1/3" 53 .Floor) == ("0.6933612743506347", .lt)
#guard D (P "1/3" "1/3" 53 .Ceiling) == ("0.6933612743506348", .gt)
#guard D (P "2/3" "5/7" 53) == ("0.7485495079957005", .lt)
#guard D (P "2/3" "5/7" 53 .Ceiling) == ("0.7485495079957006", .gt)
#guard D (P "10/3" "-7/3" 53) == ("0.06024896550739526", .gt)
#guard D (P "10/3" "-7/3" 53 .Floor) == ("0.06024896550739525", .lt)
#guard D (P "22/7" "355/113" 53) == ("36.5082966437583", .lt)
#guard D (P "22/7" "355/113" 53 .Ceiling) == ("36.50829664375831", .gt)
#guard D (P "3/2" "1/3" 53) == ("1.1447142425533319", .gt)
#guard D (P "3/2" "1/3" 53 .Floor) == ("1.1447142425533317", .lt)
#guard D (P "7" "-401/6" 53) == ("3.305833622237591e-57", .gt)

-- agreement with the one-sided rational powers
#guard P "3/2" "1/3" 53 == powRatPrecRound (X "1.5" 53) (Q "1/3") 53 .Nearest
#guard P "10" "2/7" 53 .Floor == powRatPrecRound (X "10" 53) (Q "2/7") 53 .Floor
#guard P "7" "-401/6" 53 == powRatPrecRound (X "7" 53) (Q "-401/6") 53 .Nearest
#guard P "1/3" "1/2" 53 == ratPowPrecRound (Q "1/3") (X "0.5" 53) 53 .Nearest
#guard P "22/7" "-3/4" 53 .Ceiling == ratPowPrecRound (Q "22/7") (X "-0.75" 53) 53 .Ceiling
#guard P "-5/3" "7" 53 == ratPowPrecRound (Q "-5/3") (X "7" 53) 53 .Nearest

-- 200 bits
#guard toString (ratPowRat (Q "1/3") (Q "1/3") 200)
  == "0.693361274350634704843352274785961795445935113457754036565864"

-- a tiny rational argument (`±1/(3·2^1000)`): the value is `1 ± tiny`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (ratPowRatPrecRound (Q "7/3") tinyQ 53 .Nearest) == ("1.0", .lt)
#guard D (ratPowRatPrecRound (Q "7/3") tinyQ 53 .Floor) == ("1.0", .lt)
#guard D (ratPowRatPrecRound (Q "7/3") tinyQ 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (ratPowRatPrecRound (Q "7/3") (-tinyQ) 53 .Nearest) == ("1.0", .gt)
#guard D (ratPowRatPrecRound (Q "7/3") (-tinyQ) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (ratPowRatPrecRound (Q "7/3") (-tinyQ) 53 .Ceiling) == ("1.0", .gt)
#guard D (ratPowRatPrecRound (Q "3/7") tinyQ 53 .Nearest) == ("1.0", .gt)

-- a huge rational exponent `(7·2^200 + 1)/3`: the starting precision of Ziv's loop is
-- logarithmic in its size; reference from 700-digit decimal arithmetic
private def hugeQ : AzRat := (AzNat.ofNat (7 * 2 ^ 200 + 1)).toAzRat * Q "1/3"
#guard ratPowRatPrecRound (Q "10/3") hugeQ 53 .Nearest == ((X "4985276223697164" 53)
  <<< AzInt.ofInt (Q "6512790887947396140205161270544734280809901781947594734716582").num.toNat,
  .gt)
#guard (ratPowRatPrecRound (Q "10/3") hugeQ 53 .Floor).2 == .lt
