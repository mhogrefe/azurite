/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBase
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Log2
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.Ln

/-!
# Tests for `log_b`

Special values, exact cases (integer powers of the primitive root of the base), agreement with
`log_{2^k}` for power-of-two bases, and
`log₁₀ 2 = 0.301029995663981195213738894724493026768189881462108541310427…`,
`log₃ (7/4) = 0.509384242018507385868874078396936009467300054330482623627682…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (b : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBasePrecRound x b p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (L nan 10 10) == ("NaN", .eq)
#guard D (L one 0 10) == ("NaN", .eq)  -- base 0
#guard D (L one 1 10) == ("NaN", .eq)  -- base 1
#guard D (L (infinity true) 10 10) == ("Infinity", .eq)
#guard D (L (infinity false) 10 10) == ("NaN", .eq)
#guard D (L zero 10 10) == ("-Infinity", .eq)
#guard D (L (X "-8" 53) 10 10) == ("NaN", .eq)
#guard D (L (X "8" 53) 10 0) == ("NaN", .eq)  -- precision 0

-- exact cases: `x = c^r` for `b = c^s` gives `r / s`, rounded once
#guard D (L (X "1" 53) 10 53) == ("0.0", .eq)
#guard D (L (X "1000" 53) 10 53) == ("3.0", .eq)
#guard D (L (X "36" 53) 6 53) == ("2.0", .eq)
#guard D (L (X "6" 53) 36 53) == ("0.5", .eq)
#guard D (L (X "144" 53) 12 53) == ("2.0", .eq)
#guard D (L (X "3" 53) 9 53) == ("0.5", .eq)
#guard D (L (X "27" 53) 9 53) == ("1.5", .eq)
#guard D (L (X "3" 53) 27 53) == ("0.3333333333333333", .lt)
#guard D (L (X "3" 53) 27 53 .Up) == ("0.33333333333333337", .gt)
#guard D (L (X "9" 53) 27 53 .Floor) == ("0.6666666666666666", .lt)
#guard D (L (X "1000" 53) 10 1) == ("4.0", .gt)  -- 3 rounded to 1 bit
#guard D (L (X "1000" 53) 10 1 .Floor) == ("2.0", .lt)
#guard D (L (X "10" 53) 1000 53) == ("0.3333333333333333", .lt)
#guard D (L (X "0.001" 53) 10 53) == ("-3.0", .lt)  -- 1/1000 is not a float

-- power-of-two bases agree with `log_{2^k}`
#guard L (X "10" 53) 2 53 == log2PrecRound (X "10" 53) 53 .Nearest
#guard L (X "10" 53) 8 53 == logBasePow2PrecRound (X "10" 53) (K 3) 53 .Nearest
#guard L (X "10" 53) 16 20 .Floor == logBasePow2PrecRound (X "10" 53) (K 4) 20 .Floor
#guard D (L (X "2" 53) 8 53) == ("0.3333333333333333", .lt)
#guard D (L (X "0.5" 53) 4 53) == ("-0.5", .eq)
#guard L (X "3" 53) ((1 : UInt64) <<< 63) 53 == logBasePow2PrecRound (X "3" 53) (K 63) 53 .Nearest

-- `log₁₀ 2`
private def ref102 : AzRat :=
  Q ("301029995663981195213738894724493026768189881462108541310427/1"
    ++ "".pushn '0' 60)
#guard toString (L (X "2" 53) 10 150).1 == "0.3010299956639811952137388947244930267681898814"
#guard toString (L (X "2" 53) 10 150 .Floor).1 == "0.3010299956639811952137388947244930267681898814"
#guard toString (L (X "2" 53) 10 150 .Ceiling).1 == "0.30102999566398119521373889472449302676818988\
  17"
#guard (L (X "2" 53) 10 150).2 == .lt
#guard toString (L (X "0.5" 53) 10 150).1 == "-0.3010299956639811952137388947244930267681898814"
-- `log₃ (7/4)`
private def ref374 : AzRat :=
  Q ("509384242018507385868874078396936009467300054330482623627682/1"
    ++ "".pushn '0' 60)
#guard toString (L (X "1.75" 53) 3 150).1 == "0.509384242018507385868874078396936009467300055"
#guard toString (L (X "1.75" 53) 3 150 .Up).1 == "0.509384242018507385868874078396936009467300055"
-- the largest base: `log_{2^64 − 1} 2` is just above `1/64`
#guard D (L (X "2" 53) (UInt64.ofNat (2 ^ 64 - 1)) 64) == ("0.015625", .lt)

-- default precision
#guard toString (logBase (X "1000" 10) 10) == "3.0"
#guard logBase (X "10" 53) 2 == log2 (X "10" 53)
#guard toString (logBase (X "2" 53) 10) == "0.3010299956639812"

-- precomputed constants: the same results (natural, power-of-two and tiny bases)
#guard logBaseWith (LogBaseConsts.forPrecision 10 53) (X "7" 53) == logBase (X "7" 53) 10
#guard logBaseWith (LogBaseConsts.forPrecision 3 200) (X "10" 200) == logBase (X "10" 200) 3
#guard logBaseWith (LogBaseConsts.forPrecision 8 53) (X "10" 53) == logBase (X "10" 53) 8
#guard logBaseWith (LogBaseConsts.forPrecision 10 53) (X "1000" 53) == logBase (X "1000" 53) 10
#guard logBaseWith (LogBaseConsts.forPrecision 1 53) (X "10" 53) == logBase (X "10" 53) 1
#guard logBasePrecRoundWith (LogBaseConsts.forPrecision 10 53) (X "7" 53) 53 .Floor
  == logBasePrecRound (X "7" 53) 10 53 .Floor
#guard logBaseWith (LogBaseConsts.make 10 1) (X "7" 53) == logBase (X "7" 53) 10

-- huge integers with a base that is not a power of two: the exactness test rejects them by the
-- valuation guard of `AzNat.checkedLogBase` (no power of the base is computed)
private def bigX : AzFloat := (X "1" 53) <<< AzInt.ofInt (2 ^ 30)
#guard D (L bigX 10 53) == ("323228496.62295526", .gt)
#guard D (L ((X "3" 53) <<< AzInt.ofInt (2 ^ 30)) 6 53) == ("415380039.47268426", .lt)

-- exponents far beyond memory (`2^(±2^50)`): the exactness test looks at the exponent and the
-- significand only (`logBaseExactSkip`), no integer or rational of that size is built;
-- `log₁₀ (2^K) = K log₁₀ 2`, so the result is the one for `2`, shifted
private def hugeE : Int := 2 ^ 50
private def sh (r : AzFloat × Ordering) (k : Int) : AzFloat × Ordering := (r.1 <<< K k, r.2)
private def neg (r : AzFloat × Ordering) : AzFloat × Ordering := (-r.1, r.2.swap)
#guard L ((X "1" 53) <<< K hugeE) 10 53 == sh (L (X "2" 53) 10 53) 50
#guard L ((X "1" 53) <<< K hugeE) 10 53 .Floor == sh (L (X "2" 53) 10 53 .Floor) 50
#guard L ((X "1" 53) <<< K (-hugeE)) 10 53 == neg (sh (L (X "2" 53) 10 53) 50)
#guard L ((X "1" 53) <<< K (-hugeE)) 6 53 .Floor == neg (sh (L (X "2" 53) 6 53 .Ceiling) 50)
#guard (L ((X "3" 53) <<< K hugeE) 10 53).2 != .eq
#guard (L ((X "3" 53) <<< K (-hugeE)) 12 53).2 != .eq
-- exact powers with an exponent above the precision still come out exact
#guard D (L (X "10000000000000000000000" 53) 10 53) == ("22.0", .eq)
#guard D (L (X "10000000000000000000000" 53) 100 53) == ("11.0", .eq)
#guard D (L (X "1024" 1) 4 53) == ("5.0", .eq)
#guard D (L ((X "81" 7) <<< K 4) 6 53) == ("4.0", .eq)  -- 6^4 = 81 · 2^4
#guard (L ((X "81" 7) <<< K 5) 6 53).2 != .eq
#guard D (L ((X "1" 1) <<< K 300) 1024 53) == ("3.0e1", .eq)
