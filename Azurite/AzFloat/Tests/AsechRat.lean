/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsechRat
import Azurite.AzFloat.Asech
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `asech q` of a rational

The special values (`asech 0 = +∞`; `asech 1 = 0`; `NaN` for `q < 0` and `q > 1`; `p = 0`),
the correctly rounded 53-bit values at exact rationals from `10^(−30)/3` to `1 − 10^(−30)/3`
in three modes, 1-, 2-, 20-, 113- and 200-bit results, agreement with the float `asech` at
representable arguments, 200-bit strings, and a tiny rational (where `asech q` rounds like
`ln (2/q)`).  References: an independent 6000-bit fixed-point evaluation of
`ln (1/q + √(1/q² − 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asechRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("Infinity", .eq)
#guard D (T "0" 0) == ("Infinity", .eq)
#guard D (T "1" 53) == ("0.0", .eq)
#guard D (T "3/3" 0) == ("0.0", .eq)
#guard D (T "2" 53) == ("NaN", .eq)
#guard D (T "1000001/1000000" 53) == ("NaN", .eq)
#guard D (T "-1/2" 53) == ("NaN", .eq)
#guard D (T "-1" 53) == ("NaN", .eq)
#guard D (T "-3" 53) == ("NaN", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1/2" 53) == ("1.3169578969248168", .gt)
#guard D (T "1/3" 53) == ("1.762747174039086", .gt)
#guard D (T "2/7" 53) == ("1.9248473002384139", .gt)
#guard D (T "7/22" 53) == ("1.8119507608214136", .gt)
#guard D (T "113/355" 53) == ("1.811526362033495", .gt)
#guard D (T "99/100" 53) == ("0.14201444074607708", .gt)
#guard D (T "999999999/1000000000" 53) == ("0.000044721359568629694", .lt)
#guard D (T "1/1000" 53) == ("7.600902209541989", .gt)
#guard D (T "1/1000000007" 53) == ("21.416413024506358", .gt)
#guard D (T "3/1125899906842624" 53) == ("34.2518939198891", .lt)
#guard D (T "1/3000000000000000000000000000000" 53) == ("70.86931225904942", .lt)
#guard D (T "2999999999999999999999999999999/3000000000000000000000000000000" 53) ==
  ("8.16496580927726e-16", .gt)
#guard D (T "1/3" 53 .Floor) == ("1.7627471740390859", .lt)
#guard D (T "2/7" 53 .Floor) == ("1.9248473002384137", .lt)
#guard D (T "99/100" 53 .Floor) == ("0.14201444074607705", .lt)
#guard D (T "1/1000000007" 53 .Floor) == ("21.416413024506355", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("1.762747174039086", .gt)
#guard D (T "2/7" 53 .Ceiling) == ("1.9248473002384139", .gt)
#guard D (T "99/100" 53 .Ceiling) == ("0.14201444074607708", .gt)
#guard D (T "1/1000000007" 53 .Ceiling) == ("21.416413024506358", .gt)
#guard D (T "1/3" 20) == ("1.762747", .lt)
#guard D (T "1/3" 1) == ("2.0", .gt)
#guard D (T "7/22" 2) == ("2.0", .gt)
#guard D (T "1/3" 113) == ("1.7627471740390860504652186499595846", .lt)
#guard D (T "5/7" 200) == ("0.867014726490565103950520269501467375464496489945643731323534", .gt)

-- agreement with the float `asech` at representable arguments
#guard T "3/4" 53 == asechPrecRound (X "0.75" 53) 53 .Nearest
#guard T "5/1024" 53 .Floor == asechPrecRound (X "0.0048828125" 53) 53 .Floor
#guard T "1023/1024" 20 .Ceiling == asechPrecRound (X "0.9990234375" 53) 20 .Ceiling
#guard asechRat (Q "1/3") 53 == (T "1/3" 53).1
#guard toString (asechRat (Q "1/3") 200) == "1.7627471740390860504652186499595846180563206565232708\
  21506592"
#guard toString (asechRat (Q "7/22") 200) == "1.811950760821413556235972813109322036695962129898042\
  791003144"

-- a tiny rational: `asech q` rounds like `ln (2/q)`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def bigq : AzRat := Q "6" * (pw 5000)⁻¹
#guard asechRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest == lnRatPrecRound bigq 53 .Nearest
#guard asechRatPrecRound (Q "1/3" * pw 5000) 53 .Floor == lnRatPrecRound bigq 53 .Floor
