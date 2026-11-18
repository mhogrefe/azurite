/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcschRat
import Azurite.AzFloat.Acsch
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acsch q` of a rational

The special values (`acsch 0 = +∞`, `p = 0`), the correctly rounded 53-bit values at exact
rationals from `10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113- and 200-bit results,
agreement with the float `acsch` at representable arguments, oddness, 200-bit strings, huge
rationals `±2^5000`, `±3·2^5000` (just inside `1/q`, at no cost), and a tiny rational (where
`acsch q` rounds like `ln (2/q)`).  References: an independent 6000-bit fixed-point evaluation
of `ln (1/q + √(1/q² + 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := X "0.9999999999999999" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acschRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("Infinity", .eq)
#guard D (T "0" 0) == ("Infinity", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1" 53) == ("0.881373587019543", .gt)
#guard D (T "-1" 53) == ("-0.881373587019543", .lt)
#guard D (T "1/3" 53) == ("1.8184464592320668", .gt)
#guard D (T "-2/7" 53) == ("-1.9657204716496515", .gt)
#guard D (T "22/7" 53) == ("0.313043843408309", .gt)
#guard D (T "355/113" 53) == ("0.31316585469532293", .lt)
#guard D (T "-7/5" 53) == ("-0.6643306045898851", .gt)
#guard D (T "10" 53) == ("0.09983407889920756", .lt)
#guard D (T "-100/3" 53) == ("-0.02999550182152426", .lt)
#guard D (T "1/1000" 53) == ("7.600902709541988", .lt)
#guard D (T "-1/1000000007" 53) == ("-21.416413024506358", .lt)
#guard D (T "3/1125899906842624" 53) == ("34.2518939198891", .lt)
#guard D (T "1/3000000000000000000000000000000" 53) == ("70.86931225904942", .lt)
#guard D (T "700/3" 53) == ("0.004285701166289194", .lt)
#guard D (T "1/3" 53 .Floor) == ("1.8184464592320666", .lt)
#guard D (T "-2/7" 53 .Floor) == ("-1.9657204716496517", .lt)
#guard D (T "22/7" 53 .Floor) == ("0.31304384340830893", .lt)
#guard D (T "-100/3" 53 .Floor) == ("-0.02999550182152426", .lt)
#guard D (T "1/1000000007" 53 .Floor) == ("21.416413024506355", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("1.8184464592320668", .gt)
#guard D (T "-2/7" 53 .Ceiling) == ("-1.9657204716496515", .gt)
#guard D (T "22/7" 53 .Ceiling) == ("0.313043843408309", .gt)
#guard D (T "-100/3" 53 .Ceiling) == ("-0.029995501821524256", .gt)
#guard D (T "1/1000000007" 53 .Ceiling) == ("21.416413024506358", .gt)
#guard D (T "1/3" 20) == ("1.818447", .gt)
#guard D (T "1/3" 1) == ("2.0", .gt)
#guard D (T "-22/7" 2) == ("-0.4", .lt)
#guard D (T "1/3" 113) == ("1.818446459232066823483698963560709", .gt)
#guard D (T "-7/5" 200) == ("-0.664330604589885180430840379877154481536816897552416255944839", .lt)

-- agreement with the float `acsch` at representable arguments, oddness
#guard T "3/2" 53 == acschPrecRound (X "1.5" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == acschPrecRound (X "-0.0048828125" 53) 53 .Floor
#guard T "100" 20 .Ceiling == acschPrecRound (X "100" 53) 20 .Ceiling
#guard acschRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := acschRatPrecRound q p (-m)
  acschRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "1000000/3") 53 .Floor
#guard toString (acschRat (Q "1/3") 200) == "1.8184464592320668234836989635607089937862539427681216\
  17451744"
#guard toString (acschRat (Q "-22/7") 200) == "-0.3130438434083089821206656200524819120245277732087\
  282932049765"

-- huge rationals: just inside `1/q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard D (acschRatPrecRound (pw 5000)⁻¹ 53 .Nearest) == ("7.079811261048173e-1506", .gt)
#guard D (acschRatPrecRound (pw 5000)⁻¹ 53 .Ceiling) == ("7.079811261048173e-1506", .gt)
#guard D (acschRatPrecRound (pw 5000)⁻¹ 53 .Floor) == ("7.079811261048172e-1506", .lt)
#guard D (acschRatPrecRound (-(pw 5000)⁻¹) 53 .Nearest) == ("-7.079811261048173e-1506", .lt)
#guard D (acschRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Nearest) == ("2.3599370870160575e-1506", .lt)
#guard D (acschRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Ceiling) == ("2.359937087016058e-1506", .gt)

-- a tiny rational: `acsch q` rounds like `ln (2/q)`
private def bigq : AzRat := Q "6" * (pw 5000)⁻¹
#guard acschRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest == lnRatPrecRound bigq 53 .Nearest
#guard acschRatPrecRound (Q "1/3" * pw 5000) 53 .Floor == lnRatPrecRound bigq 53 .Floor
