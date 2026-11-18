/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcoshRat
import Azurite.AzFloat.Acosh
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `acosh q` of a rational

The special values (`NaN` below `1`, `acosh 1 = 0`, `p = 0`), the correctly rounded 53-bit
values at exact rationals from `1 + 10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113-
and 200-bit results, agreement with the float `acosh` at representable arguments, 200-bit
strings, rationals extremely close to `1` (`1 + 2^(−5000)`, where the value is `≈ 2^(−2499.5)`),
and a huge rational (where `acosh q` rounds like `ln (2q)`).  References: an independent
6000-bit fixed-point evaluation of `ln (q + √(q² − 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acoshRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "1" 53) == ("0.0", .eq)
#guard D (T "3/3" 0) == ("0.0", .eq)
#guard D (T "0" 53) == ("NaN", .eq)
#guard D (T "1/2" 53) == ("NaN", .eq)
#guard D (T "999999/1000000" 53) == ("NaN", .eq)
#guard D (T "-1" 53) == ("NaN", .eq)
#guard D (T "-3" 53) == ("NaN", .eq)
#guard D (T "4/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "2" 53) == ("1.3169578969248168", .gt)
#guard D (T "4/3" 53) == ("0.7953654612239056", .lt)
#guard D (T "22/7" 53) == ("1.8119507608214136", .gt)
#guard D (T "355/113" 53) == ("1.811526362033495", .gt)
#guard D (T "7/5" 53) == ("0.8670147264905651", .lt)
#guard D (T "10" 53) == ("2.993222846126381", .lt)
#guard D (T "100/3" 53) == ("4.199480001904436", .gt)
#guard D (T "1000001/1000000" 53) == ("0.0014142134445219914", .lt)
#guard D (T "1000000007/1000000006" 53) == ("0.00004472135941210494", .gt)
#guard D (T "700/3" 53) == ("6.145610635066878", .lt)
#guard D (T "3000000000000000000000000000001/3000000000000000000000000000000" 53)
  == ("8.16496580927726e-16", .gt)
#guard D (T "4/3" 53 .Floor) == ("0.7953654612239056", .lt)
#guard D (T "22/7" 53 .Floor) == ("1.8119507608214134", .lt)
#guard D (T "1000001/1000000" 53 .Floor) == ("0.0014142134445219914", .lt)
#guard D (T "100/3" 53 .Floor) == ("4.199480001904435", .lt)
#guard D (T "4/3" 53 .Ceiling) == ("0.7953654612239057", .gt)
#guard D (T "22/7" 53 .Ceiling) == ("1.8119507608214136", .gt)
#guard D (T "1000001/1000000" 53 .Ceiling) == ("0.0014142134445219916", .gt)
#guard D (T "100/3" 53 .Ceiling) == ("4.199480001904436", .gt)
#guard D (T "4/3" 20) == ("0.795365", .lt)
#guard D (T "4/3" 1) == ("1.0", .gt)
#guard D (T "22/7" 2) == ("2.0", .gt)
#guard D (T "4/3" 113) == ("0.7953654612239056305278909331478063", .lt)
#guard D (T "7/5" 200) == ("0.867014726490565103950520269501467375464496489945643731323534", .gt)

-- agreement with the float `acosh` at representable arguments
#guard T "3/2" 53 == acoshPrecRound (X "1.5" 53) 53 .Nearest
#guard T "1025/1024" 53 .Floor == acoshPrecRound (X "1.0009765625" 53) 53 .Floor
#guard T "100" 20 .Ceiling == acoshPrecRound (X "100" 53) 20 .Ceiling
#guard acoshRat (Q "4/3") 53 == (T "4/3" 53).1
#guard toString (acoshRat (Q "4/3") 200)
  == "0.795365461223905630527890933147806300976582563714367134653302"
#guard toString (acoshRat (Q "22/7") 200)
  == "1.811950760821413556235972813109322036695962129898042791003144"

-- next to `1`: `acosh (1 + 2^(−5000)) = √2 · 2^(−2500) (1 − …)`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard D (acoshRatPrecRound (1 + pw 5000) 53 .Nearest) == ("3.762927387300524e-753", .gt)
#guard D (acoshRatPrecRound (1 + pw 5000) 53 .Floor) == ("3.7629273873005234e-753", .lt)
-- `acosh (1 + 2^(−5001)) = 2^(−2500) (1 − 2^(−5001)/12 + …)`: just below a float
#guard D (acoshRatPrecRound (1 + pw 5001) 53 .Nearest) == ("2.6607914726727784e-753", .gt)
#guard D (acoshRatPrecRound (1 + pw 5001) 53 .Floor) == ("2.660791472672778e-753", .lt)

-- a huge rational: `acosh q` rounds like `ln (2q)`
private def bigq : AzRat := Q "2/3" * (pw 5000)⁻¹
#guard acoshRatPrecRound (Q "1/3" * (pw 5000)⁻¹) 53 .Nearest == lnRatPrecRound bigq 53 .Nearest
#guard acoshRatPrecRound (Q "1/3" * (pw 5000)⁻¹) 53 .Floor == lnRatPrecRound bigq 53 .Floor
