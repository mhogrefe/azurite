/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acos
import Azurite.AzFloat.AcosRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccos q` of a rational

The special values (`arccos 1 = 0`; `arccos 0 = π/2` and `arccos (−1) = π` in several modes;
`|q| > 1` gives `NaN`; `p = 0`), the correctly rounded 53-bit values at exact rationals,
agreement with the float `acos` at representable arguments, the directed modes, 20- and 113-bit
results, a 200-bit string, and the rationals `±(1 − 2^(−200))` next to `±1` (the first gives a
result of size `2^(−99.5)` with full relative accuracy).  References: an independent 1400-bit
fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acosRatPrecRound (Q q) p m
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "1" 53) == ("0.0", .eq)
#guard D (T "1" 0) == ("0.0", .eq)
#guard D (T "0" 53) == ("1.5707963267948966", .lt)
#guard D (T "0" 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (T "-1" 53) == ("3.141592653589793", .lt)
#guard D (T "-1" 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (T "3/2" 53) == ("NaN", .eq)
#guard D (T "-22/7" 53) == ("NaN", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1/3" 53) == ("1.2309594173407747", .gt)
#guard D (T "-1/3" 53) == ("1.9106332362490186", .gt)
#guard D (T "1/10" 53) == ("1.4706289056333368", .lt)
#guard D (T "-7/10" 53) == ("2.34619382340565", .gt)
#guard D (T "3/4" 53) == ("0.7227342478134157", .gt)
#guard D (T "-22/23" 53) == ("2.8456297320922257", .lt)
#guard D (T "999999/1000000" 53) == ("0.0014142136802242518", .gt)
#guard D (T "1/1000000007" 53) == ("1.5707963257948967", .gt)
#guard D (T "355/452" 53) == ("0.6674571082868117", .lt)
#guard D (T "1/3" 53 .Floor) == ("1.2309594173407745", .lt)
#guard D (T "-3/4" 53 .Floor) == ("2.4188584057763776", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("1.2309594173407747", .gt)
#guard D (T "-3/4" 53 .Ceiling) == ("2.418858405776378", .gt)
#guard D (T "1/3" 20) == ("1.230959", .lt)
#guard D (T "3/4" 113) == ("0.7227342478134156111783773526413333", .lt)

-- agreement with the float `acos` at representable arguments
#guard T "1/2" 53 == acosPrecRound (X "0.5" 53) 53 .Nearest
#guard T "-3/4" 53 .Floor == acosPrecRound (X "-0.75" 53) 53 .Floor
#guard T "1/1024" 53 == acosPrecRound (X "0.0009765625" 53) 53 .Nearest
#guard acosRat (Q "1/3") 53 == (T "1/3" 53).1
#guard toString (acosRat (Q "1/3") 200) == "1.23095941734077468213492917824798737571034000935509483\
  9055549"

-- rationals next to `±1`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def near1 : AzRat := 1 - pw 200
#guard D (acosRatPrecRound near1 53 .Nearest) == ("1.1156177909894717e-30", .gt)
#guard D (acosRatPrecRound (-near1) 53 .Nearest) == ("3.141592653589793", .lt)
#guard D (acosRatPrecRound (-near1) 53 .Ceiling) == ("3.1415926535897936", .gt)
-- a tiny rational: next to `π/2`
#guard D (acosRatPrecRound (pw 5000) 53 .Nearest) == ("1.5707963267948966", .lt)
#guard D (acosRatPrecRound (-(pw 5000)) 53 .Ceiling) == ("1.5707963267948968", .gt)
