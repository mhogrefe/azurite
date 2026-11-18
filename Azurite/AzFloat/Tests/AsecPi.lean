/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecPi
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asecPiPrecRound x p m
private def PR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asecPiRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (P nan 53) == ("NaN", .eq)
#guard D (P zero 53) == ("NaN", .eq)
#guard D (P (X "0.5" 53) 53) == ("NaN", .eq)
#guard D (P (infinity true) 53) == ("0.5", .eq)
#guard D (P (infinity false) 53) == ("0.5", .eq)
#guard D (P (X "1" 53) 53) == ("0.0", .eq)
#guard D (P (X "-1" 53) 53) == ("1.0", .eq)
#guard D (P (X "3" 53) 0) == ("NaN", .eq)
#guard D (P (X "2" 53) 53) == ("0.3333333333333333", .lt)
#guard D (P (X "2" 53) 53 .Ceiling) == ("0.33333333333333337", .gt)
#guard D (P (X "-2" 53) 53) == ("0.6666666666666666", .lt)
#guard D (P (X "-2" 53) 53 .Ceiling) == ("0.6666666666666667", .gt)

-- correctly rounded values
#guard D (P (X "3" 53) 53) == ("0.3918265520306073", .gt)
#guard D (P (X "-3" 53) 53) == ("0.6081734479693928", .gt)
#guard D (P (X "1.5" 53) 53) == ("0.26772047280123", .gt)
#guard D (P (X "-1.4" 53) 53) == ("0.7532482855711502", .gt)
#guard D (P (X "100" 53) 53) == ("0.4968168480841269", .lt)
#guard D (P (X "1.5" 53) 53 .Floor) == ("0.26772047280122996", .lt)
#guard D (P (X "1.5" 53) 53 .Ceiling) == ("0.26772047280123", .gt)
#guard D (P (X "1.5" 53) 20) == ("0.2677207", .gt)
#guard toString (asecPi (X "1.5" 53)) == "0.26772047280123"
#guard toString (asecPiPrecRound (X "1.5" 200) 200 .Nearest).1 == "0.267720472801230010745233795941\
  2318914943660025783258458145956"
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard P huge 53 == (X "0.5" 53, .gt)
#guard P (-huge) 53 == (X "0.5" 53, .lt)
#guard (P huge 53 .Floor).2 == .lt

-- rationals
#guard D (PR "1" 53) == ("0.0", .eq)
#guard D (PR "-1" 53) == ("1.0", .eq)
#guard D (PR "1/2" 53) == ("NaN", .eq)
#guard D (PR "0" 53) == ("NaN", .eq)
#guard D (PR "3" 0) == ("NaN", .eq)
#guard D (PR "2" 53) == ("0.3333333333333333", .lt)
#guard D (PR "-4/2" 53 .Ceiling) == ("0.6666666666666667", .gt)
#guard D (PR "3" 53) == ("0.3918265520306073", .gt)
#guard D (PR "-7/5" 53) == ("0.7532482855711501", .lt)
#guard D (PR "22/7" 53) == ("0.39692775258321855", .lt)
#guard D (PR "3" 53 .Floor) == ("0.39182655203060723", .lt)
#guard D (PR "3" 53 .Ceiling) == ("0.3918265520306073", .gt)
#guard D (PR "3/2" 53) == ("0.26772047280123", .gt)
#guard asecPiRat (Q "3") 53 == (PR "3" 53).1
