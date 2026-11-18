/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Pi
import Azurite.AzFloat.AtanPi
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `atan2 (y, x) / π`

`atan2Pi`: the special values (`NaN`; `±1/4`, `±3/4`, `±1/2` for `y = ±∞`; `0`, `±1` for
`x = ±∞`; the axes; the diagonals; `p = 0`), the correctly rounded 53-bit values in all eight
octants, the directed modes, 20- and 113-bit results, agreement with `atanPi` for `x = 1`, and
extreme ratios `2^(±2^30)`.  `atan2PiRat`: the special values, exact rationals, the directed
modes, agreement with the float function, and extreme ratios.  References: an independent
1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (y x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2PiPrecRound y x p m
private def PR (y x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2PiRatPrecRound (Q y) (Q x) p m
private def inf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
private def one' : AzFloat := X "1" 53

-- special values
#guard D (P nan one' 53) == ("NaN", .eq)
#guard D (P one' nan 53) == ("NaN", .eq)
#guard D (P inf inf 53) == ("0.25", .eq)
#guard D (P ninf inf 53) == ("-0.25", .eq)
#guard D (P inf ninf 53) == ("0.75", .eq)
#guard D (P ninf ninf 53) == ("-0.75", .eq)
#guard D (P inf ninf 1) == ("1.0", .gt)
#guard D (P inf one' 53) == ("0.5", .eq)
#guard D (P ninf zero 53) == ("-0.5", .eq)
#guard D (P one' inf 53) == ("0.0", .eq)
#guard D (P one' ninf 53) == ("1.0", .eq)
#guard D (P (-one') ninf 53) == ("-1.0", .eq)
#guard D (P zero ninf 53) == ("1.0", .eq)
#guard D (P zero zero 53) == ("0.0", .eq)
#guard D (P zero (X "3" 53) 53) == ("0.0", .eq)
#guard D (P zero (X "-3" 53) 53) == ("1.0", .eq)
#guard D (P (X "2" 53) zero 53) == ("0.5", .eq)
#guard D (P (X "-2" 53) zero 53) == ("-0.5", .eq)
#guard D (P (X "3" 53) (X "3" 53) 53) == ("0.25", .eq)
#guard D (P (X "-3" 53) (X "-3" 53) 53) == ("-0.75", .eq)
#guard D (P (X "3" 53) (X "-3" 53) 1 .Floor) == ("0.5", .lt)
#guard D (P one' (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (P (X "1" 53) (X "2" 53) 53) == ("0.14758361765043326", .lt)
#guard D (P (X "2" 53) (X "1" 53) 53) == ("0.35241638234956674", .gt)
#guard D (P (X "1" 53) (X "-2" 53) 53) == ("0.8524163823495667", .gt)
#guard D (P (X "2" 53) (X "-1" 53) 53) == ("0.6475836176504333", .lt)
#guard D (P (X "-1" 53) (X "2" 53) 53) == ("-0.14758361765043326", .gt)
#guard D (P (X "-2" 53) (X "1" 53) 53) == ("-0.35241638234956674", .lt)
#guard D (P (X "-1" 53) (X "-2" 53) 53) == ("-0.8524163823495667", .lt)
#guard D (P (X "-2" 53) (X "-1" 53) 53) == ("-0.6475836176504333", .gt)
#guard D (P (X "0.3333333333333333" 53) (X "1.4" 53) 53) == ("0.07440276529861721", .lt)
#guard D (P (X "1" 53) (X "-2" 53) 53 .Floor) == ("0.8524163823495666", .lt)
#guard D (P (X "1" 53) (X "-2" 53) 53 .Ceiling) == ("0.8524163823495667", .gt)
#guard D (P (X "1" 53) (X "2" 53) 20) == ("0.1475837", .gt)
#guard D (P (X "-2" 53) (X "1" 53) 113) == ("-0.35241638234956672582459892377525946", .gt)
#guard P (X "0.3333333333333333" 53) one' 53
  == atanPiPrecRound (X "0.3333333333333333" 53) 53 .Nearest
#guard atan2Pi (X "1" 53) (X "2" 53) == (P (X "1" 53) (X "2" 53) 53).1
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard D (P huge tiny 53) == ("0.5", .gt)
#guard D (P huge (-tiny) 53) == ("0.5", .lt)
#guard D (P tiny (-huge) 53) == ("1.0", .gt)
#guard D (P (-tiny) (-huge) 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard (P tiny huge 53).2 == .gt
#guard (P tiny huge 53 .Floor).2 == .lt

-- rationals
#guard D (PR "0" "0" 53) == ("0.0", .eq)
#guard D (PR "0" "-2/3" 53) == ("1.0", .eq)
#guard D (PR "2/3" "0" 53) == ("0.5", .eq)
#guard D (PR "-2/3" "2/3" 53) == ("-0.25", .eq)
#guard D (PR "2/3" "-2/3" 53) == ("0.75", .eq)
#guard D (PR "1/3" "7/5" 0) == ("NaN", .eq)
#guard D (PR "1" "3" 53) == ("0.10241638234956672", .lt)
#guard D (PR "-3" "1" 53) == ("-0.39758361765043326", .gt)
#guard D (PR "1/3" "7/5" 53) == ("0.07440276529861721", .gt)
#guard D (PR "22/7" "-1/1000" 53) == ("0.5001012804149133", .lt)
#guard D (PR "1" "-3" 53 .Floor) == ("0.8975836176504333", .lt)
#guard D (PR "1" "-3" 53 .Ceiling) == ("0.8975836176504334", .gt)
#guard D (PR "1" "3" 20) == ("0.1024164", .gt)
#guard PR "1/2" "-3" 53 == P (X "0.5" 53) (X "-3" 53) 53
#guard atan2PiRat (Q "1") (Q "3") 53 == (PR "1" "3" 53).1
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard D (atan2PiRatPrecRound (Q "1") (pw 5000) 53 .Nearest) == ("0.5", .gt)
#guard D (atan2PiRatPrecRound (pw 5000) (Q "-1") 53 .Nearest) == ("1.0", .gt)
#guard D (atanPiRatPrecRound (pw 5000)⁻¹ 53 .Nearest) == ("0.5", .gt)
