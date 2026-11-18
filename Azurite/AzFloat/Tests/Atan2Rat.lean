/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Rat
import Azurite.AzFloat.AtanRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atan2 (y, x)` of rationals

The special values (`y = 0` against the sign of `x`; `x = 0`; `p = 0`), the correctly rounded
53-bit values in all eight octants and on the diagonals, at rationals that are not floats
(`(1/3, 7/5)`, `(22/7, −1/1000)`, …), agreement with the float `atan2` at representable
arguments and with `atanRat` for `x = 1`, invariance under a common positive factor, the
directed modes, 1-, 20- and 113-bit results, a 200-bit string, and tiny and huge ratios
(`1/(3·2^1000)`, the exactly representable `2^(−200)` and `2^(−5000)` with both signs, in every
octant).  References: an independent 1400-bit fixed-point evaluation rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def B (y x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2RatPrecRound (Q y) (Q x) p m
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (B "0" "0" 53) == ("0.0", .eq)
#guard D (B "0" "3/7" 53) == ("0.0", .eq)
#guard D (B "0" "3/7" 0) == ("0.0", .eq)
#guard D (B "0" "-3/7" 53) == ("3.141592653589793", .lt)
#guard D (B "0" "-3/7" 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (B "2/3" "0" 53) == ("1.5707963267948966", .lt)
#guard D (B "-2/3" "0" 53) == ("-1.5707963267948966", .gt)
#guard D (B "-2/3" "0" 53 .Floor) == ("-1.5707963267948968", .lt)
#guard D (B "1/3" "7/5" 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (B "1" "1" 53) == ("0.7853981633974483", .lt)
#guard D (B "1" "-1" 53) == ("2.356194490192345", .lt)
#guard D (B "-1" "-1" 53) == ("-2.356194490192345", .gt)
#guard D (B "-1" "1" 53) == ("-0.7853981633974483", .gt)
#guard D (B "1" "3" 53) == ("0.3217505543966422", .lt)
#guard D (B "3" "1" 53) == ("1.2490457723982544", .gt)
#guard D (B "1" "-3" 53) == ("2.819842099193151", .lt)
#guard D (B "3" "-1" 53) == ("1.892546881191539", .gt)
#guard D (B "-1" "3" 53) == ("-0.3217505543966422", .gt)
#guard D (B "-3" "1" 53) == ("-1.2490457723982544", .lt)
#guard D (B "-1" "-3" 53) == ("-2.819842099193151", .gt)
#guard D (B "-3" "-1" 53) == ("-1.892546881191539", .lt)
#guard D (B "1/3" "7/5" 53) == ("0.23374318086890142", .lt)
#guard D (B "-7/5" "1/3" 53) == ("-1.3370531459259951", .gt)
#guard D (B "22/7" "-1/1000" 53) == ("1.5711145086023408", .lt)
#guard D (B "1/1000" "-22/7" 53) == ("3.141274471782349", .lt)
#guard D (B "355/113" "1000000007/3" 53) == ("9.424778695088495e-9", .lt)
#guard D (B "1000000007/3" "355/113" 53) == ("1.5707963173701178", .lt)
#guard D (B "-1/1000000000000000000000000000000" "-1" 53) == ("-3.141592653589793", .gt)
#guard D (B "1" "3" 53 .Floor) == ("0.3217505543966422", .lt)
#guard D (B "-3" "-1" 53 .Floor) == ("-1.892546881191539", .lt)
#guard D (B "3" "-1" 53 .Floor) == ("1.8925468811915387", .lt)
#guard D (B "1" "3" 53 .Ceiling) == ("0.32175055439664224", .gt)
#guard D (B "-3" "-1" 53 .Ceiling) == ("-1.8925468811915387", .gt)
#guard D (B "3" "-1" 53 .Ceiling) == ("1.892546881191539", .gt)
#guard D (B "1" "3" 20) == ("0.3217506", .gt)
#guard D (B "1" "-3" 1) == ("2.0", .lt)
#guard D (B "-3" "1" 113) == ("-1.24904577239825442582991707728109", .gt)

-- agreement with the float `atan2`, with `atanRat`, and homogeneity
#guard B "1/2" "-3" 53 == atan2PrecRound (X "0.5" 53) (X "-3" 53) 53 .Nearest
#guard B "-5" "1/1024" 53 .Floor == atan2PrecRound (X "-5" 53) (X "0.0009765625" 53) 53 .Floor
#guard B "1/3" "1" 53 == atanRatPrecRound (Q "1/3") 53 .Nearest
#guard B "-22/7" "1" 53 .Ceiling == atanRatPrecRound (Q "-22/7") 53 .Ceiling
#guard B "2/21" "-2/5" 53 == B "5" "-21" 53
#guard atan2Rat (Q "1") (Q "3") 53 == (B "1" "3" 53).1
#guard toString (atan2Rat (Q "1") (Q "-2") 200) == "2.677945044588987122248387151818288482168632345\
  088985557164012"

-- tiny and huge ratios
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some 53
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def one' : AzRat := Q "1"
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard atan2RatPrecRound tinyQ one' 53 .Nearest == atanRatPrecRound tinyQ 53 .Nearest
#guard atan2RatPrecRound (-tinyQ) one' 53 .Floor == atanRatPrecRound (-tinyQ) 53 .Floor
#guard D (atan2RatPrecRound (pw 200) one' 53 .Nearest) == ("6.223015277861142e-61", .gt)
#guard (atan2RatPrecRound (pw 200) one' 53 .Floor).2 == .lt
#guard D (atan2RatPrecRound (-(pw 200)) one' 53 .Nearest) == ("-6.223015277861142e-61", .lt)
#guard D (atan2RatPrecRound (pw 5000) one' 53 .Nearest) == ("7.079811261048173e-1506", .gt)
#guard D (atan2RatPrecRound one' (pw 5000)⁻¹ 53 .Nearest) == ("7.079811261048173e-1506", .gt)
#guard D (atan2RatPrecRound one' (pw 5000) 53 .Nearest) == ("1.5707963267948966", .lt)
#guard D (atan2RatPrecRound (pw 5000) (-one') 53 .Nearest) == ("3.141592653589793", .lt)
#guard D (atan2RatPrecRound (-(pw 5000)) (-one') 53 .Floor) == ("-3.1415926535897936", .lt)
#guard D (atan2RatPrecRound (-one') (-(pw 5000)) 53 .Nearest) == ("-1.5707963267948966", .gt)
