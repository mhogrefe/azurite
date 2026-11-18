/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asin
import Azurite.AzFloat.AsinRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsin q` of a rational

The special values (`0`; `±1` give `±π/2` in every mode; `|q| > 1` gives `NaN`; `p = 0`), the
correctly rounded 53-bit values at the exact rationals `1/3`, `1/10`, `−7/10`, `3/4`, `−22/23`,
`1 − 10⁻⁶`, `1/(10⁹ + 7)`, `5/7`, `−1/1000`, `355/452`, agreement with the float `asin` at
representable arguments, the directed modes, 1-, 20- and 113-bit results, a 200-bit string, the
rational `±(1 − 2^(−200))` next to `±1` (not representable at the target precision), and the
tiny paths at `±1/(3·2^1000)` and at the exactly representable `±2^(−5000)`.  References: an
independent 1400-bit fixed-point evaluation of `arctan (q/√(1 − q²))` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinRatPrecRound (Q q) p m
private def piN : AzFloat := X "1.5707963267948966" 53
private def piC : AzFloat := X "1.5707963267948968" 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("0.0", .eq)
#guard D (T "0" 0) == ("0.0", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)
#guard D (T "1" 53) == ("1.5707963267948966", .lt)
#guard D (T "1" 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (T "-1" 53) == ("-1.5707963267948966", .gt)
#guard D (T "-1" 53 .Floor) == ("-1.5707963267948968", .lt)
#guard D (T "3/2" 53) == ("NaN", .eq)
#guard D (T "-22/7" 53) == ("NaN", .eq)
#guard D (T "1000001/1000000" 53) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1/3" 53) == ("0.3398369094541219", .lt)
#guard D (T "1/10" 53) == ("0.1001674211615598", .gt)
#guard D (T "-7/10" 53) == ("-0.7753974966107531", .lt)
#guard D (T "3/4" 53) == ("0.848062078981481", .lt)
#guard D (T "-22/23" 53) == ("-1.2748334052973291", .gt)
#guard D (T "999999/1000000" 53) == ("1.5693821131146724", .lt)
#guard D (T "1/1000000007" 53) == ("9.99999993e-10", .gt)
#guard D (T "5/7" 53) == ("0.7956029534845354", .gt)
#guard D (T "-1/1000" 53) == ("-0.0010000001666667416", .gt)
#guard D (T "355/452" 53) == ("0.9033392185080849", .lt)
#guard D (T "1/3" 53 .Floor) == ("0.3398369094541219", .lt)
#guard D (T "-3/4" 53 .Floor) == ("-0.8480620789814811", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("0.339836909454122", .gt)
#guard D (T "-3/4" 53 .Ceiling) == ("-0.848062078981481", .gt)
#guard D (T "1/3" 20) == ("0.339837", .gt)
#guard D (T "1/3" 1) == ("0.2", .lt)
#guard D (T "3/4" 113) == ("0.8480620789814810080529443389984181", .gt)

-- agreement with the float `asin` at representable arguments
#guard T "1/2" 53 == asinPrecRound (X "0.5" 53) 53 .Nearest
#guard T "-3/4" 53 .Floor == asinPrecRound (X "-0.75" 53) 53 .Floor
#guard T "1/1024" 53 == asinPrecRound (X "0.0009765625" 53) 53 .Nearest
#guard asinRat (Q "1/3") 53 == (T "1/3" 53).1
#guard toString (asinRat (Q "1/3") 200) == "0.33983690945412193709639251339176406638824469033245807\
  1431924"

-- a rational next to `±1`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def near1 : AzRat := 1 - pw 200
#guard D (asinRatPrecRound near1 53 .Nearest) == ("1.5707963267948966", .lt)
#guard D (asinRatPrecRound near1 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (asinRatPrecRound (-near1) 53 .Floor) == ("-1.5707963267948968", .lt)

-- tiny arguments
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some 53
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def tinyLo : AzFloat := (ofAzRatRound tinyQ 53 .Floor).1
private def tinyHi : AzFloat := (ofAzRatRound tinyQ 53 .Ceiling).1
#guard D (asinRatPrecRound tinyQ 53 .Nearest) == ("3.110878728344063e-302", .lt)
#guard D (asinRatPrecRound tinyQ 53 .Floor) == ("3.110878728344063e-302", .lt)
#guard D (asinRatPrecRound tinyQ 53 .Ceiling) == ("3.1108787283440633e-302", .gt)
#guard D (asinRatPrecRound (-tinyQ) 53 .Floor) == ("-3.1108787283440633e-302", .lt)
#guard D (asinRatPrecRound (-tinyQ) 53 .Ceiling) == ("-3.110878728344063e-302", .gt)
#guard D (asinRatPrecRound (pw 5000) 53 .Nearest) == ("7.079811261048173e-1506", .lt)
#guard (asinRatPrecRound (pw 5000) 53 .Ceiling).2 == .gt
#guard D (asinRatPrecRound (-(pw 5000)) 53 .Nearest) == ("-7.079811261048173e-1506", .gt)
#guard (asinTinyRat? tinyQ 53 .Nearest).isSome
#guard (asinTinyRat? (Q "1/1000") 53 .Nearest).isNone
