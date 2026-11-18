/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acosh
import Azurite.AzFloat.Ln
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `acosh x`

The special values (`NaN`; `NaN` below `1`, including `0`, negative arguments and `−∞`;
`+∞`; `acosh 1 = 0`; `p = 0`), the correctly rounded 53-bit values from `1 + 2^(−52)` to
`2^100` in three modes — among them `1 + 2^(−51)`, where the value is within a relative
`2^(−54)` of the float `2^(−25)` — 1-, 2-, 20-, 113-, 120- and 200-bit results, a 201-bit
argument `1 + 2^(−200)`, 200-bit strings, and huge arguments `2^(2^30)` (where `acosh x`
rounds like `ln (2x)`).  References: an independent 6000-bit fixed-point evaluation of
`ln (x + √(x² − 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acoshPrecRound x p m
/-- `1 + 2^(−200)` at 201 bits. -/
private def x200 : AzFloat := (addPrecRound (X "1" 53) (h (X "1" 53) (-200)) 201 .Floor).1

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("Infinity", .eq)
#guard D (A (infinity true) 0) == ("Infinity", .eq)
#guard D (A (infinity false) 53) == ("NaN", .eq)
#guard D (A zero 53) == ("NaN", .eq)
#guard D (A (X "0.5" 53) 53) == ("NaN", .eq)
#guard D (A (X "0.9999999999999999" 53) 53) == ("NaN", .eq)
#guard D (A (X "-1" 53) 53) == ("NaN", .eq)
#guard D (A (X "-3" 53) 53) == ("NaN", .eq)
#guard D (A (h (X "1" 53) (-1000)) 53) == ("NaN", .eq)
#guard D (A (X "1" 53) 53) == ("0.0", .eq)
#guard D (A (X "1" 200) 1 .Floor) == ("0.0", .eq)
#guard D (A (X "1" 53) 0) == ("0.0", .eq)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "2" 53) 53) == ("1.3169578969248168", .gt)
#guard D (A (X "1.5" 53) 53) == ("0.9624236501192069", .gt)
#guard D (A (X "1.25" 53) 53) == ("0.6931471805599453", .lt)
#guard D (A (X "3.142857142857143" 53) 53) == ("1.8119507608214136", .gt)
#guard D (A (X "10" 53) 53) == ("2.993222846126381", .lt)
#guard D (A (X "100" 53) 53) == ("5.298292365610485", .gt)
#guard D (A (X "1000000000000" 53) 53) == ("28.324168296488494", .gt)
#guard D (A (X "700" 53) 53) == ("7.244227005398878", .gt)
#guard D (A (X "1.0000000000000002" 53) 53) == ("2.1073424255447014e-8", .lt)
#guard D (A (X "1.0000000000000004" 53) 53) == ("2.9802322387695312e-8", .gt)
#guard D (A (X "1.00000095367431640625" 53) 53) == ("0.0013810678222475811", .lt)
#guard D (A (X "1.9999999999999998" 53) 53) == ("1.3169578969248166", .lt)
#guard D (A (X "1267650600228229401496703205376" 53) 53) == ("70.00786523655448", .gt)
#guard D (A (X "2" 53) 53 .Floor) == ("1.3169578969248166", .lt)
#guard D (A (X "1.5" 53) 53 .Floor) == ("0.9624236501192068", .lt)
#guard D (A (X "1.0000000000000002" 53) 53 .Floor) == ("2.1073424255447014e-8", .lt)
#guard D (A (X "1.0000000000000004" 53) 53 .Floor) == ("2.980232238769531e-8", .lt)
#guard D (A (X "100" 53) 53 .Floor) == ("5.298292365610484", .lt)
#guard D (A (X "2" 53) 53 .Ceiling) == ("1.3169578969248168", .gt)
#guard D (A (X "1.5" 53) 53 .Ceiling) == ("0.9624236501192069", .gt)
#guard D (A (X "1.0000000000000002" 53) 53 .Ceiling)
  == ("2.1073424255447017e-8", .gt)
#guard D (A (X "1.0000000000000004" 53) 53 .Ceiling)
  == ("2.9802322387695312e-8", .gt)
#guard D (A (X "100" 53) 53 .Ceiling) == ("5.298292365610485", .gt)
#guard D (A (X "2" 53) 20) == ("1.316957", .lt)
#guard D (A (X "2" 53) 1) == ("1.0", .lt)
#guard D (A (X "1.5" 53) 2) == ("1.0", .gt)
#guard D (A (X "1.5" 53) 113) == ("0.9624236501192068949955178268487368", .lt)
#guard D (A (X "1.333333333333333333333333333333333333333333333333333333333334" 200) 200)
  == ("0.7953654612239056305278909331478063009765825637143671346533025", .lt)
#guard D (A (X "1.333333333333333333333333333333333333333333333333333333333334" 200) 10 .Floor)
  == ("0.795", .lt)
#guard D (A (X "10" 53) 120) == ("2.993222846126380897912667713774182913", .lt)
#guard D (A x200 53) == ("1.1156177909894717e-30", .gt)
#guard D (A x200 53 .Floor) == ("1.1156177909894715e-30", .lt)
#guard D (A x200 53 .Ceiling) == ("1.1156177909894717e-30", .gt)
#guard acosh (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString ((acoshPrecRound (X "2" 200) 200 .Nearest).1)
  == "1.316957896924816708625046347307968444026981971467516479768473"
#guard toString ((acoshPrecRound (X "1.5" 200) 200 .Nearest).1)
  == "0.9624236501192068949955178268487368462703686687713210393220363"

-- huge arguments: `acosh x` rounds like `ln (2x)`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  A x p m == lnPrecRound (h x 1) p m
#guard big (h (X "1" 53) 1073741824) 53 .Nearest && big (h (X "3" 53) 1073741824) 53 .Floor
#guard big (h (X "5" 53) 100000) 113 .Ceiling
