/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Tanh
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `tanh x`

The special values (`NaN`, `±∞ ↦ ±1`, `0`, `p = 0`), the correctly rounded 53-bit values from
`2^(−200)` to `700` in three modes, the transition to `±1` (`18` to `40`), 1-, 2-, 20-, 113-,
120- and 200-bit results, 200-bit strings, oddness, tiny arguments `±2^(−1000)`, `±2^(−2^30)`
(the value is just inside `x`, at no cost), and large arguments `±100`, `±2^20`, `±2^(2^30)`
(the value is just inside `±1`, at no cost).  References: an independent 6000-bit fixed-point
evaluation of `(e^(2x) − 1)/(e^(2x) + 1)` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := X "0.9999999999999999" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := tanhPrecRound x p m

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("1.0", .eq)
#guard D (A (infinity false) 53) == ("-1.0", .eq)
#guard D (A (infinity false) 1 .Floor) == ("-1.0", .eq)
#guard D (A (infinity true) 0) == ("NaN", .eq)
#guard D (A zero 53) == ("0.0", .eq)
#guard D (A zero 0) == ("0.0", .eq)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "1" 53) 53) == ("0.7615941559557649", .lt)
#guard D (A (X "-1" 53) 53) == ("-0.7615941559557649", .gt)
#guard D (A (X "2" 53) 53) == ("0.9640275800758169", .gt)
#guard D (A (X "0.5" 53) 53) == ("0.46211715726000974", .lt)
#guard D (A (X "-0.3333333333333333" 53) 53) == ("-0.32151273753163434", .lt)
#guard D (A (X "1.5" 53) 53) == ("0.9051482536448664", .lt)
#guard D (A (X "-1.4" 53) 53) == ("-0.8853516482022625", .lt)
#guard D (A (X "3.142857142857143" 53) 53) == ("0.9962814746419252", .lt)
#guard D (A (X "10" 53) 53) == ("0.9999999958776927", .lt)
#guard D (A (X "-100" 53) 53) == ("-1.0", .lt)
#guard D (A (X "0.001" 53) 53) == ("0.0009999996666668", .lt)
#guard D (A (X "-0.000000000001" 53) 53) == ("-1.0e-12", .lt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("8.881784197001252e-16", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("7.888609052210118e-31", .gt)
#guard D (A (X "-1.8669045833583425e-60" 53) 53)
  == ("-1.8669045833583425e-60", .lt)
#guard D (A (X "30" 53) 53) == ("1.0", .gt)
#guard D (A (X "-37" 53) 53) == ("-1.0", .lt)
#guard D (A (X "700" 53) 53) == ("1.0", .gt)
#guard D (A (X "1" 53) 53 .Floor) == ("0.7615941559557649", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-0.761594155955765", .lt)
#guard D (A (X "1.5" 53) 53 .Floor) == ("0.9051482536448664", .lt)
#guard D (A (X "-1.4" 53) 53 .Floor) == ("-0.8853516482022625", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("0.0009999996666668", .lt)
#guard D (A (X "-100" 53) 53 .Floor) == ("-1.0", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("7.888609052210117e-31", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("0.761594155955765", .gt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("-0.7615941559557649", .gt)
#guard D (A (X "1.5" 53) 53 .Ceiling) == ("0.9051482536448665", .gt)
#guard D (A (X "-1.4" 53) 53 .Ceiling) == ("-0.8853516482022624", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("0.0009999996666668002", .gt)
#guard D (A (X "-100" 53) 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling)
  == ("7.888609052210118e-31", .gt)
#guard D (A (X "1" 53) 20) == ("0.761594", .lt)
#guard D (A (X "1" 53) 1) == ("1.0", .gt)
#guard D (A (X "-1.5" 53) 2) == ("-1.0", .lt)
#guard D (A (X "1.5" 53) 113) == ("0.9051482536448664382423036964564956", .lt)
#guard D (A (X "0.3333333333333333333333333333333333333333333333333333333333334" 200) 200)
  == ("0.321512737531634344719406222425206466005292002502083511679805", .gt)
#guard D (A (X "0.3333333333333333333333333333333333333333333333333333333333334" 200) 10 .Floor)
  == ("0.3213", .lt)
#guard D (A (X "10" 53) 120) == ("0.999999995877692763619592837138275741", .lt)
#guard tanh (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString ((tanhPrecRound (X "1" 200) 200 .Nearest).1)
  == "0.761594155955764888119458282604793590412768597257936551596811"
#guard toString ((tanhPrecRound (X "-1.5" 200) 200 .Nearest).1)
  == "-0.905148253644866438242303696456495597227641135158781798564224"

-- the transition to `±1`
#guard D (A (X "18" 53) 53) == ("0.9999999999999996", .gt)
#guard D (A (X "18" 53) 53 .Floor) == ("0.9999999999999994", .lt)
#guard D (A (X "18" 53) 53 .Ceiling) == ("0.9999999999999996", .gt)
#guard D (A (X "-19" 53) 53) == ("-0.9999999999999999", .gt)
#guard D (A (X "-19" 53) 53 .Floor) == ("-1.0", .lt)
#guard D (A (X "-19" 53) 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard D (A (X "20" 53) 53) == ("1.0", .gt)
#guard D (A (X "20" 53) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (A (X "20" 53) 53 .Ceiling) == ("1.0", .gt)
#guard D (A (X "40" 53) 53) == ("1.0", .gt)
#guard D (A (X "40" 53) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (A (X "40" 53) 53 .Ceiling) == ("1.0", .gt)
#guard D (A (X "18.75" 53) 53) == ("0.9999999999999999", .lt)
#guard D (A (X "18.75" 53) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (A (X "18.75" 53) 53 .Ceiling) == ("1.0", .gt)

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 53 .Nearest && odd (X "1.5" 53) 53 .Floor
#guard odd (X "100" 53) 20 .Ceiling && odd (X "0.001" 53) 113 .Floor
#guard odd (h (X "1" 53) (-1000)) 53 .Ceiling && odd (h (X "1" 53) 1000) 53 .Ceiling

-- tiny arguments: just inside `x`
private def tinyOk (k : Int) : Bool :=
  let x := h (X "1" 53) (-k)
  A x 53 == (x, .gt) && A x 53 .Ceiling == (x, .gt) && A x 53 .Floor == (h dn (-k), .lt)
    && A (-x) 53 == (-x, .lt) && A (-x) 53 .Floor == (-x, .lt)
    && A (-x) 53 .Ceiling == (-(h dn (-k)), .gt)
#guard tinyOk 200
#guard tinyOk 1000
#guard tinyOk 1073741824

-- large arguments: just inside `±1`
private def bigOk (x : AzFloat) : Bool :=
  A x 53 == (X "1" 53, .gt) && A x 53 .Ceiling == (X "1" 53, .gt) && A x 53 .Floor == (dn, .lt)
    && A (-x) 53 == (X "-1" 53, .lt) && A (-x) 53 .Floor == (X "-1" 53, .lt)
    && A (-x) 53 .Ceiling == (-dn, .gt) && A x 1 .Floor == (X "0.5" 1, .lt)
    && A x 200 .Nearest == (X "1" 200, .gt)
#guard bigOk (X "1000" 53)
#guard bigOk (X "1048576" 53)
#guard bigOk (h (X "1" 53) 1073741824)
#guard bigOk (h (X "3" 53) 1073741824)
#guard D (A (X "100" 53) 53) == ("1.0", .gt)
#guard D (A (X "100" 53) 53 .Floor) == ("0.9999999999999999", .lt)
