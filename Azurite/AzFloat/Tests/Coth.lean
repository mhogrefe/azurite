/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Coth
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `coth x`

The special values (`NaN`, `±∞ ↦ ±1`, `coth 0 = +∞`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `700` in three modes, the transition to `±1` (`18` to `40`), 1-, 2-,
20-, 113-, 120- and 200-bit results, 200-bit strings, oddness, tiny arguments `±2^(−1000)`,
`±2^(−2^30)` (the value is just outside `1/x`, at no cost), and large arguments `±1000`,
`±2^20`, `±2^(2^30)` (the value is just outside `±1`, at no cost).  References: an independent
6000-bit fixed-point evaluation of `(e^(2x) + 1)/(e^(2x) − 1)` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := X "1.0000000000000002" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cothPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("1.0", .eq)
#guard D (A (infinity false) 53) == ("-1.0", .eq)
#guard D (A (infinity false) 1 .Floor) == ("-1.0", .eq)
#guard D (A (infinity true) 0) == ("NaN", .eq)
#guard D (A zero 53) == ("Infinity", .eq)
#guard D (A zero 0) == ("Infinity", .eq)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "1" 53) 53) == ("1.3130352854993312", .lt)
#guard D (A (X "-1" 53) 53) == ("-1.3130352854993312", .gt)
#guard D (A (X "2" 53) 53) == ("1.0373147207275482", .gt)
#guard D (A (X "0.5" 53) 53) == ("2.163953413738653", .gt)
#guard D (A (X "-0.3333333333333333" 53) 53) == ("-3.110296679619444", .gt)
#guard D (A (X "1.5" 53) 53) == ("1.104791392982512", .gt)
#guard D (A (X "-1.4" 53) 53) == ("-1.1294947064598966", .lt)
#guard D (A (X "3.142857142857143" 53) 53) == ("1.0037324043984772", .gt)
#guard D (A (X "10" 53) 53) == ("1.0000000041223072", .lt)
#guard D (A (X "-100" 53) 53) == ("-1.0", .gt)
#guard D (A (X "0.001" 53) 53) == ("1000.0003333333111", .gt)
#guard D (A (X "-0.000000000001" 53) 53) == ("-1.0e12", .gt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("1125899906842624.0", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("1.2676506002282294e30", .lt)
#guard D (A (X "-1.8669045833583425e-60" 53) 53)
  == ("-5.356460147529967e59", .gt)
#guard D (A (X "30" 53) 53) == ("1.0", .lt)
#guard D (A (X "-37" 53) 53) == ("-1.0", .gt)
#guard D (A (X "700" 53) 53) == ("1.0", .lt)
#guard D (A (X "1" 53) 53 .Floor) == ("1.3130352854993312", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-1.3130352854993315", .lt)
#guard D (A (X "1.5" 53) 53 .Floor) == ("1.1047913929825117", .lt)
#guard D (A (X "-1.4" 53) 53 .Floor) == ("-1.1294947064598966", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("1000.000333333311", .lt)
#guard D (A (X "-100" 53) 53 .Floor) == ("-1.0000000000000002", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("1.2676506002282294e30", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("1.3130352854993315", .gt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("-1.3130352854993312", .gt)
#guard D (A (X "1.5" 53) 53 .Ceiling) == ("1.104791392982512", .gt)
#guard D (A (X "-1.4" 53) 53 .Ceiling) == ("-1.1294947064598964", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("1000.0003333333111", .gt)
#guard D (A (X "-100" 53) 53 .Ceiling) == ("-1.0", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling) == ("1.2676506002282297e30\
  ", .gt)
#guard D (A (X "1" 53) 20) == ("1.313036", .gt)
#guard D (A (X "1" 53) 1) == ("1.0", .lt)
#guard D (A (X "-1.5" 53) 2) == ("-1.0", .gt)
#guard D (A (X "1.5" 53) 113) == ("1.10479139298251190394399878919951", .lt)
#guard D (A (X "0.3333333333333333333333333333333333333333333333333333333333334" 200) 200) == ("3.1\
  10296679619443701378375231417624794566543581787011086057342\
  ", .lt)
#guard D (A (X "0.333333333333333333333333333333333333333333333333333333333333\
  4" 200) 10 .Floor) == ("3.11", .lt)
#guard D (A (X "10" 53) 120) == ("1.000000004122307253373824184028080313", .gt)
#guard coth (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString (cothPrecRound (X "1" 200) 200 .Nearest).1 == "1.3130352854993313036361612469308478\
  32912013941240452655543153"
#guard toString (cothPrecRound (X "-1.5" 200) 200 .Nearest).1 == "-1.104791392982511903943998789199\
  510110407804997609659742035555"

-- the transition to `±1`
#guard D (A (X "18" 53) 53) == ("1.0000000000000004", .lt)
#guard D (A (X "18" 53) 53 .Floor) == ("1.0000000000000004", .lt)
#guard D (A (X "18" 53) 53 .Ceiling) == ("1.0000000000000007", .gt)
#guard D (A (X "-19" 53) 53) == ("-1.0", .gt)
#guard D (A (X "-19" 53) 53 .Floor) == ("-1.0000000000000002", .lt)
#guard D (A (X "-19" 53) 53 .Ceiling) == ("-1.0", .gt)
#guard D (A (X "20" 53) 53) == ("1.0", .lt)
#guard D (A (X "20" 53) 53 .Floor) == ("1.0", .lt)
#guard D (A (X "20" 53) 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (A (X "40" 53) 53) == ("1.0", .lt)
#guard D (A (X "40" 53) 53 .Floor) == ("1.0", .lt)
#guard D (A (X "40" 53) 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (A (X "18.75" 53) 53) == ("1.0", .lt)
#guard D (A (X "18.75" 53) 53 .Floor) == ("1.0", .lt)
#guard D (A (X "18.75" 53) 53 .Ceiling) == ("1.0000000000000002", .gt)

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 53 .Nearest && odd (X "1.5" 53) 53 .Floor
#guard odd (X "100" 53) 20 .Ceiling && odd (X "0.001" 53) 113 .Floor
#guard odd (h (X "1" 53) (-1000)) 53 .Ceiling && odd (h (X "1" 53) 1000) 53 .Ceiling

-- tiny arguments: just outside `1/x`
private def tinyOk (k : Int) : Bool :=
  let x := h (X "1" 53) (-k)
  let y := h (X "1" 53) k
  A x 53 == (y, .lt) && A x 53 .Floor == (y, .lt) && A x 53 .Ceiling == (h up k, .gt)
    && A (-x) 53 == (-y, .gt) && A (-x) 53 .Ceiling == (-y, .gt)
    && A (-x) 53 .Floor == (-(h up k), .lt)
#guard tinyOk 100
#guard tinyOk 1000
#guard tinyOk 1073741824

-- large arguments: just outside `±1`
private def bigOk (x : AzFloat) : Bool :=
  A x 53 == (X "1" 53, .lt) && A x 53 .Floor == (X "1" 53, .lt) && A x 53 .Ceiling == (up, .gt)
    && A (-x) 53 == (X "-1" 53, .gt) && A (-x) 53 .Ceiling == (X "-1" 53, .gt)
    && A (-x) 53 .Floor == (-up, .lt) && A x 1 .Ceiling == (X "2" 1, .gt)
    && A x 200 .Nearest == (X "1" 200, .lt)
#guard bigOk (X "1000" 53)
#guard bigOk (X "1048576" 53)
#guard bigOk (h (X "1" 53) 1073741824)
#guard bigOk (h (X "3" 53) 1073741824)
#guard D (A (X "100" 53) 53) == ("1.0", .lt)
#guard D (A (X "100" 53) 53 .Ceiling) == ("1.0000000000000002", .gt)
