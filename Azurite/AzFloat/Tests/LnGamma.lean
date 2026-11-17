/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Parse

/-!
# Tests for `ln Γ`

* Special values: `NaN`, `±∞`, `0`, negative arguments, `p = 0`, and the exact zeros `x = 1`,
  `x = 2`.
* Integers: `ln Γ(n) = ln (n − 1)!` must agree with the correctly rounded `ln` of the exact
  factorial, in every mode — an oracle that shares nothing with Stirling's series.
* Dyadic non-integers (`1/2`, `3/2`, `5/4`, `7/2`, `17/8`, `33/32`, `2^(−10)`) in three modes
  at 53 bits and to nearest at 200 bits, against an independent 100-digit evaluation.
* Arguments next to the zeros (`1 ± 2^(−k)`, `2 ± 2^(−k)`), tiny and huge arguments, and the
  consistency of the directed modes at several precisions.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def G (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := lnGammaPrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard G nan 53 == (nan, .eq)
#guard G pinf 53 == (pinf, .eq)
#guard G ninf 53 == (nan, .eq)
#guard G zero 53 == (pinf, .eq)
#guard G zero 0 == (pinf, .eq)
#guard G (F "-1/2" 53) 53 == (nan, .eq)
#guard G (F "-3" 53) 53 == (nan, .eq)
#guard G (F "3" 53) 0 == (nan, .eq)
#guard G (F "1" 53) 53 == (zero, .eq)
#guard G (F "2" 53) 53 == (zero, .eq)
#guard G (F "1" 53) 0 == (zero, .eq)
#guard G (F "2" 7) 200 .Ceiling == (zero, .eq)

-- integers: `ln Γ(n) = ln (n − 1)!`
private def fact (n : Nat) : Nat := (List.range n).foldl (fun a i => a * (i + 1)) 1
private def intOk (n p : Nat) (m : RoundingMode) : Bool :=
  G (F (toString n) 64) p m == lnPrecRound (ofAzNat (AzNat.ofNat (fact (n - 1)))) p m
#guard [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m =>
  [3, 4, 5, 10, 20, 50, 171].all fun n => intOk n 53 m
#guard [3, 7, 30, 100, 300].all fun n => intOk n 24 .Nearest && intOk n 113 .Nearest
#guard [3, 12, 100].all fun n => intOk n 300 .Floor && intOk n 300 .Ceiling
#guard intOk 5 1 .Nearest && intOk 5 2 .Floor && intOk 1000 53 .Nearest
#guard intOk 40 700 .Nearest

-- dyadic non-integers, 53 bits
#guard G (F "1/2" 53) 53 == (F "5155405087351229/9007199254740992" 53, .lt)
#guard G (F "1/2" 53) 53 .Floor == (F "5155405087351229/9007199254740992" 53, .lt)
#guard G (F "1/2" 53) 53 .Ceiling == (F "2577702543675615/4503599627370496" 53, .gt)
#guard G (F "3/2" 53) 53 == (F "-8703277446513041/72057594037927936" 53, .gt)
#guard G (F "3/2" 53) 53 .Floor == (F "-4351638723256521/36028797018963968" 53, .lt)
#guard G (F "3/2" 53) 53 .Ceiling == (F "-8703277446513041/72057594037927936" 53, .gt)
#guard G (F "5/4" 53) 53 == (F "-7081232094244673/72057594037927936" 53, .gt)
#guard G (F "5/4" 53) 53 .Floor == (F "-3540616047122337/36028797018963968" 53, .lt)
#guard G (F "7/2" 53) 53 == (F "2704352134006043/2251799813685248" 53, .gt)
#guard G (F "7/2" 53) 53 .Floor == (F "5408704268012085/4503599627370496" 53, .lt)
#guard G (F "17/8" 53) 53 == (F "8324071866529019/144115188075855872" 53, .gt)
#guard G (F "17/8" 53) 53 .Floor == (F "4162035933264509/72057594037927936" 53, .lt)
#guard G (F "33/32" 53) 53 == (F "-4971044446163549/288230376151711744" 53, .gt)
#guard G (F "33/32" 53) 53 .Floor == (F "-2485522223081775/144115188075855872" 53, .lt)
#guard G (F "1/1024" 53) 53 == (F "7803509687568785/1125899906842624" 53, .lt)
#guard G (F "1/1024" 53) 53 .Ceiling == (F "3901754843784393/562949953421312" 53, .gt)

-- 200 bits
#guard (G (F "1/2" 53) 200).1 == F ("459877500992913075742138371806560050261594038695173574630285"
  ++ "/803469022129495137770981046170581301261101496891396417650688") 200
#guard (G (F "3/2" 53) 200).1
  == F ("-776358290907222272247917629937708823240336864634974405908929"
    ++ "/6427752177035961102167848369364650410088811975131171341205504") 200
#guard (G (F "7/2" 53) 200).1 == F ("964945085881140874069583013672322846004554124084804403385759"
  ++ "/803469022129495137770981046170581301261101496891396417650688") 200
#guard (G (F "33/32" 53) 200).1
  == F ("-886863964515712697087372162166677379528168666171518847895483"
    ++ "/51422017416287688817342786954917203280710495801049370729644032") 200
#guard (G (F "1/1024" 53) 200).1
  == F ("696096324786947185169050059313710390147128026557771689489583"
    ++ "/100433627766186892221372630771322662657637687111424552206336") 200

-- directed modes bracket the nearest value and are one ulp apart
private def consistent (x : AzFloat) (p : Nat) : Bool :=
  let f := G x p .Floor
  let c := G x p .Ceiling
  let n := G x p
  f.2 == .lt && c.2 == .gt && le f.1 n.1 && le n.1 c.1 && lt f.1 c.1
#guard [24, 53, 64, 100, 113, 200, 400].all fun p =>
  consistent (F "1/3" 53) p && consistent (F "7/5" 53) p && consistent (F "123456/7" 53) p

-- next to the zeros: `ln Γ(1 + ε) ≈ −γ ε`, `ln Γ(2 + ε) ≈ (1 − γ) ε`; the signs, and the size
private def near (s : String) : AzFloat := F s 200
#guard (G (near "1267650600228229401496703205377/1267650600228229401496703205376") 53).1.isNegative
#guard !(G (near "1267650600228229401496703205375/1267650600228229401496703205376") 53).1.isNegative
#guard !(G (near "2535301200456458802993406410753/1267650600228229401496703205376") 53).1.isNegative
#guard (G (near "2535301200456458802993406410751/1267650600228229401496703205376") 53).1.isNegative
#guard consistent (near "1267650600228229401496703205377/1267650600228229401496703205376") 53
#guard consistent (near "2535301200456458802993406410751/1267650600228229401496703205376") 53
#guard lnGammaCancelBits (near "1267650600228229401496703205377/1267650600228229401496703205376")
  200 == 99
#guard lnGammaCancelBits (F "3/2" 53) 53 == 0
#guard lnGammaCancelBits (F "1000" 53) 53 == 0

-- tiny and huge arguments: `ln Γ(x) ≈ −ln x` near `0`, `≈ x (ln x − 1)` far out
#guard consistent ((F "1" 53) <<< AzInt.ofInt (-200)) 53
#guard lt (F "138" 53) (G ((F "1" 53) <<< AzInt.ofInt (-200)) 53).1
#guard lt (G ((F "1" 53) <<< AzInt.ofInt (-200)) 53).1 (F "139" 53)
#guard consistent ((F "1" 53) <<< AzInt.ofInt (-100000)) 53
#guard consistent ((F "3" 53) <<< AzInt.ofInt 200) 53
#guard consistent ((F "3" 53) <<< AzInt.ofInt 100000) 53
#guard lnGamma (F "7/2" 53) == (G (F "7/2" 53) 53).1
#guard lnGamma nan == nan

-- the pieces
#guard lnGammaShiftExp 85 == 5
#guard lnGammaShift (F "3" 53) (AzInt.ofInt 2) 5 == 30
#guard lnGammaShift (F "1/3" 53) (AzInt.ofInt (-1)) 5 == 32
#guard lnGammaShift (F "1000" 53) (AzInt.ofInt 10) 5 == 0
#guard lnGammaShift (F "1/2" 53) (AzInt.ofInt 100) 5 == 1
#guard lnGammaTerms 85 6 == 16
#guard lnGammaTerms 2032 10 == 278
#guard lnGammaTerms 85 200 == 4
