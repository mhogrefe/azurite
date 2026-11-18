/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def G (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := lnGammaPrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard D (G nan 53) == ("NaN", .eq)
#guard D (G pinf 53) == ("Infinity", .eq)
#guard D (G ninf 53) == ("NaN", .eq)
#guard D (G zero 53) == ("Infinity", .eq)
#guard D (G zero 0) == ("Infinity", .eq)
#guard D (G (X "-0.5" 53) 53) == ("NaN", .eq)
#guard D (G (X "-3" 53) 53) == ("NaN", .eq)
#guard D (G (X "3" 53) 0) == ("NaN", .eq)
#guard D (G (X "1" 53) 53) == ("0.0", .eq)
#guard D (G (X "2" 53) 53) == ("0.0", .eq)
#guard D (G (X "1" 53) 0) == ("0.0", .eq)
#guard D (G (X "2" 7) 200 .Ceiling) == ("0.0", .eq)

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
#guard D (G (X "0.5" 53) 53) == ("0.5723649429247001", .lt)
#guard D (G (X "0.5" 53) 53 .Floor) == ("0.5723649429247001", .lt)
#guard D (G (X "0.5" 53) 53 .Ceiling) == ("0.5723649429247002", .gt)
#guard D (G (X "1.5" 53) 53) == ("-0.12078223763524522", .gt)
#guard D (G (X "1.5" 53) 53 .Floor) == ("-0.12078223763524523", .lt)
#guard D (G (X "1.5" 53) 53 .Ceiling) == ("-0.12078223763524522", .gt)
#guard D (G (X "1.25" 53) 53) == ("-0.09827183642181316", .gt)
#guard D (G (X "1.25" 53) 53 .Floor) == ("-0.09827183642181317", .lt)
#guard D (G (X "3.5" 53) 53) == ("1.2009736023470743", .gt)
#guard D (G (X "3.5" 53) 53 .Floor) == ("1.200973602347074", .lt)
#guard D (G (X "2.125" 53) 53) == ("0.057759851530343874", .gt)
#guard D (G (X "2.125" 53) 53 .Floor) == ("0.05775985153034387", .lt)
#guard D (G (X "1.03125" 53) 53) == ("-0.017246775001768067", .gt)
#guard D (G (X "1.03125" 53) 53 .Floor) == ("-0.01724677500176807", .lt)
#guard D (G (X "0.0009765625" 53) 53) == ("6.9309089024194614", .lt)
#guard D (G (X "0.0009765625" 53) 53 .Ceiling) == ("6.930908902419462", .gt)

-- 200 bits
#guard toString ((G (X "0.5" 53) 200).1)
  == "0.572364942924700087071713675676529355823647406457655785756812"
#guard toString ((G (X "1.5" 53) 200).1)
  == "-0.12078223763524522234551844578164721225185272790259946836386844"
#guard toString ((G (X "3.5" 53) 200).1)
  == "1.200973602347074224816021881450712995770238915468157197042114"
#guard toString ((G (X "1.03125" 53) 200).1)
  == "-0.01724677500176806740289126202224623179736644650510638053507814"
#guard toString ((G (X "0.0009765625" 53) 200).1)
  == "6.930908902419461889540619064660080535727272548188649964932003"

-- directed modes bracket the nearest value and are one ulp apart
private def consistent (x : AzFloat) (p : Nat) : Bool :=
  let f := G x p .Floor
  let c := G x p .Ceiling
  let n := G x p
  f.2 == .lt && c.2 == .gt && le f.1 n.1 && le n.1 c.1 && lt f.1 c.1
#guard [24, 53, 64, 100, 113, 200, 400].all fun p =>
  consistent (X "0.3333333333333333" 53) p && consistent (X "1.4" 53) p && consistent (X "17636.571\
    428571428" 53) p

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
#guard lnGammaCancelBits (X "1.5" 53) 53 == 0
#guard lnGammaCancelBits (X "1000" 53) 53 == 0

-- tiny and huge arguments: `ln Γ(x) ≈ −ln x` near `0`, `≈ x (ln x − 1)` far out
#guard consistent ((X "1" 53) <<< AzInt.ofInt (-200)) 53
#guard toString (G ((X "1" 53) <<< AzInt.ofInt (-200)) 53).1 == "138.62943611198907"
#guard lt (G ((X "1" 53) <<< AzInt.ofInt (-200)) 53).1 (X "139" 53)
#guard consistent ((X "1" 53) <<< AzInt.ofInt (-100000)) 53
#guard consistent ((X "3" 53) <<< AzInt.ofInt 200) 53
#guard consistent ((X "3" 53) <<< AzInt.ofInt 100000) 53
#guard lnGamma (X "3.5" 53) == (G (X "3.5" 53) 53).1
#guard toString (lnGamma nan) == "NaN"

-- the pieces
#guard lnGammaShiftExp 85 == 5
#guard lnGammaShift (X "3" 53) (AzInt.ofInt 2) 5 == 30
#guard lnGammaShift (X "0.3333333333333333" 53) (AzInt.ofInt (-1)) 5 == 32
#guard lnGammaShift (X "1000" 53) (AzInt.ofInt 10) 5 == 0
#guard lnGammaShift (X "0.5" 53) (AzInt.ofInt 100) 5 == 1
#guard lnGammaTerms 85 6 == 16
#guard lnGammaTerms 2032 10 == 278
#guard lnGammaTerms 85 200 == 4
