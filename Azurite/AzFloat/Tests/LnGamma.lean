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
import Azurite.AzFloat.Gamma

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

/-!
# Tests for `ln |Γ(x)|` and the sign of `Γ(x)`

* Special values: `NaN`, `±∞`, `0`, the poles, `1`, `2`, `p = 0`.
* `x > 0`: the value of `lnGammaPrecRound`, sign `true`.
* `x < 0`: decimal brackets at `−1/2`, `−3/2`, `−5/2`; the 53-bit result against the logarithm
  of the 200-bit `|Γ(x)|`, in every mode; the signs between the poles; arguments next to a
  pole, tiny and large arguments, and an argument next to a zero of `ln |Γ|`.
-/

namespace LnAbsGammaTests

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def L (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnAbsGammaPrecRound x p m
private def pinf : AzFloat := infinity true
private def modes : List RoundingMode := [.Nearest, .Floor, .Ceiling, .Down, .Up]
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A result with a flag, as decimal output. -/
private def Db (r : (AzFloat × Ordering) × Bool) : (String × Ordering) × Bool :=
  ((toString r.1.1, r.1.2), r.2)

-- special values
#guard Db (L nan 53) == (("NaN", .eq), true)
#guard Db (L pinf 53) == (("Infinity", .eq), true)
#guard Db (L (infinity false) 53) == (("Infinity", .eq), true)
#guard Db (L zero 53) == (("Infinity", .eq), true)
#guard Db (L zero 0) == (("Infinity", .eq), true)
#guard Db (L (X "-1" 53) 53) == (("Infinity", .eq), true)
#guard Db (L (X "-7" 53) 53) == (("Infinity", .eq), true)
#guard Db (L (X "-1267650600228229401496703205376" 53) 53) == (("Infinity", .eq), true)
#guard modes.all fun m => L (X "1" 53) 53 m == ((zero, .eq), true)
#guard modes.all fun m => L (X "2" 53) 53 m == ((zero, .eq), true)
#guard Db (L (X "1" 53) 0) == (("0.0", .eq), true)
#guard Db (L (X "-0.5" 53) 0) == (("NaN", .eq), false)
#guard Db (L (X "3" 53) 0) == (("NaN", .eq), true)

-- `x > 0`: `lnGammaPrecRound`
#guard ["1/3", "3/2", "5/2", "100", "1/1000000"].all fun s => modes.all fun m =>
  L (F s 53) 53 m == (lnGammaPrecRound (F s 53) 53 m, true)

-- decimal brackets: `ln (2√π)`, `ln (4√π/3)`, `ln (8√π/15)`
private def between (r : AzFloat × Ordering) (lo hi : String) : Bool :=
  lt (F lo 80) r.1 && lt r.1 (F hi 80)
#guard modes.all fun m =>
  between (L (X "-0.5" 53) 53 m).1 "1265512123484644/1000000000000000"
    "1265512123484647/1000000000000000"
#guard toString (L (X "-0.5" 53) 53).1.1 == "1.2655121234846454"
#guard modes.all fun m =>
  between (L (X "-1.5" 53) 53 m).1 "860047015376480/1000000000000000"
    "860047015376482/1000000000000000"
#guard toString (L (X "-1.5" 53) 53).1.1 == "0.860047015376481"
#guard modes.all fun m =>
  between (L (X "-2.5" 53) 53 m).1 "-56243716497675/1000000000000000"
    "-56243716497673/1000000000000000"
#guard toString (L (X "-2.5" 53) 53).1.1 == "-0.056243716497674054"

-- signs between the poles: `Γ < 0` on `(−1, 0)`, `> 0` on `(−2, −1)`, …
#guard (L (X "-0.5" 53) 53).2 == false
#guard (L (X "-1.5" 53) 53).2 == true
#guard (L (X "-2.5" 53) 53).2 == false
#guard (L (X "-3.5" 53) 53).2 == true
#guard (L (X "-0.000001" 53) 53).2 == false
#guard (L (X "-0.999999" 53) 53).2 == false
#guard (L (X "-1.000001" 53) 53).2 == true
#guard (L (X "-1000.5" 53) 53).2 == false
#guard (L (X "-1001.5" 53) 53).2 == true

/-- The 53-bit result is the rounding of `ln` of the 200-bit `|Γ(x)|` (the 200-bit value is
far from the 53-bit rounding boundaries in these cases), with the sign of `Γ(x)`. -/
private def viaGamma (x : AzFloat) (m : RoundingMode) : Bool :=
  let g := (gammaPrecRound x 200 .Nearest).1
  (L x 53 m).1.1 == (lnPrecRound g.abs 53 m).1 && (L x 53 m).2 == !g.isNegative
#guard ["-1/3", "-4/3", "-7/2", "-21/2", "-201/2", "-1/1024", "-10000001/10000000",
    "-27/10", "-1000001/3"].all fun s => modes.all fun m => viaGamma (F s 53) m

-- the comparison tag agrees with the directed roundings
#guard ["-1/3", "-27/10"].all fun s =>
  (L (F s 53) 53 .Floor).1.2 == .lt && (L (F s 53) 53 .Ceiling).1.2 == .gt
    && lt (L (F s 53) 53 .Floor).1.1 (L (F s 53) 53 .Ceiling).1.1

-- tiny arguments: `ln |Γ(x)| ≈ −ln |x|`
#guard toString (L (-(one <<< AzInt.ofInt (-200))) 53).1.1 == "138.62943611198907"
#guard (L (-(one <<< AzInt.ofInt (-200))) 53).2 == false

-- next to a zero of `ln |Γ|` (`|Γ(x)| = 1` at `x ≈ −2.457024738…`): a small value, both signs
#guard lt zero (L (X "-2.457" 53) 53).1.1
#guard lt (L (X "-2.458" 53) 53).1.1 zero
#guard lt (L (X "-2.457" 53) 53).1.1 (X "0.001" 53)

-- nearest at the precision of the argument
#guard lnAbsGamma (X "-0.5" 53) == ((L (X "-0.5" 53) 53).1.1, false)

end LnAbsGammaTests
