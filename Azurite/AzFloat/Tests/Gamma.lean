/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gamma
import Azurite.AzFloat.Pi
import Azurite.AzFloat.Ln
import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Mul
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

/-!
# Tests for `Γ` and `1/Γ`

* Special values: `NaN`, `±∞`, `0`, the poles, `p = 0`.
* Positive integers: `Γ(n) = (n − 1)!` — exact with `.eq` when the factorial fits, the rounded
  factorial otherwise, both on the exact path (`n ≤ p + 65`) and on the general path beyond it,
  where the exact factorial is an oracle that shares nothing with Stirling's series.  The same
  for `1/Γ(n)` against one correctly rounded division.
* Half-integers and other arguments against decimal brackets; `Γ(1/2)² = π`; the recurrence
  `Γ(x + 1) = x Γ(x)` across `0` and the negative axis at 200 bits; `Γ(x) · (1/Γ(x)) = 1`.
* Signs between the poles, arguments next to the poles, tiny and huge arguments, and the
  consistency of the directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def G (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := gammaPrecRound x p m
private def R (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  reciprocalGammaPrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
private def modes : List RoundingMode := [.Nearest, .Floor, .Ceiling, .Down, .Up]

-- special values of `Γ`
#guard D (G nan 53) == ("NaN", .eq)
#guard D (G pinf 53) == ("Infinity", .eq)
#guard D (G ninf 53) == ("NaN", .eq)
#guard D (G zero 53) == ("Infinity", .eq)
#guard D (G zero 0) == ("Infinity", .eq)
#guard D (G (X "-1" 53) 53) == ("NaN", .eq)
#guard D (G (X "-2" 53) 53) == ("NaN", .eq)
#guard D (G (X "-1000000" 53) 53) == ("NaN", .eq)
#guard D (G ((X "-3" 53) <<< AzInt.ofInt 1000) 53) == ("NaN", .eq)
#guard D (G (X "3" 53) 0) == ("NaN", .eq)
#guard D (G (X "0.5" 53) 0) == ("NaN", .eq)

-- special values of `1/Γ`
#guard D (R nan 53) == ("NaN", .eq)
#guard D (R pinf 53) == ("0.0", .eq)
#guard D (R ninf 53) == ("NaN", .eq)
#guard D (R zero 53) == ("0.0", .eq)
#guard D (R zero 0) == ("0.0", .eq)
#guard D (R (X "-1" 53) 53) == ("0.0", .eq)
#guard D (R (X "-7" 53) 0) == ("0.0", .eq)
#guard D (R ((X "-3" 53) <<< AzInt.ofInt 1000) 53) == ("0.0", .eq)
#guard D (R (X "3" 53) 0) == ("NaN", .eq)

-- positive integers
private def fact (n : Nat) : AzFloat :=
  ofAzNat (AzNat.ofNat ((List.range n).foldl (fun a i => a * (i + 1)) 1))
private def intOk (n p : Nat) (m : RoundingMode) : Bool :=
  G (F (toString n) 64) p m == setPrecRound (fact (n - 1)) p m
    && R (F (toString n) 64) p m == divPrecRound one (fact (n - 1)) p m
#guard D (G (X "1" 53) 53) == ("1.0", .eq)
#guard D (G (X "2" 53) 1) == ("1.0", .eq)
#guard D (G (X "5" 53) 53) == ("24.0", .eq)
#guard (G (X "23" 53) 53).2 == .eq
#guard (G (X "24" 53) 53).2 != .eq
#guard (G (X "30" 53) 200).2 == .eq
#guard D (R (X "1" 53) 53) == ("1.0", .eq)
#guard D (R (X "3" 53) 53) == ("0.5", .eq)
#guard (R (X "4" 53) 53).2 != .eq
#guard modes.all fun m => [1, 2, 3, 4, 5, 10, 19, 23, 24, 30, 60, 118].all fun n => intOk n 53 m
-- beyond `p + 65` the general path must agree with the exact factorial
#guard modes.all fun m => [119, 120, 171, 300].all fun n => intOk n 53 m
#guard [70, 100, 250].all fun n => intOk n 1 .Nearest && intOk n 2 .Floor && intOk n 24 .Up
#guard intOk 400 113 .Nearest && intOk 1000 53 .Nearest

-- decimal brackets
private def between (r : AzFloat × Ordering) (lo hi : String) : Bool :=
  lt (F lo 200) r.1 && lt r.1 (F hi 200)
#guard modes.all fun m =>
  between (G (X "0.5" 53) 53 m) "1772453850905515/1000000000000000"
    "1772453850905517/1000000000000000"
#guard modes.all fun m =>
  between (G (X "-0.5" 53) 53 m) "-3544907701811033/1000000000000000"
    "-3544907701811031/1000000000000000"
#guard modes.all fun m =>
  between (G (X "-1.5" 53) 53 m) "2363271801207354/1000000000000000"
    "2363271801207356/1000000000000000"
#guard modes.all fun m =>
  between (G (X "-2.5" 53) 53 m) "-945308720482943/1000000000000000"
    "-945308720482941/1000000000000000"
#guard modes.all fun m =>
  between (R (X "0.5" 53) 53 m) "564189583547755/1000000000000000"
    "564189583547757/1000000000000000"
#guard modes.all fun m =>
  between (R (X "-0.5" 53) 53 m) "-282094791773879/1000000000000000"
    "-282094791773877/1000000000000000"
#guard toString (G (X "1.5" 53) 53).1 == "0.886226925452758"
#guard toString (G (X "0.25" 53) 53).1 == "3.625609908221908"

-- `a ≈ b` to `k` bits (relative)
private def close (a b : AzFloat) (k : Int) : Bool :=
  le (subPrecRound a b 64 .Nearest).1.abs (b.abs <<< AzInt.ofInt (-k))

-- `Γ(1/2)² = π`
#guard close (mulPrecRound (G (X "0.5" 53) 200).1 (G (X "0.5" 53) 200).1 200 .Nearest).1
  (piPrecRound 200 .Nearest).1 196

-- the recurrence `Γ(x + 1) = x Γ(x)` at 200 bits
private def recOk (s s1 : String) : Bool :=
  close (mulPrecRound (F s 64) (G (F s 64) 200).1 200 .Nearest).1 (G (F s1 64) 200).1 196
#guard recOk "1/2" "3/2"
#guard recOk "-1/2" "1/2"
#guard recOk "-3/2" "-1/2"
#guard recOk "-7/4" "-3/4"
#guard recOk "-1001/8" "-993/8"
#guard recOk "1001/8" "1009/8"
#guard recOk "-65537/65536" "-1/65536"
#guard recOk "-200001/2" "-199999/2"

-- `Γ(x) · (1/Γ(x)) = 1`
private def prodOk (x : AzFloat) (p : Nat) : Bool :=
  close (mulPrecRound (G x (p + 8)).1 (R x (p + 8)).1 (p + 8) .Nearest).1 one p
#guard ["1/2", "-1/2", "7/3", "-7/3", "1000/3", "-1000/3", "1/1000", "-1/1000", "-2001/1000"].all
  fun s => prodOk (F s 53) 53 && prodOk (F s 53) 150

-- signs between the poles: `Γ < 0` on `(−1, 0)`, `> 0` on `(−2, −1)`, …
#guard (G (X "-0.3333333333333333" 53) 53).1.isNegative && (R (X "-0.333333333333333\
  3" 53) 53).1.isNegative
#guard !(G (X "-1.3333333333333333" 53) 53).1.isNegative && !(R (X "-1.333333333333333\
  3" 53) 53).1.isNegative
#guard (G (X "-2.3333333333333335" 53) 53).1.isNegative && (R (X "-2.333333333333333\
  5" 53) 53).1.isNegative
#guard !(G (X "-3.3333333333333335" 53) 53).1.isNegative
#guard (G (X "-333333.6666666667" 53) 53).1.isNegative == false
#guard (G (X "-333334.6666666667" 53) 53).1.isNegative == true

-- directed modes bracket the nearest value and are one ulp apart
private def consistentOf (f : RoundingMode → AzFloat × Ordering) : Bool :=
  let a := f .Floor
  let c := f .Ceiling
  let n := f .Nearest
  a.2 == .lt && c.2 == .gt && le a.1 n.1 && le n.1 c.1 && lt a.1 c.1
private def consistent (x : AzFloat) (p : Nat) : Bool :=
  consistentOf (fun m => G x p m) && consistentOf (fun m => R x p m)
#guard [1, 2, 24, 53, 64, 113, 200].all fun p =>
  consistent (X "0.3333333333333333" 53) p && consistent (X "-1.4" 53) p && consistent (X "17636.57\
    1428571428" 53) p
    && consistent (X "-17636.571428571428" 53) p

-- next to the poles and next to `1`, `2`
#guard consistent (X "-1.000000000000000000000000000000789" 110) 53
#guard consistent (X "-1.999999999999999999999999999999211" 110) 53
#guard consistent (X "1.000000000000000000000000000000789" 110) 53
#guard consistent (X "1.999999999999999999999999999999211" 110) 53
#guard toString (G (X "-1.000000000000000888" 60) 53).1 ==
  "1125899906842623.6"

-- tiny arguments: `Γ(x) ≈ 1/x − γ`, `1/Γ(x) ≈ x + γ x²`
private def tiny (s : String) (k : Int) : AzFloat := (F s 53) <<< AzInt.ofInt (-k)
#guard G (tiny "1" 100000) 53 == (tiny "1" (-100000), .gt)
#guard G (tiny "-1" 100000) 53 == (tiny "-1" (-100000), .gt)
#guard (G (tiny "1" 100000) 53 .Floor).2 == .lt && lt (G (tiny "1" 100000) 53 .Floor).1
  (tiny "1" (-100000))
#guard R (tiny "1" 100000) 53 == (tiny "1" 100000, .lt)
#guard R (tiny "-3" 100000) 53 == (tiny "-3" 100000, .lt)
#guard (R (tiny "1" 100000) 53 .Ceiling).2 == .gt
#guard consistent (tiny "3" 100000) 53 && consistent (tiny "-3" 100000) 53
#guard consistent (tiny "1" 100) 53 && consistent (tiny "-1" 100) 53
#guard consistent (tiny "5" 60) 53 && consistent (tiny "-5" 130) 53
#guard prodOk (tiny "3" 500) 53 && prodOk (tiny "-3" 500) 53

-- large arguments: no overflow; `ln (Γ(x)) = ln Γ(x)` and `ln (1/Γ(x)) = −ln Γ(x)`
private def lnOk (s : String) : Bool :=
  let x := F s 64
  let L := (lnGammaPrecRound x 64 .Nearest).1
  close (lnPrecRound (G x 64).1 64 .Nearest).1 L 50
    && close (lnPrecRound (R x 64).1 64 .Nearest).1 (-L) 50
#guard ["7/3", "1000/3", "2000001/2", "123456789012/7", "1/1000000"].all lnOk
#guard consistent (X "1000000.5" 53) 53 && consistent (X "-1000000.5" 53) 53

-- the wrappers and the pieces
#guard gamma (X "3.5" 53) == (G (X "3.5" 53) 53).1
#guard reciprocalGamma (X "3.5" 53) == (R (X "3.5" 53) 53).1
#guard toString (gamma nan) == "NaN"
#guard gammaSmallInt (X "5" 53) 10 && !gammaSmallInt (X "11" 53) 10
#guard !gammaSmallInt (X "-5" 53) 10 && !gammaSmallInt (X "2.5" 53) 10
#guard (gammaNearInt (X "-2.5" 53)).toInt == -2 && (gammaNearInt (X "-2.75" 53)).toInt == -3
#guard (gammaSinEncl (X "-0.5" 53) 96 80).map (·.1) == some true
#guard (gammaSinEncl (X "-1.5" 53) 96 80).map (·.1) == some false
#guard (gammaSinEncl (X "-2" 53) 96 80).isNone

-- quarter-integers: the certified loops (no fuel; `Γ(n/4)` is irrational)
#guard [X "0.5" 53, X "-0.5" 53, X "0.75" 53, X "2.5" 53, X "-7.25" 53, X "0.25" 53].all
  gammaSpecial
#guard [X "3" 53, X "0.125" 53, X "1e30" 100, X "-2" 53].all fun x => !gammaSpecial x
#guard D (G (X "0.5" 53) 53) == ("1.772453850905516", .gt)
#guard D (G (X "0.5" 53) 1) == ("2.0", .gt)
#guard D (G (X "-0.5" 53) 53) == ("-3.544907701811032", .lt)
#guard D (G (X "0.75" 53) 53 .Floor) == ("1.2254167024651776", .lt)
#guard D (G (X "0.25" 53) 53) == ("3.625609908221908", .lt)
#guard D (G (X "2.5" 53) 64 .Ceiling) == ("1.3293403881791370205", .gt)
#guard D (G (X "-7.25" 53) 53) == ("0.0005303977063521478", .lt)
#guard D (R (X "0.5" 53) 53) == ("0.5641895835477563", .lt)
#guard D (R (X "-2.75" 53) 53 .Up) == ("-0.9955221580277868", .lt)
#guard D (G (X "-150.75" 53) 53) == ("-1.8063763409201774e-264", .lt)

-- positive integers beyond the factorial bound: a certified loop, whatever the fuel
#guard D (gammaPrecRoundFuel 0 (X "3000" 53) 53 .Nearest) == ("1.383119867812618e9127", .lt)
#guard D (reciprocalGammaPrecRoundFuel 0 (X "3000" 53) 53 .Nearest)
  == ("7.230031346317684e-9128", .lt)
#guard G (X "0.3" 53) 53 == gammaPrecRoundFuel (gammaFuel 53) (X "0.3" 53) 53 .Nearest
#guard gammaFuel 53 == 11 && lnGammaFuel 53 == 11 && agmFuel 53 == 11
