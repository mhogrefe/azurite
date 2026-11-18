/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGammaRat
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.Ln
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString
import Azurite.AzFloat.GammaRat
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString

/-!
# Tests for `ln Γ` of a rational

* Special values: `0`, negative arguments, `p = 0`, and the exact zeros `q = 1`, `q = 2`.
* Dyadic arguments: the result must be that of the float function at the same argument, in
  every mode.
* Non-dyadic arguments: `ln Γ(1/3)`, `ln Γ(1/4)`, `ln Γ(2/3)` against decimal brackets; the
  recurrence `ln Γ(q + 1) − ln Γ(q) = ln q` at 200 bits, with `ln q` from `lnRat`; integers
  against the logarithm of the exact factorial.
* Arguments next to the zeros, tiny and huge arguments, and the consistency of the directed
  modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def G (s : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnGammaRatPrecRound (Q s) p m
private def pinf : AzFloat := infinity true
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (G "0" 53) == ("Infinity", .eq)
#guard D (G "0" 0) == ("Infinity", .eq)
#guard D (G "-1/2" 53) == ("NaN", .eq)
#guard D (G "-3" 53) == ("NaN", .eq)
#guard D (G "3" 0) == ("NaN", .eq)
#guard D (G "1/3" 0) == ("NaN", .eq)
#guard D (G "1" 53) == ("0.0", .eq)
#guard D (G "2" 53) == ("0.0", .eq)
#guard D (G "1" 0) == ("0.0", .eq)
#guard D (G "2" 200 .Ceiling) == ("0.0", .eq)

-- dyadic arguments: the float function
private def dyadicOk (s : String) (p : Nat) (m : RoundingMode) : Bool :=
  G s p m == lnGammaPrecRound (F s 64) p m
#guard [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m =>
  ["1/2", "3/2", "5/4", "7/2", "17/8", "33/32", "1/1024", "3", "10", "171", "1000"].all
    fun s => dyadicOk s 53 m
#guard ["1/2", "3/2", "7/2", "33/32", "5", "100"].all fun s =>
  dyadicOk s 24 .Nearest && dyadicOk s 200 .Nearest && dyadicOk s 200 .Floor

-- non-dyadic arguments against decimal brackets
private def between (s lo hi : String) (p : Nat) : Bool :=
  [RoundingMode.Nearest, .Floor, .Ceiling].all fun m =>
    lt (F lo 200) (G s p m).1 && lt (G s p m).1 (F hi 200)
#guard between "1/3" "985420646927766/1000000000000000" "985420646927768/1000000000000000" 53
#guard between "1/4" "1288022524698077/1000000000000000" "1288022524698078/1000000000000000" 53
#guard between "2/3" "303150275147523/1000000000000000" "303150275147524/1000000000000000" 53
#guard between "1/3" "985420646927767/1000000000000000" "985420646927768/1000000000000000" 300

-- the recurrence `ln Γ(q + 1) − ln Γ(q) = ln q` at 200 bits (within `2^(−180)`)
private def recOk (s s1 : String) : Bool :=
  let d := (subPrecRound (G s1 200).1 (G s 200).1 200 .Nearest).1
  let e := (subPrecRound d (lnRat (Q s) 200) 200 .Nearest).1
  lt e.abs (powerOf2 (AzInt.ofInt (-180)))
#guard recOk "1/3" "4/3"
#guard recOk "4/3" "7/3"
#guard recOk "22/7" "29/7"
#guard recOk "1/1000" "1001/1000"
#guard recOk "100/3" "103/3"
#guard recOk "1000/7" "1007/7"

-- integers: `ln Γ(n) = ln (n − 1)!`
private def fact (n : Nat) : Nat := (List.range n).foldl (fun a i => a * (i + 1)) 1
#guard [RoundingMode.Nearest, .Floor, .Ceiling].all fun m => [3, 4, 7, 20, 50].all fun n =>
  G (toString n) 53 m == lnPrecRound (ofAzNat (AzNat.ofNat (fact (n - 1)))) 53 m

-- directed modes bracket the nearest value and are one ulp apart
private def consistent (s : String) (p : Nat) : Bool :=
  let f := G s p .Floor
  let c := G s p .Ceiling
  let n := G s p
  f.2 == .lt && c.2 == .gt && le f.1 n.1 && le n.1 c.1 && lt f.1 c.1
#guard [1, 2, 24, 53, 64, 100, 113, 200, 400].all fun p =>
  consistent "1/3" p && consistent "7/5" p && consistent "123456/7" p

-- next to the zeros: `ln Γ(1 + ε) ≈ −γ ε`, `ln Γ(2 + ε) ≈ (1 − γ) ε`
#guard (G "1000000000000000000000000000001/1000000000000000000000000000000" 53).1.isNegative
#guard !(G "999999999999999999999999999999/1000000000000000000000000000000" 53).1.isNegative
#guard !(G "2000000000000000000000000000001/1000000000000000000000000000000" 53).1.isNegative
#guard (G "1999999999999999999999999999999/1000000000000000000000000000000" 53).1.isNegative
#guard consistent "1000000000000000000000000000001/1000000000000000000000000000000" 53
#guard consistent "1999999999999999999999999999999/1000000000000000000000000000000" 53
#guard lnGammaRatCancelBits (Q "1000000000000000000000000000001/1000000000000000000000000000000")
  == 99
#guard lnGammaRatCancelBits (Q "3/2") == 0
#guard lnGammaRatCancelBits (Q "1000/3") == 0

-- tiny and huge arguments: `ln Γ(q) ≈ −ln q` near `0`, `≈ q (ln q − 1)` far out
#guard consistent "1/1000000000000000000000000000000000000000000000000000000000003" 53
#guard between "1/1000000000000000000000000000000000000000000000000000000000000" "138" "139" 53
#guard consistent "1000000000000000000000000000000000000000000000000000000000000/3" 53
#guard lnGammaRat (Q "7/3") 53 == (G "7/3" 53).1

/-!
# Tests for `ln |Γ(q)|` and the sign of `Γ(q)` at a rational

* Special values: `0`, the poles, `1`, `2`, `p = 0`.
* `q > 0`: the value of `lnGammaRatPrecRound`, sign `true`.
* Dyadic arguments: the results of the float function at the same argument, in every mode.
* Non-dyadic `q < 0`: the 53-bit result against the logarithm of the 200-bit `|Γ(q)|`, in
  every mode; the signs between the poles; arguments next to a pole and next to `0`.
-/

namespace LnAbsGammaRatTests

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def L (s : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnAbsGammaRatPrecRound (Q s) p m
private def pinf : AzFloat := infinity true
private def modes : List RoundingMode := [.Nearest, .Floor, .Ceiling, .Down, .Up]

-- special values
#guard L "0" 53 == ((pinf, .eq), true)
#guard L "0" 0 == ((pinf, .eq), true)
#guard L "-1" 53 == ((pinf, .eq), true)
#guard L "-7" 53 == ((pinf, .eq), true)
#guard L "-1267650600228229401496703205376" 0 == ((pinf, .eq), true)
#guard modes.all fun m => L "1" 53 m == ((zero, .eq), true)
#guard modes.all fun m => L "2" 53 m == ((zero, .eq), true)
#guard L "-1/3" 0 == ((nan, .eq), false)
#guard L "1/3" 0 == ((nan, .eq), true)

-- `q > 0`: `lnGammaRatPrecRound`
#guard ["1/3", "3/2", "7/3", "100", "1/1000000"].all fun s => modes.all fun m =>
  L s 53 m == (lnGammaRatPrecRound (Q s) 53 m, true)

-- dyadic arguments: the float function
#guard ["-1/2", "-3/2", "-5/2", "-7/4", "-201/2", "-1/1024", "-4097/4096"].all fun s =>
  modes.all fun m => L s 53 m == lnAbsGammaPrecRound (F s 64) 53 m
#guard L "-5/2" 200 == lnAbsGammaPrecRound (X "-2.5" 64) 200 .Nearest

/-- The 53-bit result is the rounding of `ln` of the 200-bit `|Γ(q)|`, with the sign of
`Γ(q)`. -/
private def viaGamma (s : String) (m : RoundingMode) : Bool :=
  let g := (gammaRatPrecRound (Q s) 200 .Nearest).1
  (L s 53 m).1.1 == (lnPrecRound g.abs 53 m).1 && (L s 53 m).2 == !g.isNegative
#guard ["-1/3", "-4/3", "-7/3", "-22/7", "-27/10", "-1000001/3", "-1/1000000007",
    "-10000001/10000000", "-9999999/10000000"].all fun s => modes.all fun m => viaGamma s m

-- signs between the poles
#guard (L "-1/3" 53).2 == false
#guard (L "-4/3" 53).2 == true
#guard (L "-7/3" 53).2 == false
#guard (L "-10/3" 53).2 == true
#guard (L "-3002/3" 53).2 == false
#guard (L "-3005/3" 53).2 == true
#guard gammaRatSign (Q "-4/3") && !gammaRatSign (Q "-1/3") && gammaRatSign (Q "-2")
  && gammaRatSign (Q "0") && gammaRatSign (Q "5/3")

-- the comparison tag agrees with the directed roundings
#guard (L "-1/3" 53 .Floor).1.2 == .lt && (L "-1/3" 53 .Ceiling).1.2 == .gt
  && lt (L "-1/3" 53 .Floor).1.1 (L "-1/3" 53 .Ceiling).1.1

-- nearest
#guard lnAbsGammaRat (Q "-1/3") 53 == ((L "-1/3" 53).1.1, false)

end LnAbsGammaRatTests
