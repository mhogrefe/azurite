/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Product
import Azurite.AzFloat.Mul
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Precision
import Azurite.AzRat.Parse

/-!
# Tests for the correctly rounded product

Expected values computed by hand (the exact product, then one rounding), and agreement with a
fold of exact two-operand multiplications followed by one rounding.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def Pr (xs : List AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  productPrecRound xs p m
/-- The exact product by two-operand multiplications at a precision that holds everything,
then one rounding. -/
private def naive (xs : List AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  setPrecRound (xs.foldl (fun acc x => (mulPrecRound acc x 4096 .Floor).1) one) p m

/-! ## Special values -/

#guard Pr [] 5 == (setPrec one 5, .eq)
#guard Pr [one] 3 == (setPrec one 3, .eq)
#guard Pr [nan, one] 10 == (nan, .eq)
#guard Pr [one, infinity true] 10 == (infinity true, .eq)
#guard Pr [infinity false, one] 10 == (infinity false, .eq)
#guard Pr [infinity false, negOne] 10 == (infinity true, .eq)
#guard Pr [infinity true, negOne, F "-2" 2, F "-3" 2] 10 == (infinity false, .eq)
#guard Pr [infinity true, infinity false] 10 == (infinity false, .eq)
#guard Pr [infinity false, infinity false] 10 == (infinity true, .eq)
#guard Pr [zero, one] 10 == (zero, .eq)
#guard Pr [negOne, zero, negOne] 10 == (zero, .eq)
#guard Pr [zero, infinity true] 10 == (nan, .eq)
#guard Pr [infinity false, one, zero] 10 == (nan, .eq)
#guard Pr [nan, zero, infinity true] 10 == (nan, .eq)
#guard Pr [one] 0 == (nan, .eq)

/-! ## Two factors agree with multiplication -/

#guard Pr [F "3" 2, F "3" 2] 4 == mulPrecRound (F "3" 2) (F "3" 2) 4 .Nearest
#guard Pr [F "3" 2, F "5" 3] 3 == mulPrecRound (F "3" 2) (F "5" 3) 3 .Nearest
#guard Pr [F "3" 2, F "5" 3] 3 .Floor == mulPrecRound (F "3" 2) (F "5" 3) 3 .Floor
#guard Pr [F "1/3" 53, F "3" 2] 53 == mulPrecRound (F "1/3" 53) (F "3" 2) 53 .Nearest
#guard Pr [F "1/3" 53, F "3" 2] 53 .Floor == mulPrecRound (F "1/3" 53) (F "3" 2) 53 .Floor
#guard Pr [negOne, F "3" 2] 2 == (F "-3" 2, .eq)

/-! ## Exact products and roundings -/

#guard Pr [negOne, negOne, negOne] 1 == (negOne, .eq)
#guard Pr [negOne, negOne, negOne, negOne] 1 == (one, .eq)
#guard Pr [F "3" 2, F "3" 2, F "3" 2] 5 == (F "27" 5, .eq)
#guard Pr [F "3" 2, F "3" 2, F "3" 2] 3 == (F "28" 3, .gt)                 -- 27 → 28
#guard Pr [F "3" 2, F "3" 2, F "3" 2] 3 .Floor == (F "24" 3, .lt)
#guard Pr [F "3" 2, F "5" 3, F "7" 3] 4 == (F "104" 4, .lt)                -- 105 → 104
#guard Pr [F "3" 2, F "5" 3, F "7" 3] 4 .Ceiling == (F "112" 4, .gt)
#guard Pr [F "3" 2, F "5" 3, F "7" 3] 2 == (F "96" 2, .lt)                 -- 105 → 96
#guard Pr [F "3" 2, F "5" 3, F "7" 3] 2 .Up == (F "128" 2, .gt)
#guard Pr [F "-3" 2, F "5" 3, F "-7" 3] 4 == (F "104" 4, .lt)
#guard Pr [F "-3" 2, F "-5" 3, F "-7" 3] 4 == (F "-104" 4, .gt)
#guard Pr [F "-3" 2, F "-5" 3, F "-7" 3] 4 .Floor == (F "-112" 4, .lt)
#guard Pr [F "1/2" 1, F "1/2" 1, F "1/2" 1, F "1/2" 1] 1 == (P (-4), .eq)
#guard Pr ((List.range 10).map fun i => P i) 1 == (P 45, .eq)
#guard Pr ((List.range 100).map fun i => P (-i)) 1 == (P (-4950), .eq)
#guard Pr [P 1000000000, P (-999999999)] 1 == (two, .eq)
#guard Pr [P 1000000000, F "3" 2, P (-1000000000)] 2 == (F "3" 2, .eq)
-- `(1 − 2^−54)² = 1 − 2^−53 + 2^−108`, just above the `53`-bit float `1 − 2^−53`
#guard Pr [F "1/3" 53, F "3" 2, F "1/3" 53, F "3" 2] 53
  == (F "9007199254740991/9007199254740992" 53, .lt)
#guard Pr [F "1/3" 53, F "3" 2, F "1/3" 53, F "3" 2] 53 .Ceiling
  == (F "18014398509481983/18014398509481984" 53, .gt)
-- `10!` from the factors `1, …, 10`
#guard Pr ((List.range 10).map fun i => F (toString (i + 1)) 4) 22 == (F "3628800" 22, .eq)
#guard Pr ((List.range 10).map fun i => F (toString (i + 1)) 4) 10 == (F "3629056" 10, .gt)

/-! ## Agreement with a fold of exact multiplications -/

private def samples : List (List AzFloat) :=
  [[F "1/3" 53, F "7/5" 10, F "-11/13" 20],
   [F "1/3" 7, F "1/3" 7, F "1/3" 7, F "1/3" 7, F "1/3" 7],
   [F "123456789/1000" 40, F "-1/1000" 30, F "98765" 17, F "2/7" 64],
   (List.range 20).map fun i => F (toString (2 * i + 3) ++ "/" ++ toString (i + 2)) (i + 1),
   [F "-3/2" 2, P 100, F "3/2" 2, P (-100), F "-5" 3]]

#guard samples.all fun xs =>
  [1, 2, 3, 7, 24, 53, 100].all fun p =>
    [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m =>
      Pr xs p m == naive xs p m

/-! ## `productFloat64` -/

private def inf : Float := 1.0 / 0.0
private def maxF : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF
private def minSub : Float := Float.ofBits 1

-- exact products
#guard productFloat64 [] == 1.0
#guard productFloat64 [2.0, 3.0, 4.0] == 24.0
#guard productFloat64 [0.5, -0.25] == -0.125
#guard productFloat64 [0.1, 0.2] == 0.1 * 0.2
#guard productFloat64 [3.0, 0.0] == 0.0
#guard (productFloat64 [-3.0, 0.0]).toBits == 0 -- exact zero is +0.0
-- one rounding of the exact product
#guard productFloat64 [1.0 + 2.0 ^ (-52.0), 1.0 + 2.0 ^ (-52.0)] == 1.0 + 2.0 ^ (-51.0)
-- `(1 + 2^-52)^3 = 1 + 3·2^-52 + 3·2^-104 + 2^-156` rounds to `1 + 3·2^-52`
#guard productFloat64 [1.0 + 2.0 ^ (-52.0), 1.0 + 2.0 ^ (-52.0), 1.0 + 2.0 ^ (-52.0)]
  == 1.0 + 3.0 * 2.0 ^ (-52.0)
-- intermediate overflow and underflow do not matter: only the exact product is rounded
#guard productFloat64 [1.0e200, 1.0e200, 1.0e-300] == 1.0e100
#guard productFloat64 [1.0e-200, 1.0e-200, 1.0e300] == 1.0e-100
#guard productFloat64 [2.0 ^ 1000.0, 2.0 ^ 1000.0, 2.0 ^ (-1000.0)] == 2.0 ^ 1000.0
-- overflow at the IEEE threshold: `2^1024` is `∞`, `maxF` stays
#guard productFloat64 [2.0 ^ 1023.0, 2.0] == inf
#guard productFloat64 [-(2.0 ^ 1023.0), 2.0] == -inf
#guard productFloat64 [maxF, 1.0] == maxF
-- `maxF · (1 + 2^-52) = maxF + (2^53 − 1)·2^919`, above the midpoint `maxF + 2^970`
#guard productFloat64 [maxF, 1.0 + 2.0 ^ (-52.0)] == inf
-- subnormal results through the ternary: `a · b = 2^-1075 (1 + 2^-53 − 2^-105)` rounds up
private def a : Float := (1.0 + 2.0 ^ (-52.0)) * 2.0 ^ (-1000.0)
private def b : Float := (1.0 - 2.0 ^ (-53.0)) * 2.0 ^ (-75.0)
#guard (productFloat64 [a, b]).toBits == 1
#guard productFloat64 [a, b] == a * b
#guard productFloat64 [minSub, 0.5] == 0.0            -- a tie, to even
#guard (productFloat64 [minSub, 1.5]).toBits == 2      -- a tie, to even
#guard (productFloat64 [minSub, 0.75]).toBits == 1
-- special values
#guard (productFloat64 [1.0, 0.0 / 0.0]).isNaN
#guard (productFloat64 [0.0, inf]).isNaN
#guard productFloat64 [inf, -2.0] == -inf
#guard productFloat64 [-inf, -inf] == inf
#guard productFloat64 [inf, 1.0e-300, 1.0e-300] == inf
