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
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

/-!
# Tests for the correctly rounded product

Expected values computed by hand (the exact product, then one rounding) shown as decimal output, and
agreement with a fold of exact two-operand multiplications followed by one rounding.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def Pr (xs : List AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  productPrecRound xs p m
/-- The exact product by two-operand multiplications at a precision that holds everything,
then one rounding. -/
private def naive (xs : List AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  setPrecRound (xs.foldl (fun acc x => (mulPrecRound acc x 4096 .Floor).1) one) p m

/-! ## Special values -/

#guard D (Pr [] 5) == ("1.0", .eq)
#guard D (Pr [one] 3) == ("1.0", .eq)
#guard D (Pr [nan, one] 10) == ("NaN", .eq)
#guard D (Pr [one, infinity true] 10) == ("Infinity", .eq)
#guard D (Pr [infinity false, one] 10) == ("-Infinity", .eq)
#guard D (Pr [infinity false, negOne] 10) == ("Infinity", .eq)
#guard D (Pr [infinity true, negOne, X "-2" 2, X "-3" 2] 10) == ("-Infinity", .eq)
#guard D (Pr [infinity true, infinity false] 10) == ("-Infinity", .eq)
#guard D (Pr [infinity false, infinity false] 10) == ("Infinity", .eq)
#guard D (Pr [zero, one] 10) == ("0.0", .eq)
#guard D (Pr [negOne, zero, negOne] 10) == ("0.0", .eq)
#guard D (Pr [zero, infinity true] 10) == ("NaN", .eq)
#guard D (Pr [infinity false, one, zero] 10) == ("NaN", .eq)
#guard D (Pr [nan, zero, infinity true] 10) == ("NaN", .eq)
#guard D (Pr [one] 0) == ("NaN", .eq)

/-! ## Two factors agree with multiplication -/

#guard Pr [X "3" 2, X "3" 2] 4 == mulPrecRound (X "3" 2) (X "3" 2) 4 .Nearest
#guard Pr [X "3" 2, X "5" 3] 3 == mulPrecRound (X "3" 2) (X "5" 3) 3 .Nearest
#guard Pr [X "3" 2, X "5" 3] 3 .Floor == mulPrecRound (X "3" 2) (X "5" 3) 3 .Floor
#guard Pr [X "0.3333333333333333" 53, X "3" 2] 53 == mulPrecRound (X "0.3333333333333333" 53) (X "3\
  " 2) 53 .Nearest
#guard Pr [X "0.3333333333333333" 53, X "3" 2] 53 .Floor
  == mulPrecRound (X "0.3333333333333333" 53) (X "3" 2) 53 .Floor
#guard D (Pr [negOne, X "3" 2] 2) == ("-3.0", .eq)

/-! ## Exact products and roundings -/

#guard D (Pr [negOne, negOne, negOne] 1) == ("-1.0", .eq)
#guard D (Pr [negOne, negOne, negOne, negOne] 1) == ("1.0", .eq)
#guard D (Pr [X "3" 2, X "3" 2, X "3" 2] 5) == ("27.0", .eq)
#guard D (Pr [X "3" 2, X "3" 2, X "3" 2] 3) == ("28.0", .gt)  -- 27 → 28
#guard D (Pr [X "3" 2, X "3" 2, X "3" 2] 3 .Floor) == ("24.0", .lt)
#guard D (Pr [X "3" 2, X "5" 3, X "7" 3] 4) == ("104.0", .lt)  -- 105 → 104
#guard D (Pr [X "3" 2, X "5" 3, X "7" 3] 4 .Ceiling) == ("1.1e2", .gt)
#guard D (Pr [X "3" 2, X "5" 3, X "7" 3] 2) == ("1.0e2", .lt)  -- 105 → 96
#guard D (Pr [X "3" 2, X "5" 3, X "7" 3] 2 .Up) == ("1.3e2", .gt)
#guard D (Pr [X "-3" 2, X "5" 3, X "-7" 3] 4) == ("104.0", .lt)
#guard D (Pr [X "-3" 2, X "-5" 3, X "-7" 3] 4) == ("-104.0", .gt)
#guard D (Pr [X "-3" 2, X "-5" 3, X "-7" 3] 4 .Floor) == ("-1.1e2", .lt)
#guard D (Pr [X "0.5" 1, X "0.5" 1, X "0.5" 1, X "0.5" 1] 1) == ("0.06", .eq)
#guard D (Pr ((List.range 10).map fun i => P i) 1) == ("4.0e13", .eq)
#guard D (Pr ((List.range 100).map fun i => P (-i)) 1) == ("8.0e-1491", .eq)
#guard D (Pr [P 1000000000, P (-999999999)] 1) == ("2.0", .eq)
#guard D (Pr [P 1000000000, X "3" 2, P (-1000000000)] 2) == ("3.0", .eq)
-- `(1 − 2^−54)² = 1 − 2^−53 + 2^−108`, just above the `53`-bit float `1 − 2^−53`
#guard D (Pr [X "0.3333333333333333" 53, X "3" 2, X "0.3333333333333333" 53, X "3" 2] 53) == ("0.99\
  99999999999999", .lt)
#guard D (Pr [X "0.3333333333333333" 53, X "3" 2, X "0.3333333333333333" 53, X "3" 2] 53 .Ceiling)
  == ("1.0", .gt)
-- `10!` from the factors `1, …, 10`
#guard D (Pr ((List.range 10).map fun i => F (toString (i + 1)) 4) 22) == ("3.6288e6", .eq)
#guard D (Pr ((List.range 10).map fun i => F (toString (i + 1)) 4) 10) == ("3.63e6", .gt)

/-! ## Agreement with a fold of exact multiplications -/

private def samples : List (List AzFloat) :=
  [[X "0.3333333333333333" 53, X "1.4" 10, X "-0.846154" 20],
   [X "0.332" 7, X "0.332" 7, X "0.332" 7, X "0.332" 7, X "0.332" 7],
   [X "123456.789" 40, X "-0.001" 30, X "98765" 17, X "0.28571428571428571428" 64],
   (List.range 20).map fun i => F (toString (2 * i + 3) ++ "/" ++ toString (i + 2)) (i + 1),
   [X "-1.5" 2, P 100, X "1.5" 2, P (-100), X "-5" 3]]

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
