/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.BalancedProduct
import Azurite.AzNat.Add
import Azurite.AzNat.Mul
import Azurite.AzNat.ToStringBase
import Azurite.AzNat.ParseBase

/-!
## Sums and products of lists

`sum` is a plain left fold — addition is linear, so nothing is gained by reordering — while
`product` is the balanced tree of pairwise products (`Azurite.balancedProduct`), which keeps the
operands of every multiplication of similar size so that the subquadratic algorithms apply
throughout.  `sumArray`/`productArray` are the `Array` entry points.
-/

namespace Azurite.AzNat

/-- The sum of a list, by a left fold. -/
def sum (l : List AzNat) : AzNat := l.foldl (· + ·) 0

/-- The product of a list, by a balanced tree of pairwise products. -/
def product (l : List AzNat) : AzNat := Azurite.balancedProduct l

/-- The sum of an array. -/
def sumArray (a : Array AzNat) : AzNat := sum a.toList

/-- The product of an array, by a balanced tree of pairwise products. -/
def productArray (a : Array AzNat) : AzNat := product a.toList

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def N (s : String) : AzNat := (AzNat.parse s).get!
private def L (xs : List Nat) : List AzNat := xs.map ofNat

#guard AzNat.toString (sum []) == "0"
#guard AzNat.toString (sum (L [7])) == "7"
#guard AzNat.toString (sum (L [1, 2, 3, 4, 5])) == "15"
#guard AzNat.toString (sum [N "18446744073709551615", N "1", N "18446744073709551615"])
  == "36893488147419103231"
#guard AzNat.toString (product []) == "1"
#guard AzNat.toString (product (L [7])) == "7"
#guard AzNat.toString (product (L [2, 3, 5, 7, 11])) == "2310"
#guard AzNat.toString (product (L [2, 3, 5, 7, 11, 13])) == "30030"
#guard AzNat.toString (product (L [0, 3, 5])) == "0"
#guard AzNat.toString (product [N "18446744073709551616", N "18446744073709551616"])
  == "340282366920938463463374607431768211456"
-- the balanced tree agrees with the fold on a long list of mixed sizes
#guard product ((List.range 1000).map fun i => ofNat (i * 7919 + 1))
  == (List.range 1000).foldl (fun acc i => acc * ofNat (i * 7919 + 1)) 1
#guard AzNat.toString (sumArray #[N "5", N "6"]) == "11"
#guard AzNat.toString (productArray #[N "5", N "6", N "7"]) == "210"
#guard AzNat.toString (productArray #[]) == "1"

end Tests
