/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.BalancedProduct
import Azurite.AzInt.Add
import Azurite.AzInt.Mul
import Azurite.AzInt.Parse
import Azurite.AzInt.ToString

/-!
## Sums and products of lists of integers

The integer counterparts of `AzNat.sum`/`AzNat.product`: `sum` is a left fold, `product` the
balanced tree of pairwise products (`Azurite.balancedProduct`), which keeps the magnitudes of the
operands of every multiplication similar; `sumArray`/`productArray` take arrays.
-/

namespace Azurite.AzInt

/-- The sum of a list, by a left fold. -/
def sum (l : List AzInt) : AzInt := l.foldl (· + ·) 0

/-- The product of a list, by a balanced tree of pairwise products. -/
def product (l : List AzInt) : AzInt := Azurite.balancedProduct l

/-- The sum of an array. -/
def sumArray (a : Array AzInt) : AzInt := sum a.toList

/-- The product of an array, by a balanced tree of pairwise products. -/
def productArray (a : Array AzInt) : AzInt := product a.toList

end Azurite.AzInt

/-! ### Tests -/

section Tests

open Azurite Azurite.AzInt

private def Z (s : String) : AzInt := (AzInt.parse s).get!
private def L (xs : List String) : List AzInt := xs.map Z

#guard AzInt.toString (sum []) == "0"
#guard AzInt.toString (sum (L ["-7"])) == "-7"
#guard AzInt.toString (sum (L ["1", "-2", "3", "-4", "5"])) == "3"
#guard AzInt.toString (sum (L ["5", "-5"])) == "0"
#guard AzInt.toString (sum (L ["-18446744073709551615", "1", "-18446744073709551615"]))
  == "-36893488147419103229"
#guard AzInt.toString (product []) == "1"
#guard AzInt.toString (product (L ["-7"])) == "-7"
#guard AzInt.toString (product (L ["2", "-3", "5", "-7", "11"])) == "2310"
#guard AzInt.toString (product (L ["2", "-3", "5", "-7", "11", "-13"])) == "-30030"
#guard AzInt.toString (product (L ["0", "-3", "5"])) == "0"
#guard AzInt.toString (product (L ["-18446744073709551616", "18446744073709551616"]))
  == "-340282366920938463463374607431768211456"
-- the balanced tree agrees with the fold on a long list of alternating signs
private def alt (i : Nat) : AzInt :=
  (AzNat.ofNat (i * 7919 + 1)).toAzInt * (if i % 2 = 0 then 1 else -1)
#guard product ((List.range 1000).map alt) == (List.range 1000).foldl (fun acc i => acc * alt i) 1
#guard AzInt.toString (sumArray #[Z "5", Z "-6"]) == "-1"
#guard AzInt.toString (productArray #[Z "5", Z "-6", Z "7"]) == "-210"
#guard AzInt.toString (productArray #[]) == "1"

end Tests
