/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.BalancedProduct
import Azurite.AzRat.Add
import Azurite.AzRat.Mul
import Azurite.AzRat.Parse
import Azurite.AzRat.ToString

/-!
## Sums and products of lists of rationals

Both `sum` and `product` use balanced trees (`Azurite.balancedSum`, `Azurite.balancedProduct`):
adding rationals costs a gcd and multiplications of the numerators and denominators, so unlike
for integers a left fold would keep combining a large accumulator with small terms, while the
tree keeps the operands of every operation of similar size.  `sumArray`/`productArray` take
arrays.
-/

namespace Azurite.AzRat

/-- The sum of a list, by a balanced tree of pairwise sums. -/
def sum (l : List AzRat) : AzRat := Azurite.balancedSum l

/-- The product of a list, by a balanced tree of pairwise products. -/
def product (l : List AzRat) : AzRat := Azurite.balancedProduct l

/-- The sum of an array, by a balanced tree of pairwise sums. -/
def sumArray (a : Array AzRat) : AzRat := sum a.toList

/-- The product of an array, by a balanced tree of pairwise products. -/
def productArray (a : Array AzRat) : AzRat := product a.toList

end Azurite.AzRat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzRat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def L (xs : List String) : List AzRat := xs.map Q

#guard AzRat.toString (sum []) == "0"
#guard AzRat.toString (sum (L ["-7/3"])) == "-7/3"
#guard AzRat.toString (sum (L ["1/2", "1/3", "1/6"])) == "1"
#guard AzRat.toString (sum (L ["1/2", "-1/3", "1/4", "-1/5"])) == "13/60"
#guard AzRat.toString (sum (L ["5/7", "-5/7"])) == "0"
#guard AzRat.toString (product []) == "1"
#guard AzRat.toString (product (L ["-7/3"])) == "-7/3"
#guard AzRat.toString (product (L ["2/3", "3/4", "4/5", "5/6"])) == "1/3"
#guard AzRat.toString (product (L ["-2/3", "3/4", "-4/5", "5/6", "6/7"])) == "2/7"
#guard AzRat.toString (product (L ["0", "-3/2", "5"])) == "0"
-- the harmonic number `H_20` and the balanced trees against the folds on a long list
#guard AzRat.toString (sum ((List.range 20).map fun i => Q s!"1/{i + 1}"))
  == "55835135/15519504"
private def term (i : Nat) : AzRat := Q s!"{if i % 2 = 0 then "" else "-"}{i + 1}/{i * 7 + 3}"
#guard sum ((List.range 500).map term) == (List.range 500).foldl (fun acc i => acc + term i) 0
#guard product ((List.range 500).map term)
  == (List.range 500).foldl (fun acc i => acc * term i) 1
#guard AzRat.toString (sumArray #[Q "5/2", Q "-6/2"]) == "-1/2"
#guard AzRat.toString (productArray #[Q "5/2", Q "-6", Q "7/5"]) == "-21"
#guard AzRat.toString (productArray #[]) == "1"

end Tests
