/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.SumProduct
import Azurite.AzRat.Instances
import Azurite.AzRat.Equiv.Add
import Azurite.AzRat.Equiv.Mul
import Azurite.AzRat.Equiv.Construct

/-!
## Correctness of `AzRat.sum` and `AzRat.product`

`toRat_sum` and `toRat_product`: the balanced sum and product compute the sum and the product of
the values (`balancedSum_eq_sum`/`balancedProduct_eq_prod` in the field `AzRat`), with the array
versions as corollaries.
-/

namespace Azurite.AzRat

theorem toRat_list_sum : ∀ l : List AzRat, (l.sum).toRat = (l.map toRat).sum
  | [] => toRat_zero
  | x :: xs => by rw [List.sum_cons, toRat_add, toRat_list_sum xs, List.map_cons, List.sum_cons]

theorem toRat_list_prod : ∀ l : List AzRat, (l.prod).toRat = (l.map toRat).prod
  | [] => toRat_one
  | x :: xs => by rw [List.prod_cons, toRat_mul, toRat_list_prod xs, List.map_cons, List.prod_cons]

/-- **`sum` computes the sum.** -/
theorem toRat_sum (l : List AzRat) : (sum l).toRat = (l.map toRat).sum := by
  rw [sum, Azurite.balancedSum_eq_sum, toRat_list_sum]

/-- **`product` computes the product.** -/
theorem toRat_product (l : List AzRat) : (product l).toRat = (l.map toRat).prod := by
  rw [product, Azurite.balancedProduct_eq_prod, toRat_list_prod]

theorem toRat_sumArray (a : Array AzRat) : (sumArray a).toRat = (a.toList.map toRat).sum :=
  toRat_sum _

theorem toRat_productArray (a : Array AzRat) :
    (productArray a).toRat = (a.toList.map toRat).prod :=
  toRat_product _

end Azurite.AzRat
