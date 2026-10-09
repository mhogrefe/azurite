/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.SumProduct
import Azurite.AzNat.Instances
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Mul.Dispatch

/-!
## Correctness of `AzNat.sum` and `AzNat.product`

`toNat_sum` and `toNat_product`: the list sum and the balanced product compute the sum and the
product of the values (`balancedProduct_eq_prod` in the monoid `AzNat`, then `toNat` over the
list product), with the array versions as corollaries.
-/

namespace Azurite.AzNat

theorem toNat_foldl_add (l : List AzNat) (acc : AzNat) :
    (l.foldl (· + ·) acc).toNat = acc.toNat + (l.map toNat).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, toNat_add, List.map_cons, List.sum_cons]
    ring

/-- **`sum` computes the sum.** -/
theorem toNat_sum (l : List AzNat) : (sum l).toNat = (l.map toNat).sum := by
  rw [sum, toNat_foldl_add, toNat_zero, zero_add]

theorem toNat_list_prod : ∀ l : List AzNat, l.prod.toNat = (l.map toNat).prod
  | [] => toNat_one
  | x :: xs => by rw [List.prod_cons, toNat_mul, toNat_list_prod xs, List.map_cons, List.prod_cons]

/-- **`product` computes the product.** -/
theorem toNat_product (l : List AzNat) : (product l).toNat = (l.map toNat).prod := by
  rw [product, Azurite.balancedProduct_eq_prod, toNat_list_prod]

theorem toNat_sumArray (a : Array AzNat) : (sumArray a).toNat = (a.toList.map toNat).sum :=
  toNat_sum _

theorem toNat_productArray (a : Array AzNat) :
    (productArray a).toNat = (a.toList.map toNat).prod :=
  toNat_product _

end Azurite.AzNat
