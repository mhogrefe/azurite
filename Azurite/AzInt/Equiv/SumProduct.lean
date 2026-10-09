/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.SumProduct
import Azurite.AzInt.Instances
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Mul

/-!
## Correctness of `AzInt.sum` and `AzInt.product`

`toInt_sum` and `toInt_product`: the list sum and the balanced product compute the sum and the
product of the values (`balancedProduct_eq_prod` in the monoid `AzInt`), with the array versions
as corollaries.
-/

namespace Azurite.AzInt

theorem toInt_foldl_add (l : List AzInt) (acc : AzInt) :
    (l.foldl (· + ·) acc).toInt = acc.toInt + (l.map toInt).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, toInt_add, List.map_cons, List.sum_cons]
    ring

/-- **`sum` computes the sum.** -/
theorem toInt_sum (l : List AzInt) : (sum l).toInt = (l.map toInt).sum := by
  rw [sum, toInt_foldl_add, toInt_zero, zero_add]

theorem toInt_list_prod : ∀ l : List AzInt, l.prod.toInt = (l.map toInt).prod
  | [] => toInt_one
  | x :: xs => by rw [List.prod_cons, toInt_mul, toInt_list_prod xs, List.map_cons, List.prod_cons]

/-- **`product` computes the product.** -/
theorem toInt_product (l : List AzInt) : (product l).toInt = (l.map toInt).prod := by
  rw [product, Azurite.balancedProduct_eq_prod, toInt_list_prod]

theorem toInt_sumArray (a : Array AzInt) : (sumArray a).toInt = (a.toList.map toInt).sum :=
  toInt_sum _

theorem toInt_productArray (a : Array AzInt) :
    (productArray a).toInt = (a.toList.map toInt).prod :=
  toInt_product _

end Azurite.AzInt
