/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proof for `AzMatrix.mulList`: agrees with `Matrix.toMat` of the
  list product.
-/
import Azurite.AzMatrix.Equiv.Algebra
import Azurite.AzMatrix.MulList

namespace Azurite
variable {R : Type _} [CommSemiring R] {n : Nat}

/-- `mulList Ms` is the list product of the underlying Mathlib matrices. -/
@[simp]
theorem AzMatrix.toMat_mulList (Ms : List (AzMatrix R n n)) :
    toMat (AzMatrix.mulList Ms) = (Ms.map toMat).prod := by
  unfold AzMatrix.mulList
  -- Generalise to an arbitrary accumulator.
  suffices h : ∀ (acc : AzMatrix R n n),
      toMat (Ms.foldl AzMatrix.mul acc) = toMat acc * (Ms.map toMat).prod by
    have := h AzMatrix.identity
    show toMat (Ms.foldl AzMatrix.mul (1 : AzMatrix R n n)) = _
    rw [show (AzMatrix.identity : AzMatrix R n n) = 1 from rfl] at this
    rw [this, toMat_one, one_mul]
  intro acc
  induction Ms generalizing acc with
  | nil => simp
  | cons M Ms' ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih (AzMatrix.mul acc M)]
    show toMat (acc * M) * _ = _
    rw [toMat_mul, mul_assoc]

end Azurite
