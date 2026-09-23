/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for `AzMvPolynomial.mul`.

  Delegates to `mulNaive` equivalence proofs and will remain valid when
  `mul` switches to a more sophisticated algorithm (as long as the new
  algorithm is also proven equivalent).
-/
import Azurite.AzMvPolynomial.Equiv.MulNaive

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Multiplication commutes with `toMvPoly`. -/
theorem toMvPoly_mul (p q : AzMvPolynomial n R ord) :
    (p * q).toMvPoly = p.toMvPoly * q.toMvPoly :=
  toMvPoly_mulNaive p q

/-- Multiplication commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_mul (p q : MvPolynomial (Fin n) R) :
    (AzMvPolynomial.ofMvPoly (p * q) : AzMvPolynomial n R ord) =
      AzMvPolynomial.ofMvPoly p * AzMvPolynomial.ofMvPoly q := by
  set a := AzMvPolynomial.ofMvPoly (ord := ord) p
  set b := AzMvPolynomial.ofMvPoly (ord := ord) q
  have hp : a.toMvPoly = p := toMvPoly_ofMvPoly p
  have hq : b.toMvPoly = q := toMvPoly_ofMvPoly q
  rw [show p * q = a.toMvPoly * b.toMvPoly from by rw [hp, hq],
      ← toMvPoly_mul]
  exact ofMvPoly_toMvPoly (a * b)

end Azurite
