/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomialQ.Neg
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Neg

open Polynomial

namespace Azurite.AzPolynomialQ

@[simp] lemma toAzPolynomial_neg (p : AzPolynomialQ) : (-p).toAzPolynomial = - p.toAzPolynomial := by
  ext i
  simp

@[simp] lemma toPoly_neg (p : AzPolynomialQ) : (-p).toPoly = - p.toPoly := by
  ext i
  simp

@[simp] lemma ofAzPolynomial_neg (p : Azurite.AzPolynomial ℚ) : ofAzPolynomial (-p) = - ofAzPolynomial p := by
  apply AzPolynomialQ.coeff_ext
  intro i
  simp

end Azurite.AzPolynomialQ
