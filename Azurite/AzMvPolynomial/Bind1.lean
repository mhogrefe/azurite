/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Variable substitution (bind₁) for `AzMvPolynomial`.
-/
import Azurite.AzMvPolynomial.Pow
import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.SMul
import Azurite.AzMvPolynomial.Add

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-- Auxiliary fold for `MonicMonomial.bind₁`. -/
def monicBind₁Aux (m : MonicMonomial n ord)
    (f : Fin n → AzMvPolynomial n R ord) (i : ℕ) (acc : AzMvPolynomial n R ord) :
    AzMvPolynomial n R ord :=
  if h : i < n then
    let e := m.exponents[i]
    monicBind₁Aux m f (i + 1) (acc * (f ⟨i, h⟩).pow e)
  else acc
termination_by n - i

/-- Substitute polynomials for variables in a monic monomial. -/
def MonicMonomial.bind₁ (m : MonicMonomial n ord)
    (f : Fin n → AzMvPolynomial n R ord) : AzMvPolynomial n R ord :=
  monicBind₁Aux m f 0 1

/-- Substitute polynomials for variables in a monomial. -/
def Monomial.bind₁ (m : Monomial n R ord)
    (f : Fin n → AzMvPolynomial n R ord) : AzMvPolynomial n R ord :=
  m.coeff.val • m.monic.bind₁ f

/-- Substitute polynomials for variables in a multivariate polynomial. -/
def AzMvPolynomial.bind₁ (p : AzMvPolynomial n R ord)
    (f : Fin n → AzMvPolynomial n R ord) : AzMvPolynomial n R ord :=
  p.terms.foldl (init := 0) fun acc m => acc + m.bind₁ f

end Azurite
