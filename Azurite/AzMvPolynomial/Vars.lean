/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Variables occurring in `AzMvPolynomial` terms — indexed by `Fin n`.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [Semiring R] {n : ℕ} {ord : MonomialOrder}

/-- The set of variable indices with nonzero exponent in a monic monomial. -/
def MonicMonomial.vars (m : MonicMonomial n ord) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => m.exponents[i] ≠ 0)

/-- The set of variable indices occurring in a monomial. -/
def Monomial.vars (m : Monomial n R ord) : Finset (Fin n) :=
  m.monic.vars

/-- The set of variable indices occurring in any term of the polynomial. -/
def AzMvPolynomial.vars (p : AzMvPolynomial n R ord) : Finset (Fin n) :=
  p.terms.foldl (init := ∅) fun acc m => acc ∪ m.vars

end Azurite
