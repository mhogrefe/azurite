/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Evaluation for `AzMvPolynomial`.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite

open MonomialOrder MonicMonomial Monomial

variable {R : Type _} [CommSemiring R] {n : ℕ} {ord : MonomialOrder}

/-- Evaluate an `AzMvPolynomial` at a point given by `f : Fin n → R`. -/
def AzMvPolynomial.eval (p : AzMvPolynomial n R ord) (f : Fin n → R) : R :=
  p.terms.foldl (fun acc m => acc + m.eval f) 0

end Azurite
