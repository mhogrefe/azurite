/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `AzPolynomial` display as a thin facade over `AzMvPolynomial`.

  A univariate polynomial is reflected as a one-variable `AzMvPolynomial`
  via `AzPolynomial.toAzMvPolynomial` and rendered using the `XyzVar 1`
  naming scheme (so the variable is printed as `x`).
-/
import Azurite.AzPolynomial.CoeffChars
import Azurite.AzMvPolynomial.ToString
import Azurite.AzMvPolynomial.OfAzPolynomial

namespace Azurite

/-- `1 ≤ 26` lets us reuse `XyzVar 1` (single letter `x`) as the display
    type for univariate polynomials. -/
instance : Fact (1 ≤ 26) := ⟨by decide⟩

namespace AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R]

/-- Convert a univariate polynomial to a `String` by reflecting it as a
    one-variable `AzMvPolynomial` and rendering with `XyzVar 1`. -/
def toChars (p : AzPolynomial R) : String :=
  (AzPolynomial.toAzMvPolynomial (⟨0, Nat.zero_lt_one⟩ : Fin 1) .Degrevlex p :
      AzMvPolynomial 1 R .Degrevlex).toStrWith (XyzVar 1)

end AzPolynomial

instance instToStringAzPolynomial {R : Type _} [Semiring R] [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R] :
    ToString (AzPolynomial R) where
  toString := AzPolynomial.toChars

end Azurite
