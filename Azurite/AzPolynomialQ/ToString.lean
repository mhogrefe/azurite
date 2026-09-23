/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomialQ.Basic
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.ToString
import Azurite.AzMvPolynomial.ParsableCoeff.AzRat

/-!
# AzPolynomialQ toString

`AzPolynomialQ.toChars` is a thin wrapper that converts to `AzPolynomial AzRat`
and defers to `AzPolynomial.toChars`.
-/

namespace Azurite

open _root_.Azurite.AzPolynomial

namespace AzPolynomialQ

/-- Format a `AzPolynomialQ` as a human-readable polynomial string via
    `AzPolynomial.toChars` applied to `p.toAzRatPolynomial`. -/
def toChars (p : AzPolynomialQ) : String :=
  AzPolynomial.toChars p.toAzRatPolynomial

instance : ToString AzPolynomialQ where
  toString := toChars

end AzPolynomialQ

end Azurite
