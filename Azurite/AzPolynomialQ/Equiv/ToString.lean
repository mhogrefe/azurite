/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomialQ.ToString
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.ToString

/-!
# AzPolynomialQ ↔ AzPolynomial ℚ toString equivalence

`AzPolynomialQ.toChars` is defined as `AzPolynomial.toChars ∘ toAzPolynomial`,
so the equivalence is by definition.
-/

namespace Azurite

open _root_.Azurite.AzPolynomial

namespace AzPolynomialQ

/-- `AzPolynomialQ.toChars` agrees with `AzPolynomial.toChars` applied to
    `p.toAzRatPolynomial`. -/
theorem toChars_eq (p : AzPolynomialQ) :
    p.toChars = AzPolynomial.toChars p.toAzRatPolynomial := rfl

end AzPolynomialQ

end Azurite
