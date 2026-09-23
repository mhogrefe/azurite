/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `AzPolynomial` parsing as a thin facade over `AzMvPolynomial`.

  Delegates to `AzMvPolynomial.parseStrWith (XyzVar 1)` and converts the
  resulting single-variable multivariate polynomial back to an
  `AzPolynomial R`.
-/
import Azurite.AzPolynomial.ToString
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.ToAzPolynomial
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzMvPolynomial.ParsableCoeff.AzRat
import Azurite.AzNat.ParsableElement
import Azurite.AzInt.ParsableElement
import Azurite.AzRat.ParsableElement

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R]

/-- Parse a polynomial string by parsing it as a one-variable
    `AzMvPolynomial` (using the `XyzVar 1` naming scheme) and converting
    back to `AzPolynomial R`. -/
def parseAzPolynomial (s : String) : Option (AzPolynomial R) :=
  (AzMvPolynomial.parseStrWith (XyzVar 1) s : Option (AzMvPolynomial 1 R .Degrevlex))
    |>.map AzMvPolynomial.toAzPolynomial

end Azurite.AzPolynomial
