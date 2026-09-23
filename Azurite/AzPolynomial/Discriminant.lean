/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMatrix.DetDispatch
import Azurite.AzPolynomial.NewtonMatrix
import Azurite.AzInt.ExactDiv

/-!
# Discriminant of a monic polynomial (computable)

For a monic polynomial `P : AzPolynomial R` of degree `p`, the
discriminant is the determinant of the `p × p` Hankel matrix of Newton
sums `Newt_0(P)` (BPR §4.1). Using the Vandermonde identity
`V Vᵀ = Newt_0(P)`, we get
`det(V Vᵀ) = det(V)² = ∏_{i<j} (αᵢ − αⱼ)² = disc(P)`.

This is the computable analog of the noncomputable
`Azurite.BPR.Chapter4.disc` over `[Field K]`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [AzMatrix.HasDet R]

/-- **Computable discriminant of a monic polynomial.** For a monic
    polynomial `P` of degree `p`, returns
    `det(P.newtMatMonic p) = det(Newt_0(P)) = ∏_{i<j} (αᵢ − αⱼ)²`,
    where the `αᵢ` are the roots of `P` in an algebraic closure.

    For degree `0` (constant polynomial `1`) the empty Hankel matrix has
    determinant `1`. The function is only mathematically meaningful when
    `P` is monic; for non-monic inputs, `newtonSumMonic` does not
    compute the true Newton sums. -/
def discriminantMonic (P : AzPolynomial R) : R :=
  (P.newtMatMonic P.natDegree).det

section Tests

/-! #### Over `AzRat` (Field instance → Gauss) -/

-- P = X − 5, single root, disc = empty product = 1.
#guard
  (parseAzPolynomial (R := AzRat) "x-5").get!.discriminantMonic == 1

-- P = X² − 3X + 2 = (X−1)(X−2), disc = (1−2)² = 1.
#guard
  (parseAzPolynomial (R := AzRat) "x^2-3*x+2").get!.discriminantMonic == 1

-- P = X² + 1 (roots ±i), disc = (i − (−i))² = (2i)² = −4.
#guard
  (parseAzPolynomial (R := AzRat) "x^2+1").get!.discriminantMonic == -4

-- P = (X−1)² = X² − 2X + 1 (repeated root), disc = (1−1)² = 0.
#guard
  (parseAzPolynomial (R := AzRat) "x^2-2*x+1").get!.discriminantMonic == 0

-- P = X³ − 6X² + 11X − 6 = (X−1)(X−2)(X−3),
--   disc = (1−2)²(1−3)²(2−3)² = 4.
#guard
  (parseAzPolynomial (R := AzRat) "x^3-6*x^2+11*x-6").get!.discriminantMonic == 4

/-! #### Over `AzInt` (Domain + ExactDiv → Bareiss) -/

#guard
  (parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!.discriminantMonic == 1

#guard
  (parseAzPolynomial (R := AzInt) "x^3-6*x^2+11*x-6").get!.discriminantMonic == 4

-- P = X² + 1 over AzInt: disc = −4.
#guard
  (parseAzPolynomial (R := AzInt) "x^2+1").get!.discriminantMonic == -4

end Tests

end Azurite.AzPolynomial
