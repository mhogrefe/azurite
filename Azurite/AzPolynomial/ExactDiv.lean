/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Exact division for `AzPolynomial R` over a commutative ring `R` equipped
  with an `Azurite.ExactDiv R` instance.

  The algorithm is synthetic division (a fraction-free variant of
  Algorithm 8.3 in `AzPolynomial/QuoRem.lean`): when `Q ∣ P` in `R[X]`,
  each leading-coefficient division performed during the loop is exact
  in `R`, so the quotient stays in `R[X]` without any fraction-field
  detour.

  On inputs where `Q` does not divide `P` exactly, the function returns
  an unspecified value (the partial quotient computed using whatever
  `ExactDiv.exactDiv` returns on non-divisible inputs).
-/
import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Monomial
import Azurite.Algorithm.ExactDiv

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]

/-- One step of synthetic exact division: shave the leading coefficient
    of the running remainder by dividing it (exactly) by the leading
    coefficient of `Q`. -/
def exactDivStep (q : ℕ) (bq : R) (Q : AzPolynomial R) (j : ℕ)
    (cr : AzPolynomial R × AzPolynomial R) : AzPolynomial R × AzPolynomial R :=
  let (C, Rem) := cr
  let t := Azurite.ExactDiv.exactDiv (Rem.coeff j) bq
  let m := monomial (j - q) t
  (C + m, Rem - mulBasecaseFold m Q)

/-- Synthetic exact division as a quotient/remainder pair. When `Q ∣ P`,
    the remainder is `0` and the first component is the true quotient
    `P / Q : AzPolynomial R`. -/
def exactDivQuoRem (P Q : AzPolynomial R) :
    AzPolynomial R × AzPolynomial R :=
  if Q.coeffs.size = 0 then (0, P)
  else if P.coeffs.size = 0 then (0, P)
  else if P.coeffs.size < Q.coeffs.size then (0, P)
  else
    let p := P.coeffs.size - 1
    let q := Q.coeffs.size - 1
    let bq := Q.leadingCoeff
    let numSteps := P.coeffs.size - Q.coeffs.size + 1
    (List.range numSteps).foldl
      (fun cr k => exactDivStep q bq Q (p - k) cr)
      (0, P)

/-- **Exact division of polynomials.** Returns the quotient `P / Q` when
    `Q ∣ P` in `R[X]`. Unspecified otherwise. -/
def exactDiv (P Q : AzPolynomial R) : AzPolynomial R :=
  (exactDivQuoRem P Q).1

end Azurite.AzPolynomial

-- The bundled `ExactDiv (AzPolynomial R)` instance (operation + lawfulness)
-- lives in `Equiv/ExactDiv.lean` because the lawfulness proof
-- (`exactDiv_spec`) is established there.
