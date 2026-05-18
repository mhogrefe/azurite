/-
  Exact division for `AzMvPolynomial n R ord` over a commutative ring `R`
  equipped with `Azurite.ExactDiv R`.

  This is the fraction-free counterpart of the field-based
  `AzMvPolynomial.exactDiv` in `Azurite/AzMvPolynomial/ExactDiv.lean`. When
  the divisor exactly divides the dividend in `R[X_1, …, X_n]`, every
  leading-coefficient division performed by the loop is exact in `R`,
  so the quotient stays in `R[X_1, …, X_n]` — no fraction-field detour.

  Under the same circumstances the result is correct; on inputs where
  `q` does not divide `p`, the function returns an unspecified value
  (a "garbage" default).
-/
import Azurite.AzMvPolynomial.Add
import Azurite.AzMvPolynomial.Sub
import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.CompareEmbed
import Azurite.AzMvPolynomial.ExactDiv
import Azurite.Algorithm.ExactDiv

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial MonomialOrder

variable {n : ℕ} {ord : MonomialOrder}
variable {R : Type _} [CommRing R] [IsDomain R] [DecidableEq R]
  [Azurite.ExactDiv R]

/-! ### Monomial exact division (CommRing + ExactDiv) -/

/-- Divide a monomial `a` by `b` using `ExactDiv.exactDiv` on coefficients.
    Returns `a` (garbage) if the quotient coefficient ends up zero — which
    cannot happen when `b.coeff ∣ a.coeff` in a domain, the only case the
    surrounding algorithm reaches. -/
def Monomial.exactDivCR (a b : Monomial n R ord) : Monomial n R ord :=
  let c := Azurite.ExactDiv.exactDiv a.coeff.val b.coeff.val
  if hne : c = 0 then
    a
  else
    ⟨⟨c, hne⟩, MonicMonomial.div a.monic b.monic⟩

/-! ### Exact division of polynomials -/

/-- One step of synthetic exact division using `Azurite.ExactDiv` on
    coefficients. Uses polynomial multiplication (`*`) for the subtraction
    step so we don't depend on the field-only `AzMvPolynomial.monomialMul`. -/
def exactDivStepCR (r q : AzMvPolynomial n R ord)
    (hr : r.terms.size > 0) (_hq : q.terms.size > 0) :
    Monomial n R ord × AzMvPolynomial n R ord :=
  let leadR := r.terms[0]'(by omega)
  let leadQ := q.terms[0]'(by omega)
  let t := Monomial.exactDivCR leadR leadQ
  (t, r - AzMvPolynomial.ofMonomial t * q)

/-- Fuel-bounded loop for exact division. -/
def AzMvPolynomial.exactDivAuxCR
    (q : AzMvPolynomial n R ord)
    (hq : q.terms.size > 0) :
    ℕ → AzMvPolynomial n R ord → AzMvPolynomial n R ord → AzMvPolynomial n R ord
  | 0, c, _ => c
  | fuel + 1, c, r =>
    if hr : r.terms.size > 0 then
      let (t, r') := exactDivStepCR r q hr hq
      AzMvPolynomial.exactDivAuxCR q hq fuel (c + AzMvPolynomial.ofMonomial t) r'
    else c

/-- **Exact division of multivariate polynomials over a domain with
    `ExactDiv` on coefficients.** -/
def AzMvPolynomial.exactDivCR (p q : AzMvPolynomial n R ord) :
    AzMvPolynomial n R ord :=
  if h : q.terms.size > 0 then
    AzMvPolynomial.exactDivAuxCR q h ((p.totalDegree + 1) ^ n) 0 p
  else
    0

end Azurite

-- The bundled `ExactDiv (AzMvPolynomial n R ord)` instance (operation +
-- lawfulness) lives in `Equiv/ExactDivCR.lean` because the lawfulness proof
-- (`exactDivCR_spec`) is established there.
