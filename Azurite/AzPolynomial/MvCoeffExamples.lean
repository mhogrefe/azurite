/-
  Examples demonstrating that `AzPolynomial` works over `AzMvPolynomialNew ℤ`
  coefficients.

  The point of these tests is to exercise the typeclass machinery: building
  an `AzPolynomial (AzMvPolynomialNew n ℤ ord)` requires `Semiring`, `DecidableEq`,
  and (for arithmetic) the full `CommRing` instance on `AzMvPolynomialNew n ℤ ord`
  to be **computable**. There is no `parseAzPolynomial` or `toString` for these
  polynomials (the coefficients are themselves multivariate polynomials), so
  individual coefficients are built via `AzMvPolynomialNew.parseWith` and the
  outer polynomial is assembled with `monomial`, `C`, and ring operations.
-/
import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.PRem
import Azurite.AzMvPolynomial.New.Equiv.Algebra
import Azurite.AzMvPolynomial.New.Parse

namespace Azurite.AzPolynomial.MvCoeffExamples

open Azurite

/-- Coefficient ring used by the examples below: `ℤ[x, y, z]` under degrevlex. -/
abbrev MvInt := AzMvPolynomialNew 3 ℤ .Degrevlex

/-- Helper: parse a string as an element of `MvInt` using the `XyzVar 3`
    naming scheme (`x, y, z`). -/
private def mv (s : String) : MvInt :=
  (AzMvPolynomialNew.parseWith (n := 3) (R := ℤ) (ord := .Degrevlex)
    (XyzVar 3) s.toList).getD 0

/-! ### Constructing `AzPolynomial MvInt` values -/

/-- The zero polynomial in `AzPolynomial MvInt`. -/
private def p_zero : AzPolynomial MvInt := 0

#guard p_zero.coeffs.size == 0

/-- The one polynomial in `AzPolynomial MvInt`. -/
private def p_one : AzPolynomial MvInt := 1

#guard p_one.coeffs.size == 1
#guard p_one.coeff 0 == (mv "1")

/-- A constant `AzPolynomial` whose coefficient is `2*x + 3*y`. -/
private def p_const : AzPolynomial MvInt := C (mv "2*x+3*y")

#guard p_const.coeffs.size == 1
#guard p_const.coeff 0 == mv "2*x+3*y"

/-- The polynomial `x * T + (y + 1)` in `MvInt[T]` (where `T` is the
    outer indeterminate of `AzPolynomial`). Built by adding two monomials. -/
private def p_lin : AzPolynomial MvInt :=
  monomial 1 (mv "x") + C (mv "y+1")

#guard p_lin.coeffs.size == 2
#guard p_lin.coeff 0 == mv "y+1"
#guard p_lin.coeff 1 == mv "x"

/-- The polynomial `(x*y) * T^2 + (-z) * T + 1`. -/
private def p_quad : AzPolynomial MvInt :=
  monomial 2 (mv "x*y") + monomial 1 (mv "-z") + C (mv "1")

#guard p_quad.coeffs.size == 3
#guard p_quad.coeff 0 == mv "1"
#guard p_quad.coeff 1 == mv "-z"
#guard p_quad.coeff 2 == mv "x*y"

/-! ### Ring operations on `AzPolynomial MvInt` -/

-- Addition: `(x*T + (y+1)) + ((-x)*T + z) = (y+1+z)`
#guard
  (p_lin + (monomial 1 (mv "-x") + C (mv "z"))).coeff 0 == mv "y+z+1"

-- Subtraction: `p_lin - p_lin = 0`
#guard (p_lin - p_lin).coeffs.size == 0

-- Negation through subtraction: `0 - C(x) = C(-x)`
#guard ((0 : AzPolynomial MvInt) - C (mv "x")).coeff 0 == mv "-x"

-- Multiplication: `(x*T + y) * ((-y)*T + x) = (-x*y)*T^2 + (x^2 - y^2)*T + x*y`
private def p_a : AzPolynomial MvInt := monomial 1 (mv "x") + C (mv "y")
private def p_b : AzPolynomial MvInt := monomial 1 (mv "-y") + C (mv "x")
private def p_ab : AzPolynomial MvInt := p_a * p_b

#guard p_ab.coeffs.size == 3
#guard p_ab.coeff 0 == mv "x*y"
#guard p_ab.coeff 1 == mv "x^2-y^2"
#guard p_ab.coeff 2 == mv "-x*y"

-- The leading coefficient of `p_quad` is `x*y`.
#guard p_quad.leadingCoeff == mv "x*y"

-- Squaring `(T + x)` gives `T^2 + 2x * T + x^2`.
private def p_T_plus_x : AzPolynomial MvInt := monomial 1 (mv "1") + C (mv "x")
private def p_sq : AzPolynomial MvInt := p_T_plus_x * p_T_plus_x

#guard p_sq.coeffs.size == 3
#guard p_sq.coeff 0 == mv "x^2"
#guard p_sq.coeff 1 == mv "2*x"
#guard p_sq.coeff 2 == mv "1"

/-! ### Pseudo-remainder over `MvInt` -/

-- `(T^2 + y)` pRem `(T + x)`.
-- d = 2, b = 1.  T^2 + y = (T - x)*(T + x) + (x^2 + y).
private def p_prem1_P : AzPolynomial MvInt := monomial 2 (mv "1") + C (mv "y")
private def p_prem1_Q : AzPolynomial MvInt := monomial 1 (mv "1") + C (mv "x")
#guard pRem p_prem1_P p_prem1_Q == C (mv "x^2+y")

-- `(T^2)` pRem `(x*T + y)`: non-unit leading coefficient.
-- d = 2, b = x, b^2 * P = x^2 * T^2.
-- x^2 * T^2 = (x*T - y)*(x*T + y) + y^2, so the pseudo-remainder is y^2.
private def p_prem2_P : AzPolynomial MvInt := monomial 2 (mv "1")
private def p_prem2_Q : AzPolynomial MvInt := monomial 1 (mv "x") + C (mv "y")
#guard pRem p_prem2_P p_prem2_Q == C (mv "y^2")

-- `(x*T^2 + y)` pRem `(T + x)`.
-- d = 2, b = 1. x*T^2 + y = (x*T - x^2)*(T + x) + (x^3 + y).
private def p_prem3_P : AzPolynomial MvInt := monomial 2 (mv "x") + C (mv "y")
private def p_prem3_Q : AzPolynomial MvInt := monomial 1 (mv "1") + C (mv "x")
#guard pRem p_prem3_P p_prem3_Q == C (mv "x^3+y")

-- deg P < deg Q: the pseudo-remainder is `P`.
#guard pRem p_prem1_Q (monomial 3 (mv "1") + C (mv "1") : AzPolynomial MvInt) == p_prem1_Q

end Azurite.AzPolynomial.MvCoeffExamples
