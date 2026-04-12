/-
  Examples demonstrating that `AzPolynomial` works over `AzMvPolynomial ℤ`
  coefficients, using the dedicated `toStrMvCoeffWith` / `parseStrMvCoeffWith`
  serializers from `MvCoeffParse`.

  The inner variable scheme is `AbcVar 3` (`a, b, c`) so there is no collision
  with the outer variable, which is always rendered as `x`.
-/
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.PRem
import Azurite.AzPolynomial.MvCoeffParse

namespace Azurite.AzPolynomial.MvCoeffExamples

open Azurite

/-- Coefficient ring used by the examples below: `ℤ[a, b, c]` under degrevlex. -/
abbrev MvInt := AzMvPolynomial 3 ℤ .Degrevlex

private instance : Fact (3 ≤ 26) := ⟨by omega⟩

/-- Parse a string as an `AzPolynomial MvInt` using `AbcVar 3` for the inner
    variables.  The outer variable is `x`. -/
private def p (s : String) : AzPolynomial MvInt :=
  (AzPolynomial.parseStrMvCoeffWith (AbcVar 3) (n := 3) (R := ℤ)
    (ord := .Degrevlex) s).getD 0

/-- Render an `AzPolynomial MvInt` as a string using `AbcVar 3`. -/
private def s (q : AzPolynomial MvInt) : String :=
  q.toStrMvCoeffWith (AbcVar 3)

/-! ### Constructing `AzPolynomial MvInt` values from strings -/

-- The zero polynomial
#guard s (p "0") == "0"

-- The one polynomial
#guard s (p "(1)") == "(1)"

-- A constant whose coefficient is `2*a + 3*b`
#guard s (p "(2*a+3*b)") == "(2*a+3*b)"

-- Linear polynomial `a*x + (b+1)`
#guard s (p "(a)*x+(b+1)") == "(a)*x+(b+1)"

-- Quadratic with a `1`-coefficient term:  `x^2 + (-c)*x + (1)`
#guard s (p "x^2+(-c)*x+(1)") == "x^2+(-c)*x+(1)"

-- The flagship example `(3*a+b)*x^2 + (-c)*x + (a+b)`
#guard s (p "(3*a+b)*x^2+(-c)*x+(a+b)") == "(3*a+b)*x^2+(-c)*x+(a+b)"

/-! ### Ring operations, verified via string round-trips -/

-- Addition: `(a*x + (b+1)) + (-a*x + c) = (b+c+1)`
#guard s (p "(a)*x+(b+1)" + p "(-a)*x+(c)") == "(b+c+1)"

-- Subtraction: `p - p = 0`
#guard s (p "(a)*x+(b+1)" - p "(a)*x+(b+1)") == "0"

-- Negation through subtraction: `0 - (a) = (-a)`
#guard s (0 - p "(a)") == "(-a)"

-- Multiplication: `(a*x + b) * (-b*x + a) = (-a*b)*x^2 + (a^2 - b^2)*x + a*b`
#guard s (p "(a)*x+(b)" * p "(-b)*x+(a)") == "(-a*b)*x^2+(a^2-b^2)*x+(a*b)"

-- Squaring `(x + a)` gives `x^2 + 2a*x + a^2`.
#guard s (p "x+(a)" * p "x+(a)") == "x^2+(2*a)*x+(a^2)"

/-! ### Pseudo-remainder over `MvInt` -/

-- `(x^2 + b)` pRem `(x + a)`.
-- d = 2, b_lc = 1.  x^2 + b = (x - a)*(x + a) + (a^2 + b).
#guard s (pRem (p "x^2+(b)") (p "x+(a)")) == "(a^2+b)"

-- `x^2` pRem `(a*x + b)`: non-unit leading coefficient.
-- a^2 * x^2 = (a*x - b)*(a*x + b) + b^2.
#guard s (pRem (p "x^2") (p "(a)*x+(b)")) == "(b^2)"

-- `(a*x^2 + b)` pRem `(x + a)`.
-- a*x^2 + b = (a*x - a^2)*(x + a) + (a^3 + b).
#guard s (pRem (p "(a)*x^2+(b)") (p "x+(a)")) == "(a^3+b)"

-- deg P < deg Q: pseudo-remainder is P.
#guard s (pRem (p "x+(a)") (p "x^3+(1)")) == "x+(a)"

end Azurite.AzPolynomial.MvCoeffExamples
