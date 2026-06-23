import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R]

/-- Evaluates `p` at a value `x` in the semiring `R` using Horner's method. -/
def eval (p : AzPolynomial R) (x : R) : R :=
  p.coeffs.foldr (init := 0) (fun a acc => a + acc * x)

#guard (parseAzPolynomial (R := AzInt) "3*x^4-x^2+1").get!.eval 2 == 45
#guard (parseAzPolynomial (R := AzInt) "3*x^4-x^2+1").get!.eval 0 == 1
#guard (parseAzPolynomial (R := AzInt) "3*x^4+x^3+8*x^2+2*x+1").get!.eval 10 == 31821

/-- **BPR Algorithm 8.8 (Special Evaluation).**
    Computes `c ^ p * P(b / c)` entirely in the integers, where
    `p = natDegree P`. The result avoids rational arithmetic by
    tracking a running power `d = c ^ i` alongside the Horner
    accumulator.

    For `P = a_p X^p + ⋯ + a_0`, the recurrence is:
    - Initialize `(result, d) := (a_p, 1)`
    - For `i` from `1` to `p`:
      - `d := c * d`
      - `result := b * result + d * a_{p−i}`
    - Output `result = c^p * P(b/c)`.

    Uses `p` multiplications by `b`, `p` multiplications by `c`,
    and `p` additions. -/
def evalSpecial (p : AzPolynomial R) (b c : R) : R :=
  (p.coeffs.foldr (init := ((0 : R), (1 : R)))
    (fun a ⟨acc, d⟩ => (a * d + acc * b, d * c))).1

-- P = 3x^2 + 2x + 1, b = 5, c = 2
-- c^2 * P(5/2) = 4 * (75/4 + 5 + 1) = 99
-- ∑ a_k b^k c^{p-k} = 1·1·4 + 2·5·2 + 3·25·1 = 4 + 20 + 75 = 99
#guard (parseAzPolynomial (R := AzInt) "3*x^2+2*x+1").get!.evalSpecial 5 2 == 99

-- c = 1 recovers ordinary eval
#guard (parseAzPolynomial (R := AzInt) "3*x^4-x^2+1").get!.evalSpecial 2 1 == 45

-- P = x^2 + 1, b = 3, c = 2: c^2(9/4 + 1) = 13
#guard (parseAzPolynomial (R := AzInt) "x^2+1").get!.evalSpecial 3 2 == 13

-- c = 0 gives a_p * b^p
-- P = 2x^2 + x + 3, b = 5, c = 0: 2·25 = 50
#guard (parseAzPolynomial (R := AzInt) "2*x^2+x+3").get!.evalSpecial 5 0 == 50

end Azurite.AzPolynomial
