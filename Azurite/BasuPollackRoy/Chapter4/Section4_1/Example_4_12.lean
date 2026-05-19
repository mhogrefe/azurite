import Azurite.AzPolynomial.Discriminant
import Azurite.AzPolynomial.MvCoeffParse
import Azurite.AzInt.ExactDiv
import Azurite.AzInt.Instances
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.ExactDivCR
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzMvPolynomial.Var
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_9

/-!
# BPR Example 4.12: discriminant of `X³ + aX + b`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

Computes the discriminant of the depressed cubic `P(X) = X³ + aX + b`
over `AzInt[a, b]` via `discriminantMonic`, which dispatches to
`bareissDet` of the `3 × 3` Newton matrix `Newt₀(P)` (Proposition 4.9
with `k = p = 3`). The result is the classical value
`Disc(P) = −4a³ − 27b²`.
-/

namespace Azurite.BPR.Chapter4

open Azurite.AzPolynomial

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

/-- Coefficient ring: `AzInt[a, b]` under the degree-reverse-lex order
    (`a = X₀`, `b = X₁`). -/
private abbrev MvCoeff := AzMvPolynomial 2 AzInt MonomialOrder.Degrevlex

/-- The depressed cubic `P(X) = X³ + aX + b`, parsed from
    `"x^3+(a)*x+(b)"` as an `AzPolynomial MvCoeff`. -/
private def P_cubic : AzPolynomial MvCoeff :=
  (AzPolynomial.parseStrMvCoeffWith (AbcVar 2) (n := 2) (R := AzInt)
    (ord := MonomialOrder.Degrevlex) "x^3+(a)*x+(b)").getD 0

-- Sanity check: round-trip the input string.
#guard P_cubic.toStrMvCoeffWith (AbcVar 2) == "x^3+(a)*x+(b)"

-- **BPR Example 4.12.** `Disc(X³ + aX + b) = −4a³ − 27b²`.
#guard P_cubic.discriminantMonic.toStrWith (AbcVar 2) == "-4*a^3-27*b^2"

end Azurite.BPR.Chapter4
