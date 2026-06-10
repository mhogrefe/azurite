import Azurite.AzPolynomial.CauchyIndex

/-!
# BPR Example 2.54

With

    P = (X − 3)² · (X − 1) · (X + 3)
    Q = (X − 5) · (X − 4) · (X − 2) · (X + 1) · (X + 2) · (X + 4)

we have:

* `Ind(Q/P; −∞, +∞) = 0`,
* `Ind(Q/P; −∞, 0) = 1`,
* `Ind(Q/P; 0, +∞) = −1`.

The three identities are verified by `#guard` against the computable
`Azurite.AzPolynomial.cauchyIndexOn` (which agrees with BPR's noncomputable
`Azurite.BPR.cauchyIndexOn` via BPR Theorem 2.58).
-/

namespace Azurite.BPR.Example_2_54

open Azurite.AzPolynomial
open Azurite.BPR (ExtendedPoint)

/-- Linear factor `X − r`. -/
private def linFactor (r : ℚ) : AzPolynomial ℚ := X - C r

def P_2_54 : AzPolynomial ℚ :=
  linFactor 3 * linFactor 3 * linFactor 1 * linFactor (-3)

def Q_2_54 : AzPolynomial ℚ :=
  linFactor 5 * linFactor 4 * linFactor 2 *
    linFactor (-1) * linFactor (-2) * linFactor (-4)

#guard cauchyIndexOn Q_2_54 P_2_54 .negInf .posInf = 0
#guard cauchyIndexOn Q_2_54 P_2_54 .negInf (.finite 0) = 1
#guard cauchyIndexOn Q_2_54 P_2_54 (.finite 0) .posInf = -1

end Azurite.BPR.Example_2_54
