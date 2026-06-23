import Azurite.AzPolynomial.SturmSequence
import Azurite.AzPolynomial.NumRoots
import Azurite.AzPolynomial.CauchyIndex

/-!
# BPR Example 2.52

With `P = X⁴ − 5X² + 4 = (X − 1)(X + 1)(X − 2)(X + 2)`, the Sturm sequence
`s₀ = P`, `s₁ = P'`, `s_{i+2} = −Rem(s_i, s_{i+1})` is:

    s₀ = X⁴ − 5X² + 4
    s₁ = 4X³ − 10X
    s₂ = −Rem(s₀, s₁) = (5/2) X² − 4
    s₃ = −Rem(s₁, s₂) = (18/5) X
    s₄ = −Rem(s₂, s₃) = 4
    s₅ = −Rem(s₃, s₄) = 0 (and zero forever after)

Consequences computed against the corresponding `AzPolynomial`-side
primitives (Theorems 2.50 and 2.58 plus the definitions of `numRoots` and
`cauchyIndexOn`):

* `P` has `4` distinct real roots in `R`;
* `2` lie in `(0, +∞)` and `2` in `(−∞, 0)`;
* all `4` lie in `(−3, 3)`;
* exactly `1` (namely `x = 2`) lies in `(3/2, +∞)`;
* `Ind(P'/P; −∞, +∞) = 4` (= count of distinct real roots).
-/

namespace Azurite.BPR.Example_2_52

open Azurite.AzPolynomial
open Azurite.BPR (ExtendedPoint)

/-- `P = X⁴ − 5X² + 4`. -/
def P_2_52 : AzPolynomial AzRat := (parseAzPolynomial "x^4-5*x^2+4").get!

/-- `P' = 4X³ − 10X`. -/
def P'_2_52 : AzPolynomial AzRat := (parseAzPolynomial "4*x^3-10*x").get!

/-! ### Sturm sequence terms `s₀..s₅` -/

#guard toString (sturmSequence P_2_52 0) = "x^4-5*x^2+4"
#guard toString (sturmSequence P_2_52 1) = "4*x^3-10*x"
#guard toString (sturmSequence P_2_52 2) = "5/2*x^2-4"
#guard toString (sturmSequence P_2_52 3) = "18/5*x"
#guard toString (sturmSequence P_2_52 4) = "4"
#guard toString (sturmSequence P_2_52 5) = "0"
#guard toString (sturmSequence P_2_52 6) = "0"

/-! ### Distinct real roots of `P` via Sturm's theorem -/

#guard Azurite.AzPolynomial.numRoots P_2_52 = 4
#guard Azurite.AzPolynomial.numRootsOn P_2_52 (.finite 0) .posInf = 2
#guard Azurite.AzPolynomial.numRootsOn P_2_52 .negInf (.finite 0) = 2
#guard Azurite.AzPolynomial.numRootsOn P_2_52 (.finite (-3 : AzRat)) (.finite 3) = 4
#guard Azurite.AzPolynomial.numRootsOn P_2_52 (.finite (3 / 2 : AzRat)) .posInf = 1

/-! ### Cauchy index of `P'/P` -/

#guard cauchyIndexOn P'_2_52 P_2_52 .negInf .posInf = 4
#guard cauchyIndexOn P'_2_52 P_2_52 (.finite 0) .posInf = 2

end Azurite.BPR.Example_2_52
