import Azurite.AzPolynomial.ExtendedSRemS
import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.SignedSubresultant
import Azurite.AzPolynomial.ToString

/-!
# BPR unnumbered example (preceding Corollary 8.38): signed remainders vs signed subresultants

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, Springer 2006, §8.3.1
> (the worked example just before Corollary 8.38).

For `P = X¹¹ − X¹⁰ + 1` and its derivative `P'`, we compute both

* the **signed remainder sequence** of `P, P'` (Algorithm 8.19), over `AzRat`; and
* the **signed subresultant sequence** of `P, P'` (Algorithm 8.21), over `AzInt`.

`P` is squarefree, so the gcd of `P, P'` is a (nonzero) constant.  The degree sequence of the
signed remainders is `11, 10, 9, 1, 0` — it is **defective** (a long jump from degree `9` to
degree `1`), which is exactly the situation Corollary 8.38 covers.

The example illustrates two points at once:

* **Coefficient explosion.**  The signed remainders accumulate denominators that are powers of
  `11` (`10/121 = 10/11²`, `−1331/10 = −11³/10`, `275311670611/285311670611 = (11¹¹−10¹⁰)/11¹¹`),
  whereas the signed subresultants stay **integers**.
* **The correspondence (Cor 8.38).**  Each nonzero signed remainder is proportional to a signed
  subresultant: `SRemS₂ = (1/11²)·sResP₉`, `SRemS₃ = (121/100)·sResP₈`, and the resultant
  `sResP₀ = −275311670611 = −(11¹¹ − 10¹⁰)` is the numerator of `SRemS₄`.

Each value is pinned down by a `#guard` on its `toString`.
-/

namespace Azurite.BPR.Chapter8.Example_SignedSubresultant

open Azurite.AzPolynomial

/-! ### Signed remainder sequence over `AzRat` (Algorithm 8.19) -/

/-- `P = X¹¹ − X¹⁰ + 1`. -/
def P : AzPolynomial AzRat := (parseAzPolynomial (R := AzRat) "x^11-x^10+1").get!

/-- Its derivative `P' = 11X¹⁰ − 10X⁹`. -/
def P' : AzPolynomial AzRat := P.derivative

/-- The signed remainder sequence `SRemS₀, …, SRemS₅` of `P` and `P'` (Algorithm 8.19). -/
def srs : List (AzPolynomial AzRat) := sRemSList P P' 6

-- `SRemS₀, …, SRemS₅`.  The degree sequence `11, 10, 9, 1, 0` is defective (it jumps from `9`
-- to `1`); `SRemS₄` is a nonzero constant (so `P` is squarefree) and `SRemS₅ = 0` terminates it.
#guard srs.map toString ==
  ["x^11-x^10+1", "11*x^10-10*x^9", "10/121*x^9-1", "-1331/10*x+121",
   "275311670611/285311670611", "0"]

/-! ### Signed subresultant sequence over `AzInt` (Algorithm 8.21) -/

/-- `P = X¹¹ − X¹⁰ + 1` over the integers. -/
def Pz : AzPolynomial AzInt := (parseAzPolynomial (R := AzInt) "x^11-x^10+1").get!

/-- Its derivative `P'` over the integers. -/
def Pz' : AzPolynomial AzInt := Pz.derivative

/-- The signed subresultant sequence: `(sResP₀, …, sResP₁₁)` together with the signed
    subresultant coefficients `(s₀, …, s₁₁)`. -/
def sres : Array (AzPolynomial AzInt) × Array AzInt := signedSubresultant Pz Pz'

-- `sResP_ℓ` for `ℓ = 0, …, 11`.  The polynomials at the defective indices `2, …, 7` vanish,
-- and the two degree-`1` subresultants `sResP₈` (the defective block) and `sResP₁` are distinct.
#guard sres.1.toList.map toString ==
  ["-275311670611", "2143588810*x-1948717100", "0", "0", "0", "0", "0", "0",
   "-110*x+100", "10*x^9-121", "11*x^10-10*x^9", "x^11-x^10+1"]

-- The signed subresultant coefficients `s_ℓ`: `s_ℓ = 0` exactly at the defective indices
-- `2, …, 8`, and `s₀ = −275311670611` is the resultant `Res(P, P')`.
#guard sres.2.toList.map toString ==
  ["-275311670611", "2143588810", "0", "0", "0", "0", "0", "0", "0", "10", "11", "1"]

end Azurite.BPR.Chapter8.Example_SignedSubresultant
