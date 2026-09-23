/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.SignedSubresultant
import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.MvCoeffParse
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzMvPolynomial.Equiv.ExactDivCR
import Azurite.AzMvPolynomial.ToString
import Azurite.AzMvPolynomial.Var

/-!
# BPR Example 8.53: signed subresultants of a depressed quartic

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, Springer 2006, §8.3.4
> (the worked example just after Proposition 8.52).

For the depressed quartic with symbolic coefficients

`P = X⁴ + a·X² + b·X + c     (∈ ℤ[a, b, c][X])`

— BPR calls this "the general polynomial of degree 4", but strictly it is *depressed* (no `X³`
term); the genuinely general quartic would also carry a cubic coefficient — the signed subresultant
sequence of `P` and `P' = 4X³ + 2aX + b` (Algorithm 8.21) is, with coefficients in `ℤ[a, b, c]`:

* `sResP₄ = X⁴ + aX² + bX + c            (= P)`
* `sResP₃ = 4X³ + 2aX + b                 (= P')`
* `sResP₂ = −8a·X² − 12b·X − 16c`
* `sResP₁ = (−8a³ − 36b² + 32ac)·X + (−4a²b − 48bc)`
* `sResP₀ = −4a³b² + 16a⁴c − 27b⁴ + 144ab²c − 128a²c² + 256c³`

The constant term `sResP₀ = Res(P, P')` is the **discriminant** of the depressed quartic.  The
subresultant coefficients are `s₀ = sResP₀`, `s₁ = −8a³ − 36b² + 32ac`, `s₂ = −8a`, `s₃ = 4`,
`s₄ = 1`.

The second part of the example takes `P = X⁴ + bX + c` (the `a = 0` specialization).  Now `sResP₂`
loses its `X²` term and has degree `1`, so index `2` becomes **defective**: `s₂ = 0` even though
`sResP₂ = −12bX − 16c ≠ 0` (recall `s_j` is the `X^j`-coefficient of `sResP_j`, which vanishes when
the subresultant drops degree).  Here `sResP₀ = −27b⁴ + 256c³` is the discriminant of `X⁴ + bX + c`.

Coefficients are parsed/printed with the named variables `a, b, c` via `AbcVar 3`.
-/

namespace Azurite.BPR.Chapter8.Example_8_53

open Azurite.AzPolynomial Azurite.AzMvPolynomial

/-- The coefficient ring `ℤ[a, b, c]`. -/
abbrev MvInt3 := AzMvPolynomial 3 AzInt .Degrevlex

instance : Fact (3 ≤ 26) := ⟨by omega⟩

/-! ### First part: the depressed quartic `P = X⁴ + a·X² + b·X + c` -/

/-- The depressed quartic `P = X⁴ + a·X² + b·X + c`, with the coefficient variables named
    `a, b, c` (`AbcVar 3`). -/
def P : AzPolynomial MvInt3 :=
  (parseStrMvCoeffWith (AbcVar 3) (n := 3) (R := AzInt) (ord := .Degrevlex)
    "x^4+(a)*x^2+(b)*x+(c)").getD 0

/-- The signed subresultant sequence `(sResP₀, …, sResP₄)` together with the subresultant
    coefficients `(s₀, …, s₄)` of `P` and `P'` (Algorithm 8.21). -/
def sres : Array (AzPolynomial MvInt3) × Array MvInt3 := signedSubresultant P P.derivative

-- The signed subresultant polynomials `sResP₀, …, sResP₄ ∈ ℤ[a, b, c][X]`.
#guard sres.1.toList.map (·.toStrMvCoeffWith (AbcVar 3)) ==
  ["(-4*a^3*b^2+16*a^4*c-27*b^4+144*a*b^2*c-128*a^2*c^2+256*c^3)",
   "(-8*a^3-36*b^2+32*a*c)*x+(-4*a^2*b-48*b*c)",
   "(-8*a)*x^2+(-12*b)*x+(-16*c)",
   "(4)*x^3+(2*a)*x+(b)",
   "x^4+(a)*x^2+(b)*x+(c)"]

-- The subresultant coefficients `s₀, …, s₄ ∈ ℤ[a, b, c]`; `s₀` is the quartic's discriminant.
#guard sres.2.toList.map (·.toStrWith (AbcVar 3)) ==
  ["-4*a^3*b^2+16*a^4*c-27*b^4+144*a*b^2*c-128*a^2*c^2+256*c^3",
   "-8*a^3-36*b^2+32*a*c", "-8*a", "4", "1"]

/-! ### Second part: `P = X⁴ + b·X + c` (the `a = 0` case — defective at index 2) -/

/-- `P = X⁴ + b·X + c`: the depressed quartic with `a = 0`. -/
def P2 : AzPolynomial MvInt3 :=
  (parseStrMvCoeffWith (AbcVar 3) (n := 3) (R := AzInt) (ord := .Degrevlex)
    "x^4+(b)*x+(c)").getD 0

/-- Its signed subresultant sequence `(sResP₀, …, sResP₄)` and coefficients `(s₀, …, s₄)`. -/
def sres2 : Array (AzPolynomial MvInt3) × Array MvInt3 := signedSubresultant P2 P2.derivative

-- The signed subresultant polynomials.  `sResP₂ = −12b·X − 16c` has degree `1`: index `2` is
-- defective (the `X²` coefficient is gone), so `sResP₂` is *not* a degree-`2` polynomial.
#guard sres2.1.toList.map (·.toStrMvCoeffWith (AbcVar 3)) ==
  ["(-27*b^4+256*c^3)", "(-36*b^2)*x+(-48*b*c)", "(-12*b)*x+(-16*c)", "(4)*x^3+(b)",
   "x^4+(b)*x+(c)"]

-- The subresultant coefficients.  `s₂ = 0` (defective: the `X²`-coefficient of `sResP₂` is `0`,
-- even though `sResP₂ ≠ 0`), and `s₀ = −27b⁴ + 256c³` is the discriminant of `X⁴ + bX + c`.
#guard sres2.2.toList.map (·.toStrWith (AbcVar 3)) ==
  ["-27*b^4+256*c^3", "-36*b^2", "0", "4", "1"]

end Azurite.BPR.Chapter8.Example_8_53
