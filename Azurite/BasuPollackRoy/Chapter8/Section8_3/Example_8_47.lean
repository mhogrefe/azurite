/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.SignedSubresultant
import Azurite.AzPolynomial.ToString

/-!
# BPR Example 8.47: subresultant coefficients of Example 8.25's `P, P'`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, Springer 2006, §8.3.4
> (the worked example just before Proposition 8.48).

The signed subresultant coefficients `s_j = sRes_j(P, P')` for `j = 0, …, 13`, where `P` is the
degree-`13` polynomial of Example 8.25

`P = 9X¹³ − 18X¹¹ − 33X¹⁰ + 102X⁸ + 7X⁷ − 36X⁶ − 122X⁵ + 49X⁴ + 93X³ − 42X² − 18X + 9`

and `P' = P.derivative`, computed over `AzInt` by `signedSubresultant` (Algorithm 8.21).

`P` is *not* squarefree: `gcd(P, P')` has degree `5`, so the subresultant coefficients vanish below
that degree — `s_0 = ⋯ = s_4 = 0` (in particular `Res(P, P') = ±s_0 = 0`) — while `s_5, …, s_{13}`
are nonzero.  The sequence is non-defective: each `sResP_j` (`5 ≤ j ≤ 13`) has degree exactly `j`,
so `s_j` is its leading coefficient.  Their rapid growth (`s_{13} = 9`, …, `s_5 ≈ 1.65·10²⁰`) is
the phenomenon bounded by Proposition 8.48.

BPR's Example 8.47 tabulates the subresultant coefficients only for `j` from `p − 2 = 11` down to
`5` (`37908, −72098829, …, −165117711302736225120`), "the remaining subresultants being `0`".  The
full output array here additionally carries the two top entries `s_{13} = lcof P = 9` and
`s_{12} = lcof P' = 117`: by convention `sResP_p = P` and `sResP_{p-1} = P'` are the inputs
themselves (visible as `sres.1[13] = P`, `sres.1[12] = P'`), not computed subresultants, so BPR
does not list them.
-/

namespace Azurite.BPR.Chapter8.Example_8_47

open Azurite.AzPolynomial

/-- The example polynomial `P` of Example 8.25, over the integers. -/
def P : AzPolynomial AzInt :=
  (parseAzPolynomial (R := AzInt)
    "9*x^13-18*x^11-33*x^10+102*x^8+7*x^7-36*x^6-122*x^5+49*x^4+93*x^3-42*x^2-18*x+9").get!

/-- Its derivative `P'`. -/
def P' : AzPolynomial AzInt := P.derivative

/-- The signed subresultant sequence `(sResP₀, …, sResP₁₃)` together with the subresultant
    coefficients `(s₀, …, s₁₃)` of `P` and `P'` (Algorithm 8.21). -/
def sres : Array (AzPolynomial AzInt) × Array AzInt := signedSubresultant P P'

-- The subresultant coefficients `s₀, …, s₁₃`.  They vanish for `j < 5` (below `deg gcd(P, P') = 5`)
-- and grow rapidly above it; `s₁₃ = 9 = lcof P`, `s₁₂ = 117 = lcof P'`.
#guard sres.2.toList.map toString ==
  ["0", "0", "0", "0", "0", "-165117711302736225120", "-151645911413926622112",
   "-2181968897553243072", "-1663522740400320", "-666229317948", "-72098829", "37908", "117", "9"]

end Azurite.BPR.Chapter8.Example_8_47
