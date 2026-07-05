/-
Copyright (c) 2025 Azurite contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Parse

/-! # BPR Algorithm 8.10 — Special Translation

Given `P(X) = aₚXᵖ + ⋯ + a₀ ∈ R[X]` over a commutative ring `R` and `b, c ∈ R`,
compute the polynomial `cᵖ P(X − b/c)` **without leaving the ring `R[X]`** — the
motivating case being `R = ℤ` with `b/c ∈ ℚ`, where the result has the roots of
`P` shifted by the rational `b/c` while the coefficients stay integral.

The algorithm performs a Horner‑style accumulation with the linear polynomial
`cX − b`, keeping a running power‑of‑`c` factor `d`:

```
Initialise: result ← 0, d ← 1.
For each coefficient a (from leading to constant, i.e. `foldr` order):
  result ← C(a·d) + result · (cX − b)
  d      ← d · c
Output result.
```

## Main definitions

* `AzPolynomial.cXSubB b c` — the polynomial `cX − b`, built directly from `#[-b, c]`.
* `AzPolynomial.specialTranslate p b c` — computes `cᵖ P(X − b/c)`.

## References

* Basu, Pollack, Roy – *Algorithms in Real Algebraic Geometry*, Algorithm 8.10.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- The polynomial `c·X − b`, constructed from the coefficient array `#[-b, c]`. -/
def cXSubB (b c : R) : AzPolynomial R :=
  if h : c = 0 then
    if h2 : b = 0 then 0
    else ⟨#[-b], by simp [h2]⟩
  else ⟨#[-b, c], by simp [h]⟩

/-- **BPR Algorithm 8.10 (Special Translation).**

Given `P ∈ R[X]` and `b, c ∈ R`, produces the polynomial
`c^{deg P} · P(X − b/c)` using Horner's method with the
linear polynomial `cX − b`, keeping all intermediate results
in `R[X]` (no division needed).

When `c` is invertible (e.g. in `ℚ` or `ℝ`), evaluating the result at
`z` gives `c^p · P(z − b/c)`. -/
def specialTranslate [AzPolynomialMulConfig R] (p : AzPolynomial R) (b c : R) : AzPolynomial R :=
  let cxb := cXSubB b c
  (p.coeffs.foldr (init := ((0 : AzPolynomial R), (1 : R)))
    (fun a ⟨acc, d⟩ => (AzPolynomial.C (a * d) + acc * cxb, d * c))).1

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- (x² + 1) shifted by 1/2: 2²·((x−1/2)² + 1) = 4x² − 4x + 5
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2+1").get!.specialTranslate 1 2)
    == "4*x^2-4*x+5"

-- (2x − 3) shifted by −1/2: 2·(2(x+1/2) − 3) = 4x − 4
#guard toChars ((parseAzPolynomial (R := AzInt) "2*x-3").get!.specialTranslate (-1) 2)
    == "4*x-4"

-- c = 1 degenerates to plain translation: (x² + 1) shifted by 1 is x² − 2x + 2
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2+1").get!.specialTranslate 1 1)
    == "x^2-2*x+2"

-- Constant: c⁰·P = P
#guard toChars ((parseAzPolynomial (R := AzInt) "5").get!.specialTranslate 1 2)
    == "5"

-- Zero polynomial: zero
#guard toChars ((0 : AzPolynomial AzInt).specialTranslate 3 2) == "0"

end Tests

end Azurite.AzPolynomial
