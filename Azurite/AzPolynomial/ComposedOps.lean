import Azurite.AzPolynomial.Resultant
import Azurite.AzPolynomial.Translate
import Azurite.AzPolynomial.NegateRoots
import Azurite.AzPolynomial.ScaleRoots
import Azurite.AzPolynomial.InvertRoots
import Azurite.AzPolynomial.Equiv.ExactDiv
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.AzPolynomial.Parse

/-!
# Composed Sum and Composed Product

The binary root operations: for `P, Q ∈ R[x]` with roots `α` (of `P`) and `β`
(of `Q`), `composedSum P Q` has roots `α + β` and `composedProduct P Q` has
roots `α · β` (over each pair, with multiplicity; for the product, roots of `Q`
at `0` are dropped). These are the classical *composed sum* and *composed
product*, computed as univariate resultants over the polynomial coefficient
ring `AzPolynomial R` itself:

* `composedSum P Q = Res_y(P(y), Q(x − y))`,
* `composedProduct P Q = Res_y(P(y), y^m · Q(x / y))` where `m = deg Q`.

The companion operations `composedDifference` (roots `α − β`) and
`composedQuotient` (roots `α / β`, encoded fraction-free as `α = x · β`) are
*fusions* of the obvious compositions, each one coefficient pass cheaper:

* `composedDifference P Q = Res_y(P(y), Q(y − x))` — equals
  `composedSum P (negateRoots Q)`, but the negation cancels into the
  translation, so no `negateRoots` pass is needed;
* `composedQuotient P Q = Res_y(P(y), x^m · Q(y / x))` — equals
  `composedProduct P (invertRoots Q)` where defined, but the two coefficient
  reversals cancel, so neither `invertRoots` pass is performed (and no
  normalization strip occurs: the leading `y`-coefficient is `b_m`).
  When `P(0) = 0` and `Q(0) = 0` (the indeterminate `0 / 0`), the result is
  the zero polynomial.

All four bivariate arguments are built from the unary root-manipulation
toolkit over the coefficient ring `R[x]`: writing `P ↦ P(y)` for the
coefficient embedding `map CRingHom`,

* `Q(x − y)` is `(negateRoots (Q(y))).translate X` — negate the roots of
  `Q(y)`, then shift them by the constant-in-`y` element `x`;
* `Q(y − x)` is `(Q(y)).translate X` — just the shift;
* `y^m · Q(x / y)` is `scaleRoots (invertRoots (Q(y))) X 1` — invert the roots
  of `Q(y)`, then scale them by `x`;
* `x^m · Q(y / x)` is `scaleRoots (Q(y)) X 1` — just the scaling.

The resultant runs fraction-free over `R[x]` via the signed subresultant
algorithm, using the `ExactDiv (AzPolynomial R)` instance (which requires `R`
to be an integral domain with exact division — concretely `AzInt`).

**Application:** if `P, Q ∈ ℤ[x]` are defining polynomials of algebraic numbers
`α` and `β`, then `composedSum P Q` and `composedProduct P Q` are defining
polynomials of `α + β` and `α · β`; combined with `negateRoots` and
`invertRoots` this yields `α − β` and `α / β` as well.

## Main definitions

- `AzPolynomial.CRingHom` — `C` bundled as a ring hom `R →+* AzPolynomial R`
- `AzPolynomial.composedSum p q` — roots `α + β`
- `AzPolynomial.composedProduct p q` — roots `α · β`
- `AzPolynomial.composedDifference p q` — roots `α − β`
- `AzPolynomial.composedQuotient p q` — roots `α / β`
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- The constant-polynomial embedding `C`, bundled as a ring homomorphism
`R →+* AzPolynomial R`. Used to view `P ∈ R[x]` as a polynomial in a new
variable `y` with coefficients in `R[x]`, via `map CRingHom`. -/
def CRingHom : R →+* AzPolynomial R where
  toFun := C
  map_one' := toPoly_inj.mp (by rw [toPoly_C, toPoly_one, Polynomial.C_1])
  map_mul' a b := toPoly_inj.mp (by
    rw [toPoly_C, toPoly_mul, toPoly_C, toPoly_C, Polynomial.C_mul])
  map_zero' := toPoly_inj.mp (by rw [toPoly_C, toPoly_zero, Polynomial.C_0])
  map_add' a b := toPoly_inj.mp (by
    rw [toPoly_C, toPoly_add, toPoly_C, toPoly_C, Polynomial.C_add])

@[simp] theorem CRingHom_apply (c : R) : CRingHom c = C c := rfl

variable [IsDomain R] [Azurite.ExactDiv R]

/-- **Composed sum.** The roots of `composedSum P Q` are the pairwise sums
`α + β` of the roots of `P` and `Q` (with multiplicity), computed as the
resultant `Res_y(P(y), Q(x − y))` over the coefficient ring `R[x]`. -/
def composedSum (P Q : AzPolynomial R) : AzPolynomial R :=
  resultant (P.map CRingHom) ((negateRoots (Q.map CRingHom)).translate X)

/-- **Composed product.** The roots of `composedProduct P Q` are the pairwise
products `α · β` of the roots of `P` and the *nonzero* roots of `Q` (with
multiplicity; roots of `Q` at `0` are dropped by the inversion), computed as
the resultant `Res_y(P(y), y^m · Q(x/y))` over the coefficient ring `R[x]`. -/
def composedProduct (P Q : AzPolynomial R) : AzPolynomial R :=
  resultant (P.map CRingHom) (scaleRoots (invertRoots (Q.map CRingHom)) X 1)

/-- **Composed difference.** The roots of `composedDifference P Q` are the
pairwise differences `α − β` (with multiplicity), computed as the resultant
`Res_y(P(y), Q(y − x))`. Fused form of `composedSum P (negateRoots Q)`: the
negation cancels into the translation, saving a coefficient pass. -/
def composedDifference (P Q : AzPolynomial R) : AzPolynomial R :=
  resultant (P.map CRingHom) ((Q.map CRingHom).translate X)

/-- **Composed quotient.** The roots of `composedQuotient P Q` are the pairwise
quotients `α / β` for nonzero roots `β` of `Q` (with multiplicity; encoded
fraction-free: `z` is a root iff `α = z · β` for some root pair), computed as
the resultant `Res_y(P(y), x^m · Q(y/x))`. Fused form of
`composedProduct P (invertRoots Q)`: the two coefficient reversals cancel, so
no inversion pass is performed. If both `P` and `Q` have `0` as a root (the
indeterminate `0 / 0`), the result is the zero polynomial. -/
def composedQuotient (P Q : AzPolynomial R) : AzPolynomial R :=
  resultant (P.map CRingHom) (scaleRoots (Q.map CRingHom) X 1)

/-- **Coefficient elimination.** Given defining polynomials `Ps = [P₀, …, Pₙ]`
(little-endian, like a coefficient array: `Pᵢ` has the coefficient `cᵢ` among
its roots), returns a polynomial over `R` whose roots form a **superset** of
the roots of `F = ∑ cᵢ xⁱ` — for *every* choice of roots `cᵢ`, so the output
covers all conjugate variants of `F` at once. This reduces root-finding for
polynomials with algebraic coefficients to root-finding over `R` (plus root
selection).

Computed as an iterated resultant cascade in Horner order, with a bivariate
accumulator `A ∈ R[x][y]` whose `y`-roots track the possible Horner values
`cₖ + x(cₖ₊₁ + x(⋯ cₙ))`: each step scales the accumulated roots by `x`
(`scaleRoots A X 1`) and composed-sums with the next coefficient's defining
polynomial — `composedSum` instantiated at the coefficient ring
`AzPolynomial R` itself, running fraction-free through the nested `ExactDiv`
instance. A root `z` of `F` makes the Horner value `0`, so the answer is the
constant `y`-coefficient of the final accumulator.

Degenerate cases are honest: an empty list means `F = 0` (every `z` is a
root), and a `P₀` vanishing at `0` allows `c₀ = 0`; when every `z` must be
covered the output is the zero polynomial. -/
def eliminateCoeffs (Ps : List (AzPolynomial R)) : AzPolynomial R :=
  match Ps.reverse with
  | [] => 0
  | Pn :: rest =>
    (rest.foldl (fun A Pk => composedSum (Pk.map CRingHom) (scaleRoots A X 1))
      (Pn.map CRingHom)).coeff 0

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def pp (s : String) : AzPolynomial AzInt := (parseAzPolynomial s).get!

-- 2 + 3 = 5
#guard composedSum (pp "x-2") (pp "x-3") == pp "x-5"

-- √2 + √3: the classic x⁴ − 10x² + 1
#guard composedSum (pp "x^2-2") (pp "x^2-3") == pp "x^4-10*x^2+1"

-- ±√2 + 1: x² − 2x − 1
#guard composedSum (pp "x^2-2") (pp "x-1") == pp "x^2-2*x-1"

-- golden ratio pairs: φ+φ = 1+√5, φ+ψ = 1 (twice), ψ+ψ = 1−√5:
-- (x − 1)² (x² − 2x − 4)
#guard composedSum (pp "x^2-x-1") (pp "x^2-x-1") == pp "x^4-4*x^3+x^2+6*x-4"

-- ±i + ±i: {2i, 0, 0, −2i}: x² (x² + 4)
#guard composedSum (pp "x^2+1") (pp "x^2+1") == pp "x^4+4*x^2"

-- 2 · 3 = 6
#guard composedProduct (pp "x-2") (pp "x-3") == pp "x-6"

-- √2 · √3 pairs: ±√6 twice: (x² − 6)²
#guard composedProduct (pp "x^2-2") (pp "x^2-3") == pp "x^4-12*x^2+36"

-- ±√2 · 3: x² − 18
#guard composedProduct (pp "x^2-2") (pp "x-3") == pp "x^2-18"

-- ±i · ±i: {−1, 1, 1, −1}: (x² − 1)²
#guard composedProduct (pp "x^2+1") (pp "x^2+1") == pp "x^4-2*x^2+1"

-- Q with a root at 0: x(x − 1) — the 0 root is dropped, 2·1 = 2 survives
#guard composedProduct (pp "x-2") (pp "x^2-x") == pp "x-2"

-- 5 − 3 = 2 (sign of the output is not normalized)
#guard composedDifference (pp "x-5") (pp "x-3") == pp "-x+2"

-- ±√2 ∓ √3: same quartic as the sum, by symmetry
#guard composedDifference (pp "x^2-2") (pp "x^2-3") == pp "x^4-10*x^2+1"

-- self-difference: {0, 0, ±2√2}: x²(x²−8)
#guard composedDifference (pp "x^2-2") (pp "x^2-2") == pp "x^4-8*x^2"

-- φ − 1 = 1/φ and ψ − 1: x² + x − 1
#guard composedDifference (pp "x^2-x-1") (pp "x-1") == pp "x^2+x-1"

-- fusion agrees with the composition
#guard composedDifference (pp "x^2-x-1") (pp "x^2-3")
    == composedSum (pp "x^2-x-1") ((pp "x^2-3").negateRoots)

-- 6 / 3 = 2 (output scaled by coefficients of Q)
#guard composedQuotient (pp "x-6") (pp "x-3") == pp "-3*x+6"

-- ±3√2 / 3 = ±√2: 9(x² − 2)
#guard composedQuotient (pp "x^2-18") (pp "x-3") == pp "9*x^2-18"

-- ±√2 / ±√3 = ±√(2/3), each twice: (3x² − 2)²
#guard composedQuotient (pp "x^2-2") (pp "x^2-3") == pp "9*x^4-12*x^2+4"

-- self-quotient: {1, 1, −1, −1}: 4(x² − 1)²
#guard composedQuotient (pp "x^2-2") (pp "x^2-2") == pp "4*x^4-8*x^2+4"

-- Q with a root at 0 but P(0) ≠ 0: the 0 root contributes nothing
#guard composedQuotient (pp "x-2") (pp "x^2-x") == pp "-2*x+4"

-- indeterminate 0 / 0: both vanish at 0, so the resultant is identically zero
#guard composedQuotient (pp "x^2-x") (pp "x^2-x") == 0

-- fusion agrees with the composition
#guard composedQuotient (pp "x^2-x-1") (pp "x^2-3")
    == composedProduct (pp "x^2-x-1") ((pp "x^2-3").invertRoots)

-- eliminateCoeffs: rational coefficients recover the polynomial (up to sign):
-- F = x − 2 via c₀ = −2, c₁ = 1
#guard eliminateCoeffs [pp "x+2", pp "x-1"] == pp "-x+2"

-- F = x ∓ √2: both conjugate choices: x² − 2
#guard eliminateCoeffs [pp "x^2-2", pp "x-1"] == pp "x^2-2"

-- F = x² ∓ √2: the fourth root of 2: (x²−√2)(x²+√2) = x⁴ − 2
#guard eliminateCoeffs [pp "x^2-2", pp "x", pp "x-1"] == pp "x^4-2"

-- F = ±√2·x ± √2: roots ∓1 over the four sign choices: 4(x²−1)²
#guard eliminateCoeffs [pp "x^2-2", pp "x^2-2"] == pp "4*x^4-8*x^2+4"

-- F = x + c₀ with c₀² + c₀ − 1 = 0: roots are the golden-ratio pair
#guard eliminateCoeffs [pp "x^2+x-1", pp "x-1"] == pp "x^2-x-1"

-- two algebraic coefficients: F = x² ± √2·x ± √3, all four conjugates (degree 8)
#guard eliminateCoeffs [pp "x^2-3", pp "x^2-2", pp "x-1"]
    == pp "x^8-4*x^6-2*x^4-12*x^2+9"

-- degenerate: c₀ may be 0 and F is the constant c₀ — every z must be covered
#guard eliminateCoeffs [pp "x"] == 0

-- nonzero constant F = −5: no roots, and the output is a root-free constant
#guard eliminateCoeffs [pp "x-5"] == pp "-5"

-- empty list: F = 0 identically
#guard eliminateCoeffs ([] : List (AzPolynomial AzInt)) == 0

end Tests

end Azurite.AzPolynomial
