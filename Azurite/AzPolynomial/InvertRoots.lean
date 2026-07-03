import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Parse

/-!
# Root Inversion

Computes the reversal `X^(deg P) · P(1/X)` of `P ∈ R[X]` — the coefficient
sequence reversed. The roots of the result are the reciprocals `1/r` of the
*nonzero* roots `r` of `P`; roots at `0` are dropped (they correspond to the
vanished leading coefficients of the reversal, stripped by `normalize`), and the
degree drops by exactly the multiplicity of `0` as a root. When `P(0) ≠ 0` the
degree is preserved and the operation is an involution.

Implemented as an O(n) array reversal followed by `normalize`.

## Main definitions

- `AzPolynomial.invertRoots p` — computes `X^(deg P) · P(1/X)`

The coefficient formulas are proved here; the `toPoly` bridge (to Mathlib's
`Polynomial.reverse`), the root-inversion property, and the degree data live in
`Equiv/InvertRoots.lean`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- **Root inversion.** Reverses the coefficients, computing
`X^(deg P) · P(1/X)`: the roots of the result are the reciprocals of the
nonzero roots of `P`. -/
def invertRoots (p : AzPolynomial R) : AzPolynomial R :=
  normalize p.coeffs.reverse

/-- Within the degree range, the coefficients are reversed:
`(invertRoots p).coeff i = p.coeff (deg P − i)` for `i ≤ deg P`. -/
theorem coeff_invertRoots (p : AzPolynomial R) {i : ℕ} (hi : i ≤ p.natDegree) :
    (p.invertRoots).coeff i = p.coeff (p.natDegree - i) := by
  rw [invertRoots, coeff_normalize]
  rcases Nat.eq_zero_or_pos p.coeffs.size with hsz | hsz
  · rw [Array.getElem?_eq_none (by rw [Array.size_reverse]; omega)]
    show (0 : R) = p.coeff (p.natDegree - i)
    rw [show p.coeff (p.natDegree - i) = (p.coeffs[p.natDegree - i]?).getD 0 from rfl,
      Array.getElem?_eq_none (by omega)]
    rfl
  · have hi' : i < p.coeffs.size := by
      have : p.natDegree = p.coeffs.size - 1 := rfl
      omega
    rw [Array.getElem?_reverse hi']
    rfl

/-- The constant term of the reversal is the leading coefficient. -/
@[simp] theorem coeff_invertRoots_zero (p : AzPolynomial R) :
    (p.invertRoots).coeff 0 = p.leadingCoeff := by
  rw [coeff_invertRoots p (Nat.zero_le _), Nat.sub_zero]
  rfl

@[simp] theorem invertRoots_zero : (0 : AzPolynomial R).invertRoots = 0 := by
  apply AzPolynomial.ext
  show (normalize _).coeffs = #[]
  simp [coeffs_zero, normalize]

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- (x−1)(x−2) = x² − 3x + 2 with roots 1, 2 becomes 2x² − 3x + 1 (roots 1, 1/2)
#guard (parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!.invertRoots
    == (parseAzPolynomial (R := AzInt) "2*x^2-3*x+1").get!

-- x(x−1): the root 0 is dropped, only 1/1 remains: −x + 1
#guard (parseAzPolynomial (R := AzInt) "x^2-x").get!.invertRoots
    == (parseAzPolynomial (R := AzInt) "-x+1").get!

-- x³: all roots at 0, everything drops: the constant 1
#guard (parseAzPolynomial (R := AzInt) "x^3").get!.invertRoots
    == (parseAzPolynomial (R := AzInt) "1").get!

-- Constants unchanged
#guard (parseAzPolynomial (R := AzInt) "7").get!.invertRoots
    == (parseAzPolynomial (R := AzInt) "7").get!

-- Zero unchanged
#guard (0 : AzPolynomial AzInt).invertRoots == 0

-- Involution when the constant term is nonzero
#guard (parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!.invertRoots.invertRoots
    == (parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!

end Tests

end Azurite.AzPolynomial
