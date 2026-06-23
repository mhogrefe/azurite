import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Parse

/-!
# Truncation of `AzPolynomial`

`truncate i p` returns the polynomial obtained from `p` by dropping
all coefficients of degree `> i`. Concretely, it keeps only the first
`i + 1` entries of `p.coeffs` and renormalizes — the new final entry
may be zero, so renormalization is needed to restore the trailing-nonzero
invariant.

This implements BPR's Notation 1.16: for `Q = b_q X^q + ⋯ + b_0 ∈ R[X]`,

  Tru_i(Q) = b_i X^i + ⋯ + b_0.

The definition extends to all `i : ℕ`; when `i ≥ natDegree p` the result
is simply `p`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- BPR's **truncation** `Tru_i(p)` (Notation 1.16): for
`p = b_q X^q + ⋯ + b_0`, the polynomial obtained by dropping every
term of degree `> i`, i.e. `Tru_i(p) = b_i X^i + ⋯ + b_0`.

Implemented by taking the first `i + 1` entries of `p.coeffs` and
renormalizing. When `i ≥ natDegree p` the result equals `p`. -/
def truncate (i : ℕ) (p : AzPolynomial R) : AzPolynomial R :=
  normalize (p.coeffs.extract 0 (i + 1))

@[simp] lemma truncate_zero_poly (i : ℕ) :
    truncate i (0 : AzPolynomial R) = 0 := by
  apply AzPolynomial.ext
  unfold truncate normalize
  simp

/-- The `natDegree` of a truncation is at most `i`. -/
theorem natDegree_truncate_le (i : ℕ) (p : AzPolynomial R) :
    (truncate i p).natDegree ≤ i := by
  unfold truncate natDegree
  set a := p.coeffs.extract 0 (i + 1)
  -- normalize drops trailing zeros via popWhile, which is a suffix of the
  -- reverse → prefix of the original, so size can only shrink.
  have h_norm : (normalize a).coeffs.size ≤ a.size := by
    change (a.popWhile (· = 0)).size ≤ a.size
    rw [← Array.length_toList, ← Array.length_toList,
        toList_popWhile_eq_dropTrailingZeros]
    exact (dropTrailingZeros_prefix _).length_le
  have h_ext : a.size ≤ i + 1 := by
    simp [a, Array.size_extract]
  omega

/-! ### Tests -/

section Tests

-- Basic truncation: drop terms of degree > 2 from `x^5 - x^3 + 2x + 1`
#guard truncate 2 (parseAzPolynomial (R := AzInt) "x^5-x^3+2*x+1").get!
  == (parseAzPolynomial (R := AzInt) "2*x+1").get!

-- Truncating at `i ≥ natDegree` is a no-op.
#guard truncate 10 (parseAzPolynomial (R := AzInt) "x^3-x+1").get!
  == (parseAzPolynomial (R := AzInt) "x^3-x+1").get!

-- Truncating at `i = natDegree` is a no-op.
#guard truncate 3 (parseAzPolynomial (R := AzInt) "x^3+x^2+x+1").get!
  == (parseAzPolynomial (R := AzInt) "x^3+x^2+x+1").get!

-- Truncating the zero polynomial yields zero.
#guard truncate 5 (0 : AzPolynomial AzInt) == (0 : AzPolynomial AzInt)

-- Renormalization test: `x^4 - x^3` truncated at 3 is `-x^3`.
#guard truncate 3 (parseAzPolynomial (R := AzInt) "x^4-x^3").get!
  == (parseAzPolynomial (R := AzInt) "-x^3").get!

-- Renormalization test: `x^4 - x^3` truncated at 2 is `0`
-- (since `b_0 = b_1 = b_2 = 0`, the leading monomial is dropped entirely).
#guard truncate 2 (parseAzPolynomial (R := AzInt) "x^4-x^3").get!
  == (0 : AzPolynomial AzInt)

-- Truncating at 0 keeps only the constant term.
#guard truncate 0 (parseAzPolynomial (R := AzInt) "x^3+x^2+x+7").get!
  == (parseAzPolynomial (R := AzInt) "7").get!

end Tests

end Azurite.AzPolynomial
