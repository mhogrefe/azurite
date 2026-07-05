import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse

/-!
# Multiplication by a power of `X`

`mulXPow n p` computes `p * X^n` by prepending `n` zero coefficients to
`p.coeffs`. This is O(n + p.coeffs.size) and allocates a single output
array, which is significantly cheaper than invoking the general
`AzPolynomial` multiplication against a monomial polynomial.

The zero polynomial maps to itself (zero), and the leading coefficient
is preserved, so the `last_ne_zero` invariant is maintained without
renormalization.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R]

/-- `mulXPow n p` computes `p * X^n`, equivalently shifting every
coefficient of `p` up by `n` positions.

Implemented by prepending `n` zeros to `p.coeffs`. The leading
coefficient is preserved, so no renormalization is needed. -/
def mulXPow (n : ℕ) (p : AzPolynomial R) : AzPolynomial R :=
  if hp : p.coeffs.size = 0 then p
  else
    ⟨Array.replicate n 0 ++ p.coeffs, by
      intro h
      apply p.last_ne_zero
      -- `back?` of `xs ++ ys` equals `ys.back?.or xs.back?`.
      rw [Array.back?_append] at h
      -- `p.coeffs` is nonempty so its `back?` is `some`, hence `.or` picks it.
      have hb : ∃ r, p.coeffs.back? = some r := by
        rcases hb : p.coeffs.back? with _ | r
        · exact absurd ((Array.back?_eq_none_iff).mp hb ▸ rfl : p.coeffs.size = 0) hp
        · exact ⟨r, rfl⟩
      obtain ⟨r, hr⟩ := hb
      rw [hr] at h ⊢
      simpa using h⟩

@[simp] lemma mulXPow_zero (p : AzPolynomial R) : mulXPow 0 p = p := by
  unfold mulXPow
  split
  · next h =>
    rfl
  · next h =>
    apply AzPolynomial.ext
    simp

@[simp] lemma mulXPow_zero_poly (n : ℕ) :
    mulXPow n (0 : AzPolynomial R) = 0 := by
  unfold mulXPow
  simp

lemma mulXPow_coeffs_size_of_ne_zero (n : ℕ) (p : AzPolynomial R)
    (hp : p.coeffs.size ≠ 0) :
    (mulXPow n p).coeffs.size = n + p.coeffs.size := by
  unfold mulXPow
  rw [dif_neg hp]
  simp

/-! ### Tests -/

section Tests
variable [DecidableEq R]

-- `(x + 1) * x = x^2 + x`
#guard toChars (mulXPow 1 (parseAzPolynomial (R := AzInt) "x+1").get!)
  == "x^2+x"

-- `(x^2 + 2*x + 3) * x^2 = x^4 + 2*x^3 + 3*x^2`
#guard toChars (mulXPow 2 (parseAzPolynomial (R := AzInt) "x^2+2*x+3").get!)
  == "x^4+2*x^3+3*x^2"

-- Shifting by 0 is a no-op.
#guard toChars (mulXPow 0 (parseAzPolynomial (R := AzInt) "x^3-5*x+7").get!)
  == "x^3-5*x+7"

-- Shifting the zero polynomial yields zero.
#guard toChars (mulXPow 5 (0 : AzPolynomial AzInt)) == "0"

-- Constant `7 * x^3 = 7*x^3`
#guard toChars (mulXPow 3 (parseAzPolynomial (R := AzInt) "7").get!)
  == "7*x^3"

end Tests

end Azurite.AzPolynomial
