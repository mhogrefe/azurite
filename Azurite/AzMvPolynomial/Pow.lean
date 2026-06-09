/-
  Exponentiation for `MonicMonomial`, `Monomial`, `AzMvPolynomial`.
  Mathlib equivalences (toMvPoly_pow etc.) live in the Equiv layer.
-/
import Azurite.AzMvPolynomial.Mul
import Azurite.Algorithm.SlidingWindowPow

namespace Azurite.MonicMonomial

variable {n : ℕ} {ord : MonomialOrder}

/-- Computable exponentiation for monic monomials: scale each exponent by `k`. -/
def pow (m : MonicMonomial n ord) (k : ℕ) : MonicMonomial n ord :=
  ⟨Vector.ofFn (fun i => k * m.exponents[i])⟩

@[simp] theorem pow_exponents (m : MonicMonomial n ord) (k : ℕ) :
    (m.pow k).exponents = Vector.ofFn (fun i => k * m.exponents[i]) := rfl

/-- `pow` agrees with the `CommMonoid`'s `^` operator. -/
theorem pow_eq_npow (m : MonicMonomial n ord) (k : ℕ) : m.pow k = m ^ k := by
  induction k with
  | zero =>
    ext1; simp [_root_.pow_zero, one_exponents]
    ext i hi; simp [Vector.getElem_ofFn, Vector.getElem_replicate]
  | succ k ih =>
    rw [_root_.pow_succ, ← ih]
    ext1; ext i hi
    simp [pow_exponents, mul_exponents, Vector.getElem_ofFn]
    ring

end Azurite.MonicMonomial

namespace Azurite.Monomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R]
  {n : ℕ} {ord : MonomialOrder}

/-- Computable exponentiation for monomials: raise coefficient to `k`-th power,
    scale monic exponents by `k`. -/
def pow (m : Monomial n R ord) (k : ℕ) : Monomial n R ord :=
  ⟨⟨m.coeff.val ^ k, pow_ne_zero k m.coeff.property⟩, m.monic.pow k⟩

@[simp] theorem pow_coeff_val (m : Monomial n R ord) (k : ℕ) :
    (m.pow k).coeff.val = m.coeff.val ^ k := rfl

@[simp] theorem pow_monic (m : Monomial n R ord) (k : ℕ) :
    (m.pow k).monic = m.monic.pow k := rfl

end Azurite.Monomial

namespace Azurite.AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-- Computable exponentiation for multivariate polynomials.
    Single-term polynomials use direct monomial exponentiation; multi-term
    polynomials use `slidingWindowPow` (O(log k) multiplications). -/
def pow (p : AzMvPolynomial n R ord) (k : ℕ) : AzMvPolynomial n R ord :=
  if h : p.terms.size = 1 then
    AzMvPolynomial.ofMonomial ((p.terms[0]'(by omega)).pow k)
  else
    Azurite.slidingWindowPow p k

end Azurite.AzMvPolynomial
