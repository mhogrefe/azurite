import Azurite.AzMvPolynomial.Pow
import Azurite.AzMvPolynomial.Equiv.Mul

/-!
# Equivalence: `AzMvPolynomial.pow` ↔ `MvPolynomial.pow`

Proves that `AzMvPolynomial.pow p k` (computable, with single-monomial
optimization and sliding-window exponentiation fallback) agrees with Mathlib's
`MvPolynomial` power.
-/

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-! ### Monomial-level `toFinsupp` / `toMvPoly` preservation of `pow` -/

/-- `toFinsupp` preserves `MonicMonomial.pow`:
    `toFinsupp (m.pow k) = k • toFinsupp m`. -/
theorem MonicMonomial.toFinsupp_pow (m : MonicMonomial n ord) (k : ℕ) :
    (m.pow k).toFinsupp = k • m.toFinsupp := by
  rw [MonicMonomial.pow_eq_npow]
  induction k with
  | zero =>
    simp only [pow_zero, zero_smul]
    show MonicMonomial.toFinsupp (1 : MonicMonomial n ord) = 0
    ext v
    simp [MonicMonomial.toFinsupp, Finsupp.onFinset_apply,
          MonicMonomial.one_exponents, Vector.getElem_replicate]
  | succ k ih => rw [pow_succ, MonicMonomial.toFinsupp_mul, ih, succ_nsmul]

omit [DecidableEq R] in
/-- `toMvPoly` preserves `Monomial.pow`:
    `(m.pow k).toMvPoly = m.toMvPoly ^ k`. -/
theorem Monomial.toMvPoly_pow (m : Monomial n R ord) (k : ℕ) :
    (m.pow k).toMvPoly = m.toMvPoly ^ k := by
  simp only [Monomial.toMvPoly, Monomial.pow, MonicMonomial.toFinsupp_pow,
             MvPolynomial.monomial_pow]

/-! ### AzMvPolynomial.pow equivalence -/

omit [DecidableEq R] in
/-- Exponentiating a single monomial and wrapping gives the correct `toMvPoly`. -/
private theorem toMvPoly_pow_monomial (m : Monomial n R ord) (k : ℕ) :
    (AzMvPolynomial.ofMonomial (Monomial.pow m k)).toMvPoly =
    (AzMvPolynomial.ofMonomial m).toMvPoly ^ k := by
  simp only [AzMvPolynomial.toMvPoly_eq_list_sum, AzMvPolynomial.ofMonomial,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact Monomial.toMvPoly_pow m k

omit [NoZeroDivisors R] [DecidableEq R] in
/-- For a single-term polynomial, `toMvPoly (ofMonomial p.terms[0]) = toMvPoly p`. -/
private theorem toMvPoly_ofMonomial_first (p : AzMvPolynomial n R ord)
    (h : p.terms.size = 1) :
    (AzMvPolynomial.ofMonomial (p.terms[0]'(by omega))).toMvPoly = p.toMvPoly := by
  simp only [AzMvPolynomial.toMvPoly_eq_list_sum, AzMvPolynomial.ofMonomial,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  symm
  have hterms : p.terms.toList = [p.terms[0]'(by omega)] := by
    apply List.ext_getElem
    · simp [h]
    · intro i hi1 hi2; simp at hi2; subst hi2; simp
  rw [hterms]; simp

/-- Forward direction: `toMvPoly` preserves `AzMvPolynomial.pow`. -/
@[simp] theorem toMvPoly_pow (p : AzMvPolynomial n R ord) (k : ℕ) :
    (AzMvPolynomial.pow p k).toMvPoly = p.toMvPoly ^ k := by
  unfold AzMvPolynomial.pow
  split
  · next h =>
    rw [toMvPoly_pow_monomial, toMvPoly_ofMonomial_first p h]
  · next _ =>
    show (Azurite.slidingWindowPow p k).toMvPoly = _
    exact Azurite.map_slidingWindowPow AzMvPolynomial.toMvPoly toMvPoly_one toMvPoly_mul p k

/-- Backward direction: `ofMvPoly` preserves `pow`. -/
@[simp] theorem ofMvPoly_pow (q : MvPolynomial (Fin n) R) (k : ℕ) :
    AzMvPolynomial.pow (AzMvPolynomial.ofMvPoly q : AzMvPolynomial n R ord) k =
    AzMvPolynomial.ofMvPoly (q ^ k) :=
  toMvPoly_injective
    (by rw [toMvPoly_pow, toMvPoly_ofMvPoly, toMvPoly_ofMvPoly])

end Azurite
