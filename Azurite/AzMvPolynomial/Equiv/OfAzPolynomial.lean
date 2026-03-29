import Azurite.AzMvPolynomial.OfAzPolynomial
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Equivalence: toAzMvPolynomial ↔ Polynomial.eval₂ C (X v)

We prove that converting a univariate `AzPolynomial` to an `AzMvPolynomial`
via `toAzMvPolynomial v` agrees with Mathlib's embedding of a `Polynomial`
into `MvPolynomial` via `eval₂ C (X v)`.

```
toMvPoly (p.toAzMvPolynomial v) = Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X v) (toPoly p)
```
-/

namespace Azurite
open AzMvPolynomial MvPolynomial Polynomial MonomialOrder

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-! ### ofVarPow to Finsupp.single -/

theorem ofVarPow_toFinsupp (v : σ) (k : ℕ) :
    (MonicMonomial.ofVarPow v k : MonicMonomial σ ord).toFinsupp =
    Finsupp.single v k := by
  classical
  ext w
  simp only [MonicMonomial.toFinsupp, Finsupp.onFinset_apply,
    MonicMonomial.ofVarPow_exponent, Finsupp.single_apply]
  by_cases h : v = w
  · subst h; simp
  · have : Var.toFin v ≠ Var.toFin w := fun heq => h (Var.toFin_injective heq)
    simp [this, h]

/-! ### buildTermsDesc loop invariant -/

/-- Base case: when `idx = 0`, `buildTermsDesc` produces exactly one monomial term
    (or none if the coefficient is zero). -/
private theorem buildTermsDesc_base (v : σ) (coeffs : Array R)
    (acc : Array (Monomial σ R ord)) (fuel : ℕ) :
    ((buildTermsDesc v coeffs (fuel + 1) 0 acc).toList.map Monomial.toMvPoly).sum =
    (acc.toList.map Monomial.toMvPoly).sum +
    (MvPolynomial.monomial (Finsupp.single v 0)) ((coeffs[0]?).getD 0) := by
  classical
  change ((if hc : (coeffs[0]?).getD 0 = 0 then acc
    else acc.push ⟨⟨(coeffs[0]?).getD 0, hc⟩, MonicMonomial.ofVarPow v 0⟩).toList.map
    Monomial.toMvPoly).sum = _
  split
  · next hc => simp [hc]
  · next hc =>
    rw [Array.toList_push, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
    congr 1; unfold Monomial.toMvPoly; rw [ofVarPow_toFinsupp]

/-- Loop invariant: the sum of `Monomial.toMvPoly` over the output of
    `buildTermsDesc` equals the accumulator sum plus the polynomial sum
    `∑ i ∈ range (idx + 1), monomial (single v i) (coeffs[i])`. -/
theorem buildTermsDesc_toMvPoly_sum (v : σ) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (Monomial σ R ord))
    (hfuel : idx < fuel + 1) :
    ((buildTermsDesc v coeffs (fuel + 1) idx acc).toList.map Monomial.toMvPoly).sum =
    (acc.toList.map Monomial.toMvPoly).sum +
    ∑ i ∈ Finset.range (idx + 1),
      (MvPolynomial.monomial (Finsupp.single v i)) ((coeffs[i]?).getD 0) := by
  classical
  match fuel with
  | 0 =>
    have hidx : idx = 0 := by omega
    subst hidx
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
    exact buildTermsDesc_base v coeffs acc 0
  | fuel + 1 =>
    by_cases hidx : idx = 0
    · subst hidx
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      exact buildTermsDesc_base v coeffs acc (fuel + 1)
    · have hidx' : idx - 1 < fuel + 1 := by omega
      show ((buildTermsDesc v coeffs (fuel + 2) idx acc).toList.map Monomial.toMvPoly).sum = _
      unfold buildTermsDesc
      simp only [hidx, ↓reduceIte]
      split
      · next hc =>
        rw [buildTermsDesc_toMvPoly_sum v coeffs fuel (idx - 1) acc hidx']
        rw [show idx - 1 + 1 = idx from by omega, Finset.sum_range_succ]
        simp [hc]
      · next hc =>
        rw [buildTermsDesc_toMvPoly_sum v coeffs fuel (idx - 1)
            (acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow v idx⟩) hidx']
        rw [Array.toList_push, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton]
        rw [show idx - 1 + 1 = idx from by omega, Finset.sum_range_succ]
        conv_lhs =>
          rw [show Monomial.toMvPoly (⟨⟨_, hc⟩, MonicMonomial.ofVarPow v idx⟩ :
            Monomial σ R ord) =
            (MvPolynomial.monomial (Finsupp.single v idx)) ((coeffs[idx]?).getD 0) from by
            unfold Monomial.toMvPoly; rw [ofVarPow_toFinsupp]]
        ring

/-! ### Main equivalence -/

/-- Converting via `toAzMvPolynomial v` then `toMvPoly` equals
    embedding via `Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X v)`. -/
theorem toMvPoly_toAzMvPolynomial (v : σ)
    (p : AzPolynomial R) :
    toMvPoly (p.toAzMvPolynomial v (ord := ord)) =
    Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X v) (AzPolynomial.toPoly p) := by
  classical
  rw [AzMvPolynomial.toMvPoly_eq_list_sum, Polynomial.eval₂_eq_sum_range]
  simp only [AzPolynomial.toAzMvPolynomial]
  split
  · -- p.coeffs.size = 0 (zero polynomial)
    next h =>
    simp only [List.map_nil, List.sum_nil]
    have hnd : (AzPolynomial.toPoly p).natDegree = 0 := by
      rw [AzPolynomial.natDegree_toPoly]
      simp [Azurite.AzPolynomial.natDegree, h]
    rw [hnd, Finset.sum_range_one, pow_zero, mul_one]
    have : (AzPolynomial.toPoly p).coeff 0 = 0 := by
      rw [coeff_toPoly_eq]; simp [Azurite.AzPolynomial.coeff, h]
    rw [this, map_zero]
  · -- p.coeffs.size > 0
    next h =>
    -- Extract the terms array from the struct
    change ((buildTermsDesc v p.coeffs p.coeffs.size (p.coeffs.size - 1) #[]).toList.map
      Monomial.toMvPoly).sum = _
    -- Introduce m = size - 1 to avoid Nat subtraction issues
    set m := p.coeffs.size - 1 with hm_def
    have hm : m + 1 = p.coeffs.size := Nat.succ_pred (by omega)
    -- Rewrite fuel to (m + 1) matching buildTermsDesc_toMvPoly_sum signature
    rw [show p.coeffs.size = m + 1 from hm.symm]
    rw [buildTermsDesc_toMvPoly_sum v p.coeffs m m #[] (by omega)]
    simp only [List.map_nil, List.sum_nil, zero_add]
    -- Both sides sum over range(m+1) = range(size)
    rw [show (AzPolynomial.toPoly p).natDegree + 1 = m + 1 from by
      rw [AzPolynomial.natDegree_toPoly]
      unfold Azurite.AzPolynomial.natDegree; omega]
    congr 1; ext i
    rw [MvPolynomial.C_mul_X_pow_eq_monomial, coeff_toPoly_eq]
    simp only [Azurite.AzPolynomial.coeff]

end Azurite
