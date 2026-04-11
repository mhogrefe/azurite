import Azurite.AzMvPolynomial.OfAzPolynomial
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Equivalence: `AzPolynomial.toAzMvPolynomial` ↔ `Polynomial.eval₂ C (X i)`

We prove that converting a univariate `AzPolynomial` to an `AzMvPolynomial`
via `toAzMvPolynomial i` agrees with Mathlib's embedding via `eval₂ C (X i)`.

```
toMvPoly (p.toAzMvPolynomial i) =
  Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) (toPoly p)
```
-/

namespace Azurite
open AzMvPolynomial MvPolynomial Polynomial MonomialOrder

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-! ### ofVarPow to Finsupp.single -/

theorem ofVarPow_toFinsupp (i : Fin n) (k : ℕ) :
    (MonicMonomial.ofVarPow i k : MonicMonomial n ord).toFinsupp =
    Finsupp.single i k := by
  classical
  ext w
  simp only [MonicMonomial.toFinsupp, Finsupp.onFinset_apply, Finsupp.single_apply,
    MonicMonomial.ofVarPow]
  by_cases h : i = w
  · subst h; simp
  · have h' : (i : Fin n) ≠ ⟨(w : Fin n).val, w.isLt⟩ := by
      intro heq; apply h; ext; exact Fin.val_eq_of_eq heq
    simp [h']

/-! ### buildTermsDesc loop invariant -/

/-- Base case: when `idx = 0`, `buildTermsDesc` produces exactly one monomial term
    (or none if the coefficient is zero). -/
private theorem buildTermsDesc_base (i : Fin n) (coeffs : Array R)
    (acc : Array (Monomial n R ord)) (fuel : ℕ) :
    ((buildTermsDesc i coeffs (fuel + 1) 0 acc).toList.map Monomial.toMvPoly).sum =
    (acc.toList.map Monomial.toMvPoly).sum +
    (MvPolynomial.monomial (Finsupp.single i 0)) ((coeffs[0]?).getD 0) := by
  classical
  change ((if hc : (coeffs[0]?).getD 0 = 0 then acc
    else acc.push ⟨⟨(coeffs[0]?).getD 0, hc⟩, MonicMonomial.ofVarPow i 0⟩).toList.map
    Monomial.toMvPoly).sum = _
  split
  · next hc => simp [hc]
  · next hc =>
    rw [Array.toList_push, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
    congr 1; unfold Monomial.toMvPoly; rw [ofVarPow_toFinsupp]

/-- Loop invariant: the sum of `Monomial.toMvPoly` over the output of
    `buildTermsDesc` equals the accumulator sum plus the polynomial sum
    `∑ k ∈ range (idx + 1), monomial (single i k) (coeffs[k])`. -/
theorem buildTermsDesc_toMvPoly_sum (i : Fin n) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (Monomial n R ord))
    (hfuel : idx < fuel + 1) :
    ((buildTermsDesc i coeffs (fuel + 1) idx acc).toList.map
      Monomial.toMvPoly).sum =
    (acc.toList.map Monomial.toMvPoly).sum +
    ∑ k ∈ Finset.range (idx + 1),
      (MvPolynomial.monomial (Finsupp.single i k)) ((coeffs[k]?).getD 0) := by
  classical
  match fuel with
  | 0 =>
    have hidx : idx = 0 := by omega
    subst hidx
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
    exact buildTermsDesc_base i coeffs acc 0
  | fuel + 1 =>
    by_cases hidx : idx = 0
    · subst hidx
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      exact buildTermsDesc_base i coeffs acc (fuel + 1)
    · have hidx' : idx - 1 < fuel + 1 := by omega
      show ((buildTermsDesc i coeffs (fuel + 2) idx acc).toList.map
        Monomial.toMvPoly).sum = _
      unfold buildTermsDesc
      simp only [hidx, ↓reduceIte]
      split
      · next hc =>
        rw [buildTermsDesc_toMvPoly_sum i coeffs fuel (idx - 1) acc hidx']
        rw [show idx - 1 + 1 = idx from by omega, Finset.sum_range_succ]
        simp [hc]
      · next hc =>
        rw [buildTermsDesc_toMvPoly_sum i coeffs fuel (idx - 1)
            (acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩) hidx']
        rw [Array.toList_push, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton]
        rw [show idx - 1 + 1 = idx from by omega, Finset.sum_range_succ]
        conv_lhs =>
          rw [show Monomial.toMvPoly (⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩ :
            Monomial n R ord) =
            (MvPolynomial.monomial (Finsupp.single i idx)) ((coeffs[idx]?).getD 0) from by
            unfold Monomial.toMvPoly; rw [ofVarPow_toFinsupp]]
        ring

/-! ### Main equivalence -/

/-- Converting via `toAzMvPolynomial i` then `toMvPoly` equals
    embedding via `Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i)`. -/
theorem toMvPoly_toAzMvPolynomial (i : Fin n)
    (p : AzPolynomial R) :
    toMvPoly (p.toAzMvPolynomial i (ord := ord)) =
    Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) (AzPolynomial.toPoly p) := by
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
    change ((buildTermsDesc i p.coeffs p.coeffs.size (p.coeffs.size - 1) #[]).toList.map
      Monomial.toMvPoly).sum = _
    set m := p.coeffs.size - 1 with hm_def
    have hm : m + 1 = p.coeffs.size := Nat.succ_pred (by omega)
    rw [show p.coeffs.size = m + 1 from hm.symm]
    rw [buildTermsDesc_toMvPoly_sum i p.coeffs m m #[] (by omega)]
    simp only [List.map_nil, List.sum_nil, zero_add]
    rw [show (AzPolynomial.toPoly p).natDegree + 1 = m + 1 from by
      rw [AzPolynomial.natDegree_toPoly]
      unfold Azurite.AzPolynomial.natDegree; omega]
    congr 1; ext k
    rw [MvPolynomial.C_mul_X_pow_eq_monomial, coeff_toPoly_eq]
    simp only [Azurite.AzPolynomial.coeff]

end Azurite
