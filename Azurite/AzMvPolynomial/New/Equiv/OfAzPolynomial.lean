import Azurite.AzMvPolynomial.New.OfAzPolynomial
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Equivalence: `AzPolynomial.toAzMvPolynomialNew` ↔ `Polynomial.eval₂ C (X i)`

We prove that converting a univariate `AzPolynomial` to an `AzMvPolynomialNew`
via `toAzMvPolynomialNew i` agrees with Mathlib's embedding via `eval₂ C (X i)`.

```
toMvPoly (p.toAzMvPolynomialNew i) =
  Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) (toPoly p)
```
-/

namespace Azurite
open AzMvPolynomialNew MvPolynomial Polynomial MonomialOrder

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-! ### ofVarPow to Finsupp.single -/

theorem ofVarPow_toFinsupp_new (i : Fin n) (k : ℕ) :
    (MonicMonomialNew.ofVarPow i k : MonicMonomialNew n ord).toFinsupp =
    Finsupp.single i k := by
  classical
  ext w
  simp only [MonicMonomialNew.toFinsupp, Finsupp.onFinset_apply, Finsupp.single_apply,
    MonicMonomialNew.ofVarPow]
  by_cases h : i = w
  · subst h; simp
  · have h' : (i : Fin n) ≠ ⟨(w : Fin n).val, w.isLt⟩ := by
      intro heq; apply h; ext; exact Fin.val_eq_of_eq heq
    simp [h']

/-! ### buildTermsDescNew loop invariant -/

/-- Base case: when `idx = 0`, `buildTermsDescNew` produces exactly one monomial term
    (or none if the coefficient is zero). -/
private theorem buildTermsDescNew_base (i : Fin n) (coeffs : Array R)
    (acc : Array (MonomialNew n R ord)) (fuel : ℕ) :
    ((buildTermsDescNew i coeffs (fuel + 1) 0 acc).toList.map MonomialNew.toMvPoly).sum =
    (acc.toList.map MonomialNew.toMvPoly).sum +
    (MvPolynomial.monomial (Finsupp.single i 0)) ((coeffs[0]?).getD 0) := by
  classical
  change ((if hc : (coeffs[0]?).getD 0 = 0 then acc
    else acc.push ⟨⟨(coeffs[0]?).getD 0, hc⟩, MonicMonomialNew.ofVarPow i 0⟩).toList.map
    MonomialNew.toMvPoly).sum = _
  split
  · next hc => simp [hc]
  · next hc =>
    rw [Array.toList_push, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
    congr 1; unfold MonomialNew.toMvPoly; rw [ofVarPow_toFinsupp_new]

/-- Loop invariant: the sum of `MonomialNew.toMvPoly` over the output of
    `buildTermsDescNew` equals the accumulator sum plus the polynomial sum
    `∑ k ∈ range (idx + 1), monomial (single i k) (coeffs[k])`. -/
theorem buildTermsDescNew_toMvPoly_sum (i : Fin n) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (MonomialNew n R ord))
    (hfuel : idx < fuel + 1) :
    ((buildTermsDescNew i coeffs (fuel + 1) idx acc).toList.map
      MonomialNew.toMvPoly).sum =
    (acc.toList.map MonomialNew.toMvPoly).sum +
    ∑ k ∈ Finset.range (idx + 1),
      (MvPolynomial.monomial (Finsupp.single i k)) ((coeffs[k]?).getD 0) := by
  classical
  match fuel with
  | 0 =>
    have hidx : idx = 0 := by omega
    subst hidx
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
    exact buildTermsDescNew_base i coeffs acc 0
  | fuel + 1 =>
    by_cases hidx : idx = 0
    · subst hidx
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      exact buildTermsDescNew_base i coeffs acc (fuel + 1)
    · have hidx' : idx - 1 < fuel + 1 := by omega
      show ((buildTermsDescNew i coeffs (fuel + 2) idx acc).toList.map
        MonomialNew.toMvPoly).sum = _
      unfold buildTermsDescNew
      simp only [hidx, ↓reduceIte]
      split
      · next hc =>
        rw [buildTermsDescNew_toMvPoly_sum i coeffs fuel (idx - 1) acc hidx']
        rw [show idx - 1 + 1 = idx from by omega, Finset.sum_range_succ]
        simp [hc]
      · next hc =>
        rw [buildTermsDescNew_toMvPoly_sum i coeffs fuel (idx - 1)
            (acc.push ⟨⟨_, hc⟩, MonicMonomialNew.ofVarPow i idx⟩) hidx']
        rw [Array.toList_push, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton]
        rw [show idx - 1 + 1 = idx from by omega, Finset.sum_range_succ]
        conv_lhs =>
          rw [show MonomialNew.toMvPoly (⟨⟨_, hc⟩, MonicMonomialNew.ofVarPow i idx⟩ :
            MonomialNew n R ord) =
            (MvPolynomial.monomial (Finsupp.single i idx)) ((coeffs[idx]?).getD 0) from by
            unfold MonomialNew.toMvPoly; rw [ofVarPow_toFinsupp_new]]
        ring

/-! ### Main equivalence -/

/-- Converting via `toAzMvPolynomialNew i` then `toMvPoly` equals
    embedding via `Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i)`. -/
theorem toMvPoly_toAzMvPolynomialNew (i : Fin n)
    (p : AzPolynomial R) :
    toMvPoly (p.toAzMvPolynomialNew i (ord := ord)) =
    Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) (AzPolynomial.toPoly p) := by
  classical
  rw [AzMvPolynomialNew.toMvPoly_eq_list_sum, Polynomial.eval₂_eq_sum_range]
  simp only [AzPolynomial.toAzMvPolynomialNew]
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
    change ((buildTermsDescNew i p.coeffs p.coeffs.size (p.coeffs.size - 1) #[]).toList.map
      MonomialNew.toMvPoly).sum = _
    set m := p.coeffs.size - 1 with hm_def
    have hm : m + 1 = p.coeffs.size := Nat.succ_pred (by omega)
    rw [show p.coeffs.size = m + 1 from hm.symm]
    rw [buildTermsDescNew_toMvPoly_sum i p.coeffs m m #[] (by omega)]
    simp only [List.map_nil, List.sum_nil, zero_add]
    rw [show (AzPolynomial.toPoly p).natDegree + 1 = m + 1 from by
      rw [AzPolynomial.natDegree_toPoly]
      unfold Azurite.AzPolynomial.natDegree; omega]
    congr 1; ext k
    rw [MvPolynomial.C_mul_X_pow_eq_monomial, coeff_toPoly_eq]
    simp only [Azurite.AzPolynomial.coeff]

end Azurite
