import Mathlib.RingTheory.Polynomial.Vieta

/-! # BPR Section 2.1 — Lemma 2.12

> Let `x₁, …, xₖ ∈ K` and `P = (X − x₁)⋯(X − xₖ) = Xᵏ + C₁Xᵏ⁻¹ + ⋯ + Cₖ`.
> Then `Cᵢ = (−1)ⁱ Eᵢ(x₁, …, xₖ)`, i.e., the coefficient of `Xᵏ⁻ⁱ` in
> `P` equals `(−1)ⁱ` times the `i`-th elementary symmetric function
> evaluated at the roots.

This is `Multiset.prod_X_sub_C_coeff` in Mathlib, specialized to
`Fin k → K`.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [CommRing K]

/-- **BPR Lemma 2.12.** Let `x₁, …, xₖ ∈ K` and
    `P = (X − x₁)⋯(X − xₖ) = Xᵏ + C₁Xᵏ⁻¹ + ⋯ + Cₖ`.
    Then `Cᵢ = (−1)ⁱ Eᵢ(x₁, …, xₖ)`, i.e., the coefficient of `Xᵏ⁻ⁱ` in `P`
    equals `(−1)ⁱ` times the `i`-th elementary symmetric function evaluated at
    the roots.

    This is `Multiset.prod_X_sub_C_coeff` in Mathlib, specialized to `Fin k → K`. -/
theorem lemma_2_12 {k : ℕ} (x : Fin k → K) {i : ℕ} (hi : i ≤ k) :
    (∏ j : Fin k, (X - C (x j))).coeff (k - i) =
    (-1) ^ i * (Finset.univ.val.map x).esymm i := by
  have hcard : (Finset.univ.val.map x).card = k := by simp
  have hmap : (Finset.univ.val.map (fun j => X - C (x j))) =
      (Finset.univ.val.map x).map (fun t => X - C t) := by
    rw [Multiset.map_map]; rfl
  rw [Finset.prod_eq_multiset_prod, hmap,
      Multiset.prod_X_sub_C_coeff _ (by omega)]
  simp only [hcard, Nat.sub_sub_self hi]

end Azurite.BPR
