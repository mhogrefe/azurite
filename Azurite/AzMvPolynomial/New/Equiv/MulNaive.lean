/-
  Equivalence proofs for `AzMvPolynomialNew.mulNaive`.

  Mirrors the old `Equiv/MulNaive.lean`.  Proves `(p.mulNaive q).toMvPoly
  = p.toMvPoly * q.toMvPoly` so that `mul` delegating to `mulNaive` is
  automatically equivalent.
-/
import Azurite.AzMvPolynomial.New.Mul
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Azurite
open AzMvPolynomialNew MvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Monomial-level multiplication -/

omit [DecidableEq R] in
/-- `toMvPoly` distributes over monomial multiplication. -/
theorem MonomialNew.toMvPoly_mul (a b : MonomialNew n R ord) :
    (a * b).toMvPoly = a.toMvPoly * b.toMvPoly := by
  show monomial (a.monic * b.monic).toFinsupp (a.coeff.val * b.coeff.val) =
    monomial a.monic.toFinsupp a.coeff.val * monomial b.monic.toFinsupp b.coeff.val
  rw [MvPolynomial.monomial_mul, MonicMonomialNew.toFinsupp_mul]

/-! ### Normalization preserves toMvPoly sum -/

omit [NoZeroDivisors R] in
/-- `combineSortedNew` preserves the `toMvPoly` sum. -/
theorem toMvPoly_combineSortedNew (l : List (MonomialNew n R ord)) :
    ((combineSortedNew l).map MonomialNew.toMvPoly).sum =
    (l.map MonomialNew.toMvPoly).sum := by
  induction l using combineSortedNew.induct with
  | case1 => simp [combineSortedNew]
  | case2 _ => simp [combineSortedNew]
  | case3 m₁ m₂ rest heq hcz ih =>
    simp only [combineSortedNew, if_pos heq, dif_pos hcz, List.map_cons, List.sum_cons]; rw [ih]
    have : m₁.toMvPoly + m₂.toMvPoly = 0 := by
      simp only [MonomialNew.toMvPoly, heq]
      rw [← map_add (monomial m₂.monic.toFinsupp), hcz, monomial_zero]
    rw [← add_assoc, this, zero_add]
  | case4 m₁ m₂ rest heq hcnz ih =>
    simp only [combineSortedNew, if_pos heq, dif_neg hcnz, List.map_cons, List.sum_cons]
    rw [ih, List.map_cons, List.sum_cons]
    have : (⟨⟨m₁.coeff.val + m₂.coeff.val, hcnz⟩, m₁.monic⟩ : MonomialNew n R ord).toMvPoly =
        m₁.toMvPoly + m₂.toMvPoly := by
      simp only [MonomialNew.toMvPoly, heq]
      exact map_add (monomial m₂.monic.toFinsupp) m₁.coeff.val m₂.coeff.val
    rw [this, add_assoc]
  | case5 _ _ _ hneq ih =>
    simp only [combineSortedNew, if_neg hneq, List.map_cons, List.sum_cons]; congr 1

omit [NoZeroDivisors R] [DecidableEq R] in
/-- `sortDescendingNew` preserves the `toMvPoly` sum (via permutation). -/
theorem toMvPoly_sortDescendingNew (l : List (MonomialNew n R ord)) :
    ((sortDescendingNew l).map MonomialNew.toMvPoly).sum =
    (l.map MonomialNew.toMvPoly).sum :=
  (List.mergeSort_perm l _).map MonomialNew.toMvPoly |>.sum_eq

omit [NoZeroDivisors R] in
/-- `normalizeMonomialsNew` preserves the `toMvPoly` sum. -/
theorem toMvPoly_normalizeMonomialsNew (l : List (MonomialNew n R ord)) :
    ((normalizeMonomialsNew l).map MonomialNew.toMvPoly).sum =
    (l.map MonomialNew.toMvPoly).sum := by
  unfold normalizeMonomialsNew
  rw [toMvPoly_combineSortedNew, toMvPoly_sortDescendingNew]

/-! ### Distributive law for mulPairsNew -/

omit [DecidableEq R] in
/-- The `toMvPoly` sum of all pairwise products equals the product of the
    individual `toMvPoly` sums (distributivity). -/
theorem toMvPoly_mulPairsNew (ps qs : List (MonomialNew n R ord)) :
    ((mulPairsNew ps qs).map MonomialNew.toMvPoly).sum =
    (ps.map MonomialNew.toMvPoly).sum * (qs.map MonomialNew.toMvPoly).sum := by
  simp only [mulPairsNew, List.map_flatMap, List.map_map]
  induction ps with
  | nil => simp
  | cons p ps' ih =>
    simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, add_mul]
    rw [ih]; congr 1
    conv_lhs => rw [show (MonomialNew.toMvPoly ∘ fun q => p * q) =
      (fun q : MonomialNew n R ord => p.toMvPoly * q.toMvPoly) from
      funext (fun q => MonomialNew.toMvPoly_mul p q)]
    rw [← List.sum_map_mul_left]

/-! ### Full mulNaive equivalence -/

/-- `mulNaive` correctly computes the `MvPolynomial` product. -/
theorem toMvPoly_mulNaive_new (p q : AzMvPolynomialNew n R ord) :
    (p.mulNaive q).toMvPoly = p.toMvPoly * q.toMvPoly := by
  rw [AzMvPolynomialNew.toMvPoly_eq_list_sum (p.mulNaive q)]
  simp only [AzMvPolynomialNew.mulNaive, List.toList_toArray]
  rw [toMvPoly_normalizeMonomialsNew, toMvPoly_mulPairsNew,
      ← AzMvPolynomialNew.toMvPoly_eq_list_sum p,
      ← AzMvPolynomialNew.toMvPoly_eq_list_sum q]

end Azurite
