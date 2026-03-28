/-
  Equivalence proofs for `mulNaive`.

  Proves that `mulNaive` correctly computes the product in `MvPolynomial`
  semantics: `(p.mulNaive q).toMvPoly = p.toMvPoly * q.toMvPoly`.

  These proofs are kept separate from `Equiv/Mul.lean` so they remain valid
  when `mul` delegates to a more sophisticated algorithm.
-/
import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-! ### Monomial-level multiplication -/

omit [DecidableEq R] in
/-- `toMvPoly` distributes over monomial multiplication. -/
theorem Monomial.toMvPoly_mul (a b : Monomial σ R ord) :
    (a * b).toMvPoly = a.toMvPoly * b.toMvPoly := by
  show monomial (a.monic * b.monic).toFinsupp (a.coeff.val * b.coeff.val) =
    monomial a.monic.toFinsupp a.coeff.val * monomial b.monic.toFinsupp b.coeff.val
  rw [MvPolynomial.monomial_mul, MonicMonomial.toFinsupp_mul]

/-! ### Normalization preserves toMvPoly sum -/

omit [NoZeroDivisors R] in
/-- `combineSorted` preserves the `toMvPoly` sum. -/
theorem toMvPoly_combineSorted (l : List (Monomial σ R ord)) :
    ((combineSorted l).map Monomial.toMvPoly).sum =
    (l.map Monomial.toMvPoly).sum := by
  induction l using combineSorted.induct with
  | case1 => simp [combineSorted]
  | case2 _ => simp [combineSorted]
  | case3 m₁ m₂ rest heq hcz ih =>
    simp only [combineSorted, if_pos heq, dif_pos hcz, List.map_cons, List.sum_cons]; rw [ih]
    have : m₁.toMvPoly + m₂.toMvPoly = 0 := by
      simp only [Monomial.toMvPoly, heq]
      rw [← map_add (monomial m₂.monic.toFinsupp), hcz, monomial_zero]
    rw [← add_assoc, this, zero_add]
  | case4 m₁ m₂ rest heq hcnz ih =>
    simp only [combineSorted, if_pos heq, dif_neg hcnz, List.map_cons, List.sum_cons]
    rw [ih, List.map_cons, List.sum_cons]
    have : (⟨⟨m₁.coeff.val + m₂.coeff.val, hcnz⟩, m₁.monic⟩ : Monomial σ R ord).toMvPoly =
        m₁.toMvPoly + m₂.toMvPoly := by
      simp only [Monomial.toMvPoly, heq]
      exact map_add (monomial m₂.monic.toFinsupp) m₁.coeff.val m₂.coeff.val
    rw [this, add_assoc]
  | case5 _ _ _ hneq ih =>
    simp only [combineSorted, if_neg hneq, List.map_cons, List.sum_cons]; congr 1

omit [NoZeroDivisors R] [DecidableEq R] in
/-- `sortDescending` preserves the `toMvPoly` sum (via permutation). -/
theorem toMvPoly_sortDescending (l : List (Monomial σ R ord)) :
    ((sortDescending l).map Monomial.toMvPoly).sum =
    (l.map Monomial.toMvPoly).sum :=
  (List.mergeSort_perm l _).map Monomial.toMvPoly |>.sum_eq

omit [NoZeroDivisors R] in
/-- `normalizeMonomials` preserves the `toMvPoly` sum. -/
theorem toMvPoly_normalizeMonomials (l : List (Monomial σ R ord)) :
    ((normalizeMonomials l).map Monomial.toMvPoly).sum =
    (l.map Monomial.toMvPoly).sum := by
  unfold normalizeMonomials; rw [toMvPoly_combineSorted, toMvPoly_sortDescending]

/-! ### Distributive law for mulPairs -/

omit [DecidableEq R] in
/-- The `toMvPoly` sum of all pairwise products equals the product of the
    individual `toMvPoly` sums (distributivity). -/
theorem toMvPoly_mulPairs (ps qs : List (Monomial σ R ord)) :
    ((mulPairs ps qs).map Monomial.toMvPoly).sum =
    (ps.map Monomial.toMvPoly).sum * (qs.map Monomial.toMvPoly).sum := by
  simp only [mulPairs, List.map_flatMap, List.map_map]
  induction ps with
  | nil => simp
  | cons p ps' ih =>
    simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, add_mul]
    rw [ih]; congr 1
    conv_lhs => rw [show (Monomial.toMvPoly ∘ fun q => p * q) =
      (fun q : Monomial σ R ord => p.toMvPoly * q.toMvPoly) from
      funext (fun q => Monomial.toMvPoly_mul p q)]
    rw [← List.sum_map_mul_left]

/-! ### Full mulNaive equivalence -/

/-- `mulNaive` correctly computes the `MvPolynomial` product. -/
theorem toMvPoly_mulNaive (p q : AzMvPolynomial σ R ord) :
    (p.mulNaive q).toMvPoly = p.toMvPoly * q.toMvPoly := by
  rw [AzMvPolynomial.toMvPoly_eq_list_sum (p.mulNaive q)]
  simp only [AzMvPolynomial.mulNaive, List.toList_toArray]
  rw [toMvPoly_normalizeMonomials, toMvPoly_mulPairs,
      ← AzMvPolynomial.toMvPoly_eq_list_sum p,
      ← AzMvPolynomial.toMvPoly_eq_list_sum q]

end Azurite
