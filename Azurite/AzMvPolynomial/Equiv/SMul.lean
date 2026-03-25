/-
  Equivalence proofs for AzMvPolynomial scalar multiplication.
-/
import Azurite.AzMvPolynomial.SMul
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Basic

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-! ### Helper: filterMap smul distributes over MvPolynomial sum -/

/-- Summing `filterMap (smulMonomial r)` over a list of monomials equals
    `C r *` the original sum. -/
theorem filterMap_smul_sum (r : R) (l : List (Monomial σ R ord)) :
    ((l.filterMap (smulMonomial r)).map Monomial.toMvPoly).sum =
    MvPolynomial.C r * ((l.map Monomial.toMvPoly).sum) := by
  induction l with
  | nil => simp
  | cons m t ih =>
    rw [List.map_cons, List.sum_cons, mul_add, ← ih, List.filterMap_cons]
    rcases hm : smulMonomial r m with _ | m'
    · simp only [Monomial.toMvPoly]
      have : r * m.coeff.val = 0 := by
        unfold smulMonomial at hm; split at hm <;> [assumption; contradiction]
      rw [show MvPolynomial.C r * MvPolynomial.monomial m.monic.toFinsupp m.coeff.val =
        MvPolynomial.monomial m.monic.toFinsupp (r * m.coeff.val) from
          MvPolynomial.C_mul_monomial]
      rw [this, MvPolynomial.monomial_zero, zero_add]
    · rw [List.map_cons, List.sum_cons]; congr 1
      simp only [Monomial.toMvPoly]
      unfold smulMonomial at hm; split at hm <;> [contradiction; skip]
      injection hm with hm'; subst hm'
      rw [MvPolynomial.C_mul_monomial]

/-! ### toMvPoly_smul -/

/-- Scalar multiplication commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_smul (r : R) (p : AzMvPolynomial σ R ord) :
    (r • p).toMvPoly = r • p.toMvPoly := by
  rw [AzMvPolynomial.toMvPoly_eq_list_sum, AzMvPolynomial.toMvPoly_eq_list_sum]
  show ((p.terms.toList.filterMap (smulMonomial r)).map Monomial.toMvPoly).sum =
    r • (p.terms.toList.map Monomial.toMvPoly).sum
  rw [filterMap_smul_sum, Algebra.smul_def]
  rfl

/-! ### ofMvPoly_smul -/

/-- Scalar multiplication commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_smul (r : R) (p : MvPolynomial σ R) :
    (AzMvPolynomial.ofMvPoly (r • p) : AzMvPolynomial σ R ord) =
      r • AzMvPolynomial.ofMvPoly p := by
  set q := AzMvPolynomial.ofMvPoly (ord := ord) p
  have hp : q.toMvPoly = p := toMvPoly_ofMvPoly p
  rw [← hp, ← toMvPoly_smul r q]
  exact ofMvPoly_toMvPoly _

end Azurite
