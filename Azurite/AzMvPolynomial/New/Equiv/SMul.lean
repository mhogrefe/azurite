/-
  Equivalence proofs for `AzMvPolynomialNew` scalar multiplication.
-/
import Azurite.AzMvPolynomial.New.SMul
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Basic

namespace Azurite
open AzMvPolynomialNew MvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Helper: filterMap smul distributes over MvPolynomial sum -/

/-- Summing `filterMap (smulMonomialNew r)` over a list of monomials equals
    `C r *` the original sum. -/
theorem filterMap_smul_sum_new (r : R) (l : List (MonomialNew n R ord)) :
    ((l.filterMap (smulMonomialNew r)).map MonomialNew.toMvPoly).sum =
    MvPolynomial.C r * ((l.map MonomialNew.toMvPoly).sum) := by
  induction l with
  | nil => simp
  | cons m t ih =>
    rw [List.map_cons, List.sum_cons, mul_add, ← ih, List.filterMap_cons]
    rcases hm : smulMonomialNew r m with _ | m'
    · simp only [MonomialNew.toMvPoly]
      have : r * m.coeff.val = 0 := by
        unfold smulMonomialNew at hm; split at hm <;> [assumption; contradiction]
      rw [show MvPolynomial.C r * MvPolynomial.monomial m.monic.toFinsupp m.coeff.val =
        MvPolynomial.monomial m.monic.toFinsupp (r * m.coeff.val) from
          MvPolynomial.C_mul_monomial]
      rw [this, MvPolynomial.monomial_zero, zero_add]
    · rw [List.map_cons, List.sum_cons]; congr 1
      simp only [MonomialNew.toMvPoly]
      unfold smulMonomialNew at hm; split at hm <;> [contradiction; skip]
      injection hm with hm'; subst hm'
      rw [MvPolynomial.C_mul_monomial]

/-! ### toMvPoly_smul -/

/-- Scalar multiplication commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_smul_new (r : R) (p : AzMvPolynomialNew n R ord) :
    (r • p).toMvPoly = r • p.toMvPoly := by
  rw [AzMvPolynomialNew.toMvPoly_eq_list_sum, AzMvPolynomialNew.toMvPoly_eq_list_sum]
  show ((p.terms.toList.filterMap (smulMonomialNew r)).map MonomialNew.toMvPoly).sum =
    r • (p.terms.toList.map MonomialNew.toMvPoly).sum
  rw [filterMap_smul_sum_new, Algebra.smul_def]
  rfl

/-! ### ofMvPoly_smul -/

/-- Scalar multiplication commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_smul_new (r : R) (p : MvPolynomial (Fin n) R) :
    (AzMvPolynomialNew.ofMvPoly (r • p) : AzMvPolynomialNew n R ord) =
      r • AzMvPolynomialNew.ofMvPoly p := by
  set q := AzMvPolynomialNew.ofMvPoly (ord := ord) p
  have hp : q.toMvPoly = p := toMvPoly_ofMvPoly_new p
  rw [← hp, ← toMvPoly_smul_new r q]
  exact ofMvPoly_toMvPoly_new _

end Azurite
