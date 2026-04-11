import Azurite.AzMvPolynomial.New.Eval2
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Equivalence: `AzMvPolynomialNew.eval₂` ↔ `MvPolynomial.eval₂`

Fin-only companion to `AzMvPolynomial.Equiv.Eval2`.
-/

namespace Azurite

open AzMvPolynomialNew MonicMonomialNew MonomialNew

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}
  {S : Type _} [CommSemiring S]

omit [DecidableEq R] in
/-- Per-monomial: `MonomialNew.eval₂` on a single monomial equals
    `MvPolynomial.eval₂` on its `toMvPoly` image. -/
theorem MonomialNew.toMvPoly_eval₂ (m : MonomialNew n R ord)
    (φ : R →+* S) (f : Fin n → S) :
    m.eval₂ φ f = MvPolynomial.eval₂ φ f m.toMvPoly := by
  show φ m.coeff.val * m.monic.eval f = _
  rw [MonomialNew.toMvPoly, MvPolynomial.eval₂_monomial]
  congr 1
  show Finset.univ.prod (fun i : Fin n => f i ^ m.monic.exponents[i]) = _
  simp only [MonicMonomialNew.toFinsupp]
  rw [Finsupp.onFinset_prod _ (by intros; simp)]

omit [DecidableEq R] in
/-- Folding-with-add lemma: pulling `eval₂` over a foldl-sum of monomials. -/
private theorem toMvPoly_foldl_eval₂_new
    (l : List (MonomialNew n R ord)) (φ : R →+* S) (f : Fin n → S) (acc : S) :
    l.foldl (fun acc m => acc + m.eval₂ φ f) acc =
    acc + (l.map (fun m => MvPolynomial.eval₂ φ f m.toMvPoly)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, MonomialNew.toMvPoly_eval₂]; ring

omit [DecidableEq R] in
/-- The main bridge: `AzMvPolynomialNew.eval₂` matches `MvPolynomial.eval₂`
    applied to the `toMvPoly` image. -/
@[simp] theorem AzMvPolynomialNew.toMvPoly_eval₂ (p : AzMvPolynomialNew n R ord)
    (φ : R →+* S) (f : Fin n → S) :
    p.eval₂ φ f = MvPolynomial.eval₂ φ f p.toMvPoly := by
  show p.terms.foldl (fun acc m => acc + m.eval₂ φ f) 0 = _
  rw [← Array.foldl_toList, toMvPoly_foldl_eval₂_new, zero_add]
  rw [toMvPoly_eq_list_sum]
  have := map_list_sum (MvPolynomial.eval₂Hom φ f) (p.terms.toList.map MonomialNew.toMvPoly)
  rw [List.map_map] at this
  simp only [Function.comp_def, MvPolynomial.coe_eval₂Hom] at this
  exact this.symm

omit [DecidableEq R] in
/-- `AzMvPolynomialNew.aeval` matches `MvPolynomial.aeval` across the bridge. -/
@[simp] theorem AzMvPolynomialNew.toMvPoly_aeval [Algebra R S]
    (p : AzMvPolynomialNew n R ord) (f : Fin n → S) :
    p.aeval f = MvPolynomial.aeval f p.toMvPoly := by
  show p.eval₂ (algebraMap R S) f = _
  rw [AzMvPolynomialNew.toMvPoly_eval₂]
  rfl

end Azurite
