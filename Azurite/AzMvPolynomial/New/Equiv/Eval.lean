/-
  Equivalence between `AzMvPolynomialNew.eval` and `MvPolynomial.eval`.
-/
import Azurite.AzMvPolynomial.New.Eval
import Azurite.AzMvPolynomial.New.Equiv.Basic

namespace Azurite

open MonomialOrder MonicMonomialNew MonomialNew MvPolynomial

variable {R : Type _} [CommSemiring R] {n : ℕ} {ord : MonomialOrder}

/-! ### Monomial-level equivalence -/

/-- Evaluating a monomial via `MonomialNew.eval` agrees with `MvPolynomial.eval`
    applied to `MonomialNew.toMvPoly`. -/
theorem MonomialNew.eval_eq_mvPoly_eval [DecidableEq R]
    (m : MonomialNew n R ord) (f : Fin n → R) :
    m.eval f = MvPolynomial.eval f m.toMvPoly := by
  simp only [MonomialNew.eval, MonomialNew.toMvPoly, eval_monomial]
  congr 1
  simp only [MonicMonomialNew.eval, MonicMonomialNew.toFinsupp]
  rw [Finsupp.onFinset_prod _ (by intros; simp)]

/-! ### Polynomial-level equivalence -/

private theorem foldl_eval_eq_new [DecidableEq R]
    (l : List (MonomialNew n R ord)) (f : Fin n → R) (acc : R)
    (pacc : MvPolynomial (Fin n) R)
    (hacc : acc = MvPolynomial.eval f pacc) :
    l.foldl (fun a m => a + m.eval f) acc =
    MvPolynomial.eval f (l.foldl (fun a m => a + m.toMvPoly) pacc) := by
  induction l generalizing acc pacc with
  | nil => exact hacc
  | cons m t ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [hacc, map_add, MonomialNew.eval_eq_mvPoly_eval]

/-- Evaluating an `AzMvPolynomialNew` agrees with `MvPolynomial.eval`
    applied to the equivalent `MvPolynomial`. -/
theorem AzMvPolynomialNew.eval_eq_mvPoly_eval [DecidableEq R]
    (p : AzMvPolynomialNew n R ord) (f : Fin n → R) :
    p.eval f = MvPolynomial.eval f p.toMvPoly := by
  simp only [AzMvPolynomialNew.eval, AzMvPolynomialNew.toMvPoly]
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_eval_eq_new p.terms.toList f 0 0 (by simp)

/-- Evaluating an `MvPolynomial` via `MvPolynomial.eval` agrees with
    `AzMvPolynomialNew.eval` applied to `ofMvPoly`. -/
theorem eval_ofMvPoly_new [DecidableEq R]
    (p : MvPolynomial (Fin n) R) (f : Fin n → R) :
    (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n R ord).eval f =
    MvPolynomial.eval f p := by
  rw [AzMvPolynomialNew.eval_eq_mvPoly_eval, toMvPoly_ofMvPoly_new]

end Azurite
