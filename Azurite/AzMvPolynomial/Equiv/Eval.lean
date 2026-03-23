/-
  Equivalence between AzMvPolynomial.eval and MvPolynomial.eval.
-/
import Azurite.AzMvPolynomial.Eval
import Azurite.AzMvPolynomial.Equiv.Basic

namespace Azurite

open MonomialOrder MonicMonomial Monomial MvPolynomial

variable {R : Type _} [CommSemiring R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-! ### Monomial-level equivalence -/

/-- Evaluating a monomial via `Monomial.eval` agrees with `MvPolynomial.eval`
    applied to `Monomial.toMvPoly`. -/
theorem Monomial.eval_eq_mvPoly_eval [DecidableEq σ] [DecidableEq R]
    (m : Monomial σ R ord) (f : σ → R) :
    m.eval f = MvPolynomial.eval f m.toMvPoly := by
  simp only [Monomial.eval, Monomial.toMvPoly, eval_monomial]
  congr 1
  simp only [MonicMonomial.eval, MonicMonomial.toFinsupp]
  rw [Finsupp.onFinset_prod _ (by intros; simp)]
  apply Finset.prod_nbij Var.ofFin
  · intro a _; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  · exact fun _ _ _ _ h => Var.ofFin_injective h
  · intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨i, Finset.mem_univ _, rfl⟩
  · intro i _; simp [Var.toFin_ofFin]

/-! ### Polynomial-level equivalence -/

private theorem foldl_eval_eq [DecidableEq σ] [DecidableEq R]
    (l : List (Monomial σ R ord)) (f : σ → R) (acc : R) (pacc : MvPolynomial σ R)
    (hacc : acc = MvPolynomial.eval f pacc) :
    l.foldl (fun a m => a + m.eval f) acc =
    MvPolynomial.eval f (l.foldl (fun a m => a + m.toMvPoly) pacc) := by
  induction l generalizing acc pacc with
  | nil => exact hacc
  | cons m t ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [hacc, map_add, Monomial.eval_eq_mvPoly_eval]

/-- Evaluating an `AzMvPolynomial` agrees with `MvPolynomial.eval`
    applied to the equivalent `MvPolynomial`. -/
theorem AzMvPolynomial.eval_eq_mvPoly_eval [DecidableEq σ] [DecidableEq R]
    (p : AzMvPolynomial σ R ord) (f : σ → R) :
    p.eval f = MvPolynomial.eval f p.toMvPoly := by
  simp only [AzMvPolynomial.eval, AzMvPolynomial.toMvPoly]
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_eval_eq p.terms.toList f 0 0 (by simp)

/-- Evaluating an `MvPolynomial` via `MvPolynomial.eval` agrees with
    `AzMvPolynomial.eval` applied to `ofMvPoly`. -/
theorem eval_ofMvPoly [DecidableEq σ] [DecidableEq R]
    (p : MvPolynomial σ R) (f : σ → R) :
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial σ R ord).eval f =
    MvPolynomial.eval f p := by
  rw [AzMvPolynomial.eval_eq_mvPoly_eval, toMvPoly_ofMvPoly]

end Azurite
