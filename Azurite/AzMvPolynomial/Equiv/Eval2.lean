import Azurite.AzMvPolynomial.Eval2
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Equivalence: `AzMvPolynomial.eval₂` ↔ `MvPolynomial.eval₂`

The Azurite `eval₂` is the same function as Mathlib's `MvPolynomial.eval₂`
once we move across the `toMvPoly` bridge. Both evaluate a polynomial at
variable values `f : σ → S` using a coefficient embedding `φ : R →+* S`.

This bridge is the key ingredient for proving the forward direction of
`finSuccEquiv` matches Mathlib's.
-/

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}
  {S : Type _} [CommSemiring S]

/-- Generic form of `prod_fin_eq_prod_support`: for any commutative monoid
    target, a product over `Fin n` using `Var.ofFin` equals the product over
    the support of the finitely-supported representation of a monic monomial. -/
private theorem prod_fin_eq_prod_support_generic {M : Type _} [CommMonoid M]
    (m : MonicMonomial σ ord) (g : σ → M) :
    (∏ j : Fin n, g (Var.ofFin j) ^ m.exponents[j]) =
    ∏ v ∈ m.toFinsupp.support, g v ^ (m.toFinsupp v) := by
  have hinj := @Var.ofFin_injective σ n _ _
  have himg : (∏ j : Fin n, g (Var.ofFin j) ^ m.exponents[j])
      = ∏ v ∈ Finset.univ.image (@Var.ofFin σ n _ _), g v ^ (m.toFinsupp v) := by
    rw [Finset.prod_image (fun a _ b _ hab => hinj hab)]
    congr 1; ext j
    simp [MonicMonomial.toFinsupp, Finsupp.onFinset_apply, Var.toFin_ofFin]
  rw [himg]; symm; apply Finset.prod_subset
  · intro v hv
    rw [Finset.mem_image]; exact ⟨Var.toFin v, Finset.mem_univ _, Var.ofFin_toFin v⟩
  · intro v _ hv; simp only [Finsupp.mem_support_iff, not_not] at hv; rw [hv, pow_zero]

omit [DecidableEq R] in
/-- Per-monomial: `Monomial.eval₂` on a single monomial equals
    `MvPolynomial.eval₂` on its `toMvPoly` image. -/
theorem Monomial.toMvPoly_eval₂ (m : Monomial σ R ord)
    (φ : R →+* S) (f : σ → S) :
    m.eval₂ φ f = MvPolynomial.eval₂ φ f m.toMvPoly := by
  show φ m.coeff.val * m.monic.eval f = _
  rw [Monomial.toMvPoly, MvPolynomial.eval₂_monomial]
  congr 1
  show Finset.univ.prod (fun i : Fin n => f (Var.ofFin i) ^ m.monic.exponents[i]) = _
  exact prod_fin_eq_prod_support_generic m.monic f

omit [DecidableEq R] in
/-- Folding-with-add lemma: pulling `eval₂` over a foldl-sum of monomials. -/
private theorem toMvPoly_foldl_eval₂
    (l : List (Monomial σ R ord)) (φ : R →+* S) (f : σ → S) (acc : S) :
    l.foldl (fun acc m => acc + m.eval₂ φ f) acc =
    acc + (l.map (fun m => MvPolynomial.eval₂ φ f m.toMvPoly)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, Monomial.toMvPoly_eval₂]; ring

omit [DecidableEq R] in
/-- The main bridge: `AzMvPolynomial.eval₂` matches `MvPolynomial.eval₂`
    applied to the `toMvPoly` image. -/
@[simp] theorem AzMvPolynomial.toMvPoly_eval₂ (p : AzMvPolynomial σ R ord)
    (φ : R →+* S) (f : σ → S) :
    p.eval₂ φ f = MvPolynomial.eval₂ φ f p.toMvPoly := by
  show p.terms.foldl (fun acc m => acc + m.eval₂ φ f) 0 = _
  rw [← Array.foldl_toList, toMvPoly_foldl_eval₂, zero_add]
  rw [toMvPoly_eq_list_sum]
  have := map_list_sum (MvPolynomial.eval₂Hom φ f) (p.terms.toList.map Monomial.toMvPoly)
  rw [List.map_map] at this
  simp only [Function.comp_def, MvPolynomial.coe_eval₂Hom] at this
  exact this.symm

omit [DecidableEq R] in
/-- `AzMvPolynomial.aeval` matches `MvPolynomial.aeval` across the bridge. -/
@[simp] theorem AzMvPolynomial.toMvPoly_aeval [Algebra R S]
    (p : AzMvPolynomial σ R ord) (f : σ → S) :
    p.aeval f = MvPolynomial.aeval f p.toMvPoly := by
  show p.eval₂ (algebraMap R S) f = _
  rw [AzMvPolynomial.toMvPoly_eval₂]
  rfl

end Azurite
