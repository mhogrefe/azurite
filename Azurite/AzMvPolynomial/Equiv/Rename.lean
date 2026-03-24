/-
  Equivalence between `AzMvPolynomial.rename` and `MvPolynomial.rename`.

  Key theorem:
    (p.rename f ord₂).toMvPoly = MvPolynomial.rename f p.toMvPoly
-/
import Mathlib.Algebra.MvPolynomial.Rename
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.AzMvPolynomial.Rename

namespace Azurite

open MvPolynomial MonomialOrder Monomial MonicMonomial

variable {R : Type _} [CommSemiring R]
    {σ₁ : Type _} {n₁ : ℕ} [DecidableEq σ₁] [LinearOrder σ₁] [Var σ₁ n₁]
    {σ₂ : Type _} {n₂ : ℕ} [DecidableEq σ₂] [LinearOrder σ₂] [Var σ₂ n₂]
    {ord : MonomialOrder}

/-! ### MonicMonomial-level bridge -/

/-- Renaming variables in a `MonicMonomial` and converting to `Finsupp`
    is the same as converting to `Finsupp` first and applying `mapDomain`.

    Both sides compute the same function:
      `v ↦ ∑ i : Fin n₁, if f (Var.ofFin i) = v then m.exponents[i] else 0` -/
theorem MonicMonomial.toFinsupp_rename
    (m : MonicMonomial σ₁ ord) (f : σ₁ → σ₂) (ord₂ : MonomialOrder) :
    (m.rename f ord₂).toFinsupp = Finsupp.mapDomain f m.toFinsupp := by
  apply Finsupp.ext; intro v
  -- Unfold all definitions, push `v` inside the RHS sum,
  -- and apply `Finsupp.single_apply` to convert `single` to `if`.
  unfold MonicMonomial.toFinsupp MonicMonomial.rename
  simp only [Finsupp.onFinset_apply, Finsupp.mapDomain, Finsupp.sum]
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  -- LHS: (Vector.ofFn f')[Var.toFin v] → f' (Var.toFin v)
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  -- Convert `Var.toFin a = Var.toFin b` to `a = b` (toFin is injective)
  simp_rw [show ∀ i : Fin n₁,
    (Var.toFin (f (Var.ofFin i)) = Var.toFin v) = (f (Var.ofFin i) = v) from
    fun _ => propext ⟨fun h => Var.toFin_injective h, congrArg Var.toFin⟩]
  -- RHS: extend support → image Var.ofFin univ, reindex via Var.ofFin
  symm
  rw [Finset.sum_subset Finsupp.support_onFinset_subset (by
    intro x _ hx
    simp only [Finsupp.mem_support_iff, Finsupp.onFinset_apply, not_not] at hx
    split <;> [exact hx; rfl])]
  rw [Finset.sum_image (fun _ _ _ _ h => Var.ofFin_injective h)]
  simp [Var.toFin_ofFin]

/-! ### Monomial-level bridge -/

/-- Renaming variables in a `Monomial` and converting to `MvPolynomial`
    is the same as converting first and applying `MvPolynomial.rename`. -/
theorem Monomial.toMvPoly_rename (m : Monomial σ₁ R ord) (f : σ₁ → σ₂)
    (ord₂ : MonomialOrder) :
    (m.rename f ord₂).toMvPoly = MvPolynomial.rename f m.toMvPoly := by
  simp only [Monomial.toMvPoly, Monomial.rename, rename_monomial]
  rw [MonicMonomial.toFinsupp_rename]

/-! ### Polynomial-level equivalence -/

/-- Renaming in `AzMvPolynomial` and converting to `MvPolynomial` gives
    the same result as converting first and renaming in `MvPolynomial`.

    The proof shows that the sort → collapse → filter pipeline in
    `AzMvPolynomial.rename` preserves the polynomial sum. -/
theorem AzMvPolynomial.toMvPoly_rename [DecidableEq R]
    (p : AzMvPolynomial σ₁ R ord) (f : σ₁ → σ₂) (ord₂ : MonomialOrder) :
    (p.rename f ord₂).toMvPoly = MvPolynomial.rename f p.toMvPoly := by
  -- The rename pipeline is: map rename → mergeSort → collapseMonics → filterMap
  -- Each step preserves the MvPolynomial sum:
  --   • mergeSort is a permutation → same sum
  --   • collapseMonics sums coefficients of equal-monic terms →
  --     monomial s c₁ + monomial s c₂ = monomial s (c₁ + c₂)
  --   • filterMap removes zero coefficients →
  --     monomial s 0 = 0, so dropping it doesn't change the sum
  -- MvPolynomial.rename is a ring hom, so it distributes over the sum.
  -- Step 1: LHS = sum of per-monomial (m.rename f).toMvPoly
  rw [AzMvPolynomial.rename_toMvPoly_eq_sum]
  -- Step 2: RHS: unfold toMvPoly as sum, then distribute rename over it (ring hom)
  rw [AzMvPolynomial.toMvPoly, ← Array.foldl_toList, foldl_add_map_eq_sum,
    map_list_sum (MvPolynomial.rename f)]
  -- Step 3: align both sides (compose maps, beta-reduce)
  simp only [List.map_map, Function.comp_def]
  -- Step 4: reduce to per-monomial equivalence
  simp_rw [Monomial.toMvPoly_rename]

/-- Converting `MvPolynomial.rename f p` to `AzMvPolynomial` gives the same
    result as converting `p` first and then renaming in `AzMvPolynomial`.

    Proved by injectivity of `toMvPoly`: both sides map to `rename f p`
    via `toMvPoly_ofMvPoly` and `toMvPoly_rename`. -/
theorem AzMvPolynomial.ofMvPoly_rename [DecidableEq R]
    (p : MvPolynomial σ₁ R) (f : σ₁ → σ₂) (ord₁ ord₂ : MonomialOrder) :
    (AzMvPolynomial.ofMvPoly (MvPolynomial.rename f p) : AzMvPolynomial σ₂ R ord₂) =
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial σ₁ R ord₁).rename f ord₂ := by
  exact toMvPoly_injective
    (by rw [toMvPoly_ofMvPoly, toMvPoly_rename, toMvPoly_ofMvPoly])
end Azurite
