import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization

/-!
# Example 1.2

$\Phi = (\exists Y)(XY - 1 = 0)$ and $\Psi = (X \ne 0)$ are formulas
over $\mathbb{Z}$ with $\operatorname{Free}(\Phi) =
\operatorname{Free}(\Psi) = \{X\}$. $\Psi$ is quantifier-free, and
$\Phi$ and $\Psi$ are $C$-equivalent for any algebraically closed
field $C$.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

section Example_1_2

open Formula

/-- Φ = ∃Y, XY - 1 = 0 (0 = X, 1 = Y). -/
noncomputable def Φ_ex : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  .exists_ 1 (eq_zero (X 0 * X 1 - 1))

/-- Ψ = X ≠ 0. -/
noncomputable def Ψ_ex : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  Formula.ne_zero (X 0)

theorem freeVars_Φ : Φ_ex.freeVars = {0} := by
  simp only [Φ_ex, freeVars, eq_zero, FieldAtom.eqZero, FieldAtom.vars]
  ext x; fin_cases x
  · -- x = 0
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨fun _ => rfl, fun _ =>
      ⟨(MvPolynomial.mem_vars_iff_mem_support _).mpr
        ⟨Finsupp.single 0 1 + Finsupp.single 1 1,
          MvPolynomial.mem_support_iff.mpr (by
            simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_one]
            rw [show MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 =
              MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (1 : ℤ)
              from by simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
            simp only [MvPolynomial.coeff_monomial,
              if_neg (show (0 : (Fin 2) →₀ ℕ) ≠ Finsupp.single 0 1 + Finsupp.single 1 1
                from by intro h; have := DFunLike.congr_fun h 0; simp at this)]
            norm_num),
          by simp [Finsupp.mem_support_iff]⟩, by decide⟩⟩
  · -- x = 1
    simp [Finset.mem_sdiff, Finset.mem_singleton]

theorem freeVars_Ψ : Ψ_ex.freeVars = {0} := by
  simp only [Ψ_ex, ne_zero, freeVars, FieldAtom.neZero, FieldAtom.vars,
    MvPolynomial.vars_X]

theorem freeVars_eq : Φ_ex.freeVars = Ψ_ex.freeVars := by
  rw [freeVars_Φ, freeVars_Ψ]

theorem Ψ_qf : Ψ_ex.IsQuantifierFree := trivial

variable {C : Type*} [Field C]

/-- Example 1.2: Φ and Ψ are C-equivalent. -/
theorem example_1_2 :
    Formula.CEquiv (C := C) Φ_ex Ψ_ex := by
  unfold CEquiv Φ_ex Ψ_ex ne_zero realization
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc⟩
    simp only [realization_eq_zero, Set.mem_setOf_eq] at *
    simp only [map_sub, map_mul, map_one, MvPolynomial.aeval_X] at *
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] at hc
    intro h0
    simp only [FieldAtom.neZero, MvPolynomial.aeval_X] at h0
    rw [h0, zero_mul, zero_sub] at hc
    exact one_ne_zero (neg_eq_zero.mp hc)
  · intro h
    simp only [realization_eq_zero, Set.mem_setOf_eq] at *
    simp only [map_sub, map_mul, map_one, MvPolynomial.aeval_X] at *
    refine ⟨(y 0)⁻¹, ?_⟩
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    simp only [FieldAtom.neZero, MvPolynomial.aeval_X] at h
    rw [mul_inv_cancel₀ h, sub_self]

end Example_1_2

end Azurite.BPR
