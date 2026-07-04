import Azurite.BasuPollackRoy.Chapter1.Section1_1.Notation1_1

/-!
# Exercise 1.1

An algebraic subset of `C` (i.e. `C¹`) is either finite or all of `C`.

Proof outline: an algebraic subset is `Zer(poly_set)` for some finite `poly_set`.
If every polynomial in `poly_set` is zero, the zero set is all of `C`. Otherwise
some `P₀ ∈ poly_set` is nonzero; then `Zer(poly_set) ⊆ {x | P₀(x) = 0}`, and the
roots of a nonzero univariate polynomial are finite (Mathlib's
`Polynomial.finite_setOf_isRoot`). The transfer from `MvPolynomial (Fin 1) C` to
`C[X]` is via `mvPolyFinOneEquiv` below.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {C : Type*} [Field C] [IsAlgClosed C]

/-- The algebra equivalence MvPolynomial (Fin 1) C ≃ₐ[C] C[X]. -/
noncomputable def mvPolyFinOneEquiv :
    MvPolynomial (Fin 1) C ≃ₐ[C] C[X] :=
  (finSuccEquiv C 0).trans
    (Polynomial.mapAlgEquiv (isEmptyAlgEquiv C (Fin 0)))

omit [IsAlgClosed C] in
/-- MvPolynomial.eval at a constant function factors through
    the one-variable equivalence. -/
theorem eval_eq_polynomial_eval
    (P : MvPolynomial (Fin 1) C) (c : C) :
    MvPolynomial.eval (fun _ => c) P =
      Polynomial.eval c (mvPolyFinOneEquiv P) := by
  have heq : (fun _ : Fin 1 => c) = Fin.cons c Fin.elim0 :=
    funext (fun i => by fin_cases i; rfl)
  rw [heq, MvPolynomial.eval_eq_eval_mv_eval']
  congr 1
  simp only [mvPolyFinOneEquiv, AlgEquiv.trans_apply]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => i.elim0)
  simp only [MvPolynomial.eval_C]
  rw [show ((MvPolynomial.isEmptyAlgEquiv C (Fin 0) : MvPolynomial (Fin 0) C ≃ₐ[C] C)
        : MvPolynomial (Fin 0) C →ₐ[C] C).toRingHom (MvPolynomial.C r)
      = (MvPolynomial.isEmptyAlgEquiv C (Fin 0)) (MvPolynomial.C r) from rfl,
    ← MvPolynomial.isEmptyAlgEquiv_symm_apply (R := C) (σ := Fin 0) r,
    AlgEquiv.apply_symm_apply]

omit [IsAlgClosed C] in
/-- Exercise 1.1: An algebraic subset of C is either finite
    or all of C. -/
theorem exercise_1_1 (V : Set (Fin 1 → C))
    (hV : IsAlgebraicSet V) :
    V.Finite ∨ V = Set.univ := by
  obtain ⟨poly_set, rfl⟩ := hV
  by_cases h : ∀ P ∈ poly_set, P = 0
  · -- All polynomials are zero ⟹ Zer poly_set = Cᵏ
    right
    ext x
    simp only [Zer, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro P hP; rw [h P hP]; simp
  · -- Some P₀ ∈ poly_set is nonzero ⟹ Zer poly_set ⊆ roots(P₀)
    push Not at h
    obtain ⟨P₀, hP₀mem, hP₀ne⟩ := h
    left
    apply Set.Finite.subset (s := { x : Fin 1 → C |
        MvPolynomial.eval x P₀ = 0})
    · -- {x | eval x P₀ = 0} is finite via transfer to C[X]
      let e : (Fin 1 → C) ≃ C := Equiv.funUnique (Fin 1) C
      have hpne : mvPolyFinOneEquiv P₀ ≠ 0 :=
        fun h => hP₀ne (mvPolyFinOneEquiv.injective (by rw [h, map_zero]))
      rw [show { x : Fin 1 → C | MvPolynomial.eval x P₀ = 0} =
          e.symm '' { c : C | Polynomial.eval c (mvPolyFinOneEquiv P₀) = 0}
        from by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_image, e, Equiv.funUnique]
        constructor
        · intro hx
          exact ⟨x 0,
            by rwa [← eval_eq_polynomial_eval, show (fun (_ : Fin 1) => x 0) = x from
              _root_.funext fun ⟨i, hi⟩ => by simp [show i = 0 by omega]],
            _root_.funext fun ⟨i, hi⟩ => by simp [show i = 0 by omega]⟩
        · rintro ⟨c, hc, rfl⟩
          show MvPolynomial.eval _ P₀ = 0
          rw [← eval_eq_polynomial_eval] at hc
          exact hc]
      exact (Polynomial.finite_setOf_isRoot hpne).image _
    · intro x hx; exact hx P₀ hP₀mem

end Azurite.BPR
