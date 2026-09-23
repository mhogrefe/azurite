/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_6.Theorem_4_97
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# BPR §4.6, Theorem 4.98 (Stickelberger)

For `f ∈ Ā`, the multiplication map `L_f` has trace, determinant and characteristic polynomial
\[
  \mathrm{Tr}(L_f) = \sum_x \mu(x) f(x), \qquad \det(L_f) = \prod_x f(x)^{\mu(x)}, \qquad
  \chi(\mathcal{P}, f, T) = \prod_x (T - f(x))^{\mu(x)},
\]
the sums and products being over the zeros `x ∈ Zer(𝒫, Cᵏ)`. All three follow from Theorem 4.97:
over the algebraically closed field `C` the characteristic polynomial splits, so its trace and
determinant are the sum and product of its roots, and the roots are read off from the factored
characteristic polynomial.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K] [CharZero K]
  {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

/-- **BPR Theorem 4.98 (Stickelberger).** For `f ∈ Ā`, the trace, determinant and characteristic
polynomial of `L_f` are
`Tr(L_f) = ∑_x μ(x) f(x)`, `det(L_f) = ∏_x f(x)^{μ(x)}` and `χ = ∏_x (T − f(x))^{μ(x)}`,
the sums and products ranging over the zeros `x ∈ Zer(𝒫, Cᵏ)`. -/
theorem theorem_4_98 (Ps : Finset (MvPolynomial (Fin k) K))
    (hfin : (zerOfFinset C Ps).Finite) [Module.Finite C (quotPolysExt C Ps)]
    (f : quotPolysExt C Ps) :
    LinearMap.trace C (quotPolysExt C Ps) (mulMapExt C Ps f)
        = ∑ x : hfin.toFinset,
            multiplicityOfZero C Ps x.1 (hfin.mem_toFinset.mp x.2)
              • evalBar C Ps x.1 (hfin.mem_toFinset.mp x.2) f
      ∧ LinearMap.det (mulMapExt C Ps f)
        = ∏ x : hfin.toFinset,
            evalBar C Ps x.1 (hfin.mem_toFinset.mp x.2) f
              ^ multiplicityOfZero C Ps x.1 (hfin.mem_toFinset.mp x.2)
      ∧ LinearMap.charpoly (mulMapExt C Ps f)
        = ∏ x : hfin.toFinset,
            (Polynomial.X - Polynomial.C (evalBar C Ps x.1 (hfin.mem_toFinset.mp x.2) f))
              ^ multiplicityOfZero C Ps x.1 (hfin.mem_toFinset.mp x.2) := by
  classical
  have hchar := theorem_4_97 Ps hfin f
  -- the product of the `(X - f(x))^{μ(x)}` is nonzero, so we may compute its roots
  have hne : (∏ x : hfin.toFinset,
      (Polynomial.X - Polynomial.C (evalBar C Ps x.1 (hfin.mem_toFinset.mp x.2) f))
        ^ multiplicityOfZero C Ps x.1 (hfin.mem_toFinset.mp x.2)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro x _
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  -- over the algebraically closed field `C`, the characteristic polynomial splits
  have hsplit : (LinearMap.charpoly (mulMapExt C Ps f)).Splits := IsAlgClosed.splits _
  -- the roots of `χ` are the `f(x)`, each with multiplicity `μ(x)`
  have hroots : (LinearMap.charpoly (mulMapExt C Ps f)).roots
      = Finset.univ.val.bind (fun x : hfin.toFinset =>
          Multiset.replicate (multiplicityOfZero C Ps x.1 (hfin.mem_toFinset.mp x.2))
            (evalBar C Ps x.1 (hfin.mem_toFinset.mp x.2) f)) := by
    rw [hchar, Polynomial.roots_prod _ Finset.univ hne]
    simp only [Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.nsmul_singleton]
  refine ⟨?_, ?_, hchar⟩
  · -- trace = sum of roots = ∑_x μ(x) f(x)
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hsplit, hroots, Multiset.sum_bind]
    simp only [Multiset.sum_replicate]
    rfl
  · -- det = product of roots = ∏_x f(x)^{μ(x)}
    rw [Module.End.det_eq_prod_roots_charpoly_of_splits hsplit, hroots, Multiset.prod_bind]
    simp only [Multiset.prod_replicate]
    rfl

end Azurite.BPR.Chapter4
