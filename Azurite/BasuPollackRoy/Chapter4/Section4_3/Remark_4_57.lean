import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_54

/-!
# BPR Remark 4.57: `Her(P, 1)` as a trace form / Newton matrix

Specializing Proposition 4.54 to `Q = 1`: Hermite's quadratic form `Her(P, 1)` is the
quadratic form associating to `f = f₁ + f₂ X + ⋯ + f_p X^{p-1} ∈ A = K[X]/(P)` the
expression `Tr(L_{f²})`. Consequently the `(j+1, k+1)`-th entry of its matrix in the basis
`1, X, …, X^{p-1}` is `Tr(L_{X^{j+k}}) = N_{k+j}`, the `(k+j)`-th Newton sum of `P` — i.e.
`HerMatrix P 1` is the Newton matrix `Newt₀(P)`.
-/

namespace Azurite.BPR.Chapter4

open _root_.Polynomial
open scoped Matrix

section

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- **Remark 4.57.** `Her(P, 1)` is the quadratic form `f ↦ Tr(L_{f²})`: for the
representative `f̃ = ∑ᵢ fᵢ Xⁱ`, `Tr(L_{f̃²}) = Her(P, 1)(f₁, …, f_p)`. (The `Q = 1` case of
Proposition 4.54.) -/
theorem remark_4_57 (P : K[X]) (hP : P.Monic) (f : Fin P.natDegree → K) :
    algebraMap K C (Algebra.trace K (AdjoinRoot P)
        (AdjoinRoot.mk P ((∑ i : Fin P.natDegree, Polynomial.C (f i) * X ^ (i : ℕ)) ^ 2)))
      = Her P 1 (fun i => algebraMap K C (f i)) := by
  have h := proposition_4_54 (C := C) P 1 hP f
  rwa [one_mul] at h

/-- **Remark 4.57 (entry as a trace).** The `(k, j)`-th entry of `HerMatrix P 1` is
`Tr(L_{X^{k+j}})`. (The `Q = 1` case of `herMatrix_eq_trace`.) -/
theorem remark_4_57_entry_trace (P : K[X]) (hP : P.Monic) (k j : Fin P.natDegree) :
    algebraMap K C (Algebra.trace K (AdjoinRoot P)
        (AdjoinRoot.mk P (X ^ ((k : ℕ) + (j : ℕ)))))
      = HerMatrix P 1 k j := by
  have h := herMatrix_eq_trace (C := C) P 1 hP k j
  rwa [one_mul] at h

omit [IsAlgClosed C] in
/-- **Remark 4.57 (entry as a Newton sum).** The `(k, j)`-th entry of `HerMatrix P 1` is the
`(k+j)`-th Newton sum `N_{k+j}` of `P`. Hence `HerMatrix P 1` is the Newton matrix
`Newt₀(P)` (cf. `HerMatrix_one_eq_newtMat`). -/
theorem remark_4_57_entry (P : K[X]) (k j : Fin P.natDegree) :
    HerMatrix P 1 k j = newtonSum (C := C) P ((k : ℕ) + (j : ℕ)) := by
  simp only [HerMatrix, Matrix.of_apply, newtonSum, map_one, one_mul]

end

end Azurite.BPR.Chapter4
