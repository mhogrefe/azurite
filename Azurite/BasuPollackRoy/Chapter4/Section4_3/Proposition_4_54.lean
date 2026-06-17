import Azurite.BasuPollackRoy.Chapter4.Section4_3.Hermite
import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_55

/-!
# BPR Proposition 4.54: Hermite's quadratic form as a trace

Hermite's quadratic form `Her(P, Q)` is the quadratic form associating to a representative
`f = f₁ + f₂ X + ⋯ + f_p X^{p-1} ∈ A = K[X]/(P)` the expression `Tr(L_{Q f²})`, the trace
of multiplication by the class of `Q f²` on `A`.

The proof is immediate from Proposition 4.55: `Tr(L_{Q X^{k+j}})` is the `(k, j)` entry of
the Hankel matrix `HerMatrix P Q` (its value `∑_x μ(x) Q(x) x^{k+j}`), and summing against
`f_k f_j` (equivalently, evaluating `Her(P, Q)` at the coefficient vector) gives
`Tr(L_{Q f²})`.
-/

namespace Azurite.BPR.Chapter4

open _root_.Polynomial
open scoped Matrix

section

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- **Proposition 4.54 (matrix entries).** `Tr(L_{Q X^{k+j}})` is the `(k, j)`-th entry of
the symmetric matrix `HerMatrix P Q` associated to Hermite's quadratic form in the basis
`1, X, …, X^{p-1}` (its value `∑_{x ∈ Zer(P,C)} μ(x) Q(x) x^{k+j}`). -/
theorem herMatrix_eq_trace (P Q : K[X]) (hP : P.Monic) (k j : Fin P.natDegree) :
    algebraMap K C (Algebra.trace K (AdjoinRoot P)
        (AdjoinRoot.mk P (Q * X ^ ((k : ℕ) + (j : ℕ)))))
      = HerMatrix P Q k j := by
  rw [proposition_4_55 P hP, HerMatrix, Matrix.of_apply]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun x _ => ?_)
  rw [map_mul, map_pow, aeval_X]

/-- **Proposition 4.54.** Hermite's quadratic form `Her(P, Q)` is the quadratic form
associating to `f = f₁ + f₂ X + ⋯ + f_p X^{p-1} ∈ A = K[X]/(P)` the expression
`Tr(L_{Q f²})`: for the representative `f̃ = ∑ᵢ fᵢ Xⁱ`,
`Tr(L_{Q f̃²}) = Her(P, Q)(f₁, …, f_p)`. -/
theorem proposition_4_54 (P Q : K[X]) (hP : P.Monic) (f : Fin P.natDegree → K) :
    algebraMap K C (Algebra.trace K (AdjoinRoot P)
        (AdjoinRoot.mk P (Q * (∑ i : Fin P.natDegree, Polynomial.C (f i) * X ^ (i : ℕ)) ^ 2)))
      = Her P Q (fun i => algebraMap K C (f i)) := by
  rw [proposition_4_55 P hP, Her]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun x _ => ?_)
  have hfx : aeval x (∑ i : Fin P.natDegree, Polynomial.C (f i) * X ^ (i : ℕ))
      = ∑ k : Fin P.natDegree, algebraMap K C (f k) * x ^ (k : ℕ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X]
  rw [map_mul, map_pow, hfx]

end

end Azurite.BPR.Chapter4
