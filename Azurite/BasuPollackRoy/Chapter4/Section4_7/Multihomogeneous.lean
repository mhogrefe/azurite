import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators

/-!
# BPR §4.7: multihomogeneous polynomials

The variables are grouped into `m` blocks, the `i`-th block consisting of `k i + 1` variables
`X_{i,0}, …, X_{i,k_i}` — so the variable index type is the sigma type `(i : Fin m) × Fin (k i + 1)`
(block `i` carries exactly the `k_i + 1` homogeneous coordinates of `ℙ_{k_i}`).

A polynomial `P` is **multihomogeneous of multidegree `(d_1, …, d_m)`** if it is homogeneous of
degree `d_i` in the `i`-th block of variables for every `i`: every monomial of `P` has total degree
`d_i` in the variables `X_{i,0}, …, X_{i,k_i}`. For example, `T (X² + Y²)` (blocks `{T}` and
`{X, Y}`) is multihomogeneous of multidegree `(1, 2)`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {A : Type*} [CommSemiring A] {m : ℕ} {k : Fin m → ℕ}

/-- **BPR §4.7 (multihomogeneous polynomial).** `P ∈ A[X_{1,0}, …, X_{m,k_m}]` is *multihomogeneous
of multidegree `d = (d_1, …, d_m)`* if it is homogeneous of degree `d i` in the `i`-th block of
variables for every `i ≤ m`: each monomial `c` in the support of `P` has block-`i` total degree
`∑_{j} c(i, j) = d i`. -/
def IsMultihomogeneous (P : MvPolynomial ((i : Fin m) × Fin (k i + 1)) A) (d : Fin m → ℕ) : Prop :=
  ∀ i : Fin m, ∀ c ∈ P.support, ∑ j : Fin (k i + 1), c ⟨i, j⟩ = d i

/-- A single variable `X_{i₀,j₀}` is multihomogeneous of multidegree `e_{i₀}` (degree `1` in its
own block, `0` in every other block). -/
theorem isMultihomogeneous_X [Nontrivial A] (s : (i : Fin m) × Fin (k i + 1)) :
    IsMultihomogeneous (X s : MvPolynomial ((i : Fin m) × Fin (k i + 1)) A)
      (fun i => if i = s.1 then 1 else 0) := by
  intro i c hc
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hc
  subst hc
  obtain ⟨si, sj⟩ := s
  dsimp only
  by_cases hi : i = si
  · subst hi
    rw [if_pos rfl, Finset.sum_eq_single sj]
    · exact Finsupp.single_eq_same
    · intro j _ hj
      exact Finsupp.single_eq_of_ne fun h => hj (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    · intro h; exact absurd (Finset.mem_univ sj) h
  · rw [if_neg hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact Finsupp.single_eq_of_ne fun h => hi (Sigma.mk.inj_iff.mp h).1

/-- A product of multihomogeneous polynomials is multihomogeneous, with multidegrees adding. -/
theorem IsMultihomogeneous.mul {P Q : MvPolynomial ((i : Fin m) × Fin (k i + 1)) A}
    {d e : Fin m → ℕ} (hP : IsMultihomogeneous P d) (hQ : IsMultihomogeneous Q e) :
    IsMultihomogeneous (P * Q) (d + e) := by
  intro i c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hc)
  simp only [Finsupp.add_apply]
  rw [Finset.sum_add_distrib, hP i a ha, hQ i b hb, Pi.add_apply]

/-- A sum of two multihomogeneous polynomials of the same multidegree is multihomogeneous of that
multidegree. -/
theorem IsMultihomogeneous.add {P Q : MvPolynomial ((i : Fin m) × Fin (k i + 1)) A}
    {d : Fin m → ℕ} (hP : IsMultihomogeneous P d) (hQ : IsMultihomogeneous Q d) :
    IsMultihomogeneous (P + Q) d := by
  intro i c hc
  rcases Finset.mem_union.mp (MvPolynomial.support_add hc) with h | h
  · exact hP i c h
  · exact hQ i c h

/-- **Scaling a multihomogeneous polynomial.** If `P` is multihomogeneous of multidegree `d`, then
rescaling the `i`-th block of variables by a scalar `c i` multiplies the value of `P` by
`∏ i, (c i) ^ (d i)`. This is the algebraic core of the well-definedness of `P(x) = 0` over a
product of projective spaces. -/
theorem IsMultihomogeneous.eval_blockScale {P : MvPolynomial ((i : Fin m) × Fin (k i + 1)) A}
    {d : Fin m → ℕ} (hP : IsMultihomogeneous P d) (c : Fin m → A)
    (v : (i : Fin m) × Fin (k i + 1) → A) :
    MvPolynomial.eval (fun s => c s.1 * v s) P
      = (∏ i, c i ^ d i) * MvPolynomial.eval v P := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hsplit : (∏ s, (c s.1 * v s) ^ u s) = (∏ i, c i ^ d i) * ∏ s, v s ^ u s := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun i _ => ?_
    show (∏ j : Fin (k i + 1), c i ^ u ⟨i, j⟩) = c i ^ d i
    rw [Finset.prod_pow_eq_pow_sum, hP i u hu]
  rw [hsplit]; ring

/-- **Example.** With two blocks `{T}` and `{X, Y}`, the polynomial `T (X² + Y²)` is
multihomogeneous of multidegree `(1, 2)`: homogeneous of degree `1` in `T` and of degree `2` in
`{X, Y}`. -/
example {A : Type*} [CommSemiring A] [Nontrivial A] :
    IsMultihomogeneous
      (X ⟨0, 0⟩ * (X ⟨1, 0⟩ ^ 2 + X ⟨1, 1⟩ ^ 2) :
        MvPolynomial ((i : Fin 2) × Fin ((![0, 1] : Fin 2 → ℕ) i + 1)) A)
      ![1, 2] := by
  let σ := (i : Fin 2) × Fin ((![0, 1] : Fin 2 → ℕ) i + 1)
  rw [pow_two, pow_two]
  have h := (isMultihomogeneous_X (A := A) (⟨0, 0⟩ : σ)).mul
    (((isMultihomogeneous_X (A := A) (⟨1, 0⟩ : σ)).mul
        (isMultihomogeneous_X (A := A) (⟨1, 0⟩ : σ))).add
      ((isMultihomogeneous_X (A := A) (⟨1, 1⟩ : σ)).mul
        (isMultihomogeneous_X (A := A) (⟨1, 1⟩ : σ))))
  convert h using 1
  funext i; fin_cases i <;> decide

end Azurite.BPR.Chapter4
