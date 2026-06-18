import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Coeff

/-!
# BPR §4.4.2: coefficient-wise total-degree bound

For the quantitative Nullstellensatz (Theorem 4.83) we must bound the degree, in the variables
`X₁, …, X_{k-1}`, of the coefficients (with respect to the auxiliary `U`) of the resultant
`Res_{X_k}(P₁, R)`. Modelling `Res_{X_k}` as an element of `(MvPolynomial (Fin n) K)[U]` (the
resultant of the Sylvester matrix over that ring), the relevant quantity is:

`CoeffTotalDegreeLE f D` — every `U`-coefficient of `f` has total degree `≤ D` in the `X`
variables. We prove it is preserved by sums, products (degrees add), determinants (degree
`≤ size · D`), and `±1`-scaling — the engine for the `2d²` bound on `Res_{X_k}`.
-/

namespace Azurite.BPR.Chapter4

variable {σ : Type*} {R : Type*} [CommRing R]

/-- Every coefficient of `f ∈ (MvPolynomial σ R)[U]` (with respect to the `Polynomial`
indeterminate `U`) has total degree at most `D` in the `σ` variables. -/
def CoeffTotalDegreeLE (f : Polynomial (MvPolynomial σ R)) (D : ℕ) : Prop :=
  ∀ j, (f.coeff j).totalDegree ≤ D

theorem CoeffTotalDegreeLE.mono {f : Polynomial (MvPolynomial σ R)} {D D' : ℕ}
    (h : CoeffTotalDegreeLE f D) (hD : D ≤ D') : CoeffTotalDegreeLE f D' :=
  fun j => (h j).trans hD

theorem coeffTotalDegreeLE_zero (D : ℕ) :
    CoeffTotalDegreeLE (0 : Polynomial (MvPolynomial σ R)) D := by
  intro j; simp

theorem coeffTotalDegreeLE_one :
    CoeffTotalDegreeLE (1 : Polynomial (MvPolynomial σ R)) 0 := by
  intro j
  rw [Polynomial.coeff_one]
  split <;> simp

theorem CoeffTotalDegreeLE.add {f g : Polynomial (MvPolynomial σ R)} {D : ℕ}
    (hf : CoeffTotalDegreeLE f D) (hg : CoeffTotalDegreeLE g D) :
    CoeffTotalDegreeLE (f + g) D := by
  intro j
  rw [Polynomial.coeff_add]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hf j) (hg j))

theorem CoeffTotalDegreeLE.neg {f : Polynomial (MvPolynomial σ R)} {D : ℕ}
    (hf : CoeffTotalDegreeLE f D) : CoeffTotalDegreeLE (-f) D := by
  intro j
  rw [Polynomial.coeff_neg]
  calc (-(f.coeff j)).totalDegree = ((-1 : R) • f.coeff j).totalDegree := by rw [neg_one_smul]
    _ ≤ (f.coeff j).totalDegree := MvPolynomial.totalDegree_smul_le _ _
    _ ≤ D := hf j

theorem CoeffTotalDegreeLE.mul {f g : Polynomial (MvPolynomial σ R)} {Df Dg : ℕ}
    (hf : CoeffTotalDegreeLE f Df) (hg : CoeffTotalDegreeLE g Dg) :
    CoeffTotalDegreeLE (f * g) (Df + Dg) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro p _
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hf p.1) (hg p.2))

theorem CoeffTotalDegreeLE.units_smul {f : Polynomial (MvPolynomial σ R)} {D : ℕ} (u : ℤˣ)
    (hf : CoeffTotalDegreeLE f D) : CoeffTotalDegreeLE (u • f) D := by
  rcases Int.units_eq_one_or u with hu | hu
  · rw [hu, one_smul]; exact hf
  · rw [hu]; simpa using hf.neg

theorem CoeffTotalDegreeLE.finsetSum {ι : Type*} {s : Finset ι}
    {f : ι → Polynomial (MvPolynomial σ R)} {D : ℕ}
    (hf : ∀ i ∈ s, CoeffTotalDegreeLE (f i) D) : CoeffTotalDegreeLE (∑ i ∈ s, f i) D := by
  classical
  induction s using Finset.induction with
  | empty => simpa using coeffTotalDegreeLE_zero D
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem CoeffTotalDegreeLE.prod {ι : Type*} {s : Finset ι}
    {f : ι → Polynomial (MvPolynomial σ R)} {D : ι → ℕ}
    (hf : ∀ i ∈ s, CoeffTotalDegreeLE (f i) (D i)) :
    CoeffTotalDegreeLE (∏ i ∈ s, f i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using coeffTotalDegreeLE_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The determinant of an `N × N` matrix whose entries all satisfy `CoeffTotalDegreeLE _ D`
satisfies `CoeffTotalDegreeLE _ (N * D)`. -/
theorem CoeffTotalDegreeLE.det {N : ℕ}
    {M : Matrix (Fin N) (Fin N) (Polynomial (MvPolynomial σ R))} {D : ℕ}
    (hM : ∀ i j, CoeffTotalDegreeLE (M i j) D) : CoeffTotalDegreeLE M.det (N * D) := by
  rw [Matrix.det_apply]
  apply CoeffTotalDegreeLE.finsetSum
  intro τ _
  apply CoeffTotalDegreeLE.units_smul
  have hprod : CoeffTotalDegreeLE (∏ i, M (τ i) i) (∑ _i : Fin N, D) :=
    CoeffTotalDegreeLE.prod fun i _ => hM (τ i) i
  refine hprod.mono ?_
  simp [Finset.sum_const, Finset.card_univ]

/-- Each entry of the adjugate of an `N × N` matrix whose entries all satisfy
`CoeffTotalDegreeLE _ D` satisfies `CoeffTotalDegreeLE _ (N * D)`. -/
theorem CoeffTotalDegreeLE.adjugate {N : ℕ}
    {M : Matrix (Fin N) (Fin N) (Polynomial (MvPolynomial σ R))} {D : ℕ}
    (hM : ∀ i j, CoeffTotalDegreeLE (M i j) D) (i j : Fin N) :
    CoeffTotalDegreeLE (Matrix.adjugate M i j) (N * D) := by
  rw [Matrix.adjugate_apply]
  apply CoeffTotalDegreeLE.det
  intro a b
  rw [Matrix.updateRow_apply]
  split
  · rw [Pi.single_apply]
    split
    · exact coeffTotalDegreeLE_one.mono (Nat.zero_le D)
    · exact coeffTotalDegreeLE_zero D
  · exact hM a b

end Azurite.BPR.Chapter4
