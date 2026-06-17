import Azurite.BasuPollackRoy.Chapter4.Section4_3.QuadraticForm
import Azurite.BasuPollackRoy.Chapter4.Section4_1.NewtonMatrix
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_13
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# BPR §4.3.2: Hermite's quadratic form

Let `R` be a real closed field, `D` an ordered integral domain contained in `R`, `K` the
field of fractions of `D`, and `C = R[i]` (an algebraically closed extension). For
`P, Q ∈ D[X]` with `P` monic of degree `p` and `deg Q = q < p`, the **Hermite quadratic
form** `Her(P, Q)` in the `p` variables `f_1, …, f_p` is
`Her(P,Q)(f) = ∑_{x ∈ Zer(P,C)} μ(x) Q(x) (f_1 + f_2 x + ⋯ + f_p x^{p-1})²`,
where `Zer(P,C)` is the set of roots of `P` in `C` and `μ(x)` the multiplicity of `x`.

Expanding the square, `Her(P,Q)` is the quadratic form of the Hankel matrix
`Her_{i,j} = ∑_{x} μ(x) Q(x) x^{i+j-2}` (weighted Newton sums); this is `HerMatrix P Q`,
and the two descriptions agree (`Her_eq_matrix`).

For the bare definition we only need a field extension `C` of `D` in which to take the
roots; the order/real-closed structure of `R` and the choice `C = R[i]` enter the later
results (where `Her(P,Q)` is shown to have coefficients in `K` and its signature is
computed).
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open _root_.Polynomial

section

variable {D : Type*} [CommRing D] {C : Type*} [Field C] [Algebra D C]

/-- The **Hermite matrix** of `(P, Q)`: the `p × p` Hankel matrix whose `(i,j)`-entry is
the weighted Newton sum `∑_{x ∈ Zer(P,C)} μ(x) Q(x) x^{i+j}` (0-indexed, so it realizes
`Her_{i,j} = ∑_x μ(x) Q(x) x^{i+j-2}` in BPR's `1`-indexed convention). -/
noncomputable def HerMatrix (P Q : D[X]) :
    Matrix (Fin P.natDegree) (Fin P.natDegree) C :=
  Matrix.of fun i j => ((P.aroots C).map (fun x => aeval x Q * x ^ ((i : ℕ) + (j : ℕ)))).sum

/-- **Hermite's quadratic form** `Her(P, Q)` in the `p` variables `f_1, …, f_p`:
`Her(P,Q)(f) = ∑_{x ∈ Zer(P,C)} μ(x) Q(x) (f_1 + f_2 x + ⋯ + f_p x^{p-1})²`, the sum over
the roots of `P` in `C` (each counted with multiplicity, via `P.aroots C`). -/
noncomputable def Her (P Q : D[X]) (f : Fin P.natDegree → C) : C :=
  ((P.aroots C).map
    (fun x => aeval x Q * (∑ k : Fin P.natDegree, f k * x ^ (k : ℕ)) ^ 2)).sum

/-- **`Her(P, Q)` is the quadratic form of the Hankel matrix `HerMatrix P Q`**: expanding
the square `(∑_k f_k x^{k-1})²` shows `Her(P,Q)(f) = f · HerMatrix(P,Q) · fᵗ`. -/
theorem Her_eq_matrix (P Q : D[X]) (f : Fin P.natDegree → C) :
    Her P Q f = f ⬝ᵥ HerMatrix P Q *ᵥ f := by
  set g : C → C := fun x => aeval x Q with hg
  -- The common middle form.
  have key : ∀ i j : Fin P.natDegree,
      ((P.aroots C).map (fun x => g x * f i * f j * x ^ ((i : ℕ) + (j : ℕ)))).sum
        = f i * f j * ((P.aroots C).map (fun x => g x * x ^ ((i : ℕ) + (j : ℕ)))).sum := by
    intro i j
    rw [← Multiset.sum_map_mul_left]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro x _
    ring
  -- RHS unfolds to the double sum.
  have rhs : f ⬝ᵥ HerMatrix P Q *ᵥ f
      = ∑ i : Fin P.natDegree, ∑ j : Fin P.natDegree,
          f i * f j * ((P.aroots C).map (fun x => g x * x ^ ((i : ℕ) + (j : ℕ)))).sum := by
    simp only [dotProduct, Matrix.mulVec, HerMatrix, Matrix.of_apply, hg]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  -- LHS unfolds to the same double sum.
  have lhs : Her P Q f
      = ∑ i : Fin P.natDegree, ∑ j : Fin P.natDegree,
          f i * f j * ((P.aroots C).map (fun x => g x * x ^ ((i : ℕ) + (j : ℕ)))).sum := by
    rw [Her]
    have expand : ∀ x : C,
        g x * (∑ k : Fin P.natDegree, f k * x ^ (k : ℕ)) ^ 2
          = ∑ i : Fin P.natDegree, ∑ j : Fin P.natDegree,
              g x * f i * f j * x ^ ((i : ℕ) + (j : ℕ)) := by
      intro x
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [pow_add]
      ring
    rw [Multiset.map_congr rfl (fun x _ => expand x)]
    rw [Multiset.sum_map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Multiset.sum_map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact key i j
  rw [lhs, rhs]

/-- **Bilinear expansion of `Her(P, Q)`** (BPR's first display):
`Her(P,Q)(f) = ∑_{k,j} (∑_{x} μ(x) Q(x) x^{k+j-2}) f_k f_j`, the double sum of the Hankel
entries against `f_k f_j`. -/
theorem Her_apply (P Q : D[X]) (f : Fin P.natDegree → C) :
    Her P Q f = ∑ i : Fin P.natDegree, ∑ j : Fin P.natDegree, HerMatrix P Q i j * f i * f j := by
  rw [Her_eq_matrix, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end

section Newton

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C]

/-- **When `Q = 1`, the Hermite matrix is the Newton matrix `Newt₀(P)`.** Its `(i,j)`-entry
is the Newton sum `N_{i+j}(P)` (Definition 4.7). -/
theorem HerMatrix_one_eq_newtMat (P : K[X]) :
    (HerMatrix P 1 : Matrix (Fin P.natDegree) (Fin P.natDegree) C) = newtMat P P.natDegree := by
  ext i j
  simp only [HerMatrix, Matrix.of_apply, newtMat, newtonSum, map_one, one_mul]

/-- **`Her(P, 1)` is the quadratic form of `Newt₀(P)`** (BPR's second display):
`Her(P,1)(f) = ∑_{k,j} N_{k+j-2}(P) f_k f_j`. -/
theorem Her_one_apply (P : K[X]) (f : Fin P.natDegree → C) :
    Her P 1 f = ∑ i : Fin P.natDegree, ∑ j : Fin P.natDegree,
      newtonSum P ((i : ℕ) + (j : ℕ)) * f i * f j := by
  rw [Her_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show HerMatrix P 1 i j = newtMat P P.natDegree i j from
    congrFun (congrFun (HerMatrix_one_eq_newtMat P) i) j, newtMat, Matrix.of_apply]

end Newton

section Coefficients

variable {D : Type*} [CommRing D] {C : Type*} [Field C] [IsAlgClosed C] [Algebra D C]

open MvPolynomial in
/-- A `Fin P.natDegree` enumeration of the roots (with multiplicity) of a monic `P` over the
algebraically closed field `C`: there is `r : Fin P.natDegree → C` whose multiset of
values is exactly `P.aroots C`. -/
private theorem exists_root_enum (P : D[X]) (hP : P.Monic) :
    ∃ r : Fin P.natDegree → C,
      (Finset.univ : Finset (Fin P.natDegree)).val.map r = P.aroots C := by
  have hcard : (P.aroots C).card = P.natDegree :=
    IsAlgClosed.card_aroots_eq_natDegree_of_isUnit_leadingCoeff
      (by rw [hP.leadingCoeff]; exact isUnit_one)
  set l := (P.aroots C).toList with hl
  have hllen : l.length = P.natDegree := by rw [hl, Multiset.length_toList, hcard]
  refine ⟨fun i => l.get (Fin.cast hllen.symm i), ?_⟩
  rw [Finset.val_univ_fin, Multiset.map_coe, ← List.ofFn_eq_map]
  rw [show (List.ofFn fun i : Fin P.natDegree => l.get (Fin.cast hllen.symm i)) = l from by
    rw [← List.ofFn_congr hllen (List.get l), List.ofFn_get]]
  exact Multiset.coe_toList _

open MvPolynomial in
/-- Each elementary symmetric function (`Multiset.esymm`) of the roots of a monic `P` over
`C` lies in `(⊥ : Subalgebra D C)`, i.e. in the image of `algebraMap D C`, by Vieta's
formulas: it is (up to sign) a coefficient of `P`. -/
private theorem esymm_aroots_mem_bot (P : D[X]) (hP : P.Monic) (k : ℕ) :
    (P.aroots C).esymm k ∈ (⊥ : Subalgebra D C) := by
  set φ := algebraMap D C with hφ
  have hmonic : (P.map φ).Monic := hP.map φ
  have hcard : (P.aroots C).card = P.natDegree :=
    IsAlgClosed.card_aroots_eq_natDegree_of_isUnit_leadingCoeff
      (by rw [hP.leadingCoeff]; exact isUnit_one)
  -- `P.map φ = ∏_{x ∈ aroots} (X - C x)`.
  have haroots : P.aroots C = (P.map φ).roots := by rw [Polynomial.aroots]
  have hcardmap : (P.map φ).roots.card = (P.map φ).natDegree := by
    rw [← haroots, hcard, hP.natDegree_map]
  have hprod : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (P.map φ).roots).prod
      = P.map φ :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcardmap
  rcases le_or_gt k P.natDegree with hk | hk
  · -- coefficient at `P.natDegree - k` is `(-1)^k · esymm k`.
    have hle : P.natDegree - k ≤ (P.map φ).roots.card := by
      rw [hcardmap, hP.natDegree_map]; omega
    have hcoeff := Multiset.prod_X_sub_C_coeff (P.map φ).roots hle
    rw [hprod] at hcoeff
    have hcardsub : (P.map φ).roots.card - (P.natDegree - k) = k := by
      rw [hcardmap, hP.natDegree_map]; omega
    rw [hcardsub] at hcoeff
    -- so `esymm k = (-1)^k · (P.map φ).coeff (p-k) = (-1)^k · φ (P.coeff (p-k))`.
    have hesymm : ((P.map φ).roots).esymm k = (-1) ^ k * (P.map φ).coeff (P.natDegree - k) := by
      rw [hcoeff, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    rw [← haroots] at hesymm
    rw [hesymm, Polynomial.coeff_map]
    exact Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (neg_mem (Subalgebra.one_mem _)) k)
      (Algebra.mem_bot.mpr ⟨P.coeff (P.natDegree - k), rfl⟩)
  · -- `k` exceeds the number of roots: `esymm k = 0 ∈ ⊥`.
    rw [Multiset.esymm, Multiset.powersetCard_eq_empty k (by rw [hcard]; omega),
      Multiset.map_zero, Multiset.sum_zero]
    exact Subalgebra.zero_mem _

/-- **`Her(P, Q)` has coefficients in `D` (a fortiori in `K = Frac D`).** Each entry of
the Hankel matrix `HerMatrix P Q` — the weighted Newton sum `∑_{x} μ(x) Q(x) x^{i+j}`,
which is symmetric in the roots of the monic `P` — is a polynomial (with coefficients from
`P` and `Q`) in the elementary symmetric functions of the roots, i.e. in the coefficients
of `P`, by Proposition 2.13 (the fundamental theorem of symmetric polynomials). Hence it
lies in the image of `D`. -/
theorem HerMatrix_mem_range (P Q : D[X]) (hP : P.Monic) (i j : Fin P.natDegree) :
    HerMatrix P Q i j ∈ (algebraMap D C).range := by
  classical
  -- Reduce membership in the range of `algebraMap D C` to membership in `⊥`.
  rw [RingHom.mem_range]
  rw [show (∃ y, algebraMap D C y = HerMatrix P Q i j)
        ↔ HerMatrix P Q i j ∈ (⊥ : Subalgebra D C) from by rw [Algebra.mem_bot]; rfl]
  -- Abbreviations (kept as plain locals so the binder types `Fin P.natDegree` are untouched).
  set m : ℕ := (i : ℕ) + (j : ℕ) with hm
  -- Enumerate the roots of `P` over `C` as a tuple `r : Fin P.natDegree → C`.
  obtain ⟨r, hr⟩ := exists_root_enum (C := C) P hP
  -- The symmetric `MvPolynomial` whose evaluation at `r` is the Hankel entry.
  set W : MvPolynomial (Fin P.natDegree) D :=
    ∑ a : Fin P.natDegree, Polynomial.aeval (MvPolynomial.X a) Q * (MvPolynomial.X a) ^ m with hW
  -- `aeval r W` is exactly the Hankel entry.
  have hWeval : MvPolynomial.aeval r W = HerMatrix P Q i j := by
    rw [hW, map_sum, HerMatrix, Matrix.of_apply, ← hr, Multiset.map_map]
    rw [Finset.sum_eq_multiset_sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro a _
    rw [Function.comp_apply, map_mul, map_pow, MvPolynomial.aeval_X,
      ← Polynomial.aeval_algHom_apply (MvPolynomial.aeval r) (MvPolynomial.X a) Q,
      MvPolynomial.aeval_X]
  -- `W` is symmetric.
  have hWsymm : W.IsSymmetric := by
    intro σ
    rw [hW, map_sum]
    rw [← Equiv.sum_comp σ
      (fun a => Polynomial.aeval (MvPolynomial.X a) Q * (MvPolynomial.X a) ^ m)]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [map_mul, map_pow, MvPolynomial.rename_X,
      MvPolynomial.rename_polynomial_aeval_X]
  -- Apply the fundamental theorem of symmetric polynomials.
  obtain ⟨R, hR⟩ := Azurite.BPR.proposition_2_13 W hWsymm
  -- Evaluate: `entry = aeval r W = aeval (fun k => aeval r (esymm (k+1))) R`.
  rw [← hWeval, ← hR, MvPolynomial.comp_aeval_apply]
  -- Each argument lies in `⊥`, so the evaluation does too.
  have hargs : ∀ k : Fin P.natDegree,
      (MvPolynomial.aeval r) (MvPolynomial.esymm (Fin P.natDegree) D (↑k + 1)) ∈ (⊥ : Subalgebra D C) := by
    intro k
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hr]
    exact esymm_aroots_mem_bot P hP _
  have : (MvPolynomial.aeval fun k : Fin P.natDegree =>
      (MvPolynomial.aeval r) (MvPolynomial.esymm (Fin P.natDegree) D (↑k + 1))) R
      ∈ (⊥ : Subalgebra D C) := by
    have hsub : Set.range (fun k : Fin P.natDegree =>
        (MvPolynomial.aeval r) (MvPolynomial.esymm (Fin P.natDegree) D (↑k + 1)))
        ⊆ (↑(⊥ : Subalgebra D C) : Set C) := by
      rintro _ ⟨k, rfl⟩; exact hargs k
    have hmem := AlgHom.mem_range_self
      (MvPolynomial.aeval fun k : Fin P.natDegree =>
        (MvPolynomial.aeval r) (MvPolynomial.esymm (Fin P.natDegree) D (↑k + 1))) R
    rw [MvPolynomial.aeval_range] at hmem
    exact (Algebra.adjoin_le hsub) hmem
  exact this

end Coefficients

end Azurite.BPR.Chapter4
