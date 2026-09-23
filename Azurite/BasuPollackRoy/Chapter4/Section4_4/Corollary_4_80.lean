import Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_78
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# BPR Corollary 4.80: Homogeneous Hilbert's Nullstellensatz

Let `𝒫 = {P₁, …, P_s}` be homogeneous with `deg(Pᵢ) = dᵢ`, and `P` homogeneous of degree `p`
vanishing on the common zeros of `𝒫` in `C^k` (`K` of characteristic zero, `C` algebraically
closed, `0 < p`). Then there are `n` and homogeneous `Hᵢ` of degree `cᵢ = np - dᵢ` with
`P^n = ∑ᵢ Hᵢ Pᵢ` and `np = cᵢ + dᵢ`.

The Hᵢ are the degree-`np` homogeneous components of the coefficients in the (ordinary)
Nullstellensatz combination `P^n = ∑ Bᵢ Pᵢ` (Theorem 4.78), `n` chosen large enough that
`np ≥ dᵢ`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {K : Type*} [Field K]

/-- Homogeneous component of a product with a homogeneous factor: if `Q` is homogeneous of degree
`e` and `e ≤ m`, then the degree-`m` component of `B * Q` is `(degree-(m-e) component of B) * Q`. -/
theorem homogeneousComponent_mul_homogeneous {k : ℕ} {R : Type*} [CommRing R]
    {Q : MvPolynomial (Fin k) R} {e : ℕ} (hQ : Q.IsHomogeneous e) (m : ℕ) (hm : e ≤ m)
    (B : MvPolynomial (Fin k) R) :
    homogeneousComponent m (B * Q) = homogeneousComponent (m - e) B * Q := by
  conv_lhs => rw [← sum_homogeneousComponent B, Finset.sum_mul, map_sum]
  rw [Finset.sum_eq_single (m - e)]
  · -- the surviving term `j = m - e`
    have hh : (homogeneousComponent (m - e) B * Q).IsHomogeneous m := by
      have := (homogeneousComponent_isHomogeneous (m - e) B).mul hQ
      rwa [Nat.sub_add_cancel hm] at this
    rw [homogeneousComponent_of_mem hh, ite_eq_left rfl]
  · -- terms `j ≠ m - e` vanish
    intro j _ hjne
    have hh : (homogeneousComponent j B * Q).IsHomogeneous (j + e) :=
      (homogeneousComponent_isHomogeneous j B).mul hQ
    rw [homogeneousComponent_of_mem hh, ite_eq_right (by omega)]
  · -- `m - e ∉ range` means `homogeneousComponent (m - e) B = 0`
    intro hnot
    rw [Finset.mem_range, not_lt] at hnot
    rw [homogeneousComponent_eq_zero (m - e) B (by omega), zero_mul, map_zero]

/-- **BPR Corollary 4.80 (Homogeneous Hilbert's Nullstellensatz).** For homogeneous `Pᵢ` of degree
`dᵢ` and homogeneous `P` of degree `p > 0` vanishing on their common zeros in `C^k`, there are `n`
and homogeneous `Hᵢ` of degree `np - dᵢ` with `np = (np - dᵢ) + dᵢ` and `P^n = ∑ᵢ Hᵢ Pᵢ`. -/
theorem corollary_4_80 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
    {k s : ℕ} (Ps : Fin s → MvPolynomial (Fin k) K) (d : Fin s → ℕ)
    (hPshom : ∀ i, (Ps i).IsHomogeneous (d i)) (P : MvPolynomial (Fin k) K) (p : ℕ) (hp : 0 < p)
    (hPhom : P.IsHomogeneous p)
    (hvanish : ∀ x : Fin k → C, (∀ i, MvPolynomial.aeval x (Ps i) = 0) →
      MvPolynomial.aeval x P = 0) :
    ∃ (n : ℕ) (H : Fin s → MvPolynomial (Fin k) K),
      (∀ i, (H i).IsHomogeneous (n * p - d i)) ∧ (∀ i, d i ≤ n * p) ∧
        P ^ n = ∑ i, H i * Ps i := by
  classical
  set Pset : Finset (MvPolynomial (Fin k) K) := Finset.univ.image Ps with hPset
  -- `P` vanishes on `Zer(Pset)`.
  have hvanish' : ∀ x ∈ zerOfFinset C Pset, MvPolynomial.aeval x P = 0 := by
    intro x hx
    exact hvanish x fun i => hx (Ps i) (by rw [hPset]; exact Finset.mem_image_of_mem Ps (Finset.mem_univ i))
  -- Ordinary Nullstellensatz: `P^{n₀} ∈ Ideal(Pset)`.
  obtain ⟨n₀, hn₀⟩ := theorem_4_78 Pset P hvanish'
  -- Rewrite the ideal as the span of the range and extract the combination.
  have hcoe : (↑Pset : Set (MvPolynomial (Fin k) K)) = Set.range Ps := by
    rw [hPset, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [idealOfPolys, hcoe] at hn₀
  obtain ⟨B, hB⟩ := Ideal.mem_span_range_iff_exists_fun.mp hn₀
  have hB2 : ∑ i, B i * Ps i = P ^ n₀ := by simpa [smul_eq_mul] using hB
  -- Choose `n` large: `n ≥ n₀` and `n * p ≥ dᵢ`.
  set n : ℕ := max n₀ (Finset.univ.sup d) with hn
  have hn₀le : n₀ ≤ n := le_max_left _ _
  have hd : ∀ i, d i ≤ n * p := fun i =>
    le_trans (le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _))
      (Nat.le_mul_of_pos_right n hp)
  -- `P^n = ∑ (P^{n-n₀} Bᵢ) Pᵢ`.
  set B' : Fin s → MvPolynomial (Fin k) K := fun i => P ^ (n - n₀) * B i with hB'
  have hsum : P ^ n = ∑ i, B' i * Ps i := by
    have hpow : P ^ n = P ^ (n - n₀) * P ^ n₀ := by rw [← pow_add, Nat.sub_add_cancel hn₀le]
    rw [hpow, ← hB2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hB']; ring
  -- The homogeneous components.
  refine ⟨n, fun i => homogeneousComponent (n * p - d i) (B' i), fun i => ?_, hd, ?_⟩
  · exact homogeneousComponent_isHomogeneous _ _
  · -- `P^n` is its own degree-`np` component; project the sum.
    have hLHS : homogeneousComponent (n * p) (P ^ n) = P ^ n := by
      have hPn : (P ^ n).IsHomogeneous (n * p) := by rw [mul_comm]; exact hPhom.pow n
      rw [homogeneousComponent_of_mem hPn, ite_eq_left rfl]
    calc P ^ n = homogeneousComponent (n * p) (P ^ n) := hLHS.symm
      _ = homogeneousComponent (n * p) (∑ i, B' i * Ps i) := by rw [hsum]
      _ = ∑ i, homogeneousComponent (n * p) (B' i * Ps i) := by rw [map_sum]
      _ = ∑ i, homogeneousComponent (n * p - d i) (B' i) * Ps i :=
          Finset.sum_congr rfl fun i _ =>
            homogeneousComponent_mul_homogeneous (hPshom i) (n * p) (hd i) (B' i)

end Azurite.BPR.Chapter4
