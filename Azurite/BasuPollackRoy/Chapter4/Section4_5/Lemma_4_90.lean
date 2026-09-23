import Azurite.BasuPollackRoy.Chapter4.Section4_5.Definition_4_89
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.CharP.Algebra

/-!
# BPR §4.5, Lemma 4.90: a separating linear form of small index exists

If `#Zer(𝒫, Cᵏ) = n`, then there exists `i`, `0 ≤ i ≤ (k−1)·C(n,2)`, such that
`aᵢ = X₁ + i·X₂ + ⋯ + i^{k−1}·X_k` (`linearForm i`) is separating.

For two distinct points `x, y` of `Zer(𝒫, Cᵏ)`, the indices `i` with `aᵢ(x) = aᵢ(y)` are exactly
the natural-number roots of the nonzero polynomial `∑_j (x_j − y_j) T^{j−1}` (`pairPoly x y`),
of degree at most `k−1`; hence there are at most `k−1` of them. Summing over the `C(n,2)`
two-element subsets of `Zer(𝒫, Cᵏ)`, at most `(k−1)·C(n,2)` indices in `{0, …, (k−1)·C(n,2)}`
fail to separate, so at least one of the `(k−1)·C(n,2) + 1` indices works.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K] (C : Type*) [Field C] [Algebra K C]

/-- The linear form `aᵢ = X₁ + i·X₂ + ⋯ + i^{k−1}·X_k` (as an element of `K[X₁, …, X_k]`). -/
noncomputable def linearForm (i : ℕ) : MvPolynomial (Fin k) K :=
  ∑ j : Fin k, MvPolynomial.C ((i : K) ^ (j : ℕ)) * X j

/-- The value `aᵢ(x) = ∑_j i^{j} x_{j+1}` of the linear form `aᵢ` at a point `x ∈ Cᵏ`. -/
theorem aeval_linearForm (i : ℕ) (x : Fin k → C) :
    MvPolynomial.aeval x (linearForm (K := K) i) = ∑ j : Fin k, (i : C) ^ (j : ℕ) * x j := by
  rw [linearForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_pow, map_natCast]

/-- The "difference polynomial" `∑_j (x_j − y_j) T^{j−1}` of two points `x, y ∈ Cᵏ`. -/
private noncomputable def pairPoly (x y : Fin k → C) : Polynomial C :=
  ∑ j : Fin k, Polynomial.C (x j - y j) * Polynomial.X ^ (j : ℕ)

private theorem coeff_pairPoly (x y : Fin k → C) (j : Fin k) :
    (pairPoly C x y).coeff (j : ℕ) = x j - y j := by
  rw [pairPoly, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
      (fun j' _ hj' => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          ite_eq_right (fun heq => hj' (Fin.val_injective heq).symm), mul_zero])]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]

private theorem pairPoly_ne_zero (x y : Fin k → C) (hxy : x ≠ y) : pairPoly C x y ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  intro h
  have hc := coeff_pairPoly C x y j
  rw [h, Polynomial.coeff_zero] at hc
  exact hj (sub_eq_zero.mp hc.symm)

private theorem eval_pairPoly (x y : Fin k → C) (i : ℕ) :
    (pairPoly C x y).eval (i : C)
      = MvPolynomial.aeval x (linearForm (K := K) i) - MvPolynomial.aeval y (linearForm (K := K) i)
      := by
  rw [aeval_linearForm, aeval_linearForm, pairPoly, Polynomial.eval_finsetSum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

private theorem natDegree_pairPoly_le (x y : Fin k → C) : (pairPoly C x y).natDegree ≤ k - 1 := by
  rw [pairPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact Nat.le_sub_one_of_lt j.isLt

/-- **BPR Lemma 4.90.** If `Zer(𝒫, Cᵏ)` is finite with `n` elements, then some
`aᵢ = X₁ + i·X₂ + ⋯ + i^{k−1}·X_k` with `0 ≤ i ≤ (k−1)·C(n,2)` is separating for `𝒫`. -/
theorem lemma_4_90 [CharZero K] (Ps : Finset (MvPolynomial (Fin k) K))
    (hfin : (zerOfFinset C Ps).Finite) :
    ∃ i : ℕ, i ≤ (k - 1) * (hfin.toFinset.card).choose 2 ∧
      IsSeparating C Ps (Ideal.Quotient.mk _ (linearForm (K := K) i)) := by
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  set M := (k - 1) * (hfin.toFinset.card).choose 2 with hM
  set R := Finset.range (M + 1) with hR
  have hRcard : R.card = M + 1 := by rw [hR, Finset.card_range]
  -- for distinct `x, y`, at most `k − 1` indices `i` satisfy `aᵢ(x) = aᵢ(y)`
  have rootBound : ∀ (x y : Fin k → C), x ≠ y →
      (R.filter (fun i => MvPolynomial.aeval x (linearForm (K := K) i)
        = MvPolynomial.aeval y (linearForm (K := K) i))).card ≤ k - 1 := by
    intro x y hxy
    refine le_trans (Finset.card_le_card_of_injOn (f := fun i => (i : C))
      (t := (pairPoly C x y).roots.toFinset) ?_ ?_) ?_
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      have hev := eval_pairPoly (K := K) C x y i
      rw [hi.2, sub_self] at hev
      exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr
        (Polynomial.mem_roots'.mpr ⟨pairPoly_ne_zero C x y hxy, hev⟩))
    · intro i _ j _ hij
      exact Nat.cast_injective hij
    · refine le_trans (Multiset.toFinset_card_le _) ?_
      exact le_trans (Polynomial.card_roots' _) (natDegree_pairPoly_le C x y)
  -- non-separating indices are covered by the per-pair root sets
  have hsub : R.filter (fun i => ¬ ∀ x ∈ hfin.toFinset, ∀ y ∈ hfin.toFinset,
        MvPolynomial.aeval x (linearForm (K := K) i) = MvPolynomial.aeval y (linearForm (K := K) i) → x = y)
      ⊆ (hfin.toFinset.powersetCard 2).biUnion (fun t => R.filter (fun i => ∀ u ∈ t, ∀ v ∈ t,
        MvPolynomial.aeval u (linearForm (K := K) i) = MvPolynomial.aeval v (linearForm (K := K) i))) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiR, hnsep⟩ := hi
    push Not at hnsep
    obtain ⟨x, hxT, y, hyT, heq, hne⟩ := hnsep
    rw [Finset.mem_biUnion]
    refine ⟨{x, y}, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨fun z hz => ?_, Finset.card_pair hne⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · refine Finset.mem_filter.mpr ⟨hiR, fun u hu v hv => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
        first | rfl | exact heq | exact heq.symm
  -- each per-pair set has at most `k − 1` indices
  have hpiece : ∀ t ∈ hfin.toFinset.powersetCard 2,
      (R.filter (fun i => ∀ u ∈ t, ∀ v ∈ t,
        MvPolynomial.aeval u (linearForm (K := K) i) = MvPolynomial.aeval v (linearForm (K := K) i))).card
        ≤ k - 1 := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp ht.2
    refine le_trans (Finset.card_le_card ?_) (rootBound a b hab)
    intro i hi
    rw [Finset.mem_filter] at hi
    exact Finset.mem_filter.mpr ⟨hi.1, hi.2 a (by simp) b (by simp)⟩
  -- the union lies in `R` and covers at most `M` indices
  have hbU : (hfin.toFinset.powersetCard 2).biUnion (fun t => R.filter (fun i => ∀ u ∈ t, ∀ v ∈ t,
        MvPolynomial.aeval u (linearForm (K := K) i) = MvPolynomial.aeval v (linearForm (K := K) i))) ⊆ R :=
    Finset.biUnion_subset.mpr fun t _ => Finset.filter_subset _ _
  have hbUcard : ((hfin.toFinset.powersetCard 2).biUnion (fun t => R.filter (fun i => ∀ u ∈ t,
        ∀ v ∈ t, MvPolynomial.aeval u (linearForm (K := K) i)
          = MvPolynomial.aeval v (linearForm (K := K) i)))).card ≤ M := by
    calc ((hfin.toFinset.powersetCard 2).biUnion (fun t => R.filter (fun i => ∀ u ∈ t, ∀ v ∈ t,
            MvPolynomial.aeval u (linearForm (K := K) i) = MvPolynomial.aeval v (linearForm (K := K) i)))).card
        ≤ ∑ t ∈ hfin.toFinset.powersetCard 2, (R.filter (fun i => ∀ u ∈ t, ∀ v ∈ t,
            MvPolynomial.aeval u (linearForm (K := K) i) = MvPolynomial.aeval v (linearForm (K := K) i))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ hfin.toFinset.powersetCard 2, (k - 1) := Finset.sum_le_sum hpiece
      _ = (hfin.toFinset.powersetCard 2).card * (k - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ = M := by rw [Finset.card_powersetCard, hM]; ring
  -- hence some index of `R` avoids the union, i.e. is separating
  have hne : (R \ (hfin.toFinset.powersetCard 2).biUnion (fun t => R.filter (fun i => ∀ u ∈ t,
      ∀ v ∈ t, MvPolynomial.aeval u (linearForm (K := K) i)
        = MvPolynomial.aeval v (linearForm (K := K) i)))).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hRsub
    have hle := Finset.card_le_card hRsub
    rw [hRcard] at hle
    omega
  obtain ⟨i, hi⟩ := hne
  rw [Finset.mem_sdiff] at hi
  obtain ⟨hiR, hiNot⟩ := hi
  have hile : i ≤ M := by rw [hR, Finset.mem_range] at hiR; omega
  have hgood : ∀ x ∈ hfin.toFinset, ∀ y ∈ hfin.toFinset,
      MvPolynomial.aeval x (linearForm (K := K) i) = MvPolynomial.aeval y (linearForm (K := K) i) → x = y := by
    by_contra hcon
    exact hiNot (hsub (Finset.mem_filter.mpr ⟨hiR, hcon⟩))
  refine ⟨i, hile, ?_⟩
  intro x hx y hy heq
  rw [valueAt_mk, valueAt_mk] at heq
  exact hgood x (hfin.mem_toFinset.mpr hx) y (hfin.mem_toFinset.mpr hy) heq

end Azurite.BPR.Chapter4
