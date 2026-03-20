import Azurite.AzPolynomial.RootBound
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Map
import Mathlib.Algebra.Field.GeomSum

/-!
# Correctness Proof for the Root Bound

Proves that `rootBound f p` is a valid upper bound on the absolute value
of all roots of the polynomial, working directly over `ℚ`.

## Main Result

* `rootBound_bounds_roots`: For any root `r` of the mapped polynomial,
  `|r| < rootBound f p`.

## Proof Structure

Case 1 (`coeffs.size ≤ 1`): Constant/zero poly — contradiction with having a root.

Case 2 (`coeffs.size > 1`):
- Subcase `|r| < 1`: `rootBound ≥ 1 > |r|` since `maxCoeffRatio ≥ 0`.
- Subcase `|r| ≥ 1`: Triangle inequality on `q(r) = 0` gives
  `|aₙ|·|r|ⁿ ≤ ∑ᵢ₌₀ⁿ⁻¹ |aᵢ|·|r|ⁱ ≤ M · ∑|r|ⁱ < M·|r|ⁿ/(|r|−1)`
  where `M = maxCoeffRatio · |aₙ|`, yielding `|r| < 1 + maxCoeffRatio`.
-/

open Polynomial Finset

namespace Azurite
namespace AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

-- ── Rat-specific helpers (ℚ lacks MulPosMono in Lean 4 core) ────────────────

/-- Multiplication by a nonneg preserves ≤ for ℚ. -/
private lemma rat_mul_le_mul_nonneg_right {a b c : ℚ}
    (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := Rat.mul_nonneg (sub_nonneg.mpr h) hc
  have h2 : (b - a) * c = b * c - a * c := by ring
  linarith

/-- `1 ≤ |r|^n` when `1 ≤ |r|`. -/
private lemma one_le_abs_pow {r : ℚ} (hr : 1 ≤ |r|) : ∀ n : ℕ,  1 ≤ |r| ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ]
    have ih := one_le_abs_pow hr n
    have := rat_mul_le_mul_nonneg_right ih (show 0 ≤ |r| from by linarith [abs_nonneg r])
    linarith

-- ── Case 1: small polynomial ────────────────────────────────────────────────

/-- A polynomial with `coeffs.size ≤ 1` that is mapped to a nonzero polynomial
    cannot have any roots (it's constant). -/
private lemma no_root_of_size_le_one
    (f : R →+* ℚ) (p : Azurite.AzPolynomial R)
    (hsize : p.coeffs.size ≤ 1)
    (hpne : Polynomial.map f (AzPolynomial.toPoly p) ≠ 0)
    (r : ℚ) (hroot : (Polynomial.map f (AzPolynomial.toPoly p)).IsRoot r) : False := by
  have hnd0 : (AzPolynomial.toPoly p).natDegree = 0 := by
    rw [AzPolynomial.natDegree_toPoly]; simp [Azurite.AzPolynomial.natDegree]; omega
  have hnd_map : (Polynomial.map f (AzPolynomial.toPoly p)).natDegree = 0 :=
    le_antisymm (Polynomial.natDegree_map_le.trans (by omega)) (Nat.zero_le _)
  set q := Polynomial.map f (AzPolynomial.toPoly p) with hq_def
  have hc := Polynomial.eq_C_of_natDegree_eq_zero hnd_map
  rw [hc] at hroot hpne
  simp [Polynomial.IsRoot] at hroot
  simp [hroot] at hpne

-- ── Sub-lemma: coeff of mapped polynomial ───────────────────────────────────

/-- Coefficients of the mapped polynomial equal the mapped AzPolynomial coefficients. -/
private lemma coeff_map_toPoly (f : R →+* ℚ) (p : Azurite.AzPolynomial R) (i : ℕ) :
    (Polynomial.map f (AzPolynomial.toPoly p)).coeff i = f (p.coeff i) := by
  rw [Polynomial.coeff_map, coeff_toPoly_eq]

-- ── Case 2: Cauchy bound via triangle inequality ────────────────────────────

/-- Main Cauchy bound lemma over `ℚ`.

    Given a nonzero polynomial `q = map f (toPoly p)` of degree ≥ 1 with root `r`:
    `|r| < 1 + maxCoeffRatio f p.coeffs`.

    **Proof**:
    - If `|r| < 1`: `1 + maxCoeffRatio ≥ 1 > |r|`. (Easy, uses `maxCoeffRatio_nonneg`.)
    - If `|r| ≥ 1`: From `q(r) = 0`, since `q.coeff n ≠ 0` (leading coeff),
      cancelling `|q.coeff n|` from both sides of the triangle inequality
      yields `|r| - 1 < maxCoeffRatio`. -/
private lemma cauchy_bound_case
    (f : R →+* ℚ) (hf : Function.Injective f) (p : Azurite.AzPolynomial R)
    (hsize : ¬ p.coeffs.size ≤ 1)
    (hpne : Polynomial.map f (AzPolynomial.toPoly p) ≠ 0)
    (r : ℚ) (hroot : (Polynomial.map f (AzPolynomial.toPoly p)).IsRoot r) :
    |r| < rootBound f p := by
  unfold rootBound
  simp only [show ¬ p.coeffs.size ≤ 1 from hsize, ite_false]
  -- Goal: |r| < 1 + maxCoeffRatio f p.coeffs
  by_cases hr1 : |r| < 1
  · -- Easy case: |r| < 1, and maxCoeffRatio ≥ 0 so rootBound ≥ 1
    linarith [maxCoeffRatio_nonneg f p.coeffs]
  · -- Hard case: |r| ≥ 1
    push_neg at hr1
    set q := Polynomial.map f (AzPolynomial.toPoly p) with hq_def
    set n := q.natDegree with hn_def
    have hdeg : 1 ≤ n := by
      by_contra h; push_neg at h
      have hnd0 : q.natDegree = 0 := by omega
      have hc := Polynomial.eq_C_of_natDegree_eq_zero hnd0
      rw [hc] at hroot; simp [Polynomial.IsRoot] at hroot
      rw [hc, hroot, Polynomial.C_0] at hpne; exact hpne rfl
    have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hpne
    have hlc_pos : 0 < |q.leadingCoeff| := abs_pos.mpr hlc
    -- Step 1: From q.IsRoot r, extract leading term from eval sum
    have heval : (∑ i ∈ range (n + 1), q.coeff i * r ^ i) = 0 := by
      rw [← Polynomial.eval_eq_sum_range]; exact hroot
    rw [Finset.sum_range_succ] at heval
    have hcn : q.coeff n = q.leadingCoeff := rfl
    rw [hcn] at heval
    -- q.leadingCoeff * r^n = -(∑_{i<n} q.coeff i * r^i)
    have hiso : q.leadingCoeff * r ^ n =
        -(∑ i ∈ range n, q.coeff i * r ^ i) := by linarith
    -- Step 2: Triangle inequality → |lc|*|r|^n ≤ ∑|coeff i|*|r|^i
    have hbound1 : |q.leadingCoeff| * |r| ^ n ≤
        ∑ i ∈ range n, |q.coeff i| * |r| ^ i := by
      have h1 : |q.leadingCoeff| * |r| ^ n =
          |q.leadingCoeff * r ^ n| := by rw [abs_mul, abs_pow]
      rw [h1, hiso, abs_neg]
      calc |∑ i ∈ range n, q.coeff i * r ^ i|
        ≤ ∑ i ∈ range n, |q.coeff i * r ^ i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ range n, (|q.coeff i| * |r| ^ i) := by
          apply Finset.sum_congr rfl
          intro i _; rw [abs_mul, abs_pow]
    -- Step 3: Bound ∑|coeff i|*|r|^i ≤ M*|lc|*∑|r|^i
    --   where M = maxCoeffRatio f p.coeffs
    have hbound2 : ∑ i ∈ range n, |q.coeff i| * |r| ^ i ≤
        maxCoeffRatio f p.coeffs * |q.leadingCoeff| *
        ∑ i ∈ range n, |r| ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i hi
      have him := Finset.mem_range.mp hi
      -- |q.coeff i| ≤ maxCoeffRatio * |lc|
      have hci : |q.coeff i| ≤
          maxCoeffRatio f p.coeffs * |q.leadingCoeff| := by
        -- AzPolynomial invariant: last coeff ≠ 0 in R
        have hsz : 0 < p.coeffs.size := by omega
        have hlast_ne : p.coeffs[p.coeffs.size - 1] ≠ 0 := by
          intro h; exact p.last_ne_zero (by
            unfold Array.back?
            simp [show p.coeffs.size - 1 < p.coeffs.size from by omega, h])
        -- Since f is injective, f(last) ≠ 0
        have hflast : f (p.coeffs[p.coeffs.size - 1]'(by omega)) ≠ 0 := by
          intro h; exact hlast_ne (hf (by rwa [map_zero]))
        -- n = p.coeffs.size - 1
        have hndeg : n = p.coeffs.size - 1 := by
          have h1 : n ≤ p.coeffs.size - 1 := by
            show q.natDegree ≤ _
            calc q.natDegree
              ≤ (AzPolynomial.toPoly p).natDegree := Polynomial.natDegree_map_le
            _ = p.coeffs.size - 1 := AzPolynomial.natDegree_toPoly p
          have h2 : p.coeffs.size - 1 ≤ n := by
            show _ ≤ q.natDegree
            apply Polynomial.le_natDegree_of_ne_zero
            show q.coeff (p.coeffs.size - 1) ≠ 0
            rw [hq_def, Polynomial.coeff_map, coeff_toPoly_eq]
            simp [Azurite.AzPolynomial.coeff,
              show p.coeffs.size - 1 < p.coeffs.size from by omega]
            exact hflast
          omega
        -- q.coeff i = f(p.coeffs[i])
        have hi_sz : i < p.coeffs.size := by omega
        have hqi : q.coeff i = f (p.coeffs[i]'hi_sz) := by
          rw [hq_def, Polynomial.coeff_map, coeff_toPoly_eq]
          simp [Azurite.AzPolynomial.coeff, show i < p.coeffs.size from hi_sz]
        -- q.leadingCoeff = f(p.coeffs[size-1])
        have hqlc : q.leadingCoeff =
            f (p.coeffs[p.coeffs.size - 1]'(by omega)) := by
          show q.coeff n = _
          rw [hq_def, Polynomial.coeff_map, coeff_toPoly_eq]
          simp [Azurite.AzPolynomial.coeff, hndeg,
            show p.coeffs.size - 1 < p.coeffs.size from by omega]
        -- From le_maxCoeffRatio: ratio ≤ maxCoeffRatio
        have hfin : i < p.coeffs.size - 1 := by omega
        have hratio := le_maxCoeffRatio f p.coeffs hsize hflast ⟨i, hfin⟩
        -- Convert from ratio form to product form
        rw [hqi, hqlc]
        have habs_pos : 0 < |f (p.coeffs[p.coeffs.size - 1]'(by omega))| :=
          abs_pos.mpr hflast
        have := rat_mul_le_mul_nonneg_right hratio (le_of_lt habs_pos)
        rwa [div_mul_cancel₀ _ (ne_of_gt habs_pos)] at this
      calc |q.coeff i| * |r| ^ i
        ≤ (maxCoeffRatio f p.coeffs * |q.leadingCoeff|) * |r| ^ i :=
          rat_mul_le_mul_nonneg_right hci (pow_nonneg (abs_nonneg _) _)
      _ = maxCoeffRatio f p.coeffs * |q.leadingCoeff| * |r| ^ i :=
          by ring
    -- Step 4: Divide by |lc|: |r|^n ≤ M * ∑|r|^i
    have hbound3 : |r| ^ n ≤
        maxCoeffRatio f p.coeffs * ∑ i ∈ range n, |r| ^ i := by
      have h := le_trans hbound1 hbound2
      rw [show maxCoeffRatio f p.coeffs * |q.leadingCoeff| *
          ∑ i ∈ range n, |r| ^ i =
          (maxCoeffRatio f p.coeffs * ∑ i ∈ range n, |r| ^ i) *
          |q.leadingCoeff| by ring] at h
      have h2 : |q.leadingCoeff| * |r| ^ n ≤
          (maxCoeffRatio f p.coeffs * ∑ i ∈ range n, |r| ^ i) *
          |q.leadingCoeff| := h
      -- Since |lc| > 0, can cancel
      nlinarith [Rat.mul_nonneg (sub_nonneg.mpr h2)
        (le_of_lt (show (0 : ℚ) < |q.leadingCoeff|⁻¹ from
          Rat.inv_pos.mpr hlc_pos))]
    -- Step 5: Case split |r| = 1 vs |r| > 1
    by_cases hr_eq : |r| = 1
    · -- |r| = 1: ∑|r|^i = n, so 1 ≤ M * n → M > 0
      simp only [hr_eq, one_pow] at hbound3
      rw [Finset.sum_const, Finset.card_range,
          Nat.smul_one_eq_cast] at hbound3
      have hn_pos : (0 : ℚ) < n := by
        exact_mod_cast (show 0 < n from by omega)
      rw [hr_eq]; nlinarith
    · -- |r| > 1: use geometric series
      have hr_gt : 1 < |r| :=
        lt_of_le_of_ne hr1 (Ne.symm hr_eq)
      have hr_sub_pos : 0 < |r| - 1 := by linarith
      have hrn_pos : 0 < |r| ^ n :=
        pow_pos (by linarith : 0 < |r|) n
      have hgeom : ∑ i ∈ range n, |r| ^ i =
          (|r| ^ n - 1) / (|r| - 1) :=
        geom_sum_eq (by linarith : |r| ≠ 1) n
      rw [hgeom] at hbound3
      -- If M = 0, then |r|^n ≤ 0, contradiction
      have hM_pos : 0 < maxCoeffRatio f p.coeffs := by
        by_contra h; push_neg at h
        have : maxCoeffRatio f p.coeffs = 0 :=
          le_antisymm h (maxCoeffRatio_nonneg f p.coeffs)
        simp [this] at hbound3; linarith
      -- Clear denominator: |r|^n*(|r|-1) ≤ M*(|r|^n-1)
      have h5 : |r| ^ n * (|r| - 1) ≤
          maxCoeffRatio f p.coeffs * (|r| ^ n - 1) := by
        rw [mul_div_assoc'] at hbound3
        have := rat_mul_le_mul_nonneg_right hbound3
          (le_of_lt hr_sub_pos)
        rwa [div_mul_cancel₀ _ (ne_of_gt hr_sub_pos)] at this
      -- |r|^n*(|r|-1) < M*|r|^n since |r|^n-1 < |r|^n
      nlinarith [one_le_abs_pow hr1 n]

-- ── Main theorem ────────────────────────────────────────────────────────────

/-- **Cauchy Root Bound Theorem.** For any root `r` of the polynomial obtained
    by mapping the coefficients of `p` through a ring homomorphism `f : R →+* ℚ`,
    if the mapped polynomial is nonzero, then `|r| < rootBound f p`. -/
theorem rootBound_bounds_roots
    (f : R →+* ℚ) (hf : Function.Injective f)
    (p : Azurite.AzPolynomial R) (r : ℚ)
    (hpne : Polynomial.map f (AzPolynomial.toPoly p) ≠ 0)
    (hroot : Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p)) r) :
    |r| < rootBound f p := by
  by_cases hsize : p.coeffs.size ≤ 1
  · exact (no_root_of_size_le_one f p hsize hpne r hroot).elim
  · exact cauchy_bound_case f hf p hsize hpne r hroot

end AzPolynomial
end Azurite
