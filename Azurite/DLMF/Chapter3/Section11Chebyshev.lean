/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section8
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-!
# DLMF §3.11(ii): Chebyshev polynomials, discrete orthogonality, Clenshaw's algorithm

Formalizations of the polynomial parts of <https://dlmf.nist.gov/3.11.ii>. `T ℝ n` is Mathlib's
Chebyshev polynomial of the first kind (indexed by `ℤ`).

* 3.11.6 `dlmf_3_11_6` (`Tₙ(x) = cos(n arccos x)` on `[−1, 1]`); 3.11.7 `dlmf_3_11_7` (for every
  integer `n`) with the initial values `dlmf_3_11_7_init`.
* 3.11.8 `dlmf_3_11_8`: the integral orthogonality, from Mathlib's orthogonality with respect to
  `measureT`; the integrand is integrable (`intervalIntegrable_dlmf_3_11_8`), so the improper
  integral is an ordinary Lebesgue integral.
* 3.11.9 `dlmf_3_11_9`: the discrete orthogonality at `x_ℓ = cos(πℓ/n)` (Mathlib's `node n ℓ`),
  with the double-primed sum `sumDPrime` (first and last terms halved). Key step
  `sumDPrime_cos`: `∑''_{ℓ=0}^n cos(mπℓ/n) = n` if `2n ∣ m`, else `0`, via the Dirichlet kernel
  `halfDirichlet` of §1.8.
* `chebPartialSum c n x = ∑'_{k=0}^n c_k T_k(x)` (single prime: first term halved).
  "In general it is more efficient to make use of the orthogonal property (3.11.9)":
  `dlmf_3_11_ii_discrete_coeff` recovers `c_k` (`k < n`) of `∑'_{j≤n} c_j T_j` exactly from its
  values at the `n + 1` nodes.
* Storage: `dlmf_3_11_ii_storage` (`∑_{k=0}^n (k + 1) = ½(n + 1)(n + 2)` coefficients for the
  minimax approximations `p₀, …, pₙ`).
* Clenshaw's algorithm 3.11.15: `clenshawU` (`u_{n+1} = 0`, `u_n = c_n`, `clenshawU_succ_succ`),
  `dlmf_3_11_15` (the truncated sum equals `½(u₀ − u₂)`).

Not formalized (references): Gil et al. (2007a), Mason and Handscomb (2003), Clenshaw (1957,
1962), Miller (1966), Fox and Parker (1968), Oliver (1977). The derivation of recurrences for the
`cₙ` from differential equations is described only in outline in DLMF.
-/

open Polynomial Polynomial.Chebyshev Real Finset MeasureTheory

namespace Azurite.DLMF

/-! ### 3.11.6–3.11.8 -/

/-- **DLMF 3.11.6**: `Tₙ(x) = cos(n arccos x)`, `−1 ≤ x ≤ 1`. -/
theorem dlmf_3_11_6 (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    (T ℝ n).eval x = Real.cos (n * arccos x) := by
  conv_lhs => rw [← cos_arccos hx.1 hx.2]
  simp [T_real_cos]

/-- **DLMF 3.11.7**: `T_{n+1}(x) − 2x Tₙ(x) + T_{n−1}(x) = 0` (for every integer `n`). -/
theorem dlmf_3_11_7 (n : ℤ) (x : ℝ) :
    (T ℝ (n + 1)).eval x - 2 * x * (T ℝ n).eval x + (T ℝ (n - 1)).eval x = 0 := by
  have h := T_add_two ℝ (n - 1)
  rw [show n - 1 + 2 = n + 1 by ring, show n - 1 + 1 = n by ring] at h
  rw [h]
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
  ring

/-- **DLMF 3.11.7**, initial values `T₀(x) = 1`, `T₁(x) = x`. -/
theorem dlmf_3_11_7_init (x : ℝ) : (T ℝ 0).eval x = 1 ∧ (T ℝ 1).eval x = x := by
  simp [T_zero, T_one]

/-- The integrand of 3.11.8 is integrable on `[−1, 1]`. -/
theorem intervalIntegrable_dlmf_3_11_8 (j k : ℤ) :
    IntervalIntegrable (fun x => (T ℝ j).eval x * (T ℝ k).eval x / √(1 - x ^ 2)) volume
      (-1) 1 := by
  have h := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul
    (g := fun x => (T ℝ j).eval x * (T ℝ k).eval x) (by fun_prop)
  simpa only [div_eq_mul_inv, Real.sqrt_inv] using h

/-- **DLMF 3.11.8**: `∫_{−1}^1 T_j(x) T_k(x) / √(1 − x²) dx = π, ½π, 0` for `j = k = 0`,
`j = k ≠ 0`, `j ≠ k`. -/
theorem dlmf_3_11_8 (j k : ℕ) :
    ∫ x in (-1 : ℝ)..1, (T ℝ j).eval x * (T ℝ k).eval x / √(1 - x ^ 2) =
      if j = k then (if j = 0 then π else π / 2) else 0 := by
  have e : ∫ x in (-1 : ℝ)..1, (T ℝ j).eval x * (T ℝ k).eval x / √(1 - x ^ 2) =
      ∫ x, (T ℝ j).eval x * (T ℝ k).eval x ∂measureT := by
    rw [integral_measureT]
    simp only [div_eq_mul_inv, Real.sqrt_inv]
  rw [e]
  split_ifs with hjk hj
  · subst hjk; subst hj
    simpa using integral_eval_T_real_mul_self_measureT_zero
  · subst hjk
    exact integral_T_real_mul_self_measureT_of_ne_zero hj
  · exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne hjk

/-! ### 3.11.9: discrete orthogonality -/

/-- The double-primed sum `∑''_{ℓ=0}^n a_ℓ` (first and last terms halved). -/
noncomputable def sumDPrime (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ ℓ ∈ range (n + 1), a ℓ - a 0 / 2 - a n / 2

theorem sumDPrime_lin (n : ℕ) (u v : ℝ) (a b : ℕ → ℝ) :
    sumDPrime n (fun ℓ => u * a ℓ + v * b ℓ) = u * sumDPrime n a + v * sumDPrime n b := by
  simp only [sumDPrime, sum_add_distrib, ← mul_sum]
  ring

theorem sumDPrime_sum (n : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ) :
    sumDPrime n (fun ℓ => ∑ i ∈ s, a i ℓ) = ∑ i ∈ s, sumDPrime n (a i) := by
  simp only [sumDPrime, sum_sub_distrib, ← sum_div]
  rw [sum_comm]

theorem sumDPrime_eq_halfDirichlet (n : ℕ) (s : ℝ) :
    sumDPrime n (fun ℓ => Real.cos (ℓ * s)) = halfDirichlet n s - Real.cos (n * s) / 2 := by
  rw [sumDPrime, halfDirichlet, sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero]
  ring

/-- `∑''_{ℓ=0}^n cos(mπℓ/n) = n` if `2n ∣ m`, else `0`. -/
theorem sumDPrime_cos {n : ℕ} (hn : 0 < n) (m : ℤ) :
    sumDPrime n (fun ℓ => Real.cos (m * (ℓ * π / n))) = if (2 * n : ℤ) ∣ m then n else 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set s : ℝ := m * π / n with hs
  have e : (fun ℓ : ℕ => Real.cos (m * (ℓ * π / n))) = fun ℓ : ℕ => Real.cos (ℓ * s) := by
    funext ℓ; congr 1; rw [hs]; ring
  rw [e]
  split_ifs with hdvd
  · obtain ⟨t, ht⟩ := hdvd
    have h1 : ∀ ℓ : ℕ, Real.cos (ℓ * s) = 1 := fun ℓ => by
      have : (ℓ : ℝ) * s = ((ℓ * t : ℤ) : ℝ) * (2 * π) := by
        rw [hs, ht]; push_cast; field_simp
      rw [this, Real.cos_int_mul_two_pi]
    simp only [sumDPrime, h1, sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast; ring
  · have hsin : Real.sin (s / 2) ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h0
      apply hdvd
      refine ⟨k, ?_⟩
      have : (m : ℝ) = 2 * n * k := by
        rw [hs] at hk; field_simp at hk; linarith
      exact_mod_cast this
    have hD := two_mul_halfDirichlet_mul_sin n s
    have hns : (n : ℝ) * s = m * π := by rw [hs]; field_simp
    have hsinn : Real.sin (n * s) = 0 := by rw [hns]; exact Real.sin_int_mul_pi m
    rw [show ((n : ℝ) + 1 / 2) * s = n * s + s / 2 by ring, Real.sin_add, hsinn] at hD
    rw [sumDPrime_eq_halfDirichlet]
    have : (2 * halfDirichlet n s - Real.cos (n * s)) * Real.sin (s / 2) = 0 := by
      linear_combination hD
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hsin

theorem int_dvd_cases {N d : ℤ} (hd0 : 0 ≤ d) (hd : d ≤ N) (h : N ∣ d) : d = 0 ∨ d = N := by
  rcases hd.lt_or_eq with hlt | heq
  · left; exact Int.eq_zero_of_abs_lt_dvd h (by rw [abs_of_nonneg hd0]; exact hlt)
  · right; exact heq

/-- **DLMF 3.11.9**: for `n > 0`, `0 ≤ j, k ≤ n`, and `x_ℓ = cos(πℓ/n)` (`node n ℓ`),
`∑''_{ℓ=0}^n T_j(x_ℓ) T_k(x_ℓ) = n` if `j = k = 0` or `n`, `½n` if `j = k ≠ 0, n`, and `0` if
`j ≠ k`. -/
theorem dlmf_3_11_9 {n : ℕ} (hn : 0 < n) {j k : ℕ} (hj : j ≤ n) (hk : k ≤ n) :
    sumDPrime n (fun ℓ => (T ℝ j).eval (node n ℓ) * (T ℝ k).eval (node n ℓ)) =
      if j = k then (if j = 0 ∨ j = n then (n : ℝ) else n / 2) else 0 := by
  have e : (fun ℓ => (T ℝ j).eval (node n ℓ) * (T ℝ k).eval (node n ℓ)) =
      fun ℓ : ℕ => 1 / 2 * Real.cos (((j + k : ℤ) : ℝ) * (ℓ * π / n)) +
        1 / 2 * Real.cos (((j - k : ℤ) : ℝ) * (ℓ * π / n)) := by
    funext ℓ
    simp only [node, T_real_cos]
    push_cast
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  rw [e, sumDPrime_lin, sumDPrime_cos hn, sumDPrime_cos hn]
  have hN : (0 : ℤ) < 2 * n := by positivity
  have hsum : (2 * n : ℤ) ∣ (j + k : ℤ) ↔ (j = 0 ∧ k = 0) ∨ (j = n ∧ k = n) := by
    constructor
    · intro h
      rcases int_dvd_cases (by positivity) (by omega) h with h0 | h0 <;> omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · simp
      · exact ⟨1, by ring⟩
  have hdiff : (2 * n : ℤ) ∣ (j - k : ℤ) ↔ j = k := by
    constructor
    · intro h
      have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
      omega
    · rintro rfl; simp
  by_cases hjk : j = k
  · subst hjk
    have h2 : (2 * n : ℤ) ∣ (j - j : ℤ) := by simp
    rw [ite_eq_left h2, ite_eq_left rfl]
    by_cases h0 : j = 0 ∨ j = n
    · rw [ite_eq_left (hsum.mpr (by omega)), ite_eq_left h0]; ring
    · rw [ite_eq_right (fun h => h0 (by have := hsum.mp h; omega)), ite_eq_right h0]; ring
  · rw [ite_eq_right (fun h => hjk (hdiff.mp h)),
      ite_eq_right (fun h => hjk (by have := hsum.mp h; omega)),
      ite_eq_right hjk]
    ring

/-! ### Chebyshev sums and the discrete coefficients -/

/-- The truncated Chebyshev series `∑'_{k=0}^n c_k T_k(x) = ½c₀ + ∑_{k=1}^n c_k T_k(x)`. -/
noncomputable def chebPartialSum (c : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  c 0 / 2 + ∑ k ∈ range n, c (k + 1) * (T ℝ (k + 1 : ℕ)).eval x

theorem chebPartialSum_eq (c : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    chebPartialSum c n x = ∑ k ∈ range (n + 1), c k * (T ℝ k).eval x - c 0 / 2 := by
  rw [chebPartialSum, sum_range_succ']
  simp [T_zero]
  ring

/-- **DLMF §3.11(ii)**, "make use of the orthogonal property (3.11.9)": the coefficients `c_k`,
`k < n`, of `∑'_{j=0}^n c_j T_j` are recovered from its values at the nodes `x_ℓ = cos(πℓ/n)`:
`c_k = (2/n) ∑''_ℓ p(x_ℓ) T_k(x_ℓ)`. -/
theorem dlmf_3_11_ii_discrete_coeff {n : ℕ} (hn : 0 < n) (c : ℕ → ℝ) {k : ℕ} (hk : k < n) :
    2 / n * sumDPrime n (fun ℓ => chebPartialSum c n (node n ℓ) * (T ℝ k).eval (node n ℓ)) =
      c k := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have e : (fun ℓ => chebPartialSum c n (node n ℓ) * (T ℝ k).eval (node n ℓ)) =
      fun ℓ => ∑ j ∈ range (n + 1), (if j = 0 then c 0 / 2 else c j) *
        ((T ℝ j).eval (node n ℓ) * (T ℝ k).eval (node n ℓ)) := by
    funext ℓ
    rw [chebPartialSum, sum_range_succ', add_mul, sum_mul]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.cast_zero, T_zero, eval_one, one_mul,
      mul_assoc]
    ring
  rw [e, sumDPrime_sum]
  have hterm : ∀ j ∈ range (n + 1), sumDPrime n (fun ℓ => (if j = 0 then c 0 / 2 else c j) *
      ((T ℝ j).eval (node n ℓ) * (T ℝ k).eval (node n ℓ))) =
      if j = k then (if j = 0 then c 0 / 2 * n else c j * (n / 2)) else 0 := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have := sumDPrime_lin n (if j = 0 then c 0 / 2 else c j) 0
      (fun ℓ => (T ℝ j).eval (node n ℓ) * (T ℝ k).eval (node n ℓ)) (fun _ => 0)
    simp only [zero_mul, add_zero] at this
    rw [this, dlmf_3_11_9 hn hj' hk.le]
    by_cases hjk : j = k
    · subst hjk
      by_cases h0 : j = 0
      · subst h0; simp
      · simp [h0, show j ≠ n by omega]
    · simp [hjk]
  rw [sum_congr rfl hterm, sum_ite_eq' (range (n + 1)) k, ite_eq_left (mem_range.mpr (by omega))]
  split_ifs with h0
  · subst h0; field_simp
  · field_simp

/-- **DLMF §3.11(ii)**: the minimax approximations `p₀, …, pₙ` require
`∑_{k=0}^n (k + 1) = ½(n + 1)(n + 2)` coefficients. -/
theorem dlmf_3_11_ii_storage (n : ℕ) :
    (∑ k ∈ range (n + 1), ((k : ℝ) + 1)) = (n + 1) * (n + 2) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-! ### Clenshaw's algorithm 3.11.15 -/

/-- Clenshaw's recurrence, indexed from the top: `clenshawW c n x i = u_{n+2−i}`. -/
noncomputable def clenshawW (c : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | i + 2 => 2 * x * clenshawW c n x (i + 1) - clenshawW c n x i + c (n - i)

/-- Clenshaw's `u_k` (`u_{n+2} = u_{n+1} = 0`). -/
noncomputable def clenshawU (c : ℕ → ℝ) (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  clenshawW c n x (n + 2 - k)

theorem clenshawU_init (c : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    clenshawU c n x (n + 1) = 0 ∧ clenshawU c n x n = c n := by
  simp [clenshawU, show n + 2 - (n + 1) = 1 by omega, show n + 2 - n = 0 + 2 by omega,
    clenshawW]

/-- **DLMF 3.11.15**: `u_k = 2x u_{k+1} − u_{k+2} + c_k`, `k = n − 1, …, 0` (and `k = n`). -/
theorem clenshawU_succ_succ (c : ℕ → ℝ) (n : ℕ) (x : ℝ) {k : ℕ} (hk : k ≤ n) :
    clenshawU c n x k =
      2 * x * clenshawU c n x (k + 1) - clenshawU c n x (k + 2) + c k := by
  simp only [clenshawU]
  rw [show n + 2 - k = (n - k) + 2 by omega, show n + 2 - (k + 1) = (n - k) + 1 by omega,
    show n + 2 - (k + 2) = n - k by omega, clenshawW, show n - (n - k) = k by omega]

/-- **DLMF 3.11.15**: Clenshaw's algorithm: `∑'_{k=0}^n c_k T_k(x) = ½(u₀ − u₂)`. -/
theorem dlmf_3_11_15 (c : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    chebPartialSum c n x = (clenshawU c n x 0 - clenshawU c n x 2) / 2 := by
  set t : ℤ → ℝ := fun m => (T ℝ m).eval x with ht
  set W := clenshawW c n x with hW
  have hrec : ∀ m : ℤ, t (m + 1) - 2 * x * t m + t (m - 1) = 0 := fun m => dlmf_3_11_7 m x
  -- the invariant, processing the terms from the top
  have key : ∀ i ≤ n + 1, ∑ j ∈ range i, c (n - j) * t ((n - j : ℕ) : ℤ) =
      W (i + 1) * t ((n : ℤ) + 1 - i) - W i * t ((n : ℤ) - i) := by
    intro i
    induction i with
    | zero => intro _; simp [W, clenshawW]
    | succ i ih =>
      intro hi
      rw [sum_range_succ, ih (by omega)]
      have hW2 : W (i + 2) = 2 * x * W (i + 1) - W i + c (n - i) := by simp [W, clenshawW]
      have hr := hrec ((n : ℤ) - i)
      rw [show ((n - i : ℕ) : ℤ) = (n : ℤ) - i by omega, hW2]
      push_cast
      rw [show (n : ℤ) + 1 - (i + 1) = (n : ℤ) - i by ring,
        show (n : ℤ) - (i + 1) = (n : ℤ) - i - 1 by ring]
      rw [show (n : ℤ) - i + 1 = (n : ℤ) + 1 - i by ring] at hr
      linear_combination W (i + 1) * hr
  have hfull := key (n + 1) le_rfl
  have hrefl : ∑ j ∈ range (n + 1), c (n - j) * t ((n - j : ℕ) : ℤ) =
      ∑ j ∈ range (n + 1), c j * t j := by
    have := sum_range_reflect (fun j => c j * t j) (n + 1)
    simpa using this
  rw [hrefl] at hfull
  push_cast at hfull
  rw [show (n : ℤ) + 1 - (n + 1) = 0 by ring, show (n : ℤ) - (n + 1) = -1 by ring] at hfull
  have ht0 : t 0 = 1 := by simp [t, T_zero]
  have ht1 : t (-1) = x := by simp [t]
  rw [ht0, ht1] at hfull
  have hWn : W (n + 2) = 2 * x * W (n + 1) - W n + c 0 := by
    simp [W, clenshawW]
  have hU0 : clenshawU c n x 0 = W (n + 2) := by simp [clenshawU, W]
  have hU2 : clenshawU c n x 2 = W n := by simp [clenshawU, W]
  rw [chebPartialSum_eq, hU0, hU2]
  have hsum : ∑ k ∈ range (n + 1), c k * (T ℝ k).eval x = ∑ j ∈ range (n + 1), c j * t j := rfl
  rw [hsum, hfull]
  linear_combination (1 / 2 : ℝ) * hWn

end Azurite.DLMF
