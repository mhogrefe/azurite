/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section11RationalAchieser
import Azurite.DLMF.Chapter3.Section11RationalExampleData
import Azurite.DLMF.Chapter3.Section5ComplexGaussExample

/-!
# DLMF §3.11(iii), Example: Table 3.11.1

The rational approximation 3.11.19 of type `[3, 3]` to `J₀` with the coefficients of
Table 3.11.1 (`P33`, `Q33`, `w = 1`).

* `dlmf_3_11_iii_table_upper`: `|R₃,₃(x) − J₀(x)| ≤ 1.09·10⁻⁸` on `[0, 0.8935769663]`;
* `dlmf_3_11_iii_table_lower`: every rational approximation of type `[3, 3]` (positive
  denominator) has maximum error `≥ 1.0821·10⁻⁸` there (de la Vallée-Poussin at eight points
  where the error of `R₃,₃` alternates);
* `dlmf_3_11_iii_table_3_11_1`: hence `R₃,₃` is within `0.75 %` of the minimax error, which lies
  in `[1.0821, 1.09]·10⁻⁸` (the error curve of Figure 3.11.1).
* **Erratum** `dlmf_3_11_iii_table_erratum`: the interval of Table 3.11.1 and Figure 3.11.1 is
  `0 ≤ x ≤ 0.89357…` (`= y₀,₁`, the first zero of `Y₀`), not `0 ≤ x ≤ j₀,₁`: `j₀,₁ ∈ [2.4, 2.41]`
  (`j01_bounds`), on `[0, j₀,₁]` the error of `R₃,₃` exceeds `0.04` (at `x = 2.4`), and a cubic
  polynomial does better (`< 0.01`), so `R₃,₃` is not the minimax approximation on `[0, j₀,₁]`.

Method: `J₀` is replaced by its Maclaurin polynomial of degree `26` (`besselJ0_approx`, error
`≤ 10⁻¹⁷` for `|x| ≤ 5/2`); the polynomials (`polyOfQ`) are bounded on cells by a second-order
mean-value estimate (`poly_cell`) whose rational inputs are checked by the kernel
(`Section11RationalExampleData.lean`).
-/

open Polynomial Set

namespace Azurite.DLMF

/-! ### Polynomials with rational coefficients -/

/-- `∑_{n<N} c_n x^n` as a real polynomial. -/
noncomputable def polyOfQ (c : ℕ → ℚ) (N : ℕ) : ℝ[X] :=
  ∑ n ∈ Finset.range N, C ((c n : ℚ) : ℝ) * X ^ n

theorem coeff_polyOfQ (c : ℕ → ℚ) (N n : ℕ) :
    (polyOfQ c N).coeff n = if n < N then ((c n : ℚ) : ℝ) else 0 := by
  simp only [polyOfQ, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

theorem natDegree_polyOfQ_lt (c : ℕ → ℚ) {N : ℕ} (hN : 0 < N) : (polyOfQ c N).natDegree < N := by
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun i hi => ?_) (by omega)
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Finset.mem_range.mp hi
  omega

theorem eval_iterate_derivative_polyOfQ (c : ℕ → ℚ) {N : ℕ} (hN : 0 < N) (k : ℕ) (y : ℝ) :
    (derivative^[k] (polyOfQ c N)).eval y =
      ∑ m ∈ Finset.range N, ((dcoeffQ c N k m : ℚ) : ℝ) * y ^ m := by
  rw [eval_eq_sum_range' (n := N) (lt_of_le_of_lt (natDegree_iterate_derivative _ _)
    (lt_of_le_of_lt (Nat.sub_le _ _) (natDegree_polyOfQ_lt c hN)))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_iterate_derivative, coeff_polyOfQ, dcoeffQ]
  split_ifs <;> simp [nsmul_eq_mul]

theorem eval_iterate_derivative_polyOfQ_rat (c : ℕ → ℚ) {N : ℕ} (hN : 0 < N) (k : ℕ) (q : ℚ) :
    (derivative^[k] (polyOfQ c N)).eval (q : ℝ) = ((evQ c N k q : ℚ) : ℝ) := by
  rw [eval_iterate_derivative_polyOfQ c hN, evQ_eq]
  push_cast
  rfl

theorem eval_polyOfQ_rat (c : ℕ → ℚ) {N : ℕ} (hN : 0 < N) (q : ℚ) :
    (polyOfQ c N).eval (q : ℝ) = ((evQ c N 0 q : ℚ) : ℝ) :=
  eval_iterate_derivative_polyOfQ_rat c hN 0 q

theorem abs_eval_iterate_derivative_le (c : ℕ → ℚ) {N : ℕ} (hN : 0 < N) (k : ℕ) {R : ℚ}
    (_hR : 0 ≤ R) {y : ℝ} (hy : |y| ≤ R) :
    |(derivative^[k] (polyOfQ c N)).eval y| ≤ ((absSumQ c N k R : ℚ) : ℝ) := by
  rw [eval_iterate_derivative_polyOfQ c hN, absSumQ]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [abs_mul, abs_pow]
  gcongr

/-! ### A second-order mean-value bound on cells -/

theorem poly_mvt {G : ℝ[X]} {c δ B : ℝ} (hB : ∀ y ∈ Icc (c - δ) (c + δ),
    |(derivative G).eval y| ≤ B) (hδ : 0 ≤ δ) {x : ℝ} (hx : x ∈ Icc (c - δ) (c + δ)) :
    |G.eval x - G.eval c| ≤ B * δ := by
  have hc : c ∈ Icc (c - δ) (c + δ) := ⟨by linarith, by linarith⟩
  have h := (convex_Icc (c - δ) (c + δ)).norm_image_sub_le_of_norm_deriv_le
    (f := fun y => G.eval y) (C := B) (fun y _ => G.differentiableAt)
    (fun y hy => by rw [Polynomial.deriv, Real.norm_eq_abs]; exact hB y hy) hc hx
  simp only [Real.norm_eq_abs] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hB c hc)))
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

/-- `|H(x) − H(c)| ≤ δ(B₁ + δ(B₂ + δL₃))` on `[c − δ, c + δ]`. -/
theorem poly_cell {H : ℝ[X]} {c δ B1 B2 L3 : ℝ} (hδ : 0 ≤ δ)
    (h1 : |(derivative^[1] H).eval c| ≤ B1) (h2 : |(derivative^[2] H).eval c| ≤ B2)
    (h3 : ∀ y ∈ Icc (c - δ) (c + δ), |(derivative^[3] H).eval y| ≤ L3) {x : ℝ}
    (hx : x ∈ Icc (c - δ) (c + δ)) : |H.eval x - H.eval c| ≤ δ * (B1 + δ * (B2 + δ * L3)) := by
  have hd2 : ∀ y ∈ Icc (c - δ) (c + δ), |(derivative^[2] H).eval y| ≤ B2 + δ * L3 :=
    fun y hy => by
      have := poly_mvt (G := derivative^[2] H) (B := L3) (fun z hz => by
        rw [← Function.iterate_succ_apply' derivative]; exact h3 z hz) hδ hy
      have := abs_sub_abs_le_abs_sub ((derivative^[2] H).eval y) ((derivative^[2] H).eval c)
      linarith
  have hd1 : ∀ y ∈ Icc (c - δ) (c + δ), |(derivative^[1] H).eval y| ≤ B1 + δ * (B2 + δ * L3) :=
    fun y hy => by
      have := poly_mvt (G := derivative^[1] H) (B := B2 + δ * L3) (fun z hz => by
        rw [← Function.iterate_succ_apply' derivative]; exact hd2 z hz) hδ hy
      have := abs_sub_abs_le_abs_sub ((derivative^[1] H).eval y) ((derivative^[1] H).eval c)
      nlinarith
  have := poly_mvt (G := H) (B := B1 + δ * (B2 + δ * L3)) (fun z hz => by
    simpa using hd1 z hz) hδ hx
  linarith

/-- The cell bound with rational data. -/
theorem cell_diff_rat (c' : ℕ → ℚ) {N : ℕ} (hN : 0 < N) {cq δq L3q : ℚ} (hδ : 0 ≤ δq)
    (hL3 : ∀ y ∈ Icc ((cq : ℝ) - δq) (cq + δq),
      |(derivative^[3] (polyOfQ c' N)).eval y| ≤ L3q) {x : ℝ}
    (hx : x ∈ Icc ((cq : ℝ) - δq) (cq + δq)) :
    |(polyOfQ c' N).eval x - ((evQ c' N 0 cq : ℚ) : ℝ)| ≤
      ((δq * (|evQ c' N 1 cq| + δq * (|evQ c' N 2 cq| + δq * L3q)) : ℚ) : ℝ) := by
  rw [← eval_polyOfQ_rat c' hN]
  have h := poly_cell (H := polyOfQ c' N) (B1 := ((|evQ c' N 1 cq| : ℚ) : ℝ))
    (B2 := ((|evQ c' N 2 cq| : ℚ) : ℝ)) (L3 := (L3q : ℝ)) (by exact_mod_cast hδ)
    (by rw [eval_iterate_derivative_polyOfQ_rat c' hN]; push_cast; exact le_rfl)
    (by rw [eval_iterate_derivative_polyOfQ_rat c' hN]; push_cast; exact le_rfl) hL3 hx
  push_cast at h ⊢
  exact h

/-! ### `J₀` and its Maclaurin polynomial -/

theorem sum_range_two_mul_r33 (f : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ Finset.range (2 * M), f n = ∑ j ∈ Finset.range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

theorem aL_even_odd {j : ℕ} (hj : j < 14) :
    aL (2 * j) = (-1) ^ j / (4 ^ j * ((j.factorial ^ 2 : ℕ) : ℚ)) ∧ aL (2 * j + 1) = 0 := by
  have := List.all_eq_true.mp aL_eq j (List.mem_range.mpr hj)
  simpa using this

/-- The Maclaurin polynomial is the partial sum of the series of `J₀`. -/
theorem eval_polyOfQ_aL (x : ℝ) :
    (polyOfQ aL 28).eval x = ∑ j ∈ Finset.range 14, BZ.besselCoeff 0 j * (x / 2) ^ (2 * j + 0) := by
  simp only [polyOfQ, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [show (28 : ℕ) = 2 * 14 by norm_num, sum_range_two_mul_r33]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨h1, h2⟩ := aL_even_odd (Finset.mem_range.mp hj)
  rw [h1, h2, BZ.besselCoeff]
  push_cast
  simp only [zero_mul, add_zero, zero_add]
  rw [show (x / 2) ^ (2 * j) = (x ^ 2) ^ j / 4 ^ j by rw [div_pow, pow_mul, pow_mul]; norm_num]
  field_simp
  ring

theorem besselJ0_eq_tsum (x : ℝ) :
    besselJ0 x = ∑' j, BZ.besselCoeff 0 j * (x / 2) ^ (2 * j + 0) := rfl

/-- `|J₀(x) − ∑_{j<14} (−1)^j (x/2)^{2j}/(j!)²| ≤ 10⁻¹⁷` for `|x| ≤ 5/2`. -/
theorem besselJ0_approx {x : ℝ} (hx : |x| ≤ 5 / 2) :
    |besselJ0 x - (polyOfQ aL 28).eval x| ≤ ((tauQ : ℚ) : ℝ) := by
  set t : ℕ → ℝ := fun j => BZ.besselCoeff 0 j * (x / 2) ^ (2 * j + 0)
  have hs : Summable t := BZ.summable_besselJNat_term 0 x
  have hsplit := hs.sum_add_tsum_nat_add 14
  rw [besselJ0_eq_tsum, eval_polyOfQ_aL, ← hsplit, add_sub_cancel_left]
  have hx2 : (x / 2) ^ 2 ≤ 25 / 16 := by
    rw [div_pow]; have := sq_abs x; nlinarith [abs_nonneg x]
  -- the ratio of consecutive terms is at most `1/2` from `j = 1` on
  have hratio : ∀ j, 1 ≤ j → |t (j + 1)| ≤ |t j| / 2 := fun j hj => by
    simp only [t, BZ.besselCoeff_succ, add_zero]
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, abs_mul, abs_mul, abs_mul, abs_div,
      abs_neg]
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hj' : (2 : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hden : |((j : ℝ) + 1) * ((0 : ℕ) + (j : ℝ) + 1)| = ((j : ℝ) + 1) ^ 2 := by
      push_cast; rw [zero_add, abs_of_pos (by positivity)]; ring
    push_cast at hden ⊢
    rw [hden, abs_of_nonneg (sq_nonneg (x / 2))]
    have h4 : (4 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
    have hA := abs_nonneg (BZ.besselCoeff 0 j)
    have hB := abs_nonneg ((x / 2) ^ (2 * j))
    have : (x / 2) ^ 2 / ((j : ℝ) + 1) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc |BZ.besselCoeff 0 j| / ((j : ℝ) + 1) ^ 2 * (|(x / 2) ^ (2 * j)| * (x / 2) ^ 2)
        = |BZ.besselCoeff 0 j| * |(x / 2) ^ (2 * j)| * ((x / 2) ^ 2 / ((j : ℝ) + 1) ^ 2) := by
          ring
      _ ≤ |BZ.besselCoeff 0 j| * |(x / 2) ^ (2 * j)| * (1 / 2) := by gcongr
      _ = _ := by ring
  have hgeo : ∀ i, |t (i + 14)| ≤ |t 14| * (1 / 2) ^ i := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show i + 1 + 14 = (i + 14) + 1 by ring, pow_succ]
      have := hratio (i + 14) (by omega)
      nlinarith [abs_nonneg (t (i + 14))]
  have hsum : Summable fun i => |t (i + 14)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hgeo
      ((summable_geometric_two).mul_left (|t 14|) |>.congr fun i => by ring)
  have hbound : |∑' i, t (i + 14)| ≤ 2 * |t 14| := by
    have h1 : |∑' i, t (i + 14)| ≤ ∑' i, |t (i + 14)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun i => t (i + 14))
        (by simpa only [Real.norm_eq_abs] using hsum)
    have h2 : ∑' i, |t (i + 14)| ≤ ∑' i, |t 14| * (1 / 2) ^ i :=
      Summable.tsum_le_tsum hgeo hsum ((summable_geometric_two).mul_left _ |>.congr fun i => by
        ring)
    rw [tsum_mul_left, tsum_geometric_two] at h2
    linarith
  have ht14 : |t 14| ≤ (25 / 16) ^ 14 / ((14 : ℕ).factorial * (14 : ℕ).factorial) := by
    simp only [t, BZ.besselCoeff, add_zero]
    rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity),
      pow_mul, abs_pow, abs_of_nonneg (sq_nonneg _), zero_add]
    rw [div_mul_eq_mul_div, one_mul]
    gcongr
  refine hbound.trans ?_
  have : 2 * ((25 / 16 : ℝ) ^ 14 / ((14 : ℕ).factorial * (14 : ℕ).factorial)) ≤
      ((tauQ : ℚ) : ℝ) := by
    simp only [tauQ, Nat.factorial]
    norm_num
  linarith

/-! ### The rational function of Table 3.11.1 -/

/-- 3.11.19 with Table 3.11.1: the numerator. -/
noncomputable def P33 : ℝ[X] := polyOfQ pR33 4

/-- 3.11.19 with Table 3.11.1: the denominator. -/
noncomputable def Q33 : ℝ[X] := polyOfQ qQ 4

theorem Q33_eval (x : ℝ) : Q33.eval x = 1 + (-34039052338838 / 10 ^ 14) * x +
    (6086501629812 / 10 ^ 14) * x ^ 2 + (-1864476809090 / 10 ^ 14) * x ^ 3 := by
  simp [Q33, polyOfQ, Finset.sum_range_succ, qQ]

theorem Q33_pos {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 5 / 2) : 0 < Q33.eval x := by
  have h2 := mul_nonneg hx0 hx0
  have h3 := mul_nonneg h2 hx0
  rw [Q33_eval]; nlinarith [h2, h3]

theorem Q33_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : Q33.eval y ≤ Q33.eval x := by
  rw [Q33_eval, Q33_eval]
  have e : (1 + (-34039052338838 / 10 ^ 14) * x + (6086501629812 / 10 ^ 14) * x ^ 2 +
      (-1864476809090 / 10 ^ 14) * x ^ 3) - (1 + (-34039052338838 / 10 ^ 14) * y +
      (6086501629812 / 10 ^ 14) * y ^ 2 + (-1864476809090 / 10 ^ 14) * y ^ 3) =
      (y - x) * (34039052338838 / 10 ^ 14 - (6086501629812 / 10 ^ 14) * (x + y) +
        (1864476809090 / 10 ^ 14) * (x ^ 2 + x * y + y ^ 2)) := by ring
  have hb : 0 ≤ 34039052338838 / 10 ^ 14 - (6086501629812 / 10 ^ 14) * (x + y) +
      (1864476809090 / 10 ^ 14) * (x ^ 2 + x * y + y ^ 2) := by
    nlinarith [mul_nonneg hx (le_trans hx hxy)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hb]

theorem natDegree_P33 : P33.natDegree ≤ 3 :=
  Nat.lt_succ_iff.mp (natDegree_polyOfQ_lt _ (by norm_num))

theorem natDegree_Q33 : Q33.natDegree ≤ 3 :=
  Nat.lt_succ_iff.mp (natDegree_polyOfQ_lt _ (by norm_num))

/-- `S = P − QA`. -/
theorem polyOfQ_sL : polyOfQ sL 31 = P33 - Q33 * polyOfQ aL 28 := by
  ext n
  rw [coeff_sub, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => Q33.coeff i * (polyOfQ aL 28).coeff j)]
  simp only [P33, Q33, coeff_polyOfQ]
  by_cases hn : n < 31
  · have := List.all_eq_true.mp sL_eq n (List.mem_range.mpr hn)
    simp only [decide_eq_true_eq] at this
    rw [ite_eq_left hn, this]
    simp only [Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, apply_ite (Rat.cast : ℚ → ℝ),
      Rat.cast_zero, Nat.succ_eq_add_one]
  · rw [ite_eq_right hn, ite_eq_right (by omega), zero_sub]
    rw [Finset.sum_eq_zero fun k hk => ?_, neg_zero]
    have hk' := Finset.mem_range.mp hk
    by_cases hk4 : k < 4
    · rw [ite_eq_right (show ¬ n - k < 28 by omega), mul_zero]
    · rw [ite_eq_right hk4, zero_mul]

/-- `competitor − A`. -/
theorem polyOfQ_gL : polyOfQ gL 28 = polyOfQ cQ 4 - polyOfQ aL 28 := by
  ext n
  rw [coeff_sub]
  simp only [coeff_polyOfQ]
  by_cases hn : n < 28
  · have := List.all_eq_true.mp gL_eq n (List.mem_range.mpr hn)
    simp only [decide_eq_true_eq] at this
    rw [ite_eq_left hn, ite_eq_left hn, this]
    push_cast
    split_ifs <;> simp
  · rw [ite_eq_right hn, ite_eq_right hn, ite_eq_right (by omega), sub_zero]

theorem ratErr_P33 {x : ℝ} (hQ : Q33.eval x ≠ 0) : ratErr besselJ0 (fun _ => 1) P33 Q33 x =
    (polyOfQ sL 31).eval x / Q33.eval x + ((polyOfQ aL 28).eval x - besselJ0 x) := by
  rw [polyOfQ_sL, ratErr, div_one]
  simp only [eval_sub, eval_mul]
  field_simp
  ring

/-! ### The upper bound on `[0, 0.89357…]` -/

/-- The right end `b₀ = 0.8935769663` of the interval. -/
noncomputable def b0 : ℝ := ((b0Q : ℚ) : ℝ)

theorem b0_eq : b0 = 8935769663 / 10 ^ 10 := by simp [b0, b0Q]

theorem L3S_real {y : ℝ} (hy : |y| ≤ 1) :
    |(derivative^[3] (polyOfQ sL 31)).eval y| ≤ ((16 / 100 : ℚ) : ℝ) := by
  have h := abs_eval_iterate_derivative_le sL (N := 31) (by norm_num) 3 (R := 1) (by norm_num)
    (by exact_mod_cast hy)
  exact h.trans (by exact_mod_cast L3S_le)

/-- On a cell `[c − δ, c + δ] ⊆ [0, 1]` passing the rational check, `|ε| ≤ 1.09·10⁻⁸`. -/
theorem err_le_of_cell {cq δq : ℚ} (hδ : 0 ≤ δq) (hlo : 0 ≤ cq - δq) (hhi : cq + δq ≤ 1)
    (hcheck : cellBoundQ sL 31 (16 / 100) cq δq ≤ (109 / 10 ^ 10 - tauQ) * evQ qQ 4 0 (cq + δq))
    {x : ℝ} (hx : x ∈ Icc ((cq : ℝ) - δq) (cq + δq)) :
    |ratErr besselJ0 (fun _ => 1) P33 Q33 x| ≤ 109 / 10 ^ 10 := by
  have hlo' : (0 : ℝ) ≤ (cq : ℝ) - δq := by exact_mod_cast hlo
  have hhi' : (cq : ℝ) + δq ≤ 1 := by exact_mod_cast hhi
  have hx0 : 0 ≤ x := le_trans hlo' hx.1
  have hx1 : x ≤ 1 := le_trans hx.2 hhi'
  have hQx := Q33_pos hx0 (by linarith)
  -- `|S(x)| ≤ cell bound`
  have hS := cell_diff_rat sL (N := 31) (by norm_num) hδ (L3q := 16 / 100) (fun y hy => L3S_real
    (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)) hx
  have hSx : |(polyOfQ sL 31).eval x| ≤ ((cellBoundQ sL 31 (16 / 100) cq δq : ℚ) : ℝ) := by
    have := abs_sub_abs_le_abs_sub ((polyOfQ sL 31).eval x) ((evQ sL 31 0 cq : ℚ) : ℝ)
    simp only [cellBoundQ]
    push_cast at hS ⊢
    linarith
  -- `Q(x) ≥ Q(c + δ)`
  have hQ : ((evQ qQ 4 0 (cq + δq) : ℚ) : ℝ) ≤ Q33.eval x := by
    rw [← eval_polyOfQ_rat qQ (by norm_num), ← Q33]
    push_cast
    exact Q33_anti hx0 hx.2 hhi'
  have hcheck' : ((cellBoundQ sL 31 (16 / 100) cq δq : ℚ) : ℝ) ≤
      (109 / 10 ^ 10 - ((tauQ : ℚ) : ℝ)) * ((evQ qQ 4 0 (cq + δq) : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hcheck
    push_cast at this ⊢
    exact this
  have htau : ((tauQ : ℚ) : ℝ) = 1 / 10 ^ 17 := by simp [tauQ]
  have hJ := besselJ0_approx (x := x) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [ratErr_P33 hQx.ne']
  have hpos : 0 ≤ 109 / 10 ^ 10 - ((tauQ : ℚ) : ℝ) := by rw [htau]; norm_num
  calc |(polyOfQ sL 31).eval x / Q33.eval x + ((polyOfQ aL 28).eval x - besselJ0 x)|
      ≤ |(polyOfQ sL 31).eval x| / Q33.eval x + |(polyOfQ aL 28).eval x - besselJ0 x| := by
        rw [← abs_of_pos hQx, ← abs_div, abs_of_pos hQx]; exact abs_add_le _ _
    _ ≤ (109 / 10 ^ 10 - ((tauQ : ℚ) : ℝ)) + ((tauQ : ℚ) : ℝ) := by
        gcongr
        · rw [div_le_iff₀ hQx]
          calc _ ≤ _ := hSx
            _ ≤ _ := hcheck'
            _ ≤ _ := mul_le_mul_of_nonneg_left hQ hpos
        · rw [abs_sub_comm]; exact hJ
    _ = 109 / 10 ^ 10 := by ring

/-- **DLMF §3.11(iii), Example**: `|R₃,₃(x) − J₀(x)| ≤ 1.09·10⁻⁸` for `0 ≤ x ≤ 0.8935769663`. -/
theorem dlmf_3_11_iii_table_upper :
    ∀ x ∈ Icc 0 b0, |ratErr besselJ0 (fun _ => 1) P33 Q33 x| ≤ 109 / 10 ^ 10 := by
  intro x hx
  have hb0 : b0 = 8935769663 / 10 ^ 10 := b0_eq
  by_cases hxl : x ≤ 893 / 1000
  · set i := min ⌊1000 * x⌋₊ 892
    have hi : i < 893 := by omega
    have hcheck := List.all_eq_true.mp cellS_all i (List.mem_range.mpr hi)
    simp only [cellS, decide_eq_true_eq] at hcheck
    refine err_le_of_cell (by norm_num) ?_ ?_ hcheck ⟨?_, ?_⟩
    · have : (0 : ℚ) ≤ i := Nat.cast_nonneg i
      linarith
    · have : (i : ℚ) ≤ 892 := by exact_mod_cast (min_le_right _ _)
      linarith
    · have h1 : (i : ℝ) ≤ 1000 * x := by
        have := Nat.floor_le (show 0 ≤ 1000 * x by linarith [hx.1])
        exact le_trans (by exact_mod_cast min_le_left _ _) this
      push_cast
      linarith
    · have h1 : 1000 * x ≤ (i : ℝ) + 1 := by
        rcases le_total ⌊1000 * x⌋₊ 892 with h | h
        · have hi' : i = ⌊1000 * x⌋₊ := min_eq_left h
          rw [hi']
          exact (Nat.lt_floor_add_one _).le
        · have hi' : i = 892 := min_eq_right h
          rw [hi']; push_cast; linarith
      push_cast
      linarith
  · push Not at hxl
    refine err_le_of_cell (cq := (893 / 1000 + b0Q) / 2) (δq := (b0Q - 893 / 1000) / 2)
      (by simp [b0Q]; norm_num) (by simp [b0Q]; norm_num) (by simp [b0Q]; norm_num)
      (by have := cellS_last; simpa [show (893 / 1000 + b0Q) / 2 + (b0Q - 893 / 1000) / 2 = b0Q
        by ring] using this) ⟨?_, ?_⟩
    · push_cast; linarith
    · have := hx.2; rw [hb0] at this; push_cast; simp only [b0Q]; push_cast; linarith

/-! ### The lower bound: alternation at eight points -/

theorem continuousOn_besselJ0 (s : Set ℝ) : ContinuousOn besselJ0 s :=
  continuous_besselJ0.continuousOn

theorem ratAdmissible_P33 {c : ℝ} (hc : c ≤ 5 / 2) : RatAdmissible 0 c 3 3 P33 Q33 :=
  ⟨natDegree_P33, natDegree_Q33, fun _ hx => Q33_pos hx.1 (hx.2.trans hc)⟩

theorem err_at_rat {q : ℚ} (hq0 : 0 ≤ q) (hq : q ≤ 5 / 2) :
    |ratErr besselJ0 (fun _ => 1) P33 Q33 (q : ℝ) - ((errR33 q : ℚ) : ℝ)| ≤ ((tauQ : ℚ) : ℝ) := by
  have hq0' : (0 : ℝ) ≤ q := by exact_mod_cast hq0
  have hq' : (q : ℝ) ≤ 5 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hq; push_cast at this; exact this
  have hJ := besselJ0_approx (x := (q : ℝ)) (abs_le.mpr ⟨by linarith, hq'⟩)
  rw [ratErr, div_one, errR33]
  push_cast
  rw [← eval_polyOfQ_rat pR33 (by norm_num), ← eval_polyOfQ_rat qQ (by norm_num),
    ← eval_polyOfQ_rat aL (by norm_num), ← P33, ← Q33]
  rw [show P33.eval (q : ℝ) / Q33.eval (q : ℝ) - besselJ0 q -
    (P33.eval (q : ℝ) / Q33.eval (q : ℝ) - (polyOfQ aL 28).eval (q : ℝ)) =
      -(besselJ0 q - (polyOfQ aL 28).eval (q : ℝ)) by ring, abs_neg]
  exact hJ

/-- **DLMF §3.11(iii), Example**: every approximation of type `[3, 3]` to `J₀` on
`[0, 0.8935769663]` has maximum error `≥ 1.0821·10⁻⁸`. -/
theorem dlmf_3_11_iii_table_lower {P' Q' : ℝ[X]} (hPQ' : RatAdmissible 0 b0 3 3 P' Q') :
    10821 / 10 ^ 12 ≤ ratMaxErr 0 b0 besselJ0 (fun _ => 1) P' Q' := by
  have hb0 : b0 ≤ 5 / 2 := by rw [b0_eq]; norm_num
  have hpt : ∀ j : Fin 8, 0 ≤ altPt j ∧ altPt j ≤ b0Q := fun j => by
    have := List.all_eq_true.mp altPt_mem j (List.mem_range.mpr j.isLt)
    simpa using this
  refine dlmf_3_11_iii_vallee_poussin (continuousOn_besselJ0 _) continuousOn_const
    (fun _ _ => one_ne_zero) (ratAdmissible_P33 hb0) (x := fun j => ((altPt j : ℚ) : ℝ))
    (Fin.strictMono_iff_lt_succ.mpr fun j => ?_) (fun j => ?_) (Or.inr rfl) (fun j => ?_) hPQ'
  · have := List.all_eq_true.mp altPt_mono j (List.mem_range.mpr j.isLt)
    simp only [decide_eq_true_eq] at this
    simp only [Fin.val_castSucc, Fin.val_succ]
    exact_mod_cast this
  · obtain ⟨h1, h2⟩ := hpt j
    exact ⟨by exact_mod_cast h1, by simp only [b0]; exact_mod_cast h2⟩
  · have hc := List.all_eq_true.mp altPt_check j (List.mem_range.mpr j.isLt)
    simp only [decide_eq_true_eq] at hc
    obtain ⟨h1, h2⟩ := hpt j
    have hb : altPt j ≤ 5 / 2 := h2.trans (by simp [b0Q]; norm_num)
    have he := err_at_rat h1 hb
    have hc' : ((10821 / 10 ^ 12 + tauQ : ℚ) : ℝ) ≤
        ((-((-1) ^ (j : ℕ) * errR33 (altPt j)) : ℚ) : ℝ) := by exact_mod_cast hc
    push_cast at hc'
    have habs := abs_le.mp he
    rcases neg_one_pow_eq_or ℝ (j : ℕ) with h | h <;> rw [h] at hc' ⊢ <;> nlinarith [habs.1, habs.2]

/-- **DLMF §3.11(iii), Example (Table 3.11.1)**: on `[0, 0.8935769663]` the minimax error of
type `[3, 3]` for `J₀` lies in `[1.0821·10⁻⁸, 1.09·10⁻⁸]`, and `R₃,₃` attains error `≤ 1.09·10⁻⁸`:
it is minimax to within `0.75 %`. -/
theorem dlmf_3_11_iii_table_3_11_1 :
    RatAdmissible 0 b0 3 3 P33 Q33 ∧ ratMaxErr 0 b0 besselJ0 (fun _ => 1) P33 Q33 ≤ 109 / 10 ^ 10 ∧
      ∀ P' Q', RatAdmissible 0 b0 3 3 P' Q' →
        10821 / 10 ^ 12 ≤ ratMaxErr 0 b0 besselJ0 (fun _ => 1) P' Q' := by
  have hb0 : b0 ≤ 5 / 2 := by rw [b0_eq]; norm_num
  have hb00 : (0 : ℝ) ≤ b0 := by rw [b0_eq]; norm_num
  exact ⟨ratAdmissible_P33 hb0, ratMaxErr_le hb00 dlmf_3_11_iii_table_upper,
    fun P' Q' h => dlmf_3_11_iii_table_lower h⟩

/-! ### Erratum: the interval is not `[0, j₀,₁]` -/

/-- `j₀,₁`, the first positive zero of `J₀`. -/
noncomputable def j01 : ℝ := sInf {x : ℝ | 0 < x ∧ besselJ0 x = 0}

theorem besselJ0_pos {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 12 / 5) : 0 < besselJ0 x := by
  -- the cell containing `x`
  set i := min ⌊250 * x⌋₊ 599
  have hi : i < 600 := by omega
  have hcheck := List.all_eq_true.mp cellA_all i (List.mem_range.mpr hi)
  simp only [cellA, decide_eq_true_eq] at hcheck
  set cq : ℚ := (2 * i + 1) / 500
  have hxc : x ∈ Icc ((cq : ℝ) - (1 / 500 : ℚ)) (cq + (1 / 500 : ℚ)) := by
    have h1 : (i : ℝ) ≤ 250 * x := le_trans (by exact_mod_cast min_le_left _ _)
      (Nat.floor_le (by linarith))
    have h2 : 250 * x ≤ (i : ℝ) + 1 := by
      rcases le_total ⌊250 * x⌋₊ 599 with h | h
      · rw [show i = ⌊250 * x⌋₊ from min_eq_left h]; exact (Nat.lt_floor_add_one _).le
      · rw [show i = 599 from min_eq_right h]; push_cast; linarith
    simp only [cq]; push_cast
    constructor <;> linarith
  have hy : ∀ y ∈ Icc ((cq : ℝ) - (1 / 500 : ℚ)) (cq + (1 / 500 : ℚ)),
      |y| ≤ ((12 / 5 : ℚ) : ℝ) := by
    intro y hy
    have : (i : ℝ) ≤ 599 := by exact_mod_cast (min_le_right _ _ : i ≤ 599)
    simp only [cq] at hy; push_cast at hy ⊢
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hA := cell_diff_rat aL (N := 28) (by norm_num) (by norm_num) (L3q := 2)
    (fun y hy' => (abs_eval_iterate_derivative_le aL (by norm_num) 3 (by norm_num)
      (hy y hy')).trans (by exact_mod_cast L3A_le)) hxc
  have hJ := besselJ0_approx (x := x) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hcheck' : ((tauQ : ℚ) : ℝ) < ((evQ aL 28 0 cq - (1 / 500) * (|evQ aL 28 1 cq| +
      (1 / 500) * (|evQ aL 28 2 cq| + (1 / 500) * 2)) : ℚ) : ℝ) := by exact_mod_cast hcheck
  push_cast at hA hcheck'
  have := (abs_le.mp hA).1
  have := (abs_le.mp hJ).1
  linarith

theorem besselJ0_241_neg : besselJ0 (241 / 100) < 0 := by
  have hJ := besselJ0_approx (x := ((241 / 100 : ℚ) : ℝ)) (by norm_num)
  rw [eval_polyOfQ_rat aL (by norm_num)] at hJ
  have h := A_241_neg
  have h' : ((evQ aL 28 0 (241 / 100) + tauQ : ℚ) : ℝ) < 0 := by exact_mod_cast h
  push_cast at h' hJ
  have := (abs_le.mp hJ).2
  norm_num at this ⊢
  linarith

/-- `2.4 ≤ j₀,₁ ≤ 2.41`. -/
theorem j01_bounds : 12 / 5 ≤ j01 ∧ j01 ≤ 241 / 100 := by
  have hpos := besselJ0_pos (x := 12 / 5) (by norm_num) le_rfl
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' (show (12 / 5 : ℝ) ≤ 241 / 100 by norm_num)
    continuous_besselJ0.continuousOn
    (show (0 : ℝ) ∈ Icc (besselJ0 (241 / 100)) (besselJ0 (12 / 5)) from
      ⟨besselJ0_241_neg.le, hpos.le⟩)
  have hne : ({x : ℝ | 0 < x ∧ besselJ0 x = 0}).Nonempty := ⟨z, by linarith [hz.1], hz0⟩
  have hbdd : BddBelow {x : ℝ | 0 < x ∧ besselJ0 x = 0} := ⟨0, fun x hx => hx.1.le⟩
  constructor
  · refine le_csInf hne fun x hx => ?_
    by_contra hlt
    push Not at hlt
    exact (besselJ0_pos hx.1.le hlt.le).ne' hx.2
  · exact (csInf_le hbdd ⟨by linarith [hz.1], hz0⟩).trans hz.2

/-- The competitor `0.9975 + 0.0336x − 0.3249x² + 0.0575x³` is within `0.01` of `J₀` on
`[0, 2.41]`. -/
theorem competitor_err {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 241 / 100) :
    |(polyOfQ cQ 4).eval x - besselJ0 x| ≤ 1 / 100 := by
  set i := min ⌊100 * x⌋₊ 240
  have hi : i < 241 := by omega
  have hcheck := List.all_eq_true.mp cellG_all i (List.mem_range.mpr hi)
  simp only [cellG, decide_eq_true_eq] at hcheck
  set cq : ℚ := (2 * i + 1) / 200
  have hxc : x ∈ Icc ((cq : ℝ) - (1 / 200 : ℚ)) (cq + (1 / 200 : ℚ)) := by
    have h1 : (i : ℝ) ≤ 100 * x := le_trans (by exact_mod_cast min_le_left _ _)
      (Nat.floor_le (by linarith))
    have h2 : 100 * x ≤ (i : ℝ) + 1 := by
      rcases le_total ⌊100 * x⌋₊ 240 with h | h
      · rw [show i = ⌊100 * x⌋₊ from min_eq_left h]; exact (Nat.lt_floor_add_one _).le
      · rw [show i = 240 from min_eq_right h]; push_cast; linarith
    simp only [cq]; push_cast
    constructor <;> linarith
  have hy : ∀ y ∈ Icc ((cq : ℝ) - (1 / 200 : ℚ)) (cq + (1 / 200 : ℚ)), |y| ≤ ((5 / 2 : ℚ) : ℝ) := by
    intro y hy
    have : (i : ℝ) ≤ 240 := by exact_mod_cast (min_le_right _ _ : i ≤ 240)
    simp only [cq] at hy; push_cast at hy ⊢
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hG := cell_diff_rat gL (N := 28) (by norm_num) (by norm_num) (L3q := 5 / 2)
    (fun y hy' => (abs_eval_iterate_derivative_le gL (by norm_num) 3 (by norm_num)
      (hy y hy')).trans (by exact_mod_cast L3G_le)) hxc
  have hJ := besselJ0_approx (x := x) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hcheck' : ((cellBoundQ gL 28 (5 / 2) cq (1 / 200) : ℚ) : ℝ) ≤
      ((1 / 100 - tauQ : ℚ) : ℝ) := by
    exact_mod_cast hcheck
  have hGx : |(polyOfQ gL 28).eval x| ≤ ((cellBoundQ gL 28 (5 / 2) cq (1 / 200) : ℚ) : ℝ) := by
    have := abs_sub_abs_le_abs_sub ((polyOfQ gL 28).eval x) ((evQ gL 28 0 cq : ℚ) : ℝ)
    simp only [cellBoundQ]
    push_cast at hG ⊢
    linarith
  rw [polyOfQ_gL, eval_sub] at hGx
  push_cast at hcheck'
  have e : (polyOfQ cQ 4).eval x - besselJ0 x =
      ((polyOfQ cQ 4).eval x - (polyOfQ aL 28).eval x) + ((polyOfQ aL 28).eval x - besselJ0 x) := by
    ring
  rw [e]
  calc _ ≤ |(polyOfQ cQ 4).eval x - (polyOfQ aL 28).eval x| +
        |(polyOfQ aL 28).eval x - besselJ0 x| := abs_add_le _ _
    _ ≤ (1 / 100 - ((tauQ : ℚ) : ℝ)) + ((tauQ : ℚ) : ℝ) := by
        gcongr
        · exact hGx.trans hcheck'
        · rw [abs_sub_comm]; exact hJ
    _ = 1 / 100 := by ring

/-- **Erratum** (DLMF §3.11(iii), Example and Figure 3.11.1, "`0 ≤ x ≤ j₀,₁` … `(= 0.89357…)`"):
`j₀,₁ = 2.40…`, not `0.89357…`, and `R₃,₃` of Table 3.11.1 is not the minimax approximation on
`[0, j₀,₁]`: its error there exceeds `0.04` (at `x = 2.4`), while a cubic polynomial has error
`≤ 0.01`. The table is the minimax approximation on `[0, 0.89357…]`
(`dlmf_3_11_iii_table_3_11_1`). -/
theorem dlmf_3_11_iii_table_erratum :
    12 / 5 ≤ j01 ∧ j01 ≤ 241 / 100 ∧
      1 / 25 ≤ |ratErr besselJ0 (fun _ => 1) P33 Q33 (12 / 5)| ∧
      ¬ IsRatMinimax 0 j01 besselJ0 (fun _ => 1) 3 3 P33 Q33 := by
  obtain ⟨hj1, hj2⟩ := j01_bounds
  have herr : 1 / 25 ≤ |ratErr besselJ0 (fun _ => 1) P33 Q33 (12 / 5)| := by
    have he := err_at_rat (q := 12 / 5) (by norm_num) (by norm_num)
    have hc : ((1 / 25 + tauQ : ℚ) : ℝ) ≤ ((errR33 (12 / 5) : ℚ) : ℝ) := by exact_mod_cast err_24
    push_cast at he hc
    have := (abs_le.mp he).1
    calc (1 / 25 : ℝ) ≤ ratErr besselJ0 (fun _ => 1) P33 Q33 (12 / 5) := by linarith
      _ ≤ _ := le_abs_self _
  refine ⟨hj1, hj2, herr, fun hmin => ?_⟩
  -- the competitor `c(x)/1`
  have hadm : RatAdmissible 0 j01 3 3 (polyOfQ cQ 4) 1 :=
    ⟨Nat.lt_succ_iff.mp (natDegree_polyOfQ_lt _ (by norm_num)), by simp, fun _ _ => by simp⟩
  have hc : ratMaxErr 0 j01 besselJ0 (fun _ => 1) (polyOfQ cQ 4) 1 ≤ 1 / 100 :=
    ratMaxErr_le (by linarith) fun x hx => by
      simp only [ratErr, eval_one, div_one]
      exact competitor_err hx.1 (hx.2.trans hj2)
  have h1 := hmin.2 _ _ hadm
  have h2 := abs_ratErr_le (continuousOn_besselJ0 _) continuousOn_const (fun _ _ => one_ne_zero)
    (fun y hy => (hmin.1.2.2 y hy).ne') (P := P33) (show (12 / 5 : ℝ) ∈ Icc 0 j01 from
      ⟨by norm_num, hj1⟩)
  linarith

end Azurite.DLMF
