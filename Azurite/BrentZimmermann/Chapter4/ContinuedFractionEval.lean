/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.ContinuedFraction

/-!
# Brent–Zimmermann §4.6: Evaluating continued fractions; Theorem 4.1

For the finite fraction `y = a₁/b₁+ a₂/b₂+ … a_k/b_k` (4.42):

* the *backward recurrence* `R_k = 1`, `R_{k−1} = b_k`, `R_j = b_{j+1} R_{j+1} + a_{j+2} R_{j+2}`
  (4.43) gives `y = a₁ R₁ / R₀`, with the invariant
  `R_j / R_{j−1} = 1/b_j+ a_{j+1}/b_{j+1}+ … a_k/b_k`;
* the *forward recurrence* `P₀ = 0, P₁ = a₁, Q₀ = 1, Q₁ = b₁`, `P_j = b_j P_{j−1} + a_j P_{j−2}`,
  `Q_j = b_j Q_{j−1} + a_j Q_{j−2}` (4.44) gives `y = P_k / Q_k`.

The forward recurrence needs no cutoff in advance — stop when `D_k = P_k/Q_k − P_{k−1}/Q_{k−1}`
(4.45) is small — but costs twice as much and may be less stable; a good strategy is forward in
single precision to find `k`, then backward in multiple precision, with `D_k` computed by
`D₁ = a₁/b₁`, `D_j = −a_j Q_{j−2} D_{j−1} / Q_j` (4.46) to avoid the cancellation in (4.45).

**Theorem 4.1.**  If `a_j > 0` and `b_j > 0` for `j ≥ 1`, the even approximants increase strictly
and the odd ones decrease strictly, so `f_{2k} < f < f_{2k+1}` and
`|f − (f_{m−1} + f_m)/2| < |f_m − f_{m−1}| / 2`.

What is formalized (with `b₀` as the head, so that (4.42) is `approximant a b k` with `b 0 = 0`):

* `tailFrac a b k j` — the tail `a_j/b_j+ … a_k/b_k`; `approximant_eq_tailFrac`.
* `backR a b k j` — the backward recurrence (4.43); `backR_pos`, `backR_pred` (the invariant in
  product form, `R_{j−1} = (b_j + T_{j+1}) R_j`), `backR_div` (the text's invariant), and
  `approximant_eq_backR` (`y = b₀ + a₁ R₁/R₀`).
* The forward recurrence is Mathlib's continuants: `nums`/`dens` with head `0` satisfy
  `P₀ = 0`, `P₁ = a₁`, `Q₀ = 1`, `Q₁ = b₁` and (4.44) (`nums_zero`, `nums_one`, …, from the previous
  file); `dens_pos`.
* `diff a b k = f_k − f_{k−1}` (4.45), `det_succ` (the determinant identity
  `Δ_{j+1} = −a_{j+1} Δ_j`), `diff_eq_det_div`, `diff_succ` (4.46), `diff_one`.
* Theorem 4.1: `sign_diff`, `abs_diff_succ_lt`, `approximant_even_strictMono`,
  `diff_odd_pos`, `diff_even_neg`, `approximant_odd_strictAnti`, `approximant_even_lt_odd`, and
  with the value `f`:
  `approximant_even_lt`, `lt_approximant_odd`, `abs_sub_midpoint_lt`.
-/

namespace Azurite

namespace BZ

open Filter Topology GenContFract Finset

/-! ### Tails and the backward recurrence -/

/-- The tail `a_j/b_j+ a_{j+1}/b_{j+1}+ … a_k/b_k` of a finite continued fraction
(`0` if `j > k`). -/
noncomputable def tailFrac (a b : ℕ → ℝ) (k j : ℕ) : ℝ :=
  if k < j then 0 else a j / (b j + tailFrac a b k (j + 1))
termination_by k + 1 - j

theorem tailFrac_of_lt (a b : ℕ → ℝ) {k j : ℕ} (h : k < j) : tailFrac a b k j = 0 := by
  rw [tailFrac, ite_eq_left h]

theorem tailFrac_of_le (a b : ℕ → ℝ) {k j : ℕ} (h : j ≤ k) :
    tailFrac a b k j = a j / (b j + tailFrac a b k (j + 1)) := by
  rw [tailFrac, ite_eq_right (not_lt.mpr h)]

/-- Shifting the sequences shifts the tail. -/
theorem tailFrac_shift (a b : ℕ → ℝ) (k j : ℕ) :
    tailFrac a b (k + 1) (j + 1) = tailFrac (fun i => a (i + 1)) (fun i => b (i + 1)) k j := by
  by_cases hj : k < j
  · rw [tailFrac_of_lt _ _ (by omega), tailFrac_of_lt _ _ hj]
  · rw [tailFrac_of_le a b (k := k + 1) (j := j + 1) (by omega), tailFrac_of_le _ _ (not_lt.mp hj),
      tailFrac_shift a b k (j + 1)]
termination_by k + 1 - j

/-- The approximant is the head plus the tail from `j = 1`. -/
theorem approximant_eq_tailFrac (a b : ℕ → ℝ) (k : ℕ) :
    approximant a b k = b 0 + tailFrac a b k 1 := by
  induction k generalizing a b with
  | zero => rw [approximant_zero, tailFrac_of_lt _ _ (by omega), add_zero]
  | succ k ih =>
    rw [approximant_succ, ih, tailFrac_of_le a b (k := k + 1) (j := 1) (by omega),
      tailFrac_shift a b k 1]

/-- Nonnegativity of the tails for positive coefficients. -/
theorem tailFrac_nonneg {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k : ℕ) {j : ℕ}
    (hj : 1 ≤ j) : 0 ≤ tailFrac a b k j := by
  by_cases hkj : k < j
  · rw [tailFrac_of_lt _ _ hkj]
  · rw [tailFrac_of_le _ _ (not_lt.mp hkj)]
    have hT := tailFrac_nonneg hpos k (j := j + 1) (by omega)
    obtain ⟨ha, hb⟩ := hpos j hj
    positivity
termination_by k + 1 - j

/-- The backward recurrence (4.43): `R_k = 1`, `R_{k−1} = b_k`,
`R_j = b_{j+1} R_{j+1} + a_{j+2} R_{j+2}`. -/
noncomputable def backR (a b : ℕ → ℝ) (k j : ℕ) : ℝ :=
  if k ≤ j then 1
  else if k = j + 1 then b k
  else b (j + 1) * backR a b k (j + 1) + a (j + 2) * backR a b k (j + 2)
termination_by k - j

theorem backR_self (a b : ℕ → ℝ) (k : ℕ) : backR a b k k = 1 := by
  rw [backR, ite_eq_left le_rfl]

theorem backR_pred_self (a b : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) : backR a b k (k - 1) = b k := by
  rw [backR, ite_eq_right (by omega), ite_eq_left (by omega)]

theorem backR_of_lt (a b : ℕ → ℝ) {k j : ℕ} (h : j + 2 ≤ k) :
    backR a b k j = b (j + 1) * backR a b k (j + 1) + a (j + 2) * backR a b k (j + 2) := by
  rw [backR, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The invariant in product form: `R_{j−1} = (b_j + T_{j+1}) R_j` for `1 ≤ j ≤ k`, where
`T_{j+1} = a_{j+1}/b_{j+1}+ … a_k/b_k`. -/
theorem backR_pred {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) {k j : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ k) :
    backR a b k (j - 1) = (b j + tailFrac a b k (j + 1)) * backR a b k j := by
  rcases eq_or_lt_of_le hjk with hkj | hkj
  · subst hkj
    rw [backR_pred_self _ _ hj, backR_self, tailFrac_of_lt _ _ (by omega)]
    ring
  · have hrec := backR_of_lt a b (k := k) (j := j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega] at hrec
    have hih := backR_pred hpos (k := k) (j := j + 1) (by omega) hkj
    rw [show j + 1 - 1 = j by omega] at hih
    have hT := tailFrac_of_le a b (k := k) (j := j + 1) hkj
    have hden : 0 < b (j + 1) + tailFrac a b k (j + 2) := by
      have := tailFrac_nonneg hpos k (j := j + 2) (by omega)
      have := hpos (j + 1) (by omega)
      linarith
    rw [hrec, hih, hT]
    field_simp
termination_by k - j

theorem backR_pos {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k : ℕ) (j : ℕ) :
    0 < backR a b k j := by
  by_cases hkj : k ≤ j
  · rw [backR, ite_eq_left hkj]; exact one_pos
  · by_cases hk1 : k = j + 1
    · rw [backR, ite_eq_right hkj, ite_eq_left hk1]; exact (hpos k (by omega)).2
    · rw [backR_of_lt a b (by omega)]
      have h1 := backR_pos hpos k (j + 1)
      have h2 := backR_pos hpos k (j + 2)
      obtain ⟨-, hb⟩ := hpos (j + 1) (by omega)
      obtain ⟨ha, -⟩ := hpos (j + 2) (by omega)
      positivity
termination_by k - j

/-- The text's invariant: `R_j / R_{j−1} = 1/b_j+ a_{j+1}/b_{j+1}+ … a_k/b_k`. -/
theorem backR_div {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) {k j : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ k) :
    backR a b k j / backR a b k (j - 1) = 1 / (b j + tailFrac a b k (j + 1)) := by
  rw [backR_pred hpos hj hjk]
  have hR := backR_pos hpos k j
  have hden : 0 < b j + tailFrac a b k (j + 1) := by
    have := tailFrac_nonneg hpos k (j := j + 1) (by omega)
    have := hpos j hj
    linarith
  field_simp

/-- The backward recurrence evaluates the fraction: `y = b₀ + a₁ R₁ / R₀`. -/
theorem approximant_eq_backR {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) {k : ℕ}
    (hk : 1 ≤ k) : approximant a b k = b 0 + a 1 * backR a b k 1 / backR a b k 0 := by
  rw [approximant_eq_tailFrac, tailFrac_of_le _ _ hk]
  have h := backR_pred hpos (k := k) (j := 1) le_rfl hk
  simp only [Nat.sub_self] at h
  rw [h]
  have hR := backR_pos hpos k 1
  have hden : 0 < b 1 + tailFrac a b k 2 := by
    have := tailFrac_nonneg hpos k (j := 2) (by omega)
    have := hpos 1 le_rfl
    linarith
  field_simp

/-! ### The forward recurrence and the differences `D_k` -/

/-- The denominators `Q_j` are positive for positive coefficients. -/
theorem dens_pos {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (n : ℕ) :
    0 < (contFrac a b).dens n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [dens_zero]; exact one_pos
    | 1 => rw [dens_one]; exact (hpos 1 le_rfl).2
    | n + 2 =>
      rw [dens_recurrence']
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      obtain ⟨ha, hb⟩ := hpos (n + 2) (by omega)
      positivity

/-- `D_k = f_k − f_{k−1}` (4.45), with `D_0 = 0`. -/
noncomputable def diff (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => approximant a b (k + 1) - approximant a b k

/-- The determinant `Δ_j = P_j Q_{j−1} − P_{j−1} Q_j` satisfies `Δ_{j+1} = −a_{j+1} Δ_j`. -/
theorem det_succ (a b : ℕ → ℝ) (j : ℕ) :
    (contFrac a b).nums (j + 2) * (contFrac a b).dens (j + 1)
        - (contFrac a b).nums (j + 1) * (contFrac a b).dens (j + 2)
      = -a (j + 2) * ((contFrac a b).nums (j + 1) * (contFrac a b).dens j
        - (contFrac a b).nums j * (contFrac a b).dens (j + 1)) := by
  rw [nums_recurrence', dens_recurrence']
  ring

/-- `D_{j+1} = Δ_{j+1} / (Q_{j+1} Q_j)` for positive coefficients. -/
theorem diff_eq_det_div {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (j : ℕ) :
    diff a b (j + 1) = ((contFrac a b).nums (j + 1) * (contFrac a b).dens j
      - (contFrac a b).nums j * (contFrac a b).dens (j + 1))
        / ((contFrac a b).dens (j + 1) * (contFrac a b).dens j) := by
  rw [diff, approximant_eq_convs hpos, approximant_eq_convs hpos, convs, convs]
  have h1 := dens_pos hpos j
  have h2 := dens_pos hpos (j + 1)
  field_simp

/-- `D₁ = a₁ / b₁`. -/
theorem diff_one (a b : ℕ → ℝ) : diff a b 1 = a 1 / b 1 := by
  rw [diff, approximant_one, approximant_zero]; ring

/-- (4.46): `D_{j+2} = −a_{j+2} Q_j D_{j+1} / Q_{j+2}`. -/
theorem diff_succ {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (j : ℕ) :
    diff a b (j + 2)
      = -a (j + 2) * (contFrac a b).dens j * diff a b (j + 1) / (contFrac a b).dens (j + 2) := by
  rw [diff_eq_det_div hpos (j + 1), diff_eq_det_div hpos j, det_succ]
  have h0 := dens_pos hpos j
  have h1 := dens_pos hpos (j + 1)
  have h2 := dens_pos hpos (j + 2)
  field_simp

/-! ### Theorem 4.1 -/

/-- `D_{j+1}` has the sign `(−1)^j`: `D₁ > 0`, `D₂ < 0`, …. -/
theorem sign_diff {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (j : ℕ) :
    0 < (-1) ^ j * diff a b (j + 1) := by
  induction j with
  | zero =>
    rw [pow_zero, one_mul, diff_one]
    obtain ⟨ha, hb⟩ := hpos 1 le_rfl
    positivity
  | succ j ih =>
    rw [diff_succ hpos j, pow_succ]
    have h0 := dens_pos hpos j
    have h2 := dens_pos hpos (j + 2)
    have ha := (hpos (j + 2) (by omega)).1
    have : (-1) ^ j * -1 * (-a (j + 2) * (contFrac a b).dens j * diff a b (j + 1)
        / (contFrac a b).dens (j + 2))
        = (a (j + 2) * (contFrac a b).dens j / (contFrac a b).dens (j + 2))
          * ((-1) ^ j * diff a b (j + 1)) := by ring
    rw [this]
    positivity

/-- `|D_{j+2}| < |D_{j+1}|`: the differences shrink strictly. -/
theorem abs_diff_succ_lt {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (j : ℕ) :
    |diff a b (j + 2)| < |diff a b (j + 1)| := by
  rw [diff_succ hpos j, abs_div, abs_mul, abs_mul, abs_neg, abs_of_pos (hpos (j + 2) (by omega)).1,
    abs_of_pos (dens_pos hpos j), abs_of_pos (dens_pos hpos (j + 2)),
    div_lt_iff₀ (dens_pos hpos (j + 2))]
  have hD : 0 < |diff a b (j + 1)| := by
    have := sign_diff hpos j
    exact abs_pos.mpr fun h => by rw [h, mul_zero] at this; exact lt_irrefl _ this
  have hQ : a (j + 2) * (contFrac a b).dens j < (contFrac a b).dens (j + 2) := by
    rw [dens_recurrence']
    have := mul_pos (hpos (j + 2) (by omega)).2 (dens_pos hpos (j + 1))
    linarith
  calc a (j + 2) * (contFrac a b).dens j * |diff a b (j + 1)|
      < (contFrac a b).dens (j + 2) * |diff a b (j + 1)| := by gcongr
    _ = |diff a b (j + 1)| * (contFrac a b).dens (j + 2) := mul_comm _ _

/-- `D_{2k+1} > 0`. -/
theorem diff_odd_pos {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k : ℕ) :
    0 < diff a b (2 * k + 1) := by
  have := sign_diff hpos (2 * k)
  rwa [pow_mul, neg_one_sq, one_pow, one_mul] at this

/-- `D_{2k+2} < 0`. -/
theorem diff_even_neg {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k : ℕ) :
    diff a b (2 * k + 2) < 0 := by
  have := sign_diff hpos (2 * k + 1)
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul,
    neg_one_mul] at this
  exact neg_pos.mp this

/-- Even approximants increase strictly. -/
theorem approximant_even_lt_succ {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k : ℕ) :
    approximant a b (2 * k) < approximant a b (2 * k + 2) := by
  have h1 := diff_odd_pos hpos k
  have h2 := diff_even_neg hpos k
  have h3 := abs_diff_succ_lt hpos (2 * k)
  have hd1 : diff a b (2 * k + 1) = approximant a b (2 * k + 1) - approximant a b (2 * k) := rfl
  have hd2 : diff a b (2 * k + 2) = approximant a b (2 * k + 2) - approximant a b (2 * k + 1) := rfl
  rw [abs_of_neg h2, abs_of_pos h1] at h3
  linarith

/-- Odd approximants decrease strictly. -/
theorem approximant_odd_succ_lt {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k : ℕ) :
    approximant a b (2 * k + 3) < approximant a b (2 * k + 1) := by
  have h1 := diff_even_neg hpos k
  have h2 : 0 < diff a b (2 * k + 3) := by
    have := diff_odd_pos hpos (k + 1)
    rwa [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at this
  have h3 := abs_diff_succ_lt hpos (2 * k + 1)
  rw [show 2 * k + 1 + 2 = 2 * k + 3 by omega, show 2 * k + 1 + 1 = 2 * k + 2 by omega,
    abs_of_pos h2, abs_of_neg h1] at h3
  have hd1 : diff a b (2 * k + 2) = approximant a b (2 * k + 2) - approximant a b (2 * k + 1) := rfl
  have hd2 : diff a b (2 * k + 3) = approximant a b (2 * k + 3) - approximant a b (2 * k + 2) := rfl
  linarith

theorem approximant_even_strictMono {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) :
    StrictMono (fun k => approximant a b (2 * k)) :=
  strictMono_nat_of_lt_succ fun k => by
    simpa [show 2 * (k + 1) = 2 * k + 2 by ring] using approximant_even_lt_succ hpos k

theorem approximant_odd_strictAnti {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) :
    StrictAnti (fun k => approximant a b (2 * k + 1)) :=
  strictAnti_nat_of_succ_lt fun k => by
    simpa [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] using approximant_odd_succ_lt hpos k

/-- Every even approximant is below every odd one. -/
theorem approximant_even_lt_odd {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k m : ℕ) :
    approximant a b (2 * k) < approximant a b (2 * m + 1) := by
  have hE := approximant_even_strictMono hpos
  have hO := approximant_odd_strictAnti hpos
  -- compare through the index `n = max k m`: `f_{2k} ≤ f_{2n} < f_{2n+1} ≤ f_{2m+1}`
  have h1 : approximant a b (2 * k) ≤ approximant a b (2 * max k m) := hE.monotone (le_max_left _ _)
  have h2 : approximant a b (2 * max k m) < approximant a b (2 * max k m + 1) := by
    have := diff_odd_pos hpos (max k m)
    have hd : diff a b (2 * max k m + 1)
        = approximant a b (2 * max k m + 1) - approximant a b (2 * max k m) := rfl
    linarith
  have h3 : approximant a b (2 * max k m + 1) ≤ approximant a b (2 * m + 1) :=
    hO.antitone (le_max_right _ _)
  linarith

/-- Theorem 4.1, the bracket: if the fraction converges to `f`, then `f_{2k} < f < f_{2k+1}`. -/
theorem approximant_even_lt {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) {f : ℝ}
    (hf : HasContFracValue a b f) (k : ℕ) : approximant a b (2 * k) < f := by
  have hE := approximant_even_strictMono hpos
  have htend : Tendsto (fun k => approximant a b (2 * k)) atTop (𝓝 f) :=
    hf.comp (tendsto_atTop_mono (fun k => by show k ≤ _; omega) tendsto_id)
  have hle := hE.monotone.ge_of_tendsto htend (k + 1)
  exact lt_of_lt_of_le (hE (Nat.lt_succ_self k)) hle

theorem lt_approximant_odd {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) {f : ℝ}
    (hf : HasContFracValue a b f) (k : ℕ) : f < approximant a b (2 * k + 1) := by
  have hO := approximant_odd_strictAnti hpos
  have htend : Tendsto (fun k => approximant a b (2 * k + 1)) atTop (𝓝 f) :=
    hf.comp (tendsto_atTop_mono (fun k => by show k ≤ _; omega) tendsto_id)
  have hle := hO.antitone.le_of_tendsto htend (k + 1)
  exact lt_of_le_of_lt hle (hO (Nat.lt_succ_self k))

/-- Theorem 4.1, the error bound: `|f − (f_{m−1} + f_m)/2| < |f_m − f_{m−1}| / 2` for `m ≥ 1`. -/
theorem abs_sub_midpoint_lt {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) {f : ℝ}
    (hf : HasContFracValue a b f) {m : ℕ} (hm : 1 ≤ m) :
    |f - (approximant a b (m - 1) + approximant a b m) / 2|
      < |approximant a b m - approximant a b (m - 1)| / 2 := by
  -- `f` lies strictly between `f_{m−1}` and `f_m`, whichever is the even one
  obtain ⟨k, hk⟩ : ∃ k, m - 1 = 2 * k ∨ m - 1 = 2 * k + 1 := ⟨(m - 1) / 2, by omega⟩
  rcases hk with hk | hk
  · -- `m − 1 = 2k` even, `m = 2k + 1` odd
    have hm' : m = 2 * k + 1 := by omega
    have h1 := approximant_even_lt hpos hf k
    have h2 := lt_approximant_odd hpos hf k
    rw [hk, hm']
    rw [abs_lt, abs_of_pos (by linarith)]
    constructor <;> linarith
  · -- `m − 1 = 2k + 1` odd, `m = 2k + 2` even
    have hm' : m = 2 * (k + 1) := by omega
    have h1 := approximant_even_lt hpos hf (k + 1)
    have h2 := lt_approximant_odd hpos hf k
    rw [hk, hm']
    rw [abs_lt, abs_of_neg (by linarith)]
    constructor <;> linarith

end BZ

end Azurite
