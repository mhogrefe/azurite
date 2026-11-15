/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section12Sine
import Azurite.DLMF.Chapter6.Section3
import Azurite.DLMF.Chapter6.Section13Poly
import Azurite.DLMF.Chapter2.Section10Contour

/-!
# DLMF §6.13: zeros

Formalizations of <https://dlmf.nist.gov/6.13>.

## Main results

* `dlmf_6_13_Ei_zero`, `dlmf_6_13_Ei_zero_unique`: `Ei` has exactly one real zero `x₀`, in
  `(0, 1)` (from §6.3; `Ei(x) < 0` for `x < 0`, `Ei_neg_lt`).  The value 6.13.1 is deferred.
* `ciZero`, `siZero`, `dlmf_6_13_Ci_zeros`, `dlmf_6_13_si_zeros`: the positive zeros
  `c₀ < c₁ < ⋯` of `Ci` and `s₀ < s₁ < ⋯` of `si`, infinitely many and exhausting all positive
  zeros; `c₀ ∈ (0, π/2)`, `c_k ∈ ((k − 1/2)π, (k + 1/2)π)`, `s_k ∈ (kπ, (k + 1)π)`.
* `dlmf_6_13_2`: `c_k, s_k = α + 1/α − 16/(3α³) + 1673/(15α⁵) − 507746/(105α⁷) + O(α^{−9})`,
  `α = kπ` resp. `(k + 1/2)π`.  Both zero equations become
  `f(x) sin(x − α) = g(x) cos(x − α)` (`CiR_eq_psi`, `siR_eq_psi`, from 6.2.19, 6.2.20).  A zero
  lies in `(α, α + 4/α]` (`zero_location`); at `Q = zeroAsymp α` the residual is `O(α^{−10})`
  (`zero_residual_bound`: §6.12(ii)'s real remainder bounds for four terms of `f`, `g`, Taylor
  bounds for `sin`, `cos` (`sin_taylor_le`, `cos_taylor_le`), and the cancellation of the
  coefficients of `t⁰, …, t⁹`, `zero_poly_identity` in `Section13Poly`); the mean value theorem
  with derivative `cos(x − α)/x ≥ 1/(4α)` converts it into `O(α^{−9})` (`zero_asymp_core`).
* Not formalized here: the property that the remainder of 6.13.2 after `n` terms does not exceed
  the `(n+1)`th term in absolute value and has its sign (MacLeod 2002a, Nemes 2025), and the
  30D values of `c₁`, `c₂` (MacLeod 1996b).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The real zero of `Ei` -/

/-- **DLMF §6.13**: `Ei(x)` has exactly one real zero `x₀` (`Ei` is defined for `x ≠ 0`); it lies
in `(0, 1)`.  Its value 6.13.1, `x₀ = 0.37250 74107 …`, is deferred (numerics). -/
theorem dlmf_6_13_Ei_zero : ∃! x₀ : ℝ, x₀ ≠ 0 ∧ Ei x₀ = 0 ∧ 0 < x₀ ∧ x₀ < 1 := by
  obtain ⟨x₀, ⟨h0, hz, h1⟩, huniq⟩ := dlmf_6_3_F1_Ei_zero_unique
  refine ⟨x₀, ⟨h0.ne', hz, h0, h1⟩, fun y ⟨_, hy, hy0, hy1⟩ => huniq y ⟨hy0, hy, hy1⟩⟩

/-- `Ei(x) < 0` for `x < 0`, so the zero of `dlmf_6_13_Ei_zero` is the only one with `x ≠ 0`. -/
theorem Ei_neg_lt {x : ℝ} (hx : x < 0) : Ei x < 0 := by
  have h := (dlmf_6_2_6 (x := -x) (by linarith)).2
  rw [neg_neg, dlmf_6_3_F1_real (by linarith)] at h
  have := dlmf_6_3_F1_E1_pos (x := -x) (by linarith)
  have h' : Ei x = -expIntE₁R (-x) := by exact_mod_cast h
  linarith

theorem dlmf_6_13_Ei_zero_unique {x : ℝ} (hx : x ≠ 0) (h : Ei x = 0) : 0 < x ∧ x < 1 := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · exact absurd h (Ei_neg_lt hn).ne
  · exact ⟨hp, Ei_unique_pos hp h⟩
where
  Ei_unique_pos {x : ℝ} (hp : 0 < x) (h : Ei x = 0) : x < 1 := by
    by_contra hge
    push Not at hge
    have h1 : Ei 1 ≤ Ei x := dlmf_6_3_F1_Ei_mono.monotoneOn (mem_Ioi.2 one_pos) hp hge
    obtain ⟨x₀, ⟨h0, hz, hx₁⟩, -⟩ := dlmf_6_3_F1_Ei_zero_unique
    have h2 : Ei x₀ < Ei 1 := dlmf_6_3_F1_Ei_mono h0 (mem_Ioi.2 one_pos) hx₁
    linarith

/-! ### The zeros `c_k` of `Ci` and `s_k` of `si` -/

/-- The zeros `c_k` of `Ci`: `c₀ ∈ (0, π/2)`, `c_k ∈ ((k − 1/2)π, (k + 1/2)π)` for `k ≥ 1`. -/
noncomputable def ciZero : ℕ → ℝ
  | 0 => dlmf_6_3_F2_Ci_zeros.1.exists.choose
  | n + 1 => (dlmf_6_3_F2_Ci_zeros.2 n).exists.choose

theorem ciZero_zero_spec : ciZero 0 ∈ Ioo 0 (π / 2) ∧ CiR (ciZero 0) = 0 :=
  dlmf_6_3_F2_Ci_zeros.1.exists.choose_spec

theorem ciZero_succ_spec (n : ℕ) :
    ciZero (n + 1) ∈ Ioo ((n + 1 / 2) * π) ((n + 3 / 2) * π) ∧ CiR (ciZero (n + 1)) = 0 :=
  (dlmf_6_3_F2_Ci_zeros.2 n).exists.choose_spec

/-- `c_k` lies within `π/2` of `kπ` for `k ≥ 1`. -/
theorem ciZero_mem {k : ℕ} (hk : 1 ≤ k) :
    ciZero k ∈ Ioo (k * π - π / 2) (k * π + π / 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨⟨h1, h2⟩, -⟩ := ciZero_succ_spec n
  push_cast
  constructor <;> linarith

/-- The zeros `s_k` of `si`: `s_k ∈ (kπ, (k + 1)π)`. -/
noncomputable def siZero (k : ℕ) : ℝ := (dlmf_6_3_F2_Si_cross k).exists.choose

theorem siZero_spec (k : ℕ) :
    siZero k ∈ Ioo ((k : ℝ) * π) ((k + 1) * π) ∧ SiR (siZero k) = π / 2 :=
  (dlmf_6_3_F2_Si_cross k).exists.choose_spec

theorem CiR_half_ne (n : ℕ) : CiR ((n + 1 / 2) * π) ≠ 0 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have := (dlmf_6_3_F2_Ci_extrema m).1
    push_cast
    rw [show ((m : ℝ) + m + 1 / 2) * π = (2 * m + 1 / 2) * π by ring]
    exact this.ne'
  · have := (dlmf_6_3_F2_Ci_extrema m).2.1
    push_cast
    rw [show (2 * (m : ℝ) + 1 + 1 / 2) * π = (2 * m + 3 / 2) * π by ring]
    exact this.ne

theorem SiR_nat_mul_pi_ne (n : ℕ) : SiR (n * π) ≠ π / 2 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have := (dlmf_6_3_F2_Si_extrema m).1
    push_cast
    rw [show ((m : ℝ) + m) * π = 2 * m * π by ring]
    exact this.ne
  · have := (dlmf_6_3_F2_Si_extrema m).2.1
    push_cast
    exact this.ne'

/-- **DLMF §6.13**: `Ci(x)` has infinitely many positive real zeros; `c₀ < c₁ < c₂ < ⋯`
(`ciZero`) are all of them, in ascending order. -/
theorem dlmf_6_13_Ci_zeros :
    StrictMono ciZero ∧ (∀ k, 0 < ciZero k ∧ Ci (ciZero k) = 0) ∧
      ∀ x : ℝ, 0 < x → Ci x = 0 → ∃ k, ciZero k = x := by
  have hπ := Real.pi_pos
  have hspec : ∀ k, 0 < ciZero k ∧ CiR (ciZero k) = 0 := by
    rintro (_ | n)
    · exact ⟨ciZero_zero_spec.1.1, ciZero_zero_spec.2⟩
    · obtain ⟨⟨h1, -⟩, h⟩ := ciZero_succ_spec n
      exact ⟨lt_of_le_of_lt (by positivity) h1, h⟩
  refine ⟨strictMono_nat_of_lt_succ fun k => ?_, fun k => ⟨(hspec k).1, ?_⟩, fun x hx h => ?_⟩
  · rcases k with _ | n
    · have := ciZero_zero_spec.1.2
      have := (ciZero_succ_spec 0).1.1
      push_cast at this
      linarith
    · have := (ciZero_succ_spec n).1.2
      have := (ciZero_succ_spec (n + 1)).1.1
      push_cast at *
      linarith
  · rw [dlmf_6_3_F2_Ci_real (hspec k).1, (hspec k).2, ofReal_zero]
  · rw [dlmf_6_3_F2_Ci_real hx, ofReal_eq_zero] at h
    rcases lt_trichotomy x (π / 2) with hlt | heq | hgt
    · exact ⟨0, dlmf_6_3_F2_Ci_zeros.1.unique ciZero_zero_spec ⟨⟨hx, hlt⟩, h⟩⟩
    · exact absurd (heq ▸ h) (by
        have := CiR_half_ne 0
        rwa [show ((0 : ℕ) + 1 / 2 : ℝ) * π = π / 2 by push_cast; ring] at this)
    · obtain ⟨n, hn⟩ := exists_mem_Icc_nat_mul_pi (x := x - π / 2) (by linarith)
      have hne : x ≠ (n + 1 / 2) * π := fun e => CiR_half_ne n (e ▸ h)
      have hne' : x ≠ ((n + 1 : ℕ) + 1 / 2) * π := fun e => CiR_half_ne (n + 1) (e ▸ h)
      push_cast at hne'
      refine ⟨n + 1, (dlmf_6_3_F2_Ci_zeros.2 n).unique (ciZero_succ_spec n) ⟨⟨?_, ?_⟩, h⟩⟩
      · exact lt_of_le_of_ne (by linarith [hn.1]) (Ne.symm hne)
      · refine lt_of_le_of_ne (by linarith [hn.2]) ?_
        intro e; exact hne' (by rw [e]; ring)

/-- **DLMF §6.13**: `si(x)` has infinitely many positive real zeros; `s₀ < s₁ < s₂ < ⋯`
(`siZero`) are all of them, in ascending order. -/
theorem dlmf_6_13_si_zeros :
    StrictMono siZero ∧ (∀ k, 0 < siZero k ∧ si (siZero k) = 0) ∧
      ∀ x : ℝ, 0 < x → si x = 0 → ∃ k, siZero k = x := by
  have hπ := Real.pi_pos
  have hsi : ∀ x : ℝ, si x = ((SiR x - π / 2 : ℝ) : ℂ) := fun x => by
    rw [(dlmf_6_2_10 x).2, dlmf_6_3_F2_Si_real]; push_cast; ring
  refine ⟨strictMono_nat_of_lt_succ fun k => ?_, fun k => ⟨?_, ?_⟩, fun x hx h => ?_⟩
  · have := (siZero_spec k).1.2
    have := (siZero_spec (k + 1)).1.1
    push_cast at *
    linarith
  · exact lt_of_le_of_lt (by positivity) (siZero_spec k).1.1
  · rw [hsi, (siZero_spec k).2, sub_self, ofReal_zero]
  · rw [hsi, ofReal_eq_zero, sub_eq_zero] at h
    obtain ⟨n, hn⟩ := exists_mem_Icc_nat_mul_pi hx.le
    have hne : x ≠ n * π := fun e => SiR_nat_mul_pi_ne n (e ▸ h)
    have hne' : x ≠ (n + 1 : ℕ) * π := fun e => SiR_nat_mul_pi_ne (n + 1) (e ▸ h)
    push_cast at hne'
    exact ⟨n, (dlmf_6_3_F2_Si_cross n).unique (siZero_spec n)
      ⟨⟨lt_of_le_of_ne hn.1 (Ne.symm hne), lt_of_le_of_ne hn.2 hne'⟩, h⟩⟩

/-! ### Real forms of `f`, `g` and the zero equation -/

/-- `f(x)` at real `x > 0` (a real number, `fR_gR_spec`). -/
noncomputable def fR (x : ℝ) : ℝ := (auxF x).re

/-- `g(x)` at real `x > 0`. -/
noncomputable def gR (x : ℝ) : ℝ := (auxG x).re

/-- The real partial sum `∑_{m<n} (−1)^m (2m)!/x^{2m+1}` of 6.12.3. -/
noncomputable def fS (n : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, (-1) ^ m * ((2 * m) ! : ℝ) / x ^ (2 * m + 1)

/-- The real partial sum `∑_{m<n} (−1)^m (2m+1)!/x^{2m+2}` of 6.12.4. -/
noncomputable def gS (n : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, (-1) ^ m * ((2 * m + 1) ! : ℝ) / x ^ (2 * m + 2)

/-- `f`, `g` are real on `(0, ∞)`, and the remainders of 6.12.3, 6.12.4 have sign `(−1)ⁿ` and are
at most the first neglected terms (§6.12(ii)). -/
theorem fR_gR_spec {x : ℝ} (hx : 0 < x) (n : ℕ) :
    auxF x = (fR x : ℂ) ∧ auxG x = (gR x : ℂ) ∧
      0 < (-1) ^ n * (fR x - fS n x) ∧ |fR x - fS n x| ≤ (2 * n) ! / x ^ (2 * n + 1) ∧
      0 < (-1) ^ n * (gR x - gS n x) ∧ |gR x - gS n x| ≤ (2 * n + 1) ! / x ^ (2 * n + 2) := by
  obtain ⟨⟨r, hr, hs, hb⟩, ⟨r', hr', hs', hb'⟩⟩ := dlmf_6_12_remainder_real hx n
  rw [norm_fAsymp_succ_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at hb
  rw [norm_gAsymp_succ_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at hb'
  have hF : auxF x = ((fS n x + r : ℝ) : ℂ) := by
    rw [fAsymp_eq] at hr; simp only [fS]; push_cast; linear_combination hr
  have hG : auxG x = ((gS n x + r' : ℝ) : ℂ) := by
    rw [gAsymp_eq] at hr'; simp only [gS]; push_cast; linear_combination hr'
  have e1 : fR x = fS n x + r := by rw [fR, hF, ofReal_re]
  have e2 : gR x = gS n x + r' := by rw [gR, hG, ofReal_re]
  refine ⟨by rw [hF, e1], by rw [hG, e2], ?_, ?_, ?_, ?_⟩ <;>
    simp only [e1, e2, add_sub_cancel_left] <;> assumption

theorem fS_one (x : ℝ) : fS 1 x = 1 / x := by simp [fS]
theorem gS_one (x : ℝ) : gS 1 x = 1 / x ^ 2 := by simp [gS]
theorem fS_two (x : ℝ) : fS 2 x = 1 / x - 2 / x ^ 3 := by
  simp [fS, Finset.sum_range_succ, Nat.factorial]; ring
theorem fS_four (x : ℝ) : fS 4 x = 1 / x - 2 / x ^ 3 + 24 / x ^ 5 - 720 / x ^ 7 := by
  simp [fS, Finset.sum_range_succ, Nat.factorial]; ring
theorem gS_four (x : ℝ) : gS 4 x = 1 / x ^ 2 - 6 / x ^ 4 + 120 / x ^ 6 - 5040 / x ^ 8 := by
  simp [gS, Finset.sum_range_succ, Nat.factorial]; ring

/-- `Ci(x) = f(x) sin x − g(x) cos x` on `(0, ∞)` in real form (6.2.20). -/
theorem CiR_eq {x : ℝ} (hx : 0 < x) : CiR x = fR x * Real.sin x - gR x * Real.cos x := by
  have h := dlmf_6_2_20 (x : ℂ)
  rw [dlmf_6_3_F2_Ci_real hx, (fR_gR_spec hx 0).1, (fR_gR_spec hx 0).2.1, ← ofReal_sin,
    ← ofReal_cos] at h
  exact_mod_cast h

/-- `Si(x) = π/2 − f(x) cos x − g(x) sin x` on `(0, ∞)` in real form (6.2.19). -/
theorem SiR_eq {x : ℝ} (hx : 0 < x) : SiR x = π / 2 - fR x * Real.cos x - gR x * Real.sin x := by
  have h := dlmf_6_2_19 (x : ℂ)
  rw [dlmf_6_3_F2_Si_real, (fR_gR_spec hx 0).1, (fR_gR_spec hx 0).2.1, ← ofReal_sin,
    ← ofReal_cos] at h
  exact_mod_cast h

theorem neg_one_pow_sq_real (k : ℕ) : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by
  rw [← mul_pow]; norm_num

/-- Near `α = kπ`: `Ci(x) = (−1)^k (f(x) sin(x − α) − g(x) cos(x − α))`. -/
theorem CiR_eq_psi {x : ℝ} (hx : 0 < x) (k : ℕ) :
    CiR x = (-1) ^ k * (fR x * Real.sin (x - k * π) - gR x * Real.cos (x - k * π)) := by
  have hs : Real.sin x = (-1) ^ k * Real.sin (x - k * π) := by
    rw [← Real.sin_add_nat_mul_pi, sub_add_cancel]
  have hc : Real.cos x = (-1) ^ k * Real.cos (x - k * π) := by
    rw [← Real.cos_add_nat_mul_pi, sub_add_cancel]
  rw [CiR_eq hx, hs, hc]; ring

/-- Near `α = (k + 1/2)π`: `si(x) = (−1)^k (f(x) sin(x − α) − g(x) cos(x − α))`. -/
theorem siR_eq_psi {x : ℝ} (hx : 0 < x) (k : ℕ) :
    SiR x - π / 2 = (-1) ^ k * (fR x * Real.sin (x - (k + 1 / 2) * π) -
      gR x * Real.cos (x - (k + 1 / 2) * π)) := by
  set ε := x - (k + 1 / 2) * π
  have hx' : x = ε + π / 2 + k * π := by simp only [ε]; ring
  have hs : Real.sin x = (-1) ^ k * Real.cos ε := by
    conv_lhs => rw [hx']
    rw [Real.sin_add_nat_mul_pi, Real.sin_add_pi_div_two]
  have hc : Real.cos x = -((-1) ^ k * Real.sin ε) := by
    conv_lhs => rw [hx']
    rw [Real.cos_add_nat_mul_pi, Real.cos_add_pi_div_two]; ring
  rw [SiR_eq hx, hs, hc]; ring

/-! ### Taylor bounds for `sin`, `cos` -/

theorem sum_exp_I_nine (x : ℝ) :
    ∑ m ∈ Finset.range 9, ((x : ℂ) * I) ^ m / (m.factorial : ℂ) =
      ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 : ℝ) : ℂ) +
        ((x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 : ℝ) : ℂ) * I := by
  have h3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  have h4 : I ^ 4 = 1 := I_pow_four
  have h5 : I ^ 5 = I := by rw [pow_succ, h4, one_mul]
  have h6 : I ^ 6 = -1 := by rw [pow_succ, h5, I_mul_I]
  have h7 : I ^ 7 = -I := by rw [pow_succ, h6]; ring
  have h8 : I ^ 8 = 1 := by rw [pow_succ, h7, neg_mul, I_mul_I, neg_neg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_pow, I_sq, h3, h4, h5, h6, h7, h8,
    Nat.factorial]
  push_cast
  ring

theorem sum_exp_I_eight (x : ℝ) :
    ∑ m ∈ Finset.range 8, ((x : ℂ) * I) ^ m / (m.factorial : ℂ) =
      ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 : ℝ) : ℂ) +
        ((x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 : ℝ) : ℂ) * I := by
  have h3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  have h4 : I ^ 4 = 1 := I_pow_four
  have h5 : I ^ 5 = I := by rw [pow_succ, h4, one_mul]
  have h6 : I ^ 6 = -1 := by rw [pow_succ, h5, I_mul_I]
  have h7 : I ^ 7 = -I := by rw [pow_succ, h6]; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_pow, I_sq, h3, h4, h5, h6, h7,
    Nat.factorial]
  push_cast
  ring

/-- `|sin x − (x − x³/3! + x⁵/5! − x⁷/7!)| ≤ |x|⁹` for `|x| ≤ 1`. -/
theorem sin_taylor_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)| ≤ |x| ^ 9 := by
  have h := Complex.exp_bound (x := (x : ℂ) * I) (by rw [norm_ofReal_mul_I]; exact hx)
    (n := 9) (by norm_num)
  rw [sum_exp_I_nine, norm_ofReal_mul_I] at h
  have e : Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) =
      (cexp (x * I) - (((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 : ℝ) : ℂ) +
        ((x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 : ℝ) : ℂ) * I)).im := by
    rw [sub_im, exp_ofReal_mul_I_im, add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]
  rw [e]
  refine (abs_im_le_norm _).trans (h.trans ?_)
  have : (0 : ℝ) ≤ |x| ^ 9 := by positivity
  norm_num [Nat.factorial]
  nlinarith

/-- `|cos x − (1 − x²/2! + x⁴/4! − x⁶/6!)| ≤ |x|⁸` for `|x| ≤ 1`. -/
theorem cos_taylor_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)| ≤ |x| ^ 8 := by
  have h := Complex.exp_bound (x := (x : ℂ) * I) (by rw [norm_ofReal_mul_I]; exact hx)
    (n := 8) (by norm_num)
  rw [sum_exp_I_eight, norm_ofReal_mul_I] at h
  have e : Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) =
      (cexp (x * I) - (((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 : ℝ) : ℂ) +
        ((x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 : ℝ) : ℂ) * I)).re := by
    rw [sub_re, exp_ofReal_mul_I_re, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  rw [e]
  refine (abs_re_le_norm _).trans (h.trans ?_)
  have : (0 : ℝ) ≤ |x| ^ 8 := by positivity
  norm_num [Nat.factorial]
  nlinarith

/-! ### 6.13.2 -/

/-- The expansion `α + 1/α − 16/(3α³) + 1673/(15α⁵) − 507746/(105α⁷)` of 6.13.2. -/
noncomputable def zeroAsymp (α : ℝ) : ℝ :=
  α + 1 / α - 16 / (3 * α ^ 3) + 1673 / (15 * α ^ 5) - 507746 / (105 * α ^ 7)

theorem zeroAsymp_eq {α : ℝ} (hα : α ≠ 0) : zeroAsymp α = α + zeroDelta α⁻¹ := by
  rw [zeroAsymp, zeroDelta]; field_simp; ring

theorem zeroDelta_bounds {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) :
    0 < zeroDelta t ∧ zeroDelta t ≤ t := by
  have e : zeroDelta t = t * (1 - 16 / 3 * t ^ 2 + 1673 / 15 * (t ^ 2) ^ 2 -
      507746 / 105 * (t ^ 2) ^ 3) := by rw [zeroDelta]; ring
  have hu0 : 0 < t ^ 2 := by positivity
  have hu1 : t ^ 2 ≤ 1 / 10000 := by nlinarith
  have h1 : 0 < 1 - 16 / 3 * t ^ 2 + 1673 / 15 * (t ^ 2) ^ 2 - 507746 / 105 * (t ^ 2) ^ 3 := by
    nlinarith [mul_pos hu0 hu0, pow_pos hu0 3, pow_le_pow_left₀ hu0.le hu1 3]
  have h2 : 1 - 16 / 3 * t ^ 2 + 1673 / 15 * (t ^ 2) ^ 2 - 507746 / 105 * (t ^ 2) ^ 3 ≤ 1 := by
    nlinarith [mul_pos hu0 hu0, pow_pos hu0 3]
  rw [e]
  exact ⟨mul_pos ht0 h1, by nlinarith⟩

/-- The explicit residual constant `K = 31627 + 8! + 9! + 4 = 434831`. -/
noncomputable def zeroK : ℝ := 31627 + 8 ! + 9 ! + 4

theorem zeroK_eq : zeroK = 434831 := by norm_num [zeroK, Nat.factorial]

/-- The residual of the zero equation at the expansion: `|f(Q) sin δ − g(Q) cos δ| ≤ K/α^{10}`,
`Q = α + δ`, `δ = zeroDelta(1/α)`. -/
theorem zero_residual_bound_explicit {α : ℝ} (hα : 100 ≤ α) :
    |fR (α + zeroDelta α⁻¹) * Real.sin (zeroDelta α⁻¹) -
        gR (α + zeroDelta α⁻¹) * Real.cos (zeroDelta α⁻¹)| ≤ zeroK / α ^ 10 := by
  rw [zeroK]
  set B : ℝ := 31627 with hBdef
  have hα0 : 0 < α := by linarith
  set t := α⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 hα0
  have ht1 : t ≤ 1 / 100 := by
    rw [ht]; exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have htα : t * α = 1 := inv_mul_cancel₀ hα0.ne'
  set δ := zeroDelta t with hδ
  obtain ⟨hδ0, hδt⟩ := zeroDelta_bounds ht0 ht1
  set Q := α + δ with hQ
  have hQ0 : 0 < Q := by linarith
  set E := 1 + t * δ with hE
  have hE1 : 1 ≤ E := by have := mul_pos ht0 hδ0; linarith
  have htQ : t * Q = E := by rw [hQ, hE, mul_add, htα]
  have hQE : Q = E / t := by rw [← htQ]; field_simp
  have hinvQ : 1 / Q ≤ t := by
    rw [ht, one_div]; exact inv_anti₀ hα0 (by linarith)
  have hpowQ : ∀ n : ℕ, 1 / Q ^ n ≤ t ^ n := fun n => by
    rw [← one_div_pow]; exact pow_le_pow_left₀ (by positivity) hinvQ n
  -- the expansions of `f`, `g` at `Q`
  obtain ⟨-, -, -, hF4, -, hG4⟩ := fR_gR_spec hQ0 4
  obtain ⟨-, -, hF1, -, hG1, -⟩ := fR_gR_spec hQ0 1
  obtain ⟨-, -, hF0, -, hG0, -⟩ := fR_gR_spec hQ0 0
  simp only [pow_zero, one_mul, pow_one, fS_one, gS_one, show fS 0 Q = 0 by simp [fS],
    show gS 0 Q = 0 by simp [gS], sub_zero] at hF0 hG0 hF1 hG1
  norm_num at hF4 hG4
  have hF4' : |fR Q - fS 4 Q| ≤ 40320 * t ^ 9 := by
    refine hF4.trans ?_
    rw [div_eq_mul_one_div]; gcongr; exact hpowQ 9
  have hG4' : |gR Q - gS 4 Q| ≤ 362880 * t ^ 10 := by
    refine hG4.trans ?_
    rw [div_eq_mul_one_div]; gcongr; exact hpowQ 10
  have hfQ : fR Q ≤ t := by have := hpowQ 1; rw [pow_one, pow_one] at this; linarith
  have hgQ : gR Q ≤ t ^ 2 := by linarith [hpowQ 2]
  -- the Taylor expansions of `sin δ`, `cos δ`
  have hδ1 : |δ| ≤ 1 := by rw [abs_of_pos hδ0]; linarith
  have hS := sin_taylor_le hδ1
  have hC := cos_taylor_le hδ1
  rw [abs_of_pos hδ0] at hS hC
  have hδ9 : δ ^ 9 ≤ t ^ 9 := pow_le_pow_left₀ hδ0.le hδt 9
  have hδ8 : δ ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ hδ0.le hδt 8
  have hsin0 : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ0.le (by
    linarith [Real.pi_gt_three])
  have hsin1 : Real.sin δ ≤ t := (Real.sin_le hδ0.le).trans hδt
  have hcos : |Real.cos δ| ≤ 1 := Real.abs_cos_le_one δ
  -- the main part, by the polynomial identity
  set S := δ - δ ^ 3 / 6 + δ ^ 5 / 120 - δ ^ 7 / 5040
  set C := 1 - δ ^ 2 / 2 + δ ^ 4 / 24 - δ ^ 6 / 720
  have hE8 : E ^ 8 ≠ 0 := pow_ne_zero _ (by linarith)
  have hf8 :
      fS 4 Q * E ^ 8 = t * E ^ 7 - 2 * t ^ 3 * E ^ 5 + 24 * t ^ 5 * E ^ 3 - 720 * t ^ 7 * E := by
    rw [fS_four, hQE]; field_simp
  have hg8 : gS 4 Q * E ^ 8 =
      t ^ 2 * E ^ 6 - 6 * t ^ 4 * E ^ 4 + 120 * t ^ 6 * E ^ 2 - 5040 * t ^ 8 := by
    rw [gS_four, hQE]; field_simp
  have hid := zero_poly_identity t
  simp only at hid
  rw [← hδ, ← hE] at hid
  have hmain : fS 4 Q * S - gS 4 Q * C = t ^ 10 * zeroPolyR t / E ^ 8 := by
    rw [eq_div_iff hE8]
    calc (fS 4 Q * S - gS 4 Q * C) * E ^ 8 = (fS 4 Q * E ^ 8) * S - (gS 4 Q * E ^ 8) * C := by
          ring
      _ = _ := by rw [hf8, hg8]; exact hid
  have hR : |zeroPolyR t| ≤ B := abs_zeroPolyR_le ht0.le ht1
  have hmainb : |fS 4 Q * S - gS 4 Q * C| ≤ B * t ^ 10 := by
    rw [hmain, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t ^ 10),
      abs_of_pos (by positivity : (0 : ℝ) < E ^ 8), div_le_iff₀ (by positivity)]
    have h8 : 1 ≤ E ^ 8 := one_le_pow₀ hE1
    have hB0 : 0 ≤ B := (abs_nonneg _).trans hR
    calc t ^ 10 * |zeroPolyR t| ≤ t ^ 10 * B := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = B * t ^ 10 * 1 := by ring
      _ ≤ B * t ^ 10 * E ^ 8 := mul_le_mul_of_nonneg_left h8 (by positivity)
  -- the error terms
  have ht8 : 362880 * t ^ 8 ≤ 1 := by
    have h := pow_le_pow_left₀ ht0.le ht1 8
    have : 362880 * (1 / 100 : ℝ) ^ 8 ≤ 1 := by norm_num
    linarith [mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 362880)]
  have hfS : |fS 4 Q| ≤ 2 * t := by
    have h1 : |fS 4 Q| ≤ |fR Q| + |fR Q - fS 4 Q| := by
      have := abs_sub (fR Q) (fR Q - fS 4 Q); simp only [sub_sub_cancel] at this; exact this
    rw [abs_of_pos hF0] at h1
    have : 40320 * t ^ 9 ≤ t := by
      have h8 : 40320 * t ^ 8 ≤ 1 := by linarith [pow_pos ht0 8]
      calc 40320 * t ^ 9 = t * (40320 * t ^ 8) := by ring
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left h8 ht0.le
        _ = t := mul_one t
    linarith
  have hgS : |gS 4 Q| ≤ 2 * t ^ 2 := by
    have h1 : |gS 4 Q| ≤ |gR Q| + |gR Q - gS 4 Q| := by
      have := abs_sub (gR Q) (gR Q - gS 4 Q); simp only [sub_sub_cancel] at this; exact this
    rw [abs_of_pos hG0] at h1
    have : 362880 * t ^ 10 ≤ t ^ 2 := by
      calc 362880 * t ^ 10 = t ^ 2 * (362880 * t ^ 8) := by ring
        _ ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left ht8 (by positivity)
        _ = t ^ 2 := mul_one _
    linarith
  have e : fR Q * Real.sin δ - gR Q * Real.cos δ = (fS 4 Q * S - gS 4 Q * C) +
      (fR Q - fS 4 Q) * Real.sin δ + fS 4 Q * (Real.sin δ - S) -
      (gR Q - gS 4 Q) * Real.cos δ - gS 4 Q * (Real.cos δ - C) := by ring
  have b1 : |(fR Q - fS 4 Q) * Real.sin δ| ≤ 40320 * t ^ 10 := by
    rw [abs_mul, abs_of_nonneg hsin0]
    calc _ ≤ 40320 * t ^ 9 * t := mul_le_mul hF4' hsin1 hsin0 (by positivity)
      _ = _ := by ring
  have b2 : |fS 4 Q * (Real.sin δ - S)| ≤ 2 * t ^ 10 := by
    rw [abs_mul]
    calc _ ≤ 2 * t * t ^ 9 := mul_le_mul hfS (hS.trans hδ9) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have b3 : |(gR Q - gS 4 Q) * Real.cos δ| ≤ 362880 * t ^ 10 := by
    rw [abs_mul]
    calc _ ≤ 362880 * t ^ 10 * 1 := mul_le_mul hG4' hcos (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have b4 : |gS 4 Q * (Real.cos δ - C)| ≤ 2 * t ^ 10 := by
    rw [abs_mul]
    calc _ ≤ 2 * t ^ 2 * t ^ 8 := mul_le_mul hgS (hC.trans hδ8) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have htα10 : t ^ 10 = 1 / α ^ 10 := by rw [ht, inv_pow, one_div]
  rw [e, div_eq_mul_one_div, ← htα10]
  have key : |(fS 4 Q * S - gS 4 Q * C) + (fR Q - fS 4 Q) * Real.sin δ +
      fS 4 Q * (Real.sin δ - S) - (gR Q - gS 4 Q) * Real.cos δ - gS 4 Q * (Real.cos δ - C)| ≤
      B * t ^ 10 + 40320 * t ^ 10 + 2 * t ^ 10 + 362880 * t ^ 10 + 2 * t ^ 10 := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self (fS 4 Q * S - gS 4 Q * C),
      neg_abs_le (fS 4 Q * S - gS 4 Q * C), le_abs_self ((fR Q - fS 4 Q) * Real.sin δ),
      neg_abs_le ((fR Q - fS 4 Q) * Real.sin δ), le_abs_self (fS 4 Q * (Real.sin δ - S)),
      neg_abs_le (fS 4 Q * (Real.sin δ - S)), le_abs_self ((gR Q - gS 4 Q) * Real.cos δ),
      neg_abs_le ((gR Q - gS 4 Q) * Real.cos δ), le_abs_self (gS 4 Q * (Real.cos δ - C)),
      neg_abs_le (gS 4 Q * (Real.cos δ - C))]
  refine key.trans (le_of_eq ?_)
  norm_num [Nat.factorial]
  ring

theorem zero_residual_bound :
    ∃ K : ℝ, ∀ α : ℝ, 100 ≤ α →
      |fR (α + zeroDelta α⁻¹) * Real.sin (zeroDelta α⁻¹) -
        gR (α + zeroDelta α⁻¹) * Real.cos (zeroDelta α⁻¹)| ≤ K / α ^ 10 :=
  ⟨zeroK, fun _ hα => zero_residual_bound_explicit hα⟩

/-- A zero `ζ` of `f(x) sin(x − α) − g(x) cos(x − α)` within `π/2` of `α ≥ 100` lies in
`(α, α + 4/α]`. -/
theorem zero_location {α : ℝ} (hα : 100 ≤ α) {ζ : ℝ} (hζ : ζ ∈ Ioo (α - π / 2) (α + π / 2))
    (h0 : fR ζ * Real.sin (ζ - α) - gR ζ * Real.cos (ζ - α) = 0) :
    α < ζ ∧ ζ ≤ α + 4 / α := by
  have hπ4 := Real.pi_lt_four
  have hπ0 := Real.pi_pos
  have hζ0 : 0 < ζ := by linarith [hζ.1]
  set ε := ζ - α with hε
  have hε1 : -(π / 2) < ε := by linarith [hζ.1]
  have hε2 : ε < π / 2 := by linarith [hζ.2]
  obtain ⟨-, -, hF0, -, hG0, -⟩ := fR_gR_spec hζ0 0
  obtain ⟨-, -, -, -, hG1, -⟩ := fR_gR_spec hζ0 1
  obtain ⟨-, -, hF2, -, -, -⟩ := fR_gR_spec hζ0 2
  simp only [pow_zero, one_mul, pow_one, show fS 0 ζ = 0 by simp [fS],
    show gS 0 ζ = 0 by simp [gS], sub_zero, gS_one, fS_two] at hF0 hG0 hG1 hF2
  norm_num at hF2
  have hcos : 0 < Real.cos ε := Real.cos_pos_of_mem_Ioo ⟨hε1, hε2⟩
  have hfs : fR ζ * Real.sin ε = gR ζ * Real.cos ε := by linarith
  have hsin : 0 < Real.sin ε := by
    have : 0 < fR ζ * Real.sin ε := by rw [hfs]; positivity
    exact pos_of_mul_pos_right this hF0.le
  have hεpos : 0 < ε := by
    by_contra h
    push Not at h
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith)
    linarith
  -- `sin ε < 2/ζ`
  set u := ζ⁻¹ with hu
  have hu0 : 0 < u := inv_pos.2 hζ0
  have hu1 : u ≤ 1 / 90 := by
    rw [hu]; exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith [hζ.1])
  have hfu : u / 2 ≤ fR ζ := by
    have e : 2 / ζ ^ 3 = 2 * u ^ 3 := by rw [hu]; field_simp
    have : u / 2 ≤ u - 2 * u ^ 3 := by nlinarith [mul_pos hu0 hu0]
    linarith
  have hgu : gR ζ < u ^ 2 := by
    have e : 1 / ζ ^ 2 = u ^ 2 := by rw [hu]; field_simp
    linarith
  have hsinb : Real.sin ε < 2 * u := by
    have h1 : Real.sin ε * (u / 2) ≤ Real.sin ε * fR ζ := mul_le_mul_of_nonneg_left hfu hsin.le
    have h2 : gR ζ * Real.cos ε ≤ gR ζ := by
      have := Real.cos_le_one ε
      nlinarith
    have h3 : Real.sin ε * (u / 2) < u ^ 2 := by linarith
    nlinarith
  -- Jordan's inequality
  have hJ := Real.mul_le_sin hεpos.le hε2.le
  have hεb : ε < 4 * u := by
    have : ε ≤ π / 2 * Real.sin ε := by
      rw [div_mul_eq_mul_div, le_div_iff₀ two_pos]
      have := (div_mul_eq_mul_div 2 π ε) ▸ hJ
      rw [div_le_iff₀ hπ0] at this
      linarith
    nlinarith
  have hut : u < α⁻¹ := by rw [hu]; exact inv_strictAnti₀ (by linarith) (by linarith)
  refine ⟨by linarith, ?_⟩
  rw [div_eq_mul_inv]
  linarith

/-- The core of 6.13.2: a zero `ζ` of `f(x) sin(x − α) − g(x) cos(x − α)` within `π/2` of `α`
satisfies `|ζ − zeroAsymp α| ≤ C/α⁹` for `α ≥ 100` (MVT on `[α, α + 4/α]`, where the derivative
`cos(x − α)/x` is at least `1/(4α)`). -/
theorem zero_asymp_core_explicit :
    ∀ α : ℝ, 100 ≤ α → ∀ Ψ : ℝ → ℝ,
      (∀ x, 0 < x → Ψ x = fR x * Real.sin (x - α) - gR x * Real.cos (x - α)) →
      (∀ x, 0 < x → HasDerivAt Ψ (Real.cos (x - α) / x) x) →
      ∀ ζ ∈ Ioo (α - π / 2) (α + π / 2), Ψ ζ = 0 → |ζ - zeroAsymp α| ≤ 4 * zeroK / α ^ 9 := by
  set K := zeroK
  have hK : ∀ α : ℝ, 100 ≤ α → |fR (α + zeroDelta α⁻¹) * Real.sin (zeroDelta α⁻¹) -
      gR (α + zeroDelta α⁻¹) * Real.cos (zeroDelta α⁻¹)| ≤ K / α ^ 10 :=
    fun α hα => zero_residual_bound_explicit hα
  intro α hα Ψ hΨ hd ζ hζ h0
  have hα0 : 0 < α := by linarith
  have hπ4 := Real.pi_lt_four
  have hζ0 : 0 < ζ := by linarith [hζ.1, Real.pi_pos]
  obtain ⟨hζ1, hζ2⟩ := zero_location hα hζ (by rw [← hΨ ζ hζ0]; exact h0)
  set t := α⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 hα0
  have ht1 : t ≤ 1 / 100 := by
    rw [ht]; exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  obtain ⟨hδ0, hδt⟩ := zeroDelta_bounds ht0 ht1
  set Q := α + zeroDelta t with hQ
  rw [zeroAsymp_eq hα0.ne', ← ht, ← hQ]
  have hres := hK α hα
  rw [← ht, ← hQ] at hres
  have hΨQ : |Ψ Q| ≤ K / α ^ 10 := by
    rw [hΨ Q (by linarith), show Q - α = zeroDelta t by rw [hQ]; ring]; exact hres
  have h4 : 4 / α = 4 * t := by rw [ht, div_eq_mul_inv]
  rw [h4] at hζ2
  -- the derivative is at least `t/4` on `[α, α + 4t]`
  set D := Icc α (α + 4 * t)
  have hDpos : ∀ x ∈ D, 0 < x := fun x hx => by linarith [hx.1]
  have hcont : ContinuousOn Ψ D := fun x hx => (hd x (hDpos x hx)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ Ψ (interior D) := fun x hx =>
    (hd x (hDpos x (interior_subset hx))).differentiableAt.differentiableWithinAt
  have hder : ∀ x ∈ interior D, t / 4 ≤ deriv Ψ x := by
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [(hd x hx0).deriv]
    have hc : 1 / 2 ≤ Real.cos (x - α) := by
      have := Real.one_sub_sq_div_two_le_cos (x := x - α)
      have hxa : (x - α) ^ 2 ≤ (4 * t) ^ 2 := by
        have : 0 ≤ x - α := by linarith [hx.1]
        exact pow_le_pow_left₀ this (by linarith [hx.2]) 2
      nlinarith
    have hx2 : x ≤ 2 * α := by
      have : 4 * t ≤ α := by nlinarith
      linarith [hx.2]
    rw [le_div_iff₀ hx0]
    calc t / 4 * x ≤ t / 4 * (2 * α) := by gcongr
      _ = 1 / 2 := by rw [ht]; field_simp; ring
      _ ≤ _ := hc
  have hmvt := (convex_Icc α (α + 4 * t)).mul_sub_le_image_sub_of_le_deriv hcont hdiff hder
  have hζD : ζ ∈ D := ⟨hζ1.le, hζ2⟩
  have hQD : Q ∈ D := ⟨by linarith, by linarith⟩
  have key : t / 4 * |ζ - Q| ≤ K / α ^ 10 := by
    rcases le_total ζ Q with h | h
    · have := hmvt ζ hζD Q hQD h
      rw [h0, sub_zero] at this
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith [le_abs_self (Ψ Q)]
    · have := hmvt Q hQD ζ hζD h
      rw [h0, zero_sub] at this
      rw [abs_of_nonneg (by linarith)]
      linarith [neg_abs_le (Ψ Q)]
  have e : K / α ^ 10 = t / 4 * (4 * K / α ^ 9) := by
    rw [ht]; field_simp
  rw [e] at key
  exact le_of_mul_le_mul_left key (by positivity)

theorem zero_asymp_core :
    ∃ C : ℝ, ∀ α : ℝ, 100 ≤ α → ∀ Ψ : ℝ → ℝ,
      (∀ x, 0 < x → Ψ x = fR x * Real.sin (x - α) - gR x * Real.cos (x - α)) →
      (∀ x, 0 < x → HasDerivAt Ψ (Real.cos (x - α) / x) x) →
      ∀ ζ ∈ Ioo (α - π / 2) (α + π / 2), Ψ ζ = 0 → |ζ - zeroAsymp α| ≤ C / α ^ 9 :=
  ⟨4 * zeroK, zero_asymp_core_explicit⟩

/-- **DLMF 6.13.2** with an explicit constant: `c_k, s_k = α + 1/α − 16/(3α³) + 1673/(15α⁵)
− 507746/(105α⁷) + R`, `|R| ≤ 4·434831/α⁹` for `k ≥ 32`, with `α = kπ` for `c_k` and
`α = (k + 1/2)π` for `s_k`. -/
theorem dlmf_6_13_2_explicit {k : ℕ} (hk : 32 ≤ k) :
      |ciZero k - zeroAsymp (k * π)| ≤ 4 * zeroK / (k * π) ^ 9 ∧
        |siZero k - zeroAsymp ((k + 1 / 2) * π)| ≤ 4 * zeroK / ((k + 1 / 2) * π) ^ 9 := by
  have hC := zero_asymp_core_explicit
  refine ⟨?_, ?_⟩
  · have hk' : (32 : ℝ) ≤ k := by exact_mod_cast hk
    have hα : 100 ≤ (k : ℝ) * π := by nlinarith [Real.pi_gt_d2]
    refine hC _ hα (fun y => (-1) ^ k * CiR y) (fun y hy => ?_) (fun x hx => ?_) _
      (ciZero_mem (by omega)) ?_
    · rw [CiR_eq_psi hy k, ← mul_assoc, neg_one_pow_sq_real, one_mul]
    · refine ((hasDerivAt_CiR hx).const_mul ((-1 : ℝ) ^ k)).congr_deriv ?_
      have hc : Real.cos x = (-1) ^ k * Real.cos (x - k * π) := by
        rw [← Real.cos_add_nat_mul_pi, sub_add_cancel]
      rw [hc, ← mul_div_assoc, ← mul_assoc, neg_one_pow_sq_real, one_mul]
    · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
      simp only [(ciZero_succ_spec n).2, mul_zero]
  · have hk' : (32 : ℝ) ≤ k := by exact_mod_cast hk
    have hα : 100 ≤ ((k : ℝ) + 1 / 2) * π := by nlinarith [Real.pi_gt_d2]
    refine hC _ hα (fun y => (-1) ^ k * (SiR y - π / 2)) (fun y hy => ?_) (fun x hx => ?_) _
      ?_ ?_
    · rw [siR_eq_psi hy k, ← mul_assoc, neg_one_pow_sq_real, one_mul]
    · refine (((hasDerivAt_SiR x).sub_const (π / 2)).const_mul ((-1 : ℝ) ^ k)).congr_deriv ?_
      have hx' : x = (x - (k + 1 / 2) * π) + π / 2 + k * π := by ring
      have hs : Real.sin x = (-1) ^ k * Real.cos (x - (k + 1 / 2) * π) := by
        conv_lhs => rw [hx']
        rw [Real.sin_add_nat_mul_pi, Real.sin_add_pi_div_two]
      rw [sincR_of_ne hx.ne', hs, ← mul_div_assoc, ← mul_assoc, neg_one_pow_sq_real, one_mul]
    · obtain ⟨⟨h1, h2⟩, -⟩ := siZero_spec k
      constructor <;> linarith
    · simp only [(siZero_spec k).2, sub_self, mul_zero]

end Azurite.DLMF

namespace Azurite.DLMF

/-- **DLMF 6.13.2** (existential constant form; the constant is `4·434831`,
`dlmf_6_13_2_explicit`). -/
theorem dlmf_6_13_2 :
    ∃ C : ℝ, ∀ k : ℕ, 32 ≤ k →
      |ciZero k - zeroAsymp (k * π)| ≤ C / (k * π) ^ 9 ∧
        |siZero k - zeroAsymp ((k + 1 / 2) * π)| ≤ C / ((k + 1 / 2) * π) ^ 9 :=
  ⟨4 * zeroK, fun _ hk => dlmf_6_13_2_explicit hk⟩

end Azurite.DLMF
