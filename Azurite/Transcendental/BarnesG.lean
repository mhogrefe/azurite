/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.GlaisherKinkelin

/-!
# The Barnes `G`-function on the real line

For the computation of `G(x)` (`DLMF.barnesG`, DLMF §5.17) at a real `x`:

* `barnesGR x`, the real function; `barnesG_ofReal` (`G` is real on the reals),
  `barnesGR_pos` (`G(x) > 0` for `x > 0`), `barnesGR_neg_nat` (`G(−m) = 0`),
  `barnesGR_add_one` (`G(x + 1) = Γ(x) G(x)`), `barnesGR_natCast` (`G(n) = ∏_{k ≤ n−2} k!`);
* `barnesGR_eq_shift`: `G(x) = G(x + N) ∏_{j<N} (x + j)^(j+1) / Γ(x + N)^N`, off the zeros;
* `log_barnesGR_add_one`: `ln G(y + 1) = y²/4 + y ln Γ(y + 1) − (y(y + 1)/2 + 1/12) ln y +
  R(y)` for `y > 0`, `R` the function `glaisherR` of DLMF 5.17.5;
* the expansion of `R(y)` **with its remainder at a real `y > 0`**: `barnesRho y j` is
  `R(y) + C − ∑_{k ≤ j} t_k(y)`, `t_k(y) = B_{2k+2} / (2k (2k + 1) (2k + 2) y^{2k})`;
  `barnesRho_pred_eq`: `ρ_{j−1}(y) = ∫₀^∞ (B_{2j+2} − B̃_{2j+2}(t)) / (y + t)^{2j+1} dt /
  ((2j + 1)(2j + 2))`, of one sign (`barnesRho_sign`), so that the terms envelop the
  remainder (`barnesRho_enveloping`).
-/

open Complex Filter Topology Set Finset MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

/-- **The Barnes `G`-function at a real argument.** -/
noncomputable def barnesGR (x : ℝ) : ℝ := (barnesG x).re

/-- `G(y + 1) = exp (Ln G(y + 1))` with a real logarithm, `y > −1`. -/
theorem barnesG_add_one_ofReal {y : ℝ} (hy : -1 < y) :
    ∃ L : ℝ, barnesLog y = (L : ℂ) ∧ barnesG ((y : ℂ) + 1) = (Real.exp L : ℂ) := by
  have hs : (y : ℂ) + 1 ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp; linarith
  refine ⟨_, barnesLog_ofReal hy, ?_⟩
  rw [barnesG_add_one_eq_exp hs, barnesLog_ofReal hy, ofReal_exp]

/-- `G(−m) = 0`. -/
theorem barnesG_neg_nat (m : ℕ) : barnesG (-(m : ℂ)) = 0 := by
  rw [barnesG]
  refine mul_eq_zero_of_right _ (tprod_of_exists_eq_zero ⟨m, ?_⟩)
  have h : (1 : ℂ) + (-(m : ℂ) - 1) / ((m : ℂ) + 1) = 0 := by
    have hm : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    field_simp
    ring
  rw [barnesFactor, h, zero_pow (Nat.succ_ne_zero m), zero_mul]

/-- `G` is real on the reals. -/
theorem barnesG_im_eq_zero : ∀ (N : ℕ) (x : ℝ), 0 < x + N → (barnesG (x : ℂ)).im = 0
  | 0, x, hx => by
    obtain ⟨L, -, h⟩ := barnesG_add_one_ofReal (y := x - 1) (by simpa using hx)
    rw [show ((x - 1 : ℝ) : ℂ) + 1 = (x : ℂ) by push_cast; ring] at h
    rw [h, ofReal_im]
  | N + 1, x, hx => by
    have ih := barnesG_im_eq_zero N (x + 1) (by push_cast at hx ⊢; linarith)
    by_cases hp : (x : ℂ) ∈ gammaPoles
    · obtain ⟨m, hm⟩ := hp
      rw [← hm, barnesG_neg_nat, zero_im]
    · have h := dlmf_5_17_1.1 x hp
      have hG : Complex.Gamma x ≠ 0 := Complex.Gamma_ne_zero (not_mem_gammaPoles.mp hp)
      have e : barnesG (x : ℂ) = barnesG ((x : ℂ) + 1) / Complex.Gamma x := by
        rw [h]; field_simp
      rw [e, Complex.Gamma_ofReal, show ((x : ℂ) + 1) = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
        div_ofReal_im, ih, zero_div]

theorem barnesG_ofReal (x : ℝ) : barnesG (x : ℂ) = (barnesGR x : ℂ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-x)
  exact Complex.ext rfl (by rw [barnesG_im_eq_zero N x (by linarith), ofReal_im])

/-- `G(y + 1) = exp L` with `L = Ln G(y + 1)` real, `y > −1`. -/
theorem barnesGR_add_one_eq_exp {y : ℝ} (hy : -1 < y) :
    ∃ L : ℝ, barnesLog y = (L : ℂ) ∧ barnesGR (y + 1) = Real.exp L := by
  obtain ⟨L, h1, h2⟩ := barnesG_add_one_ofReal hy
  refine ⟨L, h1, ?_⟩
  rw [show ((y : ℂ) + 1) = ((y + 1 : ℝ) : ℂ) by push_cast; ring, barnesG_ofReal] at h2
  exact_mod_cast h2

theorem barnesGR_pos {x : ℝ} (hx : 0 < x) : 0 < barnesGR x := by
  obtain ⟨L, -, h⟩ := barnesGR_add_one_eq_exp (y := x - 1) (by linarith)
  rw [sub_add_cancel] at h
  rw [h]
  exact Real.exp_pos L

theorem barnesGR_neg_nat (m : ℕ) : barnesGR (-(m : ℝ)) = 0 := by
  have := barnesG_neg_nat m
  rw [show (-(m : ℂ)) = ((-(m : ℝ) : ℝ) : ℂ) by push_cast; ring, barnesG_ofReal] at this
  exact_mod_cast this

/-- **DLMF 5.17.1 on the reals**: `G(x + 1) = Γ(x) G(x)`, `x ≠ 0, −1, −2, …`. -/
theorem barnesGR_add_one {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) :
    barnesGR (x + 1) = Real.Gamma x * barnesGR x := by
  have hp : (x : ℂ) ∉ gammaPoles := not_mem_gammaPoles.mpr fun m h => hx m (by exact_mod_cast h)
  have h := dlmf_5_17_1.1 x hp
  rw [show ((x : ℂ) + 1) = ((x + 1 : ℝ) : ℂ) by push_cast; ring, barnesG_ofReal, barnesG_ofReal,
    Complex.Gamma_ofReal] at h
  exact_mod_cast h

theorem barnesGR_one : barnesGR 1 = 1 := by
  have := dlmf_5_17_1.2
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp, barnesG_ofReal] at this
  exact_mod_cast this

/-- **DLMF 5.17.2 on the reals**: `G(n) = (n − 2)! ⋯ 1!`, `n ≥ 2`. -/
theorem barnesGR_natCast {n : ℕ} (hn : 2 ≤ n) :
    barnesGR n = ∏ k ∈ Icc 1 (n - 2), (k ! : ℝ) := by
  have := dlmf_5_17_2 hn
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp, barnesG_ofReal] at this
  exact_mod_cast this

/-- `∏_{k<N} Γ(x + k) · ∏_{j<N} (x + j)^(j+1) = Γ(x + N)^N`. -/
theorem prod_gamma_mul_prod_pow {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (N : ℕ) :
    (∏ k ∈ range N, Real.Gamma (x + k)) * ∏ j ∈ range N, (x + j) ^ (j + 1)
      = Real.Gamma (x + N) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hxN : x + N ≠ 0 := fun h => hx N (by linarith)
    rw [prod_range_succ, prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hxN,
      mul_pow, pow_succ (Real.Gamma (x + N)), ← ih]
    ring

/-- `G(x + N) = G(x) ∏_{k<N} Γ(x + k)`. -/
theorem barnesGR_add_nat {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (N : ℕ) :
    barnesGR (x + N) = barnesGR x * ∏ k ∈ range N, Real.Gamma (x + k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hxN : ∀ m : ℕ, x + N ≠ -m := fun m h => hx (m + N) (by push_cast; linarith)
    rw [Nat.cast_succ, ← add_assoc, barnesGR_add_one hxN, ih, prod_range_succ]
    ring

/-- **The shift**: `G(x) = G(x + N) ∏_{j<N} (x + j)^(j+1) / Γ(x + N)^N` off the zeros of
`G`. -/
theorem barnesGR_eq_shift {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (N : ℕ) :
    barnesGR x = barnesGR (x + N) * (∏ j ∈ range N, (x + j) ^ (j + 1))
      / Real.Gamma (x + N) ^ N := by
  have hG : Real.Gamma (x + N) ≠ 0 :=
    Real.Gamma_ne_zero fun m h => hx (m + N) (by push_cast; linarith)
  rw [eq_div_iff (pow_ne_zero _ hG), barnesGR_add_nat hx N, ← prod_gamma_mul_prod_pow hx N]
  ring

/-! ### The expansion of `ln G(y + 1)` at a real `y > 0` -/

/-- `R(y)` at a real `y > 0`: `ln G(y + 1) = y²/4 + y ln Γ(y + 1) − (y(y + 1)/2 + 1/12) ln y +
R(y)`. -/
theorem log_barnesGR_add_one {y : ℝ} (hy : 0 < y) :
    Real.log (barnesGR (y + 1)) = y ^ 2 / 4 + y * Real.log (Real.Gamma (y + 1))
      - (y * (y + 1) / 2 + 1 / 12) * Real.log y + (glaisherR y).re := by
  obtain ⟨L, hL, hG⟩ := barnesGR_add_one_eq_exp (y := y) (by linarith)
  have hlog : Complex.log (y : ℂ) = (Real.log y : ℂ) := (ofReal_log hy.le).symm
  have hR : glaisherR y = ((L - y ^ 2 / 4 - y * Real.log (Real.Gamma (y + 1))
      + (y * (y + 1) / 2 + 1 / 12) * Real.log y : ℝ) : ℂ) := by
    rw [glaisherR, hL, show ((y : ℂ) + 1) = ((y + 1 : ℝ) : ℂ) by push_cast; ring,
      lnGamma_ofReal (by linarith), hlog]
    push_cast
    ring
  rw [hG, Real.log_exp, hR, ofReal_re]
  ring

/-- `t_k(y) = B_{2k+2} / (2k (2k + 1) (2k + 2) y^{2k})`, the terms of the expansion of
`R(y) + C`. -/
noncomputable def barnesTerm (y : ℝ) (k : ℕ) : ℝ :=
  (bernoulli (2 * k + 2) : ℝ) / (2 * k * (2 * k + 1) * (2 * k + 2) * y ^ (2 * k))

/-- `τ_k(y) = |t_k(y)| = c_{k+1} / (2k (2k + 1) y^{2k})` on the coefficients of the series
of `ψ`. -/
noncomputable def barnesTau (y : ℝ) (k : ℕ) : ℝ :=
  psiCoeffT (k + 1) / (2 * k * (2 * k + 1) * y ^ (2 * k))

theorem barnesTau_pos {y : ℝ} (hy : 0 < y) {k : ℕ} (hk : 1 ≤ k) : 0 < barnesTau y k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  exact div_pos (psiCoeffT_pos (by omega)) (by positivity)

/-- `t_k = (−1)^k τ_k`. -/
theorem barnesTerm_eq_tau {y : ℝ} (hy : 0 < y) {k : ℕ} (hk : 1 ≤ k) :
    barnesTerm y k = (-1) ^ k * barnesTau y k := by
  have hy0 : y ≠ 0 := hy.ne'
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := bernoulli_div_eq_psiCoeffT (by omega : 1 ≤ k + 1)
  have hB : (bernoulli (2 * k + 2) : ℝ) = (-1) ^ k * psiCoeffT (k + 1) * (2 * k + 2) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring] at h
    push_cast at h
    rw [div_eq_iff (by positivity)] at h
    rw [h, pow_succ, pow_succ]
    ring
  rw [barnesTerm, barnesTau, hB]
  field_simp

theorem barnesTau_natCast (n k : ℕ) : barnesTau n k = glaisherTau n k := rfl

/-- `τ_k` decreases in `y`. -/
theorem barnesTau_anti {y y' : ℝ} (hy : 0 < y) (h : y ≤ y') (k : ℕ) :
    barnesTau y' k ≤ barnesTau y k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [barnesTau]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold barnesTau
  have hp : y ^ (2 * k) ≤ y' ^ (2 * k) := pow_le_pow_left₀ hy.le h _
  exact div_le_div_of_nonneg_left (psiCoeffT_pos (by omega)).le (by positivity)
    (mul_le_mul_of_nonneg_left hp (by positivity))

/-- The error after `j` terms: `ρ_j(y) = R(y) + C − ∑_{k=1}^{j} t_k(y)`. -/
noncomputable def barnesRho (y : ℝ) (j : ℕ) : ℝ :=
  (glaisherR y).re + glaisherC - ∑ k ∈ Icc 1 j, barnesTerm y k

theorem barnesRho_succ (y : ℝ) (j : ℕ) :
    barnesRho y j = barnesRho y (j + 1) + barnesTerm y (j + 1) := by
  rw [barnesRho, barnesRho, sum_Icc_succ_top (by omega)]
  ring

/-- The integrand of the remainder is integrable. -/
theorem integrableOn_periodicBernoulli_div {y : ℝ} (hy : 0 < y) (a : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    IntegrableOn (fun t : ℝ => periodicBernoulli a t / (y + t) ^ p) (Ioi 0) := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound a
  have hz0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h := (integrableOn_div_add_pow (measurable_periodicBernoulli a) (C := C) hC hz0
    Real.pi_pos le_rfl (by simp [Complex.arg_ofReal_of_nonneg hy.le]) hp).1
  have h2 := h.re
  refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show ((periodicBernoulli a t : ℂ) / ((y : ℂ) + t) ^ p).re = _
  rw [← ofReal_add, ← ofReal_pow, ← ofReal_div, ofReal_re]

/-- `bernInt` at a real `y > 0` is the real integral. -/
theorem bernInt_ofReal (y : ℝ) (a p : ℕ) :
    bernInt a p y = ((∫ t in Ioi (0 : ℝ), periodicBernoulli a t / (y + t) ^ p : ℝ) : ℂ) := by
  rw [bernInt]
  have := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun t : ℝ => periodicBernoulli a t / (y + t) ^ p)
  refine Eq.trans ?_ this
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  show _ = ((periodicBernoulli a t / (y + t) ^ p : ℝ) : ℂ)
  push_cast
  rfl

/-- **The expansion with its remainder at a real `y > 0`**:
`ρ_j(y) = −∫₀^∞ B̃_{2j+2}(t)/(y + t)^{2j+1} dt / ((2j + 1)(2j + 2))`, `j ≥ 1`. -/
theorem barnesRho_eq {y : ℝ} (hy : 0 < y) {j : ℕ} (hj : 1 ≤ j) :
    barnesRho y j = -(1 / ((2 * (j : ℝ) + 1) * (2 * j + 2)) *
      ∫ t in Ioi (0 : ℝ), periodicBernoulli (2 * j + 2) t / (y + t) ^ (2 * j + 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hz : (y : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simpa using hy
  have hsum := glaisherR_sub_sum (2 * i + 1) hz
  rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring, sum_glaisherCoeff,
    show 2 * i + 1 + 3 = 2 * (i + 1) + 2 by ring, bernInt_ofReal] at hsum
  have hterm : ∀ k : ℕ, (bernoulli (2 * k + 2) : ℂ) / (2 * k * (2 * k + 1) * (2 * k + 2)) *
      (y : ℂ) ^ (-((2 * k : ℕ) : ℤ)) = ((barnesTerm y k : ℝ) : ℂ) := fun k => by
    rw [zpow_neg, zpow_natCast, barnesTerm]
    push_cast
    rw [← div_eq_mul_inv, div_div]
  rw [sum_congr rfl (fun k _ => hterm k), ← ofReal_sum] at hsum
  have hre := congrArg Complex.re hsum
  have hc : (1 / ((((2 * i + 1 : ℕ) : ℂ) + 2) * (((2 * i + 1 : ℕ) : ℂ) + 3)) : ℂ)
      = ((1 / ((2 * ((i + 1 : ℕ) : ℝ) + 1) * (2 * ((i + 1 : ℕ) : ℝ) + 2)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc, ← ofReal_mul, ← ofReal_neg] at hre
  simp only [sub_re, add_re, neg_re, ofReal_re] at hre
  rw [barnesRho]
  linarith

/-- **`ρ_{j−1}` as an integral of one sign**:
`ρ_{j−1}(y) = ∫₀^∞ (B_{2j+2} − B̃_{2j+2}(t))/(y + t)^{2j+1} dt / ((2j + 1)(2j + 2))`. -/
theorem barnesRho_pred_eq {y : ℝ} (hy : 0 < y) {j : ℕ} (hj : 1 ≤ j) :
    barnesRho y (j - 1) = 1 / ((2 * (j : ℝ) + 1) * (2 * j + 2)) *
      ∫ t in Ioi (0 : ℝ),
        ((bernoulli (2 * j + 2) : ℝ) - periodicBernoulli (2 * j + 2) t)
          / (y + t) ^ (2 * j + 1) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  obtain ⟨hI, hval⟩ := integral_inv_add_pow hy (by omega : 2 ≤ 2 * j + 1)
  have hB := integrableOn_periodicBernoulli_div hy (2 * j + 2) (by omega : 2 ≤ 2 * j + 1)
  have hsplit : (∫ t in Ioi (0 : ℝ), ((bernoulli (2 * j + 2) : ℝ)
        - periodicBernoulli (2 * j + 2) t) / (y + t) ^ (2 * j + 1))
      = (bernoulli (2 * j + 2) : ℝ) * (1 / ((((2 * j + 1 : ℕ) : ℝ) - 1) * y ^ (2 * j + 1 - 1)))
        - ∫ t in Ioi (0 : ℝ), periodicBernoulli (2 * j + 2) t / (y + t) ^ (2 * j + 1) := by
    rw [← hval, ← integral_const_mul, ← integral_sub (hI.const_mul _) hB]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  have h1 : barnesRho y (j - 1) = barnesRho y j + barnesTerm y j := by
    have := barnesRho_succ y (j - 1)
    rwa [show j - 1 + 1 = j by omega] at this
  rw [h1, barnesRho_eq hy hj, hsplit, barnesTerm, show 2 * j + 1 - 1 = 2 * j by omega]
  have hy0 : y ^ (2 * j) ≠ 0 := pow_ne_zero _ hy.ne'
  push_cast
  field_simp
  ring

/-- **The sign of the remainder**: `(−1)^j ρ_{j−1}(y) ≥ 0`. -/
theorem barnesRho_sign {y : ℝ} (hy : 0 < y) {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ (-1) ^ j * barnesRho y (j - 1) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  rw [barnesRho_pred_eq hy hj, ← mul_assoc, mul_comm ((-1 : ℝ) ^ j), mul_assoc,
    ← integral_const_mul]
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  have h := periodicBernoulli_sub_sign (m := j + 1) (by omega) t
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_succ] at h
  have hd : (0 : ℝ) < (y + t) ^ (2 * j + 1) := by positivity
  rw [← mul_div_assoc]
  exact div_nonneg (by linarith) hd.le

/-- **The terms envelop the remainder**: `ρ_{k−1}(y)` has the sign `(−1)^k` of the term `k` and
is bounded by it. -/
theorem barnesRho_enveloping {y : ℝ} (hy : 0 < y) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ (-1) ^ k * barnesRho y (k - 1) ∧ |barnesRho y (k - 1)| ≤ barnesTau y k := by
  have h1 := barnesRho_sign hy hk
  have h2 := barnesRho_sign hy (j := k + 1) (by omega)
  rw [Nat.add_sub_cancel, pow_succ] at h2
  have h3 : barnesRho y (k - 1) = barnesRho y k + barnesTerm y k := by
    have := barnesRho_succ y (k - 1)
    rwa [show k - 1 + 1 = k by omega] at this
  rw [barnesTerm_eq_tau hy hk] at h3
  have hsq : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have habs : |barnesRho y (k - 1)| = (-1) ^ k * barnesRho y (k - 1) := by
    rcases neg_one_pow_eq_or ℝ k with h | h
    · rw [h, one_mul] at h1 ⊢; exact abs_of_nonneg h1
    · rw [h] at h1 ⊢
      rw [abs_of_nonpos (by linarith)]
      ring
  refine ⟨h1, ?_⟩
  rw [habs, h3, mul_add, ← mul_assoc, hsq, one_mul]
  linarith

/-- `τ_k(y) ≤ 16 (k + 1)² / 4^k` at `y ≥ 4k + 4`. -/
theorem barnesTau_le {y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : ((4 * k + 4 : ℕ) : ℝ) ≤ y) :
    barnesTau y k ≤ 16 * ((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k := by
  have h0 : (0 : ℝ) < ((4 * k + 4 : ℕ) : ℝ) := by positivity
  refine (barnesTau_anti h0 hy k).trans ?_
  rw [barnesTau_natCast, glaisherTau_eq_abs (by omega) hk]
  exact abs_glaisherTerm_le hk le_rfl

end Azurite.DLMF
