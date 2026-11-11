/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section10ContourBounds

/-!
# DLMF §2.10(iii): 2.10.23

`₀F₂(−; 1, 1; x) = ∫_{−1/2}^∞ x^t/Γ(t+1)³ dt + 2ℜ ∫_{−1/2}^{i∞} x^t/Γ(t+1)³ dt/(e^{−2πit} − 1)
= ∫_0^∞ x^t/Γ(t+1)³ dt + O(1)` as `x → +∞` (`dlmf_2_10_23`, `dlmf_2_10_23_bound`). The path from
`−½` to `i∞` is the quarter circle `|t| = ½` from `−½` to `i/2` followed by the imaginary axis
(`cotPathInf`).

From 2.10.22 (`dlmf_2_10_22`): for real `x` the integrand on `𝒞₂` is the conjugate of the one on
`𝒞₁` and `𝒞₂` is the reflection of `𝒞₁` (`cotLower_eq_neg_conj_cotUpper`), so the two contour
terms are `−2ℜ∫_{𝒞₁}`. As `n → ∞` the big quarter circle contributes `O(n^{−1/2})`
(`norm_arc_integrand_le`, the DLMF's appeal to 5.11.7) and the vertical segment tends to the
integral along the imaginary axis (`integrableOn_imag_integrand`). The `O(1)` bound uses
`|x^t| ≤ 1` for `ℜt ≤ 0`, `x ≥ 1`.
-/

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real Nat

namespace Azurite.DLMF

theorem intervalIntegral_conj' (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, (starRingEnd ℂ) (f x) = (starRingEnd ℂ) (∫ x in a..b, f x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

/-! ### Conjugation symmetry -/

theorem hypF_conj {x : ℝ} (hx : 0 < x) (z : ℂ) :
    hypF x ((starRingEnd ℂ) z) = (starRingEnd ℂ) (hypF x z) := by
  have harg : (x : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  rw [hypF, hypF, Complex.cpow_conj _ _ harg, Complex.conj_ofReal, map_div₀, map_pow,
    ← Complex.Gamma_conj, map_add, map_one]

/-- The integrand on `𝒞₂` is the reflection of the one on `𝒞₁`. -/
theorem hypF_div_conj {x : ℝ} (hx : 0 < x) (z : ℂ) :
    hypF x z / (cexp (2 * π * I * z) - 1) =
      (starRingEnd ℂ) (hypF x ((starRingEnd ℂ) z) /
        (cexp (-2 * π * I * (starRingEnd ℂ) z) - 1)) := by
  rw [map_div₀, hypF_conj hx, Complex.conj_conj, map_sub, map_one, ← Complex.exp_conj]
  have : (starRingEnd ℂ) (-2 * ↑π * I * (starRingEnd ℂ) z) = 2 * π * I * z := by
    simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      Complex.conj_conj]
    ring
  rw [this]

/-- A piece of `𝒞` that is the reflection of another piece reversed. -/
theorem cotPiece_conj {R : ℝ} {u v : ℂ → ℂ}
    (hv : ∀ z, v z = (starRingEnd ℂ) (u ((starRingEnd ℂ) z)))
    {i j : ℕ} {c a b : ℝ} (hside : ∀ s, cotSide R j s = (starRingEnd ℂ) (cotSide R i (c - s)))
    (hd : ∀ s, deriv (cotSide R j) s = -(starRingEnd ℂ) (deriv (cotSide R i) (c - s))) :
    cotPiece R v j a b = -(starRingEnd ℂ) (cotPiece R u i (c - b) (c - a)) := by
  simp only [cotPiece]
  have e : ∀ s, v (cotSide R j s) * deriv (cotSide R j) s =
      -(starRingEnd ℂ) (u (cotSide R i (c - s)) * deriv (cotSide R i) (c - s)) := fun s => by
    rw [hv, hside, hd, Complex.conj_conj, map_mul]; ring
  simp only [e, intervalIntegral.integral_neg, intervalIntegral_conj']
  rw [intervalIntegral.integral_comp_sub_left
    (fun s => u (cotSide R i s) * deriv (cotSide R i) s) c]

theorem cotSide₀_conj (R s : ℝ) :
    cotSide R 0 s = (starRingEnd ℂ) (cotSide R 0 (1 - s)) := by
  simp only [cotSide, cexp_ofReal_mul_I, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  rw [show π * (1 - s) - π / 2 = -(π * s - π / 2) by ring, Real.cos_neg, Real.sin_neg]
  push_cast; ring

theorem cotSide₂_conj (R s : ℝ) :
    cotSide R 2 s = (starRingEnd ℂ) (cotSide R 2 (5 - s)) := by
  simp only [cotSide, cexp_ofReal_mul_I, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I,
    map_div₀, map_one, map_ofNat]
  rw [show π * (5 - s) - 3 * π / 2 = 2 * π - (π * s - 3 * π / 2) by ring, Real.cos_two_pi_sub,
    Real.sin_two_pi_sub]
  push_cast; ring

theorem cotSide₃_conj (R s : ℝ) :
    cotSide R 3 s = (starRingEnd ℂ) (cotSide R 1 (5 - s)) := by
  simp only [cotSide, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- `∫_{𝒞₂} x^t/Γ(t+1)³ dt/(e^{2πit} − 1) = −conj ∫_{𝒞₁} x^t/Γ(t+1)³ dt/(e^{−2πit} − 1)`. -/
theorem cotLower_eq_neg_conj_cotUpper {x : ℝ} (hx : 0 < x) (R : ℝ) :
    cotLower R (fun t => hypF x t / (cexp (2 * π * I * t) - 1)) =
      -(starRingEnd ℂ) (cotUpper R (fun t => hypF x t / (cexp (-2 * π * I * t) - 1))) := by
  have hv := hypF_div_conj hx
  have h2 := cotPiece_conj (R := R) (u := fun t => hypF x t / (cexp (-2 * π * I * t) - 1))
    (v := fun t => hypF x t / (cexp (2 * π * I * t) - 1)) hv (i := 2) (j := 2) (c := 5)
    (a := 5 / 2) (b := 3)
    (cotSide₂_conj R) (fun s => by
      rw [deriv_cotSide₂]
      simp only
      rw [cotSide₂_conj R s, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring)
  have h3 := cotPiece_conj (R := R) (u := fun t => hypF x t / (cexp (-2 * π * I * t) - 1))
    (v := fun t => hypF x t / (cexp (2 * π * I * t) - 1)) hv (i := 1) (j := 3) (c := 5)
    (a := 3) (b := 4)
    (cotSide₃_conj R) (fun s => by
      rw [deriv_cotSide₃, deriv_cotSide₁]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring)
  have h0 := cotPiece_conj (R := R) (u := fun t => hypF x t / (cexp (-2 * π * I * t) - 1))
    (v := fun t => hypF x t / (cexp (2 * π * I * t) - 1)) hv (i := 0) (j := 0) (c := 1)
    (a := 0) (b := 1 / 2)
    (cotSide₀_conj R) (fun s => by
      rw [deriv_cotSide₀]
      simp only
      rw [cotSide₀_conj R s, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring)
  simp only [cotLower, cotUpper, h2, h3, h0, map_add]
  norm_num
  ring

/-! ### The vertical segment and the limit `n → ∞` -/

/-- The segment of `𝒞₁` from `iR` down to `i/2`: `−∫_{1/2}^R u(iy) i dy`. -/
theorem cotPiece_one_eq {R : ℝ} (hR : R ≠ 1 / 2) (u : ℂ → ℂ) :
    cotPiece R u 1 1 2 = -∫ y in (1 / 2 : ℝ)..R, u ((y : ℂ) * I) * I := by
  have ha : (1 / 2 - R) ≠ 0 := sub_ne_zero.mpr hR.symm
  simp only [cotPiece, deriv_cotSide₁]
  rw [intervalIntegral.integral_mul_const]
  have h := intervalIntegral.integral_comp_mul_add (a := 1) (b := 2)
    (fun y : ℝ => u ((y : ℂ) * I)) ha (2 * R - 1 / 2)
  rw [show (1 / 2 - R) * 1 + (2 * R - 1 / 2) = R by ring,
    show (1 / 2 - R) * 2 + (2 * R - 1 / 2) = 1 / 2 by ring] at h
  have h' : ∫ s in (1 : ℝ)..2, u (cotSide R 1 s) =
      ((1 / 2 - R)⁻¹ : ℝ) • ∫ y in R..(1 / 2 : ℝ), u ((y : ℂ) * I) := h
  rw [h', intervalIntegral.integral_symm, intervalIntegral.integral_mul_const, Complex.real_smul]
  have ha' : ((1 / 2 - R : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  generalize (∫ y in (1 / 2 : ℝ)..R, u ((y : ℂ) * I)) = Z
  rw [Complex.ofReal_inv]
  generalize ((1 / 2 - R : ℝ) : ℂ) = c at ha' ⊢
  field_simp

/-- The integrand `x^t/Γ(t+1)³ · 1/(e^{−2πit} − 1)` of `𝒞₁`. -/
noncomputable def cotInt (x : ℝ) (t : ℂ) : ℂ := hypF x t / (cexp (-2 * π * I * t) - 1)

/-- `∫_{−1/2}^{i∞} x^t/Γ(t+1)³ dt/(e^{−2πit} − 1)`: the quarter circle `|t| = ½` from `−½` to
`i/2`, then the imaginary axis. -/
noncomputable def cotPathInf (x : ℝ) : ℂ :=
  -cotPiece 0 (cotInt x) 2 2 (5 / 2) + ∫ y in Ioi (1 / 2 : ℝ), cotInt x ((y : ℂ) * I) * I

theorem tendsto_cotR : Tendsto (fun n : ℕ => (n : ℝ) - 1 / 2) atTop atTop := by
  simp_rw [sub_eq_add_neg]
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- **DLMF 2.10.23** (first equality): `₀F₂(−; 1, 1; x) = ∫_{−1/2}^∞ x^t/Γ(t+1)³ dt +
2ℜ ∫_{−1/2}^{i∞} x^t/Γ(t+1)³ dt/(e^{−2πit} − 1)` for `x > 0`. -/
theorem dlmf_2_10_23 {x : ℝ} (hx : 0 < x) :
    (hyp0F2 x : ℂ) = (∫ t in Ioi (-(1 / 2) : ℝ), hypF x t) + 2 * ((cotPathInf x).re : ℂ) := by
  set Rn : ℕ → ℝ := fun n => (n : ℝ) - 1 / 2 with hRndef
  have hRn : Tendsto Rn atTop atTop := tendsto_cotR
  set P := cotPiece 0 (cotInt x) 2 2 (5 / 2) with hP
  set J := ∫ y in Ioi (1 / 2 : ℝ), cotInt x ((y : ℂ) * I) * I with hJ
  set I0 := ∫ t in Ioi (-(1 / 2) : ℝ), hypF x t with hI0
  -- the partial sums
  have hS : Tendsto (fun n => ∑ j ∈ Finset.range n, (x : ℂ) ^ j / ((j ! : ℂ) ^ 3)) atTop
      (𝓝 (hyp0F2 x : ℂ)) := by
    have := (summable_hyp0F2_complex (x : ℂ)).hasSum.tendsto_sum_nat
    convert this using 2
    rw [hyp0F2, Complex.ofReal_tsum]
    push_cast; rfl
  -- the pieces of `𝒞₁`
  set A : ℕ → ℂ := fun n => cotPiece (Rn n) (cotInt x) 0 (1 / 2) 1 with hA
  set B : ℕ → ℂ := fun n => ∫ y in (1 / 2 : ℝ)..Rn n, cotInt x ((y : ℂ) * I) * I with hB
  have hU : ∀ n, 2 ≤ n → cotUpper (Rn n) (cotInt x) = A n - B n + P := fun n hn => by
    have hR : Rn n ≠ 1 / 2 := by
      simp only [hRndef]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      intro h; linarith
    simp only [cotUpper, hA, hB, cotPiece_one_eq hR]
    rw [show cotPiece (Rn n) (cotInt x) 2 2 (5 / 2) = P from rfl]
    ring
  have heq : ∀ n, 2 ≤ n → ∑ j ∈ Finset.range n, (x : ℂ) ^ j / ((j ! : ℂ) ^ 3) =
      (∫ t in (-(1 / 2) : ℝ)..Rn n, hypF x t) - 2 * (((A n - B n + P).re : ℝ) : ℂ) := by
    intro n hn
    have h22 := dlmf_2_10_22 hx (by omega : 1 ≤ n)
    rw [cotLower_eq_neg_conj_cotUpper hx] at h22
    have hfun : (fun t => hypF x t / (cexp (-2 * π * I * t) - 1)) = cotInt x := rfl
    rw [hfun, hU n hn, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num] at h22
    rw [h22, show ∀ a b : ℂ, a - b + -(starRingEnd ℂ) b = a - (b + (starRingEnd ℂ) b) from
      fun a b => by ring, Complex.add_conj]
    push_cast
    rfl
  -- limits of the pieces
  have hI : Tendsto (fun n => ∫ t in (-(1 / 2) : ℝ)..Rn n, hypF x t) atTop (𝓝 I0) :=
    intervalIntegral_tendsto_integral_Ioi _ (integrableOn_hypF_Ioi hx) hRn
  have hBl : Tendsto B atTop (𝓝 J) :=
    intervalIntegral_tendsto_integral_Ioi _ (integrableOn_imag_integrand hx) hRn
  have hAl : Tendsto A atTop (𝓝 0) := by
    set K := 2 * π * gammaLowC ^ 3 * Real.exp 3 with hK
    have hlim : Tendsto (fun n => K * Rn n ^ (-(1 / 2) : ℝ) * |(1 : ℝ) - 1 / 2|) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (y := 1 / 2) (by norm_num)).comp hRn).const_mul K
      simpa using this.mul_const |(1 : ℝ) - 1 / 2|
    refine squeeze_zero_norm' ?_ hlim
    have hM := hRn.eventually (eventually_ge_atTop (max 1 (Real.exp ((Real.log x + 3) / 3))))
    filter_upwards [hM, eventually_ge_atTop 1] with n hn hn1
    have hR1 : 1 ≤ Rn n := le_trans (le_max_left _ _) hn
    have hxR : Real.log x + 3 ≤ 3 * Real.log (Rn n) := by
      have h1 : Real.exp ((Real.log x + 3) / 3) ≤ Rn n := le_trans (le_max_right _ _) hn
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rw [Real.log_exp] at h2
      linarith
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [uIoc_of_le (by norm_num)] at hs
    exact norm_arc_integrand_le hx hn1 hR1 hxR ⟨hs.1.le, hs.2⟩
  -- conclusion
  have hR : Tendsto (fun n => (∫ t in (-(1 / 2) : ℝ)..Rn n, hypF x t) -
      2 * (((A n - B n + P).re : ℝ) : ℂ)) atTop (𝓝 (I0 - 2 * (((0 - J + P).re : ℝ) : ℂ))) := by
    refine hI.sub (Tendsto.const_mul _ ?_)
    exact (Complex.continuous_ofReal.comp Complex.continuous_re).continuousAt.tendsto.comp
      ((hAl.sub hBl).add_const P)
  have hlim := tendsto_nhds_unique hS (hR.congr' (by
    filter_upwards [eventually_ge_atTop 2] with n hn using (heq n hn).symm))
  rw [hlim, cotPathInf, ← hP, ← hJ]
  simp only [zero_sub, Complex.add_re, Complex.neg_re]
  push_cast
  ring

/-! ### The `O(1)` bound -/

theorem norm_hypF_le_one {x : ℝ} (hx : 1 ≤ x) {t : ℂ} (ht : t.re ≤ 0) :
    ‖hypF x t‖ ≤ ‖hypF 1 t‖ := by
  rw [norm_hypF (by linarith), norm_hypF one_pos, Real.one_rpow, one_mul]
  exact mul_le_of_le_one_left (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos hx ht)

theorem re_cotSide₂_nonpos {R s : ℝ} (hs : s ∈ Icc (2 : ℝ) (5 / 2)) : (cotSide R 2 s).re ≤ 0 := by
  have hπ := Real.pi_pos
  simp only [cotSide]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, re_mul_cexp_ofReal_mul_I]
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    (Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith [hs.1]) (by nlinarith [hs.2]))

/-- **DLMF 2.10.23** (second equality): `₀F₂(−; 1, 1; x) = ∫_0^∞ x^t/Γ(t+1)³ dt + O(1)` as
`x → +∞`; the bound holds for all `x ≥ 1`. -/
theorem dlmf_2_10_23_bound :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ‖(hyp0F2 x : ℂ) - ∫ t in Ioi (0 : ℝ), hypF x t‖ ≤ C := by
  have hπ := Real.pi_pos
  -- the small quarter circle, uniformly in `x ≥ 1`
  have h1c : ContinuousOn (cotInt 1) (cotPath (((1 : ℕ) : ℝ) - 1 / 2)).curve := by
    have hπI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact continuousOn_div_cexp_sub_one le_rfl (differentiable_hypF one_pos).continuous _
      fun t m hm => ⟨-m, by
        apply mul_left_cancel₀ hπI; push_cast; linear_combination -hm⟩
  have hcont : ContinuousOn (fun s => cotInt 1 (cotSide 0 2 s) * deriv (cotSide 0 2) s)
      (Icc 2 (5 / 2)) := by
    refine ContinuousOn.mul ?_ ((contDiff_cotSide 0 2).continuous_deriv le_rfl).continuousOn
    refine h1c.comp (contDiff_cotSide 0 2).continuous.continuousOn fun s hs => ?_
    exact cotSide_mem_curve (R := ((1 : ℕ) : ℝ) - 1 / 2) (i := 2) (by norm_num)
      ⟨by norm_num; linarith [hs.1], by norm_num; linarith [hs.2]⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set C1 := ∫ t in Ioc (-(1 / 2) : ℝ) 0, ‖hypF 1 t‖
  set C2 := ∫ y in Ioi (1 / 2 : ℝ), 2 * gammaLowC ^ 3 * Real.exp 3 * Real.exp (-(π / 2) * y)
  refine ⟨C1 + 2 * (M * |(5 / 2 : ℝ) - 2| + C2), fun x hx1 => ?_⟩
  have hx : 0 < x := by linarith
  have hint := integrableOn_hypF_Ioi hx
  have hsplit : ∫ t in Ioi (-(1 / 2) : ℝ), hypF x t =
      (∫ t in Ioc (-(1 / 2) : ℝ) 0, hypF x t) + ∫ t in Ioi (0 : ℝ), hypF x t := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (-(1 / 2) : ℝ) ≤ 0)]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set (Ioc_subset_Ioi_self)) (hint.mono_set (Ioi_subset_Ioi (by norm_num)))
  rw [dlmf_2_10_23 hx, hsplit, show ∀ a b c : ℂ, a + b + c - b = a + c from
    fun a b c => by ring]
  -- the piece `[−½, 0]`
  have hI : ‖∫ t in Ioc (-(1 / 2) : ℝ) 0, hypF x t‖ ≤ C1 := by
    refine norm_integral_le_of_norm_le ?_ ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun t ht => norm_hypF_le_one hx1 (by simpa using ht.2)))
    exact ((((differentiable_hypF one_pos).continuous.comp continuous_ofReal).norm.continuousOn
      ).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- the imaginary axis
  have hJ : ‖∫ y in Ioi (1 / 2 : ℝ), cotInt x ((y : ℂ) * I) * I‖ ≤ C2 := by
    refine norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi _ (by positivity)).const_mul _)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun y hy => ?_))
    refine (norm_imag_integrand_le hx (le_of_lt (mem_Ioi.mp hy))).trans (le_of_eq ?_)
    ring_nf
  -- the small quarter circle
  have hP : ‖cotPiece 0 (cotInt x) 2 2 (5 / 2)‖ ≤ M * |(5 / 2 : ℝ) - 2| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [uIoc_of_le (by norm_num)] at hs
    have hs' : s ∈ Icc (2 : ℝ) (5 / 2) := ⟨hs.1.le, hs.2⟩
    refine le_trans ?_ (hM s hs')
    rw [norm_mul, norm_mul, cotInt, cotInt, norm_div, norm_div]
    gcongr
    exact norm_hypF_le_one hx1 (re_cotSide₂_nonpos hs')
  have hre : ‖((cotPathInf x).re : ℂ)‖ ≤ ‖cotPathInf x‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have hpath : ‖cotPathInf x‖ ≤ M * |(5 / 2 : ℝ) - 2| + C2 := by
    rw [cotPathInf]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    linarith
  calc ‖(∫ t in Ioc (-(1 / 2) : ℝ) 0, hypF x t) + 2 * ((cotPathInf x).re : ℂ)‖
      ≤ ‖∫ t in Ioc (-(1 / 2) : ℝ) 0, hypF x t‖ + 2 * ‖((cotPathInf x).re : ℂ)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]; norm_num
    _ ≤ C1 + 2 * (M * |(5 / 2 : ℝ) - 2| + C2) := by linarith

end Azurite.DLMF
