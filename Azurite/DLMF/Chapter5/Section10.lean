/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section10Orth
import Azurite.DLMF.Chapter5.Section9BinetArctan
import Azurite.DLMF.Chapter3.Section5Romberg
import Azurite.DLMF.Chapter1.Section12

/-!
# DLMF §5.10: Continued Fractions

Formalization of <https://dlmf.nist.gov/5.10>: for `ℜz > 0`,
`Ln Γ(z) + z − (z − ½) ln z − ½ ln(2π) = a₀/(z + a₁/(z + a₂/(z + ⋯)))` (5.10.1), with
`a₀ = 1/12`, `a₁ = 1/30`, `a₂ = 53/210`, `a₃ = 195/371`, `a₄ = 22999/22737`,
`a₅ = 29944523/19733142`, `a₆ = 109535241009/48264275462` (5.10.2).

The DLMF does not define `aₖ` in general. Here they are the coefficients of the continued fraction
of the weight behind Binet's formula 5.9.10_1: with `w(x) = −ln(1 − e^{−2π|x|})/(2π)` (even,
positive, `binetWeight`), `J(z) = ∫ w(x)/(z − ix) dx` (`binetJ_eq_G`, `J` is Binet's function of
5.9.10_2), `a₀ = ∫ w = m₀` and `aₖ = λₖ` (`k ≥ 1`) are the recurrence coefficients of the monic
orthogonal polynomials of `w` (`Section10Orth.lean`), so the convergents of 5.10.1 are the Padé
(Gauss quadrature) approximants `Qₙ/Pₙ` at `−iz`.

* The moments `m_{2k} = ∫ x^{2k} w = (−1)ᵏ B_{2k+2}/((2k + 1)(2k + 2))` (`binet_mom_even`), from
  `−ln(1 − q) = ∑ q^{m}/m` and `ζ(2k + 2)`; hence `m_{2k} ≤ (1/12)(k/π)^{2k}` (`binet_mom_le`),
  and the general convergence theorem `SymWeight.tendsto_qz_div_pz` (Carleman) applies.
* 5.10.1 (`dlmf_5_10_1`): the continued fraction converges to `J(z)` and `Γ(z) = exp((z − ½) ln z
  − z + ½ ln(2π) + J(z))`, i.e. its value is the left side for a value of `Ln Γ(z)`.
* 5.10.2 (`dlmf_5_10_2`): the seven values, by exact rational arithmetic from `m₀, …, m₁₂`
  (`B₂, …, B₁₄`).
-/

open Complex Filter Topology Set MeasureTheory Polynomial
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Gamma-type integrals -/

theorem integrableOn_pow_mul_exp_neg_mul (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(r * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := n) (p := 1) (b := r)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hr
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]

theorem integral_pow_mul_exp_neg_mul (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(r * t)) = n ! / r ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (by positivity) hr
  have e1 : ∀ t : ℝ, t ^ ((n : ℝ) + 1 - 1) = t ^ n := fun t => by
    rw [add_sub_cancel_right, Real.rpow_natCast]
  simp_rw [e1] at h
  rw [h, Real.Gamma_nat_eq_factorial, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, div_pow, one_pow]
  ring

/-! ### The weight -/

theorem binetLog_nonpos {t : ℝ} (ht : 0 ≤ t) : binetLog t ≤ 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [binetLog]
  · exact (binetLog_neg ht).le

/-- The weight `w(x) = −ln(1 − e^{−2π|x|})/(2π)` of Binet's formula 5.9.10_1. -/
noncomputable def binetW (x : ℝ) : ℝ := -binetLog |x| / (2 * π)

theorem measurable_binetW : Measurable binetW := by
  unfold binetW binetLog; fun_prop

/-- `IntegrableOn g (0, ∞)` gives `Integrable (g ∘ |·|)`. -/
theorem integrable_comp_abs_of_integrableOn {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) :
    Integrable fun x => g |x| := by
  have hIoi : IntegrableOn (fun x => g |x|) (Ioi 0) :=
    hg.congr_fun (fun x hx => by rw [abs_of_pos (show (0 : ℝ) < x from hx)]) measurableSet_Ioi
  have hIic : IntegrableOn (fun x => g |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hIoi
  have := hIic.union hIoi
  rwa [Iic_union_Ioi, integrableOn_univ] at this

theorem integrableOn_pow_mul_binetLog (k : ℕ) :
    IntegrableOn (fun t => t ^ k * binetLog t) (Ioi 0) := by
  have hcont : ContinuousOn (fun t => t ^ k * binetLog t) (Ioi 0) := fun t ht =>
    ((continuous_pow k).continuousAt.mul (hasDerivAt_binetLog ht).continuousAt).continuousWithinAt
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · have hb : IntegrableOn (fun t => Real.log 2 - Real.log t) (Ioc 0 1) := by
      have := (intervalIntegrable_const (c := Real.log 2)).sub
        (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine hb.mono' (hcont.mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos ht.1]
    calc t ^ k * |binetLog t| ≤ 1 * |binetLog t| := by
          gcongr; exact pow_le_one₀ ht.1.le ht.2
      _ ≤ _ := by rw [one_mul]; exact abs_binetLog_le_small ht.1 ht.2
  · have hb := ((integrableOn_pow_mul_exp_neg_mul k one_pos).mono_set
      (Ioi_subset_Ioi zero_le_one)).const_mul 2
    refine hb.mono' (hcont.mono (Ioi_subset_Ioi zero_le_one) |>.aestronglyMeasurable
      measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    have ht' : (1 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (by linarith : (0 : ℝ) < t), one_mul]
    calc t ^ k * |binetLog t| ≤ t ^ k * (2 * Real.exp (-t)) := by
          gcongr; exact abs_binetLog_le_large ht'.le
      _ = 2 * (t ^ k * Real.exp (-t)) := by ring

/-- The weight of Binet's formula as a `SymWeight`. -/
noncomputable def binetWeight : SymWeight where
  w := binetW
  nonneg x := by
    unfold binetW
    have := binetLog_nonpos (abs_nonneg x)
    have := Real.pi_pos
    exact div_nonneg (by linarith) (by positivity)
  pos x hx := by
    unfold binetW
    have := binetLog_neg (abs_pos.mpr hx)
    have := Real.pi_pos
    exact div_pos (by linarith) (by positivity)
  even x := by simp [binetW]
  integrable k := by
    have hg := ((integrableOn_pow_mul_binetLog k).norm.div_const (2 * π))
    refine (integrable_comp_abs_of_integrableOn hg).mono'
      ((measurable_id.pow_const k).mul measurable_binetW).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    have := Real.pi_pos
    rw [Real.norm_eq_abs, binetW, abs_mul, abs_pow, abs_div, abs_neg, abs_of_pos (by positivity :
      (0 : ℝ) < 2 * π), Real.norm_eq_abs, abs_mul, abs_pow, abs_abs]
    rw [mul_div_assoc]

/-! ### The moments -/

theorem binetWeight_w : binetWeight.w = binetW := rfl

theorem binet_mom_odd (k : ℕ) : binetWeight.mom (2 * k + 1) = 0 := by
  rw [← binetWeight.L_X_pow]
  refine binetWeight.L_odd ?_
  rw [X_pow_comp, Odd.neg_pow ⟨k, rfl⟩]

/-- `∫₀^∞ t^{2k} (−ln(1 − e^{−2πt})) dt/π = (2k)!/(π (2π)^{2k+1}) ∑_{m≥1} m^{−(2k+2)}`. -/
theorem binet_mom_even_tsum (k : ℕ) : binetWeight.mom (2 * k) =
    (2 * k) ! / (π * (2 * π) ^ (2 * k + 1)) * ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (2 * k + 2) := by
  have hπ := Real.pi_pos
  -- reduce to `(0, ∞)`
  have h1 : binetWeight.mom (2 * k) =
      ∫ t in Ioi (0 : ℝ), t ^ (2 * k) * (-binetLog t) / π := by
    have e : (fun x : ℝ => x ^ (2 * k) * binetWeight.w x) =
        fun x => (fun t : ℝ => t ^ (2 * k) * (-binetLog t / (2 * π))) |x| := by
      funext x
      show x ^ (2 * k) * binetW x = |x| ^ (2 * k) * (-binetLog |x| / (2 * π))
      rw [binetW, (even_two_mul k).pow_abs]
    rw [SymWeight.mom, e,
      integral_comp_abs (f := fun t : ℝ => t ^ (2 * k) * (-binetLog t / (2 * π))),
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    field_simp
  -- the series `−ln(1 − q) = ∑ q^{m+1}/(m + 1)`
  set F : ℕ → ℝ → ℝ := fun m t => t ^ (2 * k) * Real.exp (-((2 * π * (m + 1)) * t)) /
    (π * (m + 1)) with hF
  have hpt : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun m => F m t) (t ^ (2 * k) * (-binetLog t) / π) :=
    fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have hq : |Real.exp (-(2 * π * t))| < 1 := by
        rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by nlinarith)
      have := (Real.hasSum_pow_div_log_of_abs_lt_one hq).mul_left (t ^ (2 * k) / π)
      convert this using 1
      · funext m
        simp only [hF]
        rw [← Real.exp_nat_mul]
        push_cast
        field_simp
      · rw [binetLog]; ring
  have hint : ∀ m : ℕ, Integrable (F m) (volume.restrict (Ioi 0)) := fun m => by
    have := (integrableOn_pow_mul_exp_neg_mul (2 * k) (r := 2 * π * (m + 1))
      (by positivity)).div_const (π * (m + 1))
    exact this
  have hval : ∀ m : ℕ, ∫ t in Ioi (0 : ℝ), F m t =
      (2 * k) ! / (π * (2 * π) ^ (2 * k + 1)) * (1 / ((m : ℝ) + 1) ^ (2 * k + 2)) := fun m => by
    simp only [hF]
    rw [integral_div, integral_pow_mul_exp_neg_mul _ (by positivity), mul_pow,
      pow_succ ((m : ℝ) + 1) (2 * k + 1)]
    field_simp
  have hsum : Summable fun m : ℕ => ∫ t in Ioi (0 : ℝ), ‖F m t‖ := by
    have hnorm : ∀ m : ℕ, ∫ t in Ioi (0 : ℝ), ‖F m t‖ = ∫ t in Ioi (0 : ℝ), F m t := fun m =>
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        have ht' : (0 : ℝ) < t := ht
        rw [Real.norm_of_nonneg (by simp only [hF]; positivity)]
    simp_rw [hnorm, hval]
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr
      (show 1 < 2 * k + 2 by omega))
    simpa using this
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  rw [show ∫ t in Ioi (0 : ℝ), ∑' m, F m t = ∫ t in Ioi (0 : ℝ), t ^ (2 * k) * (-binetLog t) / π
    from setIntegral_congr_fun measurableSet_Ioi fun t ht => (hpt t ht).tsum_eq] at h
  simp_rw [hval] at h
  rw [h1, ← h.tsum_eq, tsum_mul_left]

/-- **The moments**: `m_{2k} = (−1)ᵏ B_{2k+2}/((2k + 1)(2k + 2))`. -/
theorem binet_mom_even (k : ℕ) :
    binetWeight.mom (2 * k) =
      (-1) ^ k * _root_.bernoulli (2 * k + 2) / ((2 * k + 1) * (2 * k + 2)) := by
  have hπ := Real.pi_pos
  have hz := hasSum_zeta_nat (k := k + 1) (by omega)
  have hz' := (hasSum_nat_add_iff' 1).mpr hz
  simp only [Finset.sum_range_one, Nat.cast_zero, show 2 * (k + 1) = 2 * k + 2 by ring,
    zero_pow (show 2 * k + 2 ≠ 0 by omega), div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at hz'
  rw [binet_mom_even_tsum, hz'.tsum_eq, show 2 * k + 2 - 1 = 2 * k + 1 by omega,
    show (2 * k + 2) ! = (2 * k + 2) * ((2 * k + 1) * (2 * k) !) by
      rw [Nat.factorial_succ, Nat.factorial_succ]]
  push_cast
  have hf : ((2 * k) ! : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `m_{2n} ≤ (1/12)(n/π)^{2n}`. -/
theorem binet_mom_le (n : ℕ) : binetWeight.mom (2 * n) ≤ 1 / 12 * (1 / π * n) ^ (2 * n) := by
  have hπ := Real.pi_pos
  rw [binet_mom_even_tsum]
  have hs2 : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hsn : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ (2 * n + 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr
      (show 1 < 2 * n + 2 by omega))
    simpa using this
  have htle : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (2 * n + 2) ≤ π ^ 2 / 6 := by
    rw [← hs2.tsum_eq]
    refine hsn.tsum_le_tsum (fun m => ?_) hs2.summable
    have : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := m.cast_nonneg (α := ℝ); linarith
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ this (by omega))
  have hfac : ((2 * n) ! : ℝ) ≤ (2 * n : ℝ) ^ (2 * n) := by
    exact_mod_cast Nat.factorial_le_pow (2 * n)
  have hT0 : 0 ≤ ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (2 * n + 2) := tsum_nonneg fun m => by positivity
  calc (2 * n) ! / (π * (2 * π) ^ (2 * n + 1)) * ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (2 * n + 2)
      ≤ (2 * n : ℝ) ^ (2 * n) / (π * (2 * π) ^ (2 * n + 1)) * (π ^ 2 / 6) := by
        gcongr
    _ = 1 / 12 * (1 / π * n) ^ (2 * n) := by
        rw [pow_succ, mul_pow, mul_pow, mul_pow, div_pow, one_pow]
        field_simp
        ring

/-! ### `J(z)` as the Cauchy transform of the weight -/

theorem norm_inv_sub_mul_I_le {z : ℂ} (hz : 0 < z.re) (x : ℝ) : ‖1 / (z - I * x)‖ ≤ 1 / z.re := by
  have h : z.re ≤ ‖z - I * x‖ := by
    have := Complex.abs_re_le_norm (z - I * x)
    simp at this
    linarith [le_abs_self z.re]
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hz h

/-- `J(z) = ∫ w(x)/(z − ix) dx = −i G(−iz)` for `ℜz > 0`. -/
theorem binetJ_eq_G {z : ℂ} (hz : 0 < z.re) : binetJ z = -I * binetWeight.G (-I * z) := by
  have hπ := Real.pi_pos
  set f : ℝ → ℂ := fun x => (binetW x : ℂ) / (z - I * x) with hf
  have hne : ∀ x : ℝ, z - I * x ≠ 0 := fun x h => by
    have := congrArg re h; simp at this; linarith
  have hfint : Integrable f := by
    refine ((binetWeight.integrable 0).norm.div_const z.re).mono' ?_ (ae_of_all _ fun x => ?_)
    · have hm : Measurable fun x : ℝ => (binetW x : ℂ) * (z - I * x)⁻¹ := by
        have := measurable_binetW; fun_prop
      exact hm.aestronglyMeasurable.congr (ae_of_all _ fun x => (div_eq_mul_inv _ _).symm)
    · simp only [hf, pow_zero, one_mul]
      rw [div_eq_mul_one_div, norm_mul, Complex.norm_real, div_eq_mul_one_div ‖_‖]
      exact mul_le_mul_of_nonneg_left (norm_inv_sub_mul_I_le hz x) (norm_nonneg _)
  -- `−i G(−iz) = ∫ f`
  have hG : -I * binetWeight.G (-I * z) = ∫ x, f x := by
    rw [SymWeight.G, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have h1 := hne x
    have h2 : -I * z - x ≠ 0 := by
      intro h; apply h1; linear_combination I * h + z * I_sq
    have hI : I ≠ 0 := I_ne_zero
    have e : z - I * x = I * (-I * z - x) := by ring_nf; rw [I_sq]; ring
    simp only [hf, binetWeight_w]
    rw [e]
    field_simp
    ring_nf
    rw [I_sq]; ring
  -- fold over `(0, ∞)`
  have hsplit : ∫ x, f x = ∫ t in Ioi (0 : ℝ), (f t + f (-t)) := by
    have hIic := hfint.integrableOn (s := Iic 0)
    have hIoi := hfint.integrableOn (s := Ioi 0)
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hIic hIoi,
      ← neg_zero, ← integral_comp_neg_Ioi, neg_zero]
    have hneg : IntegrableOn (fun t => f (-t)) (Ioi 0) := by
      have := hfint.comp_neg
      exact this.integrableOn
    rw [integral_add hIoi hneg, add_comm]
  have hpair : ∀ t ∈ Ioi (0 : ℝ), f t + f (-t) =
      -(z / π) * (((binetLog t : ℝ) : ℂ) / ((t : ℂ) ^ 2 + z ^ 2)) := fun t ht => by
    have ht' : (0 : ℝ) < t := ht
    have h1 := hne t
    have h2' : z + I * t ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    have hprod : (z - I * t) * (z + I * t) = (t : ℂ) ^ 2 + z ^ 2 := by
      ring_nf; rw [I_sq]; ring
    have h3 : (t : ℂ) ^ 2 + z ^ 2 ≠ 0 := hprod ▸ mul_ne_zero h1 h2'
    have hπ' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ.ne'
    simp only [hf]
    rw [show ((binetW (-t) : ℝ) : ℂ) = binetW t by simp [binetW],
      show z - I * ((-t : ℝ) : ℂ) = z + I * t by push_cast; ring, div_add_div _ _ h1 h2', hprod]
    simp only [binetW, abs_of_pos ht']
    push_cast
    field_simp
    ring
  rw [hG, hsplit, setIntegral_congr_fun measurableSet_Ioi hpair, integral_const_mul,
    ← integral_arctan_eq_binetJ hz, integral_arctan_eq_integral_log hz]
  rfl

/-! ### 5.10.1 -/

theorem binetWeight_h_zero : binetWeight.h 0 = binetWeight.mom 0 := by
  rw [SymWeight.h, SymWeight.P_zero, one_mul, SymWeight.L_X_pow]

/-- The coefficients of 5.10.1: `a₀ = m₀ = ∫ w`, `aₖ = λₖ` (`k ≥ 1`), the recurrence
coefficients of the monic orthogonal polynomials of the weight `w`. -/
noncomputable def binetA (k : ℕ) : ℝ := if k = 0 then binetWeight.mom 0 else binetWeight.lam k

theorem binetA_pos (k : ℕ) : 0 < binetA k := by
  unfold binetA
  split_ifs
  · rw [← binetWeight_h_zero]; exact binetWeight.h_pos 0
  · exact binetWeight.lam_pos k

/-- The partial numerators `a₁, a₂, …` of 5.10.1 in the notation of §1.12 (`aₖ₊₁ = a_k` of the
DLMF). -/
noncomputable def binetCFa (k : ℕ) : ℂ := if k = 0 then 0 else (binetA (k - 1) : ℂ)

/-- The partial denominators `b₀ = 0`, `bₖ = z` of 5.10.1. -/
def binetCFb (z : ℂ) (k : ℕ) : ℂ := if k = 0 then 0 else z

theorem binetCF_canonical (z : ℂ) : ∀ n : ℕ,
    cfQ binetCFa (binetCFb z) (n + 1) = I ^ n * binetWeight.pz n (-I * z) ∧
      cfP binetCFa (binetCFb z) (n + 1) = -I * I ^ n * binetWeight.qz n (-I * z)
  | 0 => by simp [cfQ, cfP, binetCFb, SymWeight.pz_zero, SymWeight.qz_zero]
  | 1 => by
    refine ⟨?_, ?_⟩
    · rw [show cfQ binetCFa (binetCFb z) 2 = z by simp [cfQ, binetCFb], SymWeight.pz_one]
      ring_nf; rw [I_sq]; ring
    · rw [show cfP binetCFa (binetCFb z) 2 = (binetWeight.mom 0 : ℂ) by
        simp [cfP, binetCFb, binetCFa, binetA], SymWeight.qz_one]
      ring_nf; rw [I_sq]; ring
  | n + 2 => by
    obtain ⟨hq1, hp1⟩ := binetCF_canonical z (n + 1)
    obtain ⟨hq0, hp0⟩ := binetCF_canonical z n
    have ha : binetCFa (n + 2) = (binetWeight.lam (n + 1) : ℂ) := by
      simp [binetCFa, binetA]
    have hb : binetCFb z (n + 2) = z := by simp [binetCFb]
    refine ⟨?_, ?_⟩
    · rw [show n + 2 + 1 = (n + 1) + 2 from rfl, cfQ, hq1, show n + 1 + 1 = n + 2 from rfl, hb,
        ha, hq0, SymWeight.pz_succ_succ]
      linear_combination (z * I ^ (n + 1) * binetWeight.pz (n + 1) (-I * z) +
        binetWeight.lam (n + 1) * I ^ n * binetWeight.pz n (-I * z)) * I_sq
    · rw [show n + 2 + 1 = (n + 1) + 2 from rfl, cfP, hp1, show n + 1 + 1 = n + 2 from rfl, hb,
        ha, hp0, SymWeight.qz_succ_succ]
      linear_combination (-I * (z * I ^ (n + 1) * binetWeight.qz (n + 1) (-I * z) +
        binetWeight.lam (n + 1) * I ^ n * binetWeight.qz n (-I * z))) * I_sq

theorem binetCF_nonzero {z : ℂ} (hz : 0 < z.re) :
    ∀ n w, 0 ≤ w.re → CfNonzero binetCFa (binetCFb z) n w
  | 0, _, _ => trivial
  | n + 1, w, hw => by
    have hb : binetCFb z (n + 1) = z := by simp [binetCFb]
    have hre : 0 < (z + w).re := by rw [add_re]; linarith
    have hne : z + w ≠ 0 := fun h => by rw [h, zero_re] at hre; exact lt_irrefl _ hre
    refine ⟨by rw [hb]; exact hne, binetCF_nonzero hz n _ ?_⟩
    simp only [hb, binetCFa, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Complex.div_re,
      ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    have h0 : 0 < Complex.normSq (z + w) := Complex.normSq_pos.mpr hne
    exact div_nonneg (mul_nonneg (binetA_pos n).le hre.le) h0.le

/-- **DLMF 5.10.1**: for `ℜz > 0` the continued fraction
`a₀/(z + a₁/(z + a₂/(z + ⋯)))` converges, to Binet's function `J(z)`, and
`Γ(z) = exp((z − ½) ln z − z + ½ ln(2π) + J(z))`: the value of the continued fraction is
`Ln Γ(z) + z − (z − ½) ln z − ½ ln(2π)` for a value of `Ln Γ(z)`. -/
theorem dlmf_5_10_1 {z : ℂ} (hz : 0 < z.re) :
    CfConverges binetCFa (binetCFb z) (binetJ z) ∧
      Gamma z = cexp ((z - 1 / 2) * Complex.log z - z + 1 / 2 * Complex.log (2 * π) +
        binetJ z) := by
  have hπ := Real.pi_pos
  refine ⟨?_, by rw [dlmf_5_9_10_2 hz]; rfl⟩
  have hζ : (-I * z).im ≠ 0 := by simp; linarith
  have hlim := (binetWeight.tendsto_qz_div_pz (K := 1 / 12) (C := 1 / π) (by norm_num)
    (by positivity) (fun n _ => binet_mom_le n) hζ).const_mul (-I)
  rw [← binetJ_eq_G hz] at hlim
  show Tendsto (cfConv binetCFa (binetCFb z)) atTop (𝓝 (binetJ z))
  refine hlim.congr fun n => ?_
  rw [dlmf_1_12_4 _ _ (binetCF_nonzero hz n 0 (by simp)), cfA, cfB,
    (binetCF_canonical z n).1, (binetCF_canonical z n).2]
  have h1 : I ^ n ≠ 0 := pow_ne_zero _ I_ne_zero
  have h2 := binetWeight.pz_ne_zero hζ n
  field_simp

/-! ### 5.10.2 -/

/-- The values of 5.10.2. -/
def binetAQ : ℕ → ℚ
  | 0 => 1 / 12 | 1 => 1 / 30 | 2 => 53 / 210 | 3 => 195 / 371 | 4 => 22999 / 22737
  | 5 => 29944523 / 19733142 | 6 => 109535241009 / 48264275462 | _ => 0

/-- The moments `m₀, …, m₁₂` (`binet_mom_even`). -/
def binetMQ : ℕ → ℚ
  | 0 => 1 / 12 | 2 => 1 / 360 | 4 => 1 / 1260 | 6 => 1 / 1680 | 8 => 1 / 1188
  | 10 => 691 / 360360 | 12 => 1 / 156 | _ => 0

/-- `T(n, k) = L(Rₙ xᵏ)` for the polynomials `Rₙ` of the values 5.10.2. -/
def binetTQ : ℕ → ℕ → ℚ
  | 0, k => binetMQ k
  | 1, k => binetMQ (k + 1)
  | n + 2, k => binetTQ (n + 1) (k + 1) - binetAQ (n + 1) * binetTQ n k

/-- The monic polynomials with the recurrence coefficients 5.10.2. -/
noncomputable def binetR : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * binetR (n + 1) - C (binetAQ (n + 1) : ℝ) * binetR n

theorem binet_mom_eq {j : ℕ} (hj : j ≤ 12) : binetWeight.mom j = binetMQ j := by
  rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul, binet_mom_even, bernoulli_eq_bernoulli'_of_ne_one (by omega)]
    have hk : k ≤ 6 := by omega
    interval_cases k <;>
      simp [binetMQ, bernoulli'_two, bernoulli'_four, bernoulli'_six, bernoulli'_eight,
        bernoulli'_ten, bernoulli'_twelve, bernoulli'_fourteen] <;> norm_num
  · rw [binet_mom_odd]
    have hk : k ≤ 5 := by omega
    interval_cases k <;> simp [binetMQ]

theorem L_binetR (n : ℕ) : ∀ k, n + k ≤ 12 →
    binetWeight.L (binetR n * X ^ k) = binetTQ n k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk
    match n, ih with
    | 0, _ => rw [binetR, one_mul, SymWeight.L_X_pow, binet_mom_eq (by omega), binetTQ]
    | 1, _ => rw [binetR, ← pow_succ', SymWeight.L_X_pow, binet_mom_eq (by omega), binetTQ]
    | n + 2, ih =>
      rw [binetR, sub_mul, binetWeight.L_sub,
        show X * binetR (n + 1) * X ^ k = binetR (n + 1) * X ^ (k + 1) by ring,
        show C (binetAQ (n + 1) : ℝ) * binetR n * X ^ k =
          C (binetAQ (n + 1) : ℝ) * (binetR n * X ^ k) by ring, binetWeight.L_C_mul,
        ih (n + 1) (by omega) (k + 1) (by omega), ih n (by omega) k (by omega), binetTQ]
      push_cast; ring

theorem binetTQ_ratios : ∀ n < 6, binetTQ (n + 1) (n + 1) = binetAQ (n + 1) * binetTQ n n ∧
    binetTQ n n ≠ 0 := by decide +kernel

theorem binetR_eq_P : ∀ n, n ≤ 7 → binetWeight.P n = binetR n ∧
    (1 ≤ n → n ≤ 6 → binetWeight.lam n = binetAQ n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hlam : ∀ m, m + 1 ≤ 6 → binetWeight.P m = binetR m →
        binetWeight.P (m + 1) = binetR (m + 1) → binetWeight.lam (m + 1) = binetAQ (m + 1) := by
      intro m hm h0 h1
      obtain ⟨hr, hne⟩ := binetTQ_ratios m (by omega)
      rw [SymWeight.lam, show m + 1 - 1 = m from rfl, SymWeight.h, SymWeight.h, h0, h1,
        L_binetR _ _ (by omega), L_binetR _ _ (by omega), hr]
      have : (binetTQ m m : ℝ) ≠ 0 := by exact_mod_cast hne
      push_cast
      field_simp
    match n, ih with
    | 0, _ => exact ⟨rfl, fun h => absurd h (by omega)⟩
    | 1, _ => exact ⟨rfl, fun _ _ => hlam 0 (by omega) rfl rfl⟩
    | n + 2, ih =>
      obtain ⟨h1, -⟩ := ih (n + 1) (by omega) (by omega)
      obtain ⟨h0, -⟩ := ih n (by omega) (by omega)
      have hl : binetWeight.lam (n + 1) = binetAQ (n + 1) := hlam n (by omega) h0 h1
      have hP : binetWeight.P (n + 2) = binetR (n + 2) := by
        rw [SymWeight.P_succ_succ, binetR, h1, h0, hl]
      exact ⟨hP, fun _ h6 => hlam (n + 1) (by omega) h1 hP⟩

theorem binetA_eq {k : ℕ} (hk : k ≤ 6) : binetA k = binetAQ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp only [binetA, ↓reduceIte]; rw [binet_mom_eq (by norm_num)]; rfl
  · simp only [binetA, hpos.ne', ↓reduceIte]; rw [(binetR_eq_P k (by omega)).2 hpos hk]

/-- **DLMF 5.10.2**: `a₀ = 1/12`, `a₁ = 1/30`, `a₂ = 53/210`, `a₃ = 195/371`,
`a₄ = 22999/22737`, `a₅ = 29944523/19733142`, `a₆ = 109535241009/48264275462`. -/
theorem dlmf_5_10_2 :
    binetA 0 = 1 / 12 ∧ binetA 1 = 1 / 30 ∧ binetA 2 = 53 / 210 ∧ binetA 3 = 195 / 371 ∧
      binetA 4 = 22999 / 22737 ∧ binetA 5 = 29944523 / 19733142 ∧
      binetA 6 = 109535241009 / 48264275462 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [binetA_eq (by norm_num)] <;> simp [binetAQ]

end Azurite.DLMF
