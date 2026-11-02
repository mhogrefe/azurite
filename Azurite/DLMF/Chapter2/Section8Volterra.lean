/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section7LGVolterra

/-!
# DLMF §2.8(ii): the forced Volterra equation

The Volterra equation of `Section7LGVolterra` with a general forcing term `y₀` in place of `1`:

`y(x) = y₀(x) − ½ ∫_{a₁}^{x} (1 − e^{2ξ(v) − 2ξ(x)}) q(v) y(v) dv`,

with `y₀` continuous and `|y₀| ≤ M` on `I`. Picard iteration (`forcedIter`) gives a solution
(`VolterraLG.exists_forced_solution`) with `|y − y₀| ≤ M (e^{V/2} − 1)`, `y′ = y₀′ − sP`,
`P′ = −2sP + qy` and `|P| ≤ 2M (e^{V/2} − 1)`, where `P(x) = e^{−2ξ(x)} ∫_{a₁}^{x} e^{2ξ} q y` and
`V(x) = ∫_{a₁}^{x} |q|`.
-/

open Filter Topology Set MeasureTheory

namespace Azurite.DLMF

variable {I : Set ℝ}

/-- The Picard iterates with forcing `y₀`: `h₀ = y₀`,
`h_{n+1}(x) = −½ ∫_{a₁}^{x} (1 − e^{2ξ(v)−2ξ(x)}) q(v) hₙ(v) dv`. -/
noncomputable def forcedIter (I : Set ℝ) (q ξ y₀ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => y₀
  | n + 1 => fun x => -(1 / 2) * ∫ v in I ∩ Iic x,
      (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * forcedIter I q ξ y₀ n v

namespace VolterraLG

variable {q ξ s : ℝ → ℝ} (H : VolterraLG I q ξ s) {y₀ : ℝ → ℝ} {M : ℝ}
  (hy0 : ContinuousOn y₀ I) (hM : ∀ x ∈ I, |y₀ x| ≤ M)
include H hy0 hM

omit hy0 in
theorem M_nonneg : 0 ≤ M := by
  obtain ⟨x, hx⟩ := H.nonempty
  exact (abs_nonneg _).trans (hM x hx)

theorem forcedIter_bound (n : ℕ) :
    ContinuousOn (forcedIter I q ξ y₀ n) I ∧ ∀ x ∈ I,
      |forcedIter I q ξ y₀ n x| ≤ M * ((volterraV I q x / 2) ^ n / n.factorial) := by
  have hM0 := H.M_nonneg hM
  induction n with
  | zero => exact ⟨hy0, fun x hx => by simpa [forcedIter] using hM x hx⟩
  | succ n ih =>
    obtain ⟨hc, hb⟩ := ih
    have hbd : ∀ x ∈ I, ∃ C, ∀ v ∈ I ∩ Iic x, |forcedIter I q ξ y₀ n v| ≤ C := fun x hx =>
      ⟨M * ((volterraV I q x / 2) ^ n / n.factorial), fun v hv => (hb v hv.1).trans (by
        gcongr
        · exact div_nonneg (H.V_nonneg v) zero_le_two
        · exact H.V_mono hx hv.2)⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact ((H.hasDerivAt_kernel hc hbd hx).const_mul (-(1 / 2))).continuousAt.continuousWithinAt
    · have hΦ : ∀ t : ℝ, HasDerivAt
          (fun t : ℝ => M * ((t / 2) ^ (n + 1) / ((n + 1).factorial : ℝ)))
          (M * ((t / 2) ^ n / (n.factorial : ℝ) / 2)) t := by
        intro t
        have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
        have h2 := (((hasDerivAt_pow (n + 1) (t / 2)).comp t h1).div_const
          ((n + 1).factorial : ℝ)).const_mul M
        refine h2.congr_deriv ?_
        rw [Nat.add_sub_cancel, Nat.factorial_succ]
        push_cast
        field_simp
      obtain ⟨hint, heq⟩ := H.integral_abs_mul_comp_V hΦ (by fun_prop)
      have key := heq x hx
      simp only [zero_div, zero_pow (Nat.succ_ne_zero n), sub_zero, mul_zero] at key
      show |-(1 / 2) * _| ≤ _
      rw [abs_mul, abs_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)]
      have hle : |∫ v in I ∩ Iic x,
          (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * forcedIter I q ξ y₀ n v| ≤
          ∫ v in I ∩ Iic x, |q v| * (M * ((volterraV I q v / 2) ^ n / n.factorial / 2)) * 2 := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le ((hint x hx).mul_const 2) ?_
        refine (ae_restrict_iff' (H.measR x)).mpr (Eventually.of_forall fun v hv => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 := H.abs_kernel_le hv.1 hx hv.2
        have h2 := hb v hv.1
        calc |1 - Real.exp (2 * ξ v - 2 * ξ x)| * |q v| * |forcedIter I q ξ y₀ n v|
            ≤ 1 * |q v| * (M * ((volterraV I q v / 2) ^ n / n.factorial)) := by gcongr
          _ = |q v| * (M * ((volterraV I q v / 2) ^ n / n.factorial / 2)) * 2 := by ring
      rw [integral_mul_const, key] at hle
      linarith

theorem forcedIter_summable {x : ℝ} (hx : x ∈ I) :
    Summable fun n => |forcedIter I q ξ y₀ n x| :=
  ((Real.summable_pow_div_factorial (volterraV I q x / 2)).mul_left M).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun n => (H.forcedIter_bound hy0 hM n).2 x hx

omit hy0 hM in
/-- The solution `y = ∑ hₙ` of the forced Volterra equation. -/
noncomputable def fsol (_ : VolterraLG I q ξ s) (y₀ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, forcedIter I q ξ y₀ n x

theorem fsol_sub {x : ℝ} (hx : x ∈ I) :
    |H.fsol y₀ x - y₀ x| ≤ M * (Real.exp (volterraV I q x / 2) - 1) := by
  have hs := (H.forcedIter_summable hy0 hM hx).of_abs
  rw [fsol, hs.tsum_eq_zero_add, show forcedIter I q ξ y₀ 0 x = y₀ x from rfl,
    add_sub_cancel_left]
  have hsum := (Real.summable_pow_div_factorial (volterraV I q x / 2))
  have h1 : M * (Real.exp (volterraV I q x / 2) - 1) =
      ∑' n : ℕ, M * ((volterraV I q x / 2) ^ (n + 1) / (n + 1).factorial) := by
    rw [tsum_mul_left, ← tsum_pow_div_factorial, hsum.tsum_eq_zero_add]
    simp
  rw [h1]
  have hs1 : Summable fun n => ‖forcedIter I q ξ y₀ (n + 1) x‖ := by
    simpa only [Real.norm_eq_abs] using
      (summable_nat_add_iff 1).mpr (H.forcedIter_summable hy0 hM hx)
  have h2 := norm_tsum_le_tsum_norm hs1
  rw [Real.norm_eq_abs] at h2
  refine h2.trans (Summable.tsum_le_tsum (fun n => ?_) hs1
    (((summable_nat_add_iff 1).mpr hsum).mul_left M))
  rw [Real.norm_eq_abs]
  exact (H.forcedIter_bound hy0 hM (n + 1)).2 x hx

theorem abs_fsol_le {x : ℝ} (hx : x ∈ I) :
    |H.fsol y₀ x| ≤ M * Real.exp (volterraV I q x / 2) := by
  have h1 := H.fsol_sub hy0 hM hx
  have h2 := abs_sub_abs_le_abs_sub (H.fsol y₀ x) (y₀ x)
  have h3 := hM x hx
  nlinarith

theorem fsol_cont : ContinuousOn (H.fsol y₀) I := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := exists_gt_mem H.isOpen hx
  have hS : IsOpen (I ∩ Iio b) := H.isOpen.inter isOpen_Iio
  have hM0 := H.M_nonneg hM
  have hc : ContinuousOn (H.fsol y₀) (I ∩ Iio b) :=
    continuousOn_tsum (fun n => (H.forcedIter_bound hy0 hM n).1.mono inter_subset_left)
      ((Real.summable_pow_div_factorial (volterraV I q b / 2)).mul_left M) fun n y hy => by
        rw [Real.norm_eq_abs]
        refine ((H.forcedIter_bound hy0 hM n).2 y hy.1).trans ?_
        gcongr
        · exact div_nonneg (H.V_nonneg y) zero_le_two
        · exact H.V_mono hb hy.2.le
  exact (hc.continuousAt (hS.mem_nhds ⟨hx, hxb⟩)).continuousWithinAt

theorem fsol_bdd : ∀ x ∈ I, ∃ C, ∀ v ∈ I ∩ Iic x, |H.fsol y₀ v| ≤ C := fun x hx =>
  ⟨M * Real.exp (volterraV I q x / 2), fun v hv => (H.abs_fsol_le hy0 hM hv.1).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [H.V_mono hx hv.2]))
      (H.M_nonneg hM))⟩

/-- The forced Volterra equation
`y(x) = y₀(x) − ½ ∫_{a₁}^{x} (1 − e^{2ξ(v)−2ξ(x)}) q(v) y(v) dv`. -/
theorem fsol_eq {x : ℝ} (hx : x ∈ I) :
    H.fsol y₀ x = y₀ x - 1 / 2 * ∫ v in I ∩ Iic x,
      (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * H.fsol y₀ v := by
  have hs := (H.forcedIter_summable hy0 hM hx).of_abs
  have hM0 := H.M_nonneg hM
  simp only [fsol]
  rw [hs.tsum_eq_zero_add]
  simp only [forcedIter]
  rw [tsum_mul_left]
  have hF : ∀ n, IntegrableOn
      (fun v => (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * forcedIter I q ξ y₀ n v)
      (I ∩ Iic x) := by
    intro n
    have hexp : ContinuousOn (fun v => 1 - Real.exp (2 * ξ v - 2 * ξ x)) I :=
      continuousOn_const.sub (Real.continuous_exp.comp_continuousOn
        ((continuousOn_const.mul H.ξ_cont).sub continuousOn_const))
    refine H.integrableOn_mul hexp (H.forcedIter_bound hy0 hM n).1 hx
      (C := M * ((volterraV I q x / 2) ^ n / n.factorial)) fun v hv => ?_
    rw [abs_mul]
    calc |1 - Real.exp (2 * ξ v - 2 * ξ x)| * |forcedIter I q ξ y₀ n v|
        ≤ 1 * (M * ((volterraV I q v / 2) ^ n / n.factorial)) :=
          mul_le_mul (H.abs_kernel_le hv.1 hx hv.2) ((H.forcedIter_bound hy0 hM n).2 v hv.1)
            (abs_nonneg _) zero_le_one
      _ ≤ M * ((volterraV I q x / 2) ^ n / n.factorial) := by
          rw [one_mul]
          gcongr
          · exact div_nonneg (H.V_nonneg v) zero_le_two
          · exact H.V_mono hx hv.2
  have hFs : Summable fun n => ∫ v in I ∩ Iic x,
      ‖(1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * forcedIter I q ξ y₀ n v‖ := by
    refine (((Real.summable_pow_div_factorial (volterraV I q x / 2)).mul_left M).mul_left
      (volterraV I q x)).of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      fun n => ?_
    calc ∫ v in I ∩ Iic x, ‖(1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * forcedIter I q ξ y₀ n v‖
        ≤ ∫ v in I ∩ Iic x, |q v| * (M * ((volterraV I q x / 2) ^ n / n.factorial)) := by
          refine setIntegral_mono_on (hF n).norm ((H.q_int x hx).abs.mul_const _) (H.measR x)
            fun v hv => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          calc |1 - Real.exp (2 * ξ v - 2 * ξ x)| * |q v| * |forcedIter I q ξ y₀ n v|
              ≤ 1 * |q v| * (M * ((volterraV I q x / 2) ^ n / n.factorial)) := by
                gcongr
                · exact H.abs_kernel_le hv.1 hx hv.2
                · refine ((H.forcedIter_bound hy0 hM n).2 v hv.1).trans ?_
                  gcongr
                  · exact div_nonneg (H.V_nonneg v) zero_le_two
                  · exact H.V_mono hx hv.2
            _ = |q v| * (M * ((volterraV I q x / 2) ^ n / n.factorial)) := by ring
      _ = volterraV I q x * (M * ((volterraV I q x / 2) ^ n / n.factorial)) := by
          rw [integral_mul_const, volterraV]
  rw [integral_tsum_of_summable_integral_norm hF hFs]
  have : ∀ v, ∑' n, (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * forcedIter I q ξ y₀ n v =
      (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * ∑' n, forcedIter I q ξ y₀ n v :=
    fun v => tsum_mul_left
  simp only [this]
  ring

omit hy0 hM in
/-- `P(x) = e^{−2ξ(x)} ∫_{a₁}^{x} e^{2ξ} q y`. -/
noncomputable def fsolP (_ : VolterraLG I q ξ s) (y₀ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(2 * ξ x)) * ∫ v in I ∩ Iic x,
    Real.exp (2 * ξ v) * q v * ∑' n, forcedIter I q ξ y₀ n v

theorem fsol_hasDerivAt {x : ℝ} (hx : x ∈ I) {y₀' : ℝ} (hd : HasDerivAt y₀ y₀' x) :
    HasDerivAt (H.fsol y₀) (y₀' - s x * H.fsolP y₀ x) x := by
  have hK := hd.sub ((H.hasDerivAt_kernel (H.fsol_cont hy0 hM) (H.fsol_bdd hy0 hM) hx).const_mul
    (1 / 2))
  refine hK.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards [H.isOpen.mem_nhds hx] with y hy using H.fsol_eq hy0 hM hy
  · simp only [fsolP, fsol]
    ring

theorem fsolP_hasDerivAt {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (H.fsolP y₀) (-2 * s x * H.fsolP y₀ x + q x * H.fsol y₀ x) x := by
  have hexp : ContinuousOn (fun v => Real.exp (2 * ξ v)) I :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul H.ξ_cont)
  have i2 : ∀ y ∈ I, IntegrableOn (fun v => Real.exp (2 * ξ v) * q v * H.fsol y₀ v)
      (I ∩ Iic y) := fun y hy => by
    obtain ⟨C, hC⟩ := H.fsol_bdd hy0 hM y hy
    refine H.integrableOn_mul hexp (H.fsol_cont hy0 hM) hy (C := Real.exp (2 * ξ y) * C)
      fun v hv => ?_
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [H.ξ_mono hv.1 hy hv.2])) (hC v hv)
      (abs_nonneg _) (Real.exp_pos _).le
  have hB := hasDerivAt_setIntegral_Iic H.isOpen H.ordConnected
    ((hexp.mul H.q_cont).mul (H.fsol_cont hy0 hM)) i2 hx
  have hE : HasDerivAt (fun y => Real.exp (-(2 * ξ y))) (Real.exp (-(2 * ξ x)) * -(2 * s x)) x :=
    ((H.ξ_deriv x hx).const_mul 2).neg.exp
  refine (hE.mul hB).congr_deriv ?_
  have : Real.exp (-(2 * ξ x)) * Real.exp (2 * ξ x) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [fsolP, fsol, Pi.mul_apply]
  linear_combination (q x * ∑' n, forcedIter I q ξ y₀ n x) * this

theorem abs_fsolP_le {x : ℝ} (hx : x ∈ I) :
    |H.fsolP y₀ x| ≤ 2 * M * (Real.exp (volterraV I q x / 2) - 1) := by
  have hM0 := H.M_nonneg hM
  have hΦ : ∀ t : ℝ, HasDerivAt (fun t => 2 * M * Real.exp (t / 2)) (M * Real.exp (t / 2)) t := by
    intro t
    have := (((hasDerivAt_id t).div_const 2).exp).const_mul (2 * M)
    exact this.congr_deriv (by simp only [id]; ring)
  obtain ⟨hint, heq⟩ := H.integral_abs_mul_comp_V hΦ (by fun_prop)
  have key := heq x hx
  simp only [zero_div, Real.exp_zero, mul_one] at key
  have hle : |∫ v in I ∩ Iic x, Real.exp (2 * ξ v) * q v * H.fsol y₀ v| ≤
      Real.exp (2 * ξ x) * ∫ v in I ∩ Iic x, |q v| * (M * Real.exp (volterraV I q v / 2)) := by
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hint x hx).const_mul _) ?_
    refine (ae_restrict_iff' (H.measR x)).mpr (Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (2 * ξ v) ≤ Real.exp (2 * ξ x) :=
      Real.exp_le_exp.mpr (by linarith [H.ξ_mono hv.1 hx hv.2])
    have h2 := H.abs_fsol_le hy0 hM hv.1
    calc Real.exp (2 * ξ v) * |q v| * |H.fsol y₀ v|
        ≤ Real.exp (2 * ξ x) * |q v| * (M * Real.exp (volterraV I q v / 2)) := by gcongr
      _ = Real.exp (2 * ξ x) * (|q v| * (M * Real.exp (volterraV I q v / 2))) := by ring
  rw [key] at hle
  have hP : H.fsolP y₀ x = Real.exp (-(2 * ξ x)) *
      ∫ v in I ∩ Iic x, Real.exp (2 * ξ v) * q v * H.fsol y₀ v := rfl
  rw [hP, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hee : Real.exp (-(2 * ξ x)) * Real.exp (2 * ξ x) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-(2 * ξ x)) * |∫ v in I ∩ Iic x, Real.exp (2 * ξ v) * q v * H.fsol y₀ v|
      ≤ Real.exp (-(2 * ξ x)) * (Real.exp (2 * ξ x) *
          (2 * M * Real.exp (volterraV I q x / 2) - 2 * M)) :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = 2 * M * (Real.exp (volterraV I q x / 2) - 1) := by
        rw [← mul_assoc, hee]
        ring

/-- **The forced Volterra solution**: `y′ = y₀′ − sP`, `P′ = −2sP + qy`,
`|y − y₀| ≤ M (e^{V/2} − 1)`, `|P| ≤ 2M (e^{V/2} − 1)`. -/
theorem exists_forced_solution :
    ∃ y P : ℝ → ℝ,
      (∀ x ∈ I, ∀ y₀' : ℝ, HasDerivAt y₀ y₀' x → HasDerivAt y (y₀' - s x * P x) x) ∧
      (∀ x ∈ I, HasDerivAt P (-2 * s x * P x + q x * y x) x) ∧
      ∀ x ∈ I, |y x - y₀ x| ≤ M * (Real.exp (volterraV I q x / 2) - 1) ∧
        |P x| ≤ 2 * M * (Real.exp (volterraV I q x / 2) - 1) :=
  ⟨H.fsol y₀, H.fsolP y₀, fun _ hx _ hd => H.fsol_hasDerivAt hy0 hM hx hd,
    fun _ hx => H.fsolP_hasDerivAt hy0 hM hx,
    fun _ hx => ⟨H.fsol_sub hy0 hM hx, H.abs_fsolP_le hy0 hM hx⟩⟩

end VolterraLG

end Azurite.DLMF
