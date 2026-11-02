/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section8Volterra
import Azurite.DLMF.Chapter2.Section7LG

/-!
# DLMF §2.8(ii): Case I: No Transition Points, 2.8.10–2.8.13

The transformed equation 2.8.10, `d²W/dξ² = (u² + ψ(ξ)) W` (`IsLGSolution I (fun _ => u²) ψ`), for
real `u > 0` and real `ξ` in an open interval `I = (α₁, α₂)` (finite or infinite).

* 2.8.13 (`CaseIData`): coefficients `A₀ = 1`,
  `A_{s+1} = −½ A_s′ + ½ ∫ ψ A_s` (in derivative form `2A_{s+1}′ = −A_s″ + ψ A_s`), with
  `𝒱(A₁) = ½ ∫ |ψ|` and `𝒱(Aₙ) = ∫ |Aₙ′|` finite. `dlmf_2_8_13`: for `ψ` of class `C^∞` the
  recurrence (with arbitrary constants of integration) produces such coefficients.
* 2.8.11 (`CaseIData.dlmf_2_8_11`): for every `u ≥ 1` there is a solution
  `W_{n,1}(u, ξ) = e^{uξ} (∑_{s<n} A_s(ξ)/u^s + η(u, ξ))` with `|η| ≤ C/uⁿ` and
  `|∂η/∂ξ| ≤ C/u^{n−1}`, `C` independent of `u` and `ξ` (uniform and differentiable), the reference
  point being the lower end `α₁` (`𝚫₁(α₁) = I`).
* 2.8.12 (`CaseIData.dlmf_2_8_12`): likewise
  `W_{n,2}(u, ξ) = e^{−uξ} (∑_{s<n} (−1)^s A_s(ξ)/u^s + η)`, reference point the upper end `α₂`.

The proof: the residual of the truncated sum is exactly `−2u^{1−n} Aₙ′ e^{uξ}`
(`CaseIData.sum_identity`), and the error solves `η″ + 2uη′ − ψη = 2u^{1−n} Aₙ′`
(`exists_forced_caseI`), the forced Volterra equation of `Section8Volterra` with kernel
`(1 − e^{−2u(ξ − v)})/(2u)`.
-/

open Filter Topology Set MeasureTheory
open scoped ContDiff

namespace Azurite.DLMF

variable {I : Set ℝ}

/-! ### The forced equation `η″ + 2uη′ − ψη = F` -/

/-- For `F`, `ψ` continuous and integrable on `I` and `u > 0`, `η″ + 2uη′ − ψη = F` has a solution
on `I` with `|η| ≤ (∫|F|)/(2u) · e^{∫|ψ|/(2u)}` and `|η′| ≤ (∫|F|)(1 + e^{∫|ψ|/(2u)})`. -/
theorem exists_forced_caseI (hI : IsOpen I) (hIc : I.OrdConnected) (hne : I.Nonempty)
    {ψ F : ℝ → ℝ} (hψc : ContinuousOn ψ I) (hψi : IntegrableOn ψ I) (hFc : ContinuousOn F I)
    (hFi : IntegrableOn F I) {u : ℝ} (hu : 0 < u) :
    ∃ y y' : ℝ → ℝ,
      (∀ x ∈ I, HasDerivAt y (y' x) x ∧ HasDerivAt y' (F x + ψ x * y x - 2 * u * y' x) x) ∧
      ∀ x ∈ I, |y x| ≤ (∫ v in I, |F v|) / (2 * u) * Real.exp ((∫ v in I, |ψ v|) / (2 * u)) ∧
        |y' x| ≤ (∫ v in I, |F v|) * (1 + Real.exp ((∫ v in I, |ψ v|) / (2 * u))) := by
  set ξu : ℝ → ℝ := fun x => u * x with hξu
  have hξ : ∀ x ∈ I, HasDerivAt ξu u x := fun x _ =>
    ((hasDerivAt_id x).const_mul u).congr_deriv (mul_one u)
  set 𝔉 := ∫ v in I, |F v|
  set Ψ := ∫ v in I, |ψ v|
  have hmR : ∀ x, MeasurableSet (I ∩ Iic x) := fun x => hI.measurableSet.inter measurableSet_Iic
  -- the forcing `η₀ = ∫_{α₁}^{x} (1 − e^{−2u(x−v)})/(2u) F(v) dv`
  set q₀ : ℝ → ℝ := fun v => -F v / u with hq₀
  have H₀ : VolterraLG I q₀ ξu (fun _ => u) :=
    ⟨hI, hIc, hne, hFc.neg.div_const u, fun x _ =>
      ((hFi.mono_set inter_subset_left).neg.div_const u), hξ, fun _ _ => hu.le⟩
  have hq₀int : ∀ x ∈ I, ∫ v in I ∩ Iic x, |q₀ v| ≤ 𝔉 / u := fun x hx => by
    have : ∫ v in I ∩ Iic x, |q₀ v| = (∫ v in I ∩ Iic x, |F v|) / u := by
      rw [← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [hq₀, abs_div, abs_neg, abs_of_pos hu]
    rw [this]
    exact div_le_div_of_nonneg_right (setIntegral_mono_set hFi.abs
      (ae_of_all _ fun _ => abs_nonneg _) inter_subset_left.eventuallyLE) hu.le
  set η₀ : ℝ → ℝ := fun x => -(1 / 2) * ∫ v in I ∩ Iic x,
    (1 - Real.exp (2 * ξu v - 2 * ξu x)) * q₀ v * 1 with hη₀
  set B₀ : ℝ → ℝ := fun x => ∫ v in I ∩ Iic x, Real.exp (2 * ξu v) * q₀ v * 1 with hB₀
  set η₀' : ℝ → ℝ := fun x => -u * (Real.exp (-(2 * ξu x)) * B₀ x) with hη₀'
  have hone : ∀ x ∈ I, ∃ C, ∀ v ∈ I ∩ Iic x, |(fun _ : ℝ => (1 : ℝ)) v| ≤ C :=
    fun _ _ => ⟨1, fun _ _ => by simp⟩
  have hη₀d : ∀ x ∈ I, HasDerivAt η₀ (η₀' x) x := fun x hx =>
    ((H₀.hasDerivAt_kernel continuousOn_const hone hx).const_mul (-(1 / 2))).congr_deriv
      (by simp only [hη₀', hB₀]; ring)
  have hη₀c : ContinuousOn η₀ I := fun x hx => (hη₀d x hx).continuousAt.continuousWithinAt
  have hη₀M : ∀ x ∈ I, |η₀ x| ≤ 𝔉 / (2 * u) := by
    intro x hx
    have hle : |∫ v in I ∩ Iic x, (1 - Real.exp (2 * ξu v - 2 * ξu x)) * q₀ v * 1| ≤
        ∫ v in I ∩ Iic x, |q₀ v| := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (H₀.q_int x hx).abs
        ((ae_restrict_iff' (hmR x)).mpr (Eventually.of_forall fun v hv => ?_))
      rw [Real.norm_eq_abs, mul_one, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (H₀.abs_kernel_le hv.1 hx hv.2)
    rw [hη₀, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := hq₀int x hx
    calc 1 / 2 * |∫ v in I ∩ Iic x, (1 - Real.exp (2 * ξu v - 2 * ξu x)) * q₀ v * 1|
        ≤ 1 / 2 * (𝔉 / u) := by gcongr; exact hle.trans this
      _ = 𝔉 / (2 * u) := by ring
  -- the derivative of `η₀′`
  have hexp : ContinuousOn (fun v => Real.exp (2 * ξu v)) I :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul H₀.ξ_cont)
  have hB₀d : ∀ x ∈ I, HasDerivAt B₀ (Real.exp (2 * ξu x) * q₀ x * 1) x := fun x hx =>
    hasDerivAt_setIntegral_Iic hI hIc ((hexp.mul H₀.q_cont).mul continuousOn_const)
      (fun y hy => H₀.integrableOn_mul hexp continuousOn_const hy
        (C := Real.exp (2 * ξu y)) fun v hv => by
          rw [mul_one, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (by linarith [H₀.ξ_mono hv.1 hy hv.2])) hx
  have hη₀'d : ∀ x ∈ I, HasDerivAt η₀' (-2 * u * η₀' x + F x) x := by
    intro x hx
    have hE : HasDerivAt (fun y => Real.exp (-(2 * ξu y))) (Real.exp (-(2 * ξu x)) * -(2 * u))
        x := ((hξ x hx).const_mul 2).neg.exp
    refine ((hE.mul (hB₀d x hx)).const_mul (-u)).congr_deriv ?_
    have hee : Real.exp (-(2 * ξu x)) * Real.exp (2 * ξu x) = 1 := by
      rw [← Real.exp_add]; simp
    simp only [hη₀', hq₀]
    field_simp
    linear_combination F x * hee
  have hη₀'b : ∀ x ∈ I, |η₀' x| ≤ 𝔉 := by
    intro x hx
    have hle : |B₀ x| ≤ Real.exp (2 * ξu x) * ∫ v in I ∩ Iic x, |q₀ v| := by
      rw [hB₀, ← integral_const_mul, ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((H₀.q_int x hx).abs.const_mul _)
        ((ae_restrict_iff' (hmR x)).mpr (Eventually.of_forall fun v hv => ?_))
      rw [Real.norm_eq_abs, mul_one, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (by linarith [H₀.ξ_mono hv.1 hx hv.2])) (abs_nonneg _)
    have hee : Real.exp (-(2 * ξu x)) * Real.exp (2 * ξu x) = 1 := by
      rw [← Real.exp_add]; simp
    rw [hη₀', abs_mul, abs_neg, abs_of_pos hu, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc u * (Real.exp (-(2 * ξu x)) * |B₀ x|)
        ≤ u * (Real.exp (-(2 * ξu x)) * (Real.exp (2 * ξu x) * (𝔉 / u))) := by
          gcongr
          exact hle.trans (mul_le_mul_of_nonneg_left (hq₀int x hx) (Real.exp_pos _).le)
      _ = 𝔉 := by
          rw [show u * (Real.exp (-(2 * ξu x)) * (Real.exp (2 * ξu x) * (𝔉 / u))) =
            (Real.exp (-(2 * ξu x)) * Real.exp (2 * ξu x)) * (u * (𝔉 / u)) by ring, hee, one_mul]
          field_simp
  -- the homogeneous part `q = −ψ/u`
  have H : VolterraLG I (fun v => -ψ v / u) ξu (fun _ => u) :=
    ⟨hI, hIc, hne, hψc.neg.div_const u, fun x _ =>
      ((hψi.mono_set inter_subset_left).neg.div_const u), hξ, fun _ _ => hu.le⟩
  obtain ⟨y, P, hy, hP, hb⟩ := H.exists_forced_solution hη₀c hη₀M
  have hV : ∀ x ∈ I, volterraV I (fun v => -ψ v / u) x ≤ Ψ / u := by
    intro x hx
    have : volterraV I (fun v => -ψ v / u) x = (∫ v in I ∩ Iic x, |ψ v|) / u := by
      rw [volterraV, ← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [abs_div, abs_neg, abs_of_pos hu]
    rw [this]
    exact div_le_div_of_nonneg_right (setIntegral_mono_set hψi.abs
      (ae_of_all _ fun _ => abs_nonneg _) inter_subset_left.eventuallyLE) hu.le
  have h𝔉 : 0 ≤ 𝔉 := setIntegral_nonneg_of_ae (ae_of_all _ fun _ => abs_nonneg _)
  refine ⟨y, fun x => η₀' x - u * P x, fun x hx => ⟨hy x hx _ (hη₀d x hx), ?_⟩, fun x hx => ?_⟩
  · refine ((hη₀'d x hx).sub ((hP x hx).const_mul u)).congr_deriv ?_
    field_simp
    ring
  · have hVx := hV x hx
    have hE : Real.exp (volterraV I (fun v => -ψ v / u) x / 2) ≤ Real.exp (Ψ / (2 * u)) :=
      Real.exp_le_exp.mpr (by rw [show Ψ / (2 * u) = Ψ / u / 2 by ring]; linarith)
    have hE1 : 1 ≤ Real.exp (volterraV I (fun v => -ψ v / u) x / 2) :=
      Real.one_le_exp (div_nonneg (H.V_nonneg x) zero_le_two)
    have hMn : 0 ≤ 𝔉 / (2 * u) := by positivity
    obtain ⟨h1, h2⟩ := hb x hx
    constructor
    · have := abs_sub_abs_le_abs_sub (y x) (η₀ x)
      have h3 := hη₀M x hx
      calc |y x| ≤ 𝔉 / (2 * u) * (Real.exp (volterraV I (fun v => -ψ v / u) x / 2) - 1) +
            𝔉 / (2 * u) := by linarith
        _ = 𝔉 / (2 * u) * Real.exp (volterraV I (fun v => -ψ v / u) x / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hE hMn
    · have h4 := hη₀'b x hx
      calc |η₀' x - u * P x| ≤ |η₀' x| + |u * P x| := abs_sub _ _
        _ = |η₀' x| + u * |P x| := by rw [abs_mul u (P x), abs_of_pos hu]
        _ ≤ 𝔉 + u * (2 * (𝔉 / (2 * u)) *
            (Real.exp (volterraV I (fun v => -ψ v / u) x / 2) - 1)) := by gcongr
        _ = 𝔉 + 𝔉 * (Real.exp (volterraV I (fun v => -ψ v / u) x / 2) - 1) := by
            field_simp
        _ ≤ 𝔉 + 𝔉 * Real.exp (Ψ / (2 * u)) := by
            gcongr; linarith
        _ = _ := by ring

/-! ### 2.8.11 -/

/-- Hypotheses for 2.8.11: `ψ` continuous with `∫|ψ| < ∞` on `I` (`𝒱(A₁) < ∞`); coefficients
`A_s` (`s ≤ n`) with derivatives `A_s′`, and `A_s″` for `s < n`, satisfying `A₀ = 1` and the
derivative form `2A_{s+1}′ = −A_s″ + ψ A_s` of 2.8.13; `Aₙ′` continuous with `∫|Aₙ′| < ∞`
(`𝒱(Aₙ) < ∞`). -/
structure CaseIData (I : Set ℝ) (ψ : ℝ → ℝ) (A A' A'' : ℕ → ℝ → ℝ) (n : ℕ) : Prop where
  isOpen : IsOpen I
  ordConnected : I.OrdConnected
  nonempty : I.Nonempty
  ψ_cont : ContinuousOn ψ I
  ψ_int : IntegrableOn ψ I
  A_zero : ∀ x, A 0 x = 1
  A_deriv : ∀ s ≤ n, ∀ x ∈ I, HasDerivAt (A s) (A' s x) x
  A'_deriv : ∀ s < n, ∀ x ∈ I, HasDerivAt (A' s) (A'' s x) x
  recur : ∀ s < n, ∀ x ∈ I, 2 * A' (s + 1) x = -A'' s x + ψ x * A s x
  An_cont : ContinuousOn (A' n) I
  An_int : IntegrableOn (A' n) I

namespace CaseIData

variable {ψ : ℝ → ℝ} {A A' A'' : ℕ → ℝ → ℝ} {n : ℕ} (D : CaseIData I ψ A A' A'' n)
include D

theorem A'_zero {x : ℝ} (hx : x ∈ I) : A' 0 x = 0 := by
  have h := D.A_deriv 0 (Nat.zero_le n) x hx
  have hA : A 0 = fun _ => 1 := funext D.A_zero
  rw [hA] at h
  exact h.unique (hasDerivAt_const x 1)

/-- The residual of the truncated sum: `∑_{s<m} (A_s″ + 2u A_s′ − ψ A_s)/u^s = −2u^{1−m} A_m′`. -/
theorem sum_identity {u : ℝ} (hu : u ≠ 0) {x : ℝ} (hx : x ∈ I) :
    ∀ m ≤ n, ∑ s ∈ Finset.range m, (A'' s x + 2 * u * A' s x - ψ x * A s x) / u ^ s =
      -(2 * u / u ^ m) * A' m x := by
  intro m hm
  induction m with
  | zero => simp [D.A'_zero hx]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hr := D.recur m (by omega) x hx
    have hum : u ^ m ≠ 0 := pow_ne_zero m hu
    field_simp
    rw [pow_succ]
    linear_combination (u ^ m * u) * hr

/-- **DLMF 2.8.11**: for `n ≥ 1` there is `C` such that for every `u ≥ 1`, 2.8.10 has a solution
`W_{n,1}(u, ξ) = e^{uξ} (∑_{s<n} A_s(ξ)/u^s + η(u, ξ))` with `|η| ≤ C/uⁿ` and
`|∂η/∂ξ| ≤ C/u^{n−1}` on `I`. -/
theorem dlmf_2_8_11 (hn : 1 ≤ n) :
    ∃ C : ℝ, ∀ u : ℝ, 1 ≤ u → ∃ η : ℝ → ℝ,
      IsLGSolution I (fun _ => u ^ 2) ψ
        (fun x => Real.exp (u * x) * (∑ s ∈ Finset.range n, A s x / u ^ s + η x)) ∧
      ∀ x ∈ I, |η x| ≤ C / u ^ n ∧ |deriv η x| ≤ C / u ^ (n - 1) := by
  set 𝒜 := ∫ v in I, |A' n v|
  set Ψ := ∫ v in I, |ψ v|
  have h𝒜 : 0 ≤ 𝒜 := setIntegral_nonneg_of_ae (ae_of_all _ fun _ => abs_nonneg _)
  refine ⟨4 * 𝒜 * Real.exp (Ψ / 2), fun u hu1 => ?_⟩
  have hu : 0 < u := by linarith
  have hun : 0 < u ^ n := pow_pos hu n
  set F : ℝ → ℝ := fun x => 2 * u / u ^ n * A' n x with hF
  have hFc : ContinuousOn F I := continuousOn_const.mul D.An_cont
  have hFi : IntegrableOn F I := D.An_int.const_mul _
  obtain ⟨y, y', hyd, hyb⟩ := exists_forced_caseI D.isOpen D.ordConnected D.nonempty D.ψ_cont
    D.ψ_int hFc hFi hu
  have h𝔉 : ∫ v in I, |F v| = 2 * u / u ^ n * 𝒜 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * u / u ^ n)]
  rw [h𝔉] at hyb
  have hΨ : 0 ≤ Ψ := setIntegral_nonneg_of_ae (ae_of_all _ fun _ => abs_nonneg _)
  have hexp : Real.exp (Ψ / (2 * u)) ≤ Real.exp (Ψ / 2) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hΨ two_pos (by linarith))
  have hexp1 : 1 ≤ Real.exp (Ψ / 2) := Real.one_le_exp (by positivity)
  refine ⟨y, ?_, fun x hx => ⟨?_, ?_⟩⟩
  · -- the solution property
    set S0 : ℝ → ℝ := fun x => ∑ s ∈ Finset.range n, A s x / u ^ s
    set S1 : ℝ → ℝ := fun x => ∑ s ∈ Finset.range n, A' s x / u ^ s
    set S2 : ℝ → ℝ := fun x => ∑ s ∈ Finset.range n, A'' s x / u ^ s
    have hS0 : ∀ x ∈ I, HasDerivAt S0 (S1 x) x := fun x hx => by
      have := HasDerivAt.fun_sum (u := Finset.range n) (A := fun s y => A s y / u ^ s)
        (A' := fun s => A' s x / u ^ s) fun s hs =>
          (D.A_deriv s (Finset.mem_range.mp hs).le x hx).div_const _
      simpa using this
    have hS1 : ∀ x ∈ I, HasDerivAt S1 (S2 x) x := fun x hx => by
      have := HasDerivAt.fun_sum (u := Finset.range n) (A := fun s y => A' s y / u ^ s)
        (A' := fun s => A'' s x / u ^ s) fun s hs =>
          (D.A'_deriv s (Finset.mem_range.mp hs) x hx).div_const _
      simpa using this
    have hfg : ContinuousOn (fun x => u ^ 2 + ψ x) I := continuousOn_const.add D.ψ_cont
    refine IsLGSolution.of_hasDerivAt D.isOpen hfg
      (w' := fun x => Real.exp (u * x) * (u * (S0 x + y x) + (S1 x + y' x)))
      (fun x hx => ?_) (fun x hx => ?_)
    · have hE : HasDerivAt (fun x => Real.exp (u * x)) (Real.exp (u * x) * u) x :=
        (((hasDerivAt_id x).const_mul u).congr_deriv (mul_one u)).exp
      refine (hE.mul ((hS0 x hx).add (hyd x hx).1)).congr_deriv ?_
      simp only [Pi.add_apply]
      ring
    · have hE : HasDerivAt (fun x => Real.exp (u * x)) (Real.exp (u * x) * u) x :=
        (((hasDerivAt_id x).const_mul u).congr_deriv (mul_one u)).exp
      have hd := hE.mul ((((hS0 x hx).add (hyd x hx).1).const_mul u).add
        ((hS1 x hx).add (hyd x hx).2))
      refine hd.congr_deriv ?_
      have key := D.sum_identity hu.ne' hx n le_rfl
      have e : S2 x + 2 * u * S1 x - ψ x * S0 x = -(2 * u / u ^ n) * A' n x := by
        rw [← key]
        simp only [S0, S1, S2, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      simp only [hF, Pi.add_apply] at e ⊢
      linear_combination Real.exp (u * x) * e
  · calc |y x| ≤ 2 * u / u ^ n * 𝒜 / (2 * u) * Real.exp (Ψ / (2 * u)) := (hyb x hx).1
      _ ≤ 𝒜 / u ^ n * Real.exp (Ψ / 2) := by
          rw [show 2 * u / u ^ n * 𝒜 / (2 * u) = 𝒜 / u ^ n by field_simp]
          gcongr
      _ ≤ 4 * 𝒜 * Real.exp (Ψ / 2) / u ^ n := by
          rw [div_mul_eq_mul_div]
          gcongr
          nlinarith
  · rw [(hyd x hx).1.deriv]
    have hpow : u ^ n = u * u ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    calc |y' x| ≤ 2 * u / u ^ n * 𝒜 * (1 + Real.exp (Ψ / (2 * u))) := (hyb x hx).2
      _ ≤ 2 * u / u ^ n * 𝒜 * (2 * Real.exp (Ψ / 2)) := by gcongr; linarith
      _ = 4 * 𝒜 * Real.exp (Ψ / 2) / u ^ (n - 1) := by
          rw [hpow]; field_simp; ring

/-! ### 2.8.12: reflection -/

/-- The reflected data `ψ(−ξ)`, `(−1)^s A_s(−ξ)` on `−I` (reference point `α₂ ↦ −α₂`). -/
theorem reflect : CaseIData (Neg.neg ⁻¹' I) (fun x => ψ (-x)) (fun s x => (-1) ^ s * A s (-x))
    (fun s x => (-1) ^ (s + 1) * A' s (-x)) (fun s x => (-1) ^ s * A'' s (-x)) n where
  isOpen := D.isOpen.preimage continuous_neg
  ordConnected := ⟨fun x hx y hy z hz => D.ordConnected.out hy hx ⟨by
    simp only [mem_Icc] at hz; linarith, by simp only [mem_Icc] at hz; linarith⟩⟩
  nonempty := by
    obtain ⟨x, hx⟩ := D.nonempty
    exact ⟨-x, by simpa using hx⟩
  ψ_cont := D.ψ_cont.comp continuous_neg.continuousOn fun x hx => hx
  ψ_int := by simpa using (integrableOn_comp_neg_iff I ψ).mpr D.ψ_int
  A_zero x := by simp [D.A_zero]
  A_deriv s hs x hx := by
    have := ((D.A_deriv s hs (-x) hx).comp x (hasDerivAt_neg x)).const_mul ((-1 : ℝ) ^ s)
    convert this using 1 <;> first | rfl | ring
  A'_deriv s hs x hx := by
    have := ((D.A'_deriv s hs (-x) hx).comp x (hasDerivAt_neg x)).const_mul
      ((-1 : ℝ) ^ (s + 1))
    convert this using 1 <;> first | rfl | ring
  recur s hs x hx := by
    have := D.recur s hs (-x) hx
    linear_combination (-1 : ℝ) ^ s * this
  An_cont := continuousOn_const.mul (D.An_cont.comp continuous_neg.continuousOn fun x hx => hx)
  An_int := by
    have := (integrableOn_comp_neg_iff I (A' n)).mpr D.An_int
    exact this.const_mul _

/-- **DLMF 2.8.12**: for `n ≥ 1` there is `C` such that for every `u ≥ 1`, 2.8.10 has a solution
`W_{n,2}(u, ξ) = e^{−uξ} (∑_{s<n} (−1)^s A_s(ξ)/u^s + η(u, ξ))` with `|η| ≤ C/uⁿ` and
`|∂η/∂ξ| ≤ C/u^{n−1}` on `I` (reference point the upper end `α₂`). -/
theorem dlmf_2_8_12 (hn : 1 ≤ n) :
    ∃ C : ℝ, ∀ u : ℝ, 1 ≤ u → ∃ η : ℝ → ℝ,
      IsLGSolution I (fun _ => u ^ 2) ψ (fun x => Real.exp (-(u * x)) *
        (∑ s ∈ Finset.range n, (-1) ^ s * A s x / u ^ s + η x)) ∧
      ∀ x ∈ I, |η x| ≤ C / u ^ n ∧ |deriv η x| ≤ C / u ^ (n - 1) := by
  obtain ⟨C, hC⟩ := D.reflect.dlmf_2_8_11 hn
  refine ⟨C, fun u hu => ?_⟩
  obtain ⟨η, ⟨hw2, hwode⟩, hb⟩ := hC u hu
  refine ⟨fun x => η (-x), ⟨?_, fun x hx => ?_⟩, fun x hx => ?_⟩
  · have := hw2.comp contDiff_neg.contDiffOn (fun x hx => by simpa using hx)
    refine this.congr fun x _ => ?_
    simp
  · have e : (fun x => Real.exp (-(u * x)) *
        (∑ s ∈ Finset.range n, (-1) ^ s * A s x / u ^ s + η (-x))) =
        fun y => Real.exp (u * -y) *
          (∑ s ∈ Finset.range n, (-1) ^ s * A s (-(-y)) / u ^ s + η (-y)) := by
      funext x; simp
    have key := deriv_deriv_comp_neg (fun y => Real.exp (u * y) *
      (∑ s ∈ Finset.range n, (-1) ^ s * A s (-y) / u ^ s + η y)) x
    rw [e, key, hwode (-x) (by simpa using hx)]
    simp
  · obtain ⟨h1, h2⟩ := hb (-x) (by simpa using hx)
    refine ⟨h1, ?_⟩
    rw [deriv_comp_neg η x, abs_neg]
    exact h2

end CaseIData

/-! ### 2.8.13: construction of the coefficients -/

/-- **DLMF 2.8.13**: `A₀ = 1`, `A_{s+1}(ξ) = −½ A_s′(ξ) + ½ ∫_{x₀}^{ξ} ψ A_s + c_s` (the
constants of integration `c_s` arbitrary). -/
noncomputable def dlmfA (ψ : ℝ → ℝ) (x₀ : ℝ) (c : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | s + 1 => fun x => -(1 / 2) * deriv (dlmfA ψ x₀ c s) x +
      1 / 2 * (∫ t in x₀..x, ψ t * dlmfA ψ x₀ c s t) + c s

/-- **DLMF 2.8.13**: for `ψ` of class `C^∞` on the open interval `I ∋ x₀`, every `A_s` is `C^∞` and
`2 A_{s+1}′ = −A_s″ + ψ A_s`. -/
theorem dlmf_2_8_13 (hI : IsOpen I) (hIc : I.OrdConnected) {ψ : ℝ → ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ I)
    (hψ : ContDiffOn ℝ ∞ ψ I) (c : ℕ → ℝ) (s : ℕ) :
    ContDiffOn ℝ ∞ (dlmfA ψ x₀ c s) I ∧ ∀ x ∈ I,
      2 * deriv (dlmfA ψ x₀ c (s + 1)) x =
        -deriv (deriv (dlmfA ψ x₀ c s)) x + ψ x * dlmfA ψ x₀ c s x := by
  have hsm : ∀ s, ContDiffOn ℝ ∞ (dlmfA ψ x₀ c s) I := by
    intro s
    induction s with
    | zero => exact contDiffOn_const
    | succ s ih =>
      have hd : ContDiffOn ℝ ∞ (deriv (dlmfA ψ x₀ c s)) I :=
        ih.deriv_of_isOpen hI (by simp)
      have hprod : ContDiffOn ℝ ∞ (fun t => ψ t * dlmfA ψ x₀ c s t) I := hψ.mul ih
      have hG : ContDiffOn ℝ ∞ (fun x => ∫ t in x₀..x, ψ t * dlmfA ψ x₀ c s t) I := by
        rw [contDiffOn_infty_iff_deriv_of_isOpen hI]
        have hGd : ∀ x ∈ I, HasDerivAt (fun x => ∫ t in x₀..x, ψ t * dlmfA ψ x₀ c s t)
            (ψ x * dlmfA ψ x₀ c s x) x := fun x hx =>
          intervalIntegral.integral_hasDerivAt_right
            ((hprod.continuousOn.mono (hIc.uIcc_subset hx₀ hx)).intervalIntegrable)
            (hprod.continuousOn.stronglyMeasurableAtFilter hI x hx)
            (hprod.continuousOn.continuousAt (hI.mem_nhds hx))
        exact ⟨fun x hx => (hGd x hx).differentiableAt.differentiableWithinAt,
          hprod.congr fun x hx => (hGd x hx).deriv⟩
      exact ((contDiffOn_const.mul hd).add (contDiffOn_const.mul hG)).add contDiffOn_const
  refine ⟨hsm s, fun x hx => ?_⟩
  have hd : ContDiffOn ℝ ∞ (deriv (dlmfA ψ x₀ c s)) I := (hsm s).deriv_of_isOpen hI (by simp)
  have h1 : HasDerivAt (deriv (dlmfA ψ x₀ c s)) (deriv (deriv (dlmfA ψ x₀ c s)) x) x :=
    ((hd.differentiableOn (by simp)).differentiableAt (hI.mem_nhds hx)).hasDerivAt
  have hprod : ContinuousOn (fun t => ψ t * dlmfA ψ x₀ c s t) I :=
    hψ.continuousOn.mul (hsm s).continuousOn
  have h2 : HasDerivAt (fun x => ∫ t in x₀..x, ψ t * dlmfA ψ x₀ c s t)
      (ψ x * dlmfA ψ x₀ c s x) x :=
    intervalIntegral.integral_hasDerivAt_right
      ((hprod.mono (hIc.uIcc_subset hx₀ hx)).intervalIntegrable)
      (hprod.stronglyMeasurableAtFilter hI x hx) (hprod.continuousAt (hI.mem_nhds hx))
  have h3 : HasDerivAt (fun x => -(1 / 2) * deriv (dlmfA ψ x₀ c s) x +
      1 / 2 * (∫ t in x₀..x, ψ t * dlmfA ψ x₀ c s t) + c s)
      (-(1 / 2) * deriv (deriv (dlmfA ψ x₀ c s)) x + 1 / 2 * (ψ x * dlmfA ψ x₀ c s x)) x :=
    ((h1.const_mul (-(1 / 2))).add (h2.const_mul (1 / 2))).add_const (c s)
  rw [show dlmfA ψ x₀ c (s + 1) = fun x => -(1 / 2) * deriv (dlmfA ψ x₀ c s) x +
    1 / 2 * (∫ t in x₀..x, ψ t * dlmfA ψ x₀ c s t) + c s from rfl, h3.deriv]
  ring

/-- The coefficients of 2.8.13 satisfy the hypotheses of 2.8.11–2.8.12 once `∫|ψ| < ∞` and
`∫|Aₙ′| < ∞`. -/
theorem CaseIData.of_dlmfA (hI : IsOpen I) (hIc : I.OrdConnected) {ψ : ℝ → ℝ} {x₀ : ℝ}
    (hx₀ : x₀ ∈ I) (hψ : ContDiffOn ℝ ∞ ψ I) (c : ℕ → ℝ) (n : ℕ) (hψi : IntegrableOn ψ I)
    (hAn : IntegrableOn (deriv (dlmfA ψ x₀ c n)) I) :
    CaseIData I ψ (dlmfA ψ x₀ c) (fun s => deriv (dlmfA ψ x₀ c s))
      (fun s => deriv (deriv (dlmfA ψ x₀ c s))) n := by
  have hs : ∀ s, ContDiffOn ℝ ∞ (dlmfA ψ x₀ c s) I := fun s =>
    (dlmf_2_8_13 hI hIc hx₀ hψ c s).1
  have hd : ∀ s, ContDiffOn ℝ ∞ (deriv (dlmfA ψ x₀ c s)) I := fun s =>
    (hs s).deriv_of_isOpen hI (m := ∞) (by simp)
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  exact ⟨hI, hIc, ⟨x₀, hx₀⟩, hψ.continuousOn, hψi, fun _ => rfl,
    fun s _ x hx => (((hs s).differentiableOn hne).differentiableAt (hI.mem_nhds hx)).hasDerivAt,
    fun s _ x hx => (((hd s).differentiableOn hne).differentiableAt (hI.mem_nhds hx)).hasDerivAt,
    fun s _ x hx => (dlmf_2_8_13 hI hIc hx₀ hψ c s).2 x hx, (hd n).continuousOn, hAn⟩

end Azurite.DLMF
