/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1Expansion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# DLMF §2.1(iii): functions with a prescribed asymptotic expansion

DLMF: for any coefficients `a₀, a₁, …` and suitably restricted `𝐗` there is an infinity of
analytic functions with the expansion 2.1.14 (resp. 2.1.16); for 2.1.14, `𝐗` can be the
positive real axis or any unbounded sector of finite angle. The construction (Ritt) is
`f(z) = ∑ₛ aₛz^{−s}(1 − exp(−βₛ(z e^{−iθ})^{1/4}))` with `βₛ = 1/((|aₛ| + 1)2ˢ)`, analytic in
the slit sector `|ph(z e^{−iθ})| < π` for `|z| > 1`; adding multiples of the null function
`exp(−(z e^{−iθ})^{1/4})` gives infinitely many.

* `isAsympExpansion_borelRittFn`, `isAsympExpansion_brNull`, `differentiableOn_borelRittFn`.
* `dlmf_2_1_iii_exists_sector` (sectors `|ph(z e^{−iθ})| < ω ≤ π`), `dlmf_2_1_iii_exists_real`
  (positive real axis, real analytic on `(1, ∞)`), `dlmf_2_1_iii_exists_at` (2.1.16, sectors with
  vertex `c`).
-/

open Set Filter Topology Asymptotics Complex

namespace Azurite.DLMF

/-! ### The slit sector and `z^{1/4}` -/

theorem mem_sectorDLMF_pi {θ : ℝ} {z : ℂ} :
    z ∈ sectorDLMF θ Real.pi ↔ z * exp (-(θ * I)) ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg, sectorDLMF, mem_ofPred_eq]
  have hne : z * exp (-(θ * I)) ≠ 0 ↔ z ≠ 0 := by simp [exp_ne_zero]
  rw [hne]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨fun he => by rw [he, abs_of_pos Real.pi_pos] at h; exact lt_irrefl _ h, h0⟩
  · rintro ⟨h, h0⟩
    refine ⟨h0, abs_lt.mpr ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) h⟩⟩

theorem isOpen_sectorDLMF_pi (θ : ℝ) : IsOpen (sectorDLMF θ Real.pi) := by
  have : sectorDLMF θ Real.pi = (fun z => z * exp (-(θ * I))) ⁻¹' slitPlane := by
    ext z; exact mem_sectorDLMF_pi
  rw [this]
  exact isOpen_slitPlane.preimage (continuous_id.mul continuous_const)

theorem sectorDLMF_subset_pi {θ ω : ℝ} (hω : ω ≤ Real.pi) :
    sectorDLMF θ ω ⊆ sectorDLMF θ Real.pi := fun _ hz => ⟨hz.1, hz.2.trans_le hω⟩

theorem norm_mul_exp_neg_mul_I (z : ℂ) (θ : ℝ) : ‖z * exp (-(θ * I))‖ = ‖z‖ := by
  rw [norm_mul, show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I, mul_one]

/-- `E(z) = (z e^{−iθ})^{1/4}` (principal branch). -/
noncomputable def quarterPow (θ : ℝ) (z : ℂ) : ℂ := (z * exp (-(θ * I))) ^ (1 / 4 : ℂ)

theorem norm_quarterPow (θ : ℝ) (z : ℂ) : ‖quarterPow θ z‖ = ‖z‖ ^ (1 / 4 : ℝ) := by
  rw [quarterPow, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, norm_cpow_real,
    norm_mul_exp_neg_mul_I]

theorem re_quarterPow_ge (θ : ℝ) (z : ℂ) : ‖z‖ ^ (1 / 4 : ℝ) / 2 ≤ (quarterPow θ z).re := by
  set w := z * exp (-(θ * I))
  have hw : ‖w‖ = ‖z‖ := norm_mul_exp_neg_mul_I z θ
  rcases eq_or_ne w 0 with h0 | h0
  · have : z = 0 := by simpa [w, exp_ne_zero] using h0
    subst this
    simp [quarterPow]
  rw [quarterPow, cpow_def_of_ne_zero h0, exp_re]
  have hre : (log w * (1 / 4)).re = Real.log ‖w‖ / 4 := by simp [log_re]; ring
  have him : (log w * (1 / 4)).im = arg w / 4 := by simp [log_im]; ring
  rw [hre, him, ← hw]
  have hsq : Real.exp (Real.log ‖w‖ / 4) = ‖w‖ ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr h0)]; ring_nf
  rw [hsq]
  have hcos : 1 / 2 ≤ Real.cos (arg w / 4) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ?_
    rw [abs_div, show |(4 : ℝ)| = 4 by norm_num]
    linarith [abs_arg_le_pi w, Real.pi_pos]
  nlinarith [Real.rpow_nonneg (norm_nonneg w) (1 / 4 : ℝ)]

theorem differentiableAt_quarterPow {θ : ℝ} {z : ℂ} (hz : z ∈ sectorDLMF θ Real.pi) :
    DifferentiableAt ℂ (quarterPow θ) z := by
  show DifferentiableAt ℂ (fun z => (z * exp (-(θ * I))) ^ (1 / 4 : ℂ)) z
  exact DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _) (mem_sectorDLMF_pi.mp hz)

/-- `|1 − e^{−v}| ≤ |v|` for `ℜv ≥ 0`. -/
theorem norm_one_sub_exp_neg_le {v : ℂ} (hv : 0 ≤ v.re) : ‖1 - exp (-v)‖ ≤ ‖v‖ := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t : ℝ => exp (-(t * v)))
    (f' := fun t => exp (-(t * v)) * -v) (C := ‖v‖)
    (fun t _ => by
      have h1 : HasDerivAt (fun t : ℝ => -((t : ℂ) * v)) (-v) t := by
        have := ((hasDerivAt_id t).ofReal_comp.mul_const v).fun_neg
        simpa using this
      exact h1.cexp.hasDerivWithinAt)
    (fun t ht => by
      rw [norm_mul, norm_neg, norm_exp, mul_comm]
      have : (-(↑t * v)).re ≤ 0 := by simp; nlinarith [ht.1]
      calc ‖v‖ * Real.exp (-(↑t * v)).re ≤ ‖v‖ * 1 := by
            gcongr; exact Real.exp_le_one_iff.mpr this
        _ = ‖v‖ := mul_one _)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, neg_zero, exp_zero] at h
  rwa [norm_sub_rev] at h

theorem norm_one_sub_exp_neg_le_two {v : ℂ} (hv : 0 ≤ v.re) : ‖1 - exp (-v)‖ ≤ 2 := by
  calc ‖1 - exp (-v)‖ ≤ ‖(1 : ℂ)‖ + ‖exp (-v)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
      rw [norm_one, norm_exp]; gcongr; exact Real.exp_le_one_iff.mpr (by simp [hv])
    _ = 2 := by norm_num

/-! ### The construction -/

section Construction

variable (θ : ℝ) (a : ℕ → ℂ)

/-- The damping constants `βₛ = 1/((|aₛ| + 1) 2ˢ)`. -/
noncomputable def brBeta (s : ℕ) : ℝ := 1 / ((‖a s‖ + 1) * 2 ^ s)

/-- The terms `aₛ z^{−s}(1 − exp(−βₛ E(z)))`. -/
noncomputable def brTerm (s : ℕ) (z : ℂ) : ℂ :=
  a s * z⁻¹ ^ s * (1 - exp (-((brBeta a s : ℂ) * quarterPow θ z)))

/-- Ritt's function `∑ₛ aₛ z^{−s}(1 − exp(−βₛ E(z)))`. -/
noncomputable def borelRittFn (z : ℂ) : ℂ := ∑' s, brTerm θ a s z

/-- A function with the null expansion: `exp(−E(z))`. -/
noncomputable def brNull (z : ℂ) : ℂ := exp (-quarterPow θ z)

variable {θ a}

theorem brBeta_pos (s : ℕ) : 0 < brBeta a s := by unfold brBeta; positivity

theorem norm_mul_brBeta_le (s : ℕ) : ‖a s‖ * brBeta a s ≤ (1 / 2) ^ s := by
  unfold brBeta
  rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [norm_nonneg (a s), pow_pos (two_pos : (0 : ℝ) < 2) s]

theorem re_brBeta_mul_nonneg (s : ℕ) (z : ℂ) : 0 ≤ ((brBeta a s : ℂ) * quarterPow θ z).re := by
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (brBeta_pos s).le ((by positivity : (0 : ℝ) ≤ ‖z‖ ^ (1 / 4 : ℝ) / 2).trans
    (re_quarterPow_ge θ z))

theorem norm_brTerm_le (s : ℕ) (z : ℂ) :
    ‖brTerm θ a s z‖ ≤ (1 / 2) ^ s * ‖z‖ ^ (1 / 4 : ℝ) * ‖z‖⁻¹ ^ s := by
  unfold brTerm
  rw [norm_mul, norm_mul, norm_pow, norm_inv]
  have h := norm_one_sub_exp_neg_le (re_brBeta_mul_nonneg (a := a) (θ := θ) s z)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (brBeta_pos s).le, norm_quarterPow] at h
  calc ‖a s‖ * ‖z‖⁻¹ ^ s * ‖1 - exp (-((brBeta a s : ℂ) * quarterPow θ z))‖
      ≤ ‖a s‖ * ‖z‖⁻¹ ^ s * (brBeta a s * ‖z‖ ^ (1 / 4 : ℝ)) := by gcongr
    _ = (‖a s‖ * brBeta a s) * ‖z‖ ^ (1 / 4 : ℝ) * ‖z‖⁻¹ ^ s := by ring
    _ ≤ (1 / 2) ^ s * ‖z‖ ^ (1 / 4 : ℝ) * ‖z‖⁻¹ ^ s := by gcongr; exact norm_mul_brBeta_le s

theorem norm_brTerm_le_two (s : ℕ) (z : ℂ) : ‖brTerm θ a s z‖ ≤ 2 * ‖a s‖ * ‖z‖⁻¹ ^ s := by
  unfold brTerm
  rw [norm_mul, norm_mul, norm_pow, norm_inv]
  have h := norm_one_sub_exp_neg_le_two (re_brBeta_mul_nonneg (a := a) (θ := θ) s z)
  calc ‖a s‖ * ‖z‖⁻¹ ^ s * ‖1 - exp (-((brBeta a s : ℂ) * quarterPow θ z))‖
      ≤ ‖a s‖ * ‖z‖⁻¹ ^ s * 2 := by gcongr
    _ = 2 * ‖a s‖ * ‖z‖⁻¹ ^ s := by ring

theorem inv_pow_le_one {z : ℂ} (hz : 1 ≤ ‖z‖) (s : ℕ) : ‖z‖⁻¹ ^ s ≤ 1 :=
  pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hz)

theorem summable_brTerm {z : ℂ} (hz : 1 ≤ ‖z‖) : Summable fun s => brTerm θ a s z :=
  Summable.of_norm_bounded (g := fun s => (1 / 2) ^ s * ‖z‖ ^ (1 / 4 : ℝ))
    (summable_geometric_two.mul_right _) fun s =>
      (norm_brTerm_le s z).trans (by
        have := inv_pow_le_one hz s
        have : 0 ≤ (1 / 2 : ℝ) ^ s * ‖z‖ ^ (1 / 4 : ℝ) := by positivity
        nlinarith)

theorem differentiableAt_brTerm (s : ℕ) {z : ℂ} (hz : z ∈ sectorDLMF θ Real.pi) :
    DifferentiableAt ℂ (brTerm θ a s) z := by
  have hz0 : z ≠ 0 := hz.1
  unfold brTerm
  have hE := differentiableAt_quarterPow hz
  fun_prop (disch := assumption)

theorem differentiableOn_borelRittFn :
    DifferentiableOn ℂ (borelRittFn θ a) (sectorDLMF θ Real.pi ∩ {z | 1 < ‖z‖}) := by
  intro z₀ hz₀
  set V := sectorDLMF θ Real.pi ∩ {z | 1 < ‖z‖} ∩ Metric.ball 0 (‖z₀‖ + 1)
  have hVo : IsOpen V := ((isOpen_sectorDLMF_pi θ).inter
    (isOpen_lt continuous_const continuous_norm)).inter Metric.isOpen_ball
  have hz₀V : z₀ ∈ V := ⟨hz₀, by simp⟩
  have hd : DifferentiableOn ℂ (fun w => ∑' s, brTerm θ a s w) V := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun s => (1 / 2) ^ s * (‖z₀‖ + 1) ^ (1 / 4 : ℝ))
      (summable_geometric_two.mul_right _)
      (fun s w hw => (differentiableAt_brTerm s hw.1.1).differentiableWithinAt) hVo
      fun s w hw => (norm_brTerm_le s w).trans ?_
    have hw1 : 1 ≤ ‖w‖ := hw.1.2.le
    have hwR : ‖w‖ < ‖z₀‖ + 1 := by simpa using hw.2
    have h1 := inv_pow_le_one hw1 s
    have h2 : ‖w‖ ^ (1 / 4 : ℝ) ≤ (‖z₀‖ + 1) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) hwR.le (by norm_num)
    have h3 : 0 ≤ (1 / 2 : ℝ) ^ s * ‖w‖ ^ (1 / 4 : ℝ) := by positivity
    calc (1 / 2 : ℝ) ^ s * ‖w‖ ^ (1 / 4 : ℝ) * ‖w‖⁻¹ ^ s
        ≤ (1 / 2) ^ s * ‖w‖ ^ (1 / 4 : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 h3
      _ ≤ (1 / 2) ^ s * (‖z₀‖ + 1) ^ (1 / 4 : ℝ) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
  exact (hd.differentiableAt (hVo.mem_nhds hz₀V)).differentiableWithinAt

theorem differentiableOn_brNull : DifferentiableOn ℂ (brNull θ) (sectorDLMF θ Real.pi) :=
  fun _ hz => ((differentiableAt_quarterPow hz).neg.cexp).differentiableWithinAt

end Construction

/-! ### The expansion -/

theorem isBigO_inv_pow_of_tendsto {L : Filter ℂ} (hL : ∀ᶠ z in L, z ≠ 0) {g : ℂ → ℂ} {n : ℕ}
    (h : Tendsto (fun z => ‖z‖ ^ n * ‖g z‖) L (𝓝 0)) : g =O[L] fun z => z⁻¹ ^ n := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [h.eventually (gt_mem_nhds one_pos), hL] with z hz hz0
  have hp : 0 < ‖z‖ ^ n := pow_pos (norm_pos_iff.mpr hz0) n
  rw [one_mul, norm_pow, norm_inv, inv_pow, ← one_div, le_div_iff₀ hp, mul_comm]
  exact hz.le

theorem tendsto_norm_pow_mul_exp_quarter {S : Set ℂ} (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun z : ℂ => ‖z‖ ^ k * Real.exp (-(c * ‖z‖ ^ (1 / 4 : ℝ))))
      (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝 0) := by
  have ht : Tendsto (fun z : ℂ => ‖z‖ ^ (1 / 4 : ℝ)) (Bornology.cobounded ℂ ⊓ 𝓟 S) atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
  refine ((tendsto_pow_mul_exp_neg_mul (4 * k) hc).comp ht).congr fun z => ?_
  simp only [Function.comp_apply]
  congr 1
  rw [pow_mul, ← Real.rpow_natCast (‖z‖ ^ (1 / 4 : ℝ)) 4,
    ← Real.rpow_mul (norm_nonneg _)]
  norm_num

section Expansion

variable {θ : ℝ} {a : ℕ → ℂ}

theorem norm_exp_neg_mul_quarterPow_le (b : ℝ) (hb : 0 ≤ b) (z : ℂ) :
    ‖exp (-((b : ℂ) * quarterPow θ z))‖ ≤ Real.exp (-(b / 2 * ‖z‖ ^ (1 / 4 : ℝ))) := by
  rw [norm_exp, Complex.neg_re, Complex.re_ofReal_mul]
  refine Real.exp_le_exp.mpr ?_
  have := re_quarterPow_ge θ z
  nlinarith

/-- **Ritt's function has the prescribed expansion** in the slit sector `|ph(z e^{−iθ})| < π`. -/
theorem isAsympExpansion_borelRittFn :
    IsAsympExpansionDLMF (sectorDLMF θ Real.pi) (borelRittFn θ a) a := by
  rw [isAsympExpansionDLMF_iff]
  intro n
  set L := Bornology.cobounded ℂ ⊓ 𝓟 (sectorDLMF θ Real.pi)
  have hev : ∀ᶠ z in L, 1 ≤ ‖z‖ :=
    (tendsto_norm_cobounded_atTop.mono_left inf_le_left).eventually_ge_atTop 1
  have hne : ∀ᶠ z in L, z ≠ 0 := eventually_ne_zero_atInf _
  -- the finitely many damped terms
  have h1 : (fun z => ∑ s ∈ Finset.range n, a s * z⁻¹ ^ s *
      exp (-((brBeta a s : ℂ) * quarterPow θ z))) =O[L] fun z => z⁻¹ ^ n := by
    refine IsBigO.fun_sum fun s _ => isBigO_inv_pow_of_tendsto hne ?_
    have hd := (tendsto_norm_pow_mul_exp_quarter (S := sectorDLMF θ Real.pi) n
      (half_pos (brBeta_pos (a := a) s))).const_mul ‖a s‖
    rw [mul_zero] at hd
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hd
    filter_upwards [hev] with z hz
    rw [norm_mul, norm_mul, norm_pow, norm_inv]
    have h2 := norm_exp_neg_mul_quarterPow_le (θ := θ) _ (brBeta_pos (a := a) s).le z
    have h3 := inv_pow_le_one hz s
    have : 0 ≤ ‖z‖ ^ n := by positivity
    calc ‖z‖ ^ n * (‖a s‖ * ‖z‖⁻¹ ^ s * ‖exp (-((brBeta a s : ℂ) * quarterPow θ z))‖)
        ≤ ‖z‖ ^ n * (‖a s‖ * 1 * Real.exp (-(brBeta a s / 2 * ‖z‖ ^ (1 / 4 : ℝ)))) := by gcongr
      _ = ‖a s‖ * (‖z‖ ^ n * Real.exp (-(brBeta a s / 2 * ‖z‖ ^ (1 / 4 : ℝ)))) := by ring
  -- the tail
  have h2 : (fun z => ∑' s, brTerm θ a (s + n) z) =O[L] fun z => z⁻¹ ^ n := by
    refine IsBigO.of_bound (2 * ‖a n‖ + 2) ?_
    filter_upwards [hev] with z hz
    have hs := summable_brTerm (θ := θ) (a := a) hz
    have hs' : Summable fun s => brTerm θ a (s + n) z := (summable_nat_add_iff n).mpr hs
    rw [hs'.tsum_eq_zero_add, zero_add, norm_pow, norm_inv]
    have hnz : 0 < ‖z‖ := by linarith
    have hq : ‖z‖ ^ (1 / 4 : ℝ) * ‖z‖⁻¹ ≤ 1 := by
      have := Real.rpow_le_rpow_of_exponent_le hz (show (1 / 4 : ℝ) ≤ 1 by norm_num)
      rw [Real.rpow_one] at this
      rw [mul_inv_le_iff₀ hnz, one_mul]; exact this
    have htail : ‖∑' s, brTerm θ a (s + 1 + n) z‖ ≤ 2 * ‖z‖⁻¹ ^ n := by
      have hb : ∀ s, ‖brTerm θ a (s + 1 + n) z‖ ≤
          (‖z‖ ^ (1 / 4 : ℝ) * ‖z‖⁻¹ ^ (n + 1)) * (1 / 2) ^ s := fun s => by
        refine (norm_brTerm_le _ z).trans ?_
        have e1 : (1 / 2 : ℝ) ^ (s + 1 + n) ≤ (1 / 2) ^ s :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have e2 : ‖z‖⁻¹ ^ (s + 1 + n) ≤ ‖z‖⁻¹ ^ (n + 1) := by
          rw [show s + 1 + n = s + (n + 1) by ring, pow_add]
          exact mul_le_of_le_one_left (by positivity) (inv_pow_le_one hz s)
        calc (1 / 2 : ℝ) ^ (s + 1 + n) * ‖z‖ ^ (1 / 4 : ℝ) * ‖z‖⁻¹ ^ (s + 1 + n)
            ≤ (1 / 2) ^ s * ‖z‖ ^ (1 / 4 : ℝ) * ‖z‖⁻¹ ^ (n + 1) := by gcongr
          _ = _ := by ring
      have := tsum_of_norm_bounded (hasSum_geometric_two.mul_left
        (‖z‖ ^ (1 / 4 : ℝ) * ‖z‖⁻¹ ^ (n + 1))) hb
      refine this.trans ?_
      rw [pow_succ, ← mul_assoc, mul_comm (‖z‖ ^ (1 / 4 : ℝ)), mul_assoc]
      have : 0 ≤ ‖z‖⁻¹ ^ n := by positivity
      nlinarith
    calc ‖brTerm θ a n z + ∑' s, brTerm θ a (s + 1 + n) z‖
        ≤ ‖brTerm θ a n z‖ + ‖∑' s, brTerm θ a (s + 1 + n) z‖ := norm_add_le _ _
      _ ≤ 2 * ‖a n‖ * ‖z‖⁻¹ ^ n + 2 * ‖z‖⁻¹ ^ n := add_le_add (norm_brTerm_le_two n z) htail
      _ = (2 * ‖a n‖ + 2) * ‖z‖⁻¹ ^ n := by ring
  refine (h1.neg_left.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hev] with z hz
  have hs := summable_brTerm (θ := θ) (a := a) hz
  simp only [borelRittFn, ← hs.sum_add_tsum_nat_add n, eval_trunc_eq_sum,
    PowerSeries.coeff_mk]
  rw [show ∀ x y w : ℂ, -x + y = w + y - (w + x) by intros; ring]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold brTerm; ring

/-- `exp(−E(z))` has the null expansion in the slit sector. -/
theorem isAsympExpansion_brNull : IsAsympExpansionDLMF (sectorDLMF θ Real.pi) (brNull θ) 0 := by
  refine isAsympExpansionDLMF_zero_of_tendsto fun n => ?_
  refine squeeze_zero_norm' (Eventually.of_forall fun z => ?_)
    (tendsto_norm_pow_mul_exp_quarter (S := sectorDLMF θ Real.pi) n (c := 1 / 2) (by norm_num))
  rw [norm_mul, norm_pow, brNull]
  have := norm_exp_neg_mul_quarterPow_le (θ := θ) 1 zero_le_one z
  simp only [Complex.ofReal_one, one_mul] at this
  gcongr

end Expansion

theorem IsAsympExpansionDLMF.mono {𝕜 : Type*} [NormedField 𝕜] {X Y : Set 𝕜} {f : 𝕜 → 𝕜}
    {a : ℕ → 𝕜} (h : IsAsympExpansionDLMF Y f a) (hXY : X ⊆ Y) : IsAsympExpansionDLMF X f a :=
  fun n hn => (h n hn).mono (inf_le_inf_left _ (principal_mono.mpr hXY))

/-! ### Existence and non-uniqueness of functions with a given expansion -/

theorem isAsympExpansion_borelRitt_add (θ : ℝ) (a : ℕ → ℂ) (c : ℂ) :
    IsAsympExpansionDLMF (sectorDLMF θ Real.pi)
      (fun z => borelRittFn θ a z + c * brNull θ z) a := by
  have h := dlmf_2_1_iii_add (isAsympExpansion_borelRittFn (θ := θ) (a := a))
    (dlmf_2_1_iii_const_mul c (isAsympExpansion_brNull (θ := θ)))
  have e : (a + fun n => c * (0 : ℕ → ℂ) n) = a := by funext n; simp
  rw [e] at h
  exact h

theorem differentiableOn_borelRitt_add (θ : ℝ) (a : ℕ → ℂ) (c : ℂ) :
    DifferentiableOn ℂ (fun z => borelRittFn θ a z + c * brNull θ z)
      (sectorDLMF θ Real.pi ∩ {z | 1 < ‖z‖}) :=
  differentiableOn_borelRittFn.add
    ((differentiableOn_const c).mul (differentiableOn_brNull.mono inter_subset_left))

theorem borelRitt_add_injective (θ : ℝ) (a : ℕ → ℂ) {z₀ : ℂ} :
    Function.Injective fun c : ℂ => borelRittFn θ a z₀ + c * brNull θ z₀ := fun _ _ h =>
  mul_right_cancel₀ (exp_ne_zero _) (add_left_cancel h)

/-- **DLMF §2.1(iii)**: for any coefficients `a₀, a₁, a₂, …` and any unbounded sector `𝐗` of
finite angle (here `|ph(z e^{−iθ})| < ω ≤ π`), there is an infinity of functions, analytic in
`𝐗` for `|z| > 1`, with the asymptotic expansion 2.1.14 as `z → ∞` in `𝐗`. -/
theorem dlmf_2_1_iii_exists_sector {θ ω : ℝ} (hω : ω ≤ Real.pi) (a : ℕ → ℂ) :
    {f : ℂ → ℂ | DifferentiableOn ℂ f (sectorDLMF θ ω ∩ {z | 1 < ‖z‖}) ∧
      IsAsympExpansionDLMF (sectorDLMF θ ω) f a}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun c : ℂ => fun z => borelRittFn θ a z + c * brNull θ z)
    (fun _ _ h => borelRitt_add_injective θ a (z₀ := 0) (congrFun h 0)) fun c => ⟨?_, ?_⟩
  · exact (differentiableOn_borelRitt_add θ a c).mono
      (inter_subset_inter_left _ (sectorDLMF_subset_pi hω))
  · exact (isAsympExpansion_borelRitt_add θ a c).mono (sectorDLMF_subset_pi hω)

/-- **DLMF §2.1(iii)**: the same on the positive real axis: for real coefficients there is an
infinity of real functions, analytic on `(1, ∞)`, with the expansion 2.1.14 as `x → +∞`. -/
theorem dlmf_2_1_iii_exists_real (a : ℕ → ℝ) :
    {f : ℝ → ℝ | AnalyticOnNhd ℝ f (Ioi 1) ∧ IsAsympExpansionDLMF (Ioi 0) f a}.Infinite := by
  set a' : ℕ → ℂ := fun s => (a s : ℂ)
  set G : ℝ → ℂ → ℂ := fun c z => borelRittFn 0 a' z + (c : ℂ) * brNull 0 z
  have hmemS : ∀ x : ℝ, 0 < x → (x : ℂ) ∈ sectorDLMF 0 Real.pi := fun x hx =>
    ⟨Complex.ofReal_ne_zero.mpr hx.ne', by
      simp [Complex.arg_ofReal_of_nonneg hx.le, Real.pi_pos]⟩
  -- the value of the null function at `2`
  have hnull2 : (brNull 0 (2 : ℂ)).re ≠ 0 := by
    have e : brNull 0 (2 : ℂ) = ((Real.exp (-(2 : ℝ) ^ (1 / 4 : ℝ)) : ℝ) : ℂ) := by
      rw [brNull, quarterPow]
      simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
      rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring,
        show (2 : ℂ) = ((2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (by norm_num), ← Complex.ofReal_neg, ← Complex.ofReal_exp]
    rw [e, Complex.ofReal_re]
    exact (Real.exp_pos _).ne'
  refine Set.infinite_of_injective_forall_mem (f := fun c : ℝ => fun x : ℝ => (G c x).re)
    (fun c₁ c₂ h => by
      have := congrFun h 2
      simp only [G, Complex.add_re, Complex.re_ofReal_mul, add_right_inj] at this
      exact mul_right_cancel₀ hnull2 this) fun c => ⟨?_, ?_⟩
  · intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hz : (x : ℂ) ∈ sectorDLMF 0 Real.pi ∩ {z | 1 < ‖z‖} :=
      ⟨hmemS x (by linarith), by simpa [Complex.norm_real, abs_of_pos (by linarith : (0:ℝ) < x)]⟩
    have hU : IsOpen (sectorDLMF 0 Real.pi ∩ {z : ℂ | 1 < ‖z‖}) :=
      (isOpen_sectorDLMF_pi 0).inter (isOpen_lt continuous_const continuous_norm)
    have hA : AnalyticAt ℂ (G c) (x : ℂ) :=
      (differentiableOn_borelRitt_add 0 a' c).analyticAt (hU.mem_nhds hz)
    exact (Complex.reCLM.analyticAt _).comp
      ((hA.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt x))
  · -- transfer the complex expansion to the real axis
    have hk : Tendsto (fun x : ℝ => (x : ℂ)) (Bornology.cobounded ℝ ⊓ 𝓟 (Ioi 0))
        (Bornology.cobounded ℂ ⊓ 𝓟 (sectorDLMF 0 Real.pi)) := by
      refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr ?_⟩
      · exact (tendsto_norm_cobounded_atTop.mono_left
          (inf_le_left : Bornology.cobounded ℝ ⊓ 𝓟 (Ioi 0) ≤ _)).congr fun x => by
            simp [Complex.norm_real]
      · filter_upwards [mem_inf_of_right (mem_principal_self (Ioi (0 : ℝ)))] with x hx
        exact hmemS x hx
    have hC := (isAsympExpansionDLMF_iff.mp (isAsympExpansion_borelRitt_add 0 a' c)).comp_tendsto
      hk
    rw [isAsympExpansionDLMF_iff]
    intro n
    have h1 := hC n
    have hre : (fun x : ℝ => (G c x).re - (PowerSeries.trunc n (PowerSeries.mk a)).eval x⁻¹) =
        fun x : ℝ => ((G c (x : ℂ)) - (PowerSeries.trunc n (PowerSeries.mk a')).eval
          ((x : ℂ)⁻¹)).re := by
      funext x
      rw [eval_trunc_eq_sum, eval_trunc_eq_sum, Complex.sub_re]
      congr 1
      simp only [PowerSeries.coeff_mk, a']
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre]
    have hreO : (fun x : ℝ => ((G c x) - (PowerSeries.trunc n (PowerSeries.mk a')).eval
        ((x : ℂ)⁻¹)).re) =O[Bornology.cobounded ℝ ⊓ 𝓟 (Ioi 0)] fun x : ℝ =>
        (G c x) - (PowerSeries.trunc n (PowerSeries.mk a')).eval ((x : ℂ)⁻¹) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun x => by
        rw [one_mul, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
    refine hreO.trans (h1.trans (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)))
    simp [Complex.norm_real]

theorem inv_mem_sectorDLMF {θ ω : ℝ} (hω : ω ≤ Real.pi) {w : ℂ} (hw : w ∈ sectorDLMF θ ω) :
    w⁻¹ ∈ sectorDLMF (-θ) ω := by
  obtain ⟨hw0, hwa⟩ := hw
  refine ⟨inv_ne_zero hw0, ?_⟩
  have e : w⁻¹ * exp (-(((-θ : ℝ) : ℂ) * I)) = (w * exp (-(θ * I)))⁻¹ := by
    rw [mul_inv, ← Complex.exp_neg]; push_cast; ring_nf
  rw [e, Complex.arg_inv]
  have hne : arg (w * exp (-(θ * I))) ≠ Real.pi := by
    intro h; rw [h, abs_of_pos Real.pi_pos] at hwa; linarith
  simp only [hne, ↓reduceIte, abs_neg]
  exact hwa

/-- **DLMF §2.1(iii)**: the same for expansions 2.1.16 at a finite point `c`, in a sector with
vertex `c`: there is an infinity of functions, analytic in the sector near `c`, with
`f(x) ∼ a₀ + a₁(x − c) + a₂(x − c)² + ⋯` as `x → c`. -/
theorem dlmf_2_1_iii_exists_at (c : ℂ) {θ ω : ℝ} (hω : ω ≤ Real.pi) (a : ℕ → ℂ) :
    {f : ℂ → ℂ | DifferentiableOn ℂ f {x | x - c ∈ sectorDLMF θ ω ∧ ‖x - c‖ < 1} ∧
      IsAsympExpansionAtDLMF {x | x - c ∈ sectorDLMF θ ω} c f a}.Infinite := by
  set X := {x | x - c ∈ sectorDLMF θ ω}
  set k : ℂ → ℂ := fun x => (x - c)⁻¹
  refine Set.infinite_of_injective_forall_mem
    (f := fun c' : ℂ => fun x => borelRittFn (-θ) a (k x) + c' * brNull (-θ) (k x))
    (fun c₁ c₂ h => borelRitt_add_injective (-θ) a (z₀ := k c) (congrFun h c)) fun c' => ⟨?_, ?_⟩
  · intro x hx
    have hx0 : x - c ≠ 0 := hx.1.1
    have hkx : k x ∈ sectorDLMF (-θ) Real.pi ∩ {z | 1 < ‖z‖} := by
      refine ⟨sectorDLMF_subset_pi hω (inv_mem_sectorDLMF hω hx.1), ?_⟩
      show 1 < ‖(x - c)⁻¹‖
      rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hx0)]; exact hx.2
    have hU : IsOpen (sectorDLMF (-θ) Real.pi ∩ {z : ℂ | 1 < ‖z‖}) :=
      (isOpen_sectorDLMF_pi _).inter (isOpen_lt continuous_const continuous_norm)
    have hG := ((differentiableOn_borelRitt_add (-θ) a c').differentiableAt
      (hU.mem_nhds hkx))
    have hkd : DifferentiableAt ℂ k x := ((differentiableAt_id.sub_const c).inv hx0)
    exact (hG.comp x hkd).differentiableWithinAt
  · have hk : Tendsto k (approachIn X c) (Bornology.cobounded ℂ ⊓ 𝓟 (sectorDLMF (-θ) ω)) := by
      refine tendsto_inf.mpr ⟨tendsto_inv₀_nhdsNE_zero.comp ?_, tendsto_principal.mpr ?_⟩
      · exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_sub_approachIn X c,
          (eventually_sub_ne_zero_approachIn X c).mono fun x hx => hx⟩
      · filter_upwards [self_mem_nhdsWithin (s := X \ {c}) (a := c)] with x hx
        exact inv_mem_sectorDLMF hω hx.1
    have hE := (isAsympExpansionDLMF_iff.mp
      ((isAsympExpansion_borelRitt_add (-θ) a c').mono (sectorDLMF_subset_pi hω))).comp_tendsto hk
    rw [isAsympExpansionAtDLMF_iff]
    convert hE using 1
    · funext x; simp [k]
    · rfl

end Azurite.DLMF
