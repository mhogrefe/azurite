/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section6FractionalExpansion

/-!
# DLMF §2.6(iii), Example: `f(t) = t^{1−α}/(1 + t)`, 2.6.48–2.6.52

* 2.6.48 (`dlmf_2_6_48`): `I^μ f(x) = (1/Γ(μ)) ∫₀^x (x−t)^{μ−1} t^{1−α}(1+t)^{−1} dt`.
* 2.6.49–2.6.50 (`dlmf_2_6_49`, `dlmf_2_6_50`): `f(t) = ∑_{s<n} (−1)^s t^{−s−α} +
  (−1)ⁿ t^{1−n−α}/(1+t)`, so `aₛ = (−1)^s` and `fₙ(t) = (−1)ⁿ t^{1−n−α}/(1+t)`; `fracEx_setup`:
  the hypotheses of §2.6(ii)–(iii) hold for `0 < α < 1`.
* 2.6.51 (`dlmf_2_6_51`): `𝓜f(s) = (−1)^s π/sin(πα)` for `s = 1, 2, …` (the continued transform
  `mellinCont` of 2.6.18, evaluated through `∫₀^∞ t^{s−1} fₛ(t) dt` and
  `∫₀^∞ t^{−α}/(1+t) dt = π/sin πα`).
* 2.6.52 (`dlmf_2_6_52`): the expansion 2.6.45 for this `f`,
  `I^μ f(x) = ∑_{s<n} (−1)^s Γ(1−s−α)/Γ(μ+1−s−α) x^{μ−s−α}
    − (π/sin πα) ∑_{s=1}^n x^{μ−s}/(Γ(μ+1−s)(s−1)!) + x^{−n} δₙ(x)`, `x → +∞`.
* 2.6.53 (the explicit bound on `δₙ(x)`) is NOT formalized: it rests on DLMF's representation
  2.6.47 of `δₙ` through the repeated integrals `f_{n,j}`, which is not established
  (`docs/dlmf_plan.md`). The remark that 2.6.48 is a `₂F₁` is not formalized either.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-- `f(t) = t^{1−α}/(1 + t)`. -/
noncomputable def fracExF (α : ℝ) (t : ℝ) : ℂ := ((t ^ (1 - α) / (1 + t) : ℝ) : ℂ)

/-- **DLMF 2.6.48**: `I^μ f(x) = (1/Γ(μ)) ∫₀^x (x−t)^{μ−1} t^{1−α} (1+t)^{−1} dt`. -/
theorem dlmf_2_6_48 (μ : ℂ) (α x : ℝ) :
    fracIntegral μ (fracExF α) x =
      1 / Gamma μ * ∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (μ - 1) *
        (((t ^ (1 - α) : ℝ) : ℂ) * ((1 + t : ℝ) : ℂ)⁻¹) := by
  rw [dlmf_1_15_47]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [fracExF]
  push_cast
  ring

/-- **DLMF 2.6.49–2.6.50**: `f(t) − ∑_{s<n} (−1)^s t^{−s−α} = (−1)ⁿ t^{1−n−α}/(1+t)` for `t > 0`. -/
theorem dlmf_2_6_50 (α : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    stieltjesRem (fracExF α) (fun s => (-1) ^ s) α n t =
      (-1) ^ n * ((t ^ (1 - n - α) / (1 + t) : ℝ) : ℂ) := by
  induction n with
  | zero => simp [StieltjesSetup.rem_zero, fracExF]
  | succ n ih =>
    have e : stieltjesRem (fracExF α) (fun s => (-1) ^ s) α n t =
        (-1) ^ n * (t : ℂ) ^ (-((n : ℂ) + α)) +
          stieltjesRem (fracExF α) (fun s => (-1) ^ s) α (n + 1) t :=
      StieltjesSetup.rem_eq_add_succ (f := fracExF α) (a := fun s => (-1) ^ s) (α := α) n t
    have ht1 : (1 + t : ℝ) ≠ 0 := by linarith
    have hpow : (t : ℂ) ^ (-((n : ℂ) + α)) = ((t ^ (-(n + α)) : ℝ) : ℂ) := by
      rw [ofReal_cpow ht.le]
      push_cast
      ring_nf
    have hsplit : t ^ (1 - n - α) = t * t ^ (-(n + α)) := by
      rw [show (1 - n - α : ℝ) = 1 + -(n + α) by ring, Real.rpow_add ht, Real.rpow_one]
    have hsplit' : t ^ (1 - ((n + 1 : ℕ) : ℝ) - α) = t ^ (-(n + α)) := by
      congr 1
      push_cast
      ring
    rw [hsplit', pow_succ]
    have : stieltjesRem (fracExF α) (fun s => (-1) ^ s) α (n + 1) t =
        (-1) ^ n * ((t * t ^ (-(n + α)) / (1 + t) : ℝ) : ℂ) -
          (-1) ^ n * ((t ^ (-(n + α)) : ℝ) : ℂ) := by
      rw [← hsplit, ← ih, ← hpow]
      linear_combination -e
    have ht1' : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast ht1
    rw [this]
    push_cast
    field_simp
    ring

/-- **DLMF 2.6.49** in DLMF's form. -/
theorem dlmf_2_6_49 (α : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    fracExF α t = ∑ s ∈ Finset.range n, (-1) ^ s * (t : ℂ) ^ (-((s : ℂ) + α)) +
      (-1) ^ n * ((t ^ (1 - n - α) / (1 + t) : ℝ) : ℂ) := by
  have h := dlmf_2_6_50 α n ht
  rw [stieltjesRem] at h
  linear_combination h

/-- The hypotheses of §2.6(ii)–(iii) for `f(t) = t^{1−α}/(1+t)`, `0 < α < 1`:
`aₛ = (−1)^s`. -/
theorem fracEx_setup {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    StieltjesSetup (fracExF α) (fun s => (-1) ^ s) α where
  f_loc R := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.div (continuousOn_id.rpow_const fun t _ => Or.inr (by linarith))
      (continuousOn_const.add continuousOn_id) fun t ht => ?_
    show (1 : ℝ) + t ≠ 0
    linarith [ht.1]
  f_exp := by
    refine ⟨isAsympScale_cpow_neg_atTop _ fun s => ?_, fun n => ?_⟩
    · simp only [add_re, natCast_re, ofReal_re]
      push_cast
      linarith
    · refine isBigODLMF_cpow_top_of_isBigO_rpow ?_
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      have h := dlmf_2_6_50 α n ht
      rw [stieltjesRem] at h
      rw [h, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_real,
        Real.norm_of_nonneg (div_nonneg (Real.rpow_nonneg ht.le _) (by linarith)), one_mul,
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
      simp only [add_re, natCast_re, ofReal_re]
      rw [div_le_iff₀ (by linarith), show (1 - n - α : ℝ) = 1 + -(n + α) by ring,
        Real.rpow_add ht, Real.rpow_one]
      have : 0 ≤ t ^ (-(n + α)) := Real.rpow_nonneg ht.le _
      nlinarith
  α_pos := hα0
  α_le := hα1.le

/-- **DLMF 2.6.51**: `𝓜f(s) = (−1)^s π/sin(πα)` for `s = n + 1`, `n = 0, 1, …` (the continued
Mellin transform of 2.6.18). -/
theorem dlmf_2_6_51 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    mellinCont (fracExF α) (fun s => (-1) ^ s) α ((n : ℂ) + 1) =
      (-1) ^ (n + 1) * (π / Complex.sin (π * α)) := by
  rw [(fracEx_setup hα0 hα1).mellinCont_succ_eq hα1 n]
  have h := integral_cpow_neg_div_add hα0 hα1 (z := 1) one_mem_slitPlane
  rw [one_cpow, mul_one] at h
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [dlmf_2_6_50 α (n + 1) ht0, ofReal_div, ofReal_cpow ht0.le]
  push_cast
  have hpow : (t : ℂ) ^ n * (t : ℂ) ^ (1 - ((n : ℂ) + 1) - α) = (t : ℂ) ^ (-(α : ℂ)) := by
    rw [← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr ht0.ne')]
    congr 1
    ring
  rw [add_comm (1 : ℂ) (t : ℂ)]
  linear_combination ((-1 : ℂ) ^ (n + 1) / (t + 1)) * hpow

/-- `cₛ = (π/sin πα)/(s−1)!` for `s ≥ 1`. -/
theorem stieltjesC_fracEx {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {s : ℕ} (hs : 1 ≤ s) :
    stieltjesC (fracExF α) (fun s => (-1) ^ s) α s =
      π / Complex.sin (π * α) / ((s - 1)! : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  rw [stieltjesC, Nat.add_sub_cancel, Nat.cast_succ, dlmf_2_6_51 hα0 hα1]
  rcases neg_one_pow_eq_or ℂ (m + 1) with h | h <;> rw [h] <;> ring

/-- **DLMF 2.6.52**: for `0 < α < 1`, real `μ > 0` and `x → +∞`,
`I^μ f(x) = ∑_{s<n} (−1)^s Γ(1−s−α)/Γ(μ+1−s−α) x^{μ−s−α}
  − (π/sin πα) ∑_{s=1}^n x^{μ−s}/(Γ(μ+1−s)(s−1)!) + x^{−n} δₙ(x)`. -/
theorem dlmf_2_6_52 {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, fracIntegral (μ : ℂ) (fracExF α) x =
      ∑ s ∈ Finset.range n, (-1) ^ s * (Gamma (1 - s - α) / Gamma ((μ : ℂ) + 1 - s - α)) *
        (x : ℂ) ^ ((μ : ℂ) - s - α) -
      π / Complex.sin (π * α) * ∑ s ∈ Finset.Icc 1 n,
        1 / Gamma ((μ : ℂ) + 1 - s) * ((x : ℂ) ^ ((μ : ℂ) - s) / ((s - 1)! : ℂ)) +
      (x : ℂ) ^ (-(n : ℂ)) * fracRemDelta μ (fracExF α) (fun s => (-1) ^ s) α n x := by
  filter_upwards [(fracEx_setup hα0 hα1).dlmf_2_6_45 hμ hα1 n] with x hx
  rw [hx, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [stieltjesC_fracEx hα0 hα1 (Finset.mem_Icc.mp hs).1]
  ring

end Azurite.DLMF
