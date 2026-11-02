/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section2
import Azurite.DLMF.Chapter2.Section6Fractional
import Azurite.DLMF.Chapter2.Section6StieltjesOne

/-!
# DLMF §2.6(iii): the expansion 2.6.45 of `I^μ f(x)`, `0 < α < 1`

For `f` locally integrable on `[0, ∞)` with `f(t) ∼ ∑ aₛ t^{−s−α}` (2.6.9, `StieltjesSetup`),
`0 < α < 1`, and real `μ > 0`:

* `fracRem`: the remainder `Γ(μ) x^{−n} δₙ(x)`, written as
  `∫₀^x Kₙ(x,t) tⁿ fₙ(t) dt − ∑_{i<n} binom(μ−1,i)(−1)^i x^{μ−1−i} ∫_x^∞ tⁱ fₙ(t) dt`
  (absolutely convergent for large `x`); `fracRem_zero`: `Γ(μ) I^μ f(x)` for `n = 0`.
* `fracRem_succ`: `fracRem n = aₙ Γ(μ)Γ(1−n−α)/Γ(μ+1−n−α) x^{μ−n−α} +
  binom(μ−1,n)(−1)ⁿ x^{μ−1−n} 𝓜f(n+1) + fracRem (n+1)`, from `fₙ = aₙ t^{−n−α} + f_{n+1}`, the
  kernel recursion `fracKer_succ`, `∫₀^∞ tⁿ f_{n+1} = 𝓜f(n+1)` (`mellinCont_succ_eq`) and the
  regularized beta identity `dlmf_2_6_39_reg`.
* 2.6.45 (`dlmf_2_6_45_moments`, `dlmf_2_6_45`): for `x → +∞`,
  `I^μ f(x) = ∑_{s<n} aₛ Γ(1−s−α)/Γ(μ+1−s−α) x^{μ−s−α} − ∑_{s=1}^n cₛ/Γ(μ+1−s) x^{μ−s}
    + x^{−n} δₙ(x)`
  with `cₛ` from 2.6.18 (`stieltjesC`) and `δₙ(x) := xⁿ fracRem n x / Γ(μ)` (`fracRemDelta`).
  The identity is proved by induction on `n`, as 2.6.27 was; DLMF derives it from the
  distributional identity 2.6.41 and the convolution algebra `K⁺`. DLMF's expression 2.6.47 of
  `δₙ` through the repeated integrals `f_{n,j}` is NOT established here (it is a different
  representation of the same remainder; `docs/dlmf_plan.md`).
* `fracRem_isBigO`: `fracRem n x = O(x^{μ−n−α})`, so 2.6.45 is a genuine asymptotic expansion.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The remainder -/

/-- The remainder of 2.6.45, `Γ(μ) x^{−n} δₙ(x) = ∫₀^x Kₙ(x,t) tⁿ fₙ(t) dt −
∑_{i<n} binom(μ−1,i)(−1)^i x^{μ−1−i} ∫_x^∞ tⁱ fₙ(t) dt`. -/
noncomputable def fracRem (μ : ℝ) (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (∫ t in Ioo (0 : ℝ) x, (fracKer μ n x t : ℂ) * (t : ℂ) ^ n * stieltjesRem f a α n t) -
    ∑ i ∈ Finset.range n, ((Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) : ℝ) : ℂ) *
      ∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α n t

/-- `δₙ(x) := xⁿ · fracRem n x / Γ(μ)`, so that `x^{−n} δₙ(x)` is the remainder of 2.6.45. -/
noncomputable def fracRemDelta (μ : ℝ) (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ n * fracRem μ f a α n x / Gamma μ

theorem continuousOn_fracKer (μ : ℝ) (m : ℕ) (x : ℝ) : ContinuousOn (fracKer μ m x) (Ioo 0 x) := by
  unfold fracKer
  refine ContinuousOn.div ?_ (continuousOn_pow m) fun t ht => pow_ne_zero m ht.1.ne'
  refine ContinuousOn.sub ?_ (continuousOn_finsetSum _ fun i _ =>
    continuousOn_const.mul (continuousOn_pow i))
  exact (continuousOn_const.sub continuousOn_id).rpow_const fun t ht =>
    Or.inl (by show x - t ≠ 0; linarith [ht.2])

/-- `|Kₘ(x,t)| ≤ x^{μ−1−m} (C₁ + C₂ (1 − t/x)^{μ−1})` on `(0, x)`, and `≤ x^{μ−1−m} B` on
`(0, x/2]`. -/
theorem fracKer_bound (μ : ℝ) (m : ℕ) :
    ∃ B C₁ C₂ : ℝ, 0 ≤ B ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ x : ℝ, 0 < x →
      (∀ t ∈ Ioc 0 (x / 2), |fracKer μ m x t| ≤ x ^ (μ - 1 - m) * B) ∧
      ∀ t ∈ Ioo 0 x, |fracKer μ m x t| ≤ x ^ (μ - 1 - m) * (C₁ + C₂ * (1 - t / x) ^ (μ - 1)) := by
  obtain ⟨B, hB⟩ := fracKerUnit_bound_half μ m
  obtain ⟨C₁, C₂, hC₁, hC₂, hC⟩ := fracKerUnit_bound μ m
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (1 / 2) ⟨by norm_num, le_rfl⟩)
  refine ⟨B, C₁, C₂, hB0, hC₁, hC₂, fun x hx => ⟨fun t ht => ?_, fun t ht => ?_⟩⟩
  · have htx : t < x := by linarith [ht.2]
    rw [fracKer_eq_scale m ht.1 htx, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx _)]
    exact mul_le_mul_of_nonneg_left (hB _ ⟨div_pos ht.1 hx, by
      rw [div_le_iff₀ hx]; linarith [ht.2]⟩) (Real.rpow_pos_of_pos hx _).le
  · rw [fracKer_eq_scale m ht.1 ht.2, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx _)]
    exact mul_le_mul_of_nonneg_left (hC _ ⟨div_pos ht.1 hx, (div_lt_one hx).mpr ht.2⟩)
      (Real.rpow_pos_of_pos hx _).le

/-- `(1 − t/x)^{μ−1}` is integrable on `(x/2, x)`. -/
theorem integrableOn_one_sub_div_rpow {μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (1 - t / x) ^ (μ - 1)) (Ioo (x / 2) x) := by
  have h := (integrableOn_sub_rpow (a := x / 2) (x := x) (r := μ - 1) (by linarith) (by linarith))
    |>.const_mul (x ^ (μ - 1))⁻¹
  refine IntegrableOn.congr_fun (IntegrableOn.mono_set h Ioo_subset_Ioc_self) (fun t ht => ?_)
    measurableSet_Ioo
  rw [show 1 - t / x = (x - t) / x by field_simp, Real.div_rpow (by linarith [ht.2]) hx.le]
  ring

/-- Integrability of `Kₘ(x,t) tᵐ g(t)` on `(0, x)`: `tᵐ g` integrable near `0`, `g` bounded on
`[x/2, x]`. -/
theorem integrableOn_fracKer_mul {μ : ℝ} (hμ : 0 < μ) (m : ℕ) {g : ℝ → ℂ} {x : ℝ} (hx : 0 < x)
    (hg : AEStronglyMeasurable g (volume.restrict (Ioo 0 x)))
    (h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ m * g t) (Ioc 0 (x / 2)))
    (h2 : ∃ M, ∀ t ∈ Icc (x / 2) x, ‖g t‖ ≤ M) :
    IntegrableOn (fun t : ℝ => (fracKer μ m x t : ℂ) * (t : ℂ) ^ m * g t) (Ioo 0 x) := by
  obtain ⟨B, C₁, C₂, hB0, hC₁, hC₂, hK⟩ := fracKer_bound μ m
  obtain ⟨hKa, hKb⟩ := hK x hx
  obtain ⟨M, hM⟩ := h2
  have hKmeas : AEStronglyMeasurable (fun t : ℝ => (fracKer μ m x t : ℂ))
      (volume.restrict (Ioo 0 x)) :=
    (continuous_ofReal.comp_continuousOn (continuousOn_fracKer μ m x)).aestronglyMeasurable
      measurableSet_Ioo
  have hsub1 : Ioc 0 (x / 2) ⊆ Ioo 0 x := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  have hsub2 : Ioo (x / 2) x ⊆ Ioo 0 x := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  -- near `0`
  have hpart1 : IntegrableOn (fun t : ℝ => (fracKer μ m x t : ℂ) * (t : ℂ) ^ m * g t)
      (Ioc 0 (x / 2)) := by
    have := Integrable.bdd_mul (c := x ^ (μ - 1 - m) * B) h1 (hKmeas.mono_set hsub1) ?_
    · exact IntegrableOn.congr_fun this (fun t _ => by ring) measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_real, Real.norm_eq_abs]
      exact hKa t ht
  -- near `x`
  have hpart2 : IntegrableOn (fun t : ℝ => (fracKer μ m x t : ℂ) * (t : ℂ) ^ m * g t)
      (Ioo (x / 2) x) := by
    have hdom : IntegrableOn (fun t : ℝ =>
        x ^ (μ - 1 - m) * (C₁ + C₂ * (1 - t / x) ^ (μ - 1)) * x ^ m * M) (Ioo (x / 2) x) := by
      refine Integrable.mul_const (Integrable.mul_const (Integrable.const_mul ?_ _) _) _
      exact (integrableOn_const (by simp)).add ((integrableOn_one_sub_div_rpow hμ hx).const_mul _)
    refine Integrable.mono' hdom ?_ ?_
    · exact ((hKmeas.mono_set hsub2).mul ((continuous_ofReal.pow m).aestronglyMeasurable)).mul
        (hg.mono_set hsub2)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, norm_pow, norm_real,
        Real.norm_of_nonneg ht0.le]
      have hM' := hM t ⟨ht.1.le, ht.2.le⟩
      have hKt := hKb t (hsub2 ht)
      have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM'
      have htm : t ^ m ≤ x ^ m := pow_le_pow_left₀ ht0.le ht.2.le m
      have hnn : 0 ≤ x ^ (μ - 1 - m) * (C₁ + C₂ * (1 - t / x) ^ (μ - 1)) :=
        mul_nonneg (Real.rpow_nonneg hx.le _) (add_nonneg hC₁ (mul_nonneg hC₂
          (Real.rpow_nonneg (by rw [sub_nonneg, div_le_one hx]; exact ht.2.le) _)))
      exact mul_le_mul (mul_le_mul hKt htm (pow_nonneg ht0.le m) hnn) hM' (norm_nonneg _)
        (mul_nonneg hnn (pow_nonneg hx.le m))
  have : Ioo 0 x ⊆ Ioc 0 (x / 2) ∪ Ioo (x / 2) x := fun t ht => by
    rcases le_or_gt t (x / 2) with h | h
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨h, ht.2⟩
  exact (hpart1.union hpart2).mono_set this

namespace StieltjesSetup

variable {f : ℝ → ℂ} {a : ℕ → ℂ} {α : ℝ} (hS : StieltjesSetup f a α)
include hS

/-- `tⁿ fₘ` is integrable on `(0, y]` for `m < n + 2 − α`. -/
theorem integrableOn_Ioc_pow_mul_rem' (n m : ℕ) (hm : (m : ℝ) < n + 2 - α) (y : ℝ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * stieltjesRem f a α m t) (Ioc 0 y) := by
  have h1 := hS.integrableOn_Ioc_pow_mul_rem n m hm
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * stieltjesRem f a α m t) (Icc 1 y) :=
    (hS.locallyIntegrableOn_pow_mul_rem n m).integrableOn_compact_subset
      (fun t ht => lt_of_lt_of_le zero_lt_one ht.1) isCompact_Icc
  have : Ioc 0 y ⊆ Ioc 0 1 ∪ Icc 1 y := fun t ht => by
    rcases le_or_gt t 1 with h | h
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨h.le, ht.2⟩
  exact (h1.union h2).mono_set this

/-- Eventually (in `t`), `‖fₘ(t)‖ ≤ C` for `t ≥ T`, with `T ≥ 1`. -/
theorem exists_bound_rem (m : ℕ) :
    ∃ T C : ℝ, 1 ≤ T ∧ ∀ t, T ≤ t → ‖stieltjesRem f a α m t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hS.rem_isBigO m).bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hC
  refine ⟨max T₀ 1, max C 0, le_max_right _ _, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have h := hT₀ t (le_trans (le_max_left _ _) ht)
  have hp : ‖t ^ (-(m + α))‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith [hS.α_pos, (Nat.cast_nonneg m :
      (0 : ℝ) ≤ m)])
  calc ‖stieltjesRem f a α m t‖ ≤ C * ‖t ^ (-(m + α))‖ := h
    _ ≤ max C 0 * 1 := mul_le_mul (le_max_left _ _) hp (norm_nonneg _) (le_max_right _ _)
    _ = max C 0 := mul_one _

theorem aestronglyMeasurable_rem (m : ℕ) {x : ℝ} :
    AEStronglyMeasurable (stieltjesRem f a α m) (volume.restrict (Ioo 0 x)) :=
  (hS.locallyIntegrableOn_rem m).aestronglyMeasurable.mono_set Ioo_subset_Ioi_self

/-- The tail `∫_x^∞ tⁱ fₙ` converges for `i < n`, `x ≥ 1`. -/
theorem integrableOn_Ioi_pow_mul_rem_tail {i n : ℕ} (hi : i < n) {x : ℝ} (hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ i * stieltjesRem f a α n t) (Ioi x) := by
  have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  refine IntegrableOn.mono_set (integrableOn_Ioi_one_of_isBigO
    (hS.locallyIntegrableOn_pow_mul_rem i n) (b := n + α - i) ?_ (by linarith [hS.α_pos]))
    (Ioi_subset_Ioi hx)
  refine (hS.isBigO_pow_mul_rem i n).congr' EventuallyEq.rfl (Eventually.of_forall fun t => ?_)
  rw [show (i : ℝ) - (n + α) = -(n + α - i) by ring]

/-! ### The recursion -/

variable {μ : ℝ}

omit hS in
/-- `fracRem 0 x = Γ(μ) I^μ f(x)`. -/
theorem fracRem_zero (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    fracRem μ f a α 0 x = Gamma μ * fracIntegral (μ : ℂ) f x := by
  have hΓ : Gamma (μ : ℂ) ≠ 0 := by
    rw [Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hμ).ne'
  rw [fracIntegral, fracIntegralFrom, ← mul_assoc, mul_inv_cancel₀ hΓ, one_mul, fracRem,
    Finset.range_zero, Finset.sum_empty, sub_zero, intervalIntegral.integral_of_le hx.le,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [fracKer_zero, rem_zero, pow_zero, mul_one, ofReal_cpow (by linarith [ht.2])]
  push_cast
  rfl

omit hS in
/-- `tⁿ · t^{−(n+α)} = t^{−α}` for `t > 0` (complex powers). -/
theorem pow_mul_cpow_neg {t : ℝ} (ht : 0 < t) (n : ℕ) (α : ℝ) :
    (t : ℂ) ^ n * (t : ℂ) ^ (-((n : ℂ) + α)) = (t : ℂ) ^ (-(α : ℂ)) := by
  rw [← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]
  congr 1
  ring

/-- **The recursion**: for large `x`,
`fracRem n x = aₙ Γ(μ)Γ(1−n−α)/Γ(μ+1−n−α) x^{μ−n−α} + binom(μ−1,n)(−1)ⁿ x^{μ−1−n} 𝓜f(n+1)
  + fracRem (n+1) x`. -/
theorem fracRem_succ (hμ : 0 < μ) (hα : α < 1) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, fracRem μ f a α n x =
      a n * ((Real.Gamma μ * Real.Gamma (1 - n - α) / Real.Gamma (μ + 1 - n - α) *
        x ^ (μ - n - α) : ℝ) : ℂ) +
      ((Ring.choose (μ - 1) n * (-1) ^ n * x ^ (μ - 1 - n) : ℝ) : ℂ) *
        mellinCont f a α ((n : ℂ) + 1) +
      fracRem μ f a α (n + 1) x := by
  obtain ⟨T₁, C₁, hT₁, hC₁⟩ := hS.exists_bound_rem n
  obtain ⟨T₂, C₂, hT₂, hC₂⟩ := hS.exists_bound_rem (n + 1)
  filter_upwards [eventually_ge_atTop (2 * max T₁ T₂)] with x hx
  have hT : 1 ≤ max T₁ T₂ := le_trans hT₁ (le_max_left _ _)
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx2 : 1 ≤ x / 2 := by linarith
  have hα0 := hS.α_pos
  have hbn : ∃ M, ∀ t ∈ Icc (x / 2) x, ‖stieltjesRem f a α n t‖ ≤ M :=
    ⟨C₁, fun t ht => hC₁ t (by linarith [ht.1, le_max_left T₁ T₂])⟩
  have hbn1 : ∃ M, ∀ t ∈ Icc (x / 2) x, ‖stieltjesRem f a α (n + 1) t‖ ≤ M :=
    ⟨C₂, fun t ht => hC₂ t (by linarith [ht.1, le_max_right T₁ T₂])⟩
  set K : ℕ → ℝ → ℂ := fun m t => (fracKer μ m x t : ℂ) with hK
  set X : ℕ → ℂ := fun i => ((Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) : ℝ) : ℂ) with hX
  set W : ℕ → ℂ := fun i =>
    ((x ^ ((i : ℝ) - n - α + 1) / ((i : ℝ) - n - α + 1) : ℝ) : ℂ) with hW
  -- integrability
  have hJn1' : IntegrableOn (fun t : ℝ => K (n + 1) t * (t : ℂ) ^ (n + 1) * stieltjesRem f a α n t)
      (Ioo 0 x) :=
    integrableOn_fracKer_mul hμ (n + 1) hx0 (hS.aestronglyMeasurable_rem n)
      (hS.integrableOn_Ioc_pow_mul_rem' (n + 1) n (by push_cast; linarith) _) hbn
  have hJn1 : IntegrableOn
      (fun t : ℝ => K (n + 1) t * (t : ℂ) ^ (n + 1) * stieltjesRem f a α (n + 1) t) (Ioo 0 x) :=
    integrableOn_fracKer_mul hμ (n + 1) hx0 (hS.aestronglyMeasurable_rem (n + 1))
      (hS.integrableOn_Ioc_pow_mul_rem' (n + 1) (n + 1) (by push_cast; linarith) _) hbn1
  have hKa : IntegrableOn
      (fun t : ℝ => K (n + 1) t * (t : ℂ) ^ (n + 1) * (t : ℂ) ^ (-((n : ℂ) + α))) (Ioo 0 x) := by
    refine integrableOn_fracKer_mul hμ (n + 1) hx0 (((continuousOn_ofReal_cpow_Ioi _).mono
      Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo) ?_
      ⟨(x / 2) ^ (-(n + α)), fun t ht => ?_⟩
    · have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ x / 2)).mp
        (intervalIntegral.intervalIntegrable_cpow' (r := (1 : ℂ) - α) (by simp; linarith))
      refine h.congr_fun (fun t ht => ?_) measurableSet_Ioc
      rw [← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr ht.1.ne')]
      push_cast
      ring_nf
    · have ht0 : 0 < t := by linarith [ht.1]
      rw [norm_cpow_eq_rpow_re_of_pos ht0, neg_re, add_re, natCast_re, ofReal_re]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) ht.1 (by linarith)
  have hMn : IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * stieltjesRem f a α n t) (Ioo 0 x) :=
    (hS.integrableOn_Ioc_pow_mul_rem' n n (by linarith) _).mono_set Ioo_subset_Ioc_self
  have hMn1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * stieltjesRem f a α (n + 1) t) (Ioo 0 x) :=
    (hS.integrableOn_Ioc_pow_mul_rem' n (n + 1) (by push_cast; linarith) _).mono_set
      Ioo_subset_Ioc_self
  have hpα : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(α : ℂ))) (Ioo 0 x) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx0.le).mp
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))).mono_set Ioo_subset_Ioc_self
  have hTn1 : ∀ i < n + 1,
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ i * stieltjesRem f a α (n + 1) t) (Ioi x) :=
    fun i hi => hS.integrableOn_Ioi_pow_mul_rem_tail hi hx1
  have hTp : ∀ i < n, IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((i : ℂ) - ((n : ℂ) + α))) (Ioi x) := by
    intro i hi
    have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    exact (integrableOn_Ioi_cpow_iff hx0).mpr (by simp; linarith)
  -- Step A: the kernel recursion
  have hA : (∫ t in Ioo (0 : ℝ) x, K n t * (t : ℂ) ^ n * stieltjesRem f a α n t) =
      (∫ t in Ioo (0 : ℝ) x, K (n + 1) t * (t : ℂ) ^ (n + 1) * stieltjesRem f a α n t) +
        X n * ∫ t in Ioo (0 : ℝ) x, (t : ℂ) ^ n * stieltjesRem f a α n t := by
    rw [← integral_const_mul, ← integral_add hJn1' (hMn.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have h := congrArg (fun r : ℝ => (r : ℂ)) (fracKer_succ μ n x ht.1.ne')
    rw [ofReal_mul, ofReal_pow, ofReal_add, ofReal_mul (fracKer μ (n + 1) x t), ofReal_pow,
      ofReal_mul (Ring.choose (μ - 1) n * (-1) ^ n * x ^ (μ - 1 - n)), ofReal_pow] at h
    simp only [hK, hX]
    linear_combination stieltjesRem f a α n t * h
  -- Step B: `fₙ = aₙ t^{−n−α} + f_{n+1}` in the kernel integral
  have hB : (∫ t in Ioo (0 : ℝ) x, K (n + 1) t * (t : ℂ) ^ (n + 1) * stieltjesRem f a α n t) =
      a n * (∫ t in Ioo (0 : ℝ) x, K (n + 1) t * (t : ℂ) ^ (n + 1) * (t : ℂ) ^ (-((n : ℂ) + α))) +
        ∫ t in Ioo (0 : ℝ) x, K (n + 1) t * (t : ℂ) ^ (n + 1) * stieltjesRem f a α (n + 1) t := by
    rw [← integral_const_mul, ← integral_add (hKa.const_mul _) hJn1]
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    rw [rem_eq_add_succ]
    ring
  -- Step C: the moment `∫₀^x tⁿ fₙ`
  have hC : (∫ t in Ioo (0 : ℝ) x, (t : ℂ) ^ n * stieltjesRem f a α n t) =
      (∫ t in Ioo (0 : ℝ) x, (t : ℂ) ^ n * stieltjesRem f a α (n + 1) t) +
        a n * ∫ t in Ioo (0 : ℝ) x, (t : ℂ) ^ (-(α : ℂ)) := by
    rw [← integral_const_mul, ← integral_add hMn1 (hpα.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [rem_eq_add_succ, ← pow_mul_cpow_neg ht.1 n α]
    ring
  have hCval : (∫ t in Ioo (0 : ℝ) x, (t : ℂ) ^ (-(α : ℂ))) = W n := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx0.le,
      integral_cpow (Or.inl (by simp; linarith)), hW]
    simp only
    have hne : -(α : ℂ) + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [ofReal_zero, zero_cpow hne, sub_zero, ofReal_div, ofReal_cpow hx0.le]
    push_cast
    congr 2 <;> ring
  -- Step D: the tails
  have hDval : ∀ i < n, (∫ t in Ioi x, (t : ℂ) ^ ((i : ℂ) - ((n : ℂ) + α))) = -W i := by
    intro i hi
    have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) hx0, hW]
    simp only
    rw [ofReal_div, ofReal_cpow hx0.le, neg_div]
    push_cast
    congr 3 <;> ring
  have hD : ∀ i < n, (∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α n t) =
      (∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α (n + 1) t) - a n * W i := by
    intro i hi
    have hW' : W i = -∫ t in Ioi x, (t : ℂ) ^ ((i : ℂ) - ((n : ℂ) + α)) := by
      rw [hDval i hi, neg_neg]
    rw [hW', mul_neg, sub_neg_eq_add, ← integral_const_mul,
      ← integral_add (hTn1 i (by omega)) ((hTp i hi).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans hx0 ht
    rw [rem_eq_add_succ]
    have e : (t : ℂ) ^ i * (t : ℂ) ^ (-((n : ℂ) + α)) = (t : ℂ) ^ ((i : ℂ) - ((n : ℂ) + α)) := by
      rw [← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr ht0.ne'), sub_eq_add_neg]
    rw [← e]
    ring
  have hsum : ∑ i ∈ Finset.range n, X i * ∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α n t =
      ∑ i ∈ Finset.range n, X i * (∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α (n + 1) t) -
        a n * ∑ i ∈ Finset.range n, X i * W i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hD i (Finset.mem_range.mp hi)]
    ring
  -- Step E: the full moment is `𝓜f(n+1)`
  have hE : (∫ t in Ioo (0 : ℝ) x, (t : ℂ) ^ n * stieltjesRem f a α (n + 1) t) +
      (∫ t in Ioi x, (t : ℂ) ^ n * stieltjesRem f a α (n + 1) t) =
        mellinCont f a α ((n : ℂ) + 1) := by
    rw [hS.mellinCont_succ_eq hα n, ← Ioc_union_Ioi_eq_Ioi hx0.le,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((hS.integrableOn_pow_mul_rem_succ hα n).mono_set Ioc_subset_Ioi_self)
        ((hS.integrableOn_pow_mul_rem_succ hα n).mono_set (Ioi_subset_Ioi hx0.le)),
      integral_Ioc_eq_integral_Ioo]
  -- Step F: the regularized beta identity, cast to `ℂ`
  have hG : ∀ i ∈ Finset.range (n + 1), X i * W i =
      ((Ring.choose (μ - 1) i * (-1) ^ i * (x ^ (μ - n - α) / ((i : ℝ) - n - α + 1)) : ℝ) : ℂ) := by
    intro i _
    rw [hX, hW]
    simp only
    rw [← ofReal_mul]
    congr 1
    rw [show x ^ (μ - n - α) = x ^ (μ - 1 - i) * x ^ ((i : ℝ) - n - α + 1) by
      rw [← Real.rpow_add hx0]; congr 1; ring]
    ring
  have hFint : ((∫ t in Ioo (0 : ℝ) x,
      fracKer μ (n + 1) x t * t ^ (((n + 1 : ℕ) : ℝ) - n - α) : ℝ) : ℂ) =
      ∫ t in Ioo (0 : ℝ) x, K (n + 1) t * (t : ℂ) ^ (n + 1) * (t : ℂ) ^ (-((n : ℂ) + α)) := by
    rw [show ((∫ t in Ioo (0 : ℝ) x, fracKer μ (n + 1) x t * t ^ (((n + 1 : ℕ) : ℝ) - n - α) : ℝ) :
      ℂ) = @RCLike.ofReal ℂ _ (∫ t in Ioo (0 : ℝ) x,
        fracKer μ (n + 1) x t * t ^ (((n + 1 : ℕ) : ℝ) - n - α)) from rfl, ← integral_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    change ((fracKer μ (n + 1) x t * t ^ (((n + 1 : ℕ) : ℝ) - n - α) : ℝ) : ℂ) = _
    rw [ofReal_mul, ofReal_cpow ht.1.le, hK]
    simp only
    rw [mul_assoc, ← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr ht.1.ne')]
    congr 2
    push_cast
    ring
  have hF := congrArg (fun r : ℝ => (r : ℂ))
    (dlmf_2_6_39_reg hμ hα0 hα (s := n) (n := n + 1) (Nat.lt_succ_self n) hx0)
  rw [ofReal_add, ofReal_sum, hFint, ← Finset.sum_congr rfl hG,
    Finset.sum_range_succ] at hF
  -- assemble
  simp only [fracRem]
  rw [Finset.sum_range_succ, hA, hB, hC, hCval, hsum]
  linear_combination (a n) * hF + X n * hE

/-! ### 2.6.45 -/

/-- **DLMF 2.6.45, moment form**: for `x → +∞`,
`Γ(μ) I^μ f(x) = ∑_{s<n} aₛ Γ(μ)Γ(1−s−α)/Γ(μ+1−s−α) x^{μ−s−α}
  + ∑_{i<n} binom(μ−1,i)(−1)^i x^{μ−1−i} 𝓜f(i+1) + fracRem n x`. -/
theorem dlmf_2_6_45_moments (hμ : 0 < μ) (hα : α < 1) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, Gamma μ * fracIntegral (μ : ℂ) f x =
      ∑ s ∈ Finset.range n, a s * ((Real.Gamma μ * Real.Gamma (1 - s - α) /
        Real.Gamma (μ + 1 - s - α) * x ^ (μ - s - α) : ℝ) : ℂ) +
      ∑ i ∈ Finset.range n, ((Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) : ℝ) : ℂ) *
        mellinCont f a α ((i : ℂ) + 1) +
      fracRem μ f a α n x := by
  induction n with
  | zero =>
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [fracRem_zero hμ hx]
  | succ n ih =>
    filter_upwards [ih, hS.fracRem_succ hμ hα n] with x hx hrec
    rw [hx, hrec, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

omit hS in
/-- `binom(μ−1, i)/Γ(μ) = 1/(i! Γ(μ−i))` for `μ > 0` (both sides vanish when `μ ∈ {1, …, i}`). -/
theorem choose_div_Gamma (i : ℕ) :
    Ring.choose (μ - 1) i / Real.Gamma μ = 1 / (i ! * Real.Gamma (μ - i)) := by
  have hC : Ring.choose (μ - 1) i = (∏ j ∈ Finset.range i, (μ - 1 - j)) / i ! := by
    have h := dlmf_1_2_6 ((μ - 1 : ℝ) : ℂ) i
    apply ofReal_injective
    push_cast at h ⊢
    exact h
  by_cases hz : ∃ j ∈ Finset.range i, μ - 1 - j = 0
  · obtain ⟨j, hj, hj0⟩ := hz
    have hji : j < i := Finset.mem_range.mp hj
    rw [hC, Finset.prod_eq_zero hj hj0, zero_div, zero_div]
    have : μ - i = -((i - (j + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hji]
      push_cast
      linarith
    rw [this, Real.Gamma_neg_nat_eq_zero, mul_zero, div_zero]
  · push Not at hz
    have hne : ∀ j < i, ((μ - i : ℝ) : ℂ) + j ≠ 0 := fun j hj h => by
      have := congrArg Complex.re h
      simp at this
      refine hz (i - 1 - j) (Finset.mem_range.mpr (by omega)) ?_
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      linarith
    have hΓ := Gamma_add_nat_eq_prod_mul ((μ - i : ℝ) : ℂ) i hne
    rw [show ((μ - i : ℝ) : ℂ) + i = (μ : ℂ) by push_cast; ring, Gamma_ofReal, Gamma_ofReal] at hΓ
    have hprod : ∏ j ∈ Finset.range i, (((μ - i : ℝ) : ℂ) + j) =
        ((∏ j ∈ Finset.range i, (μ - 1 - j) : ℝ) : ℂ) := by
      rw [← Finset.prod_range_reflect (fun j => (((μ - i : ℝ) : ℂ) + j)) i, ofReal_prod]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hji := Finset.mem_range.mp hj
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    have hΓ' : Real.Gamma μ = (∏ j ∈ Finset.range i, (μ - 1 - j)) * Real.Gamma (μ - i) := by
      apply ofReal_injective
      rw [ofReal_mul, ← hprod]
      exact hΓ
    have hP : (∏ j ∈ Finset.range i, (μ - 1 - j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hz
    have hf : (i ! : ℝ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    rw [hC, hΓ']
    field_simp

/-- **DLMF 2.6.45**: for `0 < α < 1`, real `μ > 0` and `x → +∞`,
`I^μ f(x) = ∑_{s<n} aₛ Γ(1−s−α)/Γ(μ+1−s−α) x^{μ−s−α} − ∑_{s=1}^n cₛ/Γ(μ+1−s) x^{μ−s}
  + x^{−n} δₙ(x)`, with `cₛ` from 2.6.18 and `δₙ = fracRemDelta` (`= O(x^{μ−α})`,
  `fracRemDelta_isBigO`). -/
theorem dlmf_2_6_45 (hμ : 0 < μ) (hα : α < 1) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, fracIntegral (μ : ℂ) f x =
      ∑ s ∈ Finset.range n, a s * (Gamma (1 - s - α) / Gamma ((μ : ℂ) + 1 - s - α)) *
        (x : ℂ) ^ ((μ : ℂ) - s - α) -
      ∑ s ∈ Finset.Icc 1 n, stieltjesC f a α s / Gamma ((μ : ℂ) + 1 - s) * (x : ℂ) ^ ((μ : ℂ) - s) +
      (x : ℂ) ^ (-(n : ℂ)) * fracRemDelta μ f a α n x := by
  filter_upwards [hS.dlmf_2_6_45_moments hμ hα n, eventually_gt_atTop 0] with x hx hx0
  have hΓR : Real.Gamma μ ≠ 0 := (Real.Gamma_pos_of_pos hμ).ne'
  have hΓ : Gamma (μ : ℂ) ≠ 0 := by rw [Gamma_ofReal]; exact_mod_cast hΓR
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  -- the first sum
  have e1 : ∀ s : ℕ, a s * ((Real.Gamma μ * Real.Gamma (1 - s - α) / Real.Gamma (μ + 1 - s - α) *
      x ^ (μ - s - α) : ℝ) : ℂ) / Gamma μ =
      a s * (Gamma (1 - s - α) / Gamma ((μ : ℂ) + 1 - s - α)) * (x : ℂ) ^ ((μ : ℂ) - s - α) := by
    intro s
    rw [ofReal_mul, ofReal_cpow hx0.le, ofReal_div, ofReal_mul, ← Gamma_ofReal, ← Gamma_ofReal,
      ← Gamma_ofReal]
    push_cast
    field_simp
  -- the second sum
  have e2 : ∀ i : ℕ, ((Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) : ℝ) : ℂ) *
      mellinCont f a α ((i : ℂ) + 1) / Gamma μ =
      -(stieltjesC f a α (i + 1) / Gamma ((μ : ℂ) + 1 - ((i + 1 : ℕ) : ℂ)) *
        (x : ℂ) ^ ((μ : ℂ) - ((i + 1 : ℕ) : ℂ))) := by
    intro i
    have hcd := choose_div_Gamma (μ := μ) i
    have hcd' : ((Ring.choose (μ - 1) i : ℝ) : ℂ) / Gamma μ =
        1 / ((i ! : ℂ) * Gamma ((μ : ℂ) - i)) := by
      rw [Gamma_ofReal, show (μ : ℂ) - i = ((μ - i : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal]
      exact_mod_cast hcd
    rw [stieltjesC, Nat.add_sub_cancel, ofReal_mul, ofReal_mul, ofReal_cpow hx0.le]
    push_cast at hcd' ⊢
    rw [show ((μ : ℂ) - 1 - i) = (μ : ℂ) - (i + 1) by ring,
      show (μ : ℂ) + 1 - (i + 1) = μ - i by ring]
    linear_combination ((-1 : ℂ) ^ i * (x : ℂ) ^ ((μ : ℂ) - (i + 1)) *
      mellinCont f a α ((i : ℂ) + 1)) * hcd'
  have hI : fracIntegral (μ : ℂ) f x =
      (∑ s ∈ Finset.range n, a s * ((Real.Gamma μ * Real.Gamma (1 - s - α) /
        Real.Gamma (μ + 1 - s - α) * x ^ (μ - s - α) : ℝ) : ℂ) / Gamma μ) +
      (∑ i ∈ Finset.range n, ((Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) : ℝ) : ℂ) *
        mellinCont f a α ((i : ℂ) + 1) / Gamma μ) +
      fracRem μ f a α n x / Gamma μ := by
    rw [← Finset.sum_div, ← Finset.sum_div, ← add_div, ← add_div, ← hx,
      mul_div_cancel_left₀ _ hΓ]
  rw [hI, Finset.sum_congr rfl fun s _ => e1 s, Finset.sum_congr rfl fun i _ => e2 i,
    Finset.sum_neg_distrib, fracRemDelta, ← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  have hre : ∀ k ∈ Finset.range n,
      stieltjesC f a α (1 + k) / Gamma ((μ : ℂ) + 1 - ((1 + k : ℕ) : ℂ)) *
        (x : ℂ) ^ ((μ : ℂ) - ((1 + k : ℕ) : ℂ)) =
      stieltjesC f a α (k + 1) / Gamma ((μ : ℂ) + 1 - ((k + 1 : ℕ) : ℂ)) *
        (x : ℂ) ^ ((μ : ℂ) - ((k + 1 : ℕ) : ℂ)) := fun k _ => by rw [add_comm 1 k]
  rw [Finset.sum_congr rfl hre, cpow_neg, cpow_natCast]
  have hxn : (x : ℂ) ^ n ≠ 0 := pow_ne_zero n hxC
  field_simp
  ring

/-! ### The remainder estimate -/

omit hS in
/-- `∫₀^x (C₁ + C₂ (1 − t/x)^{μ−1}) t^{−α} dt = x^{1−α} ∫₀¹ (C₁ + C₂ (1−u)^{μ−1}) u^{−α} du`, with
both integrals convergent. -/
theorem integral_kernel_weight {μ α C₁ C₂ : ℝ} (hμ : 0 < μ) (hα1 : α < 1) {x : ℝ}
    (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (C₁ + C₂ * (1 - t / x) ^ (μ - 1)) * t ^ (-α)) (Ioo 0 x) ∧
    (∫ t in Ioo (0 : ℝ) x, (C₁ + C₂ * (1 - t / x) ^ (μ - 1)) * t ^ (-α)) =
      x ^ (1 - α) * ∫ u in Ioo (0 : ℝ) 1, (C₁ + C₂ * (1 - u) ^ (μ - 1)) * u ^ (-α) := by
  -- the unit-interval integrand is integrable
  have hEint : IntegrableOn (fun u : ℝ => (C₁ + C₂ * (1 - u) ^ (μ - 1)) * u ^ (-α)) (Ioo 0 1) := by
    have h1 : IntegrableOn (fun u : ℝ => u ^ (-α)) (Ioo 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have h2 : IntegrableOn (fun u : ℝ => (1 - u) ^ (μ - 1) * u ^ (-α)) (Ioo 0 1) := by
      have := betaIntegral_convergent (u := ((1 - α : ℝ) : ℂ)) (v := (μ : ℂ)) (by simp; linarith)
        (by simpa using hμ)
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at this
      refine IntegrableOn.congr_fun this.norm (fun u hu => ?_) measurableSet_Ioo
      have e : (1 - (u : ℂ)) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu.1, e,
        norm_cpow_eq_rpow_re_of_pos (by linarith [hu.2])]
      simp only [sub_re, ofReal_re, one_re]
      rw [mul_comm]
      congr 2
      ring
    exact IntegrableOn.congr_fun ((h1.const_mul C₁).add (h2.const_mul C₂))
      (fun u _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioo
  -- substitution `t = x u`
  set g : ℝ → ℝ := fun u => (C₁ + C₂ * (1 - u) ^ (μ - 1)) * u ^ (-α) with hg
  have hpt : ∀ t ∈ Ioo (0 : ℝ) x, (C₁ + C₂ * (1 - t / x) ^ (μ - 1)) * t ^ (-α) =
      x ^ (-α) * g (t / x) := by
    intro t ht
    rw [hg]
    simp only
    rw [Real.div_rpow ht.1.le hx.le, Real.rpow_neg hx.le, Real.rpow_neg ht.1.le]
    have : x ^ α ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    field_simp
  have hg_int : IntegrableOn (fun t : ℝ => g (t / x)) (Ioo 0 x) := by
    have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hEint
    have h' := h.comp_mul_left (c := x⁻¹)
    rw [div_inv_eq_mul, div_inv_eq_mul, zero_mul, one_mul] at h'
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le] at h'
    refine h'.congr_fun (fun t _ => ?_) measurableSet_Ioo
    rw [div_eq_inv_mul]
  refine ⟨IntegrableOn.congr_fun (hg_int.const_mul _) (fun t ht => (hpt t ht).symm)
    measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le,
    intervalIntegral.integral_comp_div g hx.ne', zero_div, div_self hx.ne', intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    smul_eq_mul, ← mul_assoc, ← Real.rpow_add_one hx.ne']
  congr 2
  ring

/-- **The remainder estimate**: `fracRem n x = O(x^{μ−n−α})` as `x → +∞`. -/
theorem fracRem_isBigO (hμ : 0 < μ) (hα : α < 1) (n : ℕ) :
    (fun x : ℝ => fracRem μ f a α n x) =O[atTop] fun x => x ^ (μ - n - α) := by
  obtain ⟨B, C₁, C₂, hB0, hC₁, hC₂, hK⟩ := fracKer_bound μ n
  obtain ⟨C, hC⟩ := (hS.rem_isBigO n).bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hC
  set T := max T₀ 1 with hT
  have hT1 : 1 ≤ T := le_max_right _ _
  have hT0 : 0 < T := by linarith
  have hα0 := hS.α_pos
  have hC0 : 0 ≤ C := by
    have := hT₀ T (le_max_left _ _)
    have h2 : 0 < ‖T ^ (-(n + α))‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hT0.le _)]
      exact Real.rpow_pos_of_pos hT0 _
    nlinarith [norm_nonneg (stieltjesRem f a α n T)]
  have hrem : ∀ t, T ≤ t → ‖stieltjesRem f a α n t‖ ≤ C * t ^ (-(n + α)) := fun t ht => by
    have h := hT₀ t (le_trans (le_max_left _ _) ht)
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at h
  set D : ℝ := ∫ t in Ioc 0 T, ‖(t : ℂ) ^ n * stieltjesRem f a α n t‖ with hD
  have hD0 : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  have hDint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * stieltjesRem f a α n t) (Ioc 0 T) :=
    hS.integrableOn_Ioc_pow_mul_rem' n n (by linarith) T
  set E : ℝ := ∫ u in Ioo (0 : ℝ) 1, (C₁ + C₂ * (1 - u) ^ (μ - 1)) * u ^ (-α) with hE
  have hE0 : 0 ≤ E := setIntegral_nonneg measurableSet_Ioo fun u hu =>
    mul_nonneg (add_nonneg hC₁ (mul_nonneg hC₂ (Real.rpow_nonneg (by linarith [hu.2]) _)))
      (Real.rpow_nonneg hu.1.le _)
  set S : ℝ := ∑ i ∈ Finset.range n, |Ring.choose (μ - 1) i| * C / (n + α - i - 1) with hS'
  refine IsBigO.of_bound (B * D + C * E + S) ?_
  filter_upwards [eventually_ge_atTop (2 * T)] with x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hTx : T < x := by linarith
  have hT2 : T ≤ x / 2 := by linarith
  obtain ⟨hKa, hKb⟩ := hK x hx0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have hxp : 0 < x ^ (μ - 1 - n) := Real.rpow_pos_of_pos hx0 _
  -- integrability of the kernel term
  have hJint : IntegrableOn
      (fun t : ℝ => (fracKer μ n x t : ℂ) * (t : ℂ) ^ n * stieltjesRem f a α n t) (Ioo 0 x) :=
    integrableOn_fracKer_mul hμ n hx0 (hS.aestronglyMeasurable_rem n)
      (hS.integrableOn_Ioc_pow_mul_rem' n n (by linarith) _) ⟨C, fun t ht =>
        (hrem t (by linarith [ht.1])).trans (mul_le_of_le_one_right hC0
          (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by linarith)))⟩
  obtain ⟨hGint, hGval⟩ := integral_kernel_weight (C₁ := C₁) (C₂ := C₂) hμ hα hx0
  -- the kernel integral
  have hJ : ‖∫ t in Ioo (0 : ℝ) x, (fracKer μ n x t : ℂ) * (t : ℂ) ^ n * stieltjesRem f a α n t‖ ≤
      x ^ (μ - 1 - n) * B * D + x ^ (μ - 1 - n) * C * (x ^ (1 - α) * E) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← Ioc_union_Ioo_eq_Ioo hT0.le hTx, setIntegral_union
      (Ioc_disjoint_Ioi_same.mono_right Ioo_subset_Ioi_self) measurableSet_Ioo
      (IntegrableOn.mono_set hJint.norm (Ioc_union_Ioo_eq_Ioo hT0.le hTx ▸ subset_union_left))
      (IntegrableOn.mono_set hJint.norm (Ioc_union_Ioo_eq_Ioo hT0.le hTx ▸ subset_union_right))]
    refine add_le_add ?_ ?_
    · rw [hD, ← integral_const_mul]
      refine setIntegral_mono_on
        (IntegrableOn.mono_set hJint.norm (Ioc_union_Ioo_eq_Ioo hT0.le hTx ▸ subset_union_left))
        (hDint.norm.const_mul _) measurableSet_Ioc fun t ht => ?_
      rw [mul_assoc, norm_mul, norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hKa t ⟨ht.1, by linarith [ht.2]⟩) (norm_nonneg _)
    · rw [← hGval, ← integral_const_mul]
      calc (∫ t in Ioo T x, ‖(fracKer μ n x t : ℂ) * (t : ℂ) ^ n * stieltjesRem f a α n t‖)
          ≤ ∫ t in Ioo T x,
              x ^ (μ - 1 - n) * C * ((C₁ + C₂ * (1 - t / x) ^ (μ - 1)) * t ^ (-α)) := by
            refine setIntegral_mono_on (IntegrableOn.mono_set hJint.norm
              (Ioc_union_Ioo_eq_Ioo hT0.le hTx ▸ subset_union_right))
              (IntegrableOn.mono_set (hGint.const_mul _) fun t ht => ⟨by linarith [ht.1], ht.2⟩)
              measurableSet_Ioo fun t ht => ?_
            have ht0 : 0 < t := by linarith [ht.1]
            rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, norm_pow, norm_real,
              Real.norm_of_nonneg ht0.le]
            have h1 := hKb t ⟨ht0, ht.2⟩
            have h2 := hrem t ht.1.le
            have e : t ^ n * (C * t ^ (-(n + α))) = C * t ^ (-α) := by
              rw [← Real.rpow_natCast, ← mul_assoc, mul_comm (t ^ (n : ℝ)), mul_assoc,
                ← Real.rpow_add ht0]
              congr 2
              ring
            calc |fracKer μ n x t| * t ^ n * ‖stieltjesRem f a α n t‖
                ≤ x ^ (μ - 1 - n) * (C₁ + C₂ * (1 - t / x) ^ (μ - 1)) *
                    (t ^ n * (C * t ^ (-(n + α)))) := by
                  rw [mul_assoc]
                  refine mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (pow_nonneg ht0.le n))
                    (by positivity) ?_
                  exact mul_nonneg hxp.le (add_nonneg hC₁ (mul_nonneg hC₂ (Real.rpow_nonneg
                    (by rw [sub_nonneg, div_le_one hx0]; exact ht.2.le) _)))
              _ = _ := by rw [e]; ring
        _ ≤ ∫ t in Ioo 0 x,
              x ^ (μ - 1 - n) * C * ((C₁ + C₂ * (1 - t / x) ^ (μ - 1)) * t ^ (-α)) := by
            refine setIntegral_mono_set (hGint.const_mul _) ?_
              (show Ioo T x ⊆ Ioo 0 x from fun t ht => ⟨by linarith [ht.1], ht.2⟩).eventuallyLE
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
            exact mul_nonneg (mul_nonneg hxp.le hC0) (mul_nonneg (add_nonneg hC₁ (mul_nonneg hC₂
              (Real.rpow_nonneg (by rw [sub_nonneg, div_le_one hx0]; exact ht.2.le) _)))
              (Real.rpow_nonneg ht.1.le _))
  -- the tails
  have hTail : ∀ i ∈ Finset.range n,
      ‖((Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) : ℝ) : ℂ) *
        ∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α n t‖ ≤
      |Ring.choose (μ - 1) i| * C / (n + α - i - 1) * x ^ (μ - n - α) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hi
    have hexp : (i : ℝ) - n - α < -1 := by linarith
    have hden : 0 < (n : ℝ) + α - i - 1 := by linarith
    have hint := hS.integrableOn_Ioi_pow_mul_rem_tail (Finset.mem_range.mp hi) hx1
    have htail : ‖∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α n t‖ ≤
        C * (x ^ ((i : ℝ) - n - α + 1) / (n + α - i - 1)) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      calc (∫ t in Ioi x, ‖(t : ℂ) ^ i * stieltjesRem f a α n t‖)
          ≤ ∫ t in Ioi x, C * t ^ ((i : ℝ) - n - α) := by
            refine setIntegral_mono_on hint.norm
              ((integrableOn_Ioi_rpow_of_lt hexp hx0).const_mul C) measurableSet_Ioi
              fun t ht => ?_
            have hxt : x < t := ht
            have ht0 : 0 < t := lt_trans hx0 hxt
            rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg ht0.le]
            calc t ^ i * ‖stieltjesRem f a α n t‖ ≤ t ^ i * (C * t ^ (-(n + α))) :=
                  mul_le_mul_of_nonneg_left (hrem t (by linarith)) (pow_nonneg ht0.le i)
              _ = C * t ^ ((i : ℝ) - n - α) := by
                  rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add ht0]
                  congr 2
                  ring
        _ = C * (x ^ ((i : ℝ) - n - α + 1) / (n + α - i - 1)) := by
            rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp hx0, neg_div, ← div_neg]
            congr 2
            ring
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, mul_one, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    calc |Ring.choose (μ - 1) i| * x ^ (μ - 1 - i) *
          ‖∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α n t‖
        ≤ |Ring.choose (μ - 1) i| * x ^ (μ - 1 - i) *
          (C * (x ^ ((i : ℝ) - n - α + 1) / (n + α - i - 1))) := by gcongr
      _ = |Ring.choose (μ - 1) i| * C / (n + α - i - 1) *
          (x ^ (μ - 1 - i) * x ^ ((i : ℝ) - n - α + 1)) := by ring
      _ = _ := by
          rw [← Real.rpow_add hx0]
          congr 2
          ring
  -- assemble
  have hpow1 : x ^ (μ - 1 - n) ≤ x ^ (μ - n - α) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpow2 : x ^ (μ - 1 - n) * x ^ (1 - α) = x ^ (μ - n - α) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hsum : ‖∑ i ∈ Finset.range n,
      ((Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) : ℝ) : ℂ) *
        ∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α n t‖ ≤ S * x ^ (μ - n - α) := by
    refine (norm_sum_le _ _).trans ?_
    rw [hS', Finset.sum_mul]
    exact Finset.sum_le_sum hTail
  calc ‖fracRem μ f a α n x‖ ≤ ‖∫ t in Ioo (0 : ℝ) x, (fracKer μ n x t : ℂ) * (t : ℂ) ^ n *
        stieltjesRem f a α n t‖ + ‖∑ i ∈ Finset.range n,
          ((Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) : ℝ) : ℂ) *
            ∫ t in Ioi x, (t : ℂ) ^ i * stieltjesRem f a α n t‖ := norm_sub_le _ _
    _ ≤ (x ^ (μ - 1 - n) * B * D + x ^ (μ - 1 - n) * C * (x ^ (1 - α) * E)) + S * x ^ (μ - n - α) :=
        add_le_add hJ hsum
    _ ≤ (B * D + C * E + S) * x ^ (μ - n - α) := by
        have : x ^ (μ - 1 - n) * B * D ≤ B * D * x ^ (μ - n - α) := by
          rw [mul_comm (B * D)]
          exact mul_le_mul_of_nonneg_right hpow1 (mul_nonneg hB0 hD0) |> fun h => by
            simpa [mul_assoc, mul_comm, mul_left_comm] using h
        have h2 : x ^ (μ - 1 - n) * C * (x ^ (1 - α) * E) = C * E * x ^ (μ - n - α) := by
          rw [← hpow2]
          ring
        rw [h2]
        nlinarith

/-- `δₙ(x) = O(x^{μ−α})`: the remainder `x^{−n} δₙ(x)` of 2.6.45 is `O(x^{μ−n−α})`. -/
theorem fracRemDelta_isBigO (hμ : 0 < μ) (hα : α < 1) (n : ℕ) :
    (fun x : ℝ => fracRemDelta μ f a α n x) =O[atTop] fun x => x ^ (μ - α) := by
  have h2 : (fun x : ℝ => (x : ℂ) ^ n) =O[atTop] fun x => x ^ (n : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_pow, norm_real, Real.norm_of_nonneg hx.le,
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _), Real.rpow_natCast, one_mul]
  have h := ((hS.fracRem_isBigO hμ hα n).const_mul_left (Gamma (μ : ℂ))⁻¹).mul h2
  refine h.congr' (Eventually.of_forall fun x => ?_) ?_
  · simp only [fracRemDelta]
    ring
  · filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_add hx]
    congr 1
    ring

end StieltjesSetup

end Azurite.DLMF
