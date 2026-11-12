/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11RatioFormal
import Azurite.DLMF.Chapter5.Section11Shift

/-!
# DLMF §5.11(iii): `Γ(z + a)/Γ(z + b)` from 5.11.8

By 5.11.8, `Γ(z + a)/Γ(z + b) = z^{a−b} exp(R_a(z) − R_b(z))` for large `z` in
`|ph z| ≤ π − δ` (`gammaRatio_eq`), and `R_a − R_b ∼ ∑ (c_a − c_b)ₛ z^{−s}`; exponentiating
(`HasPowExpansion.cexp'`, the complex counterpart of `isAsympExpansion_cexp`) gives
`z^{b−a} Γ(z + a)/Γ(z + b) ∼ ∑ eₖ(a, b) z^{−k}` with `e = cSeriesExp (c_a − c_b)`
(`isAsympExpansion_gammaRatio_exp`). The coefficients are identified with DLMF's `Gₖ(a, b)` in
`Section11Ratio.lean`.
-/

open Complex Filter Topology Set Asymptotics PowerSeries
open scoped Real

namespace Azurite.DLMF

/-! ### Exponentiating an expansion -/

/-- `eʷ ∼ ∑ wᵏ/k!` as `w → 0`. -/
theorem hasPowExpansion_cexp_zero : HasPowExpansion (𝓝 (0 : ℂ)) id cexp (exp ℂ) := fun n => by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [trunc_zero', Polynomial.eval_zero, sub_zero, pow_zero]
    exact (continuous_exp.tendsto 0).isBigO_one ℂ
  refine IsBigO.of_bound ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with w hw
  have hw1 : ‖w‖ ≤ 1 := by simpa using hw
  have hsum : (trunc n (exp ℂ)).eval (id w) = ∑ m ∈ Finset.range n, w ^ m / m.factorial := by
    rw [eval_trunc_eq_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [coeff_exp, id, map_div₀, map_one, map_natCast]
    ring
  rw [hsum, id, norm_pow, mul_comm]
  exact Complex.exp_bound hw1 hn

theorem constantCoeff_subst_exp {a : ℕ → ℂ} (ha : a 0 = 0) :
    constantCoeff ((exp ℂ).subst (mk a)) = 1 := by
  have h0 : constantCoeff (mk a) = 0 := by simpa using ha
  have h := constantCoeff_subst_of_constantCoeff_zero (S := ℂ) h0 (exp ℂ)
  rw [show constantCoeff (exp ℂ) = 1 by simp, map_one] at h
  exact h

/-- `exp(∑ aₖ Xᵏ)` by substitution is the formal exponential `expPS a`. -/
theorem subst_exp_eq_expPS {a : ℕ → ℂ} (ha : a 0 = 0) : (exp ℂ).subst (mk a) = expPS a := by
  have h0 : constantCoeff (mk a) = 0 := by simpa using ha
  have hs : HasSubst (mk a) := HasSubst.of_constantCoeff_zero' h0
  refine eq_expPS_of_derivative a (constantCoeff_subst_exp ha) ?_
  rw [derivative_subst hs, derivative_exp', mul_comm]

/-- **The exponential of an expansion**: `f ∼ ∑ aₖ yᵏ` with `a₀ = 0` gives
`e^f ∼ ∑ bₖ yᵏ`, `b = cSeriesExp a`. -/
theorem HasPowExpansion.cexp' {α : Type*} {l : Filter α} {y f : α → ℂ}
    (hy : Tendsto y l (𝓝 0)) {a : ℕ → ℂ} (ha : a 0 = 0) (hf : HasPowExpansion l y f (mk a)) :
    HasPowExpansion l y (fun x => cexp (f x)) (expPS a) := by
  rw [← subst_exp_eq_expPS ha]
  exact HasPowExpansion.subst hy hasPowExpansion_cexp_zero hf (by simpa using ha)

/-! ### The ratio -/

/-- `Γ(z + a)/Γ(z + b) = z^{a−b} exp(R_a(z) − R_b(z))` (5.11.8). -/
theorem gammaRatio_eq {a b z : ℂ} (hz : z ≠ 0) (ha : z + a ∈ slitPlane)
    (hb : z + b ∈ slitPlane) :
    Gamma (z + a) / Gamma (z + b) =
      z ^ (a - b) * cexp (lnGammaShiftRem a z - lnGammaShiftRem b z) := by
  rw [Gamma_add_eq_exp_lnGammaShiftRem ha, Gamma_add_eq_exp_lnGammaShiftRem hb, ← Complex.exp_sub,
    cpow_def_of_ne_zero hz, ← Complex.exp_add]
  congr 1
  ring

/-- The log coefficients `c_a − c_b` of 5.11.8. -/
noncomputable def ratioLogCoeff (a b : ℂ) (s : ℕ) : ℂ :=
  lnGammaShiftCoeff a s - lnGammaShiftCoeff b s

/-- The exponentiated coefficients. -/
noncomputable def ratioExpCoeff (a b : ℂ) : ℕ → ℂ := cSeriesExp (ratioLogCoeff a b)

theorem ratioLogCoeff_zero (a b : ℂ) : ratioLogCoeff a b 0 = 0 := by
  simp [ratioLogCoeff, lnGammaShiftCoeff]

theorem mem_slitPlane_of_abs_arg_le {w : ℂ} (hw : w ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (h : |arg w| ≤ π - δ / 2) : w ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg]
  refine ⟨fun hπ => ?_, hw⟩
  rw [hπ, abs_of_pos Real.pi_pos] at h
  linarith

/-- `z^{b−a} Γ(z + a)/Γ(z + b) ∼ ∑ eₖ(a, b) z^{−k}` in `|ph z| ≤ π − δ`. -/
theorem isAsympExpansion_gammaRatio_exp (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ))
      (fun z => Gamma (z + a) / Gamma (z + b) / z ^ (a - b)) (ratioExpCoeff a b) := by
  rw [isAsympExpansionDLMF_iff]
  set l := Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))
  have hy : Tendsto (fun z : ℂ => z⁻¹) l (𝓝 0) := tendsto_inv_atInf _
  have hA := isAsympExpansionDLMF_iff.mp (dlmf_5_11_8 a hδ hδπ).2
  have hB := isAsympExpansionDLMF_iff.mp (dlmf_5_11_8 b hδ hδπ).2
  have hS : HasPowExpansion l (fun z => z⁻¹)
      (fun z => lnGammaShiftRem a z - lnGammaShiftRem b z) (mk (ratioLogCoeff a b)) := by
    have := hA.sub hB
    have e : mk (lnGammaShiftCoeff a) - mk (lnGammaShiftCoeff b) = mk (ratioLogCoeff a b) := by
      ext; simp [ratioLogCoeff]
    rw [e] at this
    exact this
  have hE := hS.cexp' hy (ratioLogCoeff_zero a b)
  refine hE.congr' ?_
  filter_upwards [eventually_shift_sector hδ a, eventually_shift_sector hδ b] with z hza hzb
  obtain ⟨hz0, ha0, -, haarg⟩ := hza
  obtain ⟨-, hb0, -, hbarg⟩ := hzb
  rw [gammaRatio_eq hz0 (mem_slitPlane_of_abs_arg_le ha0 hδ haarg)
    (mem_slitPlane_of_abs_arg_le hb0 hδ hbarg), mul_div_cancel_left₀ _
    (by rw [Ne, cpow_eq_zero_iff]; tauto)]

end Azurite.DLMF
