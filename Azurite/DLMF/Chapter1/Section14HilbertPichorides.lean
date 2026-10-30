/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Hilbert

/-!
# DLMF 1.14.45: Pichorides' elementary inequality

For `1 < p ≤ 2`, `A_p = tan(π/2p)` and `B_p = sin^{p−1}(π/2p)/cos(π/2p)`:
`|b|^p + B_p Re((|a| + ib)^p) ≤ A_p^p |a|^p` for real `a`, `b` (`pichorides_ineq`). In polar form
this is `sin^p θ + B_p cos pθ ≤ A_p^p cos^p θ` on `[0, π/2]` (`pichorides_trig`). The proof shows
that `G(θ) = (sin^p θ + B_p cos pθ)/cos^p θ` increases up to `θ₀ = π/2p` and decreases after it. The
sign of `G′` is that of `sin^{p−1}θ − B_p sin((p − 1)θ)`, which changes at `θ₀` because
`log sin((p − 1)θ) − (p − 1) log sin θ` is monotone (`monotoneOn_log_sin_ratio`).
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace Azurite.DLMF

/-- Pichorides' constant `A_p = tan(π/2p)` (the norm of `ℋ` on `L^p` for `1 < p ≤ 2`). -/
noncomputable def pichoridesA (p : ℝ) : ℝ := Real.tan (π / (2 * p))

/-- The auxiliary constant `B_p = sin^{p−1}(π/2p) / cos(π/2p)`. -/
noncomputable def pichoridesB (p : ℝ) : ℝ :=
  Real.sin (π / (2 * p)) ^ (p - 1) / Real.cos (π / (2 * p))

/-- `Re(w^p) = |w|^p cos(p arg w)`. -/
theorem re_cpow_ofReal (w : ℂ) (hw : w ≠ 0) (p : ℝ) :
    (w ^ (p : ℂ)).re = ‖w‖ ^ p * Real.cos (p * arg w) := by
  rw [cpow_def_of_ne_zero hw, Complex.exp_re]
  have h1 : (Complex.log w * p).re = Real.log ‖w‖ * p := by
    simp [Complex.log_re]
  have h2 : (Complex.log w * p).im = arg w * p := by
    simp [Complex.log_im]
  rw [h1, h2, Real.rpow_def_of_pos (norm_pos_iff.mpr hw), mul_comm (arg w)]

section Trig

variable {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2)
include hp1 hp2

omit hp2 in
theorem pichorides_theta0_mem : 0 < π / (2 * p) ∧ π / (2 * p) < π / 2 := by
  have hπ := Real.pi_pos
  refine ⟨by positivity, ?_⟩
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `log sin(αθ) − α log sin θ` is monotone on `(0, π/2)` for `α = p − 1 ∈ (0, 1]`. -/
theorem monotoneOn_log_sin_ratio :
    MonotoneOn (fun θ => Real.log (Real.sin ((p - 1) * θ)) - (p - 1) * Real.log (Real.sin θ))
      (Ioo 0 (π / 2)) := by
  have hα0 : 0 < p - 1 := by linarith
  have hα1 : p - 1 ≤ 1 := by linarith
  have hsin : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), 0 < Real.sin θ ∧ 0 < Real.sin ((p - 1) * θ) :=
    fun θ hθ => by
      have hπ := Real.pi_pos
      refine ⟨Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2]), ?_⟩
      exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hθ.1])
        (by nlinarith [hθ.1, hθ.2])
  have hd : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), HasDerivAt
      (fun θ => Real.log (Real.sin ((p - 1) * θ)) - (p - 1) * Real.log (Real.sin θ))
      ((p - 1) * (Real.cos ((p - 1) * θ) / Real.sin ((p - 1) * θ) -
        Real.cos θ / Real.sin θ)) θ := fun θ hθ => by
    obtain ⟨h1, h2⟩ := hsin θ hθ
    have e1 := ((Real.hasDerivAt_sin ((p - 1) * θ)).comp θ
      ((hasDerivAt_id θ).const_mul (p - 1))).log h2.ne'
    have e2 := ((Real.hasDerivAt_sin θ).log h1.ne').const_mul (p - 1)
    exact (e1.sub e2).congr_deriv (by simp only [Function.comp_apply]; ring)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo _ _)
    (fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt)
    (fun θ hθ => (hd θ (interior_subset hθ)).hasDerivWithinAt) (fun θ hθ => ?_)
  rw [interior_Ioo] at hθ
  obtain ⟨h1, h2⟩ := hsin θ hθ
  refine mul_nonneg hα0.le ?_
  rw [sub_nonneg, div_le_div_iff₀ h1 h2]
  have : 0 ≤ Real.sin (θ - (p - 1) * θ) := by
    have hπ := Real.pi_pos
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [hθ.1])
      (by nlinarith [hθ.1, hθ.2])
  rw [Real.sin_sub] at this
  linarith

/-- The sign of `sin^{p−1} θ − B_p sin((p − 1)θ)` changes at `θ₀ = π/2p`. -/
theorem pichorides_sign (θ : ℝ) (hθ : θ ∈ Ioo 0 (π / 2)) :
    (θ ≤ π / (2 * p) → pichoridesB p * Real.sin ((p - 1) * θ) ≤ Real.sin θ ^ (p - 1)) ∧
    (π / (2 * p) ≤ θ → Real.sin θ ^ (p - 1) ≤ pichoridesB p * Real.sin ((p - 1) * θ)) := by
  obtain ⟨h0, hθ0⟩ := pichorides_theta0_mem hp1
  set θ₀ := π / (2 * p) with hθ₀
  have hπ := Real.pi_pos
  have hmem0 : θ₀ ∈ Ioo 0 (π / 2) := ⟨h0, hθ0⟩
  have hpos : ∀ t ∈ Ioo (0 : ℝ) (π / 2), 0 < Real.sin t ∧ 0 < Real.sin ((p - 1) * t) :=
    fun t ht => ⟨Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2]),
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [ht.1]) (by nlinarith [ht.1, ht.2])⟩
  have hc0 : 0 < Real.cos θ₀ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ0⟩
  have hsα : Real.sin ((p - 1) * θ₀) = Real.cos θ₀ := by
    rw [← Real.sin_pi_div_two_sub]; congr 1; rw [hθ₀]; field_simp
  have hmono := monotoneOn_log_sin_ratio hp1 hp2
  -- `exp` of the monotone function is `sin(αθ)/sin^α θ`
  have hexp : ∀ t ∈ Ioo (0 : ℝ) (π / 2), Real.exp (Real.log (Real.sin ((p - 1) * t)) -
      (p - 1) * Real.log (Real.sin t)) = Real.sin ((p - 1) * t) / Real.sin t ^ (p - 1) :=
    fun t ht => by
      obtain ⟨h1, h2⟩ := hpos t ht
      rw [Real.exp_sub, Real.exp_log h2, Real.rpow_def_of_pos h1, mul_comm (Real.log _)]
  have hB : pichoridesB p * (Real.sin ((p - 1) * θ₀) / Real.sin θ₀ ^ (p - 1)) = 1 := by
    rw [pichoridesB, hsα, ← hθ₀]
    have : 0 < Real.sin θ₀ ^ (p - 1) := Real.rpow_pos_of_pos (hpos θ₀ hmem0).1 _
    field_simp
  have hBpos : 0 < pichoridesB p := by
    rw [pichoridesB]; exact div_pos (Real.rpow_pos_of_pos (hpos θ₀ hmem0).1 _) hc0
  obtain ⟨h1, h2⟩ := hpos θ hθ
  have hsp : 0 < Real.sin θ ^ (p - 1) := Real.rpow_pos_of_pos h1 _
  constructor
  · intro hle
    have := Real.exp_le_exp.mpr (hmono hθ hmem0 hle)
    rw [hexp θ hθ, hexp θ₀ hmem0] at this
    have := mul_le_mul_of_nonneg_left this hBpos.le
    rw [hB, mul_div_assoc', div_le_one hsp] at this
    exact this
  · intro hle
    have := Real.exp_le_exp.mpr (hmono hmem0 hθ hle)
    rw [hexp θ hθ, hexp θ₀ hmem0] at this
    have := mul_le_mul_of_nonneg_left this hBpos.le
    rw [hB, mul_div_assoc', one_le_div hsp] at this
    exact this

/-- The function `G(θ) = (sin^p θ + B_p cos pθ)/cos^p θ`. -/
noncomputable def pichoridesG (p θ : ℝ) : ℝ :=
  (Real.sin θ ^ p + pichoridesB p * Real.cos (p * θ)) / Real.cos θ ^ p

/-- Its derivative `p cos^{p−1}θ (sin^{p−1}θ − B_p sin((p − 1)θ)) / cos^{2p}θ`. -/
noncomputable def pichoridesG' (p θ : ℝ) : ℝ :=
  p * Real.cos θ ^ (p - 1) * (Real.sin θ ^ (p - 1) - pichoridesB p * Real.sin ((p - 1) * θ)) /
    (Real.cos θ ^ p) ^ 2

omit hp1 hp2 in
theorem hasDerivAt_pichoridesG {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    HasDerivAt (pichoridesG p) (pichoridesG' p θ) θ := by
  have hπ := Real.pi_pos
  have hS : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2])
  have hC : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
  set B := pichoridesB p
  set a := Real.sin θ ^ (p - 1) with ha
  set c := Real.cos θ ^ (p - 1) with hc
  have hSp : Real.sin θ ^ p = a * Real.sin θ := by
    rw [ha, Real.rpow_sub_one hS.ne', div_mul_cancel₀ _ hS.ne']
  have hCp : Real.cos θ ^ p = c * Real.cos θ := by
    rw [hc, Real.rpow_sub_one hC.ne', div_mul_cancel₀ _ hC.ne']
  have hN : HasDerivAt (fun t => Real.sin t ^ p + B * Real.cos (p * t))
      (p * (a * Real.cos θ - B * Real.sin (p * θ))) θ := by
    have e1 := (Real.hasDerivAt_sin θ).rpow_const (p := p) (Or.inl hS.ne')
    have e2 := ((Real.hasDerivAt_cos (p * θ)).comp θ ((hasDerivAt_id θ).const_mul p)).const_mul B
    exact (e1.add e2).congr_deriv (by ring)
  have hD : HasDerivAt (fun t => Real.cos t ^ p) (-(p * c * Real.sin θ)) θ :=
    ((Real.hasDerivAt_cos θ).rpow_const (p := p) (Or.inl hC.ne')).congr_deriv (by ring)
  have hDp : 0 < Real.cos θ ^ p := Real.rpow_pos_of_pos hC _
  have hsub : Real.sin ((p - 1) * θ) = Real.sin (p * θ) * Real.cos θ -
      Real.cos (p * θ) * Real.sin θ := by
    rw [← Real.sin_sub]; congr 1; ring
  have hnum : p * (a * Real.cos θ - B * Real.sin (p * θ)) * Real.cos θ ^ p -
      (Real.sin θ ^ p + B * Real.cos (p * θ)) * -(p * c * Real.sin θ) =
      p * c * (a - B * Real.sin ((p - 1) * θ)) := by
    rw [hSp, hCp, hsub]
    linear_combination (p * c * a) * Real.sin_sq_add_cos_sq θ
  exact (hN.div hD hDp.ne').congr_deriv (by rw [hnum]; rfl)

omit hp2 in
theorem continuousOn_pichoridesG : ContinuousOn (pichoridesG p) (Ico 0 (π / 2)) := by
  have hp0 : 0 < p := by linarith
  refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
    fun t ht => (Real.rpow_pos_of_pos (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩) _).ne'
  · exact ((Real.continuous_rpow_const hp0.le).comp Real.continuous_sin).add
      (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  · exact (Real.continuous_rpow_const hp0.le).comp Real.continuous_cos

omit hp2 in
theorem pichoridesG'_nonneg_iff {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    0 ≤ pichoridesG' p θ ↔ pichoridesB p * Real.sin ((p - 1) * θ) ≤ Real.sin θ ^ (p - 1) := by
  have hC : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc : 0 < p * Real.cos θ ^ (p - 1) := mul_pos (by linarith) (Real.rpow_pos_of_pos hC _)
  have hD : 0 < (Real.cos θ ^ p) ^ 2 := by have := Real.rpow_pos_of_pos hC p; positivity
  rw [pichoridesG', le_div_iff₀ hD, zero_mul, mul_nonneg_iff_of_pos_left hc, sub_nonneg]

/-- **Pichorides' inequality** in trigonometric form: for `1 < p ≤ 2` and `0 ≤ θ ≤ π/2`,
`sin^p θ + B_p cos pθ ≤ A_p^p cos^p θ`, with equality at `θ = π/2p`. -/
theorem pichorides_trig {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) :
    Real.sin θ ^ p + pichoridesB p * Real.cos (p * θ) ≤
      pichoridesA p ^ p * Real.cos θ ^ p := by
  have hπ := Real.pi_pos
  have hp0 : 0 < p := by linarith
  obtain ⟨ht0, htπ⟩ := pichorides_theta0_mem hp1
  set θ₀ := π / (2 * p) with hθ₀
  have hcont := continuousOn_pichoridesG hp1
  have hmono : MonotoneOn (pichoridesG p) (Icc 0 θ₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (hcont.mono (Icc_subset_Ico_right htπ)) (f' := pichoridesG' p)
      (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hasDerivAt_pichoridesG ⟨ht.1, ht.2.trans htπ⟩).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have hmem : t ∈ Ioo 0 (π / 2) := ⟨ht.1, ht.2.trans htπ⟩
      exact (pichoridesG'_nonneg_iff hp1 hmem).mpr
        ((pichorides_sign hp1 hp2 t hmem).1 ht.2.le)
  have hanti : AntitoneOn (pichoridesG p) (Ico θ₀ (π / 2)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico _ _)
      (hcont.mono (Ico_subset_Ico_left ht0.le)) (f' := pichoridesG' p)
      (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Ico] at ht
      exact (hasDerivAt_pichoridesG ⟨ht0.trans ht.1, ht.2⟩).hasDerivWithinAt
    · rw [interior_Ico] at ht
      have hmem : t ∈ Ioo 0 (π / 2) := ⟨ht0.trans ht.1, ht.2⟩
      have hs := (pichorides_sign hp1 hp2 t hmem).2 ht.1.le
      rcases (hs.lt_or_eq) with hlt | heq
      · by_contra hpos
        exact absurd ((pichoridesG'_nonneg_iff hp1 hmem).mp (le_of_not_ge hpos))
          (not_le.mpr hlt)
      · have := (pichoridesG'_nonneg_iff hp1 hmem).mpr heq.ge
        rw [pichoridesG', heq, sub_self, mul_zero, zero_div]
  have hC₀ : 0 < Real.cos θ₀ := Real.cos_pos_of_mem_Ioo ⟨by linarith, htπ⟩
  have hGθ₀ : pichoridesG p θ₀ = pichoridesA p ^ p := by
    have hcp : Real.cos (p * θ₀) = 0 := by
      rw [hθ₀, show p * (π / (2 * p)) = π / 2 by field_simp]; exact Real.cos_pi_div_two
    rw [pichoridesG, hcp, mul_zero, add_zero, pichoridesA, ← hθ₀, Real.tan_eq_sin_div_cos,
      Real.div_rpow (Real.sin_nonneg_of_nonneg_of_le_pi ht0.le (by linarith)) hC₀.le]
  have hle : ∀ t ∈ Ico 0 (π / 2), Real.sin t ^ p + pichoridesB p * Real.cos (p * t) ≤
      pichoridesA p ^ p * Real.cos t ^ p := fun t ht => by
    have hCt : 0 < Real.cos t ^ p :=
      Real.rpow_pos_of_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩) _
    have hG : pichoridesG p t ≤ pichoridesA p ^ p := by
      rw [← hGθ₀]
      rcases le_total t θ₀ with h | h
      · exact hmono ⟨ht.1, h⟩ ⟨ht0.le, le_rfl⟩ h
      · exact hanti ⟨le_rfl, htπ⟩ ⟨h, ht.2⟩ h
    rwa [pichoridesG, div_le_iff₀ hCt] at hG
  have hcl : θ ∈ closure (Ico 0 (π / 2)) := by
    rw [closure_Ico (by positivity : (0 : ℝ) ≠ π / 2)]; exact ⟨h0, h1⟩
  refine le_on_closure hle ?_ ?_ hcl
  · exact (((Real.continuous_rpow_const hp0.le).comp Real.continuous_sin).add
      (continuous_const.mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)))).continuousOn
  · exact (continuous_const.mul ((Real.continuous_rpow_const hp0.le).comp
      Real.continuous_cos)).continuousOn

/-- **Pichorides' inequality** (Pichorides 1972; DLMF 1.14.45 for `1 < p ≤ 2`): for real `a`, `b`,
`|b|^p + B_p Re((|a| + ib)^p) ≤ A_p^p |a|^p`, with `A_p = tan(π/2p)`. -/
theorem pichorides_ineq (a b : ℝ) :
    |b| ^ p + pichoridesB p * ((((|a| : ℝ) : ℂ) + b * I) ^ (p : ℂ)).re ≤
      pichoridesA p ^ p * |a| ^ p := by
  have hp0 : 0 < p := by linarith
  set w : ℂ := ((|a| : ℝ) : ℂ) + b * I with hw
  have hre : w.re = |a| := by simp [hw]
  have him : w.im = b := by simp [hw]
  by_cases h0 : w = 0
  · have ha : |a| = 0 := by rw [← hre, h0]; rfl
    have hb : b = 0 := by rw [← him, h0]; rfl
    rw [h0, zero_cpow (by exact_mod_cast hp0.ne'), ha, hb, abs_zero,
      Real.zero_rpow hp0.ne']
    simp
  set ρ := ‖w‖ with hρ
  set θ := arg w with hθ
  have hρ0 : 0 < ρ := norm_pos_iff.mpr h0
  have hθπ : |θ| ≤ π / 2 := abs_arg_le_pi_div_two_iff.mpr (by rw [hre]; exact abs_nonneg a)
  have hcos : |a| = ρ * Real.cos |θ| := by rw [Real.cos_abs, ← hre]; exact (norm_mul_cos_arg w).symm
  have hsin : |b| = ρ * Real.sin |θ| := by
    rw [← him, ← norm_mul_sin_arg w, ← hρ, ← hθ, abs_mul, abs_of_pos hρ0]
    congr 1
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by
        linarith [abs_le.mp hθπ, Real.pi_pos]))]
    · rw [abs_of_nonpos h, Real.sin_neg, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h
        (by linarith [abs_le.mp hθπ, Real.pi_pos]))]
  have hcp : Real.cos (p * θ) = Real.cos (p * |θ|) := by
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, mul_neg, Real.cos_neg]
  have hc0 : 0 ≤ Real.cos |θ| := Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg θ,
    Real.pi_pos], hθπ⟩
  have hs0 : 0 ≤ Real.sin |θ| := Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg θ)
    (by linarith [Real.pi_pos])
  have key := pichorides_trig hp1 hp2 (abs_nonneg θ) hθπ
  rw [re_cpow_ofReal w h0, hsin, hcos, Real.mul_rpow hρ0.le hs0, Real.mul_rpow hρ0.le hc0, ← hρ,
    ← hθ, hcp]
  have hρp : 0 < ρ ^ p := Real.rpow_pos_of_pos hρ0 p
  nlinarith [mul_le_mul_of_nonneg_left key hρp.le]

end Trig

end Azurite.DLMF
