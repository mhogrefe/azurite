/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Shift

/-!
# DLMF §5.11(i): 5.11.9

Formalization of <https://dlmf.nist.gov/5.11#E9>: `|Γ(x + iy)| ∼ √(2π) |y|^{x−½} e^{−π|y|/2}` as
`y → ±∞`, uniformly for bounded real `x`.

With `z = iy`, `u = x/z`: `ln(x + iy) = ln|y| + ½πi sign y + ln(1 + u)` (`|ph(1 + u)| ≤ ½π|u|`,
`abs_arg_one_add_le`), so `|Γ(x + iy)| = √(2π)|y|^{x−½}e^{−π|y|/2} exp(ℜ Q)` with
`Q = z(ln(1 + u) − u) + (x − ½) ln(1 + u) + J(x + iy)` (`norm_Gamma_eq_mul_exp`), and
`|Q| ≤ K/|y|` with `K` depending only on a bound for `|x|` (`norm_modulusQ_le`). "Uniformly for
bounded `x`" is convergence along `𝓟 [−X, X] ×ˢ (y → ±∞)` (`dlmf_5_11_9`).
-/

open Filter Topology Set Asymptotics
open scoped Real

namespace Azurite.DLMF

/-- `|ph(1 + u)| ≤ ½π|u|` for `|u| ≤ ½` (Jordan's inequality). -/
theorem abs_arg_one_add_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    |Complex.arg (1 + u)| ≤ π / 2 * ‖u‖ := by
  have hre : 0 ≤ (1 + u).re := by
    have := Complex.abs_re_le_norm u
    simp only [Complex.add_re, Complex.one_re]
    linarith [(abs_le.mp this).1]
  have h1 := abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hre)
  have hs : |Real.sin (Complex.arg (1 + u))| ≤ ‖u‖ := by
    simpa using abs_sin_arg_le_norm_sub_one (1 + u)
  set t := Complex.arg (1 + u)
  have key : 2 / π * |t| ≤ |Real.sin t| := by
    rcases abs_cases t with ⟨ht, ht0⟩ | ⟨ht, ht0⟩
    · rw [ht]; exact (Real.mul_le_sin ht0 h1.2).trans (le_abs_self _)
    · rw [ht]
      have := Real.mul_le_sin (by linarith : 0 ≤ -t) (by linarith)
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have hπ := Real.pi_pos
  have h2 : |t| ≤ π / 2 * |Real.sin t| := by
    have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ π / 2)
    rwa [← mul_assoc, show π / 2 * (2 / π) = 1 by field_simp, one_mul] at this
  exact h2.trans (mul_le_mul_of_nonneg_left hs (by positivity))

theorem arg_ofReal_mul_I {y : ℝ} (hy : y ≠ 0) :
    |Complex.arg ((y : ℂ) * Complex.I)| = π / 2 ∧
      y * Complex.arg ((y : ℂ) * Complex.I) = π * |y| / 2 := by
  rcases hy.lt_or_gt with h | h
  · have e : (y : ℂ) * Complex.I = ((-y : ℝ) : ℂ) * (-Complex.I) := by push_cast; ring
    rw [e, Complex.arg_real_mul _ (neg_pos.mpr h), Complex.arg_neg_I, abs_of_neg h,
      abs_neg, abs_of_pos (by positivity)]
    exact ⟨rfl, by ring⟩
  · rw [Complex.arg_real_mul _ h, Complex.arg_I, abs_of_pos h, abs_of_pos (by positivity)]
    exact ⟨rfl, by ring⟩

/-- The error term `Q = (x + iy − ½) ln(1 + x/(iy)) − x + J(x + iy)` of 5.11.9. -/
noncomputable def modulusQ (x y : ℝ) : ℂ :=
  ((x : ℂ) + y * Complex.I - 1 / 2) * Complex.log (1 + x * ((y : ℂ) * Complex.I)⁻¹) - x +
    stirlingJ (x + y * Complex.I)

/-- Geometry for `|x| ≤ |y|/2`: `ln(x + iy) = ln(iy) + ln(1 + u)`, `|ph(x + iy)| ≤ 3π/4`. -/
theorem modulus_geometry {x y : ℝ} (hy : y ≠ 0) (hxy : |x| ≤ |y| / 2) :
    Complex.log ((x : ℂ) + y * Complex.I) = Complex.log ((y : ℂ) * Complex.I) +
        Complex.log (1 + x * ((y : ℂ) * Complex.I)⁻¹) ∧
      |Complex.arg ((x : ℂ) + y * Complex.I)| ≤ π - π / 4 ∧
      ‖(x : ℂ) * ((y : ℂ) * Complex.I)⁻¹‖ = |x| / |y| := by
  have hz0 : (y : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hy) Complex.I_ne_zero
  have hyp : 0 < |y| := abs_pos.mpr hy
  have hun : ‖(x : ℂ) * ((y : ℂ) * Complex.I)⁻¹‖ = |x| / |y| := by
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, div_eq_mul_inv]
  set u := (x : ℂ) * ((y : ℂ) * Complex.I)⁻¹
  have hu : ‖u‖ ≤ 1 / 2 := by
    rw [hun, div_le_iff₀ hyp]; linarith
  have hau := abs_arg_one_add_le hu
  have hau' : |Complex.arg (1 + u)| ≤ π / 4 := by
    refine hau.trans ?_
    nlinarith [Real.pi_pos, norm_nonneg u]
  have h1u : 1 + u ≠ 0 := by
    intro h
    have : ‖u‖ = 1 := by rw [show u = -1 by linear_combination h]; simp
    linarith
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hmul : (x : ℂ) + y * Complex.I = (y : ℂ) * Complex.I * (1 + u) := by
    simp only [u]; field_simp; ring
  obtain ⟨hz, -⟩ := arg_ofReal_mul_I hy
  have ha := abs_lt.mp (show |Complex.arg ((y : ℂ) * Complex.I)| < π - π / 4 by
    rw [hz]; linarith [Real.pi_pos])
  have hb := abs_le.mp hau'
  have hlog := (Complex.log_mul_eq_add_log_iff hz0 h1u).mpr
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have harg : Complex.arg ((x : ℂ) + y * Complex.I) =
      Complex.arg ((y : ℂ) * Complex.I) + Complex.arg (1 + u) := by
    rw [← Complex.log_im, hmul, hlog, Complex.add_im, Complex.log_im, Complex.log_im]
  refine ⟨by rw [hmul, hlog], ?_, hun⟩
  rw [harg]
  have hz' := abs_le.mp hz.le
  exact abs_le.mpr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem ofReal_add_mul_I_mem_slitPlane {x y : ℝ} (hy : y ≠ 0) :
    (x : ℂ) + y * Complex.I ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hy))

/-- `|Γ(x + iy)| = √(2π)|y|^{x−½}e^{−π|y|/2} exp(ℜ Q)` for `|x| ≤ |y|/2`. -/
theorem norm_Gamma_eq_mul_exp {x y : ℝ} (hy : y ≠ 0) (hxy : |x| ≤ |y| / 2) :
    ‖Complex.Gamma (x + y * Complex.I)‖ = Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) *
      Real.exp (-(π * |y|) / 2) * Real.exp (modulusQ x y).re := by
  obtain ⟨hlog, -, -⟩ := modulus_geometry hy hxy
  obtain ⟨-, hθ⟩ := arg_ofReal_mul_I hy
  have hyp : 0 < |y| := abs_pos.mpr hy
  have hpos : (0 : ℝ) < 2 * π := by positivity
  rw [Gamma_eq_exp_stirlingJ (ofReal_add_mul_I_mem_slitPlane hy), Complex.norm_exp,
    Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hyp,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hlz : Complex.log ((y : ℂ) * Complex.I) =
      (Real.log |y| : ℂ) + (Complex.arg ((y : ℂ) * Complex.I) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
  have h2π : Complex.log (2 * π) = (Real.log (2 * π) : ℂ) := by
    rw [Complex.ofReal_log hpos.le]; push_cast; rfl
  set θ := Complex.arg ((y : ℂ) * Complex.I)
  have e : ((x : ℂ) + y * Complex.I - 1 / 2) * Complex.log ((x : ℂ) + y * Complex.I) -
      ((x : ℂ) + y * Complex.I) + 1 / 2 * Complex.log (2 * π) + stirlingJ (x + y * Complex.I) =
      ((x : ℂ) - 1 / 2 + y * Complex.I) * ((Real.log |y| : ℂ) + (θ : ℂ) * Complex.I) -
        y * Complex.I + 1 / 2 * (Real.log (2 * π) : ℂ) + modulusQ x y := by
    rw [hlog, hlz, h2π, modulusQ]; ring
  rw [e]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.div_re,
    Complex.mul_im, Complex.add_im, Complex.sub_im, Complex.one_im, Complex.div_im]
  norm_num
  linarith

/-- `|Q| ≤ K/|y|` for `|x| ≤ |y|/2`, `K = x² + (|x| + ½)(3/2)|x| + 1/(8 sin²(π/8))`. -/
theorem norm_modulusQ_le {x y : ℝ} (hy : y ≠ 0) (hxy : |x| ≤ |y| / 2) :
    ‖modulusQ x y‖ ≤ (x ^ 2 + (|x| + 1 / 2) * (3 / 2 * |x|) + 1 / 8 / Real.sin (π / 8) ^ 2) /
      |y| := by
  obtain ⟨-, harg, hun⟩ := modulus_geometry hy hxy
  have hyp : 0 < |y| := abs_pos.mpr hy
  have hz0 : (y : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hy) Complex.I_ne_zero
  set u := (x : ℂ) * ((y : ℂ) * Complex.I)⁻¹ with hu_def
  have hu : ‖u‖ ≤ 1 / 2 := by rw [hun, div_le_iff₀ hyp]; linarith
  have hw0 : (x : ℂ) + y * Complex.I ≠ 0 := Complex.slitPlane_ne_zero
    (ofReal_add_mul_I_mem_slitPlane hy)
  have hdec : modulusQ x y = (y : ℂ) * Complex.I * (Complex.log (1 + u) - u) +
      ((x : ℂ) - 1 / 2) * Complex.log (1 + u) + stirlingJ (x + y * Complex.I) := by
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    have hzu : (y : ℂ) * Complex.I * u = x := by rw [hu_def]; field_simp
    rw [modulusQ, ← hu_def]
    linear_combination hzu
  have hs : 0 < Real.sin (π / 8) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by linarith [Real.pi_pos])
  have h1 : ‖(y : ℂ) * Complex.I * (Complex.log (1 + u) - u)‖ ≤ |y| * ‖u‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ hyp.le
    refine (Complex.norm_log_one_add_sub_self_le (by linarith)).trans ?_
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖u‖)]
  have h2 : ‖((x : ℂ) - 1 / 2) * Complex.log (1 + u)‖ ≤ (|x| + 1 / 2) * (3 / 2 * ‖u‖) := by
    rw [norm_mul]
    refine mul_le_mul ?_ (Complex.norm_log_one_add_half_le_self hu) (norm_nonneg _)
      (by positivity)
    refine (norm_sub_le _ _).trans ?_
    simp
  have hwn : |y| ≤ ‖(x : ℂ) + y * Complex.I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + y * Complex.I)
    simpa using this
  have h3 : ‖stirlingJ (x + y * Complex.I)‖ ≤ 1 / 8 / (Real.sin (π / 8) ^ 2 * |y|) := by
    refine (norm_stirlingJ_le hw0 (δ := π / 4) (by positivity) (by linarith [Real.pi_pos])
      harg).trans ?_
    rw [show π / 4 / 2 = π / 8 by ring]
    gcongr
  rw [hdec]
  refine (norm_add₃_le).trans ?_
  have hfin : |y| * ‖u‖ ^ 2 + (|x| + 1 / 2) * (3 / 2 * ‖u‖) + 1 / 8 / (Real.sin (π / 8) ^ 2 * |y|)
      = (x ^ 2 + (|x| + 1 / 2) * (3 / 2 * |x|) + 1 / 8 / Real.sin (π / 8) ^ 2) / |y| := by
    rw [hun, ← sq_abs x]
    field_simp
  linarith

/-- **DLMF 5.11.9**: `|Γ(x + iy)| ∼ √(2π) |y|^{x−½} e^{−π|y|/2}` as `y → ±∞`, uniformly for
bounded real `x`: along `𝓟 [−X, X] ×ˢ (y → ±∞)` for every `X`. -/
theorem dlmf_5_11_9 (X : ℝ) :
    AsympEqDLMF (𝓟 (Icc (-X) X) ×ˢ Bornology.cobounded ℝ)
      (fun p : ℝ × ℝ => ‖Complex.Gamma (p.1 + p.2 * Complex.I)‖)
      (fun p => Real.sqrt (2 * π) * |p.2| ^ (p.1 - 1 / 2) * Real.exp (-(π * |p.2|) / 2)) := by
  set F := 𝓟 (Icc (-X) X) ×ˢ Bornology.cobounded ℝ
  set K := X ^ 2 + (|X| + 1 / 2) * (3 / 2 * |X|) + 1 / 8 / Real.sin (π / 8) ^ 2
  have h1 : ∀ᶠ p : ℝ × ℝ in F, p.1 ∈ Icc (-X) X :=
    tendsto_fst.eventually (mem_principal_self (Icc (-X) X))
  have h2 : ∀ᶠ p : ℝ × ℝ in F, 2 * |X| + 1 ≤ ‖p.2‖ :=
    (tendsto_snd (f := 𝓟 (Icc (-X) X)) (g := Bornology.cobounded ℝ)).eventually
      ((tendsto_norm_cobounded_atTop (E := ℝ)).eventually (eventually_ge_atTop _))
  have hgood : ∀ᶠ p : ℝ × ℝ in F, p.2 ≠ 0 ∧ |p.1| ≤ |p.2| / 2 ∧ |p.1| ≤ |X| := by
    filter_upwards [h1, h2] with p hp1 hp2
    rw [Real.norm_eq_abs] at hp2
    have hx : |p.1| ≤ |X| :=
      abs_le.mpr ⟨by linarith [hp1.1, le_abs_self X], by linarith [hp1.2, le_abs_self X]⟩
    exact ⟨fun h => by rw [h, abs_zero] at hp2; linarith [abs_nonneg X], by linarith, hx⟩
  have hE : Tendsto (fun p : ℝ × ℝ => (modulusQ p.1 p.2).re) F (𝓝 0) := by
    have hlim : Tendsto (fun p : ℝ × ℝ => K / |p.2|) F (𝓝 0) := by
      have : Tendsto (fun y : ℝ => K / |y|) (Bornology.cobounded ℝ) (𝓝 0) := by
        simpa [Real.norm_eq_abs] using tendsto_const_nhds.div_atTop
          (tendsto_norm_cobounded_atTop (E := ℝ))
      exact this.comp tendsto_snd
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hgood] with p hp
    obtain ⟨hy, hxy, hX⟩ := hp
    refine (Complex.abs_re_le_norm _).trans ((norm_modulusQ_le hy hxy).trans ?_)
    have hyp : 0 < |p.2| := abs_pos.mpr hy
    have hK : p.1 ^ 2 + (|p.1| + 1 / 2) * (3 / 2 * |p.1|) + 1 / 8 / Real.sin (π / 8) ^ 2 ≤ K := by
      simp only [K]
      rw [← sq_abs p.1, ← sq_abs X]
      gcongr
    exact div_le_div_of_nonneg_right hK hyp.le
  have hexp : Tendsto (fun p : ℝ × ℝ => Real.exp (modulusQ p.1 p.2).re) F (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp hE
    rw [Real.exp_zero] at this
    exact this
  refine hexp.congr' ?_
  filter_upwards [hgood] with p hp
  obtain ⟨hy, hxy, -⟩ := hp
  have hD : 0 < Real.sqrt (2 * π) * |p.2| ^ (p.1 - 1 / 2) * Real.exp (-(π * |p.2|) / 2) := by
    have := Real.rpow_pos_of_pos (abs_pos.mpr hy) (p.1 - 1 / 2)
    have := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 * π by positivity)
    positivity
  rw [norm_Gamma_eq_mul_exp hy hxy]
  field_simp

end Azurite.DLMF
