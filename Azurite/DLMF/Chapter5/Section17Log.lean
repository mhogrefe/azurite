/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section17
import Azurite.DLMF.Chapter5.Section15
import Azurite.DLMF.Chapter5.Section11Stirling
import Azurite.DLMF.Chapter1.Section13Primitive

/-!
# DLMF 5.17.4: the integral representation of `Ln G(z + 1)`

Formalization of <https://dlmf.nist.gov/5.17> (part 2). DLMF: "the Ln's have their principal
values on the positive real axis and are continued via continuity". On the cut plane
`ℂ ∖ (−∞, −1]` (`z + 1 ∈ slitPlane`):

* `Ln Γ(w)` (`lnGamma`, `w` in the slit plane) is `(w − ½) ln w − w + ½ ln(2π) + J(w)` with
  Binet's function `J` of §5.11 (`exp_lnGamma`, `lnGamma_ofReal`: real on `(0, ∞)`),
  `(Ln Γ)′ = ψ` (`hasDerivAt_lnGamma`), `Ln Γ(z + 1) = Ln Γ(z) + ln z` (`lnGamma_add_one`).
* `Ln G(z + 1)` (`barnesLog`) is the logarithm of the product 5.17.3 taken factorwise,
  `½z ln(2π) − ½z(z + 1) − ½γz² + ∑ₖ (k ln(1 + z/k) − z + z²/(2k))`: holomorphic, real on
  `(−1, ∞)` (`barnesLog_ofReal`), `exp(Ln G(z + 1)) = G(z + 1)` (`barnesG_add_one_eq_exp`), with
  `(Ln G(z + 1))′ = ½ ln(2π) − z − ½ + zψ(z + 1)` (`hasDerivAt_barnesLog`, termwise
  differentiation and 5.7.6).
* 5.17.4 (`dlmf_5_17_4`): the right side has the same derivative and both vanish at `0`; the
  integral `∫₀^z` is along the segment `[0, z]` (`segInt`).
-/

open Complex Filter Topology Set Finset Metric
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### `Ln Γ` on the slit plane -/

/-- DLMF's `Ln Γ(w)` on the slit plane `|ph w| < π`: the continuous logarithm of `Γ` that is real
on the positive real axis, `(w − ½) ln w − w + ½ ln(2π) + J(w)`. -/
noncomputable def lnGamma (w : ℂ) : ℂ :=
  (w - 1 / 2) * Complex.log w - w + 1 / 2 * Complex.log (2 * π) + stirlingJ w

theorem exp_lnGamma {w : ℂ} (hw : w ∈ slitPlane) : cexp (lnGamma w) = Gamma w :=
  (Gamma_eq_exp_stirlingJ hw).symm

theorem differentiableAt_lnGamma {w : ℂ} (hw : w ∈ slitPlane) : DifferentiableAt ℂ lnGamma w :=
  ((((differentiableAt_id.sub_const _).mul (differentiableAt_log hw)).sub
    differentiableAt_id).add_const _).add
    ((differentiableOn_stirlingJ w hw).differentiableAt (isOpen_slitPlane.mem_nhds hw))

theorem differentiableOn_lnGamma : DifferentiableOn ℂ lnGamma slitPlane := fun _ hw =>
  (differentiableAt_lnGamma hw).differentiableWithinAt

theorem hasDerivAt_lnGamma {w : ℂ} (hw : w ∈ slitPlane) : HasDerivAt lnGamma (digamma w) w := by
  have hd := (differentiableAt_lnGamma hw).hasDerivAt
  have hev : (fun v => cexp (lnGamma v)) =ᶠ[𝓝 w] Gamma := by
    filter_upwards [isOpen_slitPlane.mem_nhds hw] with v hv using exp_lnGamma hv
  have hG := hd.cexp.congr_of_eventuallyEq hev.symm
  have hΓ : Gamma w ≠ 0 := by rw [← exp_lnGamma hw]; exact exp_ne_zero _
  convert hd using 1
  rw [digamma_def, logDeriv_apply, hG.deriv, exp_lnGamma hw]
  field_simp

theorem lnGamma_ofReal {x : ℝ} (hx : 0 < x) : lnGamma x = (Real.log (Real.Gamma x) : ℂ) := by
  rw [lnGamma, stirlingJ_ofReal, stirlingJR_eq_stirlingMu hx, stirlingMu,
    ← ofReal_log hx.le, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_log (by positivity)]
  push_cast
  ring

theorem mem_slitPlane_add_one {z : ℂ} (hz : z ∈ slitPlane) : z + 1 ∈ slitPlane := by
  simpa using add_ofReal_mem_slitPlane hz (t := 1) zero_le_one

theorem isPreconnected_slitPlane_of_star : IsPreconnected slitPlane :=
  (StarConvex.isPathConnected starConvex_one_slitPlane (by simp)).isConnected.isPreconnected

/-- `Ln Γ(z + 1) = Ln Γ(z) + ln z` on the slit plane. -/
theorem lnGamma_add_one {z : ℂ} (hz : z ∈ slitPlane) :
    lnGamma (z + 1) = lnGamma z + Complex.log z := by
  have hf : AnalyticOnNhd ℂ (fun w => lnGamma (w + 1)) slitPlane :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      ((differentiableAt_lnGamma (mem_slitPlane_add_one hw)).comp w
        (differentiableAt_id.add_const 1)).differentiableWithinAt) isOpen_slitPlane
  have hg : AnalyticOnNhd ℂ (fun w => lnGamma w + Complex.log w) slitPlane :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      ((differentiableAt_lnGamma hw).add (differentiableAt_log hw)).differentiableWithinAt)
      isOpen_slitPlane
  refine eqOn_of_eq_on_pos_reals hf hg isPreconnected_slitPlane_of_star isOpen_slitPlane (by simp)
    (fun x hx _ => ?_) hz
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  rw [show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring, lnGamma_ofReal hx1,
    lnGamma_ofReal hx, ← ofReal_log hx.le, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  push_cast
  ring

/-! ### `Ln G(z + 1)` -/

/-- DLMF's `Ln G(z + 1)`: the logarithm of the product 5.17.3 taken factorwise,
`½z ln(2π) − ½z(z + 1) − ½γz² + ∑ₖ (k ln(1 + z/k) − z + z²/(2k))`. -/
noncomputable def barnesLog (z : ℂ) : ℂ :=
  z / 2 * Complex.log (2 * π) - z * (z + 1) / 2 - γ * z ^ 2 / 2 + ∑' k, barnesLogTerm z k

theorem summable_barnesLogTerm (z : ℂ) : Summable (barnesLogTerm z) := by
  refine Summable.of_norm_bounded_eventually_nat
    (summable_one_div_natCast_add_one_sq.mul_left (2 / 3 * ‖z‖ ^ 3)) ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * ‖z‖)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
  exact norm_barnesLogTerm_le (by linarith)

theorem barnesLogTerm_zero (k : ℕ) : barnesLogTerm 0 k = 0 := by simp [barnesLogTerm]

theorem barnesLog_zero : barnesLog 0 = 0 := by simp [barnesLog, barnesLogTerm_zero]

/-- `1 + z/(k + 1)` lies in the slit plane when `z + 1` does. -/
theorem one_add_div_mem_slitPlane_of_add_one {z : ℂ} (hz : z + 1 ∈ slitPlane) (k : ℕ) :
    1 + z / ((k : ℂ) + 1) ∈ slitPlane := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 := add_ofReal_mem_slitPlane hz (t := k) k.cast_nonneg
  have e : 1 + z / ((k : ℂ) + 1) = (z + 1 + (k : ℝ)) / (((k : ℝ) + 1 : ℝ) : ℂ) := by
    have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast; field_simp; ring
  rw [e]
  rw [mem_slitPlane_iff] at h1 ⊢
  simp only [div_ofReal_re, div_ofReal_im]
  rcases h1 with h | h
  · exact Or.inl (div_pos h hk)
  · exact Or.inr (div_ne_zero h hk.ne')

theorem barnesG_add_one_eq_exp {z : ℂ} (hz : z + 1 ∈ slitPlane) :
    barnesG (z + 1) = cexp (barnesLog z) := by
  have hp := (summable_barnesLogTerm z).hasSum.cexp
  have hf : (cexp ∘ barnesLogTerm z) = barnesFactor z := funext fun k =>
    (barnesFactor_eq_exp (slitPlane_ne_zero (one_add_div_mem_slitPlane_of_add_one hz k))).symm
  have hprod : ∏' k, barnesFactor z k = cexp (∑' k, barnesLogTerm z k) := by
    rw [← hf]; exact hp.tprod_eq
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
  rw [barnesG_add_one, hprod, barnesPre, cpow_def_of_ne_zero h2π, ← exp_add, ← exp_add]
  congr 1
  simp only [barnesLog]
  ring

/-- The real form of `ℓₖ(x)`, `x > −1`. -/
noncomputable def barnesLogTermR (x : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * Real.log (1 + x / ((k : ℝ) + 1)) - x + x ^ 2 / (2 * ((k : ℝ) + 1))

/-- `Ln G(x + 1)` is real for `x > −1`. -/
theorem barnesLog_ofReal {x : ℝ} (hx : -1 < x) :
    barnesLog x = ((x / 2 * Real.log (2 * π) - x * (x + 1) / 2 - γ * x ^ 2 / 2 +
      ∑' k, barnesLogTermR x k : ℝ) : ℂ) := by
  have ht : ∀ k : ℕ, barnesLogTerm x k = (barnesLogTermR x k : ℂ) := fun k => by
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hpos : 0 ≤ 1 + x / ((k : ℝ) + 1) := by
      have : -1 ≤ x / ((k : ℝ) + 1) := by
        rw [le_div_iff₀ hk]
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      linarith
    rw [barnesLogTerm, barnesLogTermR]
    push_cast
    rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_div, ← ofReal_add,
      ← ofReal_log hpos]
  rw [barnesLog, tsum_congr ht, ← ofReal_tsum, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by
    push_cast; ring, ← ofReal_log (by positivity)]
  push_cast
  ring

/-! ### The derivative of `Ln G(z + 1)` -/

theorem hasDerivAt_barnesLogTerm {z : ℂ} (k : ℕ) (hz : 1 + z / ((k : ℂ) + 1) ∈ slitPlane) :
    HasDerivAt (fun w => barnesLogTerm w k) (z * (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 + z)))
      z := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hkz : (k : ℂ) + 1 + z ≠ 0 := by
    intro h
    apply slitPlane_ne_zero hz
    field_simp
    linear_combination h
  have h1 := (((hasDerivAt_id z).div_const ((k : ℂ) + 1)).const_add 1).clog hz
  have h2 := ((h1.const_mul ((k : ℂ) + 1)).sub (hasDerivAt_id z)).add
    ((hasDerivAt_pow 2 z).div_const (2 * ((k : ℂ) + 1)))
  refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
  simp only [id]
  field_simp
  ring

/-- Termwise differentiation: `(∑ₖ ℓₖ)′(z) = ∑ₖ z(1/(k + 1) − 1/(k + 1 + z))`. -/
theorem hasDerivAt_tsum_barnesLogTerm {z₀ : ℂ} (hz₀ : z₀ + 1 ∈ slitPlane) :
    HasDerivAt (fun z => ∑' k, barnesLogTerm z k)
      (∑' k : ℕ, z₀ * (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 + z₀))) z₀ := by
  have hU : IsOpen {w : ℂ | w + 1 ∈ slitPlane} :=
    isOpen_slitPlane.preimage (continuous_id.add continuous_const)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hpole : z₀ + 1 ∉ gammaPoles := by
    rintro ⟨n, hn⟩
    rw [← hn] at hz₀
    simp [mem_slitPlane_iff] at hz₀
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨r, hr, c, hc, hb⟩ := exists_norm_add_nat_ge hpole
  set r' := min ρ r
  have hr' : 0 < r' := lt_min hρ hr
  set M := (‖z₀‖ + r') ^ 2 / c
  have hmem : ∀ y ∈ ball z₀ r', y + 1 ∈ slitPlane := fun y hy =>
    hρU (ball_subset_ball (min_le_left _ _) hy)
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => M * (1 / ((k : ℝ) + 1) ^ 2))
    (summable_one_div_natCast_add_one_sq.mul_left M) isOpen_ball
    (convex_ball z₀ r').isPreconnected
    (fun k y hy => hasDerivAt_barnesLogTerm k (one_add_div_mem_slitPlane_of_add_one (hmem y hy) k))
    (fun k y hy => ?_) (mem_ball_self hr') (summable_barnesLogTerm z₀) (mem_ball_self hr')
  have hy1 : y + 1 ∈ ball (z₀ + 1) r := by
    rw [mem_ball, dist_eq_norm, show y + 1 - (z₀ + 1) = y - z₀ by ring, ← dist_eq_norm,
      ← mem_ball]
    exact ball_subset_ball (min_le_right _ _) hy
  have hck := hb (y + 1) hy1 k
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hyn : ‖y‖ ≤ ‖z₀‖ + r' := by
    have := norm_sub_norm_le y z₀
    rw [mem_ball, dist_eq_norm] at hy
    linarith
  have hkz : ‖(k : ℂ) + 1 + y‖ = ‖y + 1 + k‖ := by ring_nf
  have hpos : 0 < ‖(k : ℂ) + 1 + y‖ := by rw [hkz]; nlinarith
  have hnk : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (k + 1)
  have hk0 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hkz0 : (k : ℂ) + 1 + y ≠ 0 := norm_pos_iff.mp hpos
  have e : y * (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 + y)) =
      y ^ 2 / (((k : ℂ) + 1) * ((k : ℂ) + 1 + y)) := by field_simp; ring
  rw [e, norm_div, norm_mul, norm_pow, hnk]
  calc ‖y‖ ^ 2 / (((k : ℝ) + 1) * ‖(k : ℂ) + 1 + y‖)
      ≤ (‖z₀‖ + r') ^ 2 / (((k : ℝ) + 1) * (c * ((k : ℝ) + 1))) := by
        gcongr
        rw [hkz]; exact hck
    _ = M * (1 / ((k : ℝ) + 1) ^ 2) := by simp only [M]; field_simp

/-- `(Ln G(z + 1))′ = ½ ln(2π) − z − ½ + zψ(z + 1)`. -/
theorem hasDerivAt_barnesLog {z : ℂ} (hz : z + 1 ∈ slitPlane) :
    HasDerivAt barnesLog (1 / 2 * Complex.log (2 * π) - z - 1 / 2 + z * digamma (z + 1)) z := by
  have hpole : z + 1 ∉ gammaPoles := by
    rintro ⟨n, hn⟩
    rw [← hn] at hz
    simp [mem_slitPlane_iff] at hz
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs := hasDerivAt_tsum_barnesLogTerm hz
  have hp : HasDerivAt (fun w : ℂ => w / 2 * Complex.log (2 * π) - w * (w + 1) / 2 -
      γ * w ^ 2 / 2) (Complex.log (2 * π) / 2 - (2 * z + 1) / 2 - γ * z) z := by
    have := ((((hasDerivAt_id z).div_const 2).mul_const (Complex.log (2 * π))).sub
      (((hasDerivAt_id z).mul ((hasDerivAt_id z).add_const 1)).div_const 2)).sub
      (((hasDerivAt_pow 2 z).const_mul (γ : ℂ)).div_const 2)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
    simp only [id]
    ring
  refine ((hp.add hs).congr_deriv ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun w => by simp [barnesLog])
  rw [digamma_eq_psiSeries hpole, psiSeries, tsum_mul_left]
  have e : ∀ k : ℕ, psiTerm k (z + 1) = 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 + z) := fun k => by
    rw [psiTerm]; ring_nf
  simp only [e]
  ring

/-! ### DLMF 5.17.4 -/

theorem segment_subset_of_add_one {z : ℂ} (hz : z + 1 ∈ slitPlane) :
    segment ℝ 0 z ⊆ {w : ℂ | w + 1 ∈ slitPlane} := by
  have hs : StarConvex ℝ 0 {w : ℂ | w + 1 ∈ slitPlane} := fun y hy a b ha hb hab => by
    have := starConvex_one_slitPlane hy ha hb hab
    show a • (0 : ℂ) + b • y + 1 ∈ slitPlane
    convert this using 1
    simp only [Complex.real_smul, mul_zero, zero_add, mul_one]
    have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
    linear_combination -hab'
  exact hs.segment_subset hz

/-- **DLMF 5.17.4**: `Ln G(z + 1) = ½z ln(2π) − ½z(z + 1) + z Ln Γ(z + 1) − ∫₀^z Ln Γ(t + 1) dt`
on `ℂ ∖ (−∞, −1]`, the integral along the segment `[0, z]`. -/
theorem dlmf_5_17_4 {z : ℂ} (hz : z + 1 ∈ slitPlane) :
    barnesLog z = 1 / 2 * z * Complex.log (2 * π) - 1 / 2 * z * (z + 1) + z * lnGamma (z + 1) -
      segInt (fun t => lnGamma (t + 1)) 0 z := by
  set U : Set ℂ := {w : ℂ | w + 1 ∈ slitPlane}
  set F : ℂ → ℂ := fun w => 1 / 2 * w * Complex.log (2 * π) - 1 / 2 * w * (w + 1) +
    w * lnGamma (w + 1) - barnesLog w
  have hF : ∀ w ∈ U, HasDerivAt F (lnGamma (w + 1)) w := fun w hw => by
    have hl : HasDerivAt (fun v => lnGamma (v + 1)) (digamma (w + 1)) w :=
      (hasDerivAt_lnGamma hw).comp_add_const w 1
    have h := ((((hasDerivAt_id w).const_mul (1 / 2 : ℂ)).mul_const (Complex.log (2 * π))).sub
      (((hasDerivAt_id w).const_mul (1 / 2 : ℂ)).mul ((hasDerivAt_id w).add_const 1))).add
      ((hasDerivAt_id w).mul hl) |>.sub (hasDerivAt_barnesLog hw)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun v => rfl)
    simp only [id]
    ring
  have hc : ContinuousOn (fun t => lnGamma (t + 1)) U := fun w hw => by
    have h : DifferentiableAt ℂ (fun t => lnGamma (t + 1)) w :=
      (differentiableAt_lnGamma hw).comp w (differentiableAt_id.add_const 1)
    exact h.continuousAt.continuousWithinAt
  have h := segInt_eq_sub (segment_subset_of_add_one hz) hF hc
  simp only [F, barnesLog_zero] at h
  rw [h]
  ring

end Azurite.DLMF
