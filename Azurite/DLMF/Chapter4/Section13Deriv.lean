/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Cut

/-!
# DLMF §4.13: higher derivatives and antiderivatives of the complex branches

* `iteratedDeriv_of_lambert_ode`: any `W` with `W′ = e^{−W}/(1 + W)` on an open set satisfies
  4.13.4_1 there (with the polynomials `pₙ` of 4.13.4_2, `lambertP`).
* `dlmf_4_13_4_1_complex`: 4.13.4_1 for every branch `W_k` on `ℂ ∖ (−∞, 0]`, and for `W₀` on
  `ℂ ∖ (−∞, −e⁻¹]`.
* `dlmf_4_13_12_complex`–`dlmf_4_13_14_complex`: the antiderivatives on `ℂ ∖ (−∞, 0]`.
-/

open Set Filter Topology Complex Polynomial
open scoped Real

namespace Azurite.DLMF

/-- `pₙ` with complex coefficients. -/
noncomputable def lambertPC (n : ℕ) : ℂ[X] := (lambertP n).map (algebraMap ℝ ℂ)

theorem lambertPC_succ_eval (n : ℕ) (w : ℂ) : (lambertPC (n + 1)).eval w =
    (1 + w) * (derivative (lambertPC n)).eval w +
      (1 - (n + 1) * (w + 3)) * (lambertPC n).eval w := by
  simp only [lambertPC, lambertP, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_natCast, Polynomial.map_ofNat,
    derivative_map, eval_add, eval_mul, eval_sub, eval_one, eval_X, eval_natCast, eval_ofNat]
  push_cast; ring

/-- 4.13.4_1 for any solution of `W′ = e^{−W}/(1 + W)` on an open set. -/
theorem iteratedDeriv_of_lambert_ode {U : Set ℂ} (hU : IsOpen U) {W : ℂ → ℂ}
    (hW : ∀ z ∈ U, HasDerivAt W (exp (-W z) / (1 + W z)) z) (h1 : ∀ z ∈ U, 1 + W z ≠ 0)
    (n : ℕ) {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv (n + 1) W z =
      exp (-((n + 1 : ℕ) : ℂ) * W z) * (lambertPC n).eval (W z) / (1 + W z) ^ (2 * n + 1) := by
  induction n generalizing z with
  | zero =>
    rw [iteratedDeriv_one, (hW z hz).deriv]
    simp [lambertPC, lambertP]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv (n + 1) W =ᶠ[𝓝 z] fun z =>
        exp (-((n + 1 : ℕ) : ℂ) * W z) * (lambertPC n).eval (W z) / (1 + W z) ^ (2 * n + 1) :=
      eventually_of_mem (hU.mem_nhds hz) fun y hy => ih hy
    rw [heq.deriv_eq]
    have hWz := hW z hz
    have hw1 := h1 z hz
    have ha := (hWz.const_mul (-((n + 1 : ℕ) : ℂ))).cexp
    have hb := ((lambertPC n).hasDerivAt (W z)).comp z hWz
    have hc := (hWz.const_add 1).pow (2 * n + 1)
    have h : HasDerivAt (fun z => exp (-((n + 1 : ℕ) : ℂ) * W z) *
        (lambertPC n).eval (W z) / (1 + W z) ^ (2 * n + 1)) _ z :=
      (ha.mul hb).div hc (pow_ne_zero _ hw1)
    rw [h.deriv, lambertPC_succ_eval]
    simp only [Pi.mul_apply, Function.comp_apply]
    have he : exp (-((n + 1 + 1 : ℕ) : ℂ) * W z) =
        exp (-((n + 1 : ℕ) : ℂ) * W z) * exp (-W z) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [he, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, show 2 * n + 1 - 1 = 2 * n by omega]
    generalize exp (-((n + 1 : ℕ) : ℂ) * W z) = E1
    generalize exp (-W z) = E2
    generalize W z = w at hw1 ⊢
    field_simp
    push_cast
    ring

theorem one_add_lambertW_ne_zero (k : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    1 + lambertW k z ≠ 0 := by
  intro h
  have hm1 : lambertW k z = -1 := by linear_combination h
  have hW := dlmf_4_13_1 k z
  rw [hm1] at hW
  rw [← hW, mem_slitPlane_iff] at hz
  have he : (-1 : ℂ) * exp (-1) = ((-Real.exp (-1) : ℝ) : ℂ) := by push_cast; ring
  rw [he] at hz
  rcases hz with h | h
  · rw [ofReal_re] at h; linarith [Real.exp_pos (-1)]
  · exact h (ofReal_im _)

/-- **DLMF 4.13.4_1** for every branch on `ℂ ∖ (−∞, 0]`. -/
theorem dlmf_4_13_4_1_complex (k : ℤ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv (n + 1) (lambertW k) z = exp (-((n + 1 : ℕ) : ℂ) * lambertW k z) *
      (lambertPC n).eval (lambertW k z) / (1 + lambertW k z) ^ (2 * n + 1) :=
  iteratedDeriv_of_lambert_ode isOpen_slitPlane (fun _ hy => (dlmf_4_13_4 k hy).1)
    (fun _ hy => one_add_lambertW_ne_zero k hy) n hz

/-- **DLMF 4.13.4_1** for `W₀` on `ℂ ∖ (−∞, −e⁻¹]`. -/
theorem dlmf_4_13_4_1_W0 (n : ℕ) {z : ℂ} (hz : z ∈ cutW0) :
    iteratedDeriv (n + 1) (lambertW 0) z = exp (-((n + 1 : ℕ) : ℂ) * lambertW 0 z) *
      (lambertPC n).eval (lambertW 0 z) / (1 + lambertW 0 z) ^ (2 * n + 1) := by
  refine iteratedDeriv_of_lambert_ode isOpen_cutW0 (fun _ hy => dlmf_4_13_W0_analytic hy)
    (fun y hy => ?_) n hz
  intro h
  have hm1 : lambertW 0 y = -1 := by linear_combination h
  have hW := dlmf_4_13_1 0 y
  rw [hm1] at hW
  apply hy
  rw [← hW, show (-1 : ℂ) * exp (-1) = ((-Real.exp (-1) : ℝ) : ℂ) by push_cast; ring]
  exact ⟨ofReal_im _, le_of_eq (ofReal_re _)⟩

/-! ### 4.13.12–4.13.14 on `ℂ ∖ (−∞, 0]` -/

theorem lambertW_ne_zero (k : ℤ) {z : ℂ} (hz : z ≠ 0) : lambertW k z ≠ 0 := fun h => by
  have := dlmf_4_13_1 k z; rw [h] at this; simp at this; exact hz this.symm

theorem hasDerivAt_lambertW' (k : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (lambertW k) (lambertW k z / (z * (1 + lambertW k z))) z := by
  obtain ⟨h1, h2⟩ := dlmf_4_13_4 k hz
  rwa [h2] at h1

/-- **DLMF 4.13.12**: `∫ W dz = z/W + zW − z`. -/
theorem dlmf_4_13_12_complex (k : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z => z / lambertW k z + z * lambertW k z - z) (lambertW k z) z := by
  have hW := hasDerivAt_lambertW' k hz
  have hz0 := slitPlane_ne_zero hz
  have hw0 := lambertW_ne_zero k hz0
  have hw1 := one_add_lambertW_ne_zero k hz
  have h : HasDerivAt (fun z => z / lambertW k z + z * lambertW k z - z) _ z :=
    (((hasDerivAt_id' z).div hW hw0).add ((hasDerivAt_id' z).mul hW)).sub (hasDerivAt_id' z)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **DLMF 4.13.13**: `∫ W/z dz = W²/2 + W`. -/
theorem dlmf_4_13_13_complex (k : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z => lambertW k z ^ 2 / 2 + lambertW k z) (lambertW k z / z) z := by
  have hW := hasDerivAt_lambertW' k hz
  have hz0 := slitPlane_ne_zero hz
  have hw1 := one_add_lambertW_ne_zero k hz
  have h : HasDerivAt (fun z => lambertW k z ^ 2 / 2 + lambertW k z) _ z :=
    ((hW.pow 2).div_const 2).add hW
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **DLMF 4.13.14**: `2∫ sin W dz = z(1 + 1/W) sin W − z cos W`. -/
theorem dlmf_4_13_14_complex (k : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z => z * (1 + 1 / lambertW k z) * sin (lambertW k z) -
      z * cos (lambertW k z)) (2 * sin (lambertW k z)) z := by
  have hW := hasDerivAt_lambertW' k hz
  have hz0 := slitPlane_ne_zero hz
  have hw0 := lambertW_ne_zero k hz0
  have hw1 := one_add_lambertW_ne_zero k hz
  have h : HasDerivAt (fun z => z * (1 + 1 / lambertW k z) * sin (lambertW k z) -
      z * cos (lambertW k z)) _ z :=
    (((hasDerivAt_id' z).mul ((hasDerivAt_const z (1 : ℂ)).add
      ((hasDerivAt_const z (1 : ℂ)).div hW hw0))).mul hW.csin).sub
      ((hasDerivAt_id' z).mul hW.ccos)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply]
  field_simp
  ring

end Azurite.DLMF
