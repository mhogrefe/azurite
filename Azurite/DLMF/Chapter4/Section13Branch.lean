/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Omega

/-!
# DLMF §4.13: the branches `W_k` of the Lambert `W`-function

`W_k(z) = ω(ln z + 2πik)` (`z ≠ 0`, `W_k(0) = 0`), with the principal `ln` (`ph ∈ (−π, π]`), so
that on the cuts the values are the limits from above (`W_{−1}(x) = W_{−1}(x + 0i)`).

* 4.13.1: `dlmf_4_13_1`; every solution of `W e^W = z` is some `W_k(z)`: `dlmf_4_13_1_all`.
* The real branches: `lambertW_zero_ofReal` (`W₀(x)` for `x ≥ −e⁻¹`) and
  `lambertW_neg_one_ofReal` (`W_{−1}(x + 0i)` for `−e⁻¹ ≤ x < 0`); 4.13.2: `dlmf_4_13_2`.
* `ω(z) = W_{𝒦(z)}(e^z)` with the unwinding number `𝒦(z) = ⌈(ℑz − π)/(2π)⌉`:
  `wrightOmega_eq_lambertW`; the tree function: `dlmf_4_13_1_3_complex`.
* Analyticity on `ℂ ∖ (−∞, 0]` with 4.13.4: `dlmf_4_13_4`.
* The images of the sheets (Figure 4.13.2): `lambertW_im_add_arg` (`ℑW + ph W ∈ (2πk − π, 2πk + π)`
  off the cut).
-/

open Set Filter Topology Complex
open scoped Real ComplexConjugate

namespace Azurite.DLMF

open Classical in
/-- **DLMF §4.13**: the branch `W_k(z) = ω(ln z + 2πik)` of the Lambert `W`-function. -/
noncomputable def lambertW (k : ℤ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else wrightOmega (log z + 2 * π * k * I)

theorem lambertW_zero_arg (k : ℤ) : lambertW k 0 = 0 := by simp [lambertW]

theorem lambertW_of_ne {k : ℤ} {z : ℂ} (hz : z ≠ 0) :
    lambertW k z = wrightOmega (log z + 2 * π * k * I) := by simp [lambertW, hz]

/-- **DLMF 4.13.1**: `W e^W = z` for every branch. -/
theorem dlmf_4_13_1 (k : ℤ) (z : ℂ) : lambertW k z * exp (lambertW k z) = z := by
  by_cases hz : z = 0
  · simp [lambertW, hz]
  · rw [lambertW_of_ne hz, wrightOmega_mul_exp, exp_add, exp_log hz]
    have : exp (2 * π * k * I) = 1 := by
      rw [show (2 * π * k * I : ℂ) = k * (2 * π * I) by ring]; exact exp_int_mul_two_pi_mul_I k
    rw [this, mul_one]

/-- **DLMF §4.13**: every solution of `W e^W = z` (`z ≠ 0`) is one of the `W_k(z)`. -/
theorem dlmf_4_13_1_all {z w : ℂ} (hz : z ≠ 0) (hw : w * exp w = z) :
    ∃ k : ℤ, lambertW k z = w := by
  have hw0 : w ≠ 0 := fun h => hz (by rw [← hw, h]; simp)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, w + log w = log z + k * (2 * π * I) := by
    apply exp_eq_exp_iff_exists_int.mp
    rw [exp_add, exp_log hw0, exp_log hz, ← hw, mul_comm]
  set ζ := log z + 2 * π * k * I
  have hζ : w + log w = ζ := by rw [hk]; simp only [ζ]; ring
  by_cases hLm : omegaLm ζ
  · exact absurd ⟨w, hw0, hζ⟩ (wrightOmega_add_log_of_Lm hLm).2
  by_cases hextra : ζ.im = π → w.im = 0 → -1 ≤ w.re
  · exact ⟨k, by rw [lambertW_of_ne hz]; exact wrightOmega_eq hLm ⟨hw0, hζ, hextra⟩⟩
  · -- `w` is the real root `< −1` on the cut: it is `W_{−1}(z)`
    push Not at hextra
    obtain ⟨him, hwim, hwre⟩ := hextra
    have hw' : w = (w.re : ℂ) := Complex.ext rfl (by simp [hwim])
    have hr : w.re < 0 := by linarith
    have hre := congrArg re hζ
    rw [hw', add_log_of_neg_real hr] at hre
    simp only at hre
    refine ⟨-1, ?_⟩
    rw [lambertW_of_ne hz]
    set ζ' := log z + 2 * π * ((-1 : ℤ) : ℂ) * I
    have hLm' : omegaLm ζ' := by
      constructor
      · have h1 : ζ.im = (log z).im + 2 * π * k := by simp [ζ]
        have h2 : ζ'.im = (log z).im - 2 * π := by simp [ζ']; ring
        -- `arg z + 2πk = π` with `arg z ∈ (−π, π]` forces `k = 0`
        have hk0 : (k : ℝ) = 0 := by
          have ha1 := neg_pi_lt_arg z
          have ha2 := arg_le_pi z
          rw [log_im] at h1
          have hlt : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
          have hgt : (-1 : ℝ) < k := by nlinarith [Real.pi_pos]
          have : k = 0 := by
            have := Int.cast_lt.mp (by simpa using hlt : (k : ℝ) < ((1 : ℤ) : ℝ))
            have := Int.cast_lt.mp (by simpa using hgt : ((-1 : ℤ) : ℝ) < k)
            omega
          simp [this]
        rw [h2]; rw [h1, hk0] at him; linarith
      · have h1 : ζ'.re = (log z).re := by simp [ζ']
        have h2 : ζ.re = (log z).re := by simp [ζ]
        rw [h1, ← h2, ← hre]
        have := Real.log_le_sub_one_of_pos (by linarith : 0 < -w.re)
        linarith
    rw [wrightOmega_of_Lm hLm', hw']
    congr 1
    have hz' : -Real.exp ζ'.re = w.re * Real.exp w.re := by
      have h1 : ζ'.re = (log z).re := by simp [ζ']
      have h2 : ζ.re = (log z).re := by simp [ζ]
      rw [h1, ← h2, ← hre, Real.exp_add, Real.exp_log (by linarith)]; ring
    rw [hz', dlmf_4_13_3_2 (lt_of_le_of_ne (by linarith) fun h => by linarith)]

/-! ### The real branches -/

/-- `W₀(x) = W₀(x)` (real) for `x ≥ −e⁻¹`. -/
theorem lambertW_zero_ofReal {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    lambertW 0 x = lambertW0 x := by
  obtain ⟨h1, h2⟩ := lambertW0_spec hx
  rcases lt_trichotomy x 0 with hx0 | rfl | hx0
  · rw [lambertW_of_ne (by exact_mod_cast hx0.ne)]
    have hw0 : lambertW0 x < 0 := by
      by_contra h; push Not at h
      have : 0 ≤ lambertW0 x * Real.exp (lambertW0 x) := mul_nonneg h (Real.exp_pos _).le
      linarith
    refine wrightOmega_eq ?_ ⟨by exact_mod_cast hw0.ne, ?_, fun _ _ => by simpa using h1⟩
    · rintro ⟨him, -⟩
      simp [log_im, arg_ofReal_of_neg hx0] at him; linarith [Real.pi_pos]
    · rw [add_log_of_neg_real hw0]
      apply Complex.ext
      · have h3 : -lambertW0 x * Real.exp (lambertW0 x) = -x := by linarith
        have h4 := congrArg Real.log h3
        rw [Real.log_mul (neg_ne_zero.mpr hw0.ne) (Real.exp_pos _).ne', Real.log_exp,
          Real.log_neg_eq_log, Real.log_neg_eq_log] at h4
        simp [log_re, abs_of_neg hx0]
        linarith
      · simp [log_im, arg_ofReal_of_neg hx0]
  · simp [lambertW_zero_arg, lambertW0_zero]
  · rw [lambertW_of_ne (by exact_mod_cast hx0.ne'), ← ofReal_log hx0.le]
    simp only [Int.cast_zero, mul_zero, zero_mul, add_zero]
    rw [wrightOmega_ofReal, wrightOmegaReal, Real.exp_log hx0]

/-- `W_{−1}(x + 0i) = W_{±1}(x ∓ 0i)` (real, `≤ −1`) for `−e⁻¹ ≤ x < 0`. -/
theorem lambertW_neg_one_ofReal {x : ℝ} (hx : -Real.exp (-1) ≤ x) (hx0 : x < 0) :
    lambertW (-1) x = lambertWm1 x := by
  rw [lambertW_of_ne (by exact_mod_cast hx0.ne)]
  have hlog : log (x : ℂ) = ⟨Real.log (-x), π⟩ := by
    apply Complex.ext
    · simp [log_re, abs_of_neg hx0]
    · simp [log_im, arg_ofReal_of_neg hx0]
  have hle : Real.log (-x) ≤ -1 := by
    have : Real.log (-x) ≤ Real.log (Real.exp (-1)) := Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_exp] at this
  have hLm : omegaLm (log (x : ℂ) + 2 * π * ((-1 : ℤ) : ℂ) * I) := by
    rw [hlog]
    refine ⟨by simp; ring, ?_⟩
    simpa using hle
  rw [wrightOmega_of_Lm hLm, hlog]
  have hre : ((⟨Real.log (-x), π⟩ : ℂ) + 2 * π * ((-1 : ℤ) : ℂ) * I).re = Real.log (-x) := by
    simp [-Real.log_neg_eq_log]
  rw [hre, Real.exp_log (by linarith), neg_neg]

/-- **DLMF 4.13.2**: `W₀(−e⁻¹) = W_{−1}(−e⁻¹ + 0i) = −1`, `W₀(0) = 0`, `W₀(e) = 1`. -/
theorem dlmf_4_13_2 :
    lambertW 0 (-Real.exp (-1) : ℝ) = -1 ∧ lambertW (-1) (-Real.exp (-1) : ℝ) = -1 ∧
      lambertW 0 0 = 0 ∧ lambertW 0 (Real.exp 1 : ℝ) = 1 := by
  refine ⟨?_, ?_, lambertW_zero_arg 0, ?_⟩
  · rw [lambertW_zero_ofReal le_rfl, lambertW0_neg_exp_neg_one]; simp
  · rw [lambertW_neg_one_ofReal le_rfl (by linarith [Real.exp_pos (-1)]),
      lambertWm1_neg_exp_neg_one]; simp
  · rw [lambertW_zero_ofReal (by linarith [Real.exp_pos (-1), Real.exp_pos 1]),
      lambertW0_exp_one]; simp

/-! ### `ω(z) = W(e^z)` and the tree function -/

/-- The unwinding number `𝒦(z) = ⌈(ℑz − π)/(2π)⌉`. -/
noncomputable def unwinding (z : ℂ) : ℤ := ⌈(z.im - π) / (2 * π)⌉

theorem log_exp_eq_sub_unwinding (z : ℂ) : log (exp z) = z - 2 * π * unwinding z * I := by
  have hk1 := Int.le_ceil ((z.im - π) / (2 * π))
  have hk2 := Int.ceil_lt_add_one ((z.im - π) / (2 * π))
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hq : (z.im - π) / (2 * π) * (2 * π) = z.im - π := div_mul_cancel₀ _ h2π.ne'
  have hk1' := mul_le_mul_of_nonneg_right hk1 h2π.le
  have hk2' := mul_lt_mul_of_pos_right hk2 h2π
  rw [hq] at hk1'
  rw [add_mul, hq, one_mul] at hk2'
  have hexp : exp z = exp (z - 2 * π * unwinding z * I) := by
    rw [exp_sub, show (2 * π * unwinding z * I : ℂ) = unwinding z * (2 * π * I) by ring,
      exp_int_mul_two_pi_mul_I, div_one]
  have him : (z - 2 * π * unwinding z * I).im = z.im - 2 * π * unwinding z := by simp
  have hK : ((unwinding z : ℤ) : ℝ) = ↑⌈(z.im - π) / (2 * π)⌉ := rfl
  rw [hexp, log_exp]
  · rw [him, hK]; linarith
  · rw [him, hK]; linarith

/-- **DLMF §4.13**: `ω(z) = W_{𝒦(z)}(e^z)`. -/
theorem wrightOmega_eq_lambertW (z : ℂ) : wrightOmega z = lambertW (unwinding z) (exp z) := by
  rw [lambertW_of_ne (exp_ne_zero z), log_exp_eq_sub_unwinding]
  congr 1; ring

/-- The tree function `T(z) = −W(−z)` (any branch). -/
noncomputable def treeTk (k : ℤ) (z : ℂ) : ℂ := -lambertW k (-z)

/-- **DLMF 4.13.1_3**: `T e^{−T} = z`. -/
theorem dlmf_4_13_1_3_complex (k : ℤ) (z : ℂ) : treeTk k z * exp (-treeTk k z) = z := by
  have := dlmf_4_13_1 k (-z)
  simp only [treeTk, neg_neg]
  linear_combination -this

/-! ### Analyticity and 4.13.4 -/

theorem not_omegaL_of_slitPlane {z : ℂ} (hz : z ∈ slitPlane) (k : ℤ) :
    ¬omegaLm (log z + 2 * π * k * I) ∧ ¬omegaLp (log z + 2 * π * k * I) := by
  have ha1 := neg_pi_lt_arg z
  have ha2 : arg z < π := by
    rcases lt_or_eq_of_le (arg_le_pi z) with h | h
    · exact h
    · exact absurd (arg_eq_pi_iff.mp h) (by
        rw [mem_slitPlane_iff] at hz
        rintro ⟨h1, h2⟩; rcases hz with h | h <;> [linarith; exact h h2])
  have him : (log z + 2 * π * k * I).im = arg z + 2 * π * k := by simp [log_im]
  -- `arg z + 2πk = ±π` is impossible for `arg z ∈ (−π, π)`
  have hne : ∀ s : ℝ, (s = 1 ∨ s = -1) → arg z + 2 * π * k ≠ s * π := by
    intro s hs he
    have hk1 : (k : ℝ) < (s + 1) / 2 := by nlinarith [Real.pi_pos]
    have hk2 : (s - 1) / 2 < (k : ℝ) := by nlinarith [Real.pi_pos]
    rcases hs with rfl | rfl
    · have h1 : k < 1 := by exact_mod_cast (by linarith : (k : ℝ) < 1)
      have h2 : 0 < k := by exact_mod_cast (by linarith : (0 : ℝ) < k)
      omega
    · have h1 : k < 0 := by exact_mod_cast (by linarith : (k : ℝ) < 0)
      have h2 : -1 < k := by exact_mod_cast (by linarith : (-1 : ℝ) < k)
      omega
  exact ⟨fun h => hne (-1) (Or.inr rfl) (by rw [← him, h.1]; ring),
    fun h => hne 1 (Or.inl rfl) (by rw [← him, h.1]; ring)⟩

/-- **DLMF 4.13.4**: `W_k` is analytic on `ℂ ∖ (−∞, 0]` with `dW/dz = e^{−W}/(1 + W) =
W/(z(1 + W))`. -/
theorem dlmf_4_13_4 (k : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (lambertW k) (exp (-lambertW k z) / (1 + lambertW k z)) z ∧
      exp (-lambertW k z) / (1 + lambertW k z) = lambertW k z / (z * (1 + lambertW k z)) := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨h1, h2⟩ := not_omegaL_of_slitPlane hz k
  have hω := hasDerivAt_wrightOmega h1 h2
  have hlog : HasDerivAt (fun z => log z + 2 * π * k * I) z⁻¹ z := by
    simpa using (hasDerivAt_log hz).add_const (2 * π * k * I)
  have hcomp := hω.comp z hlog
  have hev : lambertW k =ᶠ[𝓝 z] fun z => wrightOmega (log z + 2 * π * k * I) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
    exact lambertW_of_ne hw
  have hW := dlmf_4_13_1 k z
  rw [lambertW_of_ne hz0] at hW ⊢
  set W := wrightOmega (log z + 2 * π * k * I)
  have hW0 : W ≠ 0 := fun h => hz0 (by rw [← hW, h]; simp)
  have hW1 : 1 + W ≠ 0 := by
    intro h
    have hm1 : W = -1 := by linear_combination h
    rw [hm1] at hW
    rw [← hW, mem_slitPlane_iff] at hz
    have he : (-1 : ℂ) * exp (-1) = ((-Real.exp (-1) : ℝ) : ℂ) := by push_cast; ring
    rw [he] at hz
    rcases hz with h | h
    · rw [ofReal_re] at h; linarith [Real.exp_pos (-1)]
    · exact h (ofReal_im _)
  have hval : W / (1 + W) * z⁻¹ = exp (-W) / (1 + W) := by
    rw [← hW, exp_neg]; field_simp
  refine ⟨?_, ?_⟩
  · rw [← hval]
    exact hcomp.congr_of_eventuallyEq hev
  · rw [← hval]; field_simp

/-! ### Images of the sheets (Figure 4.13.2) -/

/-- **DLMF Figure 4.13.2**: off the cut, `W_k(z)` lies in the region `ℑW + ph W ∈ (2πk − π,
2πk + π)` (for `k = 0`, the region enclosed by the green curve `ξ = −η cot η`). -/
theorem lambertW_im_add_arg (k : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    (lambertW k z).im + arg (lambertW k z) = arg z + 2 * π * k := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨h1, -⟩ := not_omegaL_of_slitPlane hz k
  have := congrArg im (dlmf_4_13_1_2 h1)
  rw [add_log_im] at this
  rw [lambertW_of_ne hz0, this]
  simp [log_im]

end Azurite.DLMF
