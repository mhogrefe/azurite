/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SqrtPiBracket
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.AzFloat.Equiv.LogBaseFloatBracket
import Azurite.AzFloat.Equiv.Rsqrt

/-!
# Equivalence: the brackets of `√π`, `1/√π` and `1/√τ`

`rsqrtFloor_err`/`rsqrtCeiling_err` (directed `rsqrtPrecRound`), `sqrtBracket_spec` and
`rsqrtBracket_spec` (a bracket `[lo, hi]` of `M` with `lo ≥ 2` gives a bracket of `√M` of width
`≤ (hi − lo)/2 + 4 hi 2^(−w)`, and one of `1/√M` of width `≤ (hi − lo)/4 + 4 · 2^(−w)`), the
specs of the three brackets with their width functions and limits, the irrationality of `√π`,
`√(2π)` and their reciprocals (a rational square root would make `π` rational:
`irrational_sqrt_of_irrational`), and the `Roundable` specs with the Ziv certificates.
-/

namespace Azurite.AzFloat

/-- The square root of a nonnegative irrational is irrational. -/
theorem irrational_sqrt_of_irrational {x : ℝ} (hx : 0 ≤ x) (h : Irrational x) :
    Irrational (Real.sqrt x) := by
  rintro ⟨q, hq⟩
  apply h
  refine ⟨q ^ 2, ?_⟩
  rw [Rat.cast_pow, hq, Real.sq_sqrt hx]

theorem irrational_sqrt_pi : Irrational (Real.sqrt Real.pi) :=
  irrational_sqrt_of_irrational Real.pi_pos.le irrational_pi

theorem irrational_two_mul_pi : Irrational (2 * Real.pi) := by
  simpa using irrational_pi.natCast_mul (by norm_num : (2 : ℕ) ≠ 0)

theorem irrational_sqrt_two_mul_pi : Irrational (Real.sqrt (2 * Real.pi)) :=
  irrational_sqrt_of_irrational (by linarith [Real.pi_pos]) irrational_two_mul_pi

/-! ### Directed reciprocal square roots -/

theorem rsqrtFloor_err {u : AzFloat} {uv : ℝ} (hu : u.toVal = some (uv : EReal)) (h0 : 0 < uv)
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (rsqrtPrecRound u w .Floor).1.toVal = some (r : EReal) ∧
      FloorOf w (Real.sqrt uv)⁻¹ r := by
  rw [rsqrtPrecRound_eq_liftVal, liftVal, hu, Option.bind_some, Spec.rsqrt_coe uv h0]
  exact roundVal_floor_err w (by positivity)

theorem rsqrtCeiling_err {u : AzFloat} {uv : ℝ} (hu : u.toVal = some (uv : EReal))
    (h0 : 0 < uv) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (rsqrtPrecRound u w .Ceiling).1.toVal = some (r : EReal) ∧
      CeilOf w (Real.sqrt uv)⁻¹ r := by
  rw [rsqrtPrecRound_eq_liftVal, liftVal, hu, Option.bind_some, Spec.rsqrt_coe uv h0]
  exact roundVal_ceiling_err w (by positivity)

/-! ### The square root and reciprocal square root of a bracket -/

/-- Facts about `√lo ≤ √hi` for `2 ≤ lo ≤ hi`. -/
theorem sqrt_facts {lo hi : ℝ} (h2 : 2 ≤ lo) (hlh : lo ≤ hi) :
    7 / 5 ≤ Real.sqrt lo ∧ Real.sqrt lo ≤ Real.sqrt hi ∧ Real.sqrt hi ≤ hi ∧
      Real.sqrt hi - Real.sqrt lo ≤ (hi - lo) / 2 ∧ 2 ≤ Real.sqrt lo * Real.sqrt hi := by
  have ha := Real.sqrt_nonneg lo
  have hb := Real.sqrt_nonneg hi
  have hsqlo : Real.sqrt lo ^ 2 = lo := Real.sq_sqrt (by linarith)
  have hsqhi : Real.sqrt hi ^ 2 = hi := Real.sq_sqrt (by linarith)
  have hab : Real.sqrt lo ≤ Real.sqrt hi := Real.sqrt_le_sqrt hlh
  have hlo1 : 7 / 5 ≤ Real.sqrt lo := by
    have := Real.sqrt_le_sqrt (by linarith : (7 / 5 : ℝ) ^ 2 ≤ lo)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hhi1 : Real.sqrt hi ≤ hi := by
    calc Real.sqrt hi ≤ Real.sqrt (hi ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = hi := Real.sqrt_sq (by linarith)
  have hdiff : Real.sqrt hi - Real.sqrt lo ≤ (hi - lo) / 2 := by
    have := mul_nonneg (by linarith : 0 ≤ Real.sqrt hi - Real.sqrt lo)
      (by linarith : 0 ≤ Real.sqrt hi + Real.sqrt lo - 2)
    nlinarith
  have hprod : 2 ≤ Real.sqrt lo * Real.sqrt hi := by
    have h2' : Real.sqrt 2 ≤ Real.sqrt lo := Real.sqrt_le_sqrt h2
    have h2'' : Real.sqrt 2 ≤ Real.sqrt hi := Real.sqrt_le_sqrt (by linarith)
    have := mul_le_mul h2' h2'' (Real.sqrt_nonneg 2) ha
    rw [Real.mul_self_sqrt (by norm_num)] at this
    exact this
  exact ⟨hlo1, hab, hhi1, hdiff, hprod⟩

/-- A bracket `[lo, hi]` of `M` with `2 ≤ lo` gives a bracket of `√M` with lower end `≥ 1` and
width at most `(hi − lo)/2 + 4 hi 2^(−w)`. -/
theorem sqrtBracket_spec {B : AzFloat × AzFloat} {lo hi M : ℝ}
    (hlo : B.1.toVal = some (lo : EReal)) (hhi : B.2.toVal = some (hi : EReal)) (h2 : 2 ≤ lo)
    (hloM : lo ≤ M) (hMhi : M ≤ hi) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo' hi' : ℝ, (sqrtBracket B w).1.toVal = some (lo' : EReal) ∧
      (sqrtBracket B w).2.toVal = some (hi' : EReal) ∧ 1 ≤ lo' ∧
      lo' ≤ Real.sqrt M ∧ Real.sqrt M ≤ hi' ∧
      hi' - lo' ≤ (hi - lo) / 2 + 4 * hi * (1 / 2 : ℝ) ^ w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lo', hlo', hf⟩ := sqrtFloor_err hlo (by linarith) w
  obtain ⟨hi', hhi', hc⟩ := sqrtCeiling_err hhi (by linarith) w
  obtain ⟨hlo1, hab, hhi1, hdiff, -⟩ := sqrt_facts h2 (by linarith)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu8 : u ≤ 1 / 8 := by
    rw [hu]
    calc (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  have ha := Real.sqrt_nonneg lo
  have hf1 := hf.le
  have hf2 := hf.ge
  have hc1 := hc.ge
  have hc2 := hc.le
  rw [← hu] at hf2 hc2
  refine ⟨lo', hi', hlo', hhi', ?_, hf1.trans (Real.sqrt_le_sqrt hloM),
    (Real.sqrt_le_sqrt hMhi).trans hc1, ?_⟩
  · have h2' : (7 / 5 : ℝ) * (1 - 2 * u) ≤ Real.sqrt lo * (1 - 2 * u) :=
      mul_le_mul_of_nonneg_right hlo1 (by linarith)
    nlinarith
  · have h3 : 2 * Real.sqrt hi * u ≤ 2 * hi * u := by nlinarith
    have h4 : 2 * Real.sqrt lo * u ≤ 2 * hi * u := by nlinarith
    rw [← hu]
    nlinarith

/-- A bracket `[lo, hi]` of `M` with `2 ≤ lo` gives a bracket of `1/√M` with width at most
`(hi − lo)/4 + 4 · 2^(−w)`. -/
theorem rsqrtBracket_spec {B : AzFloat × AzFloat} {lo hi M : ℝ}
    (hlo : B.1.toVal = some (lo : EReal)) (hhi : B.2.toVal = some (hi : EReal)) (h2 : 2 ≤ lo)
    (hloM : lo ≤ M) (hMhi : M ≤ hi) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo' hi' : ℝ, (rsqrtBracket B w).1.toVal = some (lo' : EReal) ∧
      (rsqrtBracket B w).2.toVal = some (hi' : EReal) ∧
      lo' ≤ (Real.sqrt M)⁻¹ ∧ (Real.sqrt M)⁻¹ ≤ hi' ∧
      hi' - lo' ≤ (hi - lo) / 4 + 4 * (1 / 2 : ℝ) ^ w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lo', hlo', hf⟩ := rsqrtFloor_err hhi (by linarith) w
  obtain ⟨hi', hhi', hc⟩ := rsqrtCeiling_err hlo (by linarith) w
  obtain ⟨hlo1, hab, -, hdiff, hprod⟩ := sqrt_facts h2 (by linarith)
  have hsl : 0 < Real.sqrt lo := by linarith
  have hsh : 0 < Real.sqrt hi := by linarith
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by linarith)
  have hA1 : (Real.sqrt lo)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hBA : (Real.sqrt hi)⁻¹ ≤ (Real.sqrt lo)⁻¹ := inv_anti₀ hsl hab
  have hB0 : 0 < (Real.sqrt hi)⁻¹ := inv_pos.mpr hsh
  have hprodinv : (Real.sqrt lo)⁻¹ * (Real.sqrt hi)⁻¹ ≤ 1 / 2 := by
    rw [← mul_inv]
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hprod
    rwa [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at this
  have hsub : (Real.sqrt lo)⁻¹ - (Real.sqrt hi)⁻¹
      = (Real.sqrt hi - Real.sqrt lo) * ((Real.sqrt lo)⁻¹ * (Real.sqrt hi)⁻¹) := by
    field_simp
  have hwid : (Real.sqrt lo)⁻¹ - (Real.sqrt hi)⁻¹ ≤ (hi - lo) / 4 := by
    rw [hsub]
    calc (Real.sqrt hi - Real.sqrt lo) * ((Real.sqrt lo)⁻¹ * (Real.sqrt hi)⁻¹)
        ≤ (hi - lo) / 2 * (1 / 2) := mul_le_mul hdiff hprodinv (by positivity) (by linarith)
      _ = (hi - lo) / 4 := by ring
  have hf1 := hf.le
  have hf2 := hf.ge
  have hc1 := hc.ge
  have hc2 := hc.le
  have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  refine ⟨lo', hi', hlo', hhi', hf1.trans (inv_anti₀ hsM (Real.sqrt_le_sqrt hMhi)),
    (inv_anti₀ (by linarith) (Real.sqrt_le_sqrt hloM)).trans hc1, ?_⟩
  have h3 : 2 * (Real.sqrt lo)⁻¹ * (1 / 2 : ℝ) ^ w ≤ 2 * (1 / 2 : ℝ) ^ w := by
    have := mul_le_mul_of_nonneg_right hA1 hu
    linarith
  have h4 : 2 * (Real.sqrt hi)⁻¹ * (1 / 2 : ℝ) ^ w ≤ 2 * (1 / 2 : ℝ) ^ w := by
    have := mul_le_mul_of_nonneg_right (hBA.trans hA1) hu
    linarith
  linarith

/-! ### `√π` -/

/-- The width bound of `sqrtPiBracket`. -/
noncomputable def sqrtPiEps (w : ℕ) : ℝ :=
  piEps w / 2 + 4 * (Real.pi + piEps w) * (1 / 2 : ℝ) ^ w

theorem tendsto_sqrtPiEps : Filter.Tendsto sqrtPiEps Filter.atTop (nhds 0) := by
  have hp := tendsto_piEps
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => Real.pi) Filter.atTop (nhds Real.pi) :=
    tendsto_const_nhds
  have := (hp.div_const 2).add (((hA.add hp).const_mul 4).mul hu)
  simp only [mul_zero, add_zero, zero_div] at this
  exact this

theorem piBracket2_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, (piBracket2 w).1.toVal = some (lv : EReal) ∧
      (piBracket2 w).2.toVal = some (hv : EReal) ∧ 2 ≤ lv ∧ lv ≤ Real.pi ∧ Real.pi ≤ hv ∧
      hv - lv ≤ piEps w := by
  obtain ⟨lv, hv, hlv, hhv, -, hlo, hhi, hwid⟩ := piBracket_spec hw
  have hpi : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  exact ⟨max lv 2, hv, toVal_maxOf hlv toVal_two, hhv, le_max_right _ _, max_le hlo.le hpi, hhi,
    by linarith [le_max_left lv 2]⟩

theorem sqrtPiBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (sqrtPiBracket w).1.toVal = some (lo : EReal) ∧
      (sqrtPiBracket w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.sqrt Real.pi ∧ Real.sqrt Real.pi ≤ hi ∧ hi - lo ≤ sqrtPiEps w := by
  obtain ⟨lv, hv, hlv, hhv, h2, hlo, hhi, hwid⟩ := piBracket2_spec hw
  obtain ⟨lo, hi, hlo', hhi', -, h3, h4, h5⟩ :=
    sqrtBracket_spec (M := Real.pi) hlv hhv h2 hlo hhi hw
  refine ⟨lo, hi, hlo', hhi', h3, h4, ?_⟩
  unfold sqrtPiEps
  have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have : 4 * hv * (1 / 2 : ℝ) ^ w ≤ 4 * (Real.pi + piEps w) * (1 / 2 : ℝ) ^ w :=
    mul_le_mul_of_nonneg_right (by linarith) hu
  linarith

theorem sqrtPiApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sqrtPiApprox w).1 lv ∧ Rounds (sqrtPiApprox w).2 hv ∧
      lv < Real.sqrt Real.pi ∧ Real.sqrt Real.pi < hv ∧ hv - lv ≤ sqrtPiEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := sqrtPiBracket_spec hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 irrational_sqrt_pi
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The termination certificate for `√π`. -/
theorem sqrtPiApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (sqrtPiApprox (w₀ * 2 ^ f)).1 (sqrtPiApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode sqrtPiApprox irrational_sqrt_pi sqrtPiEps
    tendsto_sqrtPiEps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := sqrtPiApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### `1/√π` -/

/-- The width bound of `oneDivSqrtPiBracket`. -/
noncomputable def oneDivSqrtPiEps (w : ℕ) : ℝ := piEps w / 4 + 4 * (1 / 2 : ℝ) ^ w

theorem tendsto_oneDivSqrtPiEps : Filter.Tendsto oneDivSqrtPiEps Filter.atTop (nhds 0) := by
  have hp := tendsto_piEps
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have := (hp.div_const 4).add (hu.const_mul 4)
  simp only [mul_zero, add_zero, zero_div] at this
  exact this

theorem oneDivSqrtPiBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (oneDivSqrtPiBracket w).1.toVal = some (lo : EReal) ∧
      (oneDivSqrtPiBracket w).2.toVal = some (hi : EReal) ∧
      lo ≤ (Real.sqrt Real.pi)⁻¹ ∧ (Real.sqrt Real.pi)⁻¹ ≤ hi ∧ hi - lo ≤ oneDivSqrtPiEps w := by
  obtain ⟨lv, hv, hlv, hhv, h2, hlo, hhi, hwid⟩ := piBracket2_spec hw
  obtain ⟨lo, hi, hlo', hhi', h3, h4, h5⟩ :=
    rsqrtBracket_spec (M := Real.pi) hlv hhv h2 hlo hhi hw
  refine ⟨lo, hi, hlo', hhi', h3, h4, ?_⟩
  unfold oneDivSqrtPiEps
  linarith

theorem oneDivSqrtPiApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (oneDivSqrtPiApprox w).1 lv ∧ Rounds (oneDivSqrtPiApprox w).2 hv ∧
      lv < (Real.sqrt Real.pi)⁻¹ ∧ (Real.sqrt Real.pi)⁻¹ < hv ∧ hv - lv ≤ oneDivSqrtPiEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := oneDivSqrtPiBracket_spec hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 irrational_sqrt_pi.inv
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The termination certificate for `1/√π`. -/
theorem oneDivSqrtPiApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (oneDivSqrtPiApprox (w₀ * 2 ^ f)).1
      (oneDivSqrtPiApprox (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode oneDivSqrtPiApprox irrational_sqrt_pi.inv
    oneDivSqrtPiEps tendsto_oneDivSqrtPiEps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := oneDivSqrtPiApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### `1/√τ` -/

/-- The width bound of `oneDivSqrtTauBracket`. -/
noncomputable def oneDivSqrtTauEps (w : ℕ) : ℝ := piEps w / 2 + 4 * (1 / 2 : ℝ) ^ w

theorem tendsto_oneDivSqrtTauEps : Filter.Tendsto oneDivSqrtTauEps Filter.atTop (nhds 0) := by
  have hp := tendsto_piEps
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have := (hp.div_const 2).add (hu.const_mul 4)
  simp only [mul_zero, add_zero, zero_div] at this
  exact this

theorem oneDivSqrtTauBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (oneDivSqrtTauBracket w).1.toVal = some (lo : EReal) ∧
      (oneDivSqrtTauBracket w).2.toVal = some (hi : EReal) ∧
      lo ≤ (Real.sqrt (2 * Real.pi))⁻¹ ∧ (Real.sqrt (2 * Real.pi))⁻¹ ≤ hi ∧
      hi - lo ≤ oneDivSqrtTauEps w := by
  obtain ⟨lv, hv, hlv, hhv, h2, hlo, hhi, hwid⟩ := piBracket2_spec hw
  have hlv' := toVal_shiftLeft_of_toVal hlv (AzInt.ofInt 1)
  have hhv' := toVal_shiftLeft_of_toVal hhv (AzInt.ofInt 1)
  rw [AzInt.toInt_ofInt, zpow_one] at hlv' hhv'
  obtain ⟨lo, hi, hlo', hhi', h3, h4, h5⟩ :=
    rsqrtBracket_spec
      (B := ((piBracket2 w).1 <<< AzInt.ofInt 1, (piBracket2 w).2 <<< AzInt.ofInt 1))
      (lo := lv * 2) (hi := hv * 2) (M := 2 * Real.pi) hlv' hhv' (by linarith) (by linarith)
      (by linarith) hw
  refine ⟨lo, hi, hlo', hhi', h3, h4, ?_⟩
  unfold oneDivSqrtTauEps
  linarith

theorem oneDivSqrtTauApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (oneDivSqrtTauApprox w).1 lv ∧ Rounds (oneDivSqrtTauApprox w).2 hv ∧
      lv < (Real.sqrt (2 * Real.pi))⁻¹ ∧ (Real.sqrt (2 * Real.pi))⁻¹ < hv ∧
      hv - lv ≤ oneDivSqrtTauEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := oneDivSqrtTauBracket_spec hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 irrational_sqrt_two_mul_pi.inv
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The termination certificate for `1/√τ`. -/
theorem oneDivSqrtTauApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (oneDivSqrtTauApprox (w₀ * 2 ^ f)).1
      (oneDivSqrtTauApprox (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode oneDivSqrtTauApprox
    irrational_sqrt_two_mul_pi.inv oneDivSqrtTauEps tendsto_oneDivSqrtTauEps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := oneDivSqrtTauApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

end Azurite.AzFloat
