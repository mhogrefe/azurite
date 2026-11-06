/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section2Pow

/-!
# DLMF §4.8: Identities

Formalizations of <https://dlmf.nist.gov/4.8>. `Ln z` is the set `genLogSet z` of all values
`ln z + 2kπi`; `ln` is Mathlib's `Complex.log` (`ph ∈ (−π, π]`, the open definition 4.2.5). The
DLMF's default is the closed definition (§4.2(i)): `ph z ∈ [−π, π]`, two-valued on the cut; its
values form `closedLogSet z = {ln |z| + iθ : z = |z|e^{iθ}, θ ∈ [−π, π]}` (and `closedPowSet` of
§4.2(iv) for powers). Identities whose range includes an endpoint `±π` are proved for the closed
definition, and for `Complex.log` on the half-open range (with a counterexample at the excluded
endpoint, as §4.2(i) explains for 4.8.7).

* 4.8.1, 4.8.3: `dlmf_4_8_1`, `dlmf_4_8_3` (equalities of sets of values).
* 4.8.2, 4.8.4: closed `dlmf_4_8_2`, `dlmf_4_8_4`; open `dlmf_4_8_2_open`, `dlmf_4_8_4_open`;
  `dlmf_4_8_2_open_fails`.
* 4.8.5: **erratum** — read like 4.8.1 ("every value … and vice versa"), `Ln(zⁿ) = n Ln z` holds
  only for `n = ±1`; in general every value of `n Ln z` is a value of `Ln(zⁿ)`
  (`dlmf_4_8_5`, `dlmf_4_8_5_pm_one`, `dlmf_4_8_5_erratum`).
* 4.8.6, 4.8.7: closed `dlmf_4_8_6`, `dlmf_4_8_7`; open `dlmf_4_8_6_open`, `dlmf_4_8_7_open`.
* 4.8.8–4.8.10: `dlmf_4_8_8`, `dlmf_4_8_9` (closed), `dlmf_4_8_9_open`, `dlmf_4_8_10`.
* 4.8.11–4.8.13: `dlmf_4_8_11`, `dlmf_4_8_12` (with `Re(−iz ln a) = Im(z ln a)`),
  `dlmf_4_8_12_closed`, `dlmf_4_8_13`.
* 4.8.14–4.8.17: `dlmf_4_8_14`; `dlmf_4_8_15` (closed), `dlmf_4_8_15_open`; `dlmf_4_8_16`;
  `dlmf_4_8_17` (closed), `dlmf_4_8_17_open`, and "The restriction on `z₁` can be removed when
  `z₂` is an integer" (`dlmf_4_8_17_int`).
-/

open Complex Set
open scoped Real Pointwise

namespace Azurite.DLMF

/-! ### Closed principal values -/

/-- The values of `ln z` under the closed definition: `ln |z| + iθ`, `z = |z|e^{iθ}`,
`θ ∈ [−π, π]`. -/
def closedLogSet (z : ℂ) : Set ℂ :=
  {w | ∃ θ : ℝ, -π ≤ θ ∧ θ ≤ π ∧ z = ‖z‖ * exp (θ * I) ∧ w = Real.log ‖z‖ + θ * I}

theorem log_mem_closedLogSet (z : ℂ) : log z ∈ closedLogSet z :=
  ⟨arg z, (neg_pi_lt_arg z).le, arg_le_pi z, (norm_mul_exp_arg_mul_I z).symm, by
    rw [log]⟩

theorem closedLogSet_subset {z : ℂ} (hz : z ≠ 0) : closedLogSet z ⊆ genLogSet z := by
  rintro w ⟨θ, -, -, hθ, rfl⟩
  exact (polar_iff_mem_genLogSet hz θ).mp hθ

/-- A polar form `z = |z| e^{iθ}` gives the value `ln |z| + iθ`. -/
theorem mem_closedLogSet_of {z : ℂ} {θ : ℝ} (h1 : -π ≤ θ) (h2 : θ ≤ π)
    (hθ : z = ‖z‖ * exp (θ * I)) : (Real.log ‖z‖ + θ * I : ℂ) ∈ closedLogSet z :=
  ⟨θ, h1, h2, hθ, rfl⟩

/-- `ln` is determined by `exp` and the range `(−π, π]` of the phase. -/
theorem log_eq_of_exp {z w : ℂ} (h : exp w = z) (h1 : -π < w.im) (h2 : w.im ≤ π) :
    log z = w := by
  rw [← h, log_exp h1 h2]

/-! ### §4.8(i) Logarithms -/

/-- **DLMF 4.8.1**: `Ln(z₁z₂) = Ln z₁ + Ln z₂` (`z₁z₂ ≠ 0`): every value of the left side is a
value of the right side, and vice versa. -/
theorem dlmf_4_8_1 {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    genLogSet (z₁ * z₂) = genLogSet z₁ + genLogSet z₂ := by
  ext w
  rw [mem_genLogSet_iff (mul_ne_zero h₁ h₂), Set.mem_add]
  constructor
  · intro h
    refine ⟨w - log z₂, ?_, log z₂, ?_, by ring⟩
    · rw [mem_genLogSet_iff h₁, exp_sub, h, exp_log h₂]; field_simp
    · rw [mem_genLogSet_iff h₂, exp_log h₂]
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [exp_add, (mem_genLogSet_iff h₁ a).mp ha, (mem_genLogSet_iff h₂ b).mp hb]

/-- **DLMF 4.8.2** (closed definition): for phases `θⱼ ∈ [−π, π]` of `zⱼ` with
`−π ≤ θ₁ + θ₂ ≤ π`, `ln z₁ + ln z₂` is a value of `ln(z₁z₂)`. -/
theorem dlmf_4_8_2 {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) {θ₁ θ₂ : ℝ}
    (hθ₁ : z₁ = ‖z₁‖ * exp (θ₁ * I)) (hθ₂ : z₂ = ‖z₂‖ * exp (θ₂ * I))
    (hs₁ : -π ≤ θ₁ + θ₂) (hs₂ : θ₁ + θ₂ ≤ π) :
    (Real.log ‖z₁‖ + θ₁ * I) + (Real.log ‖z₂‖ + θ₂ * I) ∈ closedLogSet (z₁ * z₂) := by
  have e1 : Real.log ‖z₁ * z₂‖ = Real.log ‖z₁‖ + Real.log ‖z₂‖ := by
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h₁) (norm_ne_zero_iff.mpr h₂)]
  refine ⟨θ₁ + θ₂, hs₁, hs₂, ?_, ?_⟩
  · conv_lhs => rw [hθ₁, hθ₂]
    rw [norm_mul]; push_cast; rw [show ((θ₁ : ℂ) + θ₂) * I = θ₁ * I + θ₂ * I by ring, exp_add]
    ring
  · rw [e1]; push_cast; ring

/-- **DLMF 4.8.2** for `Complex.log` (open definition): `−π < ph z₁ + ph z₂ ≤ π`. -/
theorem dlmf_4_8_2_open {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0)
    (hs₁ : -π < arg z₁ + arg z₂) (hs₂ : arg z₁ + arg z₂ ≤ π) :
    log (z₁ * z₂) = log z₁ + log z₂ :=
  log_eq_of_exp (by rw [exp_add, exp_log h₁, exp_log h₂]) (by simpa [log_im] using hs₁)
    (by simpa [log_im] using hs₂)

/-- With `Complex.log` the endpoint `ph z₁ + ph z₂ = −π` must be excluded: `z₁ = z₂ = −i`. -/
theorem dlmf_4_8_2_open_fails : log (-I * -I) ≠ log (-I) + log (-I) := by
  rw [neg_mul_neg, I_mul_I, log_neg_one, log_neg_I]
  intro h
  have := congrArg im h
  simp at this
  linarith [Real.pi_pos]

/-- **DLMF 4.8.3**: `Ln(z₁/z₂) = Ln z₁ − Ln z₂`. -/
theorem dlmf_4_8_3 {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    genLogSet (z₁ / z₂) = genLogSet z₁ - genLogSet z₂ := by
  ext w
  rw [mem_genLogSet_iff (div_ne_zero h₁ h₂), Set.mem_sub]
  constructor
  · intro h
    refine ⟨w + log z₂, ?_, log z₂, ?_, by ring⟩
    · rw [mem_genLogSet_iff h₁, exp_add, h, exp_log h₂]; field_simp
    · rw [mem_genLogSet_iff h₂, exp_log h₂]
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [exp_sub, (mem_genLogSet_iff h₁ a).mp ha, (mem_genLogSet_iff h₂ b).mp hb]

/-- **DLMF 4.8.4** (closed definition): for phases with `−π ≤ θ₁ − θ₂ ≤ π`, `ln z₁ − ln z₂` is a
value of `ln(z₁/z₂)`. -/
theorem dlmf_4_8_4 {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) {θ₁ θ₂ : ℝ}
    (hθ₁ : z₁ = ‖z₁‖ * exp (θ₁ * I)) (hθ₂ : z₂ = ‖z₂‖ * exp (θ₂ * I))
    (hs₁ : -π ≤ θ₁ - θ₂) (hs₂ : θ₁ - θ₂ ≤ π) :
    (Real.log ‖z₁‖ + θ₁ * I) - (Real.log ‖z₂‖ + θ₂ * I) ∈ closedLogSet (z₁ / z₂) := by
  have hn : ‖z₂‖ ≠ 0 := norm_ne_zero_iff.mpr h₂
  have e1 : Real.log ‖z₁ / z₂‖ = Real.log ‖z₁‖ - Real.log ‖z₂‖ := by
    rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr h₁) hn]
  refine ⟨θ₁ - θ₂, hs₁, hs₂, ?_, ?_⟩
  · conv_lhs => rw [hθ₁, hθ₂]
    rw [norm_div]; push_cast
    rw [show ((θ₁ : ℂ) - θ₂) * I = θ₁ * I - θ₂ * I by ring, exp_sub]
    have : (‖z₂‖ : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp
  · rw [e1]; push_cast; ring

/-- **DLMF 4.8.4** for `Complex.log`: `−π < ph z₁ − ph z₂ ≤ π`. -/
theorem dlmf_4_8_4_open {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0)
    (hs₁ : -π < arg z₁ - arg z₂) (hs₂ : arg z₁ - arg z₂ ≤ π) :
    log (z₁ / z₂) = log z₁ - log z₂ :=
  log_eq_of_exp (by rw [exp_sub, exp_log h₁, exp_log h₂]) (by simpa [log_im] using hs₁)
    (by simpa [log_im] using hs₂)

/-- **DLMF 4.8.5**: every value of `n Ln z` is a value of `Ln(zⁿ)` (`n ∈ ℤ`, `z ≠ 0`). -/
theorem dlmf_4_8_5 {z : ℂ} (hz : z ≠ 0) (n : ℤ) :
    (fun w => (n : ℂ) * w) '' genLogSet z ⊆ genLogSet (z ^ n) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_genLogSet_iff (zpow_ne_zero n hz), Complex.exp_int_mul, (mem_genLogSet_iff hz w).mp hw]

/-- **DLMF 4.8.5** for `n = ±1`: `Ln(z^{±1}) = ±Ln z` as sets. -/
theorem dlmf_4_8_5_pm_one {z : ℂ} (hz : z ≠ 0) :
    genLogSet (z ^ (1 : ℤ)) = (fun w => ((1 : ℤ) : ℂ) * w) '' genLogSet z ∧
      genLogSet (z ^ (-1 : ℤ)) = (fun w => ((-1 : ℤ) : ℂ) * w) '' genLogSet z := by
  constructor
  · ext v; simp
  · ext v
    simp only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul, mem_image]
    rw [mem_genLogSet_iff (inv_ne_zero hz)]
    constructor
    · intro h
      refine ⟨-v, (mem_genLogSet_iff hz _).mpr ?_, neg_neg v⟩
      rw [exp_neg, h, inv_inv]
    · rintro ⟨w, hw, rfl⟩
      rw [exp_neg, (mem_genLogSet_iff hz w).mp hw]

/-- **Erratum to DLMF 4.8.5**: read like 4.8.1 ("every value of the left side is one of the values
of the right side, and vice versa"), `Ln(zⁿ) = n Ln z` is false for `n ≠ ±1`: `2πi` is a value of
`Ln(1²)` but not of `2 Ln 1`, and of `Ln(1⁰)` but not of `0 · Ln 1`. -/
theorem dlmf_4_8_5_erratum :
    (2 * π * I : ℂ) ∈ genLogSet ((1 : ℂ) ^ (2 : ℤ)) ∧
      (2 * π * I : ℂ) ∉ (fun w => ((2 : ℤ) : ℂ) * w) '' genLogSet 1 ∧
      (2 * π * I : ℂ) ∈ genLogSet ((1 : ℂ) ^ (0 : ℤ)) ∧
      (2 * π * I : ℂ) ∉ (fun w => ((0 : ℤ) : ℂ) * w) '' genLogSet 1 := by
  have hmem : (2 * π * I : ℂ) ∈ genLogSet 1 := ⟨1, by simp⟩
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨by simpa using hmem, ?_, by simpa using hmem, ?_⟩
  · rintro ⟨w, ⟨k, rfl⟩, h⟩
    simp only [log_one, zero_add, Int.cast_ofNat] at h
    have h' : ((4 * k : ℤ) : ℂ) * (π * I) = ((2 : ℤ) : ℂ) * (π * I) := by
      push_cast; linear_combination h
    have := mul_right_cancel₀ (mul_ne_zero hpi I_ne_zero) h'
    have : (4 * k : ℤ) = 2 := by exact_mod_cast this
    omega
  · rintro ⟨w, -, h⟩
    simp only [Int.cast_zero, zero_mul] at h
    have := congrArg im h
    simp at this

/-- **DLMF 4.8.6** (closed definition): for a phase `θ ∈ [−π, π]` of `z` with
`−π ≤ nθ ≤ π`, `n ln z` is a value of `ln(zⁿ)`. -/
theorem dlmf_4_8_6 {z : ℂ} (hz : z ≠ 0) (n : ℤ) {θ : ℝ} (hθ : z = ‖z‖ * exp (θ * I))
    (hs₁ : -π ≤ n * θ) (hs₂ : n * θ ≤ π) :
    (n : ℂ) * (Real.log ‖z‖ + θ * I) ∈ closedLogSet (z ^ n) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨n * θ, hs₁, hs₂, ?_, ?_⟩
  · conv_lhs => rw [hθ]
    rw [norm_zpow, mul_zpow, ← Complex.exp_int_mul]; push_cast; ring_nf
  · rw [norm_zpow, Real.log_zpow]; push_cast; ring

/-- **DLMF 4.8.6** for `Complex.log`: `−π < n ph z ≤ π`. -/
theorem dlmf_4_8_6_open {z : ℂ} (hz : z ≠ 0) (n : ℤ) (hs₁ : -π < n * arg z)
    (hs₂ : n * arg z ≤ π) : log (z ^ n) = n * log z :=
  log_eq_of_exp (by rw [Complex.exp_int_mul, exp_log hz])
    (by simpa [log_im] using hs₁) (by simpa [log_im] using hs₂)

/-- **DLMF 4.8.7** (closed definition): `ln(1/z) = −ln z` for every phase `θ ∈ [−π, π]` of `z`
(`|ph z| ≤ π`). -/
theorem dlmf_4_8_7 {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (h1 : -π ≤ θ) (h2 : θ ≤ π)
    (hθ : z = ‖z‖ * exp (θ * I)) :
    -(Real.log ‖z‖ + θ * I) ∈ closedLogSet (1 / z) := by
  have := dlmf_4_8_6 hz (-1) hθ (by push_cast; linarith) (by push_cast; linarith)
  simpa [one_div, zpow_neg_one] using this

/-- **DLMF 4.8.7** for `Complex.log`: valid only for `|ph z| < π` (§4.2(i)). -/
theorem dlmf_4_8_7_open {z : ℂ} (hz : arg z ≠ π) : log (1 / z) = -log z := by
  rw [one_div, log_inv _ hz]

/-- **DLMF 4.8.8**: `Ln(exp z) = z + 2kπi`, `k ∈ ℤ`. -/
theorem dlmf_4_8_8 (z : ℂ) : genLogSet (exp z) = {w | ∃ k : ℤ, w = z + 2 * k * π * I} := by
  ext w
  rw [mem_genLogSet_iff (exp_ne_zero z), exp_eq_exp_iff_exists_int]
  exact ⟨fun ⟨k, h⟩ => ⟨k, by rw [h]; ring⟩, fun ⟨k, h⟩ => ⟨k, by rw [h]; ring⟩⟩

/-- **DLMF 4.8.9** (closed definition): `ln(exp z) = z`, `−π ≤ Im z ≤ π`. -/
theorem dlmf_4_8_9 {z : ℂ} (h1 : -π ≤ z.im) (h2 : z.im ≤ π) : z ∈ closedLogSet (exp z) := by
  refine ⟨z.im, h1, h2, ?_, ?_⟩
  · rw [norm_exp, ofReal_exp, ← exp_add]; congr 1; exact (re_add_im z).symm
  · rw [norm_exp, Real.log_exp]; exact (re_add_im z).symm

/-- **DLMF 4.8.9** for `Complex.log`: `−π < Im z ≤ π`. -/
theorem dlmf_4_8_9_open {z : ℂ} (h1 : -π < z.im) (h2 : z.im ≤ π) : log (exp z) = z :=
  log_exp h1 h2

/-- **DLMF 4.8.10**: `exp(ln z) = exp(Ln z) = z` (`z ≠ 0`). -/
theorem dlmf_4_8_10 {z : ℂ} (hz : z ≠ 0) :
    exp (log z) = z ∧ ∀ w ∈ genLogSet z, exp w = z :=
  ⟨exp_log hz, fun w hw => (mem_genLogSet_iff hz w).mp hw⟩

/-- **DLMF 4.8.11**: for `a ≠ 0` and the general value `a^z = exp(zλ)`, `λ ∈ Ln a`:
`Ln(a^z) = zλ + 2kπi`, `k ∈ ℤ`. -/
theorem dlmf_4_8_11 {a ℓ : ℂ} (_hℓ : ℓ ∈ genLogSet a) (z : ℂ) :
    genLogSet (exp (z * ℓ)) = {w | ∃ k : ℤ, w = z * ℓ + 2 * k * π * I} :=
  dlmf_4_8_8 (z * ℓ)

/-- **DLMF 4.8.12**: for `a ≠ 0` and the principal value, `ln(a^z) = z ln a + 2kπi`, the integer `k`
chosen with `Re(−iz ln a) + 2kπ ∈ (−π, π]` (it is unique; `Re(−iz ln a) = Im(z ln a)`). -/
theorem dlmf_4_8_12 {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    (∃ k : ℤ, log (a ^ z) = z * log a + 2 * k * π * I ∧
      (-I * z * log a).re + 2 * k * π ∈ Ioc (-π) π) ∧
    ∀ k k' : ℤ, (-I * z * log a).re + 2 * k * π ∈ Ioc (-π) π →
      (-I * z * log a).re + 2 * k' * π ∈ Ioc (-π) π → k = k' := by
  have hre : (-I * z * log a).re = (z * log a).im := by simp
  have hpow : a ^ z = exp (z * log a) := (dlmf_4_2_28 ha z).1
  constructor
  · have hmem : log (a ^ z) ∈ genLogSet (exp (z * log a)) := by
      rw [← hpow]; exact (mem_genLogSet_iff (by rw [hpow]; exact exp_ne_zero _) _).mpr
        (exp_log (by rw [hpow]; exact exp_ne_zero _))
    rw [dlmf_4_8_8] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, hk, ?_⟩
    have him := congrArg im hk
    rw [log_im] at him
    rw [hre]
    generalize z * log a = W at him ⊢
    simp at him
    constructor
    · have := neg_pi_lt_arg (a ^ z); linarith
    · have := arg_le_pi (a ^ z); linarith
  · intro k k' h h'
    rw [hre] at h h'
    have hk : (k : ℝ) - k' < 1 := by
      have : 2 * ((k : ℝ) - k') * π < 2 * π := by linarith [h.1, h.2, h'.1, h'.2]
      nlinarith [Real.pi_pos]
    have hk' : (k' : ℝ) - k < 1 := by
      have : 2 * ((k' : ℝ) - k) * π < 2 * π := by linarith [h.1, h.2, h'.1, h'.2]
      nlinarith [Real.pi_pos]
    have h1 : k - k' < 1 := by exact_mod_cast hk
    have h2 : k' - k < 1 := by exact_mod_cast hk'
    omega

/-- **DLMF 4.8.12** (closed definition): for every integer `k` with
`Re(−iz ln a) + 2kπ ∈ [−π, π]`, `z ln a + 2kπi` is a value of `ln(a^z)`. -/
theorem dlmf_4_8_12_closed {a : ℂ} (ha : a ≠ 0) (z : ℂ) (k : ℤ)
    (h : (-I * z * log a).re + 2 * k * π ∈ Icc (-π) π) :
    z * log a + 2 * k * π * I ∈ closedLogSet (a ^ z) := by
  have hre : (-I * z * log a).re = (z * log a).im := by simp
  have hpow : a ^ z = exp (z * log a + 2 * k * π * I) := by
    rw [(dlmf_4_2_28 ha z).1, exp_add,
      show 2 * (k : ℂ) * π * I = k * (2 * π * I) by ring, exp_int_mul_two_pi_mul_I, mul_one]
  rw [hpow]
  rw [hre] at h
  generalize z * log a = W at h ⊢
  apply dlmf_4_8_9 <;> simp <;> linarith [h.1, h.2]

/-- **DLMF 4.8.13**: `ln(a^x) = x ln a`, `a > 0` (`x` real). -/
theorem dlmf_4_8_13 {a : ℝ} (ha : 0 < a) (x : ℝ) : Real.log (a ^ x) = x * Real.log a :=
  Real.log_rpow ha x

/-! ### §4.8(ii) Powers -/

/-- **DLMF 4.8.14**: `a^{z₁} a^{z₂} = a^{z₁+z₂}`, `a ≠ 0`. -/
theorem dlmf_4_8_14 {a : ℂ} (ha : a ≠ 0) (z₁ z₂ : ℂ) : a ^ z₁ * a ^ z₂ = a ^ (z₁ + z₂) :=
  (cpow_add z₁ z₂ ha).symm

/-- **DLMF 4.8.15** (closed definition): for phases `θ_a, θ_b ∈ [−π, π]` of `a, b` with
`−π ≤ θ_a + θ_b ≤ π`, `a^z b^z` is a value of `(ab)^z`. -/
theorem dlmf_4_8_15 {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (z : ℂ) {θa θb : ℝ}
    (hθa : a = ‖a‖ * exp (θa * I)) (hθb : b = ‖b‖ * exp (θb * I))
    (hs₁ : -π ≤ θa + θb) (hs₂ : θa + θb ≤ π) :
    exp (z * (Real.log ‖a‖ + θa * I)) * exp (z * (Real.log ‖b‖ + θb * I)) ∈
      closedPowSet (a * b) z := by
  obtain ⟨θ, h1, h2, h3, h4⟩ := dlmf_4_8_2 ha hb hθa hθb hs₁ hs₂
  refine ⟨θ, h1, h2, h3, ?_⟩
  rw [← exp_add, ← mul_add, h4]

/-- **DLMF 4.8.15** for the principal values: `a^z b^z = (ab)^z` when
`−π < ph a + ph b ≤ π`. -/
theorem dlmf_4_8_15_open {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (z : ℂ)
    (hs₁ : -π < arg a + arg b) (hs₂ : arg a + arg b ≤ π) :
    a ^ z * b ^ z = (a * b) ^ z := by
  rw [(dlmf_4_2_28 ha z).1, (dlmf_4_2_28 hb z).1, (dlmf_4_2_28 (mul_ne_zero ha hb) z).1,
    dlmf_4_8_2_open ha hb hs₁ hs₂, ← exp_add, mul_add]

/-- **DLMF 4.8.16**: `e^{z₁} e^{z₂} = e^{z₁+z₂}`. -/
theorem dlmf_4_8_16 (z₁ z₂ : ℂ) :
    (Real.exp 1 : ℂ) ^ z₁ * (Real.exp 1 : ℂ) ^ z₂ = (Real.exp 1 : ℂ) ^ (z₁ + z₂) := by
  rw [dlmf_4_2_32, dlmf_4_2_32, dlmf_4_2_32, exp_add]

/-- **DLMF 4.8.17** (closed definition): `(e^{z₁})^{z₂} = e^{z₁z₂}`, `−π ≤ Im z₁ ≤ π`
(a value of the closed principal power). -/
theorem dlmf_4_8_17 {z₁ : ℂ} (h1 : -π ≤ z₁.im) (h2 : z₁.im ≤ π) (z₂ : ℂ) :
    (Real.exp 1 : ℂ) ^ (z₁ * z₂) ∈ closedPowSet ((Real.exp 1 : ℂ) ^ z₁) z₂ := by
  rw [dlmf_4_2_32, dlmf_4_2_32]
  obtain ⟨θ, hθ1, hθ2, h3, h4⟩ := dlmf_4_8_9 h1 h2
  refine ⟨θ, hθ1, hθ2, h3, ?_⟩
  rw [← h4, mul_comm]

/-- **DLMF 4.8.17** for the principal value: `−π < Im z₁ ≤ π`. -/
theorem dlmf_4_8_17_open {z₁ : ℂ} (h1 : -π < z₁.im) (h2 : z₁.im ≤ π) (z₂ : ℂ) :
    ((Real.exp 1 : ℂ) ^ z₁) ^ z₂ = (Real.exp 1 : ℂ) ^ (z₁ * z₂) := by
  rw [dlmf_4_2_32, dlmf_4_2_32, (dlmf_4_2_28 (exp_ne_zero z₁) z₂).1, log_exp h1 h2, mul_comm]

/-- **DLMF §4.8(ii)**: "The restriction on `z₁` can be removed when `z₂` is an integer". -/
theorem dlmf_4_8_17_int (z₁ : ℂ) (n : ℤ) :
    ((Real.exp 1 : ℂ) ^ z₁) ^ (n : ℂ) = (Real.exp 1 : ℂ) ^ (z₁ * n) := by
  rw [dlmf_4_2_32, dlmf_4_2_32, cpow_intCast, ← Complex.exp_int_mul, mul_comm]

end Azurite.DLMF
