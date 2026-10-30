/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# DLMF Table 1.14.1: Fourier transforms (elementary rows)

Rows of <https://dlmf.nist.gov/1.14.T1> for `𝓕f(x) = (2π)^{−1/2} ∫ f(t) e^{ixt} dt`
(`dlmfFourier`).  Hyperbolic rows: `Section14TableHyperbolic.lean`; `sin(at²)`, `cos(at²)`:
`Section14TableFresnel.lean`.

* Half-line integrals for `ℜc > 0`: `integral_Ioi_cexp_neg` (`1/c`), `integral_Ioi_mul_cexp_neg`
  (`1/c²`), `integral_Ioi_rpow_neg_half_mul_cexp` (`(π/c)^{1/2}`, via `t = u²` and the complex
  Gaussian); `integral_eq_Ioi_add_neg`, `dlmfFourier_split` (split at `0`).
* Principal square roots: `re_cpow_half_pos`, `two_mul_re_cpow_half_sq`, `cpow_half_conj`.
* Rows: `dlmf_table_1_14_1_r1` (box, `x ≠ 0`; `_r1_zero` at `x = 0`), `_r2` (`e^{−a|t|}`), `_r3`
  (`t e^{−a|t|}`), `_r4` (`|t| e^{−a|t|}`), `_r5` (`e^{−a|t|}/|t|^{1/2}`), `_r8` (`e^{−at²}`).
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Half-line integrals -/

theorem integral_Ioi_cexp_neg {c : ℂ} (hc : 0 < c.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-(c * t)) = 1 / c := by
  have h := integral_exp_mul_complex_Ioi (a := -c) (by simpa using hc) 0
  simp only [neg_mul, ofReal_zero, mul_zero, Complex.exp_zero] at h
  rw [h]; field_simp

theorem integrableOn_Ioi_rpow_mul_cexp_neg {c : ℂ} (hc : 0 < c.re) {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun t : ℝ => ((t ^ s : ℝ) : ℂ) * cexp (-(c * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hs one_pos hc
  refine h.ofReal.mono'
    (((by fun_prop : Measurable fun t : ℝ => ((t ^ s : ℝ) : ℂ)).aestronglyMeasurable).mul
    ((by fun_prop : Continuous fun t : ℝ => cexp (-(c * t))).aestronglyMeasurable)
    |>.restrict) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg
    (Real.rpow_nonneg (le_of_lt ht) _), Real.rpow_one]
  simp [mul_comm]

/-- `∫_0^∞ t e^{−ct} dt = 1/c²` for `ℜc > 0`. -/
theorem integral_Ioi_mul_cexp_neg {c : ℂ} (hc : 0 < c.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-(c * t)) = 1 / c ^ 2 := by
  have hc0 : c ≠ 0 := fun h => by rw [h] at hc; simp at hc
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -((t : ℂ) / c + 1 / c ^ 2) * cexp (-(c * t)))
      ((t : ℂ) * cexp (-(c * t))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => cexp (-(c * t))) (cexp (-(c * t)) * -c) t := by
      have := ((hasDerivAt_id t).ofReal_comp.const_mul c).neg.cexp
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => -((t : ℂ) / c + 1 / c ^ 2)) (-(1 / c)) t := by
      have := (((hasDerivAt_id t).ofReal_comp.div_const c).add_const (1 / c ^ 2)).neg
      convert this using 1
      funext u; simp
    convert h2.mul h1 using 1
    field_simp; ring
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) * cexp (-(c * t))) (Ioi 0) := by
    refine (integrableOn_Ioi_rpow_mul_cexp_neg hc (s := 1) (by norm_num)).congr_fun
      (fun t _ => by simp) measurableSet_Ioi
  have hlim : Tendsto (fun t : ℝ => -((t : ℂ) / c + 1 / c ^ 2) * cexp (-(c * t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (t : ℂ) * cexp (-(c * t))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have h := (this.comp (tendsto_id.const_mul_atTop hc))
      have h' := h.div_const c.re
      rw [zero_div] at h'
      refine h'.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with t ht
      simp only [Function.comp, pow_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht,
        Complex.norm_exp, id]
      field_simp
      simp [mul_comm]
    have h2 : Tendsto (fun t : ℝ => cexp (-(c * t))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
      refine this.congr fun t => ?_
      simp [Complex.norm_exp, mul_comm]
    have := ((h1.div_const c).add (h2.const_mul (1 / c ^ 2))).neg
    simp only [zero_div, mul_zero, add_zero, neg_zero] at this
    refine this.congr fun t => ?_
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim]
  simp

/-- `∫_ℝ g = ∫_0^∞ g(t) dt + ∫_0^∞ g(−t) dt`. -/
theorem integral_eq_Ioi_add_neg {g : ℝ → ℂ} (hpos : IntegrableOn g (Ioi 0))
    (hneg : IntegrableOn (fun t => g (-t)) (Ioi 0)) :
    ∫ t, g t = (∫ t in Ioi (0 : ℝ), g t) + ∫ t in Ioi (0 : ℝ), g (-t) := by
  have hI : IntegrableOn g (Iic 0) := by
    have := ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (by simpa using hneg)).comp_neg_Iic
      (c := (0 : ℝ)) (f := fun t => g (-t))
    simpa using this
  rw [← intervalIntegral.integral_Iic_add_Ioi hI hpos, integral_comp_neg_Ioi, neg_zero, add_comm]

theorem two_div_sqrt_two_pi : 2 / √(2 * π) = √(2 / π) := by
  rw [Real.sqrt_div' 2 Real.pi_pos.le, Real.sqrt_mul' 2 Real.pi_pos.le]
  have h2 : √2 ≠ 0 := by positivity
  have hπ : √π ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

theorem cexp_phase_pos (x t : ℝ) (c : ℂ) :
    cexp (-(c * t)) * cexp (I * x * t) = cexp (-((c - I * x) * t)) := by
  rw [← Complex.exp_add]; ring_nf

/-! ### Rows -/

/-- **Table 1.14.1, row 1**: `f(t) = 1` for `|t| < a`, `0` for `|t| > a` (`a > 0`):
`𝓕f(x) = √(2/π) sin(ax)/x` (`x ≠ 0`; the value at `x = 0` is the limit `√(2/π) a`,
`dlmf_table_1_14_1_r1_zero`). -/
theorem dlmf_table_1_14_1_r1 {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≠ 0) :
    dlmfFourier (fun t => if |t| < a then 1 else 0) x =
      ((√(2 / π) * Real.sin (a * x) / x : ℝ) : ℂ) := by
  have hset : {t : ℝ | |t| < a} = Ioo (-a) a := by ext t; simp [abs_lt]
  have e : (fun t : ℝ => (if |t| < a then (1 : ℂ) else 0) * cexp (I * x * t)) =
      Set.indicator (Ioo (-a) a) (fun t => cexp ((I * x) * t)) := by
    funext t
    simp only [indicator, mem_Ioo, ← abs_lt]
    split_ifs <;> simp
  have hIx : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx)
  unfold dlmfFourier
  rw [e, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), integral_exp_mul_complex hIx]
  simp only [ofReal_neg, mul_neg]
  rw [← two_div_sqrt_two_pi]
  have hs : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := sqrt_two_pi_ne_zero
  push_cast
  rw [Complex.sin, show -((a : ℂ) * x) * I = -(I * x * a) by ring,
    show ((a : ℂ) * x) * I = I * x * a by ring]
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem dlmf_table_1_14_1_r1_zero {a : ℝ} (ha : 0 < a) :
    dlmfFourier (fun t => if |t| < a then 1 else 0) 0 = ((√(2 / π) * a : ℝ) : ℂ) := by
  have e : (fun t : ℝ => (if |t| < a then (1 : ℂ) else 0) * cexp (I * (0 : ℝ) * t)) =
      Set.indicator (Ioo (-a) a) (fun _ => (1 : ℂ)) := by
    funext t
    simp only [indicator, mem_Ioo, ← abs_lt]
    split_ifs <;> simp
  unfold dlmfFourier
  rw [e, integral_indicator measurableSet_Ioo, setIntegral_const]
  simp only [measureReal_def, Real.volume_Ioo, sub_neg_eq_add]
  rw [ENNReal.toReal_ofReal (by linarith), ← two_div_sqrt_two_pi, Complex.real_smul]
  push_cast
  field_simp
  ring

/-- DLMF's transform split at `0`. -/
theorem dlmfFourier_split {f : ℝ → ℂ} {x : ℝ}
    (hpos : IntegrableOn (fun t : ℝ => f t * cexp (I * x * t)) (Ioi 0))
    (hneg : IntegrableOn (fun t : ℝ => f (-t) * cexp (-(I * x * t))) (Ioi 0)) :
    dlmfFourier f x = ((√(2 * π) : ℝ) : ℂ)⁻¹ * ((∫ t in Ioi (0 : ℝ), f t * cexp (I * x * t)) +
      ∫ t in Ioi (0 : ℝ), f (-t) * cexp (-(I * x * t))) := by
  unfold dlmfFourier
  congr 1
  have e : ∀ t : ℝ, f (-t) * cexp (I * x * ((-t : ℝ) : ℂ)) = f (-t) * cexp (-(I * x * t)) :=
    fun t => by push_cast; ring_nf
  rw [integral_eq_Ioi_add_neg (g := fun t : ℝ => f t * cexp (I * x * t)) hpos
    (by simpa only [e] using hneg)]
  simp only [e]

/-- **Table 1.14.1, row 2**: `𝓕[e^{−a|t|}](x) = √(2/π) a/(a² + x²)` (`a > 0`). -/
theorem dlmf_table_1_14_1_r2 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    dlmfFourier (fun t => (Real.exp (-(a * |t|)) : ℂ)) x =
      ((√(2 / π) * (a / (a ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
  set c₁ : ℂ := a - I * x
  set c₂ : ℂ := a + I * x
  have hc1 : 0 < c₁.re := by simpa [c₁] using ha
  have hc2 : 0 < c₂.re := by simpa [c₂] using ha
  have e1 : EqOn (fun t : ℝ => (Real.exp (-(a * |t|)) : ℂ) * cexp (I * x * t))
      (fun t : ℝ => cexp (-(c₁ * t))) (Ioi 0) := fun t ht => by
    simp only [c₁]
    rw [abs_of_pos (mem_Ioi.mp ht), ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf
  have e2 : EqOn (fun t : ℝ => (Real.exp (-(a * |-t|)) : ℂ) * cexp (-(I * x * t)))
      (fun t : ℝ => cexp (-(c₂ * t))) (Ioi 0) := fun t ht => by
    simp only [c₂]
    rw [abs_neg, abs_of_pos (mem_Ioi.mp ht), ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf
  have i1 : IntegrableOn (fun t : ℝ => cexp (-(c₁ * t))) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_complex_Ioi (a := -c₁) (by simpa using hc1) 0
  have i2 : IntegrableOn (fun t : ℝ => cexp (-(c₂ * t))) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_complex_Ioi (a := -c₂) (by simpa using hc2) 0
  rw [dlmfFourier_split (i1.congr_fun e1.symm measurableSet_Ioi)
    (i2.congr_fun e2.symm measurableSet_Ioi), setIntegral_congr_fun measurableSet_Ioi e1,
    setIntegral_congr_fun measurableSet_Ioi e2, integral_Ioi_cexp_neg hc1,
    integral_Ioi_cexp_neg hc2, ← two_div_sqrt_two_pi]
  have h1 : c₁ ≠ 0 := fun h => by rw [h] at hc1; simp at hc1
  have h2 : c₂ ≠ 0 := fun h => by rw [h] at hc2; simp at hc2
  have hs : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := sqrt_two_pi_ne_zero
  have h3 : ((a : ℂ) ^ 2 + (x : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : a ^ 2 + x ^ 2 ≠ 0)
  have hprod : c₁ * c₂ = (a : ℂ) ^ 2 + (x : ℂ) ^ 2 := by
    simp only [c₁, c₂]; ring_nf; rw [I_sq]; ring
  push_cast
  rw [div_add_div _ _ h1 h2, hprod]
  field_simp
  simp only [c₁, c₂]
  ring

theorem integrableOn_Ioi_mul_cexp_neg {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * cexp (-(c * t))) (Ioi 0) :=
  (integrableOn_Ioi_rpow_mul_cexp_neg hc (s := 1) (by norm_num)).congr_fun
    (fun t _ => by simp) measurableSet_Ioi

/-- The two exponents `a ∓ ix` and their product `a² + x²`. -/
theorem prod_conj_exponents (a x : ℝ) :
    ((a : ℂ) - I * x) * ((a : ℂ) + I * x) = (a : ℂ) ^ 2 + (x : ℂ) ^ 2 := by
  ring_nf; rw [I_sq]; ring

/-- **Table 1.14.1, row 3**: `𝓕[t e^{−a|t|}](x) = √(2/π) 2iax/(a² + x²)²` (`a > 0`). -/
theorem dlmf_table_1_14_1_r3 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    dlmfFourier (fun t => (t : ℂ) * (Real.exp (-(a * |t|)) : ℂ)) x =
      (√(2 / π) : ℝ) * (2 * I * a * x / ((a : ℂ) ^ 2 + (x : ℂ) ^ 2) ^ 2) := by
  set c₁ : ℂ := a - I * x
  set c₂ : ℂ := a + I * x
  have hc1 : 0 < c₁.re := by simpa [c₁] using ha
  have hc2 : 0 < c₂.re := by simpa [c₂] using ha
  have e1 : EqOn (fun t : ℝ => (t : ℂ) * (Real.exp (-(a * |t|)) : ℂ) * cexp (I * x * t))
      (fun t : ℝ => (t : ℂ) * cexp (-(c₁ * t))) (Ioi 0) := fun t ht => by
    simp only [c₁]
    rw [abs_of_pos (mem_Ioi.mp ht), ofReal_exp, mul_assoc, ← Complex.exp_add]; push_cast; ring_nf
  have e2 : EqOn (fun t : ℝ => ((-t : ℝ) : ℂ) * (Real.exp (-(a * |-t|)) : ℂ) * cexp (-(I * x * t)))
      (fun t : ℝ => -((t : ℂ) * cexp (-(c₂ * t)))) (Ioi 0) := fun t ht => by
    simp only [c₂]
    rw [abs_neg, abs_of_pos (mem_Ioi.mp ht), ofReal_exp, mul_assoc, ← Complex.exp_add]
    push_cast; ring_nf
  rw [dlmfFourier_split ((integrableOn_Ioi_mul_cexp_neg hc1).congr_fun e1.symm measurableSet_Ioi)
    ((integrableOn_Ioi_mul_cexp_neg hc2).neg.congr_fun e2.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioi e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_neg, integral_Ioi_mul_cexp_neg hc1, integral_Ioi_mul_cexp_neg hc2,
    ← two_div_sqrt_two_pi]
  have h1 : c₁ ≠ 0 := fun h => by rw [h] at hc1; simp at hc1
  have h2 : c₂ ≠ 0 := fun h => by rw [h] at hc2; simp at hc2
  have hs : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := sqrt_two_pi_ne_zero
  have hprod : c₁ * c₂ = (a : ℂ) ^ 2 + (x : ℂ) ^ 2 := prod_conj_exponents a x
  have h3 : (a : ℂ) ^ 2 + (x : ℂ) ^ 2 ≠ 0 := hprod ▸ mul_ne_zero h1 h2
  rw [← hprod]
  push_cast
  field_simp
  simp only [c₁, c₂]
  ring_nf

/-- **Table 1.14.1, row 4**: `𝓕[|t| e^{−a|t|}](x) = √(2/π) (a² − x²)/(a² + x²)²` (`a > 0`). -/
theorem dlmf_table_1_14_1_r4 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    dlmfFourier (fun t => ((|t| : ℝ) : ℂ) * (Real.exp (-(a * |t|)) : ℂ)) x =
      ((√(2 / π) * ((a ^ 2 - x ^ 2) / (a ^ 2 + x ^ 2) ^ 2) : ℝ) : ℂ) := by
  set c₁ : ℂ := a - I * x
  set c₂ : ℂ := a + I * x
  have hc1 : 0 < c₁.re := by simpa [c₁] using ha
  have hc2 : 0 < c₂.re := by simpa [c₂] using ha
  have e1 : EqOn (fun t : ℝ => ((|t| : ℝ) : ℂ) * (Real.exp (-(a * |t|)) : ℂ) * cexp (I * x * t))
      (fun t : ℝ => (t : ℂ) * cexp (-(c₁ * t))) (Ioi 0) := fun t ht => by
    simp only [c₁]
    rw [abs_of_pos (mem_Ioi.mp ht), ofReal_exp, mul_assoc, ← Complex.exp_add]; push_cast; ring_nf
  have e2 : EqOn
      (fun t : ℝ => ((|-t| : ℝ) : ℂ) * (Real.exp (-(a * |-t|)) : ℂ) * cexp (-(I * x * t)))
      (fun t : ℝ => (t : ℂ) * cexp (-(c₂ * t))) (Ioi 0) := fun t ht => by
    simp only [c₂]
    rw [abs_neg, abs_of_pos (mem_Ioi.mp ht), ofReal_exp, mul_assoc, ← Complex.exp_add]
    push_cast; ring_nf
  rw [dlmfFourier_split ((integrableOn_Ioi_mul_cexp_neg hc1).congr_fun e1.symm measurableSet_Ioi)
    ((integrableOn_Ioi_mul_cexp_neg hc2).congr_fun e2.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioi e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_Ioi_mul_cexp_neg hc1, integral_Ioi_mul_cexp_neg hc2, ← two_div_sqrt_two_pi]
  have h1 : c₁ ≠ 0 := fun h => by rw [h] at hc1; simp at hc1
  have h2 : c₂ ≠ 0 := fun h => by rw [h] at hc2; simp at hc2
  have hs : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := sqrt_two_pi_ne_zero
  have hprod : c₁ * c₂ = (a : ℂ) ^ 2 + (x : ℂ) ^ 2 := prod_conj_exponents a x
  have h3 : (a : ℂ) ^ 2 + (x : ℂ) ^ 2 ≠ 0 := hprod ▸ mul_ne_zero h1 h2
  push_cast
  rw [← hprod]
  field_simp
  simp only [c₁, c₂]
  ring_nf
  rw [I_sq]
  ring

theorem cpow_half_ofReal {r : ℝ} (hr : 0 ≤ r) : (r : ℂ) ^ (1 / 2 : ℂ) = ((√r : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr]; norm_num

/-- **Table 1.14.1, row 8**: `𝓕[e^{−at²}](x) = (2a)^{−1/2} e^{−x²/(4a)}` (`a > 0`). -/
theorem dlmf_table_1_14_1_r8 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    dlmfFourier (fun t => (Real.exp (-(a * t ^ 2)) : ℂ)) x =
      ((1 / √(2 * a) * Real.exp (-(x ^ 2 / (4 * a))) : ℝ) : ℂ) := by
  have h := fourierIntegral_gaussian (b := (a : ℂ)) (by simpa using ha) (x : ℂ)
  unfold dlmfFourier
  have e : (fun t : ℝ => (Real.exp (-(a * t ^ 2)) : ℂ) * cexp (I * x * t)) =
      fun t : ℝ => cexp (I * x * t) * cexp (-(a : ℂ) * t ^ 2) := by
    funext t; rw [ofReal_exp, mul_comm]; push_cast; ring_nf
  rw [e, h, show (π : ℂ) / a = ((π / a : ℝ) : ℂ) by push_cast; ring,
    cpow_half_ofReal (by positivity)]
  have hpi : 0 < π := Real.pi_pos
  rw [Real.sqrt_div' π ha.le, Real.sqrt_mul' 2 hpi.le, Real.sqrt_mul' 2 ha.le]
  have h2 : (0 : ℝ) < √2 := by positivity
  have hpi' : (0 : ℝ) < √π := Real.sqrt_pos.mpr hpi
  have ha' : (0 : ℝ) < √a := Real.sqrt_pos.mpr ha
  push_cast
  have h2c : ((√2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  have hpc : ((√π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi'.ne'
  have hac : ((√a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha'.ne'
  rw [neg_div]
  field_simp

/-! ### Row 5: principal square roots -/

theorem re_cpow_half_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ (1 / 2 : ℂ)).re := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  rw [cpow_def_of_ne_zero hw0, Complex.exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  have harg := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  rw [abs_lt] at harg
  have : (Complex.log w * (1 / 2)).im = w.arg / 2 := by simp [Complex.log_im]; ring
  rw [this]
  constructor <;> linarith [Real.pi_pos]

theorem cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact cpow_nat_inv_pow w (by norm_num)

/-- `2 (ℜ√w)² = |w| + ℜw`. -/
theorem two_mul_re_cpow_half_sq (w : ℂ) :
    2 * (w ^ (1 / 2 : ℂ)).re ^ 2 = ‖w‖ + w.re := by
  set z := w ^ (1 / 2 : ℂ)
  have hsq : z ^ 2 = w := cpow_half_sq w
  have hre : w.re = z.re ^ 2 - z.im ^ 2 := by rw [← hsq]; simp [sq]
  have hn : ‖w‖ = z.re ^ 2 + z.im ^ 2 := by
    rw [← hsq, norm_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hre, hn]; ring

theorem cpow_half_conj {w : ℂ} (hw : 0 < w.re) :
    (starRingEnd ℂ w) ^ (1 / 2 : ℂ) = starRingEnd ℂ (w ^ (1 / 2 : ℂ)) := by
  have hne : w.arg ≠ π := by
    intro h
    have := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
    rw [h, abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_pos]
  rw [conj_cpow w _ hne]
  congr 2
  simp only [map_div₀, map_one]
  rw [show (starRingEnd ℂ) 2 = 2 from Complex.conj_ofNat 2]

/-- `∫_0^∞ t^{−1/2} e^{−ct} dt = (π/c)^{1/2}` for `ℜc > 0` (substitute `t = u²`). -/
theorem integral_Ioi_rpow_neg_half_mul_cexp {c : ℂ} (hc : 0 < c.re) :
    ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * cexp (-(c * t)) =
      ((π : ℂ) / c) ^ (1 / 2 : ℂ) := by
  have h := integral_comp_rpow_Ioi (fun t : ℝ => ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * cexp (-(c * t)))
    (p := 2) (by norm_num)
  rw [← h]
  have e : EqOn (fun x : ℝ => ((|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) : ℝ) •
      ((((x ^ (2 : ℝ)) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * cexp (-(c * ((x ^ (2 : ℝ) : ℝ) : ℂ)))))
      (fun x : ℝ => 2 * cexp (-c * (x : ℂ) ^ 2)) (Ioi 0) := by
    intro x hx
    have hx0 : 0 < x := hx
    simp only
    rw [← Real.rpow_mul hx0.le, show (2 : ℝ) * -(1 / 2) = -1 by norm_num, Real.rpow_neg_one,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, Complex.real_smul]
    have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
    push_cast
    field_simp
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_gaussian_complex_Ioi hc]
  ring

/-- **Table 1.14.1, row 5**:
`𝓕[e^{−a|t|}/|t|^{1/2}](x) = (a + (a² + x²)^{1/2})^{1/2}/(a² + x²)^{1/2}`
(`a > 0`). -/
theorem dlmf_table_1_14_1_r5 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    dlmfFourier (fun t => ((Real.exp (-(a * |t|)) / |t| ^ (1 / 2 : ℝ) : ℝ) : ℂ)) x =
      ((√(a + √(a ^ 2 + x ^ 2)) / √(a ^ 2 + x ^ 2) : ℝ) : ℂ) := by
  set c₁ : ℂ := a - I * x
  set c₂ : ℂ := a + I * x
  have hc1 : 0 < c₁.re := by simpa [c₁] using ha
  have hc2 : 0 < c₂.re := by simpa [c₂] using ha
  have hpow : ∀ t : ℝ, 0 < t → Real.exp (-(a * t)) / t ^ (1 / 2 : ℝ) =
      t ^ (-(1 / 2) : ℝ) * Real.exp (-(a * t)) := fun t ht => by
    rw [Real.rpow_neg ht.le]; ring
  have e1 : EqOn (fun t : ℝ => ((Real.exp (-(a * |t|)) / |t| ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      cexp (I * x * t)) (fun t : ℝ => ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * cexp (-(c₁ * t))) (Ioi 0) :=
    fun t ht => by
      simp only [c₁]
      rw [abs_of_pos (mem_Ioi.mp ht), hpow t ht, ofReal_mul, ofReal_exp, mul_assoc,
        ← Complex.exp_add]
      push_cast; ring_nf
  have e2 : EqOn (fun t : ℝ => ((Real.exp (-(a * |-t|)) / |-t| ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      cexp (-(I * x * t))) (fun t : ℝ => ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * cexp (-(c₂ * t)))
      (Ioi 0) := fun t ht => by
    simp only [c₂]
    rw [abs_neg, abs_of_pos (mem_Ioi.mp ht), hpow t ht, ofReal_mul, ofReal_exp, mul_assoc,
      ← Complex.exp_add]
    push_cast; ring_nf
  rw [dlmfFourier_split
    ((integrableOn_Ioi_rpow_mul_cexp_neg hc1 (s := -(1 / 2)) (by norm_num)).congr_fun e1.symm
      measurableSet_Ioi)
    ((integrableOn_Ioi_rpow_mul_cexp_neg hc2 (s := -(1 / 2)) (by norm_num)).congr_fun e2.symm
      measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioi e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_Ioi_rpow_neg_half_mul_cexp hc1, integral_Ioi_rpow_neg_half_mul_cexp hc2]
  -- `π/c₂` is the conjugate of `w = π/c₁`
  set w : ℂ := (π : ℂ) / c₁ with hw
  have hconj : (π : ℂ) / c₂ = starRingEnd ℂ w := by
    simp only [hw, c₁, c₂, map_div₀, Complex.conj_ofReal, map_sub, map_mul, Complex.conj_I]
    ring
  set r := √(a ^ 2 + x ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hrsq : r ^ 2 = a ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hns : Complex.normSq c₁ = a ^ 2 + x ^ 2 := by
    simp [c₁, Complex.normSq_apply]; ring
  have hwre : w.re = π * a / r ^ 2 := by
    simp only [hw, Complex.div_re, hns, hrsq]
    simp [c₁]
  have hwn : ‖w‖ = π / r := by
    rw [hw, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_def, hns]
  have hwpos : 0 < w.re := by rw [hwre]; positivity
  rw [hconj, cpow_half_conj hwpos, Complex.add_conj]
  set p := (w ^ (1 / 2 : ℂ)).re
  have hp : 0 < p := re_cpow_half_pos hwpos
  have hp2 : 2 * p ^ 2 = π / r + π * a / r ^ 2 := by
    have := two_mul_re_cpow_half_sq w; rw [hwn, hwre] at this; exact this
  have hp3 : 2 * p ^ 2 * r ^ 2 = π * (a + r) := by
    rw [hp2]; field_simp; ring
  -- the real identity `2p/√(2π) = √(a + r)/r`
  have key : 2 * p / √(2 * π) = √(a + r) / r := by
    have h1 : 0 ≤ 2 * p / √(2 * π) := by positivity
    have h2 : 0 ≤ √(a + r) / r := by positivity
    refine (sq_eq_sq₀ h1 h2).mp ?_
    rw [div_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have hpi : 0 < π := Real.pi_pos
    field_simp
    nlinarith [hp3]
  rw [← key]
  push_cast
  ring

end Azurite.DLMF
