/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section24
import Azurite.DLMF.Chapter4.Section32

/-!
# DLMF §4.40 Integrals (hyperbolic functions)

Formalizations of <https://dlmf.nist.gov/4.40>. An indefinite integral `∫ f dx = F` is stated as
`F′ = f` (`HasDerivAt`), as in §4.26.

* §4.40(i): "Throughout this section the variables are assumed to be real. The results in
  §§4.40(ii) and 4.40(iv) can be extended to the complex plane by using continuous branches and
  avoiding singularities." Each formula of §4.40(ii) is given for real `x` on DLMF's interval
  (`dlmf_4_40_n`) and for complex `z`, with the principal logarithm wherever its argument lies off
  the cut `(−∞, 0]` (`dlmf_4_40_n_complex`). Real `csch`, `sech`, `coth` are `1/sinh`, `1/cosh`,
  `1/tanh` (as in Table 4.30.1).
* §4.40(ii): 4.40.1–4.40.6. For 4.40.5 the real antiderivative is `gd` (the 4.23.39 integral,
  `hasDerivAt_gd`). Its complex extension is `arctan(sinh z)` (cf. 4.23.40, which gives
  `gd x = arctan(sinh x)`; `dlmf_4_40_5_complex_ofReal`), off the cuts of `arctan`.
-/

open Set Filter Topology MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### §4.40(ii) Indefinite Integrals, real -/

/-- **DLMF 4.40.1**: `∫ sinh x dx = cosh x`. -/
theorem dlmf_4_40_1 (x : ℝ) : HasDerivAt Real.cosh (Real.sinh x) x :=
  Real.hasDerivAt_cosh x

/-- **DLMF 4.40.2**: `∫ cosh x dx = sinh x`. -/
theorem dlmf_4_40_2 (x : ℝ) : HasDerivAt Real.sinh (Real.cosh x) x :=
  Real.hasDerivAt_sinh x

/-- **DLMF 4.40.3**: `∫ tanh x dx = ln(cosh x)`. -/
theorem dlmf_4_40_3 (x : ℝ) :
    HasDerivAt (fun x => Real.log (Real.cosh x)) (Real.tanh x) x := by
  refine ((Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne').congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]

/-- **DLMF 4.40.4**: `∫ csch x dx = ln(tanh(½x))`, `0 < x < ∞`. -/
theorem dlmf_4_40_4 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => Real.log (Real.tanh (1 / 2 * x))) (1 / Real.sinh x) x := by
  have hs : 0 < Real.sinh (1 / 2 * x) := Real.sinh_pos_iff.mpr (by linarith)
  have hc := Real.cosh_pos (1 / 2 * x)
  have ht : Real.tanh (1 / 2 * x) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]; exact div_ne_zero hs.ne' hc.ne'
  have hl : HasDerivAt (fun x : ℝ => 1 / 2 * x) (1 / 2) x := by
    simpa using (hasDerivAt_id x).const_mul (1 / 2 : ℝ)
  refine (((hasDerivAt_tanh' (1 / 2 * x)).comp x hl).log ht).congr_deriv ?_
  rw [Function.comp_apply, show Real.sinh x = Real.sinh (2 * (1 / 2 * x)) by ring_nf,
    Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- `gd′ = sech` (FTC for the 4.23.39 integral). -/
theorem hasDerivAt_gd (x : ℝ) : HasDerivAt gd (1 / Real.cosh x) x := by
  have hc : Continuous fun t : ℝ => 1 / Real.cosh t :=
    continuous_const.div Real.continuous_cosh fun t => (Real.cosh_pos t).ne'
  exact (hc.integral_hasStrictDerivAt 0 x).hasDerivAt

/-- **DLMF 4.40.5**: `∫ sech x dx = gd(x)` (4.23.39). -/
theorem dlmf_4_40_5 (x : ℝ) : HasDerivAt gd (1 / Real.cosh x) x := hasDerivAt_gd x

/-- **DLMF 4.40.6**: `∫ coth x dx = ln(sinh x)`, `0 < x < ∞`. -/
theorem dlmf_4_40_6 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => Real.log (Real.sinh x)) (1 / Real.tanh x) x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  refine ((Real.hasDerivAt_sinh x).log hs.ne').congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh, one_div_div]

/-! ### §4.40(ii), complex (§4.40(i)) -/

open Complex

/-- **DLMF 4.40.1**, complex: `∫ sinh z dz = cosh z`. -/
theorem dlmf_4_40_1_complex (z : ℂ) : HasDerivAt cosh (sinh z) z := hasDerivAt_cosh z

/-- **DLMF 4.40.2**, complex: `∫ cosh z dz = sinh z`. -/
theorem dlmf_4_40_2_complex (z : ℂ) : HasDerivAt sinh (cosh z) z := hasDerivAt_sinh z

/-- **DLMF 4.40.3**, complex: `∫ tanh z dz = ln(cosh z)` where `cosh z ∉ (−∞, 0]`. -/
theorem dlmf_4_40_3_complex {z : ℂ} (hz : cosh z ∈ slitPlane) :
    HasDerivAt (fun z => log (cosh z)) (tanh z) z := by
  refine ((hasDerivAt_cosh z).clog hz).congr_deriv ?_
  rw [tanh_eq_sinh_div_cosh]

/-- `tanh′ = 1/cosh²` where `cosh z ≠ 0`. -/
theorem hasDerivAt_ctanh {z : ℂ} (hz : cosh z ≠ 0) : HasDerivAt tanh (1 / cosh z ^ 2) z := by
  have hf : tanh = fun z => sinh z / cosh z := funext tanh_eq_sinh_div_cosh
  rw [hf]
  refine ((hasDerivAt_sinh z).div (hasDerivAt_cosh z) hz).congr_deriv ?_
  rw [show cosh z * cosh z - sinh z * sinh z = 1 by
    rw [← sq, ← sq, cosh_sq]; ring]

/-- **DLMF 4.40.4**, complex: `∫ csch z dz = ln(tanh ½z)` where `tanh ½z ∉ (−∞, 0]`. -/
theorem dlmf_4_40_4_complex {z : ℂ} (hz : tanh (1 / 2 * z) ∈ slitPlane) :
    HasDerivAt (fun z => log (tanh (1 / 2 * z))) (1 / sinh z) z := by
  have ht := slitPlane_ne_zero hz
  rw [tanh_eq_sinh_div_cosh] at ht
  have hc : cosh (1 / 2 * z) ≠ 0 := fun h => ht (by rw [h, div_zero])
  have hs : sinh (1 / 2 * z) ≠ 0 := fun h => ht (by rw [h, zero_div])
  have hl : HasDerivAt (fun z : ℂ => 1 / 2 * z) (1 / 2) z := by
    simpa using (hasDerivAt_id z).const_mul (1 / 2 : ℂ)
  refine (((hasDerivAt_ctanh hc).comp z hl).clog hz).congr_deriv ?_
  rw [Function.comp_apply, show sinh z = sinh (2 * (1 / 2 * z)) by ring_nf, sinh_two_mul,
    tanh_eq_sinh_div_cosh]
  field_simp

/-- **DLMF 4.40.5**, complex: `∫ sech z dz = arctan(sinh z)` where `sinh z` is off the cuts of
`arctan` (Figure 4.23.1(ii)); for real `x` this is `gd x` (`dlmf_4_40_5_complex_ofReal`). -/
theorem dlmf_4_40_5_complex {z : ℂ} (hz : sinh z ∈ arctanCut) :
    HasDerivAt (fun z => arctanD (sinh z)) (1 / cosh z) z := by
  have hc : cosh z ≠ 0 := fun h => by
    have := cosh_sq z
    rw [h] at this
    have hs : sinh z ^ 2 = -1 := by linear_combination -this
    have h1 : (sinh z - I) * (sinh z + I) = 0 := by linear_combination hs - I_sq
    rcases mul_eq_zero.mp h1 with h1 | h1
    · rw [sub_eq_zero.mp h1] at hz; rcases hz with h | h <;> simp at h
    · rw [eq_neg_of_add_eq_zero_left h1] at hz; rcases hz with h | h <;> simp at h
  refine ((dlmf_4_24_9 hz).comp z (hasDerivAt_sinh z)).congr_deriv ?_
  rw [show 1 + sinh z ^ 2 = cosh z ^ 2 by rw [cosh_sq]; ring]
  field_simp

/-- For real `x` the complex antiderivative of 4.40.5 is `gd x` (4.23.40), and `sinh x` is off
the cuts. -/
theorem dlmf_4_40_5_complex_ofReal (x : ℝ) :
    sinh (x : ℂ) ∈ arctanCut ∧ arctanD (sinh (x : ℂ)) = gd x := by
  rw [← ofReal_sinh, (dlmf_4_23_40 x).2.2.2.1]
  exact ⟨Or.inr (by simp), rfl⟩

/-- **DLMF 4.40.6**, complex: `∫ coth z dz = ln(sinh z)` where `sinh z ∉ (−∞, 0]`. -/
theorem dlmf_4_40_6_complex {z : ℂ} (hz : sinh z ∈ slitPlane) :
    HasDerivAt (fun z => log (sinh z)) (cosh z / sinh z) z :=
  (hasDerivAt_sinh z).clog hz

end Azurite.DLMF
