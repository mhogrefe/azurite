/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section4

/-!
# DLMF §6.5: further interrelations

Formalizations of <https://dlmf.nist.gov/6.5>, equations 6.5.1–6.5.7.

* 6.5.1 (`x > 0`): `dlmf_6_5_1`, the boundary values of `E₁` on the cut (from
  `dlmf_6_2_1_cut` and 6.2.7).
* 6.5.2: `dlmf_6_5_2` (for any boundary values `Lp`, `Lm`; uniqueness of limits along
  `−x ± it`, `t → 0+`).
* 6.5.3, 6.5.4 (`x > 0`): `dlmf_6_5_3`, `dlmf_6_5_4` (closed forms in `Ein`); `Shi(z) = −i Si(iz)`
  holds for every `z` (`Shi_eq_neg_I_mul_Si`).
* 6.5.5–6.5.7 (`|ph z| < π/2`, i.e. `ℜz > 0`): `dlmf_6_5_5`, `dlmf_6_5_6`, `dlmf_6_5_7`, from
  6.2.4 at `±iz` and `ln(±iz) = ln z ± πi/2` (`log_I_mul`).
-/

open Complex Filter Topology Set
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 6.5.1–6.5.4: real arguments -/

/-- `Ei(x) = −Ein(−x) + ln x + γ` as complex numbers (6.2.7). -/
theorem Ei_eq_ein {x : ℝ} (hx : 0 < x) : (Ei x : ℂ) = -ein (-(x : ℂ)) + Real.log x + γ :=
  (dlmf_6_2_7 hx).1

/-- **DLMF 6.5.1**: `E₁(−x ± i0) = −Ei(x) ∓ iπ`, `x > 0`. -/
theorem dlmf_6_5_1 {x : ℝ} (hx : 0 < x) :
    Tendsto expIntE₁ (𝓝[{z | 0 < z.im}] ((-x : ℝ) : ℂ)) (𝓝 (-(Ei x : ℂ) - π * I)) ∧
      Tendsto expIntE₁ (𝓝[{z | z.im < 0}] ((-x : ℝ) : ℂ)) (𝓝 (-(Ei x : ℂ) + π * I)) := by
  obtain ⟨h1, h2⟩ := dlmf_6_2_1_cut (show -x < 0 by linarith)
  have he : (Ei x : ℂ) = -ein ((-x : ℝ) : ℂ) + Real.log (-(-x)) + γ := by
    rw [neg_neg, Ei_eq_ein hx, ofReal_neg]
  constructor
  · convert h1 using 2
    rw [he]; ring
  · convert h2 using 2
    rw [he]; ring

/-- Approaching a real point from the upper half-plane is a nontrivial filter. -/
theorem tendsto_add_mul_I_nhdsGT (x : ℝ) :
    Tendsto (fun t : ℝ => (x : ℂ) + t * I) (𝓝[>] 0) (𝓝[{z | 0 < z.im}] (x : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun t : ℝ => (x : ℂ) + t * I) (𝓝 0) (𝓝 ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
      ((continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simpa using ht

theorem tendsto_sub_mul_I_nhdsGT (x : ℝ) :
    Tendsto (fun t : ℝ => (x : ℂ) - t * I) (𝓝[>] 0) (𝓝[{z | z.im < 0}] (x : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun t : ℝ => (x : ℂ) - t * I) (𝓝 0) (𝓝 ((x : ℂ) - ((0 : ℝ) : ℂ) * I)) :=
      ((continuous_const.sub (continuous_ofReal.mul continuous_const)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simpa using ht

/-- **DLMF 6.5.2**: `Ei(x) = −½(E₁(−x + i0) + E₁(−x − i0))`, `x > 0`: whatever the two boundary
values `Lp`, `Lm` are, `Ei(x) = −(Lp + Lm)/2`. -/
theorem dlmf_6_5_2 {x : ℝ} (hx : 0 < x) {Lp Lm : ℂ}
    (hp : Tendsto expIntE₁ (𝓝[{z | 0 < z.im}] ((-x : ℝ) : ℂ)) (𝓝 Lp))
    (hm : Tendsto expIntE₁ (𝓝[{z | z.im < 0}] ((-x : ℝ) : ℂ)) (𝓝 Lm)) :
    (Ei x : ℂ) = -((Lp + Lm) / 2) := by
  obtain ⟨h1, h2⟩ := dlmf_6_5_1 hx
  have ep : Lp = -(Ei x : ℂ) - π * I :=
    tendsto_nhds_unique (hp.comp (tendsto_add_mul_I_nhdsGT _))
      (h1.comp (tendsto_add_mul_I_nhdsGT _))
  have em : Lm = -(Ei x : ℂ) + π * I :=
    tendsto_nhds_unique (hm.comp (tendsto_sub_mul_I_nhdsGT _))
      (h2.comp (tendsto_sub_mul_I_nhdsGT _))
  rw [ep, em]
  ring

/-- `Shi(z) = −i Si(iz)` for every `z`. -/
theorem Shi_eq_neg_I_mul_Si (z : ℂ) : Shi z = -I * Si (I * z) := by
  rw [Shi_eq, Si_eq, ShiF, SiF, show I * (I * z) = -z by ring_nf; rw [I_sq]; ring,
    show -I * (I * z) = z by ring_nf; rw [I_sq]; ring]
  field_simp
  ring

/-- **DLMF 6.5.3**: `½(Ei(x) + E₁(x)) = Shi(x) = −i Si(ix)`, `x > 0`. -/
theorem dlmf_6_5_3 {x : ℝ} (hx : 0 < x) :
    ((Ei x : ℂ) + expIntE₁ x) / 2 = Shi x ∧ Shi x = -I * Si (I * x) := by
  refine ⟨?_, Shi_eq_neg_I_mul_Si _⟩
  rw [Ei_eq_ein hx, dlmf_6_2_4 (mem_slitPlane_of_re_pos (by simpa using hx)), Shi_eq, ShiF,
    ← ofReal_log hx.le]
  ring

/-- `ln(±iz) = ln z ± πi/2` for `ℜz > 0`. -/
theorem log_I_mul {z : ℂ} (hz : 0 < z.re) :
    log (I * z) = log z + π / 2 * I ∧ log (-I * z) = log z - π / 2 * I := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have ha := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have hpi := Real.pi_pos
  constructor
  · rw [log_mul I_ne_zero hz0 (by rw [arg_I]; constructor <;> linarith), log_I]
    ring
  · rw [log_mul (neg_ne_zero.mpr I_ne_zero) hz0 (by rw [arg_neg_I]; constructor <;> linarith),
      log_neg_I]
    ring

theorem I_mul_mem_slitPlane {z : ℂ} (hz : 0 < z.re) : I * z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr (by simp [hz.ne']))

theorem neg_I_mul_mem_slitPlane {z : ℂ} (hz : 0 < z.re) : -I * z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr (by simp [hz.ne']))

/-- **DLMF 6.5.4**: `½(Ei(x) − E₁(x)) = Chi(x) = Ci(ix) − ½πi`, `x > 0`. -/
theorem dlmf_6_5_4 {x : ℝ} (hx : 0 < x) :
    ((Ei x : ℂ) - expIntE₁ x) / 2 = Chi x ∧ Chi x = Ci (I * x) - π / 2 * I := by
  have hx' : 0 < (x : ℂ).re := by simpa using hx
  constructor
  · rw [Ei_eq_ein hx, dlmf_6_2_4 (mem_slitPlane_of_re_pos hx'), Chi, chiInt_eq, chiIntF,
      ← ofReal_log hx.le]
    ring
  · rw [(dlmf_6_2_13 (I_mul_mem_slitPlane hx')).2, (log_I_mul hx').1, Chi, chiInt_eq,
      chiIntF, Cin_eq, CinF, show I * (I * (x : ℂ)) = -x by ring_nf; rw [I_sq]; ring,
      show -I * (I * (x : ℂ)) = x by ring_nf; rw [I_sq]; ring]
    ring

/-! ### 6.5.5–6.5.7: `|ph z| < π/2` -/

/-- **DLMF 6.5.5**: `Si(z) = ½i(E₁(−iz) − E₁(iz)) + ½π`, `|ph z| < π/2`. -/
theorem dlmf_6_5_5 {z : ℂ} (hz : 0 < z.re) :
    Si z = I / 2 * (expIntE₁ (-I * z) - expIntE₁ (I * z)) + π / 2 := by
  obtain ⟨l1, l2⟩ := log_I_mul hz
  rw [dlmf_6_2_4 (neg_I_mul_mem_slitPlane hz), dlmf_6_2_4 (I_mul_mem_slitPlane hz), l1, l2,
    Si_eq, SiF]
  field_simp
  linear_combination (-2 * (π : ℂ) * I + 2 * ein (I * z) - 2 * ein (-(I * z))) * I_sq

/-- **DLMF 6.5.6**: `Ci(z) = −½(E₁(iz) + E₁(−iz))`, `|ph z| < π/2`. -/
theorem dlmf_6_5_6 {z : ℂ} (hz : 0 < z.re) :
    Ci z = -((expIntE₁ (I * z) + expIntE₁ (-I * z)) / 2) := by
  obtain ⟨l1, l2⟩ := log_I_mul hz
  rw [dlmf_6_2_4 (neg_I_mul_mem_slitPlane hz), dlmf_6_2_4 (I_mul_mem_slitPlane hz), l1, l2,
    (dlmf_6_2_13 (mem_slitPlane_of_re_pos hz)).2, Cin_eq, CinF]
  ring

/-- **DLMF 6.5.7**: `g(z) ± i f(z) = E₁(∓iz) e^{∓iz}`, `|ph z| < π/2`. -/
theorem dlmf_6_5_7 {z : ℂ} (hz : 0 < z.re) :
    auxG z + I * auxF z = expIntE₁ (-I * z) * cexp (-I * z) ∧
      auxG z - I * auxF z = expIntE₁ (I * z) * cexp (I * z) := by
  have h5 := dlmf_6_5_5 hz
  have h6 := dlmf_6_5_6 hz
  have hsi := (dlmf_6_2_10 z).2
  have hsc := Complex.sin_sq_add_cos_sq z
  rw [exp_neg_I_mul, exp_I_mul]
  -- `−(Ci ± i si) = E₁(∓iz)`
  have e1 : expIntE₁ (-I * z) = -(Ci z + I * si z) := by
    rw [h6, hsi, h5]
    ring_nf
    rw [I_sq]
    ring
  have e2 : expIntE₁ (I * z) = -(Ci z - I * si z) := by
    rw [h6, hsi, h5]
    ring_nf
    rw [I_sq]
    ring
  constructor
  · rw [e1, auxF, auxG]
    linear_combination (-(si z) * Complex.sin z) * I_sq
  · rw [e2, auxF, auxG]
    linear_combination (-(si z) * Complex.sin z) * I_sq

end Azurite.DLMF
