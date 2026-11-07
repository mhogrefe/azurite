/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section15
import Azurite.DLMF.Chapter4.Section16
import Azurite.DLMF.Chapter4.Section13Converge
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Basic.Real.Sign
import Azurite.DLMF.Chapter4.Section21
import Azurite.DLMF.Chapter1.Section9

/-!
# DLMF §4.23 Inverse Trigonometric Functions

The definitions 4.23.1, 4.23.2, 4.23.4, 4.23.5 (general values) and 4.23.7–4.23.9 (principal
values) were formalized in §4.15 (`Chapter4/Section15.lean`): `arcsinGen`, `arccosGen`,
`arccscGen`, `arcsecGen`, `arcsinD`, `arccosD`, `arctanD`, `arccscD`, `arcsecD`, `arccotD`.

## §4.23(i) General Definitions

* 4.23.3: `arctanGen` (`C¹` paths from `0` avoiding `±i`), `mem_arctanGen_iff` (the values are
  the solutions of `tan w = z`, via `tan_of_arctan_path`).
* 4.23.6: `arccotGen`.
* `dlmf_4_23_1` … `dlmf_4_23_6`: the definitions restated.
* "Each of the six functions is a multivalued function of `z`": `dlmf_4_23_i_multivalued`.
* "`Arctan z` and `Arccot z` have branch points at `z = ±i`; the other four functions have
  branch points at `z = ±1`": `dlmf_4_23_i_branch_points`.
  - A branch point is formalized as: no continuous single-valued branch exists on any
    punctured disc around the point.
  - Everything reduces to `no_continuous_sqrt_punctured`: `z − c` has no continuous square
    root on a punctured disc around `c`.
  - **Imprecision**: `Arccsc` and `Arcsec` also have a branch point at `z = 0`
    (`dlmf_4_23_i_branch_zero`).

## §4.23(ii) Principal Values

* The principal branches are the integrals along paths that do not cross the cuts: they are
  values of the general functions (`dlmf_4_23_ii_principal_mem`).
* "Each is two-valued on the corresponding cuts": `dlmf_4_23_ii_two_valued` (different limits
  from the two sides).
* "each is real on the part of the real axis that remains": `dlmf_4_23_ii_real`.
* 4.23.7–4.23.9: `dlmf_4_23_7_9`.
* "These functions are analytic in the cut plane depicted in Figures 4.23.1(iii) and
  4.23.1(iv)": `dlmf_4_23_ii_analytic` (also for `arcsin`, `arccos`, `arctan` and Figures
  4.23.1(i)–(ii)).

## §4.23(iii) Reflection Formulas

* 4.23.10–4.23.15: `dlmf_4_23_10`, …, `dlmf_4_23_15`, directly from the integrals. They hold for
  all `z`, including `z = ±i` in 4.23.12, 4.23.15, where both sides are Lean junk values.
* 4.23.16–4.23.17: `dlmf_4_23_16`, `dlmf_4_23_17` (§4.15).
* 4.23.18: `dlmf_4_23_18`. With `ρ(z) = (1 + iz)/(1 − iz)`, `ρ(z) ρ(1/z) = −1`, and both lie in
  the upper (`ℜz > 0`) or lower (`ℜz < 0`) half-plane, so `ln ρ(z) + ln ρ(1/z) = ±iπ`.

## §4.23(iv) Logarithmic Forms

* 4.23.19 (`arcsin`), 4.23.22 and 4.23.23 (`arccos`): `dlmf_4_23_19`, `dlmf_4_23_22`,
  `dlmf_4_23_23`, on `ℂ ∖ ((−∞, −1) ∪ (1, ∞))`, i.e. off the cuts, including the endpoints
  `±1`.
  - The logarithmic form has `sin` (respectively `cos`) equal to `z` and lies in the strip
    where the principal value lives; the principal value follows by injectivity.
* On the cuts, 4.23.20–4.23.21 (`arcsin`) and 4.23.24–4.23.25 (`arccos`): `dlmf_4_23_20_21`,
  `dlmf_4_23_24_25`, as the limits from the upper and lower sides (`ln((x² − 1)^{1/2} ± x)` is
  `arcosh |x|`).
* 4.23.26: `dlmf_4_23_26`. On the cuts, 4.23.27: `dlmf_4_23_27`, as the limits from the right
  and left sides.
* "if `0 < x < ∞` then `1/(x + i0) = (1/x) − i0`": `dlmf_4_23_iv_inv_side`.

## §4.23(v) Fundamental Property

* 4.23.28–4.23.33: `dlmf_4_23_31`, `dlmf_4_23_32`, `dlmf_4_23_33`. They rest on three general
  lemmas, `sin_eq_iff_neg_one_zpow`, `cos_eq_iff_pm` and `tan_eq_iff_add_int_mul_pi`: if
  `sin a = z` (respectively `cos a = z`, `tan a = z`) then the solutions of `z = sin w` are
  `(−1)ᵏ a + kπ` (respectively `±a + 2kπ`, `a + kπ`).
* Off the cuts the principal values are used. On the cuts, where the principal value is
  two-valued, either side value works (`dlmf_4_23_31_cut`, `dlmf_4_23_32_cut`); `arctan` uses
  Mathlib's `Complex.arctan` (all `z ≠ ±i`), which on the cuts is the right-side value
  (`arctan_cut_value`).
* `w = Arcsin z`, `Arccos z`, `Arctan z`: the general values are these sets
  (`dlmf_4_23_31_gen`, `dlmf_4_23_32_gen`, `dlmf_4_23_33_gen`).

## §4.23(vi) Real and Imaginary Parts

* 4.23.37–4.23.38: `alphaA`, `betaA`. Their facts (`alphaA_betaA_facts`): `αβ = x`,
  `(α² − 1)(1 − β²) = y²`, `α ≥ 1`, `β² ≤ 1`, and `β² < 1` off the cuts.
* 4.23.34 (`±z ∉ (1, ∞)`): `dlmf_4_23_34`. The right side has `sin = z` and lies in the
  principal strip.
* 4.23.35: `dlmf_4_23_35`.
* 4.23.36 (`|z| < 1`): `dlmf_4_23_36`.

## §4.23(vii) Special Values and Interrelations

* Table 4.23.1, rows `−1`, `0`, `1`: `dlmf_table_4_23_1_neg_one`, `dlmf_table_4_23_1_zero`,
  `dlmf_table_4_23_1_one`. The entry `∓½π` for `arccot 0` is formalized as the one-sided limits
  `±½π` from `x → 0±` (`dlmf_table_4_23_1_arccot_zero`). Rows `±∞` are limits along the real
  axis (`dlmf_table_4_23_1_top`, `dlmf_table_4_23_1_bot`). Entries marked `–` (functions
  undefined there) are not stated.
* Interrelations via Table 4.16.3: every principal inverse function inverts its function on the
  first quadrant (`inv_trig_first_quadrant`), so each column of Table 4.16.3 gives six relations
  (`dlmf_4_23_vii_sin`, …, `dlmf_4_23_vii_cot`); DLMF's example
  `arcsec a = arccot((a² − 1)^{-1/2})` is `dlmf_4_23_vii_example`.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### 4.23.3: `Arctan` -/

/-- **DLMF 4.23.3** (general values): `w ∈ Arctan z` when `w = ∫₀^z dt/(1 + t²)` along a `C¹`
path `γ : [0, 1] → ℂ` from `0` to `z` that does not pass through `±i`. -/
def arctanGen (z : ℂ) : Set ℂ :=
  {w | ∃ γ γ' : ℝ → ℂ, γ 0 = 0 ∧ γ 1 = z ∧
    (∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s) ∧ ContinuousOn γ' (Icc 0 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ I ∧ γ s ≠ -I) ∧
    w = ∫ s in (0 : ℝ)..1, γ' s / (1 + γ s ^ 2)}

/-- **DLMF 4.23.6** (general values): `Arccot z = Arctan(1/z)`. -/
def arccotGen (z : ℂ) : Set ℂ := arctanGen (1 / z)

theorem one_add_sq_eq_mul_I (γ : ℂ) : 1 + γ ^ 2 = (1 + I * γ) * (1 - I * γ) := by
  ring_nf; rw [I_sq]; ring

/-- Along a 4.23.3 path, `Φ(s) = ∫₀^{γ(s)} dt/(1 + t²)` satisfies
`e^{2iΦ(s)} (1 − iγ(s)) = 1 + iγ(s)`. -/
theorem exp_of_arctan_path {γ γ' : ℝ → ℂ} (h0 : γ 0 = 0)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hne : ∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ I ∧ γ s ≠ -I) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      exp (2 * I * ∫ u in (0 : ℝ)..s, γ' u / (1 + γ u ^ 2)) * (1 - I * γ s) = 1 + I * γ s := by
  have hm : ∀ s ∈ Icc (0 : ℝ) 1, 1 - I * γ s ≠ 0 := fun s hs h =>
    (hne s hs).2 (by linear_combination I * h + γ s * I_sq)
  have hp : ∀ s ∈ Icc (0 : ℝ) 1, 1 + I * γ s ≠ 0 := fun s hs h =>
    (hne s hs).1 (by linear_combination (-I) * h + γ s * I_sq)
  have hq : ∀ s ∈ Icc (0 : ℝ) 1, 1 + γ s ^ 2 ≠ 0 := fun s hs => by
    rw [one_add_sq_eq_mul_I]; exact mul_ne_zero (hp s hs) (hm s hs)
  set f : ℝ → ℂ := fun u => γ' u / (1 + γ u ^ 2) with hf
  have hγc : ContinuousOn γ (Icc 0 1) := fun s hs => (hγ s hs).continuousWithinAt
  have hfc : ContinuousOn f (Icc 0 1) :=
    hγ'.div (continuousOn_const.add (hγc.pow 2)) hq
  set Φ : ℝ → ℂ := fun s => ∫ u in (0 : ℝ)..s, f u with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1)
      (μ := volume) (f := f) (by rw [uIcc_of_le zero_le_one]; exact hfc.integrableOn_Icc)
    rwa [uIcc_of_le zero_le_one] at this
  have hΦd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (f s) s := by
    intro s hs
    apply intervalIntegral.integral_hasDerivAt_right
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs.1.le]
      exact hfc.mono (Icc_subset_Icc le_rfl hs.2.le)
    · exact (hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
    · exact hfc.continuousAt (Icc_mem_nhds hs.1 hs.2)
  have hγd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt γ (γ' s) s := fun s hs =>
    (hγ s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  -- `Q(s) = e^{−2iΦ(s)} (1 + iγ(s))/(1 − iγ(s))` is constant
  set Q : ℝ → ℂ := fun s => exp (-(2 * I) * Φ s) * ((1 + I * γ s) / (1 - I * γ s)) with hQ
  have hQc : ContinuousOn Q (Icc 0 1) :=
    ((continuous_exp.comp_continuousOn (continuousOn_const.mul hΦc))).mul
      ((continuousOn_const.add (continuousOn_const.mul hγc)).div
        (continuousOn_const.sub (continuousOn_const.mul hγc)) hm)
  have hQd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt Q 0 s := by
    intro s hs
    have hs' := Ioo_subset_Icc_self hs
    have h1 := ((hΦd s hs).const_mul (-(2 * I))).cexp
    have h2 := (((hγd s hs).const_mul I).const_add 1).div
      (((hγd s hs).const_mul I).const_sub 1) (hm s hs')
    refine (h1.mul h2).congr_deriv ?_
    have := hm s hs'
    have := hp s hs'
    simp only [hf, Pi.div_apply]
    rw [one_add_sq_eq_mul_I]
    field_simp
    ring_nf
  intro s hs
  have hc := eq_of_hasDerivAt_zero_Icc hQc hQd s hs
  have hQ0 : Q 0 = 1 := by simp [hQ, hΦ, h0]
  rw [hQ0] at hc
  simp only [hQ] at hc
  have := hm s hs
  field_simp at hc
  show exp (2 * I * Φ s) * (1 - I * γ s) = 1 + I * γ s
  rw [← hc, ← mul_assoc, ← exp_add, show 2 * I * Φ s + -(2 * I * Φ s) = 0 by ring, exp_zero,
    one_mul]

theorem tan_ne_of_cos_ne {θ s : ℂ} (hs : s = I ∨ s = -I) (hc : cos θ ≠ 0) : tan θ ≠ s := by
  intro h
  rw [tan_eq_sin_div_cos, div_eq_iff hc] at h
  have h1 := sin_sq_add_cos_sq θ
  rw [h] at h1
  have : cos θ ^ 2 * (s ^ 2 + 1) = 1 := by linear_combination h1
  rcases hs with rfl | rfl <;> simp [I_sq] at this

/-- A `C¹` path from `0` to `w` (`cos w ≠ 0`) on which `cos` does not vanish. -/
theorem exists_cos_ne_zero_path {w : ℂ} (hcw : cos w ≠ 0) :
    ∃ ℓ ℓ' : ℝ → ℂ, ℓ 0 = 0 ∧ ℓ 1 = w ∧ (∀ s, HasDerivAt ℓ (ℓ' s) s) ∧ Continuous ℓ' ∧
      ∀ s ∈ Icc (0 : ℝ) 1, cos (ℓ s) ≠ 0 := by
  set c : ℂ := if 0 ≤ w.im then 1 else -1 with hc
  set ℓ : ℝ → ℂ := fun s => s * w + I * c * (s - s ^ 2) with hℓdef
  set ℓ' : ℝ → ℂ := fun s => w + I * c * (1 - 2 * s) with hℓ'def
  have hℓ : ∀ s, HasDerivAt ℓ (ℓ' s) s := by
    intro s
    have h := ((hasDerivAt_id s).ofReal_comp.mul_const w).add
      (((hasDerivAt_id s).sub ((hasDerivAt_id s).pow 2)).ofReal_comp.const_mul (I * c))
    convert h using 1
    · ext u
      simp [hℓdef]
    · simp [hℓ'def]
  refine ⟨ℓ, ℓ', by simp [hℓdef], by simp [hℓdef], hℓ, by simp only [hℓ'def]; fun_prop, ?_⟩
  intro s hs hcs
  rcases hs.1.eq_or_lt with h | h
  · rw [← h] at hcs
    simp [hℓdef] at hcs
  rcases hs.2.eq_or_lt with h' | h'
  · rw [h'] at hcs
    simp [hℓdef] at hcs
    exact hcw hcs
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcs
  have him := congrArg im hk
  have hpos : 0 < s - s ^ 2 := by nlinarith
  by_cases hw0 : 0 ≤ w.im
  · simp [hℓdef, hc, hw0, ← ofReal_pow] at him
    nlinarith
  · simp [hℓdef, hc, hw0, ← ofReal_pow] at him
    nlinarith

/-- **DLMF 4.23.3** (general values): the values of `Arctan z` are exactly the solutions `w` of
`tan w = z` with `cos w ≠ 0` (compare 4.23.30 and 4.23.33). -/
theorem mem_arctanGen_iff {z w : ℂ} :
    w ∈ arctanGen z ↔ cos w ≠ 0 ∧ tan w = z := by
  constructor
  · rintro ⟨γ, γ', h0, h1', hγ, hγ', hne, rfl⟩
    have hE := exp_of_arctan_path h0 hγ hγ' hne 1 ⟨zero_le_one, le_rfl⟩
    rw [h1'] at hE
    set Φ := ∫ u in (0 : ℝ)..1, γ' u / (1 + γ u ^ 2)
    set E := exp (I * Φ)
    have hE0 : E ≠ 0 := exp_ne_zero _
    have hE2 : exp (2 * I * Φ) = E ^ 2 := by rw [← exp_nat_mul]; ring_nf
    rw [hE2] at hE
    have hEp : E ^ 2 + 1 ≠ 0 := fun h => by
      have : E ^ 2 = -1 := by linear_combination h
      rw [this] at hE
      have : (2 : ℂ) = 0 := by linear_combination -hE
      exact two_ne_zero this
    have hcos : cos Φ = (E ^ 2 + 1) / (2 * E) := by
      rw [dlmf_4_14_2, show -I * Φ = -(I * Φ) by ring, exp_neg]; field_simp; ring
    have hsin : sin Φ = (E ^ 2 - 1) / (2 * I * E) := by
      rw [dlmf_4_14_1, show -I * Φ = -(I * Φ) by ring, exp_neg]; field_simp; ring
    have hc : cos Φ ≠ 0 := by
      rw [hcos]; exact div_ne_zero hEp (mul_ne_zero two_ne_zero hE0)
    refine ⟨hc, ?_⟩
    rw [tan_eq_sin_div_cos, hsin, hcos, div_div_div_eq, div_eq_iff (mul_ne_zero (mul_ne_zero
      (mul_ne_zero two_ne_zero I_ne_zero) hE0) hEp)]
    linear_combination (2 * E) * hE
  · rintro ⟨hcw, hw⟩
    obtain ⟨ℓ, ℓ', hℓ0, hℓ1, hℓ, hℓ'c, hcl⟩ := exists_cos_ne_zero_path hcw
    have hℓc : Continuous ℓ := continuous_iff_continuousAt.mpr fun s => (hℓ s).continuousAt
    refine ⟨fun s => tan (ℓ s), fun s => ℓ' s / cos (ℓ s) ^ 2, by simp [hℓ0],
      by show tan (ℓ 1) = z; rw [hℓ1, hw],
      fun s hs => ?_, ?_, fun s hs => ⟨tan_ne_of_cos_ne (Or.inl rfl) (hcl s hs),
        tan_ne_of_cos_ne (Or.inr rfl) (hcl s hs)⟩, ?_⟩
    · have := (Complex.hasDerivAt_tan (hcl s hs)).comp s (hℓ s)
      exact (this.congr_deriv (by ring)).hasDerivWithinAt
    · exact hℓ'c.continuousOn.div ((continuous_cos.comp hℓc).continuousOn.pow 2)
        (fun s hs => pow_ne_zero 2 (hcl s hs))
    · rw [intervalIntegral.integral_congr (g := ℓ') (fun s hs => by
        rw [uIcc_of_le zero_le_one] at hs
        have hc := hcl s hs
        simp only [tan_eq_sin_div_cos]
        field_simp
        linear_combination (-ℓ' s) * sin_sq_add_cos_sq (ℓ s)),
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hℓ s)
          (hℓ'c.intervalIntegrable _ _)]
      rw [hℓ1, hℓ0, sub_zero]

/-! ### The definitions -/

/-- **DLMF 4.23.4–4.23.6**: `Arccsc z = Arcsin(1/z)`, `Arcsec z = Arccos(1/z)`,
`Arccot z = Arctan(1/z)` (general values). -/
theorem dlmf_4_23_4_6 (z : ℂ) :
    arccscGen z = arcsinGen (1 / z) ∧ arcsecGen z = arccosGen (1 / z) ∧
      arccotGen z = arctanGen (1 / z) := ⟨rfl, rfl, rfl⟩

/-! ### Multivaluedness -/

theorem cos_arctan_ne_zero (z : ℂ) (h1 : z ≠ I) (h2 : z ≠ -I) : cos (arctan z) ≠ 0 := by
  intro h
  have := tan_arctan h1 h2
  rw [tan_eq_sin_div_cos, h, div_zero] at this
  rw [← this, show arctan 0 = 0 by simp [Complex.arctan], cos_zero] at h
  exact one_ne_zero h

/-- "Each of the six functions is a multivalued function of `z`": at every admissible `z` each
has two different values. -/
theorem dlmf_4_23_i_multivalued {z : ℂ} :
    (z ≠ 1 → z ≠ -1 → ∃ w₁ ∈ arcsinGen z, ∃ w₂ ∈ arcsinGen z, w₁ ≠ w₂) ∧
    (z ≠ 1 → z ≠ -1 → ∃ w₁ ∈ arccosGen z, ∃ w₂ ∈ arccosGen z, w₁ ≠ w₂) ∧
    (z ≠ I → z ≠ -I → ∃ w₁ ∈ arctanGen z, ∃ w₂ ∈ arctanGen z, w₁ ≠ w₂) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hπ
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨w, hw⟩ := sin_surjective z
    refine ⟨w, (mem_arcsinGen_iff h1 h2).mpr hw, w + 2 * π, (mem_arcsinGen_iff h1 h2).mpr
      (by rw [sin_add_two_pi, hw]), fun h => h2π (by linear_combination -h)⟩
  · obtain ⟨w, hw⟩ := cos_surjective z
    refine ⟨w, (mem_arccosGen_iff h1 h2).mpr hw, w + 2 * π, (mem_arccosGen_iff h1 h2).mpr
      (by rw [cos_add_two_pi, hw]), fun h => h2π (by linear_combination -h)⟩
  · have hc := cos_arctan_ne_zero z h1 h2
    refine ⟨arctan z, mem_arctanGen_iff.mpr ⟨hc, tan_arctan h1 h2⟩, arctan z + π,
      mem_arctanGen_iff.mpr ⟨by rw [cos_add_pi]; exact neg_ne_zero.mpr hc,
        by rw [tan_add_pi, tan_arctan h1 h2]⟩, fun h => hπ (by linear_combination -h)⟩

/-! ### Branch points -/

/-- `z − c` has no continuous square root on a punctured disc around `c`. -/
theorem no_continuous_sqrt_punctured (c : ℂ) {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ContinuousOn g (Metric.ball c r \ {c})) :
    ¬ ∀ z ∈ Metric.ball c r \ {c}, g z ^ 2 = z - c := by
  intro hsq
  set ρ := r / 2 with hρdef
  have hρ : 0 < ρ := half_pos hr
  set p : ℝ → ℂ := fun θ => c + ρ * exp (θ * I) with hpdef
  have hp : ∀ θ : ℝ, p θ ∈ Metric.ball c r \ {c} := by
    intro θ
    have hn : ‖(ρ : ℂ) * exp (θ * I)‖ = ρ := by
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hρ.le]
    refine ⟨?_, fun h => ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, hpdef]; simp only [add_sub_cancel_left]; rw [hn]
      linarith
    · rw [mem_singleton_iff] at h
      have : (ρ : ℂ) * exp (θ * I) = 0 := by rw [hpdef] at h; linear_combination h
      rw [this, norm_zero] at hn; linarith
  set d : ℝ → ℂ := fun θ => (√ρ : ℝ) * exp (θ * I / 2) with hddef
  have hd0 : ∀ θ, d θ ≠ 0 := fun θ => mul_ne_zero
    (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hρ).ne') (exp_ne_zero _)
  set h : ℝ → ℂ := fun θ => g (p θ) / d θ with hhdef
  have hpc : Continuous p := by rw [hpdef]; fun_prop
  have hcont : Continuous h := by
    rw [hhdef]
    exact (hg.comp_continuous hpc hp).div (by rw [hddef]; fun_prop) hd0
  have hsq1 : ∀ θ, h θ ^ 2 = 1 := by
    intro θ
    have hd2 : d θ ^ 2 = ρ * exp (θ * I) := by
      rw [hddef]; simp only
      rw [mul_pow, ← ofReal_pow, Real.sq_sqrt hρ.le, ← exp_nat_mul]; push_cast; ring_nf
    rw [hhdef]; simp only
    rw [div_pow, hsq _ (hp θ), hd2, hpdef]; simp only [add_sub_cancel_left]
    exact div_self (mul_ne_zero (ofReal_ne_zero.mpr hρ.ne') (exp_ne_zero _))
  have hpm : ∀ θ, h θ = 1 ∨ h θ = -1 := fun θ => by
    have : (h θ - 1) * (h θ + 1) = 0 := by linear_combination hsq1 θ
    rcases mul_eq_zero.mp this with h' | h'
    · left; linear_combination h'
    · right; linear_combination h'
  have hre : ∀ θ, |(h θ).re| = 1 := fun θ => by
    rcases hpm θ with h' | h' <;> rw [h'] <;> simp
  have h2π : h (2 * π) = -h 0 := by
    have hp2 : p (2 * π) = p 0 := by
      rw [hpdef]; simp only
      rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, exp_two_pi_mul_I]; simp
    have hd2 : d (2 * π) = -d 0 := by
      rw [hddef]; simp only
      rw [show ((2 * π : ℝ) : ℂ) * I / 2 = π * I by push_cast; ring, exp_pi_mul_I]; simp
    rw [hhdef]; simp only
    rw [hp2, hd2, div_neg]
  obtain ⟨θ, -, hθ⟩ := intermediate_value_uIcc (a := 0) (b := 2 * π)
    (f := fun θ => (h θ).re) (continuous_re.comp hcont).continuousOn
    (show (0 : ℝ) ∈ uIcc (h 0).re (h (2 * π)).re by
      rw [h2π, neg_re]; rcases hpm 0 with h' | h' <;> rw [h'] <;> simp)
  have := hre θ
  simp only at hθ
  rw [hθ, abs_zero] at this
  exact zero_ne_one this

theorem continuousOn_cpow_half {q : ℂ → ℂ} {U : Set ℂ} (hq : ContinuousOn q U)
    (hs : ∀ z ∈ U, q z ∈ slitPlane) : ContinuousOn (fun z => q z ^ (1 / 2 : ℂ)) U :=
  fun z hz => (continuousAt_cpow_const (hs z hz)).comp_continuousWithinAt (hq z hz)

theorem mem_slitPlane_of_im_ne {w : ℂ} (h : w.im ≠ 0) : w ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr h)

/-- `Arcsin` has branch points at `±1`: no continuous `f` with `sin f(z) = z` on a punctured
disc around `±1`. -/
theorem no_arcsin_branch {s : ℂ} (hs : s = 1 ∨ s = -1) {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball s r \ {s})) :
    ¬ ∀ z ∈ Metric.ball s r \ {s}, sin (f z) = z := by
  intro h
  set r' := min r 1
  have hr' : 0 < r' := lt_min hr one_pos
  have hsub : Metric.ball s r' \ {s} ⊆ Metric.ball s r \ {s} :=
    sdiff_subset_sdiff_left (Metric.ball_subset_ball (min_le_left _ _))
  have hfc := hf.mono hsub
  have hcos2 : ∀ z ∈ Metric.ball s r' \ {s}, cos (f z) ^ 2 = 1 - z ^ 2 := fun z hz => by
    have hz' := h z (hsub hz)
    linear_combination sin_sq_add_cos_sq (f z) - (sin (f z) + z) * hz'
  have hre : ∀ z ∈ Metric.ball s r' \ {s}, |z.re - s.re| < 1 := fun z hz => by
    have h1 : ‖z - s‖ < r' := by rw [← dist_eq_norm]; exact hz.1
    have := abs_re_le_norm (z - s)
    rw [sub_re] at this
    linarith [min_le_right r 1]
  rcases hs with rfl | rfl
  · refine no_continuous_sqrt_punctured 1 hr'
      (g := fun z => I * cos (f z) * (1 / (1 + z)) ^ (1 / 2 : ℂ))
      ((continuousOn_const.mul (continuous_cos.comp_continuousOn hfc)).mul
        (continuousOn_cpow_half (continuousOn_const.div (by fun_prop) fun z hz => ?_)
          fun z hz => ?_)) fun z hz => ?_
    · intro h0
      have hz2 := hre z hz
      rw [show z = -1 by linear_combination h0] at hz2
      norm_num at hz2
    · refine mem_slitPlane_iff.mpr (Or.inl ?_)
      have := hre z hz
      have hpos : 0 < (1 + z).re := by simp at this ⊢; linarith [(abs_lt.mp this).1]
      rw [one_div, inv_re]; exact div_pos hpos (normSq_pos.mpr fun h0 => by
        rw [h0] at hpos; simp at hpos)
    · have hz1 : 1 + z ≠ 0 := fun h0 => by
        have hz2 := hre z hz
        rw [show z = -1 by linear_combination h0] at hz2
        norm_num at hz2
      rw [mul_pow, mul_pow, sq_cpow_one_half, hcos2 z hz, I_sq]
      field_simp
      ring
  · refine no_continuous_sqrt_punctured (-1) hr'
      (g := fun z => cos (f z) * (1 / (1 - z)) ^ (1 / 2 : ℂ))
      ((continuous_cos.comp_continuousOn hfc).mul
        (continuousOn_cpow_half (continuousOn_const.div (by fun_prop) fun z hz => ?_)
          fun z hz => ?_)) fun z hz => ?_
    · intro h0
      have hz2 := hre z hz
      rw [show z = 1 by linear_combination -h0] at hz2
      norm_num at hz2
    · refine mem_slitPlane_iff.mpr (Or.inl ?_)
      have := hre z hz
      have hpos : 0 < (1 - z).re := by simp at this ⊢; linarith [(abs_lt.mp this).2]
      rw [one_div, inv_re]; exact div_pos hpos (normSq_pos.mpr fun h0 => by
        rw [h0] at hpos; simp at hpos)
    · have hz1 : 1 - z ≠ 0 := fun h0 => by
        have hz2 := hre z hz
        rw [show z = 1 by linear_combination -h0] at hz2
        norm_num at hz2
      rw [mul_pow, sq_cpow_one_half, hcos2 z hz]
      field_simp
      ring

/-- `Arccos` has branch points at `±1`. -/
theorem no_arccos_branch {s : ℂ} (hs : s = 1 ∨ s = -1) {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball s r \ {s})) :
    ¬ ∀ z ∈ Metric.ball s r \ {s}, cos (f z) = z := fun h =>
  no_arcsin_branch hs hr (f := fun z => π / 2 - f z) (continuousOn_const.sub hf)
    fun z hz => by rw [sin_pi_div_two_sub, h z hz]

/-- From `tan θ = z` (`cos θ ≠ 0`): `e^{2iθ} (1 − iz) = 1 + iz`. -/
theorem exp_sq_mul_of_tan {θ z : ℂ} (hc : cos θ ≠ 0) (h : tan θ = z) :
    exp (I * θ) ^ 2 * (1 - I * z) = 1 + I * z := by
  rw [tan_eq_sin_div_cos, div_eq_iff hc, dlmf_4_14_1, dlmf_4_14_2,
    show -I * θ = -(I * θ) by ring, exp_neg] at h
  have hE := exp_ne_zero (I * θ)
  field_simp at h
  linear_combination h

/-- `Arctan` has branch points at `±i`: no continuous `f` with `tan f(z) = z` on a punctured
disc around `±i`. -/
theorem no_arctan_branch {s : ℂ} (hs : s = I ∨ s = -I) {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball s r \ {s})) :
    ¬ ∀ z ∈ Metric.ball s r \ {s}, tan (f z) = z := by
  intro h
  set r' := min r 1
  have hr' : 0 < r' := lt_min hr one_pos
  have hsub : Metric.ball s r' \ {s} ⊆ Metric.ball s r \ {s} :=
    sdiff_subset_sdiff_left (Metric.ball_subset_ball (min_le_left _ _))
  have hfc := hf.mono hsub
  have him : ∀ z ∈ Metric.ball s r' \ {s}, |z.im - s.im| < 1 := fun z hz => by
    have h1 : ‖z - s‖ < r' := by rw [← dist_eq_norm]; exact hz.1
    have := abs_im_le_norm (z - s)
    rw [sub_im] at this
    linarith [min_le_right r 1]
  have hc : ∀ z ∈ Metric.ball s r' \ {s}, cos (f z) ≠ 0 := fun z hz h0 => by
    have := h z (hsub hz)
    rw [tan_eq_sin_div_cos, h0, div_zero] at this
    have hz2 := him z hz
    rw [← this] at hz2
    rcases hs with rfl | rfl <;> norm_num at hz2
  have hE : ∀ z ∈ Metric.ball s r' \ {s}, exp (I * f z) ^ 2 * (1 - I * z) = 1 + I * z :=
    fun z hz => exp_sq_mul_of_tan (hc z hz) (h z (hsub hz))
  have hexp : ContinuousOn (fun z => exp (I * f z)) (Metric.ball s r' \ {s}) :=
    continuous_exp.comp_continuousOn (continuousOn_const.mul hfc)
  rcases hs with rfl | rfl
  · refine no_continuous_sqrt_punctured I hr'
      (g := fun z => exp (I * f z) * (-I - z) ^ (1 / 2 : ℂ))
      (hexp.mul (continuousOn_cpow_half (by fun_prop) fun z hz => ?_)) fun z hz => ?_
    · apply mem_slitPlane_of_im_ne
      have := him z hz
      simp at this ⊢
      linarith [(abs_lt.mp this).1]
    · rw [mul_pow, sq_cpow_one_half]
      linear_combination (-I) * hE z hz - z * (exp (I * f z) ^ 2 + 1) * I_sq
  · refine no_continuous_sqrt_punctured (-I) hr'
      (g := fun z => exp (-I * f z) * (I - z) ^ (1 / 2 : ℂ))
      ((continuous_exp.comp_continuousOn (continuousOn_const.mul hfc)).mul
        (continuousOn_cpow_half (by fun_prop) fun z hz => ?_)) fun z hz => ?_
    · apply mem_slitPlane_of_im_ne
      have := him z hz
      simp at this ⊢
      linarith [(abs_lt.mp this).2]
    · have hEE : exp (-I * f z) ^ 2 * exp (I * f z) ^ 2 = 1 := by
        rw [← mul_pow, ← exp_add, show -I * f z + I * f z = 0 by ring, exp_zero, one_pow]
      rw [mul_pow, sq_cpow_one_half]
      linear_combination (I * (1 - I * z)) * hEE - (I * exp (-I * f z) ^ 2) * hE z hz -
        (exp (-I * f z) ^ 2 * z + z) * I_sq

/-- Points near `1/s` invert to points near `s`. -/
theorem exists_inv_punctured {s : ℂ} (hs : s ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ r' > 0, ∀ w ∈ Metric.ball (1 / s) r' \ {1 / s}, w ≠ 0 ∧ 1 / w ∈ Metric.ball s r \ {s} := by
  have hs' : (1 / s) ≠ 0 := one_div_ne_zero hs
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp
    ((continuousAt_const (y := (1 : ℂ))).div continuousAt_id hs') r hr
  refine ⟨min δ ‖1 / s‖, lt_min hδ (norm_pos_iff.mpr hs'), fun w hw => ?_⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    have := hw.1
    rw [Metric.mem_ball, dist_zero_left] at this
    exact lt_irrefl _ (this.trans_le (min_le_right _ _))
  refine ⟨hw0, ?_, fun h => hw.2 ?_⟩
  · have := hδ' (lt_of_lt_of_le hw.1 (min_le_left _ _))
    simpa [one_div_one_div] using this
  · rw [mem_singleton_iff] at h ⊢
    rw [← h, one_div_one_div]

theorem inv_branch_aux {s : ℂ} (hs : s ≠ 0) {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball s r \ {s})) :
    ∃ r' > 0, ContinuousOn (fun w => f (1 / w)) (Metric.ball (1 / s) r' \ {1 / s}) ∧
      ∀ w ∈ Metric.ball (1 / s) r' \ {1 / s}, 1 / w ∈ Metric.ball s r \ {s} := by
  obtain ⟨r', hr', h⟩ := exists_inv_punctured hs hr
  refine ⟨r', hr', hf.comp (continuousOn_const.div continuousOn_id fun w hw => (h w hw).1)
    fun w hw => (h w hw).2, fun w hw => (h w hw).2⟩

/-- `Arccsc` has branch points at `±1`. -/
theorem no_arccsc_branch {s : ℂ} (hs : s = 1 ∨ s = -1) {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball s r \ {s})) :
    ¬ ∀ z ∈ Metric.ball s r \ {s}, sin (f z) = 1 / z := by
  intro h
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨r', hr', hc, hm⟩ := inv_branch_aux hs0 hr hf
  have hinv : 1 / s = s := by rcases hs with rfl | rfl <;> norm_num
  rw [hinv] at hc hm
  exact no_arcsin_branch hs hr' hc fun w hw => by rw [h _ (hm w hw), one_div_one_div]

/-- `Arcsec` has branch points at `±1`. -/
theorem no_arcsec_branch {s : ℂ} (hs : s = 1 ∨ s = -1) {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball s r \ {s})) :
    ¬ ∀ z ∈ Metric.ball s r \ {s}, cos (f z) = 1 / z := fun h =>
  no_arccsc_branch hs hr (f := fun z => π / 2 - f z) (continuousOn_const.sub hf)
    fun z hz => by rw [sin_pi_div_two_sub, h z hz]

/-- `Arccot` has branch points at `±i`. -/
theorem no_arccot_branch {s : ℂ} (hs : s = I ∨ s = -I) {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball s r \ {s})) :
    ¬ ∀ z ∈ Metric.ball s r \ {s}, tan (f z) = 1 / z := by
  intro h
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  obtain ⟨r', hr', hc, hm⟩ := inv_branch_aux hs0 hr hf
  have hs' : 1 / s = I ∨ 1 / s = -I := by
    rcases hs with rfl | rfl
    · right; rw [one_div, inv_I]
    · left; rw [one_div, inv_neg, inv_I, neg_neg]
  exact no_arctan_branch hs' hr' hc fun w hw => by rw [h _ (hm w hw), one_div_one_div]

/-- **Imprecision** (§4.23(i)): `Arccsc` also has a branch point at `z = 0`, which DLMF's list
omits. There is no continuous `f` with `sin f(z) = 1/z` on a punctured disc around `0`. -/
theorem no_arccsc_branch_zero {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball 0 r \ {0})) :
    ¬ ∀ z ∈ Metric.ball (0 : ℂ) r \ {0}, sin (f z) = 1 / z := by
  intro h
  set r' := min r (1 / 2)
  have hr' : 0 < r' := lt_min hr (by norm_num)
  set U := Metric.ball (0 : ℂ) r' \ {0}
  have hsub : U ⊆ Metric.ball 0 r \ {0} :=
    sdiff_subset_sdiff_left (Metric.ball_subset_ball (min_le_left _ _))
  have hfc := hf.mono hsub
  have hz0 : ∀ z ∈ U, z ≠ 0 := fun z hz => hz.2
  have hzn : ∀ z ∈ U, ‖z‖ < 1 / 2 := fun z hz => by
    have := hz.1; rw [Metric.mem_ball, dist_zero_right] at this
    exact this.trans_le (min_le_right _ _)
  set σ : ℂ → ℂ := fun z => z * cos (f z) with hσ
  have hσc : ContinuousOn σ U := continuousOn_id.mul (continuous_cos.comp_continuousOn hfc)
  have hzs : ∀ z ∈ U, z * sin (f z) = 1 := fun z hz => by
    rw [h z (hsub hz)]; field_simp [hz0 z hz]
  have hσ2 : ∀ z ∈ U, σ z ^ 2 = z ^ 2 - 1 := fun z hz => by
    simp only [hσ]
    linear_combination z ^ 2 * sin_sq_add_cos_sq (f z) - (z * sin (f z) + 1) * hzs z hz
  have hσim : ∀ z ∈ U, (σ z).im ≠ 0 := fun z hz h0 => by
    have hr := congrArg re (hσ2 z hz)
    have hs : σ z = ((σ z).re : ℂ) := Complex.ext (by simp) (by simp [h0])
    rw [hs, ← ofReal_pow, ofReal_re] at hr
    have h1 : (z ^ 2).re ≤ ‖z‖ ^ 2 := by
      rw [← norm_pow]; exact re_le_norm _
    have h2 := hzn z hz
    have h3 : 0 ≤ (σ z).re ^ 2 := sq_nonneg _
    simp only [sub_re, one_re] at hr
    nlinarith [norm_nonneg z]
  have hpre : IsPreconnected U := isPreconnected_ball_diff_zero
  have hsign : (∀ z ∈ U, 0 < (σ z).im) ∨ (∀ z ∈ U, (σ z).im < 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hcon
    obtain ⟨x, hx, hx'⟩ := hpre.intermediate_value₂ ha hb
      (continuous_im.comp_continuousOn hσc) continuousOn_const ha' hb'
    exact hσim x hx hx'
  have hsqhalf : ∀ x : ℂ, exp (x / 2) ^ 2 = exp x := fun x => by
    rw [← exp_nat_mul]; ring_nf
  rcases hsign with hpos | hneg
  · refine no_continuous_sqrt_punctured 0 hr'
      (g := fun z => exp (-I * f z / 2) * (σ z + I) ^ (1 / 2 : ℂ))
      ((continuous_exp.comp_continuousOn ((continuousOn_const.mul hfc).div_const 2)).mul
        (continuousOn_cpow_half (hσc.add continuousOn_const) fun z hz => ?_)) fun z hz => ?_
    · apply mem_slitPlane_of_im_ne; have := hpos z hz; simp; linarith
    · rw [mul_pow, sq_cpow_one_half, hsqhalf, sub_zero]
      have he : exp (f z * I) = cos (f z) + sin (f z) * I := exp_mul_I _
      have hm : exp (-I * f z) * exp (f z * I) = 1 := by
        rw [← exp_add, show -I * f z + f z * I = 0 by ring, exp_zero]
      simp only [hσ]
      linear_combination (-(z * exp (-I * f z))) * he + z * hm -
        I * exp (-I * f z) * hzs z hz
  · refine no_continuous_sqrt_punctured 0 hr'
      (g := fun z => exp (I * f z / 2) * (σ z - I) ^ (1 / 2 : ℂ))
      ((continuous_exp.comp_continuousOn ((continuousOn_const.mul hfc).div_const 2)).mul
        (continuousOn_cpow_half (hσc.sub continuousOn_const) fun z hz => ?_)) fun z hz => ?_
    · apply mem_slitPlane_of_im_ne; have := hneg z hz; simp; linarith
    · rw [mul_pow, sq_cpow_one_half, hsqhalf, sub_zero]
      have he : exp (-(f z) * I) = cos (f z) - sin (f z) * I := by
        rw [exp_mul_I, cos_neg, sin_neg]; ring
      have hm : exp (I * f z) * exp (-(f z) * I) = 1 := by
        rw [← exp_add, show I * f z + -(f z) * I = 0 by ring, exp_zero]
      simp only [hσ]
      linear_combination (-(z * exp (I * f z))) * he + z * hm +
        I * exp (I * f z) * hzs z hz

/-- **Imprecision** (§4.23(i)): `Arcsec` also has a branch point at `z = 0`. -/
theorem no_arcsec_branch_zero {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball 0 r \ {0})) :
    ¬ ∀ z ∈ Metric.ball (0 : ℂ) r \ {0}, cos (f z) = 1 / z := fun h =>
  no_arccsc_branch_zero hr (f := fun z => π / 2 - f z) (continuousOn_const.sub hf)
    fun z hz => by rw [sin_pi_div_two_sub, h z hz]

/-- **DLMF §4.23(i)**: "`Arctan z` and `Arccot z` have branch points at `z = ±i`; the other four
functions have branch points at `z = ±1`". At none of these points is there a continuous
single-valued branch on any punctured disc. -/
theorem dlmf_4_23_i_branch_points {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} :
    (∀ s : ℂ, (s = I ∨ s = -I) → ContinuousOn f (Metric.ball s r \ {s}) →
      (¬ ∀ z ∈ Metric.ball s r \ {s}, tan (f z) = z) ∧
      (¬ ∀ z ∈ Metric.ball s r \ {s}, tan (f z) = 1 / z)) ∧
    (∀ s : ℂ, (s = 1 ∨ s = -1) → ContinuousOn f (Metric.ball s r \ {s}) →
      (¬ ∀ z ∈ Metric.ball s r \ {s}, sin (f z) = z) ∧
      (¬ ∀ z ∈ Metric.ball s r \ {s}, cos (f z) = z) ∧
      (¬ ∀ z ∈ Metric.ball s r \ {s}, sin (f z) = 1 / z) ∧
      (¬ ∀ z ∈ Metric.ball s r \ {s}, cos (f z) = 1 / z)) :=
  ⟨fun _ hs hf => ⟨no_arctan_branch hs hr hf, no_arccot_branch hs hr hf⟩,
    fun _ hs hf => ⟨no_arcsin_branch hs hr hf, no_arccos_branch hs hr hf,
      no_arccsc_branch hs hr hf, no_arcsec_branch hs hr hf⟩⟩

/-- **Imprecision** (§4.23(i)): `Arccsc z = Arcsin(1/z)` and `Arcsec z = Arccos(1/z)` also have a
branch point at `z = 0` (near `0`, `1/z` runs around the branch point of `Arcsin` at `∞`). -/
theorem dlmf_4_23_i_branch_zero {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball 0 r \ {0})) :
    (¬ ∀ z ∈ Metric.ball (0 : ℂ) r \ {0}, sin (f z) = 1 / z) ∧
      (¬ ∀ z ∈ Metric.ball (0 : ℂ) r \ {0}, cos (f z) = 1 / z) :=
  ⟨no_arccsc_branch_zero hr hf, no_arcsec_branch_zero hr hf⟩

/-! ### §4.23(ii) Principal Values -/

/-- The principal values are values of the general functions (integrals along paths that do
not cross the cuts). -/
theorem dlmf_4_23_ii_principal_mem {z : ℂ} :
    (z ∈ arcsinCut → arcsinD z ∈ arcsinGen z ∧ arccosD z ∈ arccosGen z) ∧
      (z ∈ arctanCut → arctanD z ∈ arctanGen z) := by
  refine ⟨fun hz => ⟨(arcsinD_props hz).1, ⟨_, (arcsinD_props hz).1, rfl⟩⟩, fun hz => ?_⟩
  refine ⟨fun s => s * z, fun _ => z, by simp, by simp, fun s _ => ?_, continuousOn_const,
    fun s hs => ?_, rfl⟩
  · simpa using ((hasDerivAt_id s).ofReal_comp.mul_const z).hasDerivWithinAt
  · have h := mem_arctanCut_seg hz hs
    refine ⟨fun h' => ?_, fun h' => ?_⟩ <;> simp only at h' <;> rw [h'] at h <;>
      rcases h with h | h <;> simp at h

/-- **DLMF §4.23(ii)**: "Each is two-valued on the corresponding cuts": at every point of the
cuts of `arcsin`, `arccos` (`|x| > 1`) and of `arctan` (`iy`, `|y| > 1`) the limits from the two
sides exist and differ. -/
theorem dlmf_4_23_ii_two_valued :
    (∀ x : ℝ, 1 < |x| → ∃ b c : ℂ, b ≠ c ∧ Tendsto arcsinD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
      Tendsto arcsinD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c)) ∧
    (∀ x : ℝ, 1 < |x| → ∃ b c : ℂ, b ≠ c ∧ Tendsto arccosD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
      Tendsto arccosD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c)) ∧
    (∀ y : ℝ, 1 < |y| → ∃ b c : ℂ, b ≠ c ∧
      Tendsto arctanD (𝓝[{z | 0 < z.re}] (y * I)) (𝓝 b) ∧
      Tendsto arctanD (𝓝[{z | z.re < 0}] (y * I)) (𝓝 c)) := by
  have harccos : arccosD = fun z => π / 2 - arcsinD z := funext dlmf_4_23_16
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨r, hr, e1, e2⟩ := arcsinD_cut_limits hx
    exact ⟨_, _, fun h => by have := congrArg im h; simp at this; linarith, e1, e2⟩
  · obtain ⟨r, hr, e1, e2⟩ := arcsinD_cut_limits hx
    rw [harccos]
    exact ⟨_, _, fun h => by have := congrArg im h; simp at this; linarith,
      tendsto_const_nhds.sub e1, tendsto_const_nhds.sub e2⟩
  · obtain ⟨b, c, hbc, e1, e2⟩ := arctanD_cut_limits hy
    exact ⟨b, c, fun h => hbc (congrArg re h), e1, e2⟩

/-- **DLMF §4.23(ii)**: "each is real on the part of the real axis that remains after deleting
the intersections with the corresponding cuts". -/
theorem dlmf_4_23_ii_real :
    (∀ x ∈ Ioo (-1 : ℝ) 1, arcsinD x = Real.arcsin x ∧ arccosD x = Real.arccos x) ∧
      ∀ x : ℝ, arctanD x = Real.arctan x :=
  ⟨fun _ hx => ⟨arcsinD_ofReal hx, arccosD_ofReal hx⟩, arctanD_ofReal⟩

/-- **DLMF 4.23.7–4.23.9**: `arccsc z = arcsin(1/z)`, `arcsec z = arccos(1/z)`,
`arccot z = arctan(1/z)`. -/
theorem dlmf_4_23_7_9 (z : ℂ) :
    arccscD z = arcsinD (1 / z) ∧ arcsecD z = arccosD (1 / z) ∧ arccotD z = arctanD (1 / z) :=
  ⟨rfl, rfl, rfl⟩

theorem one_div_mem_arctanCut {z : ℂ} (h : z.re ≠ 0 ∨ 1 < |z.im|) :
    z ≠ 0 ∧ 1 / z ∈ arctanCut := by
  have hz : z ≠ 0 := by
    rintro rfl
    rcases h with h | h
    · exact h rfl
    · simp at h; linarith
  refine ⟨hz, ?_⟩
  by_cases hre : z.re = 0
  · right
    have hr : 1 < |z.im| := h.resolve_left (not_not.mpr hre)
    have hn : normSq z = z.im ^ 2 := by rw [normSq_apply, hre]; ring
    rw [one_div, inv_im, hn, neg_div, abs_neg, abs_div, abs_pow, sq,
      div_mul_eq_div_div, div_self (by positivity), one_div]
    exact inv_lt_one_of_one_lt₀ hr
  · left
    rw [one_div, inv_re]
    exact div_ne_zero hre (normSq_pos.mpr hz).ne'

/-- **DLMF §4.23(ii)**: the principal branches are analytic in the cut planes of Figure 4.23.1:
`arcsin`, `arccos` off `(−∞, −1] ∪ [1, ∞)`, `arctan` off `(−i∞, −i] ∪ [i, i∞)`,
`arccsc`, `arcsec` off `[−1, 1]` (Figure 4.23.1(iii)) and `arccot` off `[−i, i]`
(Figure 4.23.1(iv)). -/
theorem dlmf_4_23_ii_analytic :
    DifferentiableOn ℂ arcsinD arcsinCut ∧ DifferentiableOn ℂ arccosD arcsinCut ∧
      DifferentiableOn ℂ arctanD arctanCut ∧
      (∀ z : ℂ, z.im ≠ 0 ∨ 1 < |z.re| → DifferentiableAt ℂ arccscD z ∧
        DifferentiableAt ℂ arcsecD z) ∧
      (∀ z : ℂ, z.re ≠ 0 ∨ 1 < |z.im| → DifferentiableAt ℂ arccotD z) := by
  have harccos : arccosD = fun z => π / 2 - arcsinD z := funext dlmf_4_23_16
  have harcsec : arcsecD = fun z => π / 2 - arccscD z := funext dlmf_4_23_17
  refine ⟨dlmf_4_15_F9.1, ?_, dlmf_4_15_F11.1, fun z hz => ?_, fun z hz => ?_⟩
  · rw [harccos]; exact dlmf_4_15_F9.1.const_sub _
  · have h := dlmf_4_15_F13.1 z hz
    exact ⟨h, by rw [harcsec]; exact h.const_sub _⟩
  · obtain ⟨hz0, hc⟩ := one_div_mem_arctanCut hz
    have hd := (dlmf_4_15_F11.1 _ hc).differentiableAt (isOpen_arctanCut.mem_nhds hc)
    exact hd.comp z ((differentiableAt_const (c := (1 : ℂ))).div differentiableAt_id hz0)

/-! ### §4.23(iii) Reflection Formulas -/

/-- **DLMF 4.23.10**: `arcsin(−z) = −arcsin z`. -/
theorem dlmf_4_23_10 (z : ℂ) : arcsinD (-z) = -arcsinD z := by
  simp only [arcsinD]
  rw [← intervalIntegral.integral_neg]
  congr 1; funext s
  rw [show ((s : ℂ) * -z) ^ 2 = ((s : ℂ) * z) ^ 2 by ring, neg_div]

/-- **DLMF 4.23.11**: `arccos(−z) = π − arccos z`. -/
theorem dlmf_4_23_11 (z : ℂ) : arccosD (-z) = π - arccosD z := by
  rw [dlmf_4_23_16, dlmf_4_23_16, dlmf_4_23_10]; ring

/-- **DLMF 4.23.12**: `arctan(−z) = −arctan z`. -/
theorem dlmf_4_23_12 (z : ℂ) : arctanD (-z) = -arctanD z := by
  simp only [arctanD]
  rw [← intervalIntegral.integral_neg]
  congr 1; funext s
  rw [show ((s : ℂ) * -z) ^ 2 = ((s : ℂ) * z) ^ 2 by ring, neg_div]

/-- **DLMF 4.23.13**: `arccsc(−z) = −arccsc z`. -/
theorem dlmf_4_23_13 (z : ℂ) : arccscD (-z) = -arccscD z := by
  rw [arccscD, arccscD, show 1 / -z = -(1 / z) by ring, dlmf_4_23_10]

/-- **DLMF 4.23.14**: `arcsec(−z) = π − arcsec z`. -/
theorem dlmf_4_23_14 (z : ℂ) : arcsecD (-z) = π - arcsecD z := by
  rw [arcsecD, arcsecD, show 1 / -z = -(1 / z) by ring, dlmf_4_23_11]

/-- **DLMF 4.23.15**: `arccot(−z) = −arccot z`. -/
theorem dlmf_4_23_15 (z : ℂ) : arccotD (-z) = -arccotD z := by
  rw [arccotD, arccotD, show 1 / -z = -(1 / z) by ring, dlmf_4_23_12]

/-- `ln a + ln b = ±iπ` when `ab = −1` and `a`, `b` lie in the same open half-plane. -/
theorem log_add_log_of_mul_eq_neg_one {a b : ℂ} (hab : a * b = -1) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (ha : 0 < σ * a.im) (hb : 0 < σ * b.im) : log a + log b = σ * π * I := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  have hexp : exp (log a + log b) = exp (σ * π * I) := by
    rw [exp_add, exp_log ha0, exp_log hb0, hab]
    rcases hσ with rfl | rfl
    · rw [show ((1 : ℝ) : ℂ) * π * I = π * I by push_cast; ring, exp_pi_mul_I]
    · rw [show ((-1 : ℝ) : ℂ) * π * I = -(π * I) by push_cast; ring, exp_neg, exp_pi_mul_I]
      norm_num
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp hexp
  have him := congrArg im hk
  simp only [add_im, log_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    mul_one, intCast_re, intCast_im, add_zero, zero_add] at him
  have h2 : (2 * (π : ℂ)).re = 2 * π := by simp
  have h3 : ((σ : ℂ) * π).re = σ * π := by rw [← ofReal_mul, ofReal_re]
  simp only [h2, h3] at him
  have hpa := neg_pi_lt_arg a
  have hpb := neg_pi_lt_arg b
  have hqa := arg_le_pi a
  have hqb := arg_le_pi b
  have hk0 : k = 0 := by
    rcases hσ with rfl | rfl
    · have ha' : 0 < a.im := by simpa using ha
      have hb' : 0 < b.im := by simpa using hb
      have h1 : 0 < arg a := lt_of_le_of_ne (arg_nonneg_iff.mpr ha'.le)
        (fun h => by have := (arg_eq_zero_iff.mp h.symm).2; linarith)
      have h1' : 0 < arg b := lt_of_le_of_ne (arg_nonneg_iff.mpr hb'.le)
        (fun h => by have := (arg_eq_zero_iff.mp h.symm).2; linarith)
      have h3 : arg a < π := arg_lt_pi_iff.mpr (Or.inr ha'.ne')
      have h3' : arg b < π := arg_lt_pi_iff.mpr (Or.inr hb'.ne')
      have : (k : ℝ) < 1 / 2 := by nlinarith [Real.pi_pos]
      have : (-1 / 2 : ℝ) < k := by nlinarith [Real.pi_pos]
      have : k < 1 := by exact_mod_cast (by linarith : (k : ℝ) < 1)
      have : -1 < k := by exact_mod_cast (by linarith : (-1 : ℝ) < k)
      omega
    · have ha' : a.im < 0 := by simpa using ha
      have hb' : b.im < 0 := by simpa using hb
      have h1 : arg a < 0 := arg_neg_iff.mpr ha'
      have h1' : arg b < 0 := arg_neg_iff.mpr hb'
      have : (k : ℝ) < 1 / 2 := by nlinarith [Real.pi_pos]
      have : (-1 / 2 : ℝ) < k := by nlinarith [Real.pi_pos]
      have : k < 1 := by exact_mod_cast (by linarith : (k : ℝ) < 1)
      have : -1 < k := by exact_mod_cast (by linarith : (-1 : ℝ) < k)
      omega
  rw [hk, hk0]; simp

/-- **DLMF 4.23.18**: `arccot z = ±π/2 − arctan z` for `ℜz ≷ 0`. -/
theorem dlmf_4_23_18 {z : ℂ} :
    (0 < z.re → arccotD z = π / 2 - arctanD z) ∧ (z.re < 0 → arccotD z = -(π / 2) - arctanD z) := by
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → 0 < σ * z.re →
      arccotD z = σ * (π / 2) - arctanD z := by
    intro σ hσ hz
    have hre : z.re ≠ 0 := fun h => by rw [h, mul_zero] at hz; exact lt_irrefl _ hz
    have hz0 : z ≠ 0 := fun h => hre (by rw [h]; simp)
    have hzc : z ∈ arctanCut := Or.inl hre
    obtain ⟨-, hzc'⟩ := one_div_mem_arctanCut (Or.inl hre)
    have hN : 0 < normSq z := normSq_pos.mpr hz0
    have hre' : (1 / z).re = z.re / normSq z := by rw [one_div, inv_re]
    obtain ⟨h1, h2, -⟩ := arctan_ratio_props hzc
    obtain ⟨h1', h2', -⟩ := arctan_ratio_props hzc'
    have hab : (1 + z * I) / (1 - z * I) * ((1 + 1 / z * I) / (1 - 1 / z * I)) = -1 := by
      have hzI : z - I ≠ 0 := fun h => h2 (by rw [sub_eq_zero.mp h]; rw [I_mul_I]; ring)
      field_simp
      ring_nf
      rw [I_sq]
      ring
    have hσa : 0 < σ * ((1 + z * I) / (1 - z * I)).im := by
      rw [im_arctan_ratio]
      have := normSq_pos.mpr h1
      rw [mul_div_assoc', ← mul_assoc, mul_comm σ 2, mul_assoc]
      exact div_pos (by linarith) this
    have hσb : 0 < σ * ((1 + 1 / z * I) / (1 - 1 / z * I)).im := by
      rw [im_arctan_ratio, hre']
      have := normSq_pos.mpr h1'
      rw [mul_div_assoc', ← mul_assoc, mul_comm σ 2, mul_assoc, mul_div_assoc']
      exact div_pos (by nlinarith [div_pos hz hN]) this
    have hL := log_add_log_of_mul_eq_neg_one hab σ hσ hσa hσb
    rw [arccotD, arctanD_eq hzc', arctanD_eq hzc]
    show -I / 2 * log ((1 + 1 / z * I) / (1 - 1 / z * I)) =
      σ * (π / 2) - -I / 2 * log ((1 + z * I) / (1 - z * I))
    have : log ((1 + 1 / z * I) / (1 - 1 / z * I)) =
        σ * π * I - log ((1 + z * I) / (1 - z * I)) := by linear_combination hL
    rw [this]
    ring_nf
    rw [I_sq]
    ring
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · simpa using key 1 (Or.inl rfl) (by simpa using hz)
  · have := key (-1) (Or.inr rfl) (by simpa using hz)
    rw [this]; push_cast; ring

/-! ### §4.23(iv) Logarithmic Forms -/

theorem arcsinD_one : arcsinD 1 = π / 2 := by
  rw [arcsinD, ← integral_one_div_sqrt_one_sub_sq]
  congr 1; funext s; rw [mul_one]

theorem arcsinD_neg_one : arcsinD (-1) = -(π / 2) := by
  rw [dlmf_4_23_10, arcsinD_one]

theorem cpow_half_zero : (0 : ℂ) ^ (1 / 2 : ℂ) = 0 := zero_cpow (by norm_num)

theorem re_pos_of_mul_eq_one {u v : ℂ} (h : u * v = 1) (hs : 0 < u.re + v.re) : 0 < u.re := by
  have hu : u ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  have hv : v = u⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [hv, inv_re] at hs
  by_contra hc
  push Not at hc
  have := div_nonpos_of_nonpos_of_nonneg hc (normSq_nonneg u)
  linarith

/-- **DLMF 4.23.19**: `arcsin z = −i ln((1 − z²)^{1/2} + iz)`, `z ∈ ℂ ∖ ((−∞, −1) ∪ (1, ∞))`. -/
theorem dlmf_4_23_19 {z : ℂ} (hz : z ∈ arcsinCut ∨ z = 1 ∨ z = -1) :
    arcsinD z = -I * log ((1 - z ^ 2) ^ (1 / 2 : ℂ) + I * z) := by
  rcases hz with hz | rfl | rfl
  · set a := (1 - z ^ 2) ^ (1 / 2 : ℂ) with ha
    set u := a + I * z with hu
    have hsl : 1 - z ^ 2 ∈ slitPlane := by
      simpa using one_sub_sq_mem_slitPlane hz (s := 1) ⟨zero_le_one, le_rfl⟩
    have hare : 0 < a.re := re_cpow_half_pos_of_mem_slitPlane hsl
    have hprod : u * (a - I * z) = 1 := by
      rw [hu]; ring_nf; rw [ha, sq_cpow_one_half, I_sq]; ring
    have hu0 : u ≠ 0 := fun h0 => by rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
    have hure : 0 < u.re := re_pos_of_mul_eq_one hprod (by simp [hu]; linarith)
    have hinv : u⁻¹ = a - I * z := (eq_inv_of_mul_eq_one_right hprod).symm
    obtain ⟨-, hs, hsin, -⟩ := arcsinD_props hz
    refine injOn_sin_sinStrip hs ?_ ?_
    · have harg := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hure)
      have hre : (-I * log u).re = arg u := by simp [log_im]
      constructor <;> rw [hre] <;> linarith [(abs_lt.mp harg).1, (abs_lt.mp harg).2]
    · rw [hsin, dlmf_4_14_1, show I * (-I * log u) = log u by ring_nf; rw [I_sq]; ring,
        show -I * (-I * log u) = -log u by ring_nf; rw [I_sq]; ring, exp_neg, exp_log hu0, hinv]
      field_simp
      rw [hu]
      ring
  · rw [arcsinD_one]; norm_num; rw [log_I]; linear_combination (π / 2 : ℂ) * I_sq
  · rw [arcsinD_neg_one]; norm_num; rw [log_neg_I]; linear_combination (π / 2 : ℂ) * I_sq

/-- **DLMF 4.23.22**: `arccos z = π/2 + i ln((1 − z²)^{1/2} + iz)`,
`z ∈ ℂ ∖ ((−∞, −1) ∪ (1, ∞))`. -/
theorem dlmf_4_23_22 {z : ℂ} (hz : z ∈ arcsinCut ∨ z = 1 ∨ z = -1) :
    arccosD z = π / 2 + I * log ((1 - z ^ 2) ^ (1 / 2 : ℂ) + I * z) := by
  rw [dlmf_4_23_16, dlmf_4_23_19 hz]; ring

theorem half_mem_slitPlane {z : ℂ} (hz : z ∈ arcsinCut) :
    (1 + z) / 2 ∈ slitPlane ∧ (1 - z) / 2 ∈ slitPlane := by
  rcases hz with hz | hz
  · exact ⟨mem_slitPlane_of_im_ne (by simpa using hz), mem_slitPlane_of_im_ne (by simpa using hz)⟩
  · have := abs_lt.mp hz
    exact ⟨mem_slitPlane_iff.mpr (Or.inl (by simp; linarith)),
      mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))⟩

/-- **DLMF 4.23.23** (Kahan): `arccos z = −2i ln(((1 + z)/2)^{1/2} + i((1 − z)/2)^{1/2})`,
`z ∈ ℂ ∖ ((−∞, −1) ∪ (1, ∞))`. -/
theorem dlmf_4_23_23 {z : ℂ} (hz : z ∈ arcsinCut ∨ z = 1 ∨ z = -1) :
    arccosD z = -2 * I * log (((1 + z) / 2) ^ (1 / 2 : ℂ) + I * ((1 - z) / 2) ^ (1 / 2 : ℂ)) := by
  rcases hz with hz | rfl | rfl
  · set p := ((1 + z) / 2) ^ (1 / 2 : ℂ) with hp
    set q := ((1 - z) / 2) ^ (1 / 2 : ℂ) with hq
    set w := p + I * q with hw
    obtain ⟨hs1, hs2⟩ := half_mem_slitPlane hz
    have hpre : 0 < p.re := re_cpow_half_pos_of_mem_slitPlane hs1
    have hqre : 0 < q.re := re_cpow_half_pos_of_mem_slitPlane hs2
    have hprod : w * (p - I * q) = 1 := by
      rw [hw]; ring_nf; rw [hp, hq, sq_cpow_one_half, sq_cpow_one_half, I_sq]; ring
    have hw0 : w ≠ 0 := fun h0 => by rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
    have hinv : w⁻¹ = p - I * q := (eq_inv_of_mul_eq_one_right hprod).symm
    have hN : 0 < normSq w := normSq_pos.mpr hw0
    have hwre : 0 < w.re := re_pos_of_mul_eq_one hprod (by simp [hw]; linarith)
    have hwim : 0 < w.im := by
      have h1 : (p - I * q).im = -(w.im / normSq w) := by rw [← hinv, inv_im, neg_div]
      have h2 : w.im - (p - I * q).im = 2 * q.re := by simp [hw]; ring
      rw [h1] at h2
      have : w.im * (1 + 1 / normSq w) = 2 * q.re := by rw [← h2]; field_simp; ring
      have h3 : 0 < 1 + 1 / normSq w := by positivity
      nlinarith
    have harg1 : 0 < arg w := lt_of_le_of_ne (arg_nonneg_iff.mpr hwim.le)
      (fun h => by have := (arg_eq_zero_iff.mp h.symm).2; linarith)
    have harg2 : arg w < π / 2 := (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre))).2
    set ψ := -2 * I * log w with hψ
    have hψre : ψ.re = 2 * arg w := by simp [hψ, log_im]
    have hcos : cos ψ = z := by
      have h2log : exp (2 * log w) = w ^ 2 := by
        rw [show (2 : ℂ) * log w = ((2 : ℕ) : ℂ) * log w by norm_num, exp_nat_mul, exp_log hw0]
      rw [dlmf_4_14_2, show I * ψ = 2 * log w by rw [hψ]; ring_nf; rw [I_sq]; ring,
        show -I * ψ = -(2 * log w) by rw [hψ]; ring_nf; rw [I_sq]; ring, exp_neg, h2log,
        ← inv_pow, hinv]
      have hp2 : p ^ 2 = (1 + z) / 2 := sq_cpow_one_half _
      have hq2 : q ^ 2 = (1 - z) / 2 := sq_cpow_one_half _
      rw [hw]
      linear_combination hp2 + q ^ 2 * I_sq - hq2
    obtain ⟨-, hs, hsin, -⟩ := arcsinD_props hz
    have hstrip : π / 2 - ψ ∈ sinStrip := by
      constructor <;> simp [hψre] <;> linarith
    have := injOn_sin_sinStrip hs hstrip (by rw [hsin, sin_pi_div_two_sub, hcos])
    rw [dlmf_4_23_16, this]; ring
  · rw [show arccosD 1 = 0 by rw [dlmf_4_23_16, arcsinD_one]; ring]
    norm_num
  · rw [show arccosD (-1) = π by rw [dlmf_4_23_16, arcsinD_neg_one]; ring]
    norm_num; rw [log_I]; linear_combination (π : ℂ) * I_sq

theorem arcosh_eq_log {x : ℝ} : Real.arcosh x = Real.log (√(x ^ 2 - 1) + x) := by
  rw [Real.arcosh, add_comm]

theorem arcosh_neg_eq_log {x : ℝ} : Real.arcosh (-x) = Real.log (√(x ^ 2 - 1) - x) := by
  rw [Real.arcosh, neg_sq, add_comm, ← sub_eq_add_neg]

/-- **DLMF 4.23.20–4.23.21** (on the cuts): `arcsin x = π/2 ± i ln((x² − 1)^{1/2} + x)` for
`x ∈ [1, ∞)` and `arcsin x = −π/2 ± i ln((x² − 1)^{1/2} − x)` for `x ∈ (−∞, −1]`. The upper and
lower signs are the limits from the upper and lower sides; at `x = ±1` both sides give `±π/2`. -/
theorem dlmf_4_23_20_21 {x : ℝ} :
    (1 < x → Tendsto arcsinD (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝 (π / 2 + I * Real.log (√(x ^ 2 - 1) + x))) ∧
      Tendsto arcsinD (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝 (π / 2 - I * Real.log (√(x ^ 2 - 1) + x)))) ∧
    (x < -1 → Tendsto arcsinD (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝 (-(π / 2) + I * Real.log (√(x ^ 2 - 1) - x))) ∧
      Tendsto arcsinD (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝 (-(π / 2) - I * Real.log (√(x ^ 2 - 1) - x)))) ∧
    arcsinD 1 = π / 2 ∧ arcsinD (-1) = -(π / 2) := by
  refine ⟨fun hx => ?_, fun hx => ?_, arcsinD_one, arcsinD_neg_one⟩
  · have hr := Real.arcosh_pos hx
    obtain ⟨e1, e2, -, -⟩ := dlmf_4_15_F7_edges hr
    rw [Real.cosh_arcosh hx.le, arcosh_eq_log] at e1 e2
    exact ⟨by simpa [mul_comm] using e1, by simpa [mul_comm] using e2⟩
  · have hr := Real.arcosh_pos (by linarith : 1 < -x)
    obtain ⟨-, -, e3, e4⟩ := dlmf_4_15_F7_edges hr
    rw [Real.cosh_arcosh (by linarith), arcosh_neg_eq_log] at e3 e4
    push_cast at e3 e4
    rw [neg_neg] at e3 e4
    exact ⟨by simpa [mul_comm] using e3, by simpa [mul_comm] using e4⟩

/-- **DLMF 4.23.24–4.23.25** (on the cuts): `arccos x = ∓i ln((x² − 1)^{1/2} + x)` for
`x ∈ [1, ∞)` and `arccos x = π ∓ i ln((x² − 1)^{1/2} − x)` for `x ∈ (−∞, −1]`, the upper/lower
signs corresponding to the upper/lower sides. -/
theorem dlmf_4_23_24_25 {x : ℝ} :
    (1 < x → Tendsto arccosD (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝 (-(I * Real.log (√(x ^ 2 - 1) + x)))) ∧
      Tendsto arccosD (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝 (I * Real.log (√(x ^ 2 - 1) + x)))) ∧
    (x < -1 → Tendsto arccosD (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝 (π - I * Real.log (√(x ^ 2 - 1) - x))) ∧
      Tendsto arccosD (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝 (π + I * Real.log (√(x ^ 2 - 1) - x)))) := by
  have harccos : arccosD = fun z => π / 2 - arcsinD z := funext dlmf_4_23_16
  obtain ⟨h1, h2, -⟩ := dlmf_4_23_20_21 (x := x)
  rw [harccos]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨e1, e2⟩ := h1 hx
    exact ⟨by convert tendsto_const_nhds.sub e1 using 2; ring,
      by convert tendsto_const_nhds.sub e2 using 2; ring⟩
  · obtain ⟨e1, e2⟩ := h2 hx
    exact ⟨by convert tendsto_const_nhds.sub e1 using 2; ring,
      by convert tendsto_const_nhds.sub e2 using 2; ring⟩

/-- **DLMF 4.23.26**: `arctan z = (i/2) ln((i + z)/(i − z))`, `z/i ∈ ℂ ∖ ((−∞, −1] ∪ [1, ∞))`
(i.e. `z` off the cuts of `arctan`). -/
theorem dlmf_4_23_26 {z : ℂ} (hz : z ∈ arctanCut) :
    arctanD z = I / 2 * log ((I + z) / (I - z)) := by
  obtain ⟨h1, h2, hs⟩ := arctan_ratio_props hz
  have hzI : I - z ≠ 0 := fun h => h2 (by
    rw [← sub_eq_zero.mp h, I_mul_I]; ring)
  have hinv : (I + z) / (I - z) = ((1 + z * I) / (1 - z * I))⁻¹ := by
    rw [inv_div, div_eq_div_iff hzI h2]
    ring_nf; rw [I_sq]; ring
  rw [arctanD_eq hz, hinv, log_inv _ (mem_slitPlane_iff_arg.mp hs).1]
  show -I / 2 * log ((1 + z * I) / (1 - z * I)) = _
  ring

/-- **DLMF 4.23.27** (on the cuts): `arctan(iy) = ±π/2 + (i/2) ln((y + 1)/(y − 1))`,
`y ∈ (−∞, −1) ∪ (1, ∞)`, the upper/lower sign corresponding to the right/left side. -/
theorem dlmf_4_23_27 {y : ℝ} (hy : 1 < |y|) :
    Tendsto arctanD (𝓝[{z | 0 < z.re}] (y * I))
        (𝓝 (π / 2 + I / 2 * Real.log ((y + 1) / (y - 1)))) ∧
      Tendsto arctanD (𝓝[{z | z.re < 0}] (y * I))
        (𝓝 (-(π / 2) + I / 2 * Real.log ((y + 1) / (y - 1)))) := by
  obtain ⟨h1, h2⟩ := arctanD_cut_tendsto hy
  have hy1 : y - 1 ≠ 0 := by intro h; rcases lt_abs.mp hy with h' | h' <;> linarith
  have hy2 : y + 1 ≠ 0 := by intro h; rcases lt_abs.mp hy with h' | h' <;> linarith
  have hpos : 0 < (y - 1) / (y + 1) := by
    have : (y - 1) / (y + 1) = (y ^ 2 - 1) / (y + 1) ^ 2 := by field_simp; ring
    rw [this]
    have : 1 < y ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_nonneg y, le_abs_self y, neg_abs_le y] : -|y| < 1)
      nlinarith [sq_abs y, abs_nonneg y]
    exact div_pos (by linarith) (by positivity)
  have hL : Real.log |(1 - y) / (1 + y)| = -Real.log ((y + 1) / (y - 1)) := by
    rw [show (1 - y) / (1 + y) = -((y - 1) / (y + 1)) by ring, abs_neg, abs_of_pos hpos,
      ← Real.log_inv, inv_div]
  rw [hL] at h1 h2
  exact ⟨by convert h1 using 2; push_cast; ring_nf; rw [I_sq]; ring,
    by convert h2 using 2; push_cast; ring_nf; rw [I_sq]; ring⟩

/-- **DLMF §4.23(iv)**: "Care needs to be taken on the cuts, for example, if `0 < x < ∞` then
`1/(x + i0) = (1/x) − i0`". -/
theorem dlmf_4_23_iv_inv_side {x : ℝ} (hx : 0 < x) :
    Tendsto (fun z : ℂ => 1 / z) (𝓝[{w | 0 < w.im}] (x : ℂ))
      (𝓝[{w | w.im < 0}] ((1 / x : ℝ) : ℂ)) :=
  (tendsto_one_div_nhdsWithin hx.ne').1

/-! ### §4.23(v) Fundamental Property -/

/-- The solutions of `sin w = sin a` are `w = (−1)ᵏ a + kπ`. -/
theorem sin_eq_iff_neg_one_zpow {a z : ℂ} (ha : sin a = z) (w : ℂ) :
    sin w = z ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k * a + k * π := by
  rw [← ha, show (sin w = sin a) ↔ (sin a = sin w) from eq_comm, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨2 * k, by rw [h, Even.neg_one_zpow ⟨k, by ring⟩]; push_cast; ring⟩
    · exact ⟨2 * k + 1, by rw [h, Odd.neg_one_zpow ⟨k, rfl⟩]; push_cast; ring⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · exact ⟨m, Or.inl (by rw [Even.neg_one_zpow ⟨m, by ring⟩]; push_cast; ring)⟩
    · exact ⟨m, Or.inr (by rw [Odd.neg_one_zpow ⟨m, rfl⟩]; push_cast; ring)⟩

/-- The solutions of `cos w = cos a` are `w = ±a + 2kπ`. -/
theorem cos_eq_iff_pm {a z : ℂ} (ha : cos a = z) (w : ℂ) :
    cos w = z ↔ ∃ k : ℤ, w = a + 2 * k * π ∨ w = -a + 2 * k * π := by
  rw [← ha, show (cos w = cos a) ↔ (cos a = cos w) from eq_comm, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩

theorem cos_add_int_mul_pi_ne_zero {a : ℂ} (ha : cos a ≠ 0) (k : ℤ) : cos (a + k * π) ≠ 0 := by
  rw [cos_add, sin_int_mul_pi, mul_zero, sub_zero]
  refine mul_ne_zero ha fun h => ?_
  have := sin_sq_add_cos_sq ((k : ℂ) * π)
  rw [h, sin_int_mul_pi] at this
  norm_num at this

/-- The solutions of `tan w = tan a` (`cos a ≠ 0`, `w` not a pole) are `w = a + kπ`. -/
theorem tan_eq_iff_add_int_mul_pi {a z : ℂ} (hc : cos a ≠ 0) (ha : tan a = z) (w : ℂ) :
    (cos w ≠ 0 ∧ tan w = z) ↔ ∃ k : ℤ, w = a + k * π := by
  constructor
  · rintro ⟨hcw, hw⟩
    have h : sin (w - a) = 0 := by
      rw [← ha, tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff hcw hc] at hw
      rw [sin_sub]; linear_combination hw
    obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp h
    exact ⟨k, by linear_combination hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨cos_add_int_mul_pi_ne_zero hc k, by rw [dlmf_4_14_10, ha]⟩

theorem sin_arcsinD {z : ℂ} (hz : z ∈ arcsinCut ∨ z = 1 ∨ z = -1) : sin (arcsinD z) = z := by
  rcases hz with hz | rfl | rfl
  · exact (arcsinD_props hz).2.2.1
  · rw [arcsinD_one, sin_pi_div_two]
  · rw [arcsinD_neg_one, sin_neg, sin_pi_div_two]

theorem cos_arccosD {z : ℂ} (hz : z ∈ arcsinCut ∨ z = 1 ∨ z = -1) : cos (arccosD z) = z := by
  rw [dlmf_4_23_16, cos_pi_div_two_sub, sin_arcsinD hz]

/-- **DLMF 4.23.28, 4.23.31**: the general solution of `z = sin w` is
`w = (−1)ᵏ arcsin z + kπ`, `k ∈ ℤ` (`z` off the cuts, or `z = ±1`). -/
theorem dlmf_4_23_31 {z : ℂ} (hz : z ∈ arcsinCut ∨ z = 1 ∨ z = -1) (w : ℂ) :
    sin w = z ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k * arcsinD z + k * π :=
  sin_eq_iff_neg_one_zpow (sin_arcsinD hz) w

/-- **DLMF 4.23.29, 4.23.32**: the general solution of `z = cos w` is `w = ±arccos z + 2kπ`. -/
theorem dlmf_4_23_32 {z : ℂ} (hz : z ∈ arcsinCut ∨ z = 1 ∨ z = -1) (w : ℂ) :
    cos w = z ↔ ∃ k : ℤ, w = arccosD z + 2 * k * π ∨ w = -arccosD z + 2 * k * π :=
  cos_eq_iff_pm (cos_arccosD hz) w

/-- **DLMF 4.23.30, 4.23.33**: the general solution of `z = tan w` is `w = arctan z + kπ`,
`z ≠ ±i` (Mathlib's principal `Complex.arctan`, defined for all `z ≠ ±i`). -/
theorem dlmf_4_23_33 {z : ℂ} (h1 : z ≠ I) (h2 : z ≠ -I) (w : ℂ) :
    (cos w ≠ 0 ∧ tan w = z) ↔ ∃ k : ℤ, w = arctan z + k * π :=
  tan_eq_iff_add_int_mul_pi (cos_arctan_ne_zero z h1 h2) (tan_arctan h1 h2) w

/-- **DLMF 4.23.33** with the principal value `arctanD` of §4.23(ii) (`z` off the cuts). -/
theorem dlmf_4_23_33' {z : ℂ} (hz : z ∈ arctanCut) (w : ℂ) :
    (cos w ≠ 0 ∧ tan w = z) ↔ ∃ k : ℤ, w = arctanD z + k * π := by
  have h1 : z ≠ I := fun h => by rw [h] at hz; rcases hz with h | h <;> simp at h
  have h2 : z ≠ -I := fun h => by rw [h] at hz; rcases hz with h | h <;> simp at h
  rw [arctanD_eq hz]; exact dlmf_4_23_33 h1 h2 w

/-- **DLMF 4.23.31** as sets: `Arcsin z = {(−1)ᵏ arcsin z + kπ}` (4.23.1 general values). -/
theorem dlmf_4_23_31_gen {z : ℂ} (hz : z ∈ arcsinCut) :
    arcsinGen z = {w | ∃ k : ℤ, w = (-1 : ℂ) ^ k * arcsinD z + k * π} := by
  have h1 : z ≠ 1 := fun h => by rw [h] at hz; rcases hz with h | h <;> simp at h
  have h2 : z ≠ -1 := fun h => by rw [h] at hz; rcases hz with h | h <;> simp at h
  ext w
  rw [mem_arcsinGen_iff h1 h2, dlmf_4_23_31 (Or.inl hz)]
  rfl

/-- **DLMF 4.23.32** as sets: `Arccos z = {±arccos z + 2kπ}` (4.23.2 general values). -/
theorem dlmf_4_23_32_gen {z : ℂ} (hz : z ∈ arcsinCut) :
    arccosGen z = {w | ∃ k : ℤ, w = arccosD z + 2 * k * π ∨ w = -arccosD z + 2 * k * π} := by
  have h1 : z ≠ 1 := fun h => by rw [h] at hz; rcases hz with h | h <;> simp at h
  have h2 : z ≠ -1 := fun h => by rw [h] at hz; rcases hz with h | h <;> simp at h
  ext w
  rw [mem_arccosGen_iff h1 h2, dlmf_4_23_32 (Or.inl hz)]
  rfl

/-- **DLMF 4.23.33** as sets: `Arctan z = {arctan z + kπ}` (4.23.3 general values). -/
theorem dlmf_4_23_33_gen {z : ℂ} (h1 : z ≠ I) (h2 : z ≠ -I) :
    arctanGen z = {w | ∃ k : ℤ, w = arctan z + k * π} := by
  ext w
  rw [mem_arctanGen_iff, dlmf_4_23_33 h1 h2]
  rfl

theorem sin_pi_div_two_add' (y : ℂ) : sin (π / 2 + y) = cos y := by
  rw [add_comm, sin_add_pi_div_two]

/-- On the cuts of `arcsin` (`|x| > 1`) both side values of 4.23.20–4.23.21 satisfy
`sin = x`, so 4.23.31 holds with either of them. -/
theorem dlmf_4_23_31_cut {x : ℝ} (w : ℂ) :
    (1 < x → (sin w = x ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k *
        (π / 2 + I * Real.log (√(x ^ 2 - 1) + x)) + k * π) ∧
      (sin w = x ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k *
        (π / 2 - I * Real.log (√(x ^ 2 - 1) + x)) + k * π)) ∧
    (x < -1 → (sin w = x ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k *
        (-(π / 2) + I * Real.log (√(x ^ 2 - 1) - x)) + k * π) ∧
      (sin w = x ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k *
        (-(π / 2) - I * Real.log (√(x ^ 2 - 1) - x)) + k * π)) := by
  have hcosh : ∀ r : ℝ, cos (I * r) = Real.cosh r := fun r => by
    rw [mul_comm, cos_mul_I, ofReal_cosh]
  refine ⟨fun hx => ⟨sin_eq_iff_neg_one_zpow ?_ w, sin_eq_iff_neg_one_zpow ?_ w⟩,
    fun hx => ⟨sin_eq_iff_neg_one_zpow ?_ w, sin_eq_iff_neg_one_zpow ?_ w⟩⟩
  · rw [sin_pi_div_two_add', hcosh, ← arcosh_eq_log, Real.cosh_arcosh hx.le]
  · rw [sub_eq_add_neg, sin_pi_div_two_add', cos_neg, hcosh, ← arcosh_eq_log,
      Real.cosh_arcosh hx.le]
  · rw [show -((π : ℂ) / 2) + I * Real.log (√(x ^ 2 - 1) - x) =
      -(π / 2 - I * Real.log (√(x ^ 2 - 1) - x)) by ring, sin_neg, sin_pi_div_two_sub,
      hcosh, ← arcosh_neg_eq_log, Real.cosh_arcosh (by linarith)]
    push_cast; ring
  · rw [show -((π : ℂ) / 2) - I * Real.log (√(x ^ 2 - 1) - x) =
      -(π / 2 + I * Real.log (√(x ^ 2 - 1) - x)) by ring, sin_neg, sin_pi_div_two_add',
      hcosh, ← arcosh_neg_eq_log, Real.cosh_arcosh (by linarith)]
    push_cast; ring

/-- On the cuts of `arccos` (`|x| > 1`) both side values of 4.23.24–4.23.25 satisfy
`cos = x`, so 4.23.32 holds with either of them. -/
theorem dlmf_4_23_32_cut {x : ℝ} (w : ℂ) :
    (1 < x → (cos w = x ↔ ∃ k : ℤ, w = I * Real.log (√(x ^ 2 - 1) + x) + 2 * k * π ∨
        w = -(I * Real.log (√(x ^ 2 - 1) + x)) + 2 * k * π)) ∧
    (x < -1 → (cos w = x ↔ ∃ k : ℤ, w = π - I * Real.log (√(x ^ 2 - 1) - x) + 2 * k * π ∨
        w = -(π - I * Real.log (√(x ^ 2 - 1) - x)) + 2 * k * π)) := by
  have hcosh : ∀ r : ℝ, cos (I * r) = Real.cosh r := fun r => by
    rw [mul_comm, cos_mul_I, ofReal_cosh]
  refine ⟨fun hx => cos_eq_iff_pm ?_ w, fun hx => cos_eq_iff_pm ?_ w⟩
  · rw [hcosh, ← arcosh_eq_log, Real.cosh_arcosh hx.le]
  · rw [sub_eq_add_neg, cos_add, cos_pi, sin_pi, cos_neg, hcosh, ← arcosh_neg_eq_log,
      Real.cosh_arcosh (by linarith)]
    push_cast; ring

/-- On the cuts of `arctan` (`iy`, `|y| > 1`), Mathlib's `Complex.arctan` is the right-side
value of 4.23.27. -/
theorem arctan_cut_value {y : ℝ} (hy : 1 < |y|) :
    arctan (y * I) = π / 2 + I / 2 * Real.log ((y + 1) / (y - 1)) := by
  have hy1 : y - 1 ≠ 0 := by intro h; rcases lt_abs.mp hy with h' | h' <;> linarith
  have hy2 : y + 1 ≠ 0 := by intro h; rcases lt_abs.mp hy with h' | h' <;> linarith
  have hpos : 0 < (y - 1) / (y + 1) := by
    have : (y - 1) / (y + 1) = (y ^ 2 - 1) / (y + 1) ^ 2 := by field_simp; ring
    rw [this]
    have : 1 < y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    exact div_pos (by linarith) (by positivity)
  have hratio : (1 + (y : ℂ) * I * I) / (1 - y * I * I) = (((1 - y) / (1 + y) : ℝ) : ℂ) := by
    rw [mul_assoc, I_mul_I]; push_cast; ring
  have hneg : (1 - y) / (1 + y) < 0 := by
    rw [show (1 - y) / (1 + y) = -((y - 1) / (y + 1)) by ring]; linarith
  have hlog : log (((1 - y) / (1 + y) : ℝ) : ℂ) =
      -Real.log ((y + 1) / (y - 1)) + π * I := by
    apply Complex.ext
    · rw [log_re, norm_real, Real.norm_eq_abs,
        show (1 - y) / (1 + y) = -((y - 1) / (y + 1)) by ring, abs_neg, abs_of_pos hpos]
      simp only [add_re, neg_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul,
        sub_zero, add_zero]
      rw [← Real.log_inv, inv_div]
    · rw [log_im, arg_ofReal_of_neg hneg]; simp
  show -I / 2 * log ((1 + (y : ℂ) * I * I) / (1 - y * I * I)) = _
  rw [hratio, hlog]
  ring_nf
  rw [I_sq]
  ring

/-! ### §4.23(vi) Real and Imaginary Parts -/

/-- **DLMF 4.23.37**: `α = ½((x + 1)² + y²)^{1/2} + ½((x − 1)² + y²)^{1/2}`. -/
noncomputable def alphaA (x y : ℝ) : ℝ :=
  1 / 2 * √((x + 1) ^ 2 + y ^ 2) + 1 / 2 * √((x - 1) ^ 2 + y ^ 2)

/-- **DLMF 4.23.38**: `β = ½((x + 1)² + y²)^{1/2} − ½((x − 1)² + y²)^{1/2}`. -/
noncomputable def betaA (x y : ℝ) : ℝ :=
  1 / 2 * √((x + 1) ^ 2 + y ^ 2) - 1 / 2 * √((x - 1) ^ 2 + y ^ 2)

theorem alphaA_betaA_facts (x y : ℝ) :
    alphaA x y * betaA x y = x ∧ (alphaA x y ^ 2 - 1) * (1 - betaA x y ^ 2) = y ^ 2 ∧
      1 ≤ alphaA x y ∧ betaA x y ^ 2 ≤ 1 := by
  set A := √((x + 1) ^ 2 + y ^ 2) with hA
  set B := √((x - 1) ^ 2 + y ^ 2) with hB
  have hA2 : A ^ 2 = (x + 1) ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hB2 : B ^ 2 = (x - 1) ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hnA : ‖((x + 1 : ℝ) : ℂ) + y * I‖ = A := norm_add_mul_I _ _
  have hnB : ‖((x - 1 : ℝ) : ℂ) + y * I‖ = B := norm_add_mul_I _ _
  have hdiff : ((x + 1 : ℝ) : ℂ) + y * I - (((x - 1 : ℝ) : ℂ) + y * I) = 2 := by push_cast; ring
  have hsum : 2 ≤ A + B := by
    have := norm_sub_le (((x + 1 : ℝ) : ℂ) + y * I) (((x - 1 : ℝ) : ℂ) + y * I)
    rw [hdiff, hnA, hnB] at this; simpa using this
  have hdif : |A - B| ≤ 2 := by
    have := abs_norm_sub_norm_le (((x + 1 : ℝ) : ℂ) + y * I) (((x - 1 : ℝ) : ℂ) + y * I)
    rw [hdiff, hnA, hnB] at this; simpa using this
  simp only [alphaA, betaA]
  refine ⟨?_, ?_, by linarith, ?_⟩
  · nlinarith
  · nlinarith
  · have := abs_le.mp hdif
    nlinarith

/-- `β² < 1` off the cuts. -/
theorem betaA_sq_lt_one {x y : ℝ} (hz : y ≠ 0 ∨ |x| < 1) : betaA x y ^ 2 < 1 := by
  obtain ⟨hab, hp, ha1, hb1⟩ := alphaA_betaA_facts x y
  rcases hb1.lt_or_eq with h | h
  · exact h
  exfalso
  have hy : y = 0 := by
    rw [h, sub_self, mul_zero] at hp; exact pow_eq_zero_iff two_ne_zero |>.mp hp.symm
  rcases hz with hz | hz
  · exact hz hy
  · have hx2 : x ^ 2 = alphaA x y ^ 2 := by
      rw [show x ^ 2 = alphaA x y ^ 2 * betaA x y ^ 2 by rw [← mul_pow, hab], h, mul_one]
    have : alphaA x y ≤ |x| := by
      rw [← Real.sqrt_sq_eq_abs, hx2, Real.sqrt_sq (by linarith)]
    linarith

/-- **DLMF 4.23.34**: `arcsin z = arcsin β + i sign(y) ln(α + (α² − 1)^{1/2})`, `z = x + iy`,
`±z ∉ (1, ∞)`. -/
theorem dlmf_4_23_34 {x y : ℝ} (hz : y ≠ 0 ∨ |x| ≤ 1) :
    arcsinD (x + y * I) = (Real.arcsin (betaA x y) : ℝ) +
      I * ((Real.sign y * Real.log (alphaA x y + √(alphaA x y ^ 2 - 1)) : ℝ) : ℂ) := by
  obtain ⟨hab, hp, ha1, hb1⟩ := alphaA_betaA_facts x y
  -- the endpoints `±1`
  by_cases he : y = 0 ∧ |x| = 1
  · obtain ⟨rfl, hx⟩ := he
    have hx' : x = 1 ∨ x = -1 := by
      rcases abs_eq (zero_le_one' ℝ) |>.mp hx with h | h <;> simp [h]
    rcases hx' with rfl | rfl
    · have : alphaA 1 0 = 1 ∧ betaA 1 0 = 1 := by
        simp only [alphaA, betaA]; norm_num
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
      rw [this.1, this.2]; simp [arcsinD_one]
    · have : alphaA (-1) 0 = 1 ∧ betaA (-1) 0 = -1 := by
        simp only [alphaA, betaA]; norm_num
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
      rw [this.1, this.2]
      simp only [Real.sign_zero, Real.arcsin_neg_one]
      push_cast
      rw [show (-1 : ℂ) + 0 * I = -1 by ring, arcsinD_neg_one]; ring
  have hcut : y ≠ 0 ∨ |x| < 1 := by
    rcases hz with h | h
    · exact Or.inl h
    · by_cases hy : y = 0
      · exact Or.inr (lt_of_le_of_ne h fun h' => he ⟨hy, h'⟩)
      · exact Or.inl hy
  have hzc : (x : ℂ) + y * I ∈ arcsinCut := by
    rcases hcut with h | h
    · exact Or.inl (by simpa using h)
    · right; simpa using h
  have hb := betaA_sq_lt_one hcut
  have hbab : |betaA x y| < 1 := by
    rw [← Real.sqrt_sq_eq_abs]; rw [Real.sqrt_lt' one_pos]; simpa using hb
  set L := Real.log (alphaA x y + √(alphaA x y ^ 2 - 1)) with hL
  have hLa : L = Real.arcosh (alphaA x y) := rfl
  have hcoshL : Real.cosh L = alphaA x y := by rw [hLa, Real.cosh_arcosh ha1]
  have hsinhL : Real.sinh L = √(alphaA x y ^ 2 - 1) := by rw [hLa, Real.sinh_arcosh ha1]
  have hsq : √(1 - betaA x y ^ 2) * √(alphaA x y ^ 2 - 1) = |y| := by
    rw [← Real.sqrt_mul (by nlinarith), mul_comm, hp, Real.sqrt_sq_eq_abs]
  obtain ⟨-, hs, hsin, -⟩ := arcsinD_props hzc
  set w : ℂ := ((Real.arcsin (betaA x y) : ℝ) : ℂ) + I * ((Real.sign y * L : ℝ) : ℂ) with hw
  have hwI : w = ((Real.arcsin (betaA x y) : ℝ) : ℂ) + ((Real.sign y * L : ℝ) : ℂ) * I := by
    rw [hw]; push_cast; ring
  have hsinw : sin w = x + y * I := by
    rw [hwI, dlmf_4_21_37, Real.sin_arcsin (by linarith [(abs_lt.mp hbab).1])
      (by linarith [(abs_lt.mp hbab).2]), Real.cos_arcsin]
    rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [Real.sign_of_neg hy, neg_one_mul, Real.cosh_neg, Real.sinh_neg, hcoshL, hsinhL,
        mul_neg, mul_comm (betaA x y), hab, hsq, abs_of_neg hy]
      push_cast; ring
    · subst hy
      rw [Real.sign_zero, zero_mul, Real.cosh_zero, Real.sinh_zero, mul_zero, mul_one]
      have ha : alphaA x 0 = 1 := by
        have : alphaA x 0 ^ 2 - 1 = 0 := by
          rcases mul_eq_zero.mp (by rw [hp]; ring : (alphaA x 0 ^ 2 - 1) * (1 - betaA x 0 ^ 2) = 0)
            with h | h
          · exact h
          · exfalso; linarith
        nlinarith
      rw [ha, one_mul] at hab
      rw [mul_comm, hab]
    · rw [Real.sign_of_pos hy, one_mul, hcoshL, hsinhL, mul_comm (betaA x y), hab, hsq,
        abs_of_pos hy]
      ring
  have hws : w ∈ sinStrip := by
    have h1 := Real.neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp hbab).1
    have h2 := Real.arcsin_lt_pi_div_two.mpr (abs_lt.mp hbab).2
    simp only [sinStrip, Set.mem_ofPred_eq, hw, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, one_mul, sub_zero, add_zero]
    constructor <;> linarith
  exact injOn_sin_sinStrip hs hws (by rw [hsin, hsinw])

/-- **DLMF 4.23.35**: `arccos z = arccos β − i sign(y) ln(α + (α² − 1)^{1/2})`, `±z ∉ (1, ∞)`. -/
theorem dlmf_4_23_35 {x y : ℝ} (hz : y ≠ 0 ∨ |x| ≤ 1) :
    arccosD (x + y * I) = (Real.arccos (betaA x y) : ℝ) -
      I * ((Real.sign y * Real.log (alphaA x y + √(alphaA x y ^ 2 - 1)) : ℝ) : ℂ) := by
  rw [dlmf_4_23_16, dlmf_4_23_34 hz, Real.arccos_eq_pi_div_two_sub_arcsin]
  push_cast; ring

/-- **DLMF 4.23.36**: `arctan z = ½ arctan(2x/(1 − x² − y²)) + ¼ i ln((x² + (y + 1)²)/(x² +
(y − 1)²))`, `|z| < 1`. -/
theorem dlmf_4_23_36 {x y : ℝ} (hz : x ^ 2 + y ^ 2 < 1) :
    arctanD (x + y * I) = 1 / 2 * ((Real.arctan (2 * x / (1 - x ^ 2 - y ^ 2)) : ℝ) : ℂ) +
      1 / 4 * I * ((Real.log ((x ^ 2 + (y + 1) ^ 2) / (x ^ 2 + (y - 1) ^ 2)) : ℝ) : ℂ) := by
  have hy : |y| < 1 := by
    rw [← Real.sqrt_sq_eq_abs, Real.sqrt_lt' one_pos]; nlinarith [sq_nonneg x]
  have hzc : (x : ℂ) + y * I ∈ arctanCut := Or.inr (by simpa using hy)
  set z : ℂ := x + y * I with hzdef
  set u : ℂ := 1 + z * I with hu
  set v : ℂ := 1 - z * I with hv
  have hure : u.re = 1 - y := by simp [hu, hzdef, sub_eq_add_neg]
  have huim : u.im = x := by simp [hu, hzdef]
  have hvre : v.re = 1 + y := by simp [hv, hzdef]
  have hvim : v.im = -x := by simp [hv, hzdef]
  have hNu : normSq u = x ^ 2 + (y - 1) ^ 2 := by rw [normSq_apply, hure, huim]; ring
  have hNv : normSq v = x ^ 2 + (y + 1) ^ 2 := by rw [normSq_apply, hvre, hvim]; ring
  obtain ⟨hv0, hu0, -⟩ := arctan_ratio_props hzc
  have hNv0 : 0 < normSq v := normSq_pos.mpr hv0
  have hNu0 : 0 < normSq u := normSq_pos.mpr hu0
  have hρre : (u / v).re = (1 - x ^ 2 - y ^ 2) / normSq v := by
    rw [Complex.div_re, hure, huim, hvre, hvim]; field_simp; ring
  have hρim : (u / v).im = 2 * x / normSq v := by
    rw [Complex.div_im, hure, huim, hvre, hvim]; field_simp; ring
  have hρpos : 0 < (u / v).re := by rw [hρre]; exact div_pos (by linarith) hNv0
  have harg : arg (u / v) = Real.arctan (2 * x / (1 - x ^ 2 - y ^ 2)) := by
    rw [arg_eq_arctan_of_re_pos hρpos, hρre, hρim]
    congr 1; field_simp
  have hnorm : Real.log ‖u / v‖ = -(1 / 2 * Real.log ((x ^ 2 + (y + 1) ^ 2) /
      (x ^ 2 + (y - 1) ^ 2))) := by
    rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hu0) (norm_ne_zero_iff.mpr hv0),
      Real.log_div (by rw [← hNv]; exact hNv0.ne') (by rw [← hNu]; exact hNu0.ne'), ← hNu, ← hNv,
      ← Complex.sq_norm, ← Complex.sq_norm, Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [arctanD_eq hzc]
  show -I / 2 * log (u / v) = _
  apply Complex.ext
  · simp only [mul_re, div_re, neg_re, I_re, I_im, log_re, log_im, mul_im, div_im, neg_im,
      ofReal_re, ofReal_im, add_re, one_re, one_im]
    rw [harg]
    norm_num
  · simp only [mul_im, div_re, div_im, neg_re, neg_im, I_re, I_im, log_re, log_im, mul_re,
      ofReal_re, ofReal_im, add_im, one_re, one_im]
    rw [hnorm]
    norm_num
    ring

/-! ### §4.23(vii) Special Values and Interrelations -/

theorem arcsinD_ofReal_Icc {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : arcsinD x = Real.arcsin x := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h; push_cast; rw [arcsinD_neg_one, Real.arcsin_neg_one]; push_cast; ring
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · subst h'; push_cast; rw [arcsinD_one, Real.arcsin_one]; push_cast; ring
  exact arcsinD_ofReal ⟨h, h'⟩

theorem arccosD_ofReal_Icc {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : arccosD x = Real.arccos x := by
  rw [dlmf_4_23_16, arcsinD_ofReal_Icc hx, Real.arccos_eq_pi_div_two_sub_arcsin]; push_cast; ring

/-- **Table 4.23.1**, row `x = −1`. -/
theorem dlmf_table_4_23_1_neg_one :
    arcsinD (-1) = -(π / 2) ∧ arccosD (-1) = π ∧ arctanD (-1) = -(π / 4) ∧
      arccscD (-1) = -(π / 2) ∧ arcsecD (-1) = π ∧ arccotD (-1) = -(π / 4) := by
  have ht : arctanD (-1) = -(π / 4) := by
    have := arctanD_ofReal (-1)
    rw [ofReal_neg, ofReal_one] at this
    rw [this, Real.arctan_neg, Real.arctan_one]; push_cast; ring
  have hi : (1 : ℂ) / (-1) = -1 := by norm_num
  have hc : arccosD (-1) = π := by rw [dlmf_4_23_16, arcsinD_neg_one]; ring
  refine ⟨arcsinD_neg_one, hc, ht, ?_, ?_, ?_⟩
  · rw [arccscD, hi, arcsinD_neg_one]
  · rw [arcsecD, hi, hc]
  · rw [arccotD, hi, ht]

/-- **Table 4.23.1**, row `x = 0` (`arcsin`, `arccos`, `arctan`). -/
theorem dlmf_table_4_23_1_zero : arcsinD 0 = 0 ∧ arccosD 0 = π / 2 ∧ arctanD 0 = 0 := by
  have hs : arcsinD 0 = 0 := by
    have := arcsinD_ofReal (x := 0) ⟨by norm_num, by norm_num⟩
    simpa using this
  refine ⟨hs, by rw [dlmf_4_23_16, hs, sub_zero], ?_⟩
  have := arctanD_ofReal 0
  simpa using this

/-- **Table 4.23.1**, row `x = 1`. -/
theorem dlmf_table_4_23_1_one :
    arcsinD 1 = π / 2 ∧ arccosD 1 = 0 ∧ arctanD 1 = π / 4 ∧
      arccscD 1 = π / 2 ∧ arcsecD 1 = 0 ∧ arccotD 1 = π / 4 := by
  have ht : arctanD 1 = π / 4 := by
    have := arctanD_ofReal 1
    rw [ofReal_one] at this
    rw [this, Real.arctan_one]; push_cast; ring
  have hc : arccosD 1 = 0 := by rw [dlmf_4_23_16, arcsinD_one, sub_self]
  refine ⟨arcsinD_one, hc, ht, ?_, ?_, ?_⟩
  · rw [arccscD, div_one, arcsinD_one]
  · rw [arcsecD, div_one, hc]
  · rw [arccotD, div_one, ht]

/-- **Table 4.23.1**, entry `arccot 0 = ∓½π`: the one-sided limits along the real axis. -/
theorem dlmf_table_4_23_1_arccot_zero :
    Tendsto (fun x : ℝ => arccotD x) (𝓝[>] 0) (𝓝 (π / 2)) ∧
      Tendsto (fun x : ℝ => arccotD x) (𝓝[<] 0) (𝓝 (-(π / 2))) := by
  have he : (fun x : ℝ => arccotD x) = fun x => ((Real.arctan x⁻¹ : ℝ) : ℂ) := by
    funext x; rw [arccotD_ofReal, one_div]
  rw [he]
  constructor
  · have := (continuous_ofReal.tendsto _).comp ((tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atTop).comp tendsto_inv_nhdsGT_zero)
    simpa [Function.comp_def] using this
  · have := (continuous_ofReal.tendsto _).comp ((tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atBot).comp tendsto_inv_nhdsLT_zero)
    simpa [Function.comp_def] using this

/-- `arccsc x = arcsin(1/x)` for real `|x| ≥ 1`. -/
theorem arccscD_ofReal {x : ℝ} (hx : 1 ≤ |x|) : arccscD x = Real.arcsin x⁻¹ := by
  have h0 : 0 < |x| := by linarith
  have hb : |x⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hx
  rw [arccscD, one_div, ← ofReal_inv, arcsinD_ofReal_Icc (abs_le.mp hb)]

theorem tendsto_arccscD_of {l : Filter ℝ} (hl : ∀ᶠ x in l, 1 ≤ |x|)
    (h : Tendsto (fun x : ℝ => x⁻¹) l (𝓝 0)) :
    Tendsto (fun x : ℝ => arccscD x) l (𝓝 0) := by
  have := (continuous_ofReal.tendsto _).comp ((Real.continuous_arcsin.tendsto 0).comp h)
  simp only [Function.comp_def, Real.arcsin_zero, ofReal_zero] at this
  exact this.congr' (hl.mono fun x hx => (arccscD_ofReal hx).symm)

theorem tendsto_arccotD_of {l : Filter ℝ} (h : Tendsto (fun x : ℝ => x⁻¹) l (𝓝 0)) :
    Tendsto (fun x : ℝ => arccotD x) l (𝓝 0) := by
  have := (continuous_ofReal.tendsto _).comp ((Real.continuous_arctan.tendsto 0).comp h)
  simp only [Function.comp_def, Real.arctan_zero, ofReal_zero] at this
  refine this.congr fun x => ?_
  rw [arccotD_ofReal, one_div]

/-- **Table 4.23.1**, row `x = ∞` (limits along the real axis). -/
theorem dlmf_table_4_23_1_top :
    Tendsto (fun x : ℝ => arctanD x) atTop (𝓝 (π / 2)) ∧
      Tendsto (fun x : ℝ => arccscD x) atTop (𝓝 0) ∧
      Tendsto (fun x : ℝ => arcsecD x) atTop (𝓝 (π / 2)) ∧
      Tendsto (fun x : ℝ => arccotD x) atTop (𝓝 0) := by
  have hl : ∀ᶠ x : ℝ in atTop, 1 ≤ |x| :=
    (eventually_ge_atTop 1).mono fun x hx => hx.trans (le_abs_self x)
  have hc := tendsto_arccscD_of hl tendsto_inv_atTop_zero
  refine ⟨?_, hc, ?_, tendsto_arccotD_of tendsto_inv_atTop_zero⟩
  · have := (continuous_ofReal.tendsto _).comp (tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atTop)
    simp only [ofReal_div, ofReal_ofNat] at this
    refine this.congr fun x => ?_
    simp [arctanD_ofReal]
  · have := (tendsto_const_nhds (x := ((π / 2 : ℝ) : ℂ))).sub hc
    simp only [sub_zero, ofReal_div, ofReal_ofNat] at this
    refine this.congr fun x => ?_
    rw [dlmf_4_23_17]

/-- **Table 4.23.1**, row `x = −∞` (limits along the real axis). -/
theorem dlmf_table_4_23_1_bot :
    Tendsto (fun x : ℝ => arctanD x) atBot (𝓝 (-(π / 2))) ∧
      Tendsto (fun x : ℝ => arccscD x) atBot (𝓝 0) ∧
      Tendsto (fun x : ℝ => arcsecD x) atBot (𝓝 (π / 2)) ∧
      Tendsto (fun x : ℝ => arccotD x) atBot (𝓝 0) := by
  have hl : ∀ᶠ x : ℝ in atBot, 1 ≤ |x| :=
    (eventually_le_atBot (-1)).mono fun x hx => by rw [abs_of_neg (by linarith)]; linarith
  have hc := tendsto_arccscD_of hl tendsto_inv_atBot_zero
  refine ⟨?_, hc, ?_, tendsto_arccotD_of tendsto_inv_atBot_zero⟩
  · have := (continuous_ofReal.tendsto _).comp (tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atBot)
    simp only [ofReal_neg, ofReal_div, ofReal_ofNat] at this
    refine this.congr fun x => ?_
    simp [arctanD_ofReal]
  · have := (tendsto_const_nhds (x := ((π / 2 : ℝ) : ℂ))).sub hc
    simp only [sub_zero, ofReal_div, ofReal_ofNat] at this
    refine this.congr fun x => ?_
    rw [dlmf_4_23_17]

/-- On the first quadrant each principal inverse function inverts its function. -/
theorem inv_trig_first_quadrant {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    arcsinD (Real.sin θ) = θ ∧ arccosD (Real.cos θ) = θ ∧ arctanD (Real.tan θ) = θ ∧
      arccscD (1 / Real.sin θ : ℝ) = θ ∧ arcsecD (1 / Real.cos θ : ℝ) = θ ∧
      arccotD (Real.cot θ) = θ := by
  obtain ⟨hs, hc, -⟩ := first_quadrant_facts hθ
  have hπ := Real.pi_pos
  have hs1 : Real.sin θ < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hθ.1]) le_rfl hθ.2
  have hc1 : Real.cos θ < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl hθ.2.le hθ.1
  have hS : arcsinD (Real.sin θ) = θ := by
    rw [arcsinD_ofReal ⟨by linarith, hs1⟩, Real.arcsin_sin (by linarith [hθ.1]) hθ.2.le]
  have hC : arccosD (Real.cos θ) = θ := by
    rw [arccosD_ofReal ⟨by linarith, hc1⟩, Real.arccos_cos hθ.1.le (by linarith [hθ.2])]
  refine ⟨hS, hC, ?_, ?_, ?_, ?_⟩
  · rw [arctanD_ofReal, Real.arctan_tan (by linarith [hθ.1]) hθ.2]
  · rw [arccscD]; push_cast; rw [one_div_one_div]; exact_mod_cast hS
  · rw [arcsecD]; push_cast; rw [one_div_one_div]; exact_mod_cast hC
  · rw [arccotD_ofReal, Real.cot_eq_cos_div_sin, one_div_div, ← Real.tan_eq_sin_div_cos,
      Real.arctan_tan (by linarith [hθ.1]) hθ.2]

/-- **§4.23(vii)** with Table 4.16.3, column `sin θ = a`, `0 < a < 1`. -/
theorem dlmf_4_23_vii_sin {a : ℝ} (ha : a ∈ Ioo 0 1) :
    arccosD (√(1 - a ^ 2) : ℝ) = arcsinD a ∧ arctanD (a * (√(1 - a ^ 2))⁻¹ : ℝ) = arcsinD a ∧
      arccscD (a⁻¹ : ℝ) = arcsinD a ∧ arcsecD ((√(1 - a ^ 2))⁻¹ : ℝ) = arcsinD a ∧
      arccotD (a⁻¹ * √(1 - a ^ 2) : ℝ) = arcsinD a := by
  obtain ⟨θ, hθd⟩ : ∃ θ, θ = Real.arcsin a := ⟨_, rfl⟩
  have hθ : θ ∈ Ioo 0 (π / 2) :=
    hθd ▸ ⟨Real.arcsin_pos.mpr ha.1, Real.arcsin_lt_pi_div_two.mpr ha.2⟩
  have hv : arcsinD a = θ := by rw [hθd]; exact arcsinD_ofReal ⟨by linarith [ha.1], ha.2⟩
  obtain ⟨-, e2, e3, e4, e5, e6⟩ :=
    dlmf_table_4_16_3_sin hθ (hθd ▸ Real.sin_arcsin (by linarith [ha.1]) ha.2.le)
  obtain ⟨-, i2, i3, i4, i5, i6⟩ := inv_trig_first_quadrant hθ
  rw [hv]
  exact ⟨by rw [← e2, i2], by rw [← e3, i3], by rw [← e4, i4], by rw [← e5, i5],
    by rw [← e6, i6]⟩

/-- **§4.23(vii)** with Table 4.16.3, column `cos θ = a`, `0 < a < 1`. -/
theorem dlmf_4_23_vii_cos {a : ℝ} (ha : a ∈ Ioo 0 1) :
    arcsinD (√(1 - a ^ 2) : ℝ) = arccosD a ∧ arctanD (a⁻¹ * √(1 - a ^ 2) : ℝ) = arccosD a ∧
      arccscD ((√(1 - a ^ 2))⁻¹ : ℝ) = arccosD a ∧ arcsecD (a⁻¹ : ℝ) = arccosD a ∧
      arccotD (a * (√(1 - a ^ 2))⁻¹ : ℝ) = arccosD a := by
  obtain ⟨θ, hθd⟩ : ∃ θ, θ = Real.arccos a := ⟨_, rfl⟩
  have hθ : θ ∈ Ioo 0 (π / 2) :=
    hθd ▸ ⟨Real.arccos_pos.mpr ha.2, Real.arccos_lt_pi_div_two.mpr ha.1⟩
  have hv : arccosD a = θ := by rw [hθd]; exact arccosD_ofReal ⟨by linarith [ha.1], ha.2⟩
  obtain ⟨e1, -, e3, e4, e5, e6⟩ :=
    dlmf_table_4_16_3_cos hθ (hθd ▸ Real.cos_arccos (by linarith [ha.1]) ha.2.le)
  obtain ⟨i1, -, i3, i4, i5, i6⟩ := inv_trig_first_quadrant hθ
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e3, i3], by rw [← e4, i4], by rw [← e5, i5],
    by rw [← e6, i6]⟩

/-- **§4.23(vii)** with Table 4.16.3, column `tan θ = a`, `a > 0`. -/
theorem dlmf_4_23_vii_tan {a : ℝ} (ha : 0 < a) :
    arcsinD (a * (√(1 + a ^ 2))⁻¹ : ℝ) = arctanD a ∧
      arccosD ((√(1 + a ^ 2))⁻¹ : ℝ) = arctanD a ∧
      arccscD (a⁻¹ * √(1 + a ^ 2) : ℝ) = arctanD a ∧ arcsecD (√(1 + a ^ 2) : ℝ) = arctanD a ∧
      arccotD (a⁻¹ : ℝ) = arctanD a := by
  obtain ⟨θ, hθd⟩ : ∃ θ, θ = Real.arctan a := ⟨_, rfl⟩
  have hθ : θ ∈ Ioo 0 (π / 2) := hθd ▸ ⟨Real.arctan_pos.mpr ha, Real.arctan_lt_pi_div_two a⟩
  have hv : arctanD a = θ := by rw [hθd]; exact arctanD_ofReal a
  obtain ⟨e1, e2, -, e4, e5, e6⟩ := dlmf_table_4_16_3_tan hθ (hθd ▸ Real.tan_arctan a)
  obtain ⟨i1, i2, -, i4, i5, i6⟩ := inv_trig_first_quadrant hθ
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e2, i2], by rw [← e4, i4], by rw [← e5, i5],
    by rw [← e6, i6]⟩

/-- **§4.23(vii)** with Table 4.16.3, column `csc θ = a`, `a > 1`. -/
theorem dlmf_4_23_vii_csc {a : ℝ} (ha : 1 < a) :
    arcsinD (a⁻¹ : ℝ) = arccscD a ∧ arccosD (a⁻¹ * √(a ^ 2 - 1) : ℝ) = arccscD a ∧
      arctanD ((√(a ^ 2 - 1))⁻¹ : ℝ) = arccscD a ∧
      arcsecD (a * (√(a ^ 2 - 1))⁻¹ : ℝ) = arccscD a ∧
      arccotD (√(a ^ 2 - 1) : ℝ) = arccscD a := by
  have ha0 : 0 < a := by linarith
  have hb1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  obtain ⟨θ, hθd⟩ : ∃ θ, θ = Real.arcsin a⁻¹ := ⟨_, rfl⟩
  have hθ : θ ∈ Ioo 0 (π / 2) :=
    hθd ▸ ⟨Real.arcsin_pos.mpr (inv_pos.mpr ha0), Real.arcsin_lt_pi_div_two.mpr hb1⟩
  have hv : arccscD a = θ := by
    rw [hθd]; exact arccscD_ofReal (by rw [abs_of_pos ha0]; exact ha.le)
  have hg : 1 / Real.sin θ = a := by
    rw [hθd, Real.sin_arcsin (by linarith [inv_pos.mpr ha0]) hb1.le, one_div, inv_inv]
  obtain ⟨e1, e2, e3, -, e5, e6⟩ := dlmf_table_4_16_3_csc hθ hg
  obtain ⟨i1, i2, i3, -, i5, i6⟩ := inv_trig_first_quadrant hθ
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e2, i2], by rw [← e3, i3], by rw [← e5, i5],
    by rw [← e6, i6]⟩

/-- **§4.23(vii)** with Table 4.16.3, column `sec θ = a`, `a > 1`. -/
theorem dlmf_4_23_vii_sec {a : ℝ} (ha : 1 < a) :
    arcsinD (a⁻¹ * √(a ^ 2 - 1) : ℝ) = arcsecD a ∧ arccosD (a⁻¹ : ℝ) = arcsecD a ∧
      arctanD (√(a ^ 2 - 1) : ℝ) = arcsecD a ∧
      arccscD (a * (√(a ^ 2 - 1))⁻¹ : ℝ) = arcsecD a ∧
      arccotD ((√(a ^ 2 - 1))⁻¹ : ℝ) = arcsecD a := by
  have ha0 : 0 < a := by linarith
  have hb1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hb : a⁻¹ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [inv_pos.mpr ha0], hb1.le⟩
  obtain ⟨θ, hθd⟩ : ∃ θ, θ = Real.arccos a⁻¹ := ⟨_, rfl⟩
  have hθ : θ ∈ Ioo 0 (π / 2) :=
    hθd ▸ ⟨Real.arccos_pos.mpr hb1, Real.arccos_lt_pi_div_two.mpr (inv_pos.mpr ha0)⟩
  have hv : arcsecD a = θ := by
    rw [hθd, arcsecD, one_div, ← ofReal_inv, arccosD_ofReal_Icc hb]
  have hg : 1 / Real.cos θ = a := by
    rw [hθd, Real.cos_arccos hb.1 hb.2, one_div, inv_inv]
  obtain ⟨e1, e2, e3, e4, -, e6⟩ := dlmf_table_4_16_3_sec hθ hg
  obtain ⟨i1, i2, i3, i4, -, i6⟩ := inv_trig_first_quadrant hθ
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e2, i2], by rw [← e3, i3], by rw [← e4, i4],
    by rw [← e6, i6]⟩

/-- **§4.23(vii)** with Table 4.16.3, column `cot θ = a`, `a > 0`. -/
theorem dlmf_4_23_vii_cot {a : ℝ} (ha : 0 < a) :
    arcsinD ((√(1 + a ^ 2))⁻¹ : ℝ) = arccotD a ∧
      arccosD (a * (√(1 + a ^ 2))⁻¹ : ℝ) = arccotD a ∧ arctanD (a⁻¹ : ℝ) = arccotD a ∧
      arccscD (√(1 + a ^ 2) : ℝ) = arccotD a ∧
      arcsecD (a⁻¹ * √(1 + a ^ 2) : ℝ) = arccotD a := by
  obtain ⟨θ, hθd⟩ : ∃ θ, θ = Real.arctan a⁻¹ := ⟨_, rfl⟩
  have hθ : θ ∈ Ioo 0 (π / 2) :=
    hθd ▸ ⟨Real.arctan_pos.mpr (inv_pos.mpr ha), Real.arctan_lt_pi_div_two _⟩
  have hv : arccotD a = θ := by rw [hθd, arccotD_ofReal, one_div]
  have hg : Real.cot θ = a := by
    rw [hθd, Real.cot_eq_cos_div_sin, ← inv_div, ← Real.tan_eq_sin_div_cos, Real.tan_arctan,
      inv_inv]
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := dlmf_table_4_16_3_cot hθ hg
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := inv_trig_first_quadrant hθ
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e2, i2], by rw [← e3, i3], by rw [← e4, i4],
    by rw [← e5, i5]⟩

/-- **§4.23(vii)**, DLMF's example: `arcsec a = arccot((a² − 1)^{-1/2})` (`a > 1`). -/
theorem dlmf_4_23_vii_example {a : ℝ} (ha : 1 < a) :
    arcsecD a = arccotD ((a ^ 2 - 1) ^ (-1 / 2 : ℝ) : ℝ) := by
  have h : (a ^ 2 - 1) ^ (-1 / 2 : ℝ) = (√(a ^ 2 - 1))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by nlinarith)]; norm_num
  rw [h, (dlmf_4_23_vii_sec ha).2.2.2.2]

end Azurite.DLMF
