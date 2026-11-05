/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section8NewtonExample
import Azurite.DLMF.Chapter3.Section5ContourTable

/-!
# DLMF §3.8(ii), Example: Table 3.8.1, certified

Exact rational interval arithmetic checked by `decide +kernel`: `sin`, `cos` by Taylor series
with remainder at half angles (`sinSumQ`, `cosEncl`), `cot` on `(0, π/2)` (`cotLo`, `cotHi`,
`cot_mem`, `cot_antitone`), `π` to 20 decimals, and the step `φ` on intervals (`phiEncl`,
`phiEncl_sound`).

* The zero: `ζ ∈ (4.49340 94579 0905, 4.49340 94579 0907)` is the unique zero in `(π, 3π/2)`
  and the first positive zero (`dlmf_3_8_ii_example_zero`).
* Table 3.8.1 (`dlmf_table_3_8_1`): Newton's iterates from `x₀ = 4.65` are `φⁿ(4.65)` and tend to
  `ζ`. The printed `x₀`, `x₆`, `x₇`, `x₈` are correctly rounded. **Erratum**: `x₁, …, x₅` are off
  by 1–2 units in the 13th decimal (`tab381`, `tab381c`).
* **Erratum**: "When `x₀ ≤ 4.2875` … Newton's rule does not converge to the required zero" fails
  for `x₀ = 2.25` (`dlmf_3_8_ii_example_erratum`).
* The function `x cos x − sin x = cos x (x − tan x)` (`exG`, `exG_eq`) has the Newton rule
  `x + cot x − 1/x` (`newtonStep_exG`). The claims that this converges faster and from a larger
  interval are not formalized.
-/

open Finset Filter Topology Set Real

namespace Azurite.DLMF

/-! ### Rational enclosures of `sin`, `cot` -/

/-- `∑_{j<n} ℑ(iy)ʲ/j!`. -/
def sinSumQ (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sinSumQ y n + (cisPow y n).2 / n.factorial

theorem sinSumQ_cast (y : ℚ) (n : ℕ) :
    (sinSumQ y n : ℝ) = (∑ i ∈ range n, ((y : ℂ) * Complex.I) ^ i / i.factorial).im := by
  induction n with
  | zero => simp [sinSumQ]
  | succ n ih =>
    rw [sinSumQ, sum_range_succ, Complex.add_im, ← ih, cisPow_spec,
      show ((n.factorial : ℂ)) = ((n.factorial : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_im]
    push_cast
    ring

theorem sin_sub_sinSumQ_le {y : ℚ} (hy : |y| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.sin y - sinSumQ y n| ≤ (expErrQ y n : ℝ) := by
  have hz : ‖(y : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ratCast]; exact_mod_cast hy
  have hb := Complex.exp_bound hz hn
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ratCast] at hb
  have him : Real.sin y - sinSumQ y n = (Complex.exp ((y : ℂ) * Complex.I) -
      ∑ i ∈ range n, ((y : ℂ) * Complex.I) ^ i / i.factorial).im := by
    rw [Complex.sub_im, ← sinSumQ_cast, show ((y : ℂ)) = ((y : ℝ) : ℂ) by push_cast; rfl,
      Complex.exp_ofReal_mul_I_im]
  rw [him]
  refine (Complex.abs_im_le_norm _).trans (hb.trans (le_of_eq ?_))
  simp [expErrQ, div_eq_mul_inv]

/-- Number of Taylor terms. -/
def nTay : ℕ := 30

/-- Enclosures of `sin(t/2)` and `cos(t/2)`. -/
def sinHalfLo (t : ℚ) : ℚ := sinSumQ (t / 2) nTay - expErrQ (t / 2) nTay
def sinHalfHi (t : ℚ) : ℚ := sinSumQ (t / 2) nTay + expErrQ (t / 2) nTay
def cosHalfLo (t : ℚ) : ℚ := (cosEncl nTay (t / 2)).1
def cosHalfHi (t : ℚ) : ℚ := (cosEncl nTay (t / 2)).2

/-- `cot t = (1 − 2 sin²(t/2))/(2 sin(t/2) cos(t/2))`: lower and upper bounds. -/
def cotLo (t : ℚ) : ℚ := (1 - 2 * sinHalfHi t ^ 2) / (2 * sinHalfHi t * cosHalfHi t)
def cotHi (t : ℚ) : ℚ := (1 - 2 * sinHalfLo t ^ 2) / (2 * sinHalfLo t * cosHalfLo t)

/-- The checkable conditions for `cotLo t ≤ cot t ≤ cotHi t`. -/
def CotOk (t : ℚ) : Prop :=
  0 ≤ t ∧ t ≤ 2 ∧ 0 < sinHalfLo t ∧ 0 < cosHalfLo t ∧ 0 < 1 - 2 * sinHalfHi t ^ 2

instance (t : ℚ) : Decidable (CotOk t) := by unfold CotOk; infer_instance

theorem cot_mem {t : ℚ} (h : CotOk t) :
    (cotLo t : ℝ) ≤ cot t ∧ cot (t : ℝ) ≤ cotHi t := by
  obtain ⟨h0, h2, hsl, hcl, hnum⟩ := h
  have hy : |t / 2| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hs := abs_le.mp (sin_sub_sinSumQ_le hy (show 0 < nTay by decide))
  have hc := cosEncl_sound (show 0 < nTay by decide) hy
  push_cast at hs hc
  set s := Real.sin ((t : ℝ) / 2)
  set c := Real.cos ((t : ℝ) / 2)
  have hsl' : (sinHalfLo t : ℝ) ≤ s := by simp only [sinHalfLo]; push_cast; linarith [hs.1]
  have hsu' : s ≤ sinHalfHi t := by simp only [sinHalfHi]; push_cast; linarith [hs.2]
  have hcl' : (cosHalfLo t : ℝ) ≤ c := hc.1
  have hcu' : c ≤ cosHalfHi t := hc.2
  have hsl0 : (0 : ℝ) < sinHalfLo t := by exact_mod_cast hsl
  have hcl0 : (0 : ℝ) < cosHalfLo t := by exact_mod_cast hcl
  have hnum' : (0 : ℝ) < 1 - 2 * (sinHalfHi t : ℝ) ^ 2 := by exact_mod_cast hnum
  have hcot : cot (t : ℝ) = (1 - 2 * s ^ 2) / (2 * s * c) := by
    rw [cot_eq_cos_div_sin, show (t : ℝ) = 2 * ((t : ℝ) / 2) by ring, sin_two_mul, cos_two_mul]
    have := sin_sq_add_cos_sq ((t : ℝ) / 2)
    congr 1
    linarith
  rw [hcot]
  have hs0 : 0 < s := lt_of_lt_of_le hsl0 hsl'
  have hc0 : 0 < c := lt_of_lt_of_le hcl0 hcl'
  constructor
  · simp only [cotLo]; push_cast
    have hN : 1 - 2 * (sinHalfHi t : ℝ) ^ 2 ≤ 1 - 2 * s ^ 2 := by nlinarith
    have hD : 2 * s * c ≤ 2 * (sinHalfHi t : ℝ) * cosHalfHi t := by
      have := mul_le_mul hsu' hcu' hc0.le (le_trans hs0.le hsu'); nlinarith
    exact div_le_div₀ (by linarith) hN (by positivity) hD
  · simp only [cotHi]; push_cast
    have hN : 1 - 2 * s ^ 2 ≤ 1 - 2 * (sinHalfLo t : ℝ) ^ 2 := by nlinarith
    have hD : 2 * (sinHalfLo t : ℝ) * cosHalfLo t ≤ 2 * s * c := by
      have := mul_le_mul hsl' hcl' hcl0.le hs0.le; nlinarith
    exact div_le_div₀ (by nlinarith) hN (by positivity) hD

/-- `cot` decreases on `(0, π/2)`. -/
theorem cot_antitone {a y : ℝ} (ha : 0 < a) (hay : a ≤ y) (hy : y < π / 2) : cot y ≤ cot a := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin]
  have hsa : 0 < sin a := sin_pos_of_pos_of_lt_pi ha (by linarith [pi_pos])
  have hsy : sin a ≤ sin y := sin_le_sin_of_le_of_le_pi_div_two (by linarith) hy.le hay
  have hcy : cos y ≤ cos a := cos_le_cos_of_nonneg_of_le_pi ha.le (by linarith [pi_pos]) hay
  have hcy0 : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith, hy⟩
  rw [div_le_div_iff₀ (lt_of_lt_of_le hsa hsy) hsa]
  nlinarith

/-! ### `π` -/

/- `piLoQ < π < piHiQ` (20 decimals) are those of `Section5ContourTable`. -/

theorem cot_sub_pi (x : ℝ) : cot (x - π) = cot x := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_sub_pi, sin_sub_pi, neg_div_neg_eq]

/-! ### One step of `φ` on an interval -/

/-- Outward-rounding precision. -/
def dPrec : ℕ := 120

/-- An enclosure of `cot x` for `x ∈ [l, u] ⊂ (π, 3π/2)`: `cot x = cot(x − π)`. -/
def cotEnclX (I : ℚ × ℚ) : ℚ × ℚ :=
  (cotLo (rdUp 90 (I.2 - piLoQ)), cotHi (rdDown 90 (I.1 - piHiQ)))

def CotXOk (I : ℚ × ℚ) : Prop :=
  CotOk (rdUp 90 (I.2 - piLoQ)) ∧ CotOk (rdDown 90 (I.1 - piHiQ)) ∧
    0 < rdDown 90 (I.1 - piHiQ) ∧ rdUp 90 (I.2 - piLoQ) ≤ 157 / 100 ∧ I.1 ≤ I.2

instance (I : ℚ × ℚ) : Decidable (CotXOk I) := by unfold CotXOk; infer_instance

theorem cotEnclX_sound {I : ℚ × ℚ} (h : CotXOk I) {x : ℝ} (hx1 : (I.1 : ℝ) ≤ x)
    (hx2 : x ≤ I.2) : ((cotEnclX I).1 : ℝ) ≤ cot x ∧ cot x ≤ (cotEnclX I).2 := by
  obtain ⟨hu, hl, hl0, hu1, -⟩ := h
  set yl := rdDown 90 (I.1 - piHiQ)
  set yu := rdUp 90 (I.2 - piLoQ)
  have hyl : (yl : ℝ) ≤ x - π := by
    have := rdDown_le 90 (I.1 - piHiQ)
    have h' : ((I.1 - piHiQ : ℚ) : ℝ) ≤ x - π := by push_cast; linarith [pi_lt_piHiQ]
    exact le_trans (by exact_mod_cast this) h'
  have hyu : x - π ≤ (yu : ℝ) := by
    have := le_rdUp 90 (I.2 - piLoQ)
    have h' : x - π ≤ ((I.2 - piLoQ : ℚ) : ℝ) := by push_cast; linarith [piLoQ_lt]
    exact le_trans h' (by exact_mod_cast this)
  have hl0' : (0 : ℝ) < yl := by exact_mod_cast hl0
  have hpi2 : (157 / 100 : ℝ) < π / 2 := by linarith [Real.pi_gt_d2]
  have hu1q : ((yu : ℚ) : ℝ) ≤ ((157 / 100 : ℚ) : ℝ) := by exact_mod_cast hu1
  push_cast at hu1q
  have hu1' : (yu : ℝ) < π / 2 := lt_of_le_of_lt hu1q hpi2
  rw [← cot_sub_pi x]
  have h1 := cot_mem hu
  have h2 := cot_mem hl
  constructor
  · exact h1.1.trans (cot_antitone (by linarith) hyu hu1')
  · exact (cot_antitone hl0' hyl (by linarith)).trans h2.2

/-- An enclosure of `φ(x) = x + x cot² x − cot x` for `x ∈ [l, u]`. -/
def phiEncl (I : ℚ × ℚ) : ℚ × ℚ :=
  (rdDown dPrec (I.1 + I.1 * (cotEnclX I).1 ^ 2 - (cotEnclX I).2),
    rdUp dPrec (I.2 + I.2 * (cotEnclX I).2 ^ 2 - (cotEnclX I).1))

def PhiOk (I : ℚ × ℚ) : Prop := CotXOk I ∧ 0 < I.1 ∧ 0 < (cotEnclX I).1

instance (I : ℚ × ℚ) : Decidable (PhiOk I) := by unfold PhiOk; infer_instance

theorem phiEncl_sound {I : ℚ × ℚ} (h : PhiOk I) {x : ℝ} (hx1 : (I.1 : ℝ) ≤ x)
    (hx2 : x ≤ I.2) : ((phiEncl I).1 : ℝ) ≤ exPhi x ∧ exPhi x ≤ (phiEncl I).2 := by
  obtain ⟨hc, hl0, hcl0⟩ := h
  obtain ⟨h1, h2⟩ := cotEnclX_sound hc hx1 hx2
  have hl0' : (0 : ℝ) < I.1 := by exact_mod_cast hl0
  have hcl0' : (0 : ℝ) < (cotEnclX I).1 := by exact_mod_cast hcl0
  set c := cot x
  have hc0 : 0 < c := lt_of_lt_of_le hcl0' h1
  simp only [phiEncl, exPhi]
  constructor
  · have hr := rdDown_le dPrec (I.1 + I.1 * (cotEnclX I).1 ^ 2 - (cotEnclX I).2)
    have hr' : ((rdDown dPrec (I.1 + I.1 * (cotEnclX I).1 ^ 2 - (cotEnclX I).2) : ℚ) : ℝ) ≤
        ((I.1 + I.1 * (cotEnclX I).1 ^ 2 - (cotEnclX I).2 : ℚ) : ℝ) := by exact_mod_cast hr
    refine le_trans hr' ?_
    push_cast
    have : (I.1 : ℝ) * (cotEnclX I).1 ^ 2 ≤ x * c ^ 2 :=
      mul_le_mul hx1 (pow_le_pow_left₀ hcl0'.le h1 2) (by positivity) (by linarith)
    linarith
  · have hr := le_rdUp dPrec (I.2 + I.2 * (cotEnclX I).2 ^ 2 - (cotEnclX I).1)
    have hr' : ((I.2 + I.2 * (cotEnclX I).2 ^ 2 - (cotEnclX I).1 : ℚ) : ℝ) ≤
        ((rdUp dPrec (I.2 + I.2 * (cotEnclX I).2 ^ 2 - (cotEnclX I).1) : ℚ) : ℝ) := by
      exact_mod_cast hr
    refine le_trans ?_ hr'
    push_cast
    have : x * c ^ 2 ≤ (I.2 : ℝ) * (cotEnclX I).2 ^ 2 :=
      mul_le_mul hx2 (pow_le_pow_left₀ hc0.le h2 2) (by positivity) (by linarith)
    linarith

/-! ### Table 3.8.1 -/

/-- The enclosures of `xₙ = φⁿ(4.65)`. -/
def tabEncl : ℕ → ℚ × ℚ
  | 0 => (465 / 100, 465 / 100)
  | n + 1 => phiEncl (tabEncl n)

theorem tabEncl_ok : ∀ n < 8, PhiOk (tabEncl n) := by decide +kernel

theorem tabEncl_sound : ∀ n ≤ 8, ((tabEncl n).1 : ℝ) ≤ exPhi^[n] (465 / 100) ∧
    exPhi^[n] (465 / 100) ≤ (tabEncl n).2 := by
  intro n hn
  induction n with
  | zero => simp [tabEncl]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact phiEncl_sound (tabEncl_ok n (by omega)) (ih (by omega)).1 (ih (by omega)).2

/-- The values printed in Table 3.8.1 (`xₙ` to 13 decimals). -/
def tab381 : ℕ → ℚ
  | 0 => 46500000000000 / 10 ^ 13
  | 1 => 46056766065900 / 10 ^ 13
  | 2 => 45514053475751 / 10 ^ 13
  | 3 => 45090376975617 / 10 ^ 13
  | 4 => 44945561600185 / 10 ^ 13
  | 5 => 44934156569391 / 10 ^ 13
  | 6 => 44934094580903 / 10 ^ 13
  | _ => 44934094579091 / 10 ^ 13

/-- The correctly rounded values. -/
def tab381c : ℕ → ℚ
  | 0 => 46500000000000 / 10 ^ 13
  | 1 => 46056766065899 / 10 ^ 13
  | 2 => 45514053475750 / 10 ^ 13
  | 3 => 45090376975615 / 10 ^ 13
  | 4 => 44945561600187 / 10 ^ 13
  | 5 => 44934156569392 / 10 ^ 13
  | 6 => 44934094580903 / 10 ^ 13
  | _ => 44934094579091 / 10 ^ 13

/-- Half a unit in the 13th decimal. -/
def halfUlp : ℚ := 5 / 10 ^ 14

theorem tab_correct_check : ∀ n ≤ 8,
    tab381c n - halfUlp < (tabEncl n).1 ∧ (tabEncl n).2 < tab381c n + halfUlp := by decide +kernel

theorem tab_wrong_check : ∀ n ∈ Finset.Icc 1 5,
    (tabEncl n).2 < tab381 n - halfUlp ∨ tab381 n + halfUlp < (tabEncl n).1 := by decide +kernel

/-! ### The zero `ζ = 4.49340 94579 091` -/

theorem tan_eq_inv_cot (x : ℝ) : tan x = (cot x)⁻¹ := by
  rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin, inv_div]

def zetaLo : ℚ := 449340945790905 / 10 ^ 14
def zetaHi : ℚ := 449340945790907 / 10 ^ 14

theorem zeta_checks : CotXOk (zetaLo, zetaLo) ∧ 0 < (cotEnclX (zetaLo, zetaLo)).1 ∧
    1 < zetaLo * (cotEnclX (zetaLo, zetaLo)).1 ∧ CotXOk (zetaHi, zetaHi) ∧
    0 < (cotEnclX (zetaHi, zetaHi)).1 ∧ zetaHi * (cotEnclX (zetaHi, zetaHi)).2 < 1 := by
  decide +kernel

theorem three_pi_div_two_gt : (47 / 10 : ℝ) < 3 * π / 2 := by linarith [Real.pi_gt_d2]

theorem mem_Ioo_of_tab {x : ℝ} (h1 : (449 / 100 : ℝ) ≤ x) (h2 : x ≤ 47 / 10) :
    x ∈ Ioo π (3 * π / 2) :=
  ⟨by linarith [Real.pi_lt_d2], by linarith [three_pi_div_two_gt]⟩

theorem exF_zetaLo_pos : 0 < tanExF zetaLo := by
  obtain ⟨h1, h2, h3, -⟩ := zeta_checks
  obtain ⟨hl, -⟩ := cotEnclX_sound h1 (x := zetaLo) le_rfl le_rfl
  have h2' : (0 : ℝ) < (cotEnclX (zetaLo, zetaLo)).1 := by exact_mod_cast h2
  have h3' : (1 : ℝ) < zetaLo * (cotEnclX (zetaLo, zetaLo)).1 := by exact_mod_cast h3
  have hc : 0 < cot (zetaLo : ℝ) := lt_of_lt_of_le h2' hl
  simp only [tanExF, tan_eq_inv_cot]
  rw [sub_pos, inv_lt_comm₀ hc (by norm_num [zetaLo])]
  rw [inv_lt_iff_one_lt_mul₀' (by norm_num [zetaLo])] at *
  nlinarith

theorem exF_zetaHi_neg : tanExF zetaHi < 0 := by
  obtain ⟨-, -, -, h4, h5, h6⟩ := zeta_checks
  obtain ⟨hl, hu⟩ := cotEnclX_sound h4 (x := zetaHi) le_rfl le_rfl
  have h5' : (0 : ℝ) < (cotEnclX (zetaHi, zetaHi)).1 := by exact_mod_cast h5
  have h6' : (zetaHi : ℝ) * (cotEnclX (zetaHi, zetaHi)).2 < 1 := by exact_mod_cast h6
  have hc : 0 < cot (zetaHi : ℝ) := lt_of_lt_of_le h5' hl
  simp only [tanExF, tan_eq_inv_cot]
  rw [sub_neg, lt_inv_comm₀ (by norm_num [zetaHi]) hc]
  rw [inv_eq_one_div, lt_div_iff₀ (by norm_num [zetaHi])]
  nlinarith

/-- **DLMF §3.8(ii), Example**: "The first positive zero of `f(x)` lies in the interval
`(π, 3π/2)`": it is the unique zero `ζ` of `x − tan x` there, `ζ = 4.49340 94579 091` to 13
decimals, and `x − tan x` has no zero in `(0, ζ)`. -/
theorem dlmf_3_8_ii_example_zero : ∃ ζ : ℝ, ζ ∈ Ioo (zetaLo : ℝ) zetaHi ∧ tanExF ζ = 0 ∧
    ζ ∈ Ioo π (3 * π / 2) ∧ (∀ x ∈ Ioo π (3 * π / 2), tanExF x = 0 → x = ζ) ∧
    ∀ x ∈ Ioo 0 ζ, tanExF x ≠ 0 := by
  have hab : (zetaLo : ℝ) ≤ zetaHi := by norm_num [zetaLo, zetaHi]
  have hsub : Icc (zetaLo : ℝ) zetaHi ⊆ Ioo π (3 * π / 2) := fun y hy =>
    mem_Ioo_of_tab (le_trans (by norm_num [zetaLo]) hy.1) (le_trans hy.2 (by norm_num [zetaHi]))
  have hcont : ContinuousOn tanExF (Icc (zetaLo : ℝ) zetaHi) := fun y hy =>
    (hasDerivAt_exF (cos_neg_of_mem (hsub hy)).ne).continuousAt.continuousWithinAt
  obtain ⟨ζ, hζ, hz⟩ := intermediate_value_Icc' hab hcont ⟨exF_zetaHi_neg.le, exF_zetaLo_pos.le⟩
  have hζI := hsub hζ
  have hlo : (zetaLo : ℝ) < ζ := lt_of_le_of_ne hζ.1 (fun h => by
    rw [← h] at hz; linarith [exF_zetaLo_pos])
  have hhi : ζ < zetaHi := lt_of_le_of_ne hζ.2 (fun h => by
    rw [h] at hz; linarith [exF_zetaHi_neg])
  refine ⟨ζ, ⟨hlo, hhi⟩, hz, hζI, fun x hx hx0 => exF_strictAntiOn.injOn hx hζI (hx0.trans hz.symm),
    fun x hx => ?_⟩
  rcases le_or_gt x π with h | h
  · exact exF_ne_zero_of_mem_Ioc ⟨hx.1, h⟩
  · have hxI : x ∈ Ioo π (3 * π / 2) := ⟨h, hx.2.trans hζI.2⟩
    have := exF_strictAntiOn hxI hζI hx.2
    rw [hz] at this
    exact this.ne'

/-! ### Table 3.8.1 -/

/-- **DLMF Table 3.8.1**: Newton's rule for `x − tan x` from `x₀ = 4.65` is the iteration of `φ`
(3.8.5), and converges (monotonically, quadratically) to `ζ`. The printed `x₀`, `x₆`, `x₇`, `x₈`
are the correctly rounded values of the iterates. **Erratum**: the printed `x₁, …, x₅` are not;
the correct roundings are `4.60567 66065 899`, `4.55140 53475 750`, `4.50903 76975 615`,
`4.49455 61600 187`, `4.49341 56569 392` (`tab381c`). -/
theorem dlmf_table_3_8_1 : ∃ ζ : ℝ, tanExF ζ = 0 ∧ ζ ∈ Ioo π (3 * π / 2) ∧
    (∀ n, (newtonStep tanExF)^[n] (465 / 100) = exPhi^[n] (465 / 100)) ∧
    Tendsto (fun n => (newtonStep tanExF)^[n] (465 / 100)) atTop (𝓝 ζ) ∧
    (∀ n ∈ ({0, 6, 7, 8} : Finset ℕ), |exPhi^[n] (465 / 100) - tab381 n| < halfUlp) ∧
    (∀ n ∈ Finset.Icc 1 5, halfUlp < |exPhi^[n] (465 / 100) - tab381 n| ∧
      |exPhi^[n] (465 / 100) - tab381c n| < halfUlp) := by
  obtain ⟨ζ, hζb, hz, hζI, -, -⟩ := dlmf_3_8_ii_example_zero
  have hx0 : (465 / 100 : ℝ) ∈ Ioo ζ (3 * π / 2) :=
    ⟨lt_trans hζb.2 (by norm_num [zetaHi]), by linarith [three_pi_div_two_gt]⟩
  obtain ⟨heq, -, -, hlim, -⟩ := exF_newton_converges hζI hz hx0
  have hc : ∀ n ≤ 8, |exPhi^[n] (465 / 100) - tab381c n| < halfUlp := fun n hn => by
    obtain ⟨h1, h2⟩ := tabEncl_sound n hn
    obtain ⟨c1, c2⟩ := tab_correct_check n hn
    have c1' : ((tab381c n - halfUlp : ℚ) : ℝ) < (tabEncl n).1 := by exact_mod_cast c1
    have c2' : ((tabEncl n).2 : ℝ) < ((tab381c n + halfUlp : ℚ) : ℝ) := by exact_mod_cast c2
    push_cast at c1' c2'
    rw [abs_lt]; constructor <;> linarith
  refine ⟨ζ, hz, hζI, heq, hlim, fun n hn => ?_, fun n hn => ?_⟩
  · have hn' : n ≤ 8 := by simp at hn; omega
    have := hc n hn'
    have e : tab381 n = tab381c n := by simp at hn; rcases hn with rfl | rfl | rfl | rfl <;> rfl
    rwa [e]
  · have hn' := Finset.mem_Icc.mp hn
    refine ⟨?_, hc n (by omega)⟩
    obtain ⟨h1, h2⟩ := tabEncl_sound n (by omega)
    rcases tab_wrong_check n hn with w | w
    · have w' : ((tabEncl n).2 : ℝ) < ((tab381 n - halfUlp : ℚ) : ℝ) := by exact_mod_cast w
      push_cast at w'
      rw [lt_abs]; right; linarith
    · have w' : ((tab381 n + halfUlp : ℚ) : ℝ) < (tabEncl n).1 := by exact_mod_cast w
      push_cast at w'
      rw [lt_abs]; left; linarith

/-! ### "When `x₀ ≤ 4.2875` … Newton's rule does not converge to the required zero" -/

/-- An enclosure of `cot(π − 2.25)`. -/
def cot225 : ℚ × ℚ := (cotLo (rdUp 90 (piHiQ - 9 / 4)), cotHi (rdDown 90 (piLoQ - 9 / 4)))

theorem cot225_checks : CotOk (rdUp 90 (piHiQ - 9 / 4)) ∧ CotOk (rdDown 90 (piLoQ - 9 / 4)) ∧
    0 < rdDown 90 (piLoQ - 9 / 4) ∧ rdUp 90 (piHiQ - 9 / 4) ≤ 157 / 100 ∧ 0 < cot225.1 ∧
    zetaHi < 9 / 4 + 9 / 4 * cot225.1 ^ 2 + cot225.1 ∧
    9 / 4 + 9 / 4 * cot225.2 ^ 2 + cot225.2 < 47 / 10 := by
  decide +kernel

/-- **DLMF §3.8(ii), Example, erratum**: "When `x₀ ≤ 4.2875` or `x₀ ≥ 4.7125`, Newton's rule
does not converge to the required zero" fails for `x₀ = 2.25`: the first step lands in
`(ζ, 3π/2)`, from where the iteration converges monotonically to `ζ`. -/
theorem dlmf_3_8_ii_example_erratum : (9 / 4 : ℝ) ≤ 4.2875 ∧ ∃ ζ : ℝ, tanExF ζ = 0 ∧
    ζ ∈ Ioo π (3 * π / 2) ∧ Tendsto (fun n => (newtonStep tanExF)^[n] (9 / 4)) atTop (𝓝 ζ) := by
  refine ⟨by norm_num, ?_⟩
  obtain ⟨ζ, hζb, hz, hζI, -, -⟩ := dlmf_3_8_ii_example_zero
  obtain ⟨hu, hl, hl0, hu1, hc0, hlow, hhigh⟩ := cot225_checks
  -- `cot 2.25 = −cot(π − 2.25)`
  set u : ℝ := π - 9 / 4 with hu_def
  have hul : ((rdDown 90 (piLoQ - 9 / 4) : ℚ) : ℝ) ≤ u := by
    have := rdDown_le 90 (piLoQ - 9 / 4)
    have h' : ((piLoQ - 9 / 4 : ℚ) : ℝ) ≤ u := by push_cast; linarith [piLoQ_lt, hu_def]
    exact le_trans (by exact_mod_cast this) h'
  have huu : u ≤ ((rdUp 90 (piHiQ - 9 / 4) : ℚ) : ℝ) := by
    have := le_rdUp 90 (piHiQ - 9 / 4)
    have h' : u ≤ ((piHiQ - 9 / 4 : ℚ) : ℝ) := by push_cast; linarith [pi_lt_piHiQ, hu_def]
    exact le_trans h' (by exact_mod_cast this)
  have hl0' : (0 : ℝ) < rdDown 90 (piLoQ - 9 / 4) := by exact_mod_cast hl0
  have hu1q : ((rdUp 90 (piHiQ - 9 / 4) : ℚ) : ℝ) ≤ ((157 / 100 : ℚ) : ℝ) := by exact_mod_cast hu1
  push_cast at hu1q
  have hpi2 : (157 / 100 : ℝ) < π / 2 := by linarith [Real.pi_gt_d2]
  have hcl : (cot225.1 : ℝ) ≤ cot u :=
    (cot_mem hu).1.trans (cot_antitone (by linarith) huu (by linarith))
  have hcu : cot u ≤ cot225.2 := (cot_antitone hl0' hul (by linarith)).trans (cot_mem hl).2
  have hcot : cot (9 / 4 : ℝ) = -cot u := by
    simp only [u, cot_eq_cos_div_sin, cos_pi_sub, sin_pi_sub, neg_div, neg_neg]
  have hc0' : (0 : ℝ) < cot225.1 := by exact_mod_cast hc0
  have hcu0 : 0 < cot u := lt_of_lt_of_le hc0' hcl
  have hx1 : exPhi (9 / 4) = 9 / 4 + 9 / 4 * cot u ^ 2 + cot u := by
    simp only [exPhi, hcot]; ring
  have hlow' : ((zetaHi : ℚ) : ℝ) < ((9 / 4 + 9 / 4 * cot225.1 ^ 2 + cot225.1 : ℚ) : ℝ) := by
    exact_mod_cast hlow
  have hhigh' : ((9 / 4 + 9 / 4 * cot225.2 ^ 2 + cot225.2 : ℚ) : ℝ) < ((47 / 10 : ℚ) : ℝ) := by
    exact_mod_cast hhigh
  push_cast at hlow' hhigh'
  have hmem : exPhi (9 / 4) ∈ Ioo ζ (3 * π / 2) := by
    rw [hx1]
    constructor
    · have : (cot225.1 : ℝ) ^ 2 ≤ cot u ^ 2 := pow_le_pow_left₀ hc0'.le hcl 2
      linarith [hζb.2]
    · have : cot u ^ 2 ≤ (cot225.2 : ℝ) ^ 2 := pow_le_pow_left₀ hcu0.le hcu 2
      linarith [three_pi_div_two_gt]
  -- the first step is `φ`
  have hstep : newtonStep tanExF (9 / 4) = exPhi (9 / 4) := by
    have h1 : π / 2 < (9 / 4 : ℝ) := by linarith [Real.pi_lt_d2]
    have h2 : (9 / 4 : ℝ) < π := by linarith [Real.pi_gt_d2]
    exact dlmf_3_8_5 (cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [pi_pos])).ne
      (sin_pos_of_pos_of_lt_pi (by norm_num) h2).ne'
  obtain ⟨-, -, -, hlim, -⟩ := exF_newton_converges hζI hz hmem
  refine ⟨ζ, hz, hζI, ?_⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hlim.congr fun n => ?_
  rw [Function.iterate_succ_apply, hstep]

/-! ### `f(x) = x cos x − sin x` -/

/-- The alternative function `x cos x − sin x = cos x · (x − tan x)`. -/
noncomputable def exG (x : ℝ) : ℝ := x * cos x - sin x

theorem exG_eq {x : ℝ} (hc : cos x ≠ 0) : exG x = cos x * tanExF x := by
  simp only [exG, tanExF, tan_eq_sin_div_cos]
  field_simp

/-- Newton's rule for `x cos x − sin x`: `x ↦ x + cot x − 1/x`. -/
theorem newtonStep_exG {x : ℝ} (hx : x ≠ 0) (hs : sin x ≠ 0) :
    newtonStep exG x = x + cot x - 1 / x := by
  have hd : HasDerivAt exG (-(x * sin x)) x := by
    have := ((hasDerivAt_id x).mul (hasDerivAt_cos x)).sub (hasDerivAt_sin x)
    exact this.congr_deriv (by simp)
  simp only [newtonStep, hd.deriv, exG, cot_eq_cos_div_sin]
  field_simp
  ring

end Azurite.DLMF
