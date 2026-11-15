/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanBracket
import Azurite.AzFloat.Equiv.SinCosBracket
import Azurite.AzFloat.Equiv.TanBracket

/-!
# Equivalence: the bracket of `arctan x`

* Real analysis: `sub_cube_div_three_le_arctan` (`x − x³/3 ≤ arctan x`),
  `arctan_le_sub_cube_add_fifth` (`arctan x ≤ x − x³/3 + x⁵/5`),
  `arctan_sub_arctan_le` (`arctan` is `1`-Lipschitz), `tan_le_five_fourths_mul`,
  `arctan_sub_eq_arctan_div` (`arctan t − y = arctan ((t cos y − sin y)/(cos y + t sin y))`),
  `irrational_arctan_rat`, `irrational_arctan_of_toVal`.
* `IsEncl0W.div_pos`: the quotient of enclosures with a width bound.
* `atanBase_spec`, `atanStepAt_spec` (the step from any `y ≤ arctan t`, known or certified by
  the flag), `atanStep_spec`, `atanSeeded?_spec` (the step from the unverified seed, accepted
  only when certified), `atanLoop_spec` (width at most `(3/4) 2^(−K)` with fuel
  `≥ K − 1`), `atanBracket_spec` (width at most `2^(−w)`), `atanApprox_spec`,
  `atanApprox_isSome_exists` (the Ziv certificate), `atanTiny?_eq`.
-/

open Real

namespace Azurite.AzFloat

/-! ### Real analysis -/

/-- `x − x³/3 ≤ arctan x` for `x ≥ 0`. -/
theorem sub_cube_div_three_le_arctan {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ arctan x := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => arctan y - y + y ^ 3 / 3)
      (1 / (1 + y ^ 2) - 1 + 3 * y ^ 2 / 3) y := fun y => by
    have h := ((hasDerivAt_arctan y).sub (hasDerivAt_id y)).add
      ((hasDerivAt_pow 3 y).div_const 3)
    exact h.congr_deriv (by simp)
  have hmono : Monotone (fun y : ℝ => arctan y - y + y ^ 3 / 3) := by
    refine monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt) fun y => ?_
    rw [(hd y).deriv]
    have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
    have h2 : 1 / (1 + y ^ 2) - 1 + 3 * y ^ 2 / 3 = y ^ 4 / (1 + y ^ 2) := by
      field_simp
      ring
    rw [h2]
    positivity
  have h := hmono hx
  simp only [arctan_zero] at h
  norm_num at h
  linarith

/-- `arctan x ≤ x − x³/3 + x⁵/5` for `x ≥ 0`. -/
theorem arctan_le_sub_cube_add_fifth {x : ℝ} (hx : 0 ≤ x) :
    arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => y - y ^ 3 / 3 + y ^ 5 / 5 - arctan y)
      (1 - 3 * y ^ 2 / 3 + 5 * y ^ 4 / 5 - 1 / (1 + y ^ 2)) y := fun y => by
    have h := (((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 3)).add
      ((hasDerivAt_pow 5 y).div_const 5)).sub (hasDerivAt_arctan y)
    exact h.congr_deriv (by simp)
  have hmono : Monotone (fun y : ℝ => y - y ^ 3 / 3 + y ^ 5 / 5 - arctan y) := by
    refine monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt) fun y => ?_
    rw [(hd y).deriv]
    have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
    have h2 : 1 - 3 * y ^ 2 / 3 + 5 * y ^ 4 / 5 - 1 / (1 + y ^ 2) = y ^ 6 / (1 + y ^ 2) := by
      field_simp
      ring
    rw [h2]
    positivity
  have h := hmono hx
  simp only [arctan_zero] at h
  norm_num at h
  linarith

/-- `arctan` is `1`-Lipschitz: `arctan b − arctan a ≤ b − a` for `a ≤ b`. -/
theorem arctan_sub_arctan_le {a b : ℝ} (hab : a ≤ b) : arctan b - arctan a ≤ b - a := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y => y - arctan y) (1 - 1 / (1 + y ^ 2)) y := fun y =>
    (hasDerivAt_id y).sub (hasDerivAt_arctan y)
  have hmono : Monotone (fun y : ℝ => y - arctan y) := by
    refine monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt) fun y => ?_
    rw [(hd y).deriv]
    have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
    have h2 : 1 / (1 + y ^ 2) ≤ 1 := by
      rw [div_le_one h1]
      nlinarith [sq_nonneg y]
    linarith
  have h := hmono hab
  simp only at h
  linarith

/-- `tan x ≤ (5/4) x` for `0 ≤ x ≤ 7/16`. -/
theorem tan_le_five_fourths_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 7 / 16) :
    tan x ≤ 5 / 4 * x := by
  have hc : 4 / 5 ≤ cos x := by
    have := one_sub_sq_div_two_le_cos (x := x)
    nlinarith
  rw [tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
  have hs := sin_le hx0
  nlinarith

/-- The addition formula behind the iteration: `arctan t − y = arctan δ` with
`δ = (t cos y − sin y) / (cos y + t sin y)`, when `|arctan t − y| < π/2`. -/
theorem arctan_sub_eq_arctan_div {t y : ℝ} (h1 : -(π / 2) < arctan t - y)
    (h2 : arctan t - y < π / 2) :
    arctan t - y = arctan ((t * cos y - sin y) / (cos y + t * sin y)) := by
  have hc := cos_arctan_pos t
  have hcd : 0 < cos (arctan t - y) := cos_pos_of_mem_Ioo ⟨h1, h2⟩
  have ht : t * cos (arctan t) = sin (arctan t) := by
    have h := tan_arctan t
    rw [tan_eq_sin_div_cos, div_eq_iff hc.ne'] at h
    exact h.symm
  have hq : (t * cos y - sin y) / (cos y + t * sin y) = tan (arctan t - y) := by
    rw [tan_eq_sin_div_cos, sin_sub, cos_sub]
    rw [cos_sub] at hcd
    have hden : cos y + t * sin y =
        (cos (arctan t) * cos y + sin (arctan t) * sin y) / cos (arctan t) := by
      rw [eq_div_iff hc.ne']
      linear_combination sin y * ht
    have hnum : t * cos y - sin y =
        (sin (arctan t) * cos y - cos (arctan t) * sin y) / cos (arctan t) := by
      rw [eq_div_iff hc.ne']
      linear_combination cos y * ht
    rw [hden, hnum, div_div_div_cancel_right₀ hc.ne']
  rw [hq, arctan_tan h1 h2]

/-- `arctan q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_arctan_rat {q : ℚ} (hq : q ≠ 0) : Irrational (arctan q) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero] at hr
    exact hq (by exact_mod_cast arctan_eq_zero_iff.mp hr.symm)
  apply irrational_tan_rat hr0
  rw [hr, tan_arctan]
  exact ⟨q, rfl⟩

/-- `arctan x` is irrational for a nonzero finite float `x`. -/
theorem irrational_arctan_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (arctan xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [hq, Rat.cast_zero]
  rw [hq]
  exact irrational_arctan_rat hq0

/-- `arctan x = ± arctan |x|` with the sign bit of `x`. -/
theorem arctan_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    arctan xv = (if neg then -1 else 1) * arctan |xv| := by
  cases neg with
  | false =>
    have : ¬ xv < 0 := fun h => by simpa using hneg.mpr h
    simp [abs_of_nonneg (not_lt.mp this)]
  | true =>
    have h := hneg.mp rfl
    rw [abs_of_neg h, arctan_neg]
    simp

/-! ### The quotient of enclosures -/

/-- The quotient of a nonnegative enclosure of `x ≤ 2` by an enclosure of `y ≥ 1/2` of width at
most `1/4`. -/
theorem IsEncl0W.div_pos {a b : Encl} {x y δ ε : ℝ} (ha : IsEncl0W a x δ) (hb : IsEnclW b y ε)
    (hx : x ≤ 2) (hy : 1 / 2 ≤ y) (hδ : δ ≤ 1) (hε : ε ≤ 1 / 4) {W : ℕ} (hW : 64 ≤ W) :
    IsEncl0W (Encl.div W a b) (x / y) (4 * δ + 16 * ε + 64 * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨la, ha', hla, hha, ha0, ha1, ha2, ha3⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, hb1, hb2, hb3⟩ := hb
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hδ0 : 0 ≤ δ := by linarith
  have hε0 : 0 ≤ ε := by linarith
  have hlb0 : 1 / 4 ≤ lb := by linarith
  have hhb0 : 1 / 2 ≤ hb' := by linarith
  have hx0 : 0 ≤ x := ha0.trans ha1
  obtain ⟨lo, hlo, hlof⟩ := divFloor_err hla hhb (by linarith) ha0 W
  obtain ⟨hi, hhi, hhic⟩ := divCeiling_err hha hlb (by linarith) (by linarith) W
  have h1 := hlof.ge
  have h2 := hhic.le
  rw [← hu] at h1 h2
  set q := la / hb' with hq
  have hq0 : 0 ≤ q := div_nonneg ha0 (by linarith)
  have hq4 : q ≤ 4 := by
    rw [hq, div_le_iff₀ (by linarith)]
    linarith
  have hqm : q * hb' = la := div_mul_cancel₀ la (by linarith)
  have hQ : ha' / lb ≤ q + 4 * δ + 16 * ε := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hlb0), mul_nonneg hε0 (sub_nonneg.mpr hlb0),
      mul_nonneg hq0 (sub_nonneg.mpr hb3), mul_nonneg (sub_nonneg.mpr hq4) hε0]
  have hQ12 : ha' / lb ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  refine ⟨lo, hi, hlo, hhi, hlof.nonneg,
    hlof.le.trans (div_le_div₀ hx0 ha1 (by linarith) hb2),
    (div_le_div₀ (by linarith) ha2 (by linarith) hb1).trans hhic.ge, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hQ12 hu0, mul_le_mul_of_nonneg_right hq4 hu0]

/-! ### The base and the step -/

/-- The base enclosure `[t − t³/3, t]`: width at most `3/8`. -/
theorem atanBase_spec {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (ht0 : 0 ≤ tv)
    (ht1 : tv ≤ 1) {V : ℕ} (hV : 64 ≤ V) :
    ∃ lo hi : ℝ, (atanBase t V).1.toVal = some (lo : EReal) ∧
      (atanBase t V).2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ arctan tv ∧ arctan tv ≤ hi ∧
      hi - lo ≤ 3 / 8 := by
  have : NeZero V := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ V with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 1024 := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (by omega : 10 ≤ V)
    rw [← hu] at h
    norm_num at h
    linarith
  obtain ⟨c1, hc1, hc1c⟩ := mulCeiling_err ht ht V (mul_nonneg ht0 ht0)
  have hc10 : 0 ≤ c1 := (mul_nonneg ht0 ht0).trans hc1c.ge
  obtain ⟨c2, hc2, hc2c⟩ := mulCeiling_err hc1 ht V (mul_nonneg hc10 ht0)
  have hc20 : 0 ≤ c2 := (mul_nonneg hc10 ht0).trans hc2c.ge
  obtain ⟨th, hth, hthc⟩ := divCeiling_err hc2 (toVal_ofAzNat_ofNat 3) (by norm_num) hc20 V
  obtain ⟨r, hr, hr1, hr2⟩ := subFloor_abs ht hth V
  obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hr
  have h1 := hc1c.ge
  have h1' := hc1c.le
  have h2 := hc2c.ge
  have h2' := hc2c.le
  have h3 := hthc.ge
  have h3' := hthc.le
  rw [← hu] at h1' h2' h3'
  push_cast at h3 h3'
  have htt : tv * tv ≤ 1 := by nlinarith
  have hc1u : c1 ≤ 1003 / 1000 := by nlinarith
  have hc2u : c2 ≤ 1007 / 1000 := by
    have : c1 * tv ≤ 1003 / 1000 := by nlinarith
    nlinarith
  have hthu : th ≤ 337 / 1000 := by
    have : c2 / 3 ≤ 1007 / 3000 := by linarith
    nlinarith
  have hcube : tv ^ 3 / 3 ≤ th := by
    have : tv ^ 3 ≤ c2 := by
      have : tv * tv * tv ≤ c1 * tv := mul_le_mul_of_nonneg_right h1 ht0
      nlinarith
    linarith
  have hth0 : 0 ≤ th := le_trans (by positivity) hcube
  have hat := sub_cube_div_three_le_arctan ht0
  have hat0 : 0 ≤ arctan tv := arctan_nonneg.mpr ht0
  have habs : |tv - th| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrc : r ≤ cv := by
    rcases le_or_gt 0 r with h | h
    · rw [hcveq h]
    · linarith
  refine ⟨cv, tv, hcv, ht, hcv0, hcvle.trans (max_le (by linarith) hat0),
    arctan_le_self ht0, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right habs hu0]

/-- The working precision of a step dominates its level: with `V = K + lg K + 64` and
`T ≤ K + 3` fraction bits, `296 T 2^(−V) ≤ 2^(−K−40)/8192` and `2^(−V) ≤ 2^(−K−40)/2^24`. -/
theorem atanStep_prec {T K : ℕ} (hT : T ≤ K + 3) :
    296 * (T : ℝ) * (1 / 2 : ℝ) ^ (K + (AzNat.ofNat K).size + 64) ≤
        (1 / 2 : ℝ) ^ (K + 40) / 8192 ∧
      (1 / 2 : ℝ) ^ (K + (AzNat.ofNat K).size + 64) ≤ (1 / 2 : ℝ) ^ (K + 40) / 16777216 := by
  rw [AzNat.size_ofNat]
  set s := K.size with hs
  have hK : (K : ℝ) < 2 ^ s := by exact_mod_cast Nat.lt_size_self K
  have h2s : (2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  have h2s1 : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have hs1 : (1 / 2 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs0 : (0 : ℝ) < (1 / 2 : ℝ) ^ s := by positivity
  set a := (1 / 2 : ℝ) ^ K with ha
  have ha0 : 0 < a := by positivity
  have e64 : (1 / 2 : ℝ) ^ 64 = 1 / 18446744073709551616 := by norm_num
  have e40 : (1 / 2 : ℝ) ^ 40 = 1 / 1099511627776 := by norm_num
  have hT' : (T : ℝ) ≤ 4 * 2 ^ s := by
    have : (T : ℝ) ≤ K + 3 := by exact_mod_cast hT
    linarith
  rw [pow_add, pow_add, pow_add, ← ha, e64, e40]
  constructor
  · have h1 : (T : ℝ) * (1 / 2 : ℝ) ^ s ≤ 4 := by
      calc (T : ℝ) * (1 / 2 : ℝ) ^ s ≤ 4 * 2 ^ s * (1 / 2 : ℝ) ^ s :=
            mul_le_mul_of_nonneg_right hT' hs0.le
        _ = 4 := by rw [mul_assoc, h2s, mul_one]
    have h2 : 296 * (T : ℝ) * (a * (1 / 2 : ℝ) ^ s * (1 / 18446744073709551616)) =
        296 * a * (1 / 18446744073709551616) * ((T : ℝ) * (1 / 2 : ℝ) ^ s) := by ring
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha0.le]
  · nlinarith [mul_le_mul_of_nonneg_left hs1 ha0.le]

/-- The enclosure of the numerator `t cos y − sin y` of the step, before the clamp. -/
theorem atanStep_num {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (ht0 : 0 ≤ tv)
    (ht1 : tv ≤ 1) {sc : Encl × Encl} {yv η ν : ℝ} {V : ℕ} (hV64 : 64 ≤ V)
    (hη0 : 0 ≤ η) (hη : η ≤ ν / 8192) (hu : (1 / 2 : ℝ) ^ V ≤ ν / 16777216) (hν1 : ν ≤ 1 / 1024)
    (hs : IsEncl0W sc.1 (sin yv) η) (hc : IsEncl0W sc.2 (cos yv) η) (hcy : 1 / 2 ≤ cos yv) :
    IsEnclW (Encl.sub V (Encl.mul V (Encl.exact t) sc.2) sc.1) (tv * cos yv - sin yv)
      (ν / 512) := by
  set u := (1 / 2 : ℝ) ^ V with hu'
  have hu0 : 0 ≤ u := by positivity
  have hν0 : 0 ≤ ν := by linarith
  have hsy1 : sin yv ≤ 1 := sin_le_one _
  have hcy1 : cos yv ≤ 1 := cos_le_one _
  have htc : tv * cos yv ≤ 1 := by nlinarith
  have hte := isEncl0W_exact ht ht0
  have hmc := (IsEncl0W.mul hte hc ht1 hcy1 (by norm_num) (by linarith) hV64).mono
    (by rw [← hu']; linarith : _ ≤ ν / 1024)
  exact (IsEnclW.sub0 hmc.toW hs (M := 1)
    (by rw [abs_of_nonneg (mul_nonneg ht0 (by linarith))]; exact htc) hsy1 (by linarith)
    (by linarith) hV64).mono (by rw [← hu']; linarith : _ ≤ ν / 512)

/-- The interval part of the step: from enclosures of `sin y` and `cos y` of width `η` to
enclosure of `δ = (t cos y − sin y)/(cos y + t sin y)`. -/
theorem atanStep_encl {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (ht0 : 0 ≤ tv)
    (ht1 : tv ≤ 1) {sc : Encl × Encl} {yv η ν : ℝ} {V : ℕ} (hV64 : 64 ≤ V)
    (hη0 : 0 ≤ η) (hη : η ≤ ν / 8192) (hu : (1 / 2 : ℝ) ^ V ≤ ν / 16777216) (hν1 : ν ≤ 1 / 1024)
    (hs : IsEncl0W sc.1 (sin yv) η) (hc : IsEncl0W sc.2 (cos yv) η) (hsy0 : 0 ≤ sin yv)
    (hcy : 1 / 2 ≤ cos yv) (hN0 : 0 ≤ tv * cos yv - sin yv) :
    IsEncl0W (Encl.div V (enclClamp0 (Encl.sub V (Encl.mul V (Encl.exact t) sc.2) sc.1))
        (Encl.add V sc.2 (Encl.mul V (Encl.exact t) sc.1)))
      ((tv * cos yv - sin yv) / (cos yv + tv * sin yv)) (ν / 16) := by
  set u := (1 / 2 : ℝ) ^ V with hu'
  have hu0 : 0 ≤ u := by positivity
  have hν0 : 0 ≤ ν := by linarith
  have hsy1 : sin yv ≤ 1 := sin_le_one _
  have hcy1 : cos yv ≤ 1 := cos_le_one _
  have htc : tv * cos yv ≤ 1 := by nlinarith
  have hts0 : 0 ≤ tv * sin yv := mul_nonneg ht0 hsy0
  have hts : tv * sin yv ≤ 1 := by nlinarith
  have hte := isEncl0W_exact ht ht0
  have hmc := (IsEncl0W.mul hte hc ht1 hcy1 (by norm_num) (by linarith) hV64).mono
    (by rw [← hu']; linarith : _ ≤ ν / 1024)
  have hnum := enclClamp0_spec ((IsEnclW.sub0 hmc.toW hs (M := 1)
    (by rw [abs_of_nonneg (mul_nonneg ht0 (by linarith))]; exact htc) hsy1 (by linarith)
    (by linarith) hV64).mono (by rw [← hu']; linarith : _ ≤ ν / 512)) hN0
  have hms := (IsEncl0W.mul hte hs ht1 hsy1 (by norm_num) (by linarith) hV64).mono
    (by rw [← hu']; linarith : _ ≤ ν / 1024)
  have hden := (IsEnclW.add0 hc.toW hms (M := 1)
    (by rw [abs_of_nonneg (by linarith)]; exact hcy1) hts (by linarith) (by linarith)
    hV64).mono (by rw [← hu']; linarith : _ ≤ ν / 512)
  exact (IsEncl0W.div_pos hnum hden (by linarith) (by linarith) (by linarith) (by linarith)
    hV64).mono (by rw [← hu']; linarith)

/-- The cube over three and the fifth power over five of a nonnegative enclosure of `δ ≤ 1` of
width at most `ν/16`. -/
theorem atanStep_cube {d : Encl} {δ ν : ℝ} {V : ℕ} (hV64 : 64 ≤ V)
    (hu : (1 / 2 : ℝ) ^ V ≤ ν / 16777216) (hν1 : ν ≤ 1 / 1024) (hd : IsEncl0W d δ (ν / 16))
    (hδ1 : δ ≤ 1) :
    IsEncl0W (Encl.div V (Encl.mul V (Encl.mul V d d) d) (Encl.nat 3)) (δ * δ * δ / 3)
        (ν / 4) ∧
      IsEncl0W (Encl.div V (Encl.mul V (Encl.mul V (Encl.mul V d d) d) (Encl.mul V d d))
        (Encl.nat 5)) (δ * δ * δ * (δ * δ) / 5) (ν / 4) := by
  set u := (1 / 2 : ℝ) ^ V with hu'
  have hu0 : 0 ≤ u := by positivity
  have hν0 : 0 ≤ ν := by linarith
  have hδ0 : 0 ≤ δ := hd.nonneg
  have hνν : ν * ν ≤ ν := by nlinarith
  have hdd := (IsEncl0W.mul hd hd hδ1 hδ1 (by linarith) (by linarith) hV64).mono
    (by rw [← hu']; nlinarith : _ ≤ ν / 4)
  have hδδ : δ * δ ≤ 1 := by nlinarith
  have hddd := (IsEncl0W.mul hdd hd hδδ hδ1 (by linarith) (by linarith) hV64).mono
    (by rw [← hu']; nlinarith : _ ≤ ν / 2)
  have hδ3 : δ * δ * δ ≤ 1 := by nlinarith
  have hd5 := (IsEncl0W.mul hddd hdd hδ3 hδδ (by linarith) (by linarith) hV64).mono
    (by rw [← hu']; nlinarith : _ ≤ ν)
  have hδ5 : δ * δ * δ * (δ * δ) ≤ 1 := by nlinarith [mul_nonneg hδ0 hδ0]
  have hth := (IsEncl0W.div_nat hddd (n := 3) (by norm_num) hδ3 (by linarith)
    hV64).mono (by rw [← hu']; push_cast; linarith : _ ≤ ν / 4)
  have hfi := (IsEncl0W.div_nat hd5 (n := 5) (by norm_num) hδ5 (by linarith)
    hV64).mono (by rw [← hu']; push_cast; linarith : _ ≤ ν / 4)
  push_cast at hth hfi
  exact ⟨hth, hfi⟩

/-- The assembly of the step: `[y + δ_lo − (δ³/3)_hi, y + δ_hi − (δ³/3)_lo + (δ⁵/5)_hi]`,
clamped at `0`, encloses `θ = y + arctan δ` with width at most `δ⁵/5 + ν`. -/
theorem atanStep_assemble {y : AzFloat} {d third fifth : Encl} {yv δ θ ν : ℝ} {V : ℕ}
    (hV64 : 64 ≤ V)
    (hu : (1 / 2 : ℝ) ^ V ≤ ν / 16777216) (hν1 : ν ≤ 1 / 1024)
    (hy : y.toVal = some (yv : EReal)) (hyv0 : 0 ≤ yv) (hyv1 : yv ≤ 1)
    (hd : IsEncl0W d δ (ν / 16)) (hth : IsEncl0W third (δ * δ * δ / 3) (ν / 4))
    (hfi : IsEncl0W fifth (δ * δ * δ * (δ * δ) / 5) (ν / 4)) (hδ1 : δ ≤ 1)
    (hθ : θ = yv + arctan δ) :
    ∃ lo hi : ℝ,
      (clampNonneg (addPrecRound y (subPrecRound d.1 third.2 V .Floor).1 V .Floor).1).toVal =
        some (lo : EReal) ∧
      (addPrecRound y (addPrecRound (subPrecRound d.2 third.1 V .Ceiling).1 fifth.2 V
        .Ceiling).1 V .Ceiling).1.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ θ ∧ θ ≤ hi ∧
      hi - lo ≤ δ ^ 5 / 5 + ν := by
  have : NeZero V := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ V with hu'
  have hu0 : 0 ≤ u := by positivity
  have hν0 : 0 ≤ ν := by linarith
  have hδ0 : 0 ≤ δ := hd.nonneg
  obtain ⟨dl, dh, hdl, hdh, hdl0, hdl1, hdh1, hdw⟩ := hd
  obtain ⟨tl, th, htl, hth', htl0, htl1, hth1, htw⟩ := hth
  obtain ⟨fl, fh, hfl, hfh, hfl0, hfl1, hfh1, hfw⟩ := hfi
  obtain ⟨r1, hr1, hr1le, hr1ge⟩ := subFloor_abs hdl hth' V
  obtain ⟨r2, hr2, hr2le, hr2ge⟩ := addFloor_abs hy hr1 V
  obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hr2
  obtain ⟨r3, hr3, hr3ge, hr3le⟩ := subCeiling_abs hdh htl V
  obtain ⟨r4, hr4, hr4ge, hr4le⟩ := addCeiling_abs hr3 hfh V
  obtain ⟨r5, hr5, hr5ge, hr5le⟩ := addCeiling_abs hy hr4 V
  rw [← hu'] at hr1ge hr2ge hr3le hr4le hr5le
  have hcube : δ ^ 3 / 3 = δ * δ * δ / 3 := by ring
  have hfifth : δ ^ 5 / 5 = δ * δ * δ * (δ * δ) / 5 := by ring
  have hlow := sub_cube_div_three_le_arctan hδ0
  have hup := arctan_le_sub_cube_add_fifth hδ0
  have hat0 : 0 ≤ arctan δ := arctan_nonneg.mpr hδ0
  have hδ2 : δ * δ ≤ 1 := by nlinarith
  have hδ3 : δ * δ * δ ≤ 1 := by nlinarith
  have hδ5 : δ * δ * δ * (δ * δ) ≤ 1 := by nlinarith [mul_nonneg hδ0 hδ0]
  have hδ30 : 0 ≤ δ * δ * δ := by positivity
  have hδ50 : 0 ≤ δ * δ * δ * (δ * δ) := by positivity
  have hu1 : u ≤ 1 / 16777216 := by linarith
  have hth3 : th ≤ 1 / 2 := by linarith
  have h1abs : |dl - th| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have m1 := mul_le_mul_of_nonneg_right h1abs hu0
  have hr1lo : -3 ≤ r1 := by linarith
  have h2abs : |yv + r1| ≤ 4 := by
    rw [abs_le]
    constructor <;> linarith
  have m2 := mul_le_mul_of_nonneg_right h2abs hu0
  have h3abs : |dh - tl| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have m3 := mul_le_mul_of_nonneg_right h3abs hu0
  have hr3hi : r3 ≤ 3 := by linarith
  have h4abs : |r3 + fh| ≤ 4 := by
    rw [abs_le]
    constructor <;> linarith
  have m4 := mul_le_mul_of_nonneg_right h4abs hu0
  have hr4hi : r4 ≤ 5 := by linarith
  have h5abs : |yv + r4| ≤ 6 := by
    rw [abs_le]
    constructor <;> linarith
  have m5 := mul_le_mul_of_nonneg_right h5abs hu0
  have hrc : r2 ≤ cv := by
    rcases le_or_gt 0 r2 with h | h
    · rw [hcveq h]
    · linarith
  rw [hcube, hfifth] at hup
  rw [hcube] at hlow
  refine ⟨cv, r5, hcv, hr5, hcv0, hcvle.trans (max_le (by linarith) (by linarith)),
    by linarith, ?_⟩
  rw [hfifth]
  linarith

/-- **The step from `y = M 2^(−T)`**: an enclosure of `arctan t` of width at most
`tan (arctan t − y)⁵/5 + 2^(−K−40)`, provided `y ≤ arctan t` — known beforehand, or certified
by the flag of the step. -/
theorem atanStepAt_spec {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (ht0 : 0 ≤ tv)
    (ht1 : tv ≤ 1) {M : AzNat} {T K : ℕ} (hT0 : 0 < T) (hTK : T ≤ K + 3)
    (hMlt : M.toNat < 2 ^ T)
    (hy : (M.toNat : ℝ) / 2 ^ T ≤ arctan tv ∨ (atanStepAt t M T K).1 = true) :
    ∃ lo hi : ℝ, (atanStepAt t M T K).2.1.toVal = some (lo : EReal) ∧
      (atanStepAt t M T K).2.2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ arctan tv ∧
      arctan tv ≤ hi ∧
      hi - lo ≤ tan (arctan tv - (M.toNat : ℝ) / 2 ^ T) ^ 5 / 5 + (1 / 2 : ℝ) ^ (K + 40) := by
  unfold atanStepAt at hy ⊢
  dsimp only at hy ⊢
  set V := K + (AzNat.ofNat K).size + 64 with hV
  have hV64 : 64 ≤ V := by omega
  set θ := arctan tv with hθ
  have hθ0 : 0 ≤ θ := arctan_nonneg.mpr ht0
  have hθ1 : θ ≤ π / 4 := by
    rw [← arctan_one]
    exact arctan_strictMono.monotone ht1
  have hπ := pi_lt_four
  have hπ3 := pi_gt_three
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  set yv := (M.toNat : ℝ) / 2 ^ T with hyv
  have hyv0 : 0 ≤ yv := by positivity
  have hy1' : yv ≤ 1 := by
    rw [hyv, div_le_one h2T]
    exact_mod_cast hMlt.le
  -- the precision
  obtain ⟨hη, hu⟩ := atanStep_prec (T := T) (K := K) hTK
  rw [← hV] at hη hu
  set ν := (1 / 2 : ℝ) ^ (K + 40) with hν
  have hν0 : 0 ≤ ν := by positivity
  have hν1 : ν ≤ 1 / 1024 := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (by omega : 10 ≤ K + 40)
    rw [← hν] at h
    norm_num at h
    linarith
  have hη0 : 0 ≤ 296 * (T : ℝ) * (1 / 2 : ℝ) ^ V := by positivity
  -- the sine and the cosine of `y`
  obtain ⟨hs, hc⟩ := sinCosFix_spec M hV64 hT0 hMlt (by linarith)
  rw [← hyv] at hs hc
  have hsy0 : 0 ≤ sin yv := sin_nonneg_of_nonneg_of_le_pi hyv0 (by linarith)
  have hcy : 1 / 2 ≤ cos yv := by
    have := one_sub_sq_div_two_le_cos (x := yv)
    nlinarith
  -- `y ≤ θ`
  have hyθ : yv ≤ θ := by
    rcases hy with h | h
    · exact h
    · obtain ⟨rl, rh, hrl, -, hrl1, -, -⟩ :=
        atanStep_num ht ht0 ht1 hV64 hη0 hη hu hν1 hs hc hcy
      simp only [Bool.not_eq_true'] at h
      have h0 := (toVal_sign_of_isNegative hrl).2 h
      have htan : tan yv ≤ tv := by
        rw [tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
        linarith
      have hmono := arctan_strictMono.monotone htan
      rwa [arctan_tan (by linarith) (by linarith)] at hmono
  -- the residual
  have hid := arctan_sub_eq_arctan_div (t := tv) (y := yv) (by rw [← hθ]; linarith)
    (by rw [← hθ]; linarith)
  rw [← hθ] at hid
  set N := tv * cos yv - sin yv with hN
  set D := cos yv + tv * sin yv with hD
  have hts0 : 0 ≤ tv * sin yv := mul_nonneg ht0 hsy0
  have hD1 : 1 / 2 ≤ D := by linarith
  set δ := N / D with hδ
  have hδ0 : 0 ≤ δ := arctan_nonneg.mp (by rw [← hid]; linarith)
  have hN0 : 0 ≤ N := by
    have : N = δ * D := by rw [hδ, div_mul_cancel₀]; linarith
    rw [this]
    exact mul_nonneg hδ0 (by linarith)
  have hND : N ≤ D := by nlinarith [cos_le_one yv]
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by linarith)]
    exact hND
  have htan : δ = tan (θ - yv) := by rw [hid, tan_arctan]
  have hd := atanStep_encl ht ht0 ht1 hV64 hη0 hη hu hν1 hs hc hsy0 hcy hN0
  rw [← hN, ← hD, ← hδ] at hd
  obtain ⟨hth, hfi⟩ := atanStep_cube hV64 hu hν1 hd hδ1
  have hyval : (ofAzNat M <<< AzInt.ofInt (-(T : Int))).toVal = some ((yv : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal (toVal_ofAzNat M) (AzInt.ofInt (-(T : Int)))
    rw [h, AzInt.toInt_ofInt, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  obtain ⟨lo, hi, hlo, hhi, h0, h1, h2, h3⟩ := atanStep_assemble hV64 hu hν1 hyval hyv0 hy1'
    hd hth hfi hδ1 (θ := θ) (by rw [← hid]; ring)
  rw [htan] at h3
  exact ⟨lo, hi, hlo, hhi, h0, h1, h2, h3⟩

/-- **The step**: from a lower end `lb ∈ [0, arctan t]` to an enclosure of `arctan t` of width at
most `tan (arctan t − y)⁵/5 + 2^(−K−40)`, where `y ≤ lb < y + 2^(−K'−3)` is the truncation. -/
theorem atanStep_spec {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (ht0 : 0 ≤ tv)
    (ht1 : tv ≤ 1) {b : Encl} {lb : ℝ} (hb : b.1.toVal = some (lb : EReal)) (hb0 : 0 ≤ lb)
    (hbθ : lb ≤ arctan tv) {K' K : ℕ} (hK : K' ≤ K) :
    ∃ lo hi yv : ℝ, (atanStep t b K' K).1.toVal = some (lo : EReal) ∧
      (atanStep t b K' K).2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ arctan tv ∧
      arctan tv ≤ hi ∧ yv ≤ lb ∧ lb < yv + (1 / 2 : ℝ) ^ (K' + 3) ∧
      hi - lo ≤ tan (arctan tv - yv) ^ 5 / 5 + (1 / 2 : ℝ) ^ (K + 40) := by
  unfold atanStep
  set T := K' + 3 with hT
  set M := floorScaled b.1 T with hM
  obtain ⟨hM1, hM2⟩ := floorScaled_spec hb T
  rw [abs_of_nonneg hb0, ← hM] at hM1 hM2
  have hθ1 : arctan tv ≤ π / 4 := by
    rw [← arctan_one]
    exact arctan_strictMono.monotone ht1
  have hπ := pi_lt_four
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  set yv := (M.toNat : ℝ) / 2 ^ T with hyv
  have hy1 : yv ≤ lb := by
    rw [hyv, div_le_iff₀ h2T]
    exact hM1
  have hy2 : lb < yv + (1 / 2 : ℝ) ^ T := by
    have h : (1 / 2 : ℝ) ^ T = 1 / 2 ^ T := by rw [one_div, inv_pow, one_div]
    rw [hyv, h, ← add_div, lt_div_iff₀ h2T]
    exact hM2
  have hMlt : M.toNat < 2 ^ T := by
    have : (M.toNat : ℝ) < 2 ^ T := by nlinarith
    exact_mod_cast this
  obtain ⟨lo, hi, hlo, hhi, h0, h1, h2, h3⟩ := atanStepAt_spec ht ht0 ht1 (by omega)
    (by omega : T ≤ K + 3) hMlt (Or.inl (hy1.trans hbθ))
  exact ⟨lo, hi, yv, hlo, hhi, h0, h1, h2, hy1, hy2, h3⟩

/-- **The step from the seed**: whatever the (unverified) seed is, an accepted result encloses
`arctan t` with a nonnegative lower end and width at most `(3/4) 2^(−K)`. -/
theorem atanSeeded?_spec {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal))
    (ht0 : 0 ≤ tv) (ht1 : tv ≤ 1) {K : ℕ} {r : Encl} (h : atanSeeded? t K = some r) :
    ∃ lo hi : ℝ, r.1.toVal = some (lo : EReal) ∧ r.2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧
      lo ≤ arctan tv ∧ arctan tv ≤ hi ∧ hi - lo ≤ 3 / 4 * (1 / 2 : ℝ) ^ K := by
  unfold atanSeeded? at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  obtain ⟨hflag, hle⟩ := h3
  rw [Option.some.injEq] at h
  subst h
  set M := atanSeed t with hM
  set Ke := max K 59 with hKe
  have hMlt : M.toNat < 2 ^ 62 := by
    rw [← Nat.size_le, AzNat.size_toNat]
    omega
  obtain ⟨lo, hi, hlo, hhi, h0, hl, hu, -⟩ := atanStepAt_spec ht ht0 ht1 (by norm_num)
    (by omega : 62 ≤ Ke + 3) hMlt (Or.inr hflag)
  obtain ⟨wv, hwv, hwge, -⟩ := subCeiling_abs hhi hlo 64
  have hc := toVal_shiftLeft_of_toVal (toVal_ofAzNat (AzNat.ofNat 3))
    (AzInt.ofInt (-((Ke : Int) + 2)))
  rw [AzNat.toNat_ofNat, AzInt.toInt_ofInt] at hc
  have hle' := (le_eq_true_iff hwv hc).mp hle
  have e : ((3 : ℕ) : ℝ) * (2 : ℝ) ^ (-((Ke : ℤ) + 2)) = 3 / 4 * (1 / 2 : ℝ) ^ Ke := by
    rw [zpow_neg, zpow_add₀ two_ne_zero, zpow_natCast, one_div, inv_pow]
    norm_num
    ring
  have hmono : (1 / 2 : ℝ) ^ Ke ≤ (1 / 2 : ℝ) ^ K :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
  rw [e] at hle'
  exact ⟨lo, hi, hlo, hhi, h0, hl, hu, by linarith⟩

/-! ### The levels -/

/-- **The levels**: `atanLoop t fuel K` encloses `arctan t` (`0 ≤ t ≤ 1`), with a nonnegative
lower end, and its width is at most `(3/4) 2^(−K)` when `K ≤ fuel + 1`. -/
theorem atanLoop_spec {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (ht0 : 0 ≤ tv)
    (ht1 : tv ≤ 1) (fuel K : ℕ) :
    ∃ lo hi : ℝ, (atanLoop t fuel K).1.toVal = some (lo : EReal) ∧
      (atanLoop t fuel K).2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ arctan tv ∧
      arctan tv ≤ hi ∧ (K ≤ fuel + 1 → hi - lo ≤ 3 / 4 * (1 / 2 : ℝ) ^ K) := by
  have hbase : ∀ K : ℕ, ∃ lo hi : ℝ, (atanBase t (K + 64)).1.toVal = some (lo : EReal) ∧
      (atanBase t (K + 64)).2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ arctan tv ∧
      arctan tv ≤ hi ∧ (K ≤ 1 → hi - lo ≤ 3 / 4 * (1 / 2 : ℝ) ^ K) := fun K => by
    obtain ⟨lo, hi, hlo, hhi, h0, h1, h2, h3⟩ := atanBase_spec ht ht0 ht1 (V := K + 64) (by omega)
    refine ⟨lo, hi, hlo, hhi, h0, h1, h2, fun hK => ?_⟩
    interval_cases K <;> norm_num <;> linarith
  induction fuel generalizing K with
  | zero =>
    obtain ⟨lo, hi, hlo, hhi, h0, h1, h2, h3⟩ := hbase K
    exact ⟨lo, hi, hlo, hhi, h0, h1, h2, fun hK => h3 (by omega)⟩
  | succ f ih =>
    rw [atanLoop]
    split_ifs with hK1
    · obtain ⟨lo, hi, hlo, hhi, h0, h1, h2, h3⟩ := hbase K
      exact ⟨lo, hi, hlo, hhi, h0, h1, h2, fun _ => h3 hK1⟩
    · split
      · rename_i r hr
        obtain ⟨lo, hi, hlo, hhi, h0, h1, h2, hw⟩ := atanSeeded?_spec ht ht0 ht1 hr
        exact ⟨lo, hi, hlo, hhi, h0, h1, h2, fun _ => hw⟩
      · set K' := (K + 4) / 5 with hK'
        obtain ⟨lb, hb, hlb, hhb, hb0, hb1, hb2, hbw⟩ := ih K'
        obtain ⟨lo, hi, yv, hlo, hhi, h0, h1, h2, hy1, hy2, hw⟩ :=
          atanStep_spec ht ht0 ht1 hlb hb0 hb1 (K' := K') (K := K) (by omega)
        refine ⟨lo, hi, hlo, hhi, h0, h1, h2, fun hK => hw.trans ?_⟩
        have hbw' := hbw (by omega)
        set h := (1 / 2 : ℝ) ^ K' with hh
        have hh0 : 0 < h := by positivity
        have hh1 : h ≤ 1 / 2 := by
          have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
            (by omega : 1 ≤ K')
          rw [← hh] at this
          linarith
        have hh3 : (1 / 2 : ℝ) ^ (K' + 3) = h / 8 := by rw [pow_add, ← hh]; ring
        rw [hh3] at hy2
        set φ := arctan tv - yv with hφ
        have hφ0 : 0 ≤ φ := by linarith
        have hφ1 : φ ≤ 7 / 8 * h := by linarith
        have htan := tan_le_five_fourths_mul hφ0 (by linarith)
        have htan0 : 0 ≤ tan φ := tan_nonneg_of_nonneg_of_le_pi_div_two hφ0
          (by linarith [pi_gt_three])
        have hcube : tan φ ^ 5 ≤ (35 / 32 * h) ^ 5 := pow_le_pow_left₀ htan0 (by linarith) 5
        have hh3K : h ^ 5 ≤ (1 / 2 : ℝ) ^ K := by
          rw [hh, ← pow_mul]
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have hν : (1 / 2 : ℝ) ^ (K + 40) ≤ (1 / 2 : ℝ) ^ K / 1024 := by
          rw [pow_add]
          have : (1 / 2 : ℝ) ^ 40 ≤ 1 / 1024 := by norm_num
          have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
          nlinarith
        have hexp : (35 / 32 * h) ^ 5 = 52521875 / 33554432 * h ^ 5 := by ring
        rw [hexp] at hcube
        linarith

/-! ### The bracket -/

/-- **The bracket of `arctan |x|`**: ends with values around `arctan |x|`, width at most
`2^(−w)`. -/
theorem atanBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {ex : AzInt} (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|)
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w : ℕ) :
    ∃ lo hi : ℝ, (atanBracket x ex w).1.toVal = some (lo : EReal) ∧
      (atanBracket x ex w).2.toVal = some (hi : EReal) ∧ lo ≤ arctan |xv| ∧
      arctan |xv| ≤ hi ∧ hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  have htoInt : ex.toInt = if ex.sign then (ex.abs.toNat : ℤ) else -(ex.abs.toNat : ℤ) := rfl
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  unfold atanBracket
  split_ifs with hc
  · -- `|x| < 1`
    have hex0 : ex.toInt ≤ 0 := by
      rw [htoInt]
      rcases hc with hc | hc
      · rw [hc]; simp
      · rw [hc]; simp
    have ha1 : a ≤ 1 := hex.le.trans (zpow_le_one_of_nonpos₀ (by norm_num) hex0)
    dsimp only
    obtain ⟨lo, hi, hlo, hhi, -, h1, h2, h3⟩ :=
      atanLoop_spec habs ha0.le ha1 (atanWork ex w) (atanWork ex w)
    refine ⟨lo, hi, hlo, hhi, h1, h2, (h3 (by omega)).trans ?_⟩
    have hle : (1 / 2 : ℝ) ^ atanWork ex w ≤ (1 / 2 : ℝ) ^ w :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold atanWork; omega)
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ atanWork ex w := by positivity
    linarith
  · -- `|x| ≥ 1`
    have hex0 : 1 ≤ ex.toInt := by
      rw [htoInt]
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      have hs : ex.sign = true := by simpa using hc1
      rw [hs]
      simp only [↓reduceIte]
      omega
    have ha1 : 1 ≤ a := le_trans (one_le_zpow₀ (by norm_num) (by omega)) hex1
    dsimp only
    set K := w + 8 with hK
    set V := K + 64 with hV
    have hV64 : 64 ≤ V := by omega
    have : NeZero V := ⟨by omega⟩
    have : NeZero 64 := ⟨by omega⟩
    set u := (1 / 2 : ℝ) ^ V with hu
    have hu0 : 0 ≤ u := by positivity
    have hwu : (1 / 2 : ℝ) ^ w = 2 ^ 72 * u := by
      have e : (2 : ℝ) ^ 72 * (1 / 2 : ℝ) ^ 72 = 1 := by norm_num
      rw [hu, hV, hK, show w + 8 + 64 = w + 72 by ring, pow_add (1 / 2 : ℝ) w 72]
      linear_combination (-(1 / 2 : ℝ) ^ w) * e
    have hu1 : u ≤ 1 / 2 ^ 72 := by
      have : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      rw [hwu] at this
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hKu : (1 / 2 : ℝ) ^ K = 2 ^ 64 * u := by
      have e : (2 : ℝ) ^ 64 * (1 / 2 : ℝ) ^ 64 = 1 := by norm_num
      rw [hu, hV, pow_add (1 / 2 : ℝ) K 64]
      linear_combination (-(1 / 2 : ℝ) ^ K) * e
    set r := 1 / a with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 := by
      rw [hr, div_le_one ha0]
      exact ha1
    obtain ⟨rl, hrl, hrlf⟩ := divFloor_err toVal_one' habs ha0 (by norm_num) V
    obtain ⟨rh, hrh, hrhc⟩ := divCeiling_err toVal_one' habs ha0 (by norm_num) V
    rw [← hr] at hrlf hrhc
    have hrl1 := hrlf.le
    have hrl2 := hrlf.ge
    have hrh1 := hrhc.ge
    have hrh2 := hrhc.le
    rw [← hu] at hrl2 hrh2
    obtain ⟨lb, hb, hlb, hhb, hb0, hb1, hb2, hbw⟩ :=
      atanLoop_spec hrl hrlf.nonneg (hrl1.trans hr1) K K
    have hbw' := hbw (by omega)
    rw [hKu] at hbw'
    obtain ⟨dv, hdv, hdv1, hdv2⟩ := subCeiling_abs hrh hrl 64
    obtain ⟨up, hup, hup1, hup2⟩ := addCeiling_abs hhb hdv V
    rw [← hu] at hup2
    obtain ⟨pl, ph, hpl, hph, hpl0, hpl1, hph1, hpw⟩ := piBracket_spec_width hV64
    rw [← hu] at hpw
    have hpl' : ((piBracket V).1 <<< AzInt.ofInt (-1)).toVal = some ((pl / 2 : ℝ) : EReal) := by
      have h := toVal_shiftLeft_of_toVal hpl (AzInt.ofInt (-1))
      rw [h, AzInt.toInt_ofInt, zpow_neg_one, div_eq_mul_inv]
    have hph' : ((piBracket V).2 <<< AzInt.ofInt (-1)).toVal = some ((ph / 2 : ℝ) : EReal) := by
      have h := toVal_shiftLeft_of_toVal hph (AzInt.ofInt (-1))
      rw [h, AzInt.toInt_ofInt, zpow_neg_one, div_eq_mul_inv]
    obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hpl' hup V
    obtain ⟨hi, hhi, hhi1, hhi2⟩ := subCeiling_abs hph' hlb V
    rw [← hu] at hlo2 hhi2
    have hinv : arctan a = π / 2 - arctan r := by
      have hra : r⁻¹ = a := by rw [hr, one_div, inv_inv]
      rw [← hra, arctan_inv_of_pos hr0]
    have hlip := arctan_sub_arctan_le hrl1
    have hrr : arctan rl ≤ arctan r := arctan_strictMono.monotone hrl1
    have hat0 : 0 ≤ arctan rl := arctan_nonneg.mpr hrlf.nonneg
    have hat1 : arctan rl ≤ 1 := (arctan_le_self hrlf.nonneg).trans (hrl1.trans hr1)
    have hru : r * u ≤ u := mul_le_of_le_one_left hu0 hr1
    have hdr0 : 0 ≤ rh - rl := by linarith
    have hdr : rh - rl ≤ 4 * u := by linarith
    have hdv3 : dv ≤ 8 * u := by
      have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
      rw [abs_of_nonneg hdr0] at hdv2
      have := mul_le_mul_of_nonneg_left h64 hdr0
      linarith
    have hu8 : u ≤ 1 / 1024 := hu1.trans (by norm_num)
    have h64u : (2 : ℝ) ^ 64 * u ≤ 1 / 256 := by
      have h := mul_le_mul_of_nonneg_left hu1 (by positivity : (0 : ℝ) ≤ 2 ^ 64)
      have e : (2 : ℝ) ^ 64 * (1 / 2 ^ 72) = 1 / 256 := by norm_num
      linarith
    have hπ := pi_lt_four
    have hπ3 := pi_gt_three
    have hhb3 : hb ≤ 2 := by linarith
    have habs1 : |hb + dv| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith
    have m1 := mul_le_mul_of_nonneg_right habs1 hu0
    have hup3 : up ≤ 4 := by linarith
    have hup0 : 0 ≤ up := by linarith
    have habs2 : |pl / 2 - up| ≤ 8 := by
      rw [abs_le]
      constructor <;> linarith
    have habs3 : |ph / 2 - lb| ≤ 8 := by
      rw [abs_le]
      constructor <;> linarith
    have m2 := mul_le_mul_of_nonneg_right habs2 hu0
    have m3 := mul_le_mul_of_nonneg_right habs3 hu0
    refine ⟨lo, hi, hlo, hhi, by linarith, by linarith, ?_⟩
    have h72 : (2 : ℝ) ^ 72 * u = 256 * (2 ^ 64 * u) := by
      have : (2 : ℝ) ^ 72 = 256 * 2 ^ 64 := by norm_num
      rw [this]
      ring
    have h64big : 1000 * u ≤ 2 ^ 64 * u :=
      mul_le_mul_of_nonneg_right (by norm_num) hu0
    rw [hwu, h72]
    linarith

/-- `atanApprox neg` as a pair of `Roundable`s bracketing `± arctan |x|`. -/
theorem atanApprox_spec (neg : Bool) {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {ex : AzInt} (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|)
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (atanApprox neg x ex w).1 lv ∧ Rounds (atanApprox neg x ex w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * arctan |xv| ∧
      (if neg then -1 else 1) * arctan |xv| ≤ hv ∧ hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := atanBracket_spec hx hx0 hex1 hex w
  simp only [atanApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    have hnlo : (-(atanBracket x ex w).2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(atanBracket x ex w).1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- The Ziv certificate for `arctan x`, `x` a nonzero finite float. -/
theorem atanApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hneg : neg = true ↔ xv < 0) {ex : AzInt} (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|)
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (atanApprox neg x ex (w₀ * 2 ^ f)).1
      (atanApprox neg x ex (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hval := arctan_eq_of_neg_iff hneg
  refine exists_isSome_of_irrational_threshold p mode (atanApprox neg x ex)
    (v := (if neg then -1 else 1) * arctan |xv|) ?_ (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => atanApprox_spec neg hx hx0 hex1 hex w) w₀ hw₀
  rw [← hval]
  exact irrational_arctan_of_toVal hx hx0

/-- The tiny-argument path answers with the rounding of `arctan x`. -/
theorem atanTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : atanTiny? s (finite s e q m hv) e q p mode = some r) :
    r = roundVal p mode (some ((arctan (finiteVal s e m) : ℝ) : EReal)) :=
  sinTiny?_eq_of arctan_neg (fun _ ha => arctan_lt_self ha)
    (fun a ha => by
      have h1 := sub_cube_div_three_le_arctan ha.le
      have h2 : 0 < a ^ 3 := by positivity
      linarith) hv p mode h

end Azurite.AzFloat
