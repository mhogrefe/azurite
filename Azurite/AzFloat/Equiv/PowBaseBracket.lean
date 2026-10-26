/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBaseBracket
import Azurite.AzFloat.Equiv.LogBaseExact
import Azurite.AzFloat.Equiv.Pow2Bracket
import Azurite.AzFloat.Equiv.Pow2Rat
import Azurite.AzFloat.PowBaseBracket

/-!
# Equivalence: the brackets of `u^x` and `u^q`

* `pow_ne_pow_of_not_pow`: `M^D ≠ r^N` for `0 < N < D` when `r` is not a perfect power, and
  `irrational_rpow_of_rat_of_not_pow`: `r^y` is irrational for such `r ≥ 2` and a non-integer
  rational `y`.
* `lnBaseMulBracket_spec` (width `mulLnEps e eb w = lnEps (|eb| + 16 + max(e, 0)) w + 2^(−w)`:
  the `|x| ≤ 2^max(e, 0)` factor is absorbed by the `expWork` precision), `mulLnEps_le_one` from
  `136 + max(e, 0) + |eb|` bits (`two_pow_54_mul_pow5_le`, `mulLnEps_le_inv256`),
  `powBaseBracket_spec` (width
  `powBaseEps`).
* `powBaseExact?_some` (`u^x = r^n`) and `irrational_of_powBaseExact?_none`,
  `powBaseApprox_spec`, `powBaseApprox_isSome_exists`; and the rational versions
  `lnBaseMulRatBracket_spec`, `powBaseRatBracket_spec`, `powBaseRatExact?_some`,
  `irrational_of_powBaseRatExact?_none`, `powBaseRatApprox_spec`,
  `powBaseRatApprox_isSome_exists`.
* `u^x − 1`: `mulLnEps_comp_le` (the compensated bracket of `x ln u` has width `≤ 2^e / 4`),
  `powBaseM1Bracket_spec` (through `expM1OfBracket_spec_of_bounds` at the exponent `e + 6`,
  width `powBaseM1Eps`), `powBaseM1Approx_spec`, `powBaseM1Approx_isSome_exists`,
  `irrational_sub_one_of_powBaseExact?_none`; and for `u^q − 1`: `powBaseM1RatBracket_spec`
  (the exponent `pow2M1RatExp q + 6`, `mulLnEps_comp_le_of` with `B = |e| + size (num q)`),
  `powBaseM1RatApprox_spec`, `powBaseM1RatApprox_isSome_exists`,
  `irrational_sub_one_of_powBaseRatExact?_none`.
-/

namespace Azurite.AzFloat

/-! ### Irrationality of `r^y` for a primitive `r` -/

/-- `M^D = r^N` with `0 < N < D` makes `r` a perfect power
(`Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow` after dividing the exponents by their
gcd). -/
theorem pow_ne_pow_of_not_pow {r : ℕ} (hnp : ∀ t, 2 ≤ t → ¬ ∃ d, r = d ^ t) {M D N : ℕ}
    (hN : 0 < N) (hND : N < D) : M ^ D ≠ r ^ N := by
  intro h
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd D N := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨D', hD'⟩ : ∃ D', D' = D / g := ⟨_, rfl⟩
  obtain ⟨N', hN'⟩ : ∃ N', N' = N / g := ⟨_, rfl⟩
  have hcop : Nat.Coprime D' N' := by
    rw [hD', hN', hg]; exact Nat.coprime_div_gcd_div_gcd (by rw [← hg]; exact hg0)
  have hDg : D = g * D' := by rw [hD', hg]; exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hNg : N = g * N' := by
    rw [hN', hg]; exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  have hN'0 : 0 < N' := by
    rcases Nat.eq_zero_or_pos N' with h0 | h0
    · rw [h0, mul_zero] at hNg; omega
    · exact h0
  have hD'2 : 2 ≤ D' := by
    by_contra hlt
    have hD'1 : D' ≤ 1 := by omega
    have : D ≤ N := by
      calc D = g * D' := hDg
        _ ≤ g * 1 := Nat.mul_le_mul_left _ hD'1
        _ ≤ g * N' := Nat.mul_le_mul_left _ hN'0
        _ = N := hNg.symm
    omega
  have hred : M ^ D' = r ^ N' := by
    have : (M ^ D') ^ g = (r ^ N') ^ g := by
      rw [← pow_mul, ← pow_mul, mul_comm D', mul_comm N', ← hDg, ← hNg]; exact h
    exact (pow_left_inj₀ (by positivity) (by positivity) hg0.ne').mp this
  obtain ⟨C, -, hrC⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcop hred
  exact hnp D' hD'2 ⟨C, hrC⟩

/-- `r^y` is irrational for `r ≥ 2` not a perfect power and a rational `y = N / D` that is not
an integer. -/
theorem irrational_rpow_of_rat_of_not_pow {r : ℕ} (hr : 2 ≤ r)
    (hnp : ∀ t, 2 ≤ t → ¬ ∃ d, r = d ^ t) {y : ℝ} {N : ℤ} {D : ℕ} (hD : 0 < D)
    (hd : y * D = N) (hni : ¬ ∃ n : ℤ, y = n) : Irrational ((r : ℝ) ^ y) := by
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hxv : y = (N : ℝ) / (D : ℝ) := by
    rw [eq_div_iff hDr.ne']
    exact hd
  have hf0 : 0 ≤ Int.fract y := Int.fract_nonneg y
  have hf1 : Int.fract y < 1 := Int.fract_lt_one y
  have hfne : Int.fract y ≠ 0 := by
    intro h0
    apply hni
    refine ⟨⌊y⌋, ?_⟩
    have := Int.fract_add_floor y
    rw [h0, zero_add] at this
    exact this.symm
  have hfpos : 0 < Int.fract y := lt_of_le_of_ne hf0 (Ne.symm hfne)
  have hfrac : Int.fract y = ((N % D : ℤ) : ℝ) / (D : ℝ) := by
    rw [hxv, Int.fract_div_intCast_eq_div_intCast_mod]
  have hm0 : 0 ≤ N % D := Int.emod_nonneg _ (by exact_mod_cast hD.ne')
  have hmD : N % D < D := Int.emod_lt_of_pos _ (by exact_mod_cast hD)
  have hmne : N % D ≠ 0 := by
    intro h0
    apply hfne
    rw [hfrac, h0, Int.cast_zero, zero_div]
  have hy1 : 1 < (r : ℝ) ^ Int.fract y := Real.one_lt_rpow hr1 hfpos
  have hmt : ((N % D : ℤ) : ℝ) = (((N % D).toNat : ℕ) : ℝ) := by
    have := Int.toNat_of_nonneg hm0
    exact_mod_cast this.symm
  have hyn : ((r : ℝ) ^ Int.fract y) ^ D = ((r ^ (N % D).toNat : ℤ) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0, hfrac]
    have e1 : ((N % D : ℤ) : ℝ) / (D : ℝ) * (D : ℝ) = ((N % D : ℤ) : ℝ) := by
      field_simp
    rw [e1, hmt, Real.rpow_natCast]
    push_cast
    ring
  have hirr : Irrational ((r : ℝ) ^ Int.fract y) := by
    refine irrational_nrt_of_notint_nrt D (r ^ (N % D).toNat) hyn ?_ hD
    rintro ⟨z, hz⟩
    rw [hz] at hy1 hyn
    have hz1 : (1 : ℤ) < z := by exact_mod_cast hy1
    obtain ⟨Mz, hMz⟩ : ∃ Mz : ℕ, z = Mz := ⟨z.toNat, by omega⟩
    rw [hMz] at hyn
    have hnat : Mz ^ D = r ^ (N % D).toNat := by exact_mod_cast hyn
    have hNpos : 0 < (N % D).toNat := by omega
    have hNlt : (N % D).toNat < D := by omega
    exact pow_ne_pow_of_not_pow hnp hNpos hNlt hnat
  have hsplit : (r : ℝ) ^ y = (((r : ℚ) ^ ⌊y⌋ : ℚ) : ℝ) * (r : ℝ) ^ Int.fract y := by
    conv_lhs => rw [← Int.floor_add_fract y]
    rw [Real.rpow_add (by linarith), Real.rpow_intCast, Rat.cast_zpow, Rat.cast_natCast]
  rw [hsplit]
  exact hirr.ratCast_mul (zpow_ne_zero _ (by positivity))

/-! ### The bracket of `x ln u` -/

/-- The width bound of `lnBaseMulBracket` at exponents `e` (of `x`) and `eb` (of `u`). -/
noncomputable def mulLnEps (e eb : ℤ) (w : ℕ) : ℝ :=
  lnEps (|eb| + 16 + max e 0) w + (1 / 2 : ℝ) ^ w

theorem tendsto_mulLnEps (e eb : ℤ) : Filter.Tendsto (mulLnEps e eb) Filter.atTop (nhds 0) := by
  have h1 := tendsto_lnEps (|eb| + 16 + max e 0)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have := h1.add h2
  rwa [add_zero] at this

/-- `expWork e w − w − 16` is `max(e, 0)`. -/
theorem expPos_eq_max (e : AzInt) :
    ((if e.sign then e.abs.toNat else 0 : ℕ) : ℤ) = max e.toInt 0 := by
  split_ifs with hs
  · have h0 := (AzInt.sign_eq_true_iff e).mp hs
    rw [AzInt.abs_toNat_eq e, abs_of_nonneg h0, max_eq_left h0]
  · have := (AzInt.sign_eq_true_iff e).not.mp hs
    push Not at this
    push_cast
    rw [max_eq_right this.le]

/-- `ln u < 45` for a 64-bit `u`. -/
theorem log_lt_45_of_lt_two_pow_64 {n : ℕ} (hn : n < 2 ^ 64) : Real.log n < 45 := by
  have h2 : Real.log ((2 : ℝ) ^ 64) = 64 * Real.log 2 := by
    rw [Real.log_pow]; push_cast; ring
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]; norm_num
  · have : Real.log n < Real.log ((2 : ℝ) ^ 64) :=
      Real.log_lt_log (by exact_mod_cast h0) (by exact_mod_cast hn)
    rw [h2] at this
    linarith [Real.log_two_lt_d9]

set_option maxHeartbeats 1000000 in
/-- `lnBaseMulBracket x e u w` encloses `x ln u` with width at most `mulLnEps e eb w`, for
`|x| < 2^e` and `2 ≤ u`. -/
theorem lnBaseMulBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (e : AzInt) (hxe : |xv| < (2 : ℝ) ^ e.toInt) (u : UInt64) (hu : 2 ≤ u.toNat) (w : ℕ)
    (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (lnBaseMulBracket x e u w).1.toVal = some (lo : EReal) ∧
      (lnBaseMulBracket x e u w).2.toVal = some (hi : EReal) ∧
      lo ≤ xv * Real.log u.toNat ∧ xv * Real.log u.toNat ≤ hi ∧
      hi - lo ≤ mulLnEps e.toInt ((baseFloat u).exponent?.getD 0).toInt w := by
  -- the working precision and the scale (as in `ln2MulBracket_spec`)
  obtain ⟨emax, hemax⟩ : ∃ n : ℕ, n = if e.sign then e.abs.toNat else 0 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = expWork e w := ⟨_, rfl⟩
  have hWv : W = w + 16 + emax := by rw [hW, hemax]; rfl
  have hemaxM : (emax : ℤ) = max e.toInt 0 := by rw [hemax]; exact expPos_eq_max e
  have hemaxZ : e.toInt ≤ (emax : ℤ) := by rw [hemaxM]; exact le_max_left _ _
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ emax := ⟨_, rfl⟩
  have hxE : |xv| < E := by
    calc |xv| < (2 : ℝ) ^ e.toInt := hxe
      _ ≤ (2 : ℝ) ^ (emax : ℤ) := zpow_le_zpow_right₀ (by norm_num) hemaxZ
      _ = E := by rw [hE, zpow_natCast]
  obtain ⟨uu, huu⟩ : ∃ uu : ℝ, uu = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have huu0 : 0 < uu := by rw [huu]; positivity
  have : NeZero W := ⟨by omega⟩
  have hδ : (1 / 2 : ℝ) ^ W = uu * (1 / 65536) * (1 / 2 : ℝ) ^ emax := by
    rw [hWv, pow_add, pow_add, huu, show ((1 : ℝ) / 2) ^ 16 = 1 / 65536 by norm_num]
  have hEu : E * (1 / 2 : ℝ) ^ emax = 1 := by
    rw [hE, one_div_pow, mul_one_div, div_self (by positivity)]
  have hhalf0 : 0 ≤ (1 / 2 : ℝ) ^ emax := by positivity
  have hX : |xv| * (1 / 2 : ℝ) ^ W ≤ uu / 65536 := by
    rw [hδ]
    have : |xv| * (1 / 2 : ℝ) ^ emax ≤ E * (1 / 2 : ℝ) ^ emax :=
      mul_le_mul_of_nonneg_right hxE.le hhalf0
    rw [hEu] at this
    calc |xv| * (uu * (1 / 65536) * (1 / 2 : ℝ) ^ emax)
        = uu / 65536 * (|xv| * (1 / 2 : ℝ) ^ emax) := by ring
      _ ≤ uu / 65536 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = uu / 65536 := mul_one _
  have hδ0 : 0 ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hW64 : (1 / 2 : ℝ) ^ W ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  -- the bracket of `ln u` and the products with `|x|`
  obtain ⟨eb, heb⟩ : ∃ eb : ℤ, eb = ((baseFloat u).exponent?.getD 0).toInt := ⟨_, rfl⟩
  obtain ⟨c, d, hc, hd, hc0, hcM, hMd, hcd⟩ := lnBaseBracket_spec (by omega : 64 ≤ W) u hu
  rw [← heb] at hcd
  have hlog45 : Real.log u.toNat < 45 := log_lt_45_of_lt_two_pow_64 u.toBitVec.isLt
  have hc1 : 0 ≤ c := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hlnE0 : 0 ≤ lnEps eb W := by unfold lnEps; positivity
  have hd45 : d ≤ 45 + lnEps eb W := by linarith
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hka0 : 0 ≤ |xv| := abs_nonneg _
  obtain ⟨plo, hplo, hplo1⟩ := mulFloor_err habs hc W (mul_nonneg hka0 hc1)
  obtain ⟨phi, hphi, hphi1⟩ := mulCeiling_err habs hd W (mul_nonneg hka0 hd0)
  have hP1 : plo ≤ |xv| * Real.log u.toNat :=
    hplo1.le.trans (mul_le_mul_of_nonneg_left hcM hka0)
  have hP2 : |xv| * Real.log u.toNat ≤ phi :=
    (mul_le_mul_of_nonneg_left hMd hka0).trans hphi1.ge
  -- the key identity: `|x| lnEps eb W ≤ lnEps (|eb| + 16 + emax) w / 65536`
  have hkey : |xv| * lnEps eb W ≤ lnEps (|eb| + 16 + max e.toInt 0) w / 65536 := by
    unfold lnEps
    have hpoly : ((W : ℕ) : ℝ) + |(eb : ℝ)| + 8
        = (w : ℝ) + |((|eb| + 16 + max e.toInt 0 : ℤ) : ℝ)| + 8 := by
      rw [← hemaxM, hWv]
      push_cast
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |(eb : ℝ)| + 16 + emax)]
      ring
    rw [hpoly]
    have hP0 : 0 ≤ (2 : ℝ) ^ 40 * ((w : ℝ) + |((|eb| + 16 + max e.toInt 0 : ℤ) : ℝ)| + 8) ^ 5 := by
      positivity
    rw [← huu]
    calc |xv| * (2 ^ 40 * ((w : ℝ) + |((|eb| + 16 + max e.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * (1 / 2 : ℝ) ^ W)
        = 2 ^ 40 * ((w : ℝ) + |((|eb| + 16 + max e.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * (|xv| * (1 / 2 : ℝ) ^ W) := by ring
      _ ≤ 2 ^ 40 * ((w : ℝ) + |((|eb| + 16 + max e.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * (uu / 65536) := mul_le_mul_of_nonneg_left hX hP0
      _ = _ := by ring
  have hpwid : phi - plo ≤ mulLnEps e.toInt eb w := by
    unfold mulLnEps
    rw [← huu]
    have h1 := hplo1.ge
    have h2 := hphi1.le
    have h3 : |xv| * (d - c) ≤ |xv| * lnEps eb W := mul_le_mul_of_nonneg_left hcd hka0
    have h4 : 2 * (|xv| * d) * (1 / 2 : ℝ) ^ W
        ≤ 2 * (45 * (uu / 65536) + lnEps eb W * (|xv| * (1 / 2 : ℝ) ^ W)) := by
      have : |xv| * d * (1 / 2 : ℝ) ^ W ≤ |xv| * (45 + lnEps eb W) * (1 / 2 : ℝ) ^ W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd45 hka0) hδ0
      have h5 : |xv| * (45 + lnEps eb W) * (1 / 2 : ℝ) ^ W
          = 45 * (|xv| * (1 / 2 : ℝ) ^ W) + lnEps eb W * (|xv| * (1 / 2 : ℝ) ^ W) := by ring
      rw [h5] at this
      linarith
    have h6 : 2 * (|xv| * c) * (1 / 2 : ℝ) ^ W ≤ 2 * (45 * (uu / 65536)) := by
      have hc45 : c ≤ 45 := by linarith
      have : |xv| * c * (1 / 2 : ℝ) ^ W ≤ |xv| * 45 * (1 / 2 : ℝ) ^ W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc45 hka0) hδ0
      have h5 : |xv| * 45 * (1 / 2 : ℝ) ^ W = 45 * (|xv| * (1 / 2 : ℝ) ^ W) := by ring
      rw [h5] at this
      linarith
    have h7 : lnEps eb W * (|xv| * (1 / 2 : ℝ) ^ W) ≤ lnEps eb W * (uu / 65536) :=
      mul_le_mul_of_nonneg_left hX hlnE0
    -- `lnEps eb W ≤ lnEps (|eb| + 16 + max(e, 0)) w`: the same polynomial, `W ≥ w`
    have h8 : lnEps eb W ≤ lnEps (|eb| + 16 + max e.toInt 0) w := by
      unfold lnEps
      have hpoly : ((W : ℕ) : ℝ) + |(eb : ℝ)| + 8
          = (w : ℝ) + |((|eb| + 16 + max e.toInt 0 : ℤ) : ℝ)| + 8 := by
        rw [← hemaxM, hWv]
        push_cast
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |(eb : ℝ)| + 16 + emax)]
        ring
      rw [hpoly]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hL0 : 0 ≤ lnEps (|eb| + 16 + max e.toInt 0) w := by unfold lnEps; positivity
    have huu1 : uu ≤ 1 := by rw [huu]; exact pow_le_one₀ (by norm_num) (by norm_num)
    have h9 : lnEps eb W * (uu / 65536) ≤ lnEps (|eb| + 16 + max e.toInt 0) w * (uu / 65536) :=
      mul_le_mul_of_nonneg_right h8 (by positivity)
    have h10 : lnEps (|eb| + 16 + max e.toInt 0) w * (uu / 65536)
        ≤ lnEps (|eb| + 16 + max e.toInt 0) w * (1 / 65536) :=
      mul_le_mul_of_nonneg_left (by linarith) hL0
    have h11 : |xv| * (d - c) = |xv| * d - |xv| * c := by ring
    nlinarith
  -- the sign of `x`
  simp only [lnBaseMulBracket, mulBracketSigned, absMulBracket]
  rw [← hW, ← heb]
  split_ifs with hneg
  · have hxneg : xv < 0 := (toVal_sign_of_isNegative hx).1 hneg
    have hax : |xv| = -xv := abs_of_neg hxneg
    have hnphi : (-(mulPrecRound x.abs (lnBaseBracket u W).2 W .Ceiling).1).toVal
        = some ((-phi : ℝ) : EReal) := by rw [toVal_neg, hphi, Option.map_some, EReal.coe_neg]
    have hnplo : (-(mulPrecRound x.abs (lnBaseBracket u W).1 W .Floor).1).toVal
        = some ((-plo : ℝ) : EReal) := by rw [toVal_neg, hplo, Option.map_some, EReal.coe_neg]
    refine ⟨-phi, -plo, hnphi, hnplo, ?_, ?_, ?_⟩
    · rw [hax] at hP2; linarith
    · rw [hax] at hP1; linarith
    · linarith
  · have hxnn : 0 ≤ xv := by
      exact (toVal_sign_of_isNegative hx).2 (by simpa using hneg)
    have hax : |xv| = xv := abs_of_nonneg hxnn
    refine ⟨plo, phi, hplo, hphi, ?_, ?_, hpwid⟩
    · rw [hax] at hP1; exact hP1
    · rw [hax] at hP2; exact hP2

/-! ### The width bound below `1` -/

/-- `2^54 w^5 ≤ 2^w` from `w = 136`. -/
theorem two_pow_54_mul_pow5_le {w : ℕ} (hw : 136 ≤ w) : 2 ^ 54 * w ^ 5 ≤ 2 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h5 : n * 128 ≤ n ^ 2 := by nlinarith
    have h4 : n ^ 2 * 128 ≤ n ^ 3 := by nlinarith
    have h3 : n ^ 3 * 128 ≤ n ^ 4 := by nlinarith
    have h2 : n ^ 4 * 128 ≤ n ^ 5 := by nlinarith
    have hstep : (n + 1) ^ 5 ≤ 2 * n ^ 5 := by
      have e : (n + 1) ^ 5 = n ^ 5 + 5 * n ^ 4 + 10 * n ^ 3 + 10 * n ^ 2 + 5 * n + 1 := by ring
      rw [e]
      linarith
    calc 2 ^ 54 * (n + 1) ^ 5 ≤ 2 ^ 54 * (2 * n ^ 5) := Nat.mul_le_mul_left _ hstep
      _ = 2 * (2 ^ 54 * n ^ 5) := by ring
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (n + 1) := by ring

/-- From `136 + max(e, 0) + |eb|` bits the width bound is below `1/256`. -/
theorem mulLnEps_le_inv256 (e eb : ℤ) (w : ℕ) (hw : 136 + max e 0 + |eb| ≤ (w : ℤ)) :
    mulLnEps e eb w ≤ 1 / 256 := by
  unfold mulLnEps lnEps
  have hw136 : 136 ≤ w := by
    have h1 : (0 : ℤ) ≤ max e 0 := le_max_right _ _
    have h2 : (0 : ℤ) ≤ |eb| := abs_nonneg _
    omega
  have hwR : (136 : ℝ) + max (e : ℝ) 0 + |(eb : ℝ)| ≤ w := by
    have : ((136 + max e 0 + |eb| : ℤ) : ℝ) ≤ ((w : ℤ) : ℝ) := by exact_mod_cast hw
    push_cast at this
    exact this
  have hE : ((|eb| + 16 + max e 0 : ℤ) : ℝ) = |(eb : ℝ)| + 16 + max (e : ℝ) 0 := by push_cast; ring
  rw [hE, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |(eb : ℝ)| + 16 + max (e : ℝ) 0)]
  have hpoly : (w : ℝ) + (|(eb : ℝ)| + 16 + max (e : ℝ) 0) + 8 ≤ 2 * w := by linarith
  have hpoly0 : (0 : ℝ) ≤ (w : ℝ) + (|(eb : ℝ)| + 16 + max (e : ℝ) 0) + 8 := by positivity
  have h1 : (2 : ℝ) ^ 40 * ((w : ℝ) + (|(eb : ℝ)| + 16 + max (e : ℝ) 0) + 8) ^ 5
      ≤ 2 ^ 40 * (2 * w) ^ 5 := by gcongr
  have h2 : (2 : ℝ) ^ 40 * (2 * (w : ℝ)) ^ 5 = 2 ^ 45 * (w : ℝ) ^ 5 := by ring
  have h3 : (2 : ℝ) ^ 54 * (w : ℝ) ^ 5 ≤ 2 ^ w := by exact_mod_cast two_pow_54_mul_pow5_le hw136
  have hp : (0 : ℝ) < 2 ^ w := by positivity
  have hhalf : (1 / 2 : ℝ) ^ w = 1 / 2 ^ w := by rw [one_div_pow]
  have hhw : (1 / 2 : ℝ) ^ w ≤ 1 / 512 := by
    calc (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 9 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 512 := by norm_num
  have h4 : (2 : ℝ) ^ 40 * ((w : ℝ) + (|(eb : ℝ)| + 16 + max (e : ℝ) 0) + 8) ^ 5 * (1 / 2 : ℝ) ^ w
      ≤ 1 / 512 := by
    rw [hhalf, ← div_eq_mul_one_div, div_le_iff₀ hp]
    linarith
  linarith

/-- From `136 + max(e, 0) + |eb|` bits the width bound is below `1`. -/
theorem mulLnEps_le_one (e eb : ℤ) (w : ℕ) (hw : 136 + max e 0 + |eb| ≤ (w : ℤ)) :
    mulLnEps e eb w ≤ 1 :=
  (mulLnEps_le_inv256 e eb w hw).trans (by norm_num)

/-! ### The bracket of `u^x` -/

/-- The width bound of `powBaseBracket` at the exponents `e`, `eb` and the value `v = x ln u`. -/
noncomputable def powBaseEps (e eb : ℤ) (v : ℝ) (w : ℕ) : ℝ :=
  expOfBracketEps v (mulLnEps e eb w) w

theorem tendsto_powBaseEps (e eb : ℤ) (v : ℝ) :
    Filter.Tendsto (powBaseEps e eb v) Filter.atTop (nhds 0) := by
  unfold powBaseEps expOfBracketEps
  have h1 := tendsto_expEps v
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 := (((tendsto_mulLnEps e eb).const_mul 24).add (hu.div_const 4)).const_mul (Real.exp v)
  simp only [mul_zero, zero_div, add_zero] at h2
  have := h1.add h2
  rwa [add_zero] at this

/-- `u^x = exp (x ln u)` for `u > 0`. -/
theorem natCast_rpow_eq_exp {u : ℕ} (hu : 0 < u) (xv : ℝ) :
    (u : ℝ) ^ xv = Real.exp (xv * Real.log u) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hu), mul_comm]

/-- `powBaseW₀ e u` as an integer. -/
theorem powBaseW₀_eq (e : AzInt) (u : UInt64) :
    ((powBaseW₀ e u : ℕ) : ℤ) = 136 + max e.toInt 0 + |((baseFloat u).exponent?.getD 0).toInt| := by
  unfold powBaseW₀
  rw [Nat.cast_add, Nat.cast_add, expPos_eq_max, AzInt.abs_toNat_eq]
  push_cast
  ring

/-- `powBaseBracket x e u w` encloses `u^x` for `|x| < 2^e`, `2 ≤ u` and `w ≥ powBaseW₀ e u`,
with width at most `powBaseEps e eb (x ln u) w`. -/
theorem powBaseBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (e : AzInt) (hxe : |xv| < (2 : ℝ) ^ e.toInt) (u : UInt64) (hu : 2 ≤ u.toNat) {w : ℕ}
    (hw : powBaseW₀ e u ≤ w) :
    ∃ lo hi : ℝ, (powBaseBracket x e u w).1.toVal = some (lo : EReal) ∧
      (powBaseBracket x e u w).2.toVal = some (hi : EReal) ∧
      lo ≤ (u.toNat : ℝ) ^ xv ∧ (u.toNat : ℝ) ^ xv ≤ hi ∧
      hi - lo ≤ powBaseEps e.toInt ((baseFloat u).exponent?.getD 0).toInt (xv * Real.log u.toNat)
        w := by
  have hw64 : 64 ≤ w := by unfold powBaseW₀ at hw; omega
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnBaseMulBracket_spec hx e hxe u hu w hw64
  have hwZ : 136 + max e.toInt 0 + |((baseFloat u).exponent?.getD 0).toInt| ≤ (w : ℤ) := by
    rw [← powBaseW₀_eq]; exact_mod_cast hw
  have hw1 : hi - lo ≤ 1 := hwid.trans (mulLnEps_le_one _ _ _ hwZ)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw64
  rw [natCast_rpow_eq_exp (by omega)]
  refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
  unfold powBaseEps
  refine hab.trans ?_
  unfold expOfBracketEps
  have := Real.exp_pos (xv * Real.log u.toNat)
  nlinarith

/-! ### The exact powers -/

/-- `powBaseExact? x u = some (r, n)`: `r` is the primitive root of `u` and `u^x = r^n`. -/
theorem powBaseExact?_some (x : AzFloat) (u : AzNat) (hu : 2 ≤ u.toNat) {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {r : AzNat} {n : AzInt}
    (h : powBaseExact? x u = some (r, n)) :
    r = (maxRootBase u).1 ∧ (u.toNat : ℝ) ^ xv = (r.toNat : ℝ) ^ n.toInt := by
  obtain ⟨hcs, -, hc2, -⟩ := maxRootBase_spec u hu
  unfold powBaseExact? at h
  cases hq : x.toAzRat? with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    simp only [] at h
    split_ifs at h with hden
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hr, hn⟩ := h
    refine ⟨hr.symm, ?_⟩
    have hval := toVal_of_toAzRat? x q hq
    rw [hx, Option.some.injEq, EReal.coe_eq_coe_iff] at hval
    obtain ⟨y, hy⟩ : ∃ y : AzRat, y = q * (AzNat.ofNat (maxRootBase u).2).toAzRat := ⟨_, rfl⟩
    rw [← hy] at hden hn
    have hden' : y.den.toNat = 1 := by rw [hden]; exact AzNat.toNat_one
    have hyv : (AzRat.toRat y : ℝ) = (n.toInt : ℝ) := by
      rw [AzRat.toRat_cast_eq, hden', Nat.cast_one, div_one, ← hn, toInt_mkNorm]
    have hyq : (AzRat.toRat y : ℝ) = xv * (maxRootBase u).2 := by
      rw [hy, AzRat.toRat_mul, AzRat.toRat_toAzRat, AzNat.toNat_ofNat, Rat.cast_mul,
        Rat.cast_natCast, hval]
    have hr0 : (0 : ℝ) ≤ (maxRootBase u).1.toNat := by positivity
    rw [← hr, hcs, Nat.cast_pow, ← Real.rpow_natCast_mul hr0, mul_comm, ← hyq, hyv,
      Real.rpow_intCast]

/-- `powBaseExact? = none` for a finite float: `u^x` is irrational. -/
theorem irrational_of_powBaseExact?_none (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (u : AzNat) (hu : 2 ≤ u.toNat) (hu64 : u.toNat < 2 ^ 64)
    (h : powBaseExact? (finite s e q m hv) u = none) :
    Irrational ((u.toNat : ℝ) ^ finiteVal s e m) := by
  obtain ⟨hcs, -, hc2, -⟩ := maxRootBase_spec u hu
  have hnotpow := maxRootBase_not_pow u hu hu64
  obtain ⟨qr, hqr⟩ : ∃ qr, (finite s e q m hv).toAzRat? = some qr := ⟨_, rfl⟩
  have hval := toVal_of_toAzRat? _ qr hqr
  rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hval
  unfold powBaseExact? at h
  rw [hqr] at h
  simp only [] at h
  split_ifs at h with hden
  obtain ⟨y, hy⟩ : ∃ y : AzRat, y = qr * (AzNat.ofNat (maxRootBase u).2).toAzRat := ⟨_, rfl⟩
  rw [← hy] at hden
  have hyq : (AzRat.toRat y : ℝ) = finiteVal s e m * (maxRootBase u).2 := by
    rw [hy, AzRat.toRat_mul, AzRat.toRat_toAzRat, AzNat.toNat_ofNat, Rat.cast_mul,
      Rat.cast_natCast, hval]
  have hr0 : (0 : ℝ) ≤ (maxRootBase u).1.toNat := by positivity
  have hsplit : (u.toNat : ℝ) ^ finiteVal s e m
      = ((maxRootBase u).1.toNat : ℝ) ^ (AzRat.toRat y : ℝ) := by
    rw [hcs, Nat.cast_pow, ← Real.rpow_natCast_mul hr0, mul_comm, ← hyq]
  rw [hsplit]
  obtain ⟨N, J, hNJ⟩ := exists_dyadic_of_finiteVal s e m
  refine irrational_rpow_of_rat_of_not_pow hc2 hnotpow (N := N * (maxRootBase u).2)
    (D := 2 ^ J) (by positivity) ?_ ?_
  · rw [hyq]
    push_cast
    rw [mul_right_comm, hNJ]
  · rintro ⟨z, hz⟩
    apply hden
    have hq : AzRat.toRat y = (z : ℚ) := by exact_mod_cast hz
    have := congrArg Rat.den hq
    rw [Rat.den_intCast] at this
    exact AzNat.toNat_injective (by rw [AzNat.toNat_one]; exact this)

/-! ### The Ziv loop -/

/-- `powBaseApprox` is a strict enclosure of `u^x` when `powBaseExact? = none`, with width at
most `powBaseEps`. -/
theorem powBaseApprox_spec {w : ℕ} (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (u : UInt64) (hu : 2 ≤ u.toNat)
    (hirr : Irrational ((u.toNat : ℝ) ^ finiteVal s e m)) (hw : powBaseW₀ e u ≤ w) :
    ∃ lv hv' : ℝ, Rounds (powBaseApprox (finite s e q m hv) e u w).1 lv ∧
      Rounds (powBaseApprox (finite s e q m hv) e u w).2 hv' ∧
      lv < (u.toNat : ℝ) ^ finiteVal s e m ∧ (u.toNat : ℝ) ^ finiteVal s e m < hv' ∧
      hv' - lv ≤ powBaseEps e.toInt ((baseFloat u).exponent?.getD 0).toInt
        (finiteVal s e m * Real.log u.toNat) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ :=
    powBaseBracket_spec (toVal_finite s e q m hv) e (abs_finiteVal_bounds s e hv).2 u hu hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 hirr
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `u^x`. -/
theorem powBaseApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (s : Bool)
    (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (u : UInt64) (hu : 2 ≤ u.toNat)
    (hirr : Irrational ((u.toNat : ℝ) ^ finiteVal s e m)) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (powBaseApprox (finite s e q m hv) e u (w₀ * 2 ^ f)).1
      (powBaseApprox (finite s e q m hv) e u (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (powBaseApprox (finite s e q m hv) e u) hirr
    (powBaseEps e.toInt ((baseFloat u).exponent?.getD 0).toInt
      (finiteVal s e m * Real.log u.toNat))
    (tendsto_powBaseEps _ _ _) (powBaseW₀ e u)
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := powBaseApprox_spec s e hv u hu hirr hw
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-! ### The rational exponent -/

set_option maxHeartbeats 1000000 in
/-- `lnBaseMulRatBracket q u w` encloses `q ln u` with width at most
`mulLnEps (size (num q)) eb w`, for `2 ≤ u`. -/
theorem lnBaseMulRatBracket_spec (q : AzRat) (u : UInt64) (hu : 2 ≤ u.toNat) (w : ℕ)
    (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (lnBaseMulRatBracket q u w).1.toVal = some (lo : EReal) ∧
      (lnBaseMulRatBracket q u w).2.toVal = some (hi : EReal) ∧
      lo ≤ (AzRat.toRat q : ℝ) * Real.log u.toNat ∧
      (AzRat.toRat q : ℝ) * Real.log u.toNat ≤ hi ∧
      hi - lo ≤ mulLnEps (q.num.size : ℤ) ((baseFloat u).exponent?.getD 0).toInt w := by
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = w + 16 + q.num.size := ⟨_, rfl⟩
  have : NeZero W := ⟨by omega⟩
  obtain ⟨qv, hqv⟩ : ∃ qv : ℝ, qv = (AzRat.toRat q : ℝ) := ⟨_, rfl⟩
  obtain ⟨uu, huu⟩ : ∃ uu : ℝ, uu = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have huu0 : 0 < uu := by rw [huu]; positivity
  have huu1 : uu ≤ 1 := by rw [huu]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hqs : |qv| < (2 : ℝ) ^ q.num.size := by
    have h := abs_toRat_lt q
    rw [zpow_natCast, ← hqv] at h
    exact h
  have hs0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ q.num.size := by positivity
  have hs1 : (2 : ℝ) ^ q.num.size * (1 / 2 : ℝ) ^ q.num.size = 1 := by
    rw [one_div_pow, mul_one_div, div_self (by positivity)]
  have hδ : (1 / 2 : ℝ) ^ W = uu * (1 / 65536) * (1 / 2 : ℝ) ^ q.num.size := by
    rw [hW, pow_add, pow_add, huu, show ((1 : ℝ) / 2) ^ 16 = 1 / 65536 by norm_num]
  have hX : |qv| * (1 / 2 : ℝ) ^ W ≤ uu / 65536 := by
    rw [hδ]
    have := mul_le_mul_of_nonneg_right hqs.le hs0
    rw [hs1] at this
    calc |qv| * (uu * (1 / 65536) * (1 / 2 : ℝ) ^ q.num.size)
        = uu / 65536 * (|qv| * (1 / 2 : ℝ) ^ q.num.size) := by ring
      _ ≤ uu / 65536 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = uu / 65536 := mul_one _
  have hδ0 : 0 ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hW64 : (1 / 2 : ℝ) ^ W ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  -- the bracket of `ln u` and the floats around `|q|`
  obtain ⟨eb, heb⟩ : ∃ eb : ℤ, eb = ((baseFloat u).exponent?.getD 0).toInt := ⟨_, rfl⟩
  obtain ⟨c, d, hc, hd, hc0, hcM, hMd, hcd⟩ := lnBaseBracket_spec (by omega : 64 ≤ W) u hu
  rw [← heb] at hcd
  have hlog45 : Real.log u.toNat < 45 := log_lt_45_of_lt_two_pow_64 u.toBitVec.isLt
  have hc1 : 0 ≤ c := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hc45 : c ≤ 45 := by linarith
  have hlnE0 : 0 ≤ lnEps eb W := by unfold lnEps; positivity
  have hd45 : d ≤ 45 + lnEps eb W := by linarith
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |qv| := by
    rw [AzRat.toRat_abs, Rat.cast_abs, hqv]
  obtain ⟨a, ha, ha1, ha2⟩ := ofAzRatRound_floor_abs q.abs W
  obtain ⟨b, hb, hb1, hb2⟩ := ofAzRatRound_ceiling_abs q.abs W
  rw [habs] at ha1 ha2 hb1 hb2
  simp only [abs_abs] at ha2 hb2
  have hka0 : 0 ≤ |qv| := abs_nonneg _
  have hqδ : 2 * |qv| * (1 / 2 : ℝ) ^ W ≤ 2 * |qv| * (1 / 64) :=
    mul_le_mul_of_nonneg_left hW64 (by positivity)
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hb2' : b ≤ 2 * |qv| := by linarith
  have hba : b - a ≤ 4 * |qv| * (1 / 2 : ℝ) ^ W := by linarith
  obtain ⟨plo, hplo, hplo1⟩ := mulFloor_err ha hc W (mul_nonneg ha0 hc1)
  obtain ⟨phi, hphi, hphi1⟩ := mulCeiling_err hb hd W (mul_nonneg hb0 hd0)
  have hln0 : 0 ≤ Real.log u.toNat := by linarith
  have hP1 : plo ≤ |qv| * Real.log u.toNat :=
    hplo1.le.trans (mul_le_mul ha1 hcM hc1 hka0)
  have hP2 : |qv| * Real.log u.toNat ≤ phi :=
    (mul_le_mul hb1 hMd hln0 hb0).trans hphi1.ge
  -- the width: `b d − a c = b (d − c) + (b − a) c`, plus the roundings
  have hkey : |qv| * lnEps eb W ≤ lnEps (|eb| + 16 + max (q.num.size : ℤ) 0) w / 65536 := by
    unfold lnEps
    have hpoly : ((W : ℕ) : ℝ) + |(eb : ℝ)| + 8
        = (w : ℝ) + |((|eb| + 16 + max (q.num.size : ℤ) 0 : ℤ) : ℝ)| + 8 := by
      rw [max_eq_left (by positivity), hW]
      push_cast
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |(eb : ℝ)| + 16 + q.num.size)]
      ring
    rw [hpoly]
    have hP0 : 0 ≤ (2 : ℝ) ^ 40
        * ((w : ℝ) + |((|eb| + 16 + max (q.num.size : ℤ) 0 : ℤ) : ℝ)| + 8) ^ 5 := by
      positivity
    rw [← huu]
    calc |qv| * (2 ^ 40 * ((w : ℝ) + |((|eb| + 16 + max (q.num.size : ℤ) 0 : ℤ) : ℝ)| + 8) ^ 5
          * (1 / 2 : ℝ) ^ W)
        = 2 ^ 40 * ((w : ℝ) + |((|eb| + 16 + max (q.num.size : ℤ) 0 : ℤ) : ℝ)| + 8) ^ 5
          * (|qv| * (1 / 2 : ℝ) ^ W) := by ring
      _ ≤ 2 ^ 40 * ((w : ℝ) + |((|eb| + 16 + max (q.num.size : ℤ) 0 : ℤ) : ℝ)| + 8) ^ 5
          * (uu / 65536) := mul_le_mul_of_nonneg_left hX hP0
      _ = _ := by ring
  have h8 : lnEps eb W ≤ lnEps (|eb| + 16 + max (q.num.size : ℤ) 0) w := by
    unfold lnEps
    have hpoly : ((W : ℕ) : ℝ) + |(eb : ℝ)| + 8
        = (w : ℝ) + |((|eb| + 16 + max (q.num.size : ℤ) 0 : ℤ) : ℝ)| + 8 := by
      rw [max_eq_left (by positivity), hW]
      push_cast
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |(eb : ℝ)| + 16 + q.num.size)]
      ring
    rw [hpoly]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hL0 : 0 ≤ lnEps (|eb| + 16 + max (q.num.size : ℤ) 0) w := by unfold lnEps; positivity
  have hpwid : phi - plo ≤ mulLnEps (q.num.size : ℤ) eb w := by
    unfold mulLnEps
    rw [← huu]
    have h1 := hplo1.ge
    have h2 := hphi1.le
    -- `b (d − c) ≤ 2|q| lnEps`, `(b − a) c ≤ 4|q| δ · 45`
    have h3 : b * (d - c) ≤ 2 * |qv| * lnEps eb W :=
      mul_le_mul hb2' hcd (by linarith) (by positivity)
    have h4 : (b - a) * c ≤ 4 * |qv| * (1 / 2 : ℝ) ^ W * 45 :=
      mul_le_mul hba hc45 hc1 (by positivity)
    have hid : b * d - a * c = b * (d - c) + (b - a) * c := by ring
    -- the roundings: `2 b d δ ≤ 2 · 2|q| (45 + lnEps) δ`, `2 a c δ ≤ 2 |q| 45 δ`
    have h5 : b * d ≤ 2 * |qv| * (45 + lnEps eb W) := mul_le_mul hb2' hd45 hd0 (by positivity)
    have h6 : a * c ≤ |qv| * 45 := mul_le_mul ha1 hc45 hc1 hka0
    have h7 : 2 * (b * d) * (1 / 2 : ℝ) ^ W
        ≤ 2 * (2 * |qv| * (45 + lnEps eb W)) * (1 / 2 : ℝ) ^ W :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0
    have h9 : 2 * (a * c) * (1 / 2 : ℝ) ^ W ≤ 2 * (|qv| * 45) * (1 / 2 : ℝ) ^ W :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0
    have h10 : 2 * (2 * |qv| * (45 + lnEps eb W)) * (1 / 2 : ℝ) ^ W
        = 180 * (|qv| * (1 / 2 : ℝ) ^ W) + 4 * (lnEps eb W * (|qv| * (1 / 2 : ℝ) ^ W)) := by
      ring
    have h11 : lnEps eb W * (|qv| * (1 / 2 : ℝ) ^ W) ≤ lnEps eb W * (uu / 65536) :=
      mul_le_mul_of_nonneg_left hX hlnE0
    have h12 : lnEps eb W * (uu / 65536)
        ≤ lnEps (|eb| + 16 + max (q.num.size : ℤ) 0) w * (uu / 65536) :=
      mul_le_mul_of_nonneg_right h8 (by positivity)
    have h13 : lnEps (|eb| + 16 + max (q.num.size : ℤ) 0) w * (uu / 65536)
        ≤ lnEps (|eb| + 16 + max (q.num.size : ℤ) 0) w * (1 / 65536) :=
      mul_le_mul_of_nonneg_left (by linarith) hL0
    have h14 : 4 * |qv| * (1 / 2 : ℝ) ^ W * 45 = 180 * (|qv| * (1 / 2 : ℝ) ^ W) := by ring
    have h15 : 2 * (|qv| * 45) * (1 / 2 : ℝ) ^ W = 90 * (|qv| * (1 / 2 : ℝ) ^ W) := by ring
    nlinarith
  -- the sign of `q`
  simp only [lnBaseMulRatBracket, absMulRatBracket]
  rw [← hW, ← hqv, ← heb]
  split_ifs with hs
  · have hq0 : 0 ≤ qv := by rw [hqv]; exact toRat_nonneg_of_sign q hs
    have hax : |qv| = qv := abs_of_nonneg hq0
    refine ⟨plo, phi, hplo, hphi, ?_, ?_, hpwid⟩
    · rw [hax] at hP1; exact hP1
    · rw [hax] at hP2; exact hP2
  · have hqneg : qv < 0 := by rw [hqv]; exact toRat_neg_of_sign' q (by simpa using hs)
    have hax : |qv| = -qv := abs_of_neg hqneg
    have hnphi : (-(mulPrecRound (ofAzRatRound q.abs W .Ceiling).1 (lnBaseBracket u W).2 W
        .Ceiling).1).toVal = some ((-phi : ℝ) : EReal) := by
      rw [toVal_neg, hphi, Option.map_some, EReal.coe_neg]
    have hnplo : (-(mulPrecRound (ofAzRatRound q.abs W .Floor).1 (lnBaseBracket u W).1 W
        .Floor).1).toVal = some ((-plo : ℝ) : EReal) := by
      rw [toVal_neg, hplo, Option.map_some, EReal.coe_neg]
    refine ⟨-phi, -plo, hnphi, hnplo, ?_, ?_, ?_⟩
    · rw [hax] at hP2; linarith
    · rw [hax] at hP1; linarith
    · linarith

/-- `powBaseRatW₀ q u` as an integer. -/
theorem powBaseRatW₀_eq (q : AzRat) (u : UInt64) :
    ((powBaseRatW₀ q u : ℕ) : ℤ)
      = 136 + max (q.num.size : ℤ) 0 + |((baseFloat u).exponent?.getD 0).toInt| := by
  unfold powBaseRatW₀
  rw [Nat.cast_add, Nat.cast_add, AzInt.abs_toNat_eq, max_eq_left (by positivity)]
  push_cast
  ring

/-- `powBaseRatBracket q u w` encloses `u^q` for `2 ≤ u` and `w ≥ powBaseRatW₀ q u`, with
width at most `powBaseEps (size (num q)) eb (q ln u) w`. -/
theorem powBaseRatBracket_spec (q : AzRat) (u : UInt64) (hu : 2 ≤ u.toNat) {w : ℕ}
    (hw : powBaseRatW₀ q u ≤ w) :
    ∃ lo hi : ℝ, (powBaseRatBracket q u w).1.toVal = some (lo : EReal) ∧
      (powBaseRatBracket q u w).2.toVal = some (hi : EReal) ∧
      lo ≤ (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) ∧ (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) ≤ hi ∧
      hi - lo ≤ powBaseEps (q.num.size : ℤ) ((baseFloat u).exponent?.getD 0).toInt
        ((AzRat.toRat q : ℝ) * Real.log u.toNat) w := by
  have hw64 : 64 ≤ w := by unfold powBaseRatW₀ at hw; omega
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnBaseMulRatBracket_spec q u hu w hw64
  have hwZ : 136 + max (q.num.size : ℤ) 0 + |((baseFloat u).exponent?.getD 0).toInt|
      ≤ (w : ℤ) := by
    rw [← powBaseRatW₀_eq]; exact_mod_cast hw
  have hw1 : hi - lo ≤ 1 := hwid.trans (mulLnEps_le_one _ _ _ hwZ)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw64
  rw [natCast_rpow_eq_exp (by omega)]
  refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
  unfold powBaseEps
  refine hab.trans ?_
  unfold expOfBracketEps
  have := Real.exp_pos ((AzRat.toRat q : ℝ) * Real.log u.toNat)
  nlinarith

/-- `powBaseRatExact? q u = some (r, n)`: `r` is the primitive root of `u` and `u^q = r^n`. -/
theorem powBaseRatExact?_some (q : AzRat) (u : AzNat) (hu : 2 ≤ u.toNat) {r : AzNat}
    {n : AzInt} (h : powBaseRatExact? q u = some (r, n)) :
    r = (maxRootBase u).1 ∧ (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) = (r.toNat : ℝ) ^ n.toInt := by
  obtain ⟨hcs, -, hc2, -⟩ := maxRootBase_spec u hu
  unfold powBaseRatExact? at h
  simp only [] at h
  split_ifs at h with hden
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hr, hn⟩ := h
  refine ⟨hr.symm, ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : AzRat, y = q * (AzNat.ofNat (maxRootBase u).2).toAzRat := ⟨_, rfl⟩
  rw [← hy] at hden hn
  have hden' : y.den.toNat = 1 := by rw [hden]; exact AzNat.toNat_one
  have hyv : (AzRat.toRat y : ℝ) = (n.toInt : ℝ) := by
    rw [AzRat.toRat_cast_eq, hden', Nat.cast_one, div_one, ← hn, toInt_mkNorm]
  have hyq : (AzRat.toRat y : ℝ) = (AzRat.toRat q : ℝ) * (maxRootBase u).2 := by
    rw [hy, AzRat.toRat_mul, AzRat.toRat_toAzRat, AzNat.toNat_ofNat, Rat.cast_mul,
      Rat.cast_natCast]
  have hr0 : (0 : ℝ) ≤ (maxRootBase u).1.toNat := by positivity
  rw [← hr, hcs, Nat.cast_pow, ← Real.rpow_natCast_mul hr0, mul_comm, ← hyq, hyv,
    Real.rpow_intCast]

/-- `powBaseRatExact? = none`: `u^q` is irrational. -/
theorem irrational_of_powBaseRatExact?_none (q : AzRat) (u : AzNat) (hu : 2 ≤ u.toNat)
    (hu64 : u.toNat < 2 ^ 64) (h : powBaseRatExact? q u = none) :
    Irrational ((u.toNat : ℝ) ^ (AzRat.toRat q : ℝ)) := by
  obtain ⟨hcs, -, hc2, -⟩ := maxRootBase_spec u hu
  have hnotpow := maxRootBase_not_pow u hu hu64
  unfold powBaseRatExact? at h
  simp only [] at h
  split_ifs at h with hden
  obtain ⟨y, hy⟩ : ∃ y : AzRat, y = q * (AzNat.ofNat (maxRootBase u).2).toAzRat := ⟨_, rfl⟩
  rw [← hy] at hden
  have hyq : (AzRat.toRat y : ℝ) = (AzRat.toRat q : ℝ) * (maxRootBase u).2 := by
    rw [hy, AzRat.toRat_mul, AzRat.toRat_toAzRat, AzNat.toNat_ofNat, Rat.cast_mul,
      Rat.cast_natCast]
  have hr0 : (0 : ℝ) ≤ (maxRootBase u).1.toNat := by positivity
  have hsplit : (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ)
      = ((maxRootBase u).1.toNat : ℝ) ^ (AzRat.toRat y : ℝ) := by
    rw [hcs, Nat.cast_pow, ← Real.rpow_natCast_mul hr0, mul_comm, ← hyq]
  rw [hsplit]
  have hD : 0 < y.den.toNat := AzRat.den_toNat_pos y
  refine irrational_rpow_of_rat_of_not_pow hc2 hnotpow
    (N := if y.sign then (y.num.toNat : ℤ) else -(y.num.toNat : ℤ)) (D := y.den.toNat) hD ?_ ?_
  · rw [AzRat.toRat_cast_eq]
    have : (y.den.toNat : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
  · rintro ⟨z, hz⟩
    apply hden
    have hq : AzRat.toRat y = (z : ℚ) := by exact_mod_cast hz
    have := congrArg Rat.den hq
    rw [Rat.den_intCast] at this
    exact AzNat.toNat_injective (by rw [AzNat.toNat_one]; exact this)

/-- `powBaseRatApprox` is a strict enclosure of `u^q` when `powBaseRatExact? = none`, with width
at most `powBaseEps`. -/
theorem powBaseRatApprox_spec {w : ℕ} (q : AzRat) (u : UInt64) (hu : 2 ≤ u.toNat)
    (hirr : Irrational ((u.toNat : ℝ) ^ (AzRat.toRat q : ℝ))) (hw : powBaseRatW₀ q u ≤ w) :
    ∃ lv hv : ℝ, Rounds (powBaseRatApprox q u w).1 lv ∧ Rounds (powBaseRatApprox q u w).2 hv ∧
      lv < (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) ∧ (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) < hv ∧
      hv - lv ≤ powBaseEps (q.num.size : ℤ) ((baseFloat u).exponent?.getD 0).toInt
        ((AzRat.toRat q : ℝ) * Real.log u.toNat) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := powBaseRatBracket_spec q u hu hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 hirr
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `u^q`. -/
theorem powBaseRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (u : UInt64) (hu : 2 ≤ u.toNat) (hirr : Irrational ((u.toNat : ℝ) ^ (AzRat.toRat q : ℝ)))
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (powBaseRatApprox q u (w₀ * 2 ^ f)).1
      (powBaseRatApprox q u (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (powBaseRatApprox q u) hirr
    (powBaseEps (q.num.size : ℤ) ((baseFloat u).exponent?.getD 0).toInt
      ((AzRat.toRat q : ℝ) * Real.log u.toNat))
    (tendsto_powBaseEps _ _ _) (powBaseRatW₀ q u)
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwidth⟩ := powBaseRatApprox_spec q u hu hirr hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-! ### `u^x − 1` -/

/-- The exponent `e + 6` as an integer. -/
theorem powBaseM1Exp_toInt (e : AzInt) : (powBaseM1Exp e).toInt = e.toInt + 6 := by
  unfold powBaseM1Exp
  rw [AzInt.toInt_add, AzInt.toInt_ofInt]

/-- The compensation `max(−e − 6, 0)` at the exponent `e + 6` satisfies
`c + max(e, 0) ≤ |e|`. -/
theorem expM1Comp_powBaseM1Exp_le (e : AzInt) :
    ((expM1Comp (powBaseM1Exp e) : ℕ) : ℤ) + max e.toInt 0 ≤ |e.toInt| := by
  have htoInt : (powBaseM1Exp e).toInt = e.toInt + 6 := powBaseM1Exp_toInt e
  have hsign : (powBaseM1Exp e).sign = true ↔ 0 ≤ (powBaseM1Exp e).toInt :=
    AzInt.sign_eq_true_iff _
  unfold expM1Comp
  split_ifs with hs
  · simp only [Nat.cast_zero, zero_add]
    exact max_le (le_abs_self _) (abs_nonneg _)
  · have h0 := (hsign.not.mp hs)
    push Not at h0
    rw [htoInt] at h0
    rw [AzInt.abs_toNat_eq, htoInt, abs_of_neg h0, max_eq_right (by omega),
      abs_of_neg (by omega)]
    omega

/-- The compensated width of a bracket of `x ln u` is at most `2^e / 4` from `136 + B + |eb|`
bits, where `B` bounds the compensation plus the exponent argument `E` of the width bound:
`(1/2)^(max(−e − 6, 0)) ≤ 64 · 2^e` and `2^53 w^5 + 2^8 ≤ 2^w`. -/
theorem mulLnEps_comp_le_of (E : ℤ) (e : AzInt) (eb : ℤ) (w : ℕ) (B : ℤ)
    (hcm : ((expM1Comp (powBaseM1Exp e) : ℕ) : ℤ) + max E 0 ≤ B)
    (hw : 136 + B + |eb| ≤ (w : ℤ)) :
    mulLnEps E eb (w + expM1Comp (powBaseM1Exp e)) ≤ (2 : ℝ) ^ e.toInt / 4 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = expM1Comp (powBaseM1Exp e) := ⟨_, rfl⟩
  have htoInt : (powBaseM1Exp e).toInt = e.toInt + 6 := powBaseM1Exp_toInt e
  have hsign : (powBaseM1Exp e).sign = true ↔ 0 ≤ (powBaseM1Exp e).toInt :=
    AzInt.sign_eq_true_iff _
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e.toInt := by positivity
  -- `(1/2)^c ≤ 64 · 2^e` and `c + max(E, 0) ≤ B`
  have hcz1 : (1 / 2 : ℝ) ^ c ≤ 64 * (2 : ℝ) ^ e.toInt := by
    rw [hc]
    unfold expM1Comp
    split_ifs with hs
    · have h0 := hsign.mp hs
      rw [htoInt] at h0
      have : (2 : ℝ) ^ (-6 : ℤ) ≤ (2 : ℝ) ^ e.toInt :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h6 : (2 : ℝ) ^ (-6 : ℤ) = 1 / 64 := by norm_num
      rw [h6] at this
      rw [pow_zero]
      linarith
    · have h0 := (hsign.not.mp hs)
      push Not at h0
      rw [htoInt] at h0
      have habs : ((powBaseM1Exp e).abs.toNat : ℤ) = -(e.toInt + 6) := by
        rw [AzInt.abs_toNat_eq, htoInt, abs_of_neg h0]
      have hpow : (1 / 2 : ℝ) ^ (powBaseM1Exp e).abs.toNat
          = (2 : ℝ) ^ (-((powBaseM1Exp e).abs.toNat : ℤ)) := by
        rw [zpow_neg, zpow_natCast, one_div_pow, one_div]
      have h6 : (2 : ℝ) ^ (6 : ℤ) = 64 := by norm_num
      rw [hpow, habs, neg_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), h6, mul_comm]
  have hcz2 : (c : ℤ) + max E 0 ≤ B := by rw [hc]; exact hcm
  rw [← hc]
  unfold mulLnEps lnEps
  have hw136 : 136 ≤ w := by
    have h1 : (0 : ℤ) ≤ (c : ℤ) + max E 0 := add_nonneg (by positivity) (le_max_right _ _)
    have h2 : (0 : ℤ) ≤ |eb| := abs_nonneg _
    omega
  have hwR : (136 : ℝ) + B + |(eb : ℝ)| ≤ w := by
    have : ((136 + B + |eb| : ℤ) : ℝ) ≤ ((w : ℤ) : ℝ) := by exact_mod_cast hw
    push_cast at this
    exact this
  have hcR : (c : ℝ) + max (E : ℝ) 0 ≤ B := by
    have := hcz2
    exact_mod_cast this
  have hE : ((|eb| + 16 + max E 0 : ℤ) : ℝ) = |(eb : ℝ)| + 16 + max (E : ℝ) 0 := by
    push_cast; ring
  rw [hE, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |(eb : ℝ)| + 16 + max (E : ℝ) 0)]
  have hpoly : ((w + c : ℕ) : ℝ) + (|(eb : ℝ)| + 16 + max (E : ℝ) 0) + 8 ≤ 2 * w := by
    push_cast; linarith
  have hpoly0 : (0 : ℝ) ≤ ((w + c : ℕ) : ℝ) + (|(eb : ℝ)| + 16 + max (E : ℝ) 0) + 8 := by
    positivity
  have h1 : (2 : ℝ) ^ 40 * (((w + c : ℕ) : ℝ) + (|(eb : ℝ)| + 16 + max (E : ℝ) 0) + 8) ^ 5
      ≤ 2 ^ 40 * (2 * w) ^ 5 := by gcongr
  have h2 : (2 : ℝ) ^ 40 * (2 * (w : ℝ)) ^ 5 = 2 ^ 45 * (w : ℝ) ^ 5 := by ring
  have h3 : (2 : ℝ) ^ 54 * (w : ℝ) ^ 5 ≤ 2 ^ w := by exact_mod_cast two_pow_54_mul_pow5_le hw136
  have hp : (0 : ℝ) < 2 ^ w := by positivity
  have hw1 : (1 : ℝ) ≤ (w : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ w))
  have hsplit : (1 / 2 : ℝ) ^ (w + c) = (1 / 2 : ℝ) ^ w * (1 / 2 : ℝ) ^ c := pow_add _ _ _
  have hhalf : (1 / 2 : ℝ) ^ w = 1 / 2 ^ w := by rw [one_div_pow]
  have hc0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ c := by positivity
  -- `(2^45 w^5 + 1) · 64 / 2^w ≤ 1/4`
  have hkey : ((2 : ℝ) ^ 45 * (w : ℝ) ^ 5 + 1) * (1 / 2 : ℝ) ^ w * 64 ≤ 1 / 4 := by
    rw [hhalf, ← div_eq_mul_one_div, div_mul_eq_mul_div, div_le_iff₀ hp]
    nlinarith
  have hP : (2 : ℝ) ^ 40 * (((w + c : ℕ) : ℝ) + (|(eb : ℝ)| + 16 + max (E : ℝ) 0) + 8) ^ 5
      ≤ 2 ^ 45 * (w : ℝ) ^ 5 := h1.trans h2.le
  have hP0 : (0 : ℝ) ≤ 2 ^ 40
      * (((w + c : ℕ) : ℝ) + (|(eb : ℝ)| + 16 + max (E : ℝ) 0) + 8) ^ 5 := by positivity
  rw [hsplit]
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  calc 2 ^ 40 * (((w + c : ℕ) : ℝ) + (|(eb : ℝ)| + 16 + max (E : ℝ) 0) + 8) ^ 5
        * ((1 / 2 : ℝ) ^ w * (1 / 2 : ℝ) ^ c) + (1 / 2 : ℝ) ^ w * (1 / 2 : ℝ) ^ c
      = (2 ^ 40 * (((w + c : ℕ) : ℝ) + (|(eb : ℝ)| + 16 + max (E : ℝ) 0) + 8) ^ 5 + 1)
        * (1 / 2 : ℝ) ^ w * (1 / 2 : ℝ) ^ c := by ring
    _ ≤ (2 ^ 45 * (w : ℝ) ^ 5 + 1) * (1 / 2 : ℝ) ^ w * (64 * (2 : ℝ) ^ e.toInt) := by
      apply mul_le_mul _ hcz1 hc0 (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) hu0
    _ = ((2 ^ 45 * (w : ℝ) ^ 5 + 1) * (1 / 2 : ℝ) ^ w * 64) * (2 : ℝ) ^ e.toInt := by ring
    _ ≤ 1 / 4 * (2 : ℝ) ^ e.toInt := mul_le_mul_of_nonneg_right hkey h2e.le
    _ = (2 : ℝ) ^ e.toInt / 4 := by ring

/-- The compensated width of the `x ln u` bracket is at most `2^e / 4` from
`136 + |e| + |eb|` bits. -/
theorem mulLnEps_comp_le (e : AzInt) (eb : ℤ) (w : ℕ) (hw : 136 + |e.toInt| + |eb| ≤ (w : ℤ)) :
    mulLnEps e.toInt eb (w + expM1Comp (powBaseM1Exp e)) ≤ (2 : ℝ) ^ e.toInt / 4 :=
  mulLnEps_comp_le_of e.toInt e eb w |e.toInt| (expM1Comp_powBaseM1Exp_le e) hw

/-- The width bound of `powBaseM1Bracket` at compensation `c` and the value `v = x ln u`. -/
noncomputable def powBaseM1Eps (e eb : ℤ) (c : ℕ) (v : ℝ) (w : ℕ) : ℝ :=
  expM1RatEps v c w + 32 * Real.exp v * mulLnEps e eb (w + c)

theorem tendsto_powBaseM1Eps (e eb : ℤ) (c : ℕ) (v : ℝ) :
    Filter.Tendsto (powBaseM1Eps e eb c v) Filter.atTop (nhds 0) := by
  unfold powBaseM1Eps
  have h1 := tendsto_expM1RatEps v c
  have h2 := ((tendsto_mulLnEps e eb).comp (Filter.tendsto_add_atTop_nat c)).const_mul
    (32 * Real.exp v)
  rw [mul_zero] at h2
  have := h1.add h2
  rwa [add_zero] at this

/-- `powBaseM1W₀ e u` as an integer. -/
theorem powBaseM1W₀_eq (e : AzInt) (u : UInt64) :
    ((powBaseM1W₀ e u : ℕ) : ℤ)
      = 136 + |e.toInt| + |((baseFloat u).exponent?.getD 0).toInt| := by
  unfold powBaseM1W₀
  rw [Nat.cast_add, Nat.cast_add, AzInt.abs_toNat_eq, AzInt.abs_toNat_eq]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- `powBaseM1Bracket x e u w` encloses `u^x − 1` for `2^(e−1) ≤ |x| < 2^e`, `2 ≤ u` and
`w ≥ powBaseM1W₀ e u`, with width at most `powBaseM1Eps`. -/
theorem powBaseM1Bracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (e : AzInt) (hxe : |xv| < (2 : ℝ) ^ e.toInt) (hxe1 : (2 : ℝ) ^ e.toInt ≤ 2 * |xv|)
    (u : UInt64) (hu : 2 ≤ u.toNat) {w : ℕ} (hw : powBaseM1W₀ e u ≤ w) :
    ∃ lo hi : ℝ, (powBaseM1Bracket x e u w).1.toVal = some (lo : EReal) ∧
      (powBaseM1Bracket x e u w).2.toVal = some (hi : EReal) ∧
      lo ≤ (u.toNat : ℝ) ^ xv - 1 ∧ (u.toNat : ℝ) ^ xv - 1 ≤ hi ∧
      hi - lo ≤ powBaseM1Eps e.toInt ((baseFloat u).exponent?.getD 0).toInt
        (expM1Comp (powBaseM1Exp e)) (xv * Real.log u.toNat) w := by
  have hw64 : 64 ≤ w := by unfold powBaseM1W₀ at hw; omega
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = expM1Comp (powBaseM1Exp e) := ⟨_, rfl⟩
  obtain ⟨eb, heb⟩ : ∃ eb : ℤ, eb = ((baseFloat u).exponent?.getD 0).toInt := ⟨_, rfl⟩
  have hwZ : 136 + |e.toInt| + |eb| ≤ (w : ℤ) := by
    rw [heb, ← powBaseM1W₀_eq]; exact_mod_cast hw
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnBaseMulBracket_spec hx e hxe u hu (w + c) (by omega)
  rw [← heb] at hwid
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = mulLnEps e.toInt eb (w + c) := ⟨_, rfl⟩
  rw [← hδ] at hwid
  have hδ0 : 0 ≤ δ := by rw [hδ]; unfold mulLnEps lnEps; positivity
  have hδ1 : δ ≤ 1 / 64 := by
    rw [hδ]
    refine (mulLnEps_le_inv256 e.toInt eb (w + c) ?_).trans (by norm_num)
    have h1 : max e.toInt 0 ≤ |e.toInt| := by
      rcases le_or_gt e.toInt 0 with h | h
      · rw [max_eq_right h]; positivity
      · rw [max_eq_left h.le]; exact le_abs_self _
    push_cast
    omega
  have hδe : δ ≤ (2 : ℝ) ^ e.toInt / 4 := by rw [hδ, hc]; exact mulLnEps_comp_le e eb w hwZ
  -- the value and its size: `0.69 |x| ≤ |v| < 45 |x|`
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = xv * Real.log u.toNat := ⟨_, rfl⟩
  rw [← hv] at h1 h2
  have hlog45 : Real.log u.toNat < 45 := log_lt_45_of_lt_two_pow_64 u.toBitVec.isLt
  have hlog2 : Real.log 2 ≤ Real.log u.toNat :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hu)
  have hln1 := Real.log_two_gt_d9
  have habsv : |v| = |xv| * Real.log u.toNat := by
    rw [hv, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log u.toNat)]
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e.toInt := by positivity
  have hxv0 := abs_nonneg xv
  have hlo_e : |lo| < (2 : ℝ) ^ (powBaseM1Exp e).toInt := by
    rw [powBaseM1Exp_toInt, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : |lo| ≤ |v| + δ := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le v, le_abs_self v]
    have h3 : |v| ≤ |xv| * 45 := by rw [habsv]; nlinarith
    have h4 : (2 : ℝ) ^ (6 : ℤ) = 64 := by norm_num
    rw [h4]
    nlinarith
  have hlo_v : |lo| ≤ 2 * |v| := by
    have : |lo| ≤ |v| + δ := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le v, le_abs_self v]
    have h3 : |xv| * (6 / 10) ≤ |v| := by rw [habsv]; nlinarith
    linarith
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expM1OfBracket_spec_of_bounds (powBaseM1Exp e) hlo hhi
    h1 h2 hwid hδ0 hδ1 hlo_e hlo_v hw64
  simp only [powBaseM1Bracket]
  rw [natCast_rpow_eq_exp (by omega), ← hv, ← hc, ← heb]
  rw [← hc] at hab
  refine ⟨a, b, ha, hb, ha1, hb1, hab.trans ?_⟩
  unfold powBaseM1Eps
  rw [← hδ]
  have hslack := expM1RatEps_slack v c w
  have hEvp := Real.exp_pos v
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have := mul_nonneg hEvp.le hu0
  linarith

/-- `powBaseM1Approx` is a strict enclosure of `u^x − 1` (given its irrationality), with width
at most `powBaseM1Eps`. -/
theorem powBaseM1Approx_spec {w : ℕ} (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (u : UInt64) (hu : 2 ≤ u.toNat)
    (hirr : Irrational ((u.toNat : ℝ) ^ finiteVal s e m - 1)) (hw : powBaseM1W₀ e u ≤ w) :
    ∃ lv hv' : ℝ, Rounds (powBaseM1Approx (finite s e q m hv) e u w).1 lv ∧
      Rounds (powBaseM1Approx (finite s e q m hv) e u w).2 hv' ∧
      lv < (u.toNat : ℝ) ^ finiteVal s e m - 1 ∧ (u.toNat : ℝ) ^ finiteVal s e m - 1 < hv' ∧
      hv' - lv ≤ powBaseM1Eps e.toInt ((baseFloat u).exponent?.getD 0).toInt
        (expM1Comp (powBaseM1Exp e)) (finiteVal s e m * Real.log u.toNat) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := powBaseM1Bracket_spec (toVal_finite s e q m hv) e
    (abs_finiteVal_bounds s e hv).2 (two_zpow_le_two_mul_abs_finiteVal s e hv) u hu hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 hirr
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `u^x − 1`. -/
theorem powBaseM1Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (s : Bool)
    (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (u : UInt64) (hu : 2 ≤ u.toNat)
    (hirr : Irrational ((u.toNat : ℝ) ^ finiteVal s e m - 1)) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (powBaseM1Approx (finite s e q m hv) e u (w₀ * 2 ^ f)).1
      (powBaseM1Approx (finite s e q m hv) e u (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (powBaseM1Approx (finite s e q m hv) e u) hirr
    (powBaseM1Eps e.toInt ((baseFloat u).exponent?.getD 0).toInt (expM1Comp (powBaseM1Exp e))
      (finiteVal s e m * Real.log u.toNat))
    (tendsto_powBaseM1Eps _ _ _ _) (powBaseM1W₀ e u)
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := powBaseM1Approx_spec s e hv u hu hirr hw
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-- `u^x − 1` is irrational when `powBaseExact? = none`. -/
theorem irrational_sub_one_of_powBaseExact?_none (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (u : AzNat) (hu : 2 ≤ u.toNat) (hu64 : u.toNat < 2 ^ 64)
    (h : powBaseExact? (finite s e q m hv) u = none) :
    Irrational ((u.toNat : ℝ) ^ finiteVal s e m - 1) := by
  have h' := (irrational_of_powBaseExact?_none s e hv u hu hu64 h).sub_intCast 1
  rwa [Int.cast_one] at h'

/-! ### `u^q − 1` -/

/-- `powBaseM1RatW₀ q u` as an integer. -/
theorem powBaseM1RatW₀_eq (q : AzRat) (u : UInt64) :
    ((powBaseM1RatW₀ q u : ℕ) : ℤ) = 136 + (|(pow2M1RatExp q).toInt| + q.num.size)
      + |((baseFloat u).exponent?.getD 0).toInt| := by
  unfold powBaseM1RatW₀
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, AzInt.abs_toNat_eq, AzInt.abs_toNat_eq]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- `powBaseM1RatBracket q u w` encloses `u^q − 1` for `q ≠ 0`, `2 ≤ u` and
`w ≥ powBaseM1RatW₀ q u`, with width at most `powBaseM1Eps`. -/
theorem powBaseM1RatBracket_spec (q : AzRat) (h0 : q.num ≠ 0) (u : UInt64) (hu : 2 ≤ u.toNat)
    {w : ℕ} (hw : powBaseM1RatW₀ q u ≤ w) :
    ∃ lo hi : ℝ, (powBaseM1RatBracket q u w).1.toVal = some (lo : EReal) ∧
      (powBaseM1RatBracket q u w).2.toVal = some (hi : EReal) ∧
      lo ≤ (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1 ∧
      (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1 ≤ hi ∧
      hi - lo ≤ powBaseM1Eps (q.num.size : ℤ) ((baseFloat u).exponent?.getD 0).toInt
        (expM1Comp (powBaseM1Exp (pow2M1RatExp q))) ((AzRat.toRat q : ℝ) * Real.log u.toNat)
        w := by
  have hw64 : 64 ≤ w := by unfold powBaseM1RatW₀ at hw; omega
  obtain ⟨e, he⟩ : ∃ e : AzInt, e = pow2M1RatExp q := ⟨_, rfl⟩
  obtain ⟨hxe, hxe1⟩ := pow2M1RatExp_bounds q h0
  rw [← he] at hxe hxe1
  obtain ⟨xv, hxv⟩ : ∃ xv : ℝ, xv = (AzRat.toRat q : ℝ) := ⟨_, rfl⟩
  rw [← hxv] at hxe hxe1
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = expM1Comp (powBaseM1Exp e) := ⟨_, rfl⟩
  obtain ⟨eb, heb⟩ : ∃ eb : ℤ, eb = ((baseFloat u).exponent?.getD 0).toInt := ⟨_, rfl⟩
  have hwZ : 136 + (|e.toInt| + q.num.size) + |eb| ≤ (w : ℤ) := by
    rw [heb, he, ← powBaseM1RatW₀_eq]; exact_mod_cast hw
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnBaseMulRatBracket_spec q u hu (w + c) (by omega)
  rw [← heb] at hwid
  rw [← hxv] at h1 h2
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = mulLnEps (q.num.size : ℤ) eb (w + c) := ⟨_, rfl⟩
  rw [← hδ] at hwid
  have hδ0 : 0 ≤ δ := by rw [hδ]; unfold mulLnEps lnEps; positivity
  have hδ1 : δ ≤ 1 / 64 := by
    rw [hδ]
    refine (mulLnEps_le_inv256 (q.num.size : ℤ) eb (w + c) ?_).trans (by norm_num)
    have h1 : max (q.num.size : ℤ) 0 = q.num.size := max_eq_left (by positivity)
    have h2 : (0 : ℤ) ≤ |e.toInt| := abs_nonneg _
    push_cast
    omega
  have hcm := expM1Comp_powBaseM1Exp_le e
  have hδe : δ ≤ (2 : ℝ) ^ e.toInt / 4 := by
    rw [hδ, hc]
    refine mulLnEps_comp_le_of (q.num.size : ℤ) e eb w (|e.toInt| + q.num.size) ?_ hwZ
    have h1 : max (q.num.size : ℤ) 0 = q.num.size := max_eq_left (by positivity)
    have h2 : (0 : ℤ) ≤ max e.toInt 0 := le_max_right _ _
    omega
  -- the value and its size: `0.69 |q| ≤ |v| < 45 |q|`
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = xv * Real.log u.toNat := ⟨_, rfl⟩
  rw [← hv] at h1 h2
  have hlog45 : Real.log u.toNat < 45 := log_lt_45_of_lt_two_pow_64 u.toBitVec.isLt
  have hlog2 : Real.log 2 ≤ Real.log u.toNat :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hu)
  have hln1 := Real.log_two_gt_d9
  have habsv : |v| = |xv| * Real.log u.toNat := by
    rw [hv, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log u.toNat)]
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e.toInt := by positivity
  have hxv0 := abs_nonneg xv
  have hlo_e : |lo| < (2 : ℝ) ^ (powBaseM1Exp e).toInt := by
    rw [powBaseM1Exp_toInt, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : |lo| ≤ |v| + δ := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le v, le_abs_self v]
    have h3 : |v| ≤ |xv| * 45 := by rw [habsv]; nlinarith
    have h4 : (2 : ℝ) ^ (6 : ℤ) = 64 := by norm_num
    rw [h4]
    nlinarith
  have hlo_v : |lo| ≤ 2 * |v| := by
    have : |lo| ≤ |v| + δ := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le v, le_abs_self v]
    have h3 : |xv| * (6 / 10) ≤ |v| := by rw [habsv]; nlinarith
    linarith
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expM1OfBracket_spec_of_bounds (powBaseM1Exp e) hlo hhi
    h1 h2 hwid hδ0 hδ1 hlo_e hlo_v hw64
  simp only [powBaseM1RatBracket]
  rw [natCast_rpow_eq_exp (by omega), ← hxv, ← hv, ← he, ← hc, ← heb]
  rw [← hc] at hab
  refine ⟨a, b, ha, hb, ha1, hb1, hab.trans ?_⟩
  unfold powBaseM1Eps
  rw [← hδ]
  have hslack := expM1RatEps_slack v c w
  have hEvp := Real.exp_pos v
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have := mul_nonneg hEvp.le hu0
  linarith

/-- `powBaseM1RatApprox` is a strict enclosure of `u^q − 1` (given its irrationality), with
width at most `powBaseM1Eps`. -/
theorem powBaseM1RatApprox_spec {w : ℕ} (q : AzRat) (h0 : q.num ≠ 0) (u : UInt64)
    (hu : 2 ≤ u.toNat) (hirr : Irrational ((u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1))
    (hw : powBaseM1RatW₀ q u ≤ w) :
    ∃ lv hv : ℝ, Rounds (powBaseM1RatApprox q u w).1 lv ∧
      Rounds (powBaseM1RatApprox q u w).2 hv ∧
      lv < (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1 ∧
      (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1 < hv ∧
      hv - lv ≤ powBaseM1Eps (q.num.size : ℤ) ((baseFloat u).exponent?.getD 0).toInt
        (expM1Comp (powBaseM1Exp (pow2M1RatExp q))) ((AzRat.toRat q : ℝ) * Real.log u.toNat)
        w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := powBaseM1RatBracket_spec q h0 u hu hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 hirr
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The Ziv certificate for `u^q − 1`. -/
theorem powBaseM1RatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (u : UInt64) (hu : 2 ≤ u.toNat)
    (hirr : Irrational ((u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1)) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (powBaseM1RatApprox q u (w₀ * 2 ^ f)).1
      (powBaseM1RatApprox q u (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (powBaseM1RatApprox q u) hirr
    (powBaseM1Eps (q.num.size : ℤ) ((baseFloat u).exponent?.getD 0).toInt
      (expM1Comp (powBaseM1Exp (pow2M1RatExp q))) ((AzRat.toRat q : ℝ) * Real.log u.toNat))
    (tendsto_powBaseM1Eps _ _ _ _) (powBaseM1RatW₀ q u)
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwidth⟩ := powBaseM1RatApprox_spec q h0 u hu hirr hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwidth⟩) w₀ hw₀

/-- `u^q − 1` is irrational when `powBaseRatExact? = none`. -/
theorem irrational_sub_one_of_powBaseRatExact?_none (q : AzRat) (u : AzNat) (hu : 2 ≤ u.toNat)
    (hu64 : u.toNat < 2 ^ 64) (h : powBaseRatExact? q u = none) :
    Irrational ((u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1) := by
  have h' := (irrational_of_powBaseRatExact?_none q u hu hu64 h).sub_intCast 1
  rwa [Int.cast_one] at h'

end Azurite.AzFloat
