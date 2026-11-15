/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CatalanBracket
import Azurite.AzFloat.Equiv.Constants
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.AzFloat.Equiv.Sum
import Azurite.AzNat.Equiv.HypSplit
import Azurite.Transcendental.CatalanIrrational

/-!
# Equivalence: the bracket of Catalan's constant

`catalanBracket_spec`: `catalanBracket w` encloses `G` with width at most `2^(−w)` (`w ≥ 64`).
The exact partial sums come from `AzNat.catalanNumDen_eq` and `AzNat.atanhSqrtThreeNumDen_eq`,
bracketed by `seriesBracket_spec_of`; the tails from `tsum_catalanTerm_sub_sum` and
`tsum_atanhSqrtThreeTerm_sub_sum`; `π` from `piBracket_spec_width`; and the products are tracked
with absolute errors (`mulFloor_sub_le`, `mulCeil_sub_le`).  With `u = 2^(−w−16)` the lower end
is within `22u + 2^(−w−11) + 2^(−w−12)` of `G` and the upper end within `52u + 2^(−w−10)`.

`catalanApprox_isSome_exists` is the termination certificate of the Ziv loop: `G` is irrational
(`irrational_catalanConstant`) and the width tends to zero.
-/

namespace Azurite.AzFloat

open Finset Real

/-- Rounding a product down: the absolute error against upper bounds `x ≥ a`, `y ≥ b`. -/
theorem mulFloor_sub_le {k : ℕ} {a b x y r ea eb X Y : ℝ} (h : FloorOf k (a * b) r)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hax : a ≤ x) (hby : b ≤ y) (hea : x - a ≤ ea)
    (heb : y - b ≤ eb) (hxX : x ≤ X) (hyY : y ≤ Y) :
    r ≤ x * y ∧ x * y - r ≤ ea * Y + X * eb + 2 * X * Y * (1 / 2 : ℝ) ^ k := by
  have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
  have hX : 0 ≤ X := (ha0.trans hax).trans hxX
  have hab : a * b ≤ x * y := mul_le_mul hax hby hb0 (ha0.trans hax)
  have h1 : (x - a) * y ≤ ea * Y :=
    mul_le_mul hea hyY (hb0.trans hby) ((sub_nonneg.2 hax).trans hea)
  have h2 : a * (y - b) ≤ X * eb := mul_le_mul (hax.trans hxX) heb (sub_nonneg.2 hby) hX
  have h3 : a * b ≤ X * Y := mul_le_mul (hax.trans hxX) (hby.trans hyY) hb0 hX
  have h4 := h.ge
  have h5 : 2 * (a * b) * (1 / 2 : ℝ) ^ k ≤ 2 * X * Y * (1 / 2 : ℝ) ^ k := by
    have := mul_le_mul_of_nonneg_right h3 hu
    linarith
  have e : x * y - a * b = (x - a) * y + a * (y - b) := by ring
  exact ⟨h.le.trans hab, by linarith⟩

/-- Rounding a product up: the absolute error against lower bounds `x ≤ a`, `y ≤ b`. -/
theorem mulCeil_sub_le {k : ℕ} {a b x y r ea eb X Y : ℝ} (h : CeilOf k (a * b) r)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxa : x ≤ a) (hyb : y ≤ b) (hea : a - x ≤ ea)
    (heb : b - y ≤ eb) (haX : a ≤ X) (hbY : b ≤ Y) :
    x * y ≤ r ∧ r - x * y ≤ ea * Y + X * eb + 2 * X * Y * (1 / 2 : ℝ) ^ k := by
  have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
  have ha0 : 0 ≤ a := hx0.trans hxa
  have hb0 : 0 ≤ b := hy0.trans hyb
  have hX : 0 ≤ X := ha0.trans haX
  have hab : x * y ≤ a * b := mul_le_mul hxa hyb hy0 ha0
  have h1 : (a - x) * b ≤ ea * Y := mul_le_mul hea hbY hb0 ((sub_nonneg.2 hxa).trans hea)
  have h2 : x * (b - y) ≤ X * eb := mul_le_mul (hxa.trans haX) heb (sub_nonneg.2 hyb) hX
  have h3 : a * b ≤ X * Y := mul_le_mul haX hbY hb0 hX
  have h4 := h.le
  have h5 : 2 * (a * b) * (1 / 2 : ℝ) ^ k ≤ 2 * X * Y * (1 / 2 : ℝ) ^ k := by
    have := mul_le_mul_of_nonneg_right h3 hu
    linarith
  have e : a * b - x * y = (a - x) * b + x * (b - y) := by ring
  exact ⟨hab.trans h.ge, by linarith⟩

/-- The tail float `2^(−w−10)`. -/
theorem toVal_catalan_tail (w : ℕ) :
    (powerOf2 (-(AzNat.ofNat (w + 10)).toAzInt)).toVal
      = some (((1 / 2 : ℝ) ^ (w + 10) : ℝ) : EReal) := by
  rw [toVal_powerOf2, AzInt.toInt_neg, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg,
    zpow_natCast, one_div_pow, one_div]

/-- `3^(−N) ≤ 2^(−w−11)` for `N = atanhSqrtThreeTerms w`. -/
theorem one_third_pow_atanhSqrtThreeTerms_le (w : ℕ) :
    (1 / 3 : ℝ) ^ atanhSqrtThreeTerms w ≤ (1 / 2 : ℝ) ^ (w + 11) := by
  rw [atanhSqrtThreeTerms, pow_mul]
  calc ((1 / 3 : ℝ) ^ 2) ^ ((w + 10) / 3 + 1) ≤ ((1 / 2 : ℝ) ^ 3) ^ ((w + 10) / 3 + 1) :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (1 / 2 : ℝ) ^ (3 * ((w + 10) / 3 + 1)) := by rw [← pow_mul]
    _ ≤ (1 / 2 : ℝ) ^ (w + 11) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- `4^(−N) ≤ 2^(−w−11)` for `N = catalanTerms w`. -/
theorem one_fourth_pow_catalanTerms_le (w : ℕ) :
    (1 / 4 : ℝ) ^ catalanTerms w ≤ (1 / 2 : ℝ) ^ (w + 11) := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold catalanTerms; omega)

/-- **`catalanBracket w` encloses Catalan's constant, with width at most `2^(−w)`.** -/
theorem catalanBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (catalanBracket w).1.toVal = some (lo : EReal) ∧
      (catalanBracket w).2.toVal = some (hi : EReal) ∧
      lo ≤ catalanConstant ∧ catalanConstant ≤ hi ∧ hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  set k := catalanBits w with hk
  have hk64 : 64 ≤ k := by rw [hk]; unfold catalanBits; omega
  have : NeZero k := ⟨by omega⟩
  set NA := atanhSqrtThreeTerms w with hNA
  set NS := catalanTerms w with hNS
  set u : ℝ := (1 / 2 : ℝ) ^ k with hu
  set δ : ℝ := (1 / 2 : ℝ) ^ w with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have huδ : u = δ / 65536 := by
    rw [hu, hk, catalanBits, pow_add, ← hδ]; norm_num; ring
  have hu0 : 0 < u := by rw [huδ]; positivity
  have hu1 : u ≤ 1 / 65536 := by rw [huδ]; linarith
  -- the two series, their partial sums and tails
  set A := ∑' i, atanhSqrtThreeTerm i with hA
  set S := ∑' i, catalanTerm i with hS
  set AN := ∑ i ∈ range NA, atanhSqrtThreeTerm i with hAN
  set SN := ∑ i ∈ range NS, catalanTerm i with hSN
  obtain ⟨hAt0, hAt⟩ := tsum_atanhSqrtThreeTerm_sub_sum NA
  obtain ⟨hSt0, hSt⟩ := tsum_catalanTerm_sub_sum NS
  have hA0 := (tsum_atanhSqrtThreeTerm_sub_sum 0).2
  have hS0 := (tsum_catalanTerm_sub_sum 0).2
  simp only [range_zero, sum_empty, sub_zero, pow_zero, mul_one] at hA0 hS0
  rw [← hA] at hA0 hAt0 hAt
  rw [← hS] at hS0 hSt0 hSt
  rw [← hAN] at hAt0 hAt
  rw [← hSN] at hSt0 hSt
  have hAN0 : 0 ≤ AN := sum_nonneg fun i _ => (atanhSqrtThreeTerm_pos i).le
  have hSN0 : 0 ≤ SN := sum_nonneg fun i _ => (catalanTerm_pos i).le
  have hp11 : (1 / 2 : ℝ) ^ (w + 11) = δ / 2048 := by rw [pow_add, ← hδ]; norm_num; ring
  have hp10 : (1 / 2 : ℝ) ^ (w + 10) = δ / 1024 := by rw [pow_add, ← hδ]; norm_num; ring
  have hτA : A - AN ≤ δ / 4096 := by
    have := one_third_pow_atanhSqrtThreeTerms_le w
    rw [hp11, ← hNA] at this
    linarith
  have hτS : S - SN ≤ δ / 1536 := by
    have := one_fourth_pow_catalanTerms_le w
    rw [hp11, ← hNS] at this
    linarith
  -- the brackets of the exact partial sums `x = AN/4` and `z = 3 SN/8`
  set x : ℝ := 1 / 4 * AN with hx
  set y : ℝ := 1 / 4 * A with hy
  set z : ℝ := 3 / 8 * SN with hz
  have hx0 : 0 ≤ x := by positivity
  have hz0 : 0 ≤ z := by positivity
  have hxy : x ≤ y := by rw [hx, hy]; linarith
  have hy8 : y ≤ 1 / 8 := by rw [hy]; linarith
  have hx8 : x ≤ 1 / 8 := hxy.trans hy8
  have hz2 : z ≤ 1 / 2 := by rw [hz]; linarith
  obtain ⟨al, ah, hal, hah, hal0, halx, hallow, hahx, hahup⟩ :=
    seriesBracket_spec_of (AzNat.atanhSqrtThreeNumDen_eq NA) (AzNat.atanhSqrtThreeNumDen_den_pos NA)
      hx0 (k := k) (by omega)
  obtain ⟨sl, sh, hsl, hsh, hsl0, hslz, hsllow, hshz, hshup⟩ :=
    seriesBracket_spec_of (AzNat.catalanNumDen_eq NS) (AzNat.catalanNumDen_den_pos NS)
      hz0 (k := k) (by omega)
  rw [← hAN, ← hx] at halx hallow hahx hahup
  rw [← hSN, ← hz] at hslz hsllow hshz hshup
  rw [← hu] at hallow hahup hsllow hshup
  have hux : u * x ≤ u * (1 / 8) := mul_le_mul_of_nonneg_left hx8 hu0.le
  have huz : u * z ≤ u * (1 / 2) := mul_le_mul_of_nonneg_left hz2 hu0.le
  have hxal : x - al ≤ u := by linarith
  have hahx' : ah - x ≤ u := by linarith
  have hzsl : z - sl ≤ 3 * u := by linarith
  have hshz' : sh - z ≤ 4 * u := by linarith
  -- `√3`
  have h3v : (ofAzNat (AzNat.ofNat 3)).toVal = some (((3 : ℝ)) : EReal) := by
    have := toVal_ofAzNat_ofNat 3
    rwa [show ((3 : ℕ) : ℝ) = 3 by norm_num] at this
  obtain ⟨rl, hrl, hrlF⟩ := sqrtFloor_err h3v (by norm_num) k
  obtain ⟨rh, hrh, hrhC⟩ := sqrtCeiling_err h3v (by norm_num) k
  set ρ : ℝ := Real.sqrt 3 with hρ
  have hρsq : ρ ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg 3
  have hρ2 : ρ ≤ 2 := by
    by_contra h
    push Not at h
    have : (2 : ℝ) * 2 < ρ * ρ := mul_lt_mul h h.le (by norm_num) hρ0
    linarith [sq ρ ▸ hρsq]
  have hρl : ρ - rl ≤ 4 * u := by
    have h1 : ρ ≤ rl + 2 * ρ * u := hrlF.2.2
    have := mul_le_mul_of_nonneg_right hρ2 hu0.le
    linarith
  have hρh : rh - ρ ≤ 4 * u := by
    have h1 : rh ≤ ρ + 2 * ρ * u := hrhC.2
    have := mul_le_mul_of_nonneg_right hρ2 hu0.le
    linarith
  -- `π`
  obtain ⟨pl, ph, hpl, hph, hpl0, hplπ, hπph, hpw⟩ := piBracket_spec_width hk64
  rw [← hu] at hpw
  have hπ4 := Real.pi_le_four
  have hπ0 := Real.pi_pos
  have hρπ : ρ * π ≤ 8 := by
    have := mul_le_mul hρ2 hπ4 hπ0.le (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hρπ0 : 0 ≤ ρ * π := mul_nonneg hρ0 hπ0.le
  -- the value
  have hG : catalanConstant = ρ * π * y + 3 / 8 * S := by
    rw [catalanConstant_eq, hy, hρ]; ring
  have hyx : ρ * π * (y - x) ≤ δ / 2048 := by
    have h1 : y - x ≤ δ / 16384 := by rw [hx, hy]; linarith
    have := mul_le_mul hρπ h1 (sub_nonneg.2 hxy) (by norm_num : (0 : ℝ) ≤ 8)
    linarith
  -- the tail float
  have ht := toVal_catalan_tail w
  rw [hp10] at ht
  -- the lower end
  obtain ⟨m1, hm1, hm1F⟩ := mulFloor_err hrl hpl k (mul_nonneg hrlF.1 hpl0)
  obtain ⟨m2, hm2, hm2F⟩ := mulFloor_err hm1 hal k (mul_nonneg hm1F.1 hal0)
  obtain ⟨lo, hlo, hloF⟩ := addFloor_err hm2 hsl k (add_nonneg hm2F.1 hsl0)
  obtain ⟨L1a, L1b⟩ := mulFloor_sub_le hm1F hrlF.1 hpl0 hrlF.2.1 hplπ.le hρl
    (by linarith : π - pl ≤ 8 * u) hρ2 hπ4
  rw [← hu] at L1b
  obtain ⟨L2a, L2b⟩ := mulFloor_sub_le hm2F hm1F.1 hal0 L1a (halx.trans hxy)
    (by linarith : ρ * π - m1 ≤ 48 * u)
    (by linarith : y - al ≤ δ / 16384 + u) hρπ hy8
  rw [← hu] at L2b
  have hm2le : m2 ≤ 1 := by
    have := mul_le_mul hρπ hy8 (hx0.trans hxy) (by norm_num : (0 : ℝ) ≤ 8)
    linarith
  have hlo1 : lo ≤ catalanConstant := by
    rw [hG]
    have := hloF.2.1
    linarith
  have hlo2 : catalanConstant - lo ≤ 22 * u + δ / 2048 + δ / 4096 := by
    rw [hG]
    have h1 : m2 + sl ≤ lo + 2 * (m2 + sl) * u := hloF.2.2
    have h2 : 2 * (m2 + sl) * u ≤ 3 * u := by
      have := mul_le_mul_of_nonneg_right (by linarith : m2 + sl ≤ 3 / 2) hu0.le
      linarith
    linarith
  -- the upper end
  have hrh3 : rh ≤ 3 := by linarith
  have hph5 : ph ≤ 5 := by linarith
  obtain ⟨M1, hM1, hM1C⟩ := mulCeiling_err hrh hph k
    (mul_nonneg (hρ0.trans hrhC.1) (hπ0.le.trans hπph))
  obtain ⟨U1a, U1b⟩ := mulCeil_sub_le hM1C hρ0 hπ0.le hrhC.1 hπph hρh
    (by linarith : ph - π ≤ 8 * u) hrh3 hph5
  rw [← hu] at U1b
  have hM19 : M1 ≤ 9 := by linarith
  have hah4 : ah ≤ 1 / 4 := by linarith
  obtain ⟨M2, hM2, hM2C⟩ := mulCeiling_err hM1 hah k
    (mul_nonneg (hρπ0.trans U1a) (hx0.trans hahx))
  obtain ⟨U2a, U2b⟩ := mulCeil_sub_le hM2C hρπ0 hx0 U1a hahx
    (by linarith : M1 - ρ * π ≤ 74 * u) hahx' hM19 hah4
  rw [← hu] at U2b
  have hρπx : ρ * π * x ≤ 1 := by
    have := mul_le_mul hρπ hx8 hx0 (by norm_num : (0 : ℝ) ≤ 8)
    linarith
  have hM22 : M2 ≤ 2 := by linarith
  have hM20 : 0 ≤ M2 := (mul_nonneg hρπ0 hx0).trans U2a
  have hsh1 : sh ≤ 1 := by linarith
  obtain ⟨U1, hU1, hU1C⟩ := addCeiling_err hM2 hsh k (add_nonneg hM20 (hz0.trans hshz))
  have hU1le : U1 - (M2 + sh) ≤ 6 * u := by
    have h1 : U1 ≤ M2 + sh + 2 * (M2 + sh) * u := hU1C.2
    have := mul_le_mul_of_nonneg_right (by linarith : M2 + sh ≤ 3) hu0.le
    linarith
  have hU10 : 0 ≤ U1 := (add_nonneg hM20 (hz0.trans hshz)).trans hU1C.1
  obtain ⟨hi, hhi, hhiC⟩ := addCeiling_err hU1 ht k (add_nonneg hU10 (by positivity))
  have hhile : hi - (U1 + δ / 1024) ≤ 10 * u := by
    have h1 : hi ≤ U1 + δ / 1024 + 2 * (U1 + δ / 1024) * u := hhiC.2
    have := mul_le_mul_of_nonneg_right (by linarith : U1 + δ / 1024 ≤ 5) hu0.le
    linarith
  have hlow : ρ * π * x + z ≤ catalanConstant := by
    rw [hG]
    have : ρ * π * x ≤ ρ * π * y := mul_le_mul_of_nonneg_left hxy hρπ0
    rw [hz]; linarith
  have hhi1 : catalanConstant ≤ hi := by
    have h1 := hhiC.1
    have h2 := hU1C.1
    have e : catalanConstant = ρ * π * x + z + ρ * π * (y - x) + 3 / 8 * (S - SN) := by
      rw [hG, hz]; ring
    rw [e]
    linarith
  have hhi2 : hi - catalanConstant ≤ 52 * u + δ / 1024 := by linarith
  refine ⟨lo, hi, ?_, ?_, hlo1, hhi1, ?_⟩
  · simp only [catalanBracket]
    rw [← hk, ← hNA, ← hNS]
    exact hlo
  · simp only [catalanBracket]
    rw [← hk, ← hNA, ← hNS]
    exact hhi
  · rw [huδ] at hlo2 hhi2
    linarith

theorem catalanApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (catalanApprox w).1 lv ∧ Rounds (catalanApprox w).2 hv ∧
      lv ≤ catalanConstant ∧ catalanConstant ≤ hv ∧ hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := catalanBracket_spec hw
  refine ⟨lo, hi, ?_, ?_, h1, h2, h3⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR

/-- The Ziv certificate: at some working precision `w₀ · 2^f`, rounding is possible, because
Catalan's constant is irrational and the bracket width tends to zero. -/
theorem catalanApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (catalanApprox (w₀ * 2 ^ f)).1 (catalanApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode catalanApprox irrational_catalanConstant
    (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 64
    (fun _ hw => catalanApprox_spec hw) w₀ hw₀

end Azurite.AzFloat
