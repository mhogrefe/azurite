/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosWithPeriodBracket
import Azurite.AzFloat.Equiv.CosRatBracket
import Azurite.AzRat.Equiv.Construct
import Azurite.Transcendental.Niven
import Azurite.AzFloat.Equiv.RatPow

/-!
# Equivalence: the bracket of `cos (2πr)`

`periodFrac_spec` (the fractional part), `cosPeriodBracket_spec` (width `cosPeriodEps w`),
`tendsto_cosPeriodEps`, `cosPeriodApprox_spec`, `cosPeriodApprox_isSome_exists` (the Ziv
certificate from Niven's theorem), and the denominator helpers `den_toRat_eq`, `den_toRat_ne`.
-/

namespace Azurite.AzFloat

/-! ### The fractional part -/

theorem natCast_div_eq_add_mod_div (X U : ℕ) (hU : 0 < U) :
    (X : ℝ) / U = ((X / U : ℕ) : ℝ) + ((X % U : ℕ) : ℝ) / U := by
  have hU' : (U : ℝ) ≠ 0 := by positivity
  have h' : (X : ℝ) = U * ((X / U : ℕ) : ℝ) + ((X % U : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod X U).symm
  rw [h']
  field_simp

theorem toNat_shiftLeft' (a : AzNat) (n : ℕ) : (a <<< n).toNat = a.toNat * 2 ^ n :=
  AzNat.toNat_shiftLeft a n

/-- `periodFrac m E u` is the fractional part of `m 2^E / u`. -/
theorem periodFrac_spec (m : AzNat) (E : AzInt) {u : AzNat} (hu : u ≠ 0) :
    ∃ k : ℕ, (m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat
        = k + ((AzRat.toRat (periodFrac m E u) : ℚ) : ℝ) ∧
      0 ≤ ((AzRat.toRat (periodFrac m E u) : ℚ) : ℝ) ∧
      ((AzRat.toRat (periodFrac m E u) : ℚ) : ℝ) < 1 := by
  have htoInt : E.toInt = if E.sign then (E.abs.toNat : ℤ) else -(E.abs.toNat : ℤ) := rfl
  have hUn : 0 < u.toNat :=
    Nat.pos_of_ne_zero fun h => hu (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
  have hU : (0 : ℝ) < u.toNat := by exact_mod_cast hUn
  unfold periodFrac
  rw [htoInt]
  split_ifs with hs
  · rw [AzRat.toRat_ofAzNats, AzNat.toNat_mod, toNat_shiftLeft']
    refine ⟨m.toNat * 2 ^ E.abs.toNat / u.toNat, ?_, by positivity, ?_⟩
    · have h := natCast_div_eq_add_mod_div (m.toNat * 2 ^ E.abs.toNat) u.toNat hUn
      push_cast at h ⊢
      rw [zpow_natCast]
      exact h
    · push_cast
      rw [div_lt_one hU]
      exact_mod_cast Nat.mod_lt _ hUn
  · rw [AzRat.toRat_ofAzNats, AzNat.toNat_mod, toNat_shiftLeft']
    have hDn : 0 < u.toNat * 2 ^ E.abs.toNat := by positivity
    have hD : (0 : ℝ) < ((u.toNat * 2 ^ E.abs.toNat : ℕ) : ℝ) := by exact_mod_cast hDn
    refine ⟨m.toNat / (u.toNat * 2 ^ E.abs.toNat), ?_, by positivity, ?_⟩
    · have h := natCast_div_eq_add_mod_div m.toNat (u.toNat * 2 ^ E.abs.toNat) hDn
      have e : (m.toNat : ℝ) * (2 : ℝ) ^ (-(E.abs.toNat : ℤ)) / u.toNat
          = (m.toNat : ℝ) / ((u.toNat * 2 ^ E.abs.toNat : ℕ) : ℝ) := by
        rw [zpow_neg, zpow_natCast]
        push_cast
        field_simp
      rw [e, h]
      push_cast
      ring
    · push_cast at hD ⊢
      rw [div_lt_one hD]
      exact_mod_cast Nat.mod_lt _ hDn

/-- `periodFracRat q u` is the fractional part of `|q| / u`. -/
theorem periodFracRat_spec (q : AzRat) {u : AzNat} (hu : u ≠ 0) :
    ∃ k : ℕ, |((AzRat.toRat q : ℚ) : ℝ)| / u.toNat
        = k + ((AzRat.toRat (periodFracRat q u) : ℚ) : ℝ) ∧
      0 ≤ ((AzRat.toRat (periodFracRat q u) : ℚ) : ℝ) ∧
      ((AzRat.toRat (periodFracRat q u) : ℚ) : ℝ) < 1 := by
  have hUn : 0 < u.toNat :=
    Nat.pos_of_ne_zero fun h => hu (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
  have hdn : 0 < q.den.toNat := AzRat.den_toNat_pos q
  have hDn : 0 < q.den.toNat * u.toNat := Nat.mul_pos hdn hUn
  have hD : (0 : ℝ) < ((q.den.toNat * u.toNat : ℕ) : ℝ) := by exact_mod_cast hDn
  unfold periodFracRat
  rw [abs_coe_toRat, AzRat.toRat_ofAzNats, AzNat.toNat_mod, AzNat.toNat_mul]
  refine ⟨q.num.toNat / (q.den.toNat * u.toNat), ?_, by positivity, ?_⟩
  · have h := natCast_div_eq_add_mod_div q.num.toNat (q.den.toNat * u.toNat) hDn
    rw [div_div]
    push_cast at h ⊢
    exact h
  · push_cast at hD ⊢
    rw [div_lt_one hD]
    exact_mod_cast Nat.mod_lt _ hDn

/-! ### The denominator of an `AzRat` -/

theorem den_toRat_eq {r : AzRat} {n : ℕ} (h : r.den = AzNat.ofNat n) : (AzRat.toRat r).den = n := by
  show r.den.toNat = n
  rw [h, AzNat.toNat_ofNat]

theorem den_toRat_ne {r : AzRat} {n : ℕ} (h : r.den ≠ AzNat.ofNat n) : (AzRat.toRat r).den ≠ n :=
  fun h' => h (AzNat.toNat_injective (by rw [AzNat.toNat_ofNat]; exact h'))

/-! ### The bracket -/

/-- The width of `cosPeriodBracket r w`. -/
noncomputable def cosPeriodEps (w : ℕ) : ℝ :=
  cosEps (AzInt.ofInt 3) w + 152 * (1 / 2 : ℝ) ^ cosWork (AzInt.ofInt 3) w

/-- **`cosPeriodBracket` encloses `cos (2πr)`** for `0 ≤ r < 1`, at Ziv level `w ≥ 64`, with
width at most `cosPeriodEps w`. -/
theorem cosPeriodBracket_spec (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (cosPeriodBracket r w).1.toVal = some (lo : EReal) ∧
      (cosPeriodBracket r w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) ∧
      Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) ≤ hi ∧ hi - lo ≤ cosPeriodEps w := by
  set rv := ((AzRat.toRat r : ℚ) : ℝ) with hrv
  have hW64 : 64 ≤ cosWork (AzInt.ofInt 3) w := by unfold cosWork; omega
  have hεle := cosEps_le_one (AzInt.ofInt 3) hw
  simp only [cosPeriodBracket]
  set W := cosWork (AzInt.ofInt 3) w with hWdef
  have : NeZero W := ⟨by omega⟩
  set P := piBracket W with hP
  set a := (ofAzRatRound r W .Floor).1 with ha
  set t := (mulPrecRound (a <<< AzInt.ofInt 1) P.1 W .Floor).1 with ht
  set E := one <<< AzInt.ofInt (6 - W) with hE
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hW64
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  obtain ⟨lv, hv, hlv, hhv, hlv0, hlvπ, hπhv, hwid⟩ := piBracket_spec_width hW64
  rw [← hu] at hwid
  have hlv1 : 1 ≤ lv := by linarith
  have hlv4 : lv ≤ 4 := by linarith
  have hlv' : P.1.toVal = some (lv : EReal) := hlv
  obtain ⟨av, hav, hav1, hav2⟩ := ofAzRatRound_floor_abs r W
  rw [← hrv] at hav1
  rw [← hrv, ← hu, abs_of_nonneg hr0] at hav2
  have hav' : a.toVal = some (av : EReal) := hav
  have h2a := toVal_shiftLeft_one hav'
  obtain ⟨tv, htv, htv1, htv2⟩ := mulFloor_abs h2a hlv' W
  rw [← hu] at htv2
  have hrvu : rv * u ≤ u := by nlinarith
  have hav3 : av ≤ 1 := by linarith
  have hav4 : -2 * u ≤ av := by linarith
  have hprod : |2 * av * lv| ≤ 8 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hprodu := mul_le_mul_of_nonneg_right hprod hu0
  have havlv : av * lv < lv := by
    have : av < 1 := by linarith
    nlinarith
  have ht8 : |tv| < (2 : ℝ) ^ (AzInt.ofInt 3).toInt := by
    rw [AzInt.toInt_ofInt, show (2 : ℝ) ^ (3 : ℤ) = 8 by norm_num, abs_lt]
    constructor <;> nlinarith
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid'⟩ := cosBracket_spec htv ht8 hw
  have h64 : (1 : ℝ) * (2 : ℝ) ^ ((6 : ℤ) - (W : ℤ)) = 64 * u := by
    rw [one_mul, zpow_sub₀ two_ne_zero, zpow_natCast, hu, one_div_pow, div_eq_mul_inv]
    norm_num
  have hEv : E.toVal = some ((64 * u : ℝ) : EReal) := by
    rw [hE, toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt, h64]
  have herr0 : 0 ≤ 2 * Real.pi * rv - tv := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hlvπ.le), mul_nonneg hlv0 (sub_nonneg.mpr hav1)]
  have herr : 2 * Real.pi * rv - tv ≤ 48 * u := by
    have e1 : rv * (Real.pi - lv) ≤ 1 * (8 * u) :=
      mul_le_mul hr1.le (by linarith) (by linarith) zero_le_one
    have e2 : lv * (rv - av) ≤ 4 * (2 * u) :=
      mul_le_mul hlv4 (by linarith) (by linarith) (by norm_num)
    nlinarith
  have hz : |Real.cos (2 * Real.pi * rv) - Real.cos tv| ≤ 64 * u := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [abs_of_nonneg herr0]
    linarith
  have hB : IsEnclW (cosBracket t (AzInt.ofInt 3) w) (Real.cos tv) (cosEps (AzInt.ofInt 3) w) :=
    ⟨lo, hi, hlo, hhi, h1, h2, hwid'⟩
  have hC := hB.widen0 (M := 2) (isEncl0W_exact hEv (by positivity)) hz
    ((Real.abs_cos_le_one _).trans (by norm_num)) (by linarith) hεle (by norm_num) hW64
  obtain ⟨lo', hi', hlo', hhi', h1', h2', hwid''⟩ := hC
  rw [← hu] at hwid''
  refine ⟨lo', hi', hlo', hhi', h1', h2', hwid''.trans ?_⟩
  unfold cosPeriodEps
  rw [← hWdef, ← hu]
  linarith

/-- `cosPeriodEps w → 0` as `w → ∞`. -/
theorem tendsto_cosPeriodEps : Filter.Tendsto cosPeriodEps Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (cosWork (AzInt.ofInt 3)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by unfold cosWork; omega⟩
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp hc
  have h := (tendsto_cosEps (AzInt.ofInt 3)).add (h2.const_mul 152)
  simp only [mul_zero, add_zero] at h
  exact h

/-- `cosPeriodApprox` as a pair of `Roundable`s bracketing `cos (2πr)`. -/
theorem cosPeriodApprox_spec (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (cosPeriodApprox r w).1 lv ∧ Rounds (cosPeriodApprox r w).2 hv ∧
      lv ≤ Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) ∧
      Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) ≤ hv ∧ hv - lv ≤ cosPeriodEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := cosPeriodBracket_spec r hr0 hr1 hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [cosPeriodApprox]
  exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩

/-- `cos (2πr)` is irrational for an `AzRat` whose denominator is not `1, 2, 3, 4, 6`. -/
theorem irrational_cos_two_pi_mul_toRat (r : AzRat) (h1 : r.den ≠ AzNat.ofNat 1)
    (h2 : r.den ≠ AzNat.ofNat 2) (h3 : r.den ≠ AzNat.ofNat 3) (h4 : r.den ≠ AzNat.ofNat 4)
    (h6 : r.den ≠ AzNat.ofNat 6) : Irrational (Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))) :=
  irrational_cos_two_pi_mul_rat (den_toRat_ne h1) (den_toRat_ne h2) (den_toRat_ne h3)
    (den_toRat_ne h4) (den_toRat_ne h6)

/-- The Ziv certificate for `cos (2πr)`, `r ∈ [0, 1)` with an irrational cosine. -/
theorem cosPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (r : AzRat)
    (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1)
    (h1 : r.den ≠ AzNat.ofNat 1) (h2 : r.den ≠ AzNat.ofNat 2) (h3 : r.den ≠ AzNat.ofNat 3)
    (h4 : r.den ≠ AzNat.ofNat 4) (h6 : r.den ≠ AzNat.ofNat 6) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cosPeriodApprox r (w₀ * 2 ^ f)).1
      (cosPeriodApprox r (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (cosPeriodApprox r)
    (irrational_cos_two_pi_mul_toRat r h1 h2 h3 h4 h6) cosPeriodEps tendsto_cosPeriodEps 64
    (fun _ hw => cosPeriodApprox_spec r hr0 hr1 hw) w₀ hw₀

end Azurite.AzFloat
