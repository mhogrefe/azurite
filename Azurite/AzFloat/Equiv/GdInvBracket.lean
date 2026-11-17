/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GdInvBracket
import Azurite.AzFloat.Equiv.LnEncl
import Azurite.AzFloat.Equiv.AtanhBracket
import Azurite.AzFloat.Equiv.CosRat
import Azurite.AzFloat.Equiv.CotBracket
import Azurite.AzFloat.Equiv.SinCosRatBracket
import Azurite.AzFloat.Equiv.GdBracket
import Azurite.AzFloat.Equiv.PiConstants
import Azurite.AzFloat.Equiv.TanBracket
import Azurite.AzFloat.Equiv.TanRatBracket

/-!
# Equivalence: the bracket of the inverse Gudermannian

* `gdInv_neg_of`, `irrational_gdInv_rat` (from `irrational_gd_rat` through `gd (gd⁻¹ x) = x`),
  `gdInv_tiny_bounds` (`a < gd⁻¹ a ≤ a + a³` for `a ≤ 1/4`).
* `gdInvNum_spec`; `lnOfEncl_core` (the logarithm of an enclosure with a positive float lower
  end), `lnOfEncl_dummy`, `lnOfEncl_valid`, `lnOfEncl_width`.
* `gdInvBracket_valid_or_dummy`, `gdInvApprox_valid_or_none` (at every level the bracket
  encloses `± gd⁻¹ |x|` or is rejected), `gdInvBracket_width` (width `gdInvEps → 0` once the
  enclosure of `cos x` is narrow enough), `gdInvApprox_isSome_exists` (the Ziv certificate).
* `gdInvInDomain_iff`: the domain test is `|x| < π/2`.
-/

open Real

namespace Azurite.AzFloat

open Azurite.DLMF (gd gdInv)

/-! ### The function -/

theorem gdInv_neg_of {a : ℝ} (ha : |a| < π / 2) : gdInv (-a) = -gdInv a := by
  have hm : a ∈ Set.Ioo (-(π / 2)) (π / 2) := abs_lt.mp ha
  have hm' : -a ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hm.2], by linarith [hm.1]⟩
  rw [DLMF.gdInv_eq_artanh hm', DLMF.gdInv_eq_artanh hm, sin_neg, artanh_neg']

/-- **`gd⁻¹ q` is irrational** for a rational `q ≠ 0` with `|q| < π/2`. -/
theorem irrational_gdInv_rat {q : ℚ} (hq : q ≠ 0) (hd : |(q : ℝ)| < π / 2) :
    Irrational (gdInv q) := by
  rintro ⟨r, hr⟩
  have h := DLMF.gd_gdInv (abs_lt.mp hd)
  rw [← hr] at h
  by_cases hr0 : r = 0
  · subst hr0
    rw [Rat.cast_zero, gd_zero] at h
    exact hq (by exact_mod_cast h.symm)
  · exact irrational_gd_rat hr0 ⟨q, h.symm⟩

/-- `a < gd⁻¹ a ≤ a + a³` for `0 < a ≤ 1/4`. -/
theorem gdInv_tiny_bounds {a : ℝ} (h0 : 0 < a) (h1 : a ≤ 1 / 4) :
    a < gdInv a ∧ gdInv a ≤ a + a ^ 3 := by
  have hpi := pi_gt_three
  have hm : a ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hs0 : 0 < Real.sin a := sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsa : Real.sin a ≤ a := sin_le h0.le
  obtain ⟨hb1, hb2⟩ := artanh_tiny_bounds hs0 (hsa.trans h1)
  have hval := DLMF.gdInv_eq_artanh hm
  have hy0 : 0 < gdInv a := by rw [hval]; linarith
  refine ⟨?_, ?_⟩
  · have := gd_lt_self hy0
    rwa [DLMF.gd_gdInv hm] at this
  · rw [hval]
    have hcube : Real.sin a ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hs0.le hsa 3
    linarith

/-- `gd⁻¹` near `0`, patched by the tangent above `1/4`: an odd function with
`a < f a ≤ a + a³` on `(0, 1]`, as the generic tiny-argument lemma requires. -/
noncomputable def gdInvPatch (a : ℝ) : ℝ := if |a| ≤ 1 / 4 then gdInv a else Real.tan a

theorem gdInvPatch_neg (a : ℝ) : gdInvPatch (-a) = -gdInvPatch a := by
  unfold gdInvPatch
  rw [abs_neg]
  by_cases ha : |a| ≤ 1 / 4
  · rw [ite_eq_left ha, ite_eq_left ha, gdInv_neg_of (by linarith [pi_gt_three])]
  · rw [ite_eq_right ha, ite_eq_right ha, Real.tan_neg]

theorem gdInvPatch_bounds (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    a < gdInvPatch a ∧ gdInvPatch a ≤ a + a ^ 3 := by
  unfold gdInvPatch
  rw [abs_of_pos ha0]
  by_cases ha : a ≤ 1 / 4
  · rw [ite_eq_left ha]
    exact gdInv_tiny_bounds ha0 ha
  · rw [ite_eq_right ha]
    exact tan_bounds_of_small ha0 ha1

theorem gdInvPatch_eq {a : ℝ} (ha : |a| ≤ 1 / 4) : gdInvPatch a = gdInv a := by
  unfold gdInvPatch
  rw [ite_eq_left ha]

/-- `gd⁻¹ x = ± gd⁻¹ |x|` with the sign bit of `x`, for `|x| < π/2`. -/
theorem gdInv_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0)
    (hd : |xv| < π / 2) : gdInv xv = (if neg then -1 else 1) * gdInv |xv| := by
  cases neg with
  | true =>
    have h := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg h, gdInv_neg_of hd]
    ring
  | false =>
    have h : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg h]

/-! ### The numerator -/

/-- **`gdInvNum` encloses `(1 + σ)/2`** for an enclosure of `σ ∈ [0, 1]` of width `δ ≤ 1`:
width at most `δ/2 + 5·2^(−V)`. -/
theorem gdInvNum_spec {S : Encl} {σ δ : ℝ} (hS : IsEnclW S σ δ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1)
    (hδ : δ ≤ 1) {V : ℕ} (hV : 1 ≤ V) :
    IsEnclW (gdInvNum S V) ((1 + σ) / 2) (δ / 2 + 5 * (1 / 2 : ℝ) ^ V) := by
  obtain ⟨sl, sh, hsl, hsh, s1, s2, sw⟩ := hS
  have : NeZero V := ⟨by omega⟩
  obtain ⟨l, hl, hl1, hl2⟩ := addFloor_abs toVal_one' hsl V
  obtain ⟨h, hh, hh1, hh2⟩ := addCeiling_abs toVal_one' hsh V
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
  have ha1 : |1 + sl| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have ha2 : |1 + sh| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith
  have m1 := mul_le_mul_of_nonneg_right ha1 hu0
  have m2 := mul_le_mul_of_nonneg_right ha2 hu0
  unfold gdInvNum
  exact ⟨l / 2, h / 2, toVal_shiftLeft_neg_one hl, toVal_shiftLeft_neg_one hh, by linarith,
    by linarith, by linarith⟩

/-! ### The logarithm of an enclosure: its width -/

/-- The width bound of `lnOfEncl` for an enclosure of width `δ` of a number in `[1, 2^E)`. -/
noncomputable def lnOfEnclEps (E : ℕ) (δ : ℝ) (w : ℕ) : ℝ :=
  lnEps E w + 4 * δ + 2 * ((E : ℝ) + lnEps E w + 2) * (1 / 2 : ℝ) ^ w

/-- **The width of `lnOfEncl`** for an enclosure of width `δ ≤ 1/2` of `v ∈ [1, 2^E)`,
`E ≥ 1`. -/
theorem lnOfEncl_width {y : Encl} {v δ : ℝ} (hy : IsEnclW y v δ) (hv1 : 1 ≤ v) (hδ : δ ≤ 1 / 2)
    {E : ℕ} (hE1 : 1 ≤ E) (hvE : v < (2 : ℝ) ^ E) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (lnOfEncl y w) (Real.log v) (lnOfEnclEps E δ w) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwd⟩ := hy
  have hlo2 : 1 / 2 ≤ lo := by linarith
  obtain ⟨e, q, m, hm, heq⟩ := exists_finite_true_of_toVal_pos hlo (by linarith)
  have hyeq : y = (finite true e q m hm, y.2) := Prod.ext heq rfl
  rw [heq, toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hlo
  rw [hyeq]
  obtain ⟨lv, up, hlv, hup, k1, k2, k3⟩ := lnOfEncl_core hm hhi (hlo ▸ h1) h2 hw
  rw [hlo] at k3
  refine ⟨lv, up, hlv, hup, k1, k2, k3.trans ?_⟩
  -- the exponent of `lo` is in `[0, E]`
  obtain ⟨hb1, hb2⟩ := abs_finiteVal_bounds true e hm
  rw [hlo, abs_of_pos (by linarith : (0 : ℝ) < lo)] at hb1 hb2
  have he0 : 0 ≤ e.toInt := by
    by_contra hcon
    push Not at hcon
    have : (2 : ℝ) ^ e.toInt ≤ 2 ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_neg_one] at this
    norm_num at this
    linarith
  have heE : e.toInt ≤ E := by
    by_contra hcon
    push Not at hcon
    have h3 : (2 : ℝ) ^ (E : ℤ) ≤ 2 ^ (e.toInt - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_natCast] at h3
    linarith
  have hmono : lnEps e.toInt w ≤ lnEps E w :=
    lnEps_mono (by rw [abs_of_nonneg he0, abs_of_nonneg (by positivity)]; exact heE) w
  have hlnE0 : 0 ≤ lnEps e.toInt w := by unfold lnEps; positivity
  have hD : (hi - lo) / lo ≤ 2 * δ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hD0 : 0 ≤ (hi - lo) / lo := div_nonneg (by linarith) (by linarith)
  have hlogabs : |Real.log lo| ≤ (E : ℝ) := by
    have hE1' : (1 : ℝ) ≤ E := by exact_mod_cast hE1
    rw [abs_le]
    constructor
    · have h3 : Real.log (1 / 2) ≤ Real.log lo := Real.log_le_log (by norm_num) hlo2
      rw [one_div, Real.log_inv] at h3
      have := Real.log_two_lt_d9
      linarith
    · have h3 : Real.log lo ≤ Real.log ((2 : ℝ) ^ E) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_pow] at h3
      have := Real.log_two_lt_d9
      nlinarith
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  unfold lnOfEnclEps
  have m1 : (|Real.log lo| + lnEps e.toInt w + 2 * ((hi - lo) / lo)) * (1 / 2 : ℝ) ^ w
      ≤ ((E : ℝ) + lnEps E w + 2) * (1 / 2 : ℝ) ^ w :=
    mul_le_mul_of_nonneg_right (by linarith) hu0
  linarith

/-! ### The bracket -/

/-- Doubling an enclosure with a width. -/
theorem isEnclW_double {A : Encl} {v δ : ℝ} (h : IsEnclW A v δ) :
    IsEnclW (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1) (2 * v) (2 * δ) := by
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := h
  have e1 := toVal_shiftLeft_of_toVal hl (AzInt.ofInt 1)
  have e2 := toVal_shiftLeft_of_toVal hu (AzInt.ofInt 1)
  rw [AzInt.toInt_ofInt, zpow_one] at e1 e2
  exact ⟨l * 2, u * 2, e1, e2, by linarith, by linarith, by linarith⟩

/-- The value under the logarithm: `2 · ((1 + sin a)/2) / cos a`. -/
theorem gdInv_abs_eq_log {xv : ℝ} (hd : |xv| < π / 2) :
    gdInv |xv| = Real.log (2 * ((1 + Real.sin |xv|) / 2 / Real.cos xv)) := by
  have hm : |xv| ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith [abs_nonneg xv, pi_pos], hd⟩
  rw [DLMF.gdInv_eq_log hm, Real.cos_abs]
  congr 1
  ring

/-- **The step is the dummy `[−1, 1]` or encloses `ln (2 · ((1 + σ)/2) / c)`**, for
enclosures of `σ ∈ [0, 1]` (width at most `1`) and of `c`. -/
theorem gdInvOfSinCos_valid_or_dummy {b : Encl × Encl} {σ c δS δC : ℝ} (hS : IsEnclW b.1 σ δS)
    (hC : IsEnclW b.2 c δC) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hδS : δS ≤ 1) {w : ℕ} (hw : 64 ≤ w) :
    gdInvOfSinCos b w = (-one, one) ∨
      IsEncl (gdInvOfSinCos b w) (Real.log (2 * ((1 + σ) / 2 / c))) := by
  have hN := gdInvNum_spec hS hσ0 hσ1 hδS (V := w + 12) (by omega)
  have hu : (1 / 2 : ℝ) ^ (w + 12) ≤ 1 / 16 := by
    calc (1 / 2 : ℝ) ^ (w + 12) ≤ (1 / 2 : ℝ) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have hs : |(1 + σ) / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  unfold gdInvOfSinCos
  dsimp only
  rcases tanOfSinCos_spec (b := (gdInvNum b.1 (w + 12), b.2)) hN hC hs (by linarith)
      (V := w + 12) (by omega) with ⟨hdum, -⟩ | ⟨b1, hb1, -, h⟩
  · left
    rw [hdum]
    have hl := toVal_shiftLeft_of_toVal toVal_neg_one_float (AzInt.ofInt 1)
    exact lnOfEncl_dummy hl (by rw [AzInt.toInt_ofInt, zpow_one]; norm_num) w
  · obtain ⟨lo, hi, hlo, hhi, h1, h2, -⟩ := isEnclW_double (h b1 hb1 le_rfl)
    exact lnOfEncl_valid ⟨lo, hi, hlo, hhi, h1, h2⟩ hw

/-- The width of the quotient `(1 + σ)/(2c)` from enclosures of widths `δS`, `δC ≤ c/2`. -/
noncomputable def gdInvQEpsOf (δS δC c : ℝ) (w : ℕ) : ℝ :=
  (δS / 2 + 5 * (1 / 2 : ℝ) ^ (w + 12) + 2 * δC / (c / 2) + 8 * (1 / 2 : ℝ) ^ (w + 12)) / (c / 2)

theorem tendsto_gdInvQEpsOf {δS δC : ℕ → ℝ} (hS : Filter.Tendsto δS Filter.atTop (nhds 0))
    (hC : Filter.Tendsto δC Filter.atTop (nhds 0)) (c : ℝ) :
    Filter.Tendsto (fun w => gdInvQEpsOf (δS w) (δC w) c w) Filter.atTop (nhds 0) := by
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp (Filter.tendsto_add_atTop_nat 12)
  have h := (((hS.const_mul (1 / 2)).add (hC.const_mul (2 / (c / 2)))).add
    (h2.const_mul 13)).div_const (c / 2)
  simp only [mul_zero, add_zero, zero_div] at h
  refine h.congr fun w => ?_
  simp only [Function.comp, gdInvQEpsOf]
  ring

/-- The width bound of `gdInvOfSinCos`, for `V = (1 + σ)/c`. -/
noncomputable def gdInvEpsOf (V : ℝ) (Q : ℝ) (w : ℕ) : ℝ := lnOfEnclEps ⌈V⌉₊ (2 * Q) w

theorem tendsto_gdInvEpsOf (V : ℝ) {Q : ℕ → ℝ} (hQ : Filter.Tendsto Q Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun w => gdInvEpsOf V (Q w) w) Filter.atTop (nhds 0) := by
  have h1 := tendsto_lnEps (⌈V⌉₊ : ℤ)
  have h2 := hQ.const_mul 2
  have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hc : Filter.Tendsto (fun _ : ℕ => ((⌈V⌉₊ : ℝ) + 2)) Filter.atTop
      (nhds ((⌈V⌉₊ : ℝ) + 2)) := tendsto_const_nhds
  have h := (h1.add (h2.const_mul 4)).add ((((hc.add h1).const_mul 2).mul h3))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun w => ?_
  simp only [gdInvEpsOf, lnOfEnclEps]
  ring

/-- **The width of the step** once the enclosure of `c ∈ (0, 1]` is narrow enough
(`δC ≤ c/2`) and the quotient is known to `1/4`. -/
theorem gdInvOfSinCos_width {b : Encl × Encl} {σ c δS δC : ℝ} (hS : IsEnclW b.1 σ δS)
    (hC : IsEnclW b.2 c δC) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hδS : δS ≤ 1) (hc0 : 0 < c)
    (hc1 : c ≤ 1) {w : ℕ} (hw : 64 ≤ w) (hc : δC ≤ c / 2)
    (hq : gdInvQEpsOf δS δC c w ≤ 1 / 4) :
    IsEnclW (gdInvOfSinCos b w) (Real.log (2 * ((1 + σ) / 2 / c)))
      (gdInvEpsOf (2 * ((1 + σ) / 2 / c)) (gdInvQEpsOf δS δC c w) w) := by
  have hN := gdInvNum_spec hS hσ0 hσ1 hδS (V := w + 12) (by omega)
  have hu : (1 / 2 : ℝ) ^ (w + 12) ≤ 1 / 16 := by
    calc (1 / 2 : ℝ) ^ (w + 12) ≤ (1 / 2 : ℝ) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have hs : |(1 + σ) / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hQ := tanOfSinCos_width (b := (gdInvNum b.1 (w + 12), b.2)) hN hC hs (by linarith)
    (V := w + 12) (by omega) (abs_pos.mpr hc0.ne') (by rw [abs_of_pos hc0]; exact hc)
  rw [abs_of_pos hc0] at hQ
  have hY := isEnclW_double hQ
  set Vv := 2 * ((1 + σ) / 2 / c) with hVv
  have hV1 : 1 ≤ Vv := by
    have : Vv = (1 + σ) / c := by rw [hVv]; ring
    rw [this, le_div_iff₀ hc0]
    linarith
  have hVE : Vv < (2 : ℝ) ^ ⌈Vv⌉₊ := by
    calc Vv ≤ (⌈Vv⌉₊ : ℝ) := Nat.le_ceil Vv
      _ < (2 : ℝ) ^ ⌈Vv⌉₊ := by exact_mod_cast Nat.lt_two_pow_self
  have hE1 : 1 ≤ ⌈Vv⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h
    have := Nat.le_ceil Vv
    rw [h] at this
    norm_num at this
    linarith)
  unfold gdInvOfSinCos gdInvEpsOf
  dsimp only
  exact lnOfEncl_width hY hV1 (by unfold gdInvQEpsOf at hq; linarith) hE1 hVE hw

/-- The enclosures that `gdInvBracket` starts from. -/
theorem gdInvParts_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (hd : |xv| < π / 2) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (sinCosBracket x ex w).1 (Real.sin |xv|) (sinCosEps ex w) ∧
      IsEnclW (sinCosBracket x ex w).2 (Real.cos xv) (sinCosEps ex w) ∧
      0 ≤ Real.sin |xv| ∧ Real.sin |xv| ≤ 1 ∧ sinCosEps ex w ≤ 1 := by
  obtain ⟨hS, hC⟩ := sinCosBracket_spec hx hex hw
  exact ⟨hS, hC, sin_nonneg_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]),
    Real.sin_le_one _, sinCosEps_le_one ex hw⟩

/-- **At every level `w ≥ 64` the bracket is the dummy `[−1, 1]` or encloses `gd⁻¹ |x|`.** -/
theorem gdInvBracket_valid_or_dummy {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) (hd : |xv| < π / 2) {w : ℕ} (hw : 64 ≤ w) :
    gdInvBracket x ex w = (-one, one) ∨ IsEncl (gdInvBracket x ex w) (gdInv |xv|) := by
  obtain ⟨hS, hC, h0, h1, hδ⟩ := gdInvParts_spec hx hex hd hw
  rw [gdInv_abs_eq_log hd]
  exact gdInvOfSinCos_valid_or_dummy hS hC h0 h1 hδ hw

/-- **At every level `w ≥ 64` the bracket of `gdInvApprox neg` encloses `± gd⁻¹ |x|` or is
rejected by `roundingPossible`.** -/
theorem gdInvApprox_valid_or_none (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt)
    (hd : |xv| < π / 2) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (gdInvApprox neg x ex w).1 lv ∧ Rounds (gdInvApprox neg x ex w).2 hv ∧
        lv ≤ (if neg then -1 else 1) * gdInv |xv| ∧
        (if neg then -1 else 1) * gdInv |xv| ≤ hv) ∨
      roundingPossible (gdInvApprox neg x ex w).1 (gdInvApprox neg x ex w).2 p mode = none := by
  unfold gdInvApprox
  rcases gdInvBracket_valid_or_dummy hx hex hd hw with hdum | ⟨lo, hi, hlo, hhi, h1, h2⟩
  · right
    rw [hdum]
    exact roundingPossible_negSwapApprox_dummy neg p mode
  · left
    obtain ⟨lv, hv, hl, hh, k1, k2, -⟩ :=
      negSwapApprox_of_isEnclW neg ⟨lo, hi, hlo, hhi, h1, h2, le_rfl⟩
    exact ⟨lv, hv, hl, hh, k1, k2⟩

/-- The width of the quotient for a float argument. -/
noncomputable def gdInvQEps (c : ℝ) (ex : AzInt) (w : ℕ) : ℝ :=
  gdInvQEpsOf (sinCosEps ex w) (sinCosEps ex w) c w

theorem tendsto_gdInvQEps (c : ℝ) (ex : AzInt) :
    Filter.Tendsto (gdInvQEps c ex) Filter.atTop (nhds 0) :=
  tendsto_gdInvQEpsOf (tendsto_sinCosEps ex) (tendsto_sinCosEps ex) c

/-- The width bound of `gdInvBracket`, for `V = (1 + sin a)/cos a` and `c = cos a`. -/
noncomputable def gdInvEps (V c : ℝ) (ex : AzInt) (w : ℕ) : ℝ :=
  gdInvEpsOf V (gdInvQEps c ex w) w

theorem tendsto_gdInvEps (V c : ℝ) (ex : AzInt) :
    Filter.Tendsto (gdInvEps V c ex) Filter.atTop (nhds 0) :=
  tendsto_gdInvEpsOf V (tendsto_gdInvQEps c ex)

/-- **`gdInvBracket` encloses `gd⁻¹ |x|`** with width at most `gdInvEps V (cos x) ex w`, once
the enclosure of `cos x` is narrow enough (`sinCosEps ex w ≤ cos x / 2`) and the quotient is
known to `1/4` (`gdInvQEps ≤ 1/4`). -/
theorem gdInvBracket_width {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) (hd : |xv| < π / 2) {w : ℕ} (hw : 64 ≤ w)
    (hc : sinCosEps ex w ≤ Real.cos xv / 2) (hq : gdInvQEps (Real.cos xv) ex w ≤ 1 / 4) :
    IsEnclW (gdInvBracket x ex w) (gdInv |xv|)
      (gdInvEps (2 * ((1 + Real.sin |xv|) / 2 / Real.cos xv)) (Real.cos xv) ex w) := by
  obtain ⟨hS, hC, h0, h1, hδ⟩ := gdInvParts_spec hx hex hd hw
  rw [gdInv_abs_eq_log hd]
  exact gdInvOfSinCos_width hS hC h0 h1 hδ (cos_pos_of_mem_Ioo (abs_lt.mp hd))
    (Real.cos_le_one _) hw hc hq

/-- `gd⁻¹ x` is irrational for a nonzero finite float `x` with `|x| < π/2`. -/
theorem irrational_gdInv_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hd : |xv| < π / 2) : Irrational (gdInv xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [hq, Rat.cast_zero]
  rw [hq] at hd ⊢
  exact irrational_gdInv_rat hq0 hd

/-- The Ziv certificate for `gd⁻¹ x`, `x` a nonzero finite float with `|x| < π/2`. -/
theorem gdInvApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hd : |xv| < π / 2) (hneg : neg = true ↔ xv < 0) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gdInvApprox neg x ex (w₀ * 2 ^ f)).1
      (gdInvApprox neg x ex (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hcos : 0 < Real.cos xv := cos_pos_of_mem_Ioo (abs_lt.mp hd)
  obtain ⟨W₁, hW₁⟩ := ((tendsto_sinCosEps ex).eventually
    (gt_mem_nhds (half_pos hcos))).exists_forall_of_atTop
  obtain ⟨W₂, hW₂⟩ := ((tendsto_gdInvQEps (Real.cos xv) ex).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists_forall_of_atTop
  refine exists_isSome_of_irrational_threshold p mode (gdInvApprox neg x ex)
    (v := (if neg then -1 else 1) * gdInv |xv|) ?_
    (gdInvEps (2 * ((1 + Real.sin |xv|) / 2 / Real.cos xv)) (Real.cos xv) ex)
    (tendsto_gdInvEps _ _ ex) (max 64 (max W₁ W₂))
    (fun w hw => negSwapApprox_of_isEnclW neg (gdInvBracket_width hx hex hd
      (le_of_max_le_left hw) (hW₁ w (le_of_max_le_left (le_of_max_le_right hw))).le
      (hW₂ w (le_of_max_le_right (le_of_max_le_right hw))).le)) w₀ hw₀
  rw [← gdInv_eq_of_neg_iff hneg hd]
  exact irrational_gdInv_of_toVal hx hx0 hd

/-! ### The domain -/

/-- **The domain test**: `gdInvInDomain` holds exactly when `|x| < π/2`. -/
theorem gdInvInDomain_iff (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    gdInvInDomain (finite s e q m hv) e q = true ↔ |finiteVal s e m| < π / 2 := by
  have hpi := pi_gt_three
  have hb := abs_finiteVal_bounds s e hv
  unfold gdInvInDomain
  split_ifs with he
  · simp only [true_iff]
    have h1 : |finiteVal s e m| < 1 := abs_lt_one_of_exponent hb.2 (by
      rintro ⟨h1, h2⟩
      rcases he with h | h
      · rw [h1] at h; cases h
      · exact h2 h)
    linarith
  · have : NeZero q := ⟨hv.pos.ne'⟩
    have habs : (finite s e q m hv).abs.toVal = some ((|finiteVal s e m| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    have hP : (piDiv2PrecRound q .Floor).1.toVal
        = some ((RoundingTarget.round (floatSet q) .Floor (π / 2)).val) := by
      rw [piDiv2PrecRound_eq_liftVal₀]
      exact (roundVal_coe q .Floor (π / 2)).1
    obtain ⟨r, hr, hr1, -⟩ := roundVal_floor_spec q (π / 2)
    have hPr : (piDiv2PrecRound q .Floor).1.toVal = some (r : EReal) := by
      rw [piDiv2PrecRound_eq_liftVal₀]
      exact hr
    have hrv : ((r : ℝ) : EReal) = (RoundingTarget.round (floatSet q) .Floor (π / 2)).val :=
      Option.some.inj (hPr.symm.trans hP)
    rw [le_eq_true_iff habs hPr]
    constructor
    · intro hle
      refine lt_of_le_of_ne (hle.trans hr1) fun heq => ?_
      obtain ⟨t, ht⟩ := exists_rat_of_toVal habs
      have hirr : Irrational (π / 2) := irrational_pi.div_natCast (by norm_num : (2 : ℕ) ≠ 0)
      exact hirr ⟨t, by rw [← ht, heq]⟩
    · intro hlt
      have hmem : ((|finiteVal s e m| : ℝ) : EReal) ∈ floatSet q :=
        ⟨(finite s e q m hv).abs, Or.inl rfl, habs⟩
      have hg := (RoundingTarget.isGreatest_roundFloor (floatSet q) (π / 2)).2
        ⟨hmem, EReal.coe_le_coe_iff.mpr hlt.le⟩
      have : ((|finiteVal s e m| : ℝ) : EReal) ≤ ((r : ℝ) : EReal) := by
        rw [hrv]
        exact hg
      exact EReal.coe_le_coe_iff.mp this

/-! ### A rational argument -/

/-- The enclosures that `gdInvRatBracket` starts from. -/
theorem gdInvRatParts_spec (q : AzRat) (hd : |((AzRat.toRat q : ℚ) : ℝ)| < π / 2) {w : ℕ}
    (hw : 64 ≤ w) :
    IsEnclW (sinCosRatBracket q w).1 (Real.sin |((AzRat.toRat q : ℚ) : ℝ)|) (sinRatEps q w) ∧
      IsEnclW (sinCosRatBracket q w).2 (Real.cos (AzRat.toRat q : ℝ)) (cosRatEps q w) ∧
      0 ≤ Real.sin |((AzRat.toRat q : ℚ) : ℝ)| ∧ Real.sin |((AzRat.toRat q : ℚ) : ℝ)| ≤ 1 ∧
      sinRatEps q w ≤ 1 :=
  ⟨sinRatBracket_spec q hw, cosRatBracket_spec q hw,
    sin_nonneg_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]), Real.sin_le_one _,
    sinRatEps_le_one q hw⟩

/-- **At every level `w ≥ 64` the bracket of `gdInvRatApprox` encloses `gd⁻¹ q` or is rejected
by `roundingPossible`.** -/
theorem gdInvRatApprox_valid_or_none (q : AzRat) (h0 : q.num ≠ 0)
    (hd : |((AzRat.toRat q : ℚ) : ℝ)| < π / 2) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (gdInvRatApprox q w).1 lv ∧ Rounds (gdInvRatApprox q w).2 hv ∧
        lv ≤ gdInv (AzRat.toRat q : ℝ) ∧ gdInv (AzRat.toRat q : ℝ) ≤ hv) ∨
      roundingPossible (gdInvRatApprox q w).1 (gdInvRatApprox q w).2 p mode = none := by
  obtain ⟨hS, hC, hs0, hs1, hδ⟩ := gdInvRatParts_spec q hd hw
  have hval := gdInv_eq_of_neg_iff (toRat_neg_iff q h0) hd
  unfold gdInvRatApprox gdInvRatBracket
  rcases gdInvOfSinCos_valid_or_dummy hS hC hs0 hs1 hδ hw with hdum | ⟨lo, hi, hlo, hhi, h1, h2⟩
  · right
    rw [hdum]
    exact roundingPossible_negSwapApprox_dummy _ p mode
  · left
    rw [← gdInv_abs_eq_log hd] at h1 h2
    obtain ⟨lv, hv, hl, hh, k1, k2, -⟩ :=
      negSwapApprox_of_isEnclW (!q.sign) ⟨lo, hi, hlo, hhi, h1, h2, le_rfl⟩
    rw [← hval] at k1 k2
    exact ⟨lv, hv, hl, hh, k1, k2⟩

/-- `gd⁻¹ q` is irrational for a rational `q ≠ 0` with `|q| < π/2`. -/
theorem irrational_gdInv_toRat (q : AzRat) (h0 : q.num ≠ 0)
    (hd : |((AzRat.toRat q : ℚ) : ℝ)| < π / 2) : Irrational (gdInv (AzRat.toRat q : ℝ)) :=
  irrational_gdInv_rat (q := AzRat.toRat q)
    (fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp (by rw [h, Rat.cast_zero]))) hd

/-- The Ziv certificate for `gd⁻¹ q`. -/
theorem gdInvRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (hd : |((AzRat.toRat q : ℚ) : ℝ)| < π / 2) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gdInvRatApprox q (w₀ * 2 ^ f)).1
      (gdInvRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  have hcos : 0 < Real.cos qv := cos_pos_of_mem_Ioo (abs_lt.mp hd)
  have hQ := tendsto_gdInvQEpsOf (tendsto_sinRatEps q) (tendsto_cosRatEps q) (Real.cos qv)
  obtain ⟨W₁, hW₁⟩ := ((tendsto_cosRatEps q).eventually
    (gt_mem_nhds (half_pos hcos))).exists_forall_of_atTop
  obtain ⟨W₂, hW₂⟩ := (hQ.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists_forall_of_atTop
  have hval := gdInv_eq_of_neg_iff (toRat_neg_iff q h0) hd
  refine exists_isSome_of_irrational_threshold p mode (gdInvRatApprox q)
    (v := (if (!q.sign) = true then -1 else 1) * gdInv |qv|) ?_
    (fun w => gdInvEpsOf (2 * ((1 + Real.sin |qv|) / 2 / Real.cos qv))
      (gdInvQEpsOf (sinRatEps q w) (cosRatEps q w) (Real.cos qv) w) w)
    (tendsto_gdInvEpsOf _ hQ) (max 64 (max W₁ W₂)) (fun w hw => ?_) w₀ hw₀
  · rw [← hval]
    exact irrational_gdInv_toRat q h0 hd
  · have hw64 : 64 ≤ w := le_of_max_le_left hw
    obtain ⟨hS, hC, hs0, hs1, hδ⟩ := gdInvRatParts_spec q hd hw64
    have hwid := gdInvOfSinCos_width hS hC hs0 hs1 hδ hcos (Real.cos_le_one _) hw64
      (hW₁ w (le_of_max_le_left (le_of_max_le_right hw))).le
      (hW₂ w (le_of_max_le_right (le_of_max_le_right hw))).le
    rw [← gdInv_abs_eq_log hd] at hwid
    exact negSwapApprox_of_isEnclW (!q.sign) hwid

/-- **The domain test for a rational**: `gdInvRatInDomain q` holds exactly when `|q| < π/2`. -/
theorem gdInvRatInDomain_iff (q : AzRat) (h0 : q.num ≠ 0) :
    gdInvRatInDomain q = true ↔ |((AzRat.toRat q : ℚ) : ℝ)| < π / 2 := by
  have hpi := pi_gt_three
  have hpi4 := pi_le_four
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  unfold gdInvRatInDomain
  split_ifs with h1 h2
  · simp only [true_iff]
    have := (abs_toRat_le_one_iff q).mp h1
    linarith
  · simp only [false_iff, not_lt]
    have := (one_le_abs_toRat_iff (q >>> (1 : ℕ))).mp h2
    rw [toRat_half_abs] at this
    linarith
  · have hlt2 : |qv| < 2 := by
      have := not_le.mp fun h => h2 ((one_le_abs_toRat_iff (q >>> (1 : ℕ))).mpr h)
      rw [toRat_half_abs] at this
      linarith
    have hirr := irrational_cos_toRat q h0
    have hR : cosRatPrecRound q 1 .Floor
        = roundVal 1 .Floor (some ((Real.cos qv : ℝ) : EReal)) := by
      rw [cosRatPrecRound_eq, Spec.cos_coe]
    obtain ⟨v, hv, hv1, hv2⟩ := roundVal_floor_spec 1 (Real.cos qv)
    rw [← hR] at hv
    obtain ⟨hn1, hn2⟩ := toVal_sign_of_isNegative hv
    have hcosabs : Real.cos qv = Real.cos |qv| := (Real.cos_abs qv).symm
    rw [Bool.not_eq_true']
    constructor
    · intro hneg
      have hc0 : 0 ≤ Real.cos qv := (hn2 hneg).trans hv1
      have hcpos : 0 < Real.cos qv := lt_of_le_of_ne hc0 (Ne.symm hirr.ne_zero)
      by_contra hcon
      push Not at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith)
      rw [← hcosabs] at this
      linarith
    · intro hd
      have hcpos : 0 < Real.cos qv := cos_pos_of_mem_Ioo (abs_lt.mp hd)
      by_contra hcon
      have := hn1 (by simpa using hcon)
      linarith [hv2 hcpos.le]

end Azurite.AzFloat
