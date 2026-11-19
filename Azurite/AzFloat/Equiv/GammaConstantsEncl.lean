/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AgmConstants
import Azurite.AzFloat.Equiv.Agm
import Azurite.AzFloat.Equiv.Cbrt
import Azurite.AzFloat.Equiv.GammaBracket
import Azurite.Transcendental.GammaAGM

/-!
# The enclosures of `Γ(1/4)` and `Γ(1/3)`: correctness

* `lnGammaApproxOf_spec`: a bracket as `Roundable`s encloses its value, strictly from below.
* `IsEnclPos.sqrt`, `IsEnclPos.cbrt`, `IsEnclPos.agm`, `IsEnclPos.half`: the operations on
  positive enclosures.
* `gammaOneQuarterEncl_spec`, `gammaOneThirdEncl_spec`, and the brackets as `Roundable`s
  (`gammaOneQuarterApprox_spec`, `gammaOneThirdApprox_spec`), from the AGM formulas of
  `Transcendental/GammaAGM.lean`.
-/

namespace Azurite.AzFloat

open Azurite.BZ RoundingTarget

variable {w : ℕ} {a b : Encl} {x y : ℝ}

/-- A bracket as `Roundable`s encloses its value, strictly from below. -/
theorem lnGammaApproxOf_spec {b : Encl} {v : ℝ} (hb : IsEncl b v) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (lnGammaApproxOf b w).1 lv ∧ Rounds (lnGammaApproxOf b w).2 hv ∧
      lv < v ∧ v ≤ hv := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := hb
  have : NeZero (2 * w + 64) := ⟨by omega⟩
  have ht : (powerOf2 (-(AzNat.ofNat (4 * w)).toAzInt)).toVal
      = some (((1 / 2 : ℝ) ^ (4 * w) : ℝ) : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_neg, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg,
      zpow_natCast, one_div_pow, one_div]
  obtain ⟨r, hr, hrle, -⟩ := subFloor_le hlo ht (2 * w + 64)
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ (4 * w) := by positivity
  refine ⟨r, hi, ?_, ?_, by linarith, h2⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hr)
    rw [fval_of_toVal_coe hr] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR

theorem isEnclPos_nat {n : ℕ} (hn : 0 < n) : IsEnclPos (Encl.nat n) n :=
  isEnclPos_exact (toVal_ofAzNat_ofNat n) (by exact_mod_cast hn)

theorem IsEnclPos.half (h : IsEnclPos a x) : IsEnclPos (Encl.half a) (x / 2) := by
  obtain ⟨l, u, hl, hu, h0, h1, h2⟩ := h
  have e1 := toVal_shiftLeft_of_toVal hl (AzInt.ofInt (-1))
  have e2 := toVal_shiftLeft_of_toVal hu (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at e1 e2
  exact ⟨l / 2, u / 2, e1, e2, by linarith, by linarith, by linarith⟩

theorem IsEnclPos.sqrt [NeZero w] (hw : 2 ≤ w) (h : IsEnclPos a x) :
    IsEnclPos (Encl.sqrt w a) (Real.sqrt x) := by
  obtain ⟨l, u, hl, hu, h0, h1, h2⟩ := h
  obtain ⟨r, hr, hr1⟩ := sqrtFloor_err hl h0.le w
  obtain ⟨s, hs, hs1⟩ := sqrtCeiling_spec hu (by linarith) w
  exact ⟨r, s, hr, hs, hr1.pos hw (Real.sqrt_pos.mpr h0),
    hr1.le.trans (Real.sqrt_le_sqrt h1), (Real.sqrt_le_sqrt h2).trans hs1⟩

theorem realCbrt_le_realCbrt {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : realCbrt s ≤ realCbrt t := by
  rw [realCbrt_of_nonneg hs, realCbrt_of_nonneg (hs.trans hst)]
  exact Real.rpow_le_rpow hs hst (by positivity)

theorem realCbrt_pos {s : ℝ} (hs : 0 < s) : 0 < realCbrt s := by
  rw [realCbrt_of_nonneg hs.le]
  exact Real.rpow_pos_of_pos hs _

theorem IsEnclPos.cbrt [NeZero w] (hw : 2 ≤ w) (h : IsEnclPos a x) :
    IsEnclPos (Encl.cbrt w a) (realCbrt x) := by
  obtain ⟨l, u, hl, hu, h0, h1, h2⟩ := h
  obtain ⟨r, hr, hr1⟩ : ∃ r : ℝ, (cbrtPrecRound a.1 w .Floor).1.toVal = some (r : EReal) ∧
      FloorOf w (realCbrt l) r := by
    rw [cbrtPrecRound_eq_liftVal, liftVal, hl, Option.bind_some, Spec.cbrt_coe]
    exact roundVal_floor_err w (realCbrt_nonneg h0.le)
  obtain ⟨s, hs, hs1⟩ : ∃ s : ℝ, (cbrtPrecRound a.2 w .Ceiling).1.toVal = some (s : EReal) ∧
      realCbrt u ≤ s := by
    rw [cbrtPrecRound_eq_liftVal, liftVal, hu, Option.bind_some, Spec.cbrt_coe]
    exact roundVal_ceiling_spec w _
  exact ⟨r, s, hr, hs, hr1.pos hw (realCbrt_pos h0),
    hr1.le.trans (realCbrt_le_realCbrt h0.le h1),
    (realCbrt_le_realCbrt (h0.le.trans h1) h2).trans hs1⟩

/-- The interval AGM of two positive enclosures is a positive enclosure of the AGM. -/
theorem IsEnclPos.agm [NeZero w] (ha : IsEnclPos a x) (hb : IsEnclPos b y) :
    IsEnclPos (Encl.agm w a b) (AGM x y) := by
  obtain ⟨la, ua, hla, hua, ha0, ha1, ha2⟩ := ha
  obtain ⟨lb, ub, hlb, hub, hb0, hb1, hb2⟩ := hb
  have hx : 0 < x := ha0.trans_le ha1
  have hy : 0 < y := hb0.trans_le hb1
  have h₀ : Encloses x y 0 ⟨a.1, a.2, b.1, b.2⟩ :=
    encloses_init_bounds hla hua hlb hub ha0.le ha1 ha2 hb0.le hb1 hb2
  obtain ⟨m, hm, ⟨-, ⟨ah, hah, hahge⟩, ⟨bl, hbl, -, hblle⟩, -⟩⟩ :=
    encloses_agmIter hx hy w (w + 4) _ 1 (encloses_agmStep hx hy w h₀)
  have hup : AGM x y ≤ ah := (AGM_le_agmA hx hy hm).trans hahge
  have hmin := min_le_AGM hx hy
  unfold Encl.agm
  dsimp only
  by_cases h1 : lt zero (agmIter w (w + 4) (agmStep w ⟨a.1, a.2, b.1, b.2⟩)).bLo = true
  · rw [ite_eq_left h1]
    exact ⟨bl, ah, hbl, hah, (lt_eq_true_iff toVal_zero' hbl).mp h1,
      hblle.trans (agmB_le_AGM hx hy hm), hup⟩
  · rw [ite_eq_right h1]
    by_cases h2 : le a.1 b.1 = true
    · rw [ite_eq_left h2]
      have := (le_eq_true_iff hla hlb).mp h2
      exact ⟨la, ah, hla, hah, ha0, (le_min ha1 (by linarith)).trans hmin, hup⟩
    · rw [ite_eq_right h2]
      have := not_le.mp (fun h => h2 ((le_eq_true_iff hla hlb).mpr h))
      exact ⟨lb, ah, hlb, hah, hb0, (le_min (by linarith) hb1).trans hmin, hup⟩

/-- **`gammaOneQuarterEncl` encloses `Γ(1/4)`.** -/
theorem gammaOneQuarterEncl_spec {w : ℕ} (hw : 64 ≤ w) :
    IsEncl (gammaOneQuarterEncl w) (Real.Gamma (1 / 4)) := by
  unfold gammaOneQuarterEncl
  dsimp only
  have : NeZero (w + 32) := ⟨by omega⟩
  have hW : 2 ≤ w + 32 := by omega
  have hM := (enclosesPos_one.agm (w := w + 32) ((isEnclPos_nat (by norm_num : 0 < 2)).sqrt hW))
  have hT := (isEnclPos_nat (by norm_num : 0 < 2)).mul hW (enclosesPos_pi (w := w + 32) (by omega))
  have hE := (((hT.mul hW (hT.sqrt hW)).div hW hM).sqrt hW).encloses0.encloses
  convert hE using 1
  have hg : 0 ≤ Real.Gamma (1 / 4) := (Real.Gamma_pos_of_pos (by norm_num)).le
  rw [← Real.sqrt_sq hg, gamma_one_quarter_sq]
  norm_num

/-- **`gammaOneThirdEncl` encloses `Γ(1/3)`.** -/
theorem gammaOneThirdEncl_spec {w : ℕ} (hw : 64 ≤ w) :
    IsEncl (gammaOneThirdEncl w) (Real.Gamma (1 / 3)) := by
  unfold gammaOneThirdEncl
  dsimp only
  have : NeZero (w + 32) := ⟨by omega⟩
  have hW : 2 ≤ w + 32 := by omega
  have h3 := (isEnclPos_nat (by norm_num : 0 < 3))
  have hr := h3.sqrt hW
  have hA := ((hr.add hW h3.half.encloses0).half).sqrt hW
  have hM := hA.agm (w := w + 32) (hr.sqrt hW)
  have hP := enclosesPos_pi (w := w + 32) (by omega)
  have h2 := (isEnclPos_nat (by norm_num : 0 < 2))
  have hN := ((h2.mul hW (h2.cbrt hW)).mul hW (hP.mul hW hP))
  have hE := ((hN.div hW hM).cbrt hW).encloses0.encloses
  convert hE using 1
  have hg : 0 ≤ Real.Gamma (1 / 3) := (Real.Gamma_pos_of_pos (by norm_num)).le
  symm
  apply realCbrt_eq_of_pow_three hg
  rw [gamma_one_third_cube (realCbrt_pos (by norm_num : (0 : ℝ) < 2)) (realCbrt_pow_three 2)]
  push_cast
  ring

theorem gammaOneQuarterApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (gammaOneQuarterApprox w).1 lv ∧ Rounds (gammaOneQuarterApprox w).2 hv ∧
      lv ≤ Real.Gamma (1 / 4) ∧ Real.Gamma (1 / 4) ≤ hv ∧
      (lv = Real.Gamma (1 / 4) → hv = Real.Gamma (1 / 4)) := by
  obtain ⟨lv, hv, h1, h2, h3, h4⟩ := lnGammaApproxOf_spec (gammaOneQuarterEncl_spec hw) w
  exact ⟨lv, hv, h1, h2, h3.le, h4, fun h => absurd h h3.ne⟩

theorem gammaOneThirdApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (gammaOneThirdApprox w).1 lv ∧ Rounds (gammaOneThirdApprox w).2 hv ∧
      lv ≤ Real.Gamma (1 / 3) ∧ Real.Gamma (1 / 3) ≤ hv ∧
      (lv = Real.Gamma (1 / 3) → hv = Real.Gamma (1 / 3)) := by
  obtain ⟨lv, hv, h1, h2, h3, h4⟩ := lnGammaApproxOf_spec (gammaOneThirdEncl_spec hw) w
  exact ⟨lv, hv, h1, h2, h3.le, h4, fun h => absurd h h3.ne⟩

end Azurite.AzFloat
