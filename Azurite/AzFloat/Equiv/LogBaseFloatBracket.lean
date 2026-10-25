/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseFloatBracket
import Azurite.AzFloat.Equiv.LogBaseBracket
import Azurite.AzFloat.Equiv.LogBaseExact
import Azurite.AzRat.Equiv.Sub

/-!
# Equivalence: the bracket of `log_b x` for a float base

* `lnBaseFloatBracket_spec`: a bracket of `ln b` of width `lnEps eb w` whose ends are bounded away
  from `0` on the side of `ln b` by `lnKappa b` (`(b − 1)/(4b)` for `b > 1`, `(1 − b)/2` for
  `b < 1`), at every working precision `w ≥ 64`.
* `divBracketByPosBracket_spec`: dividing a bracket of `L` by a bracket `(c, d)` of `M` with
  `0 < c` gives a bracket of `L / M` of width `divEps (1/c) |L| ε δ w`.
* `logBaseQuotCore_spec`/`logBaseQuotWith_spec`: dividing a bracket of `L` by a bracket of `M`
  whose ends have the sign of `M` (bounded away from `0` by `κ`) gives a (strict) bracket of
  `L / M`; `logBaseFloatQuot_spec` is the instance for the clamped float bracket of `ln b`, and
  `lnRatBaseBracket_spec`/`logBaseRatBaseApprox_spec` cover a rational base;
  `logBaseFloatApprox_spec` (width
  `logBaseFloatEps`) and `logBaseFloatP1Approx_spec` (width `logBaseFloatP1Eps`) are its
  instances, with the Ziv certificates `logBaseFloatApprox_isSome_exists` and
  `logBaseFloatP1Approx_isSome_exists`.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### `maxOf`, `minOf`, `normShift` -/

theorem toVal_maxOf {x y : AzFloat} {xv yv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hy : y.toVal = some (yv : EReal)) : (maxOf x y).toVal = some ((max xv yv : ℝ) : EReal) := by
  unfold maxOf
  rw [partialCompare_eq, hx, hy]
  simp only [compare_coe_coe, beq_iff_eq, Option.some.injEq]
  split_ifs with h
  · rw [compare_lt_iff_lt] at h
    rw [hy, max_eq_right h.le]
  · rw [compare_lt_iff_lt] at h
    push Not at h
    rw [hx, max_eq_left h]

theorem toVal_minOf {x y : AzFloat} {xv yv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hy : y.toVal = some (yv : EReal)) : (minOf x y).toVal = some ((min xv yv : ℝ) : EReal) := by
  unfold minOf
  rw [partialCompare_eq, hx, hy]
  simp only [compare_coe_coe, beq_iff_eq, Option.some.injEq]
  split_ifs with h
  · rw [compare_lt_iff_lt] at h
    rw [hy, min_eq_right h.le]
  · rw [compare_lt_iff_lt] at h
    push Not at h
    rw [hx, min_eq_left h]

/-- The shift of a positive float brings it to `[1/2, ∞)` and is at most `1 + 1/c`. -/
theorem normShift_spec {c : AzFloat} {cv : ℝ} (hc : c.toVal = some (cv : EReal)) (hpos : 0 < cv) :
    1 / 2 ≤ cv * (2 : ℝ) ^ (normShift c).toInt ∧
      (2 : ℝ) ^ (normShift c).toInt ≤ 1 + 1 / cv := by
  rcases c with _ | s | _ | ⟨s, e, q, m, hv⟩
  · simp at hc
  · cases s <;> simp at hc
  · simp only [toVal_zero, Option.some.injEq] at hc
    exact absurd (EReal.coe_eq_zero.mp hc.symm) hpos.ne'
  · simp only [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hc
    cases s with
    | false =>
      exfalso
      rw [finiteVal_false] at hc
      have := finiteVal_true_pos e hv
      linarith
    | true =>
      obtain ⟨hlo, hhi⟩ := abs_finiteVal_bounds true e hv
      rw [abs_of_pos (finiteVal_true_pos e hv), hc] at hlo hhi
      have hns : normShift (finite true e q m hv) = if e ≤ 0 then -e else 0 := rfl
      rw [hns]
      split_ifs with h
      · rw [AzInt.le_iff_toInt_le, AzInt.toInt_zero] at h
        rw [AzInt.toInt_neg]
        have h2 : (0 : ℝ) < (2 : ℝ) ^ (-e.toInt) := zpow_pos two_pos _
        constructor
        · calc (1 / 2 : ℝ) = (2 : ℝ) ^ (e.toInt - 1) * (2 : ℝ) ^ (-e.toInt) := by
                rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0),
                  show e.toInt - 1 + -e.toInt = -1 by ring, zpow_neg_one]
                norm_num
            _ ≤ cv * (2 : ℝ) ^ (-e.toInt) := mul_le_mul_of_nonneg_right hlo h2.le
        · rw [zpow_neg]
          have : ((2 : ℝ) ^ e.toInt)⁻¹ < cv⁻¹ := inv_strictAnti₀ hpos hhi
          rw [one_div]
          linarith [inv_pos.mpr hpos]
      · rw [AzInt.le_iff_toInt_le, AzInt.toInt_zero] at h
        push Not at h
        rw [AzInt.toInt_zero, zpow_zero, mul_one]
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (e.toInt - 1) := one_le_zpow₀ one_le_two (by omega)
        constructor
        · linarith
        · linarith [one_div_pos.mpr hpos]

/-! ### Dividing by a positive bracket -/

/-- The width bound of `divBracketByPosBracket` (`K` bounds the shift `2^l ≤ 1 + 1/c`). -/
noncomputable def divEps (K A ε δ : ℝ) (w : ℕ) : ℝ :=
  (1 + K) * (2 * ε + 8 * (A + ε) * ((1 + K) * δ + (1 / 2 : ℝ) ^ w))

theorem divEps_mono {K K' A ε δ : ℝ} (w : ℕ) (hK : K ≤ K') (hK0 : 0 ≤ K) (hA : 0 ≤ A)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) : divEps K A ε δ w ≤ divEps K' A ε δ w := by
  unfold divEps
  have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have h1 : (1 + K) * δ ≤ (1 + K') * δ := mul_le_mul_of_nonneg_right (by linarith) hδ
  have h2 : 8 * (A + ε) * ((1 + K) * δ + (1 / 2 : ℝ) ^ w)
      ≤ 8 * (A + ε) * ((1 + K') * δ + (1 / 2 : ℝ) ^ w) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)

theorem divBracketByPosBracket_spec {w : ℕ} (hw : 64 ≤ w) {X B : AzFloat × AzFloat}
    {a bv c d L M ε δ : ℝ} (ha : X.1.toVal = some (a : EReal)) (hb : X.2.toVal = some (bv : EReal))
    (hc : B.1.toVal = some (c : EReal)) (hd : B.2.toVal = some (d : EReal))
    (hc0 : 0 < c) (hcM : c ≤ M) (hMd : M ≤ d) (hcd : d - c ≤ δ)
    (haL : a ≤ L) (hLb : L ≤ bv) (hwid : bv - a ≤ ε) :
    ∃ lo hi : ℝ, (divBracketByPosBracket X B w).1.toVal = some (lo : EReal) ∧
      (divBracketByPosBracket X B w).2.toVal = some (hi : EReal) ∧
      lo ≤ L / M ∧ L / M ≤ hi ∧ hi - lo ≤ divEps (1 / c) |L| ε δ w := by
  obtain ⟨h12, hK⟩ := normShift_spec hc hc0
  unfold divBracketByPosBracket
  simp only []
  set l := normShift B.1 with hl
  set K := (2 : ℝ) ^ l.toInt with hK_def
  have hK0 : 0 < K := zpow_pos two_pos _
  have hM0 : 0 < M := lt_of_lt_of_le hc0 hcM
  have hc' := toVal_shiftLeft_of_toVal hc l
  have hd' := toVal_shiftLeft_of_toVal hd l
  rw [← hK_def] at hc' hd'
  obtain ⟨lo', hi', hlo', hhi', hlo1, hhi1, hwidth⟩ :=
    quotientBracket_spec hw ha hb (cd := (B.1 <<< l, B.2 <<< l)) (δ := δ * K) hc' hd' h12
      (mul_le_mul_of_nonneg_right hcM hK0.le)
      (mul_le_mul_of_nonneg_right hMd hK0.le)
      (by rw [← sub_mul]; exact mul_le_mul_of_nonneg_right hcd hK0.le) haL hLb hwid
  have hlo := toVal_shiftLeft_of_toVal hlo' l
  have hhi := toVal_shiftLeft_of_toVal hhi' l
  rw [← hK_def] at hlo hhi
  refine ⟨lo' * K, hi' * K, hlo, hhi, ?_, ?_, ?_⟩
  · calc lo' * K ≤ L / (M * K) * K := mul_le_mul_of_nonneg_right hlo1 hK0.le
      _ = L / M := by field_simp
  · calc L / M = L / (M * K) * K := by field_simp
      _ ≤ hi' * K := mul_le_mul_of_nonneg_right hhi1 hK0.le
  · have hε0 : 0 ≤ ε := by linarith
    have hδ0 : 0 ≤ δ := by linarith
    have hu : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    have hA : 0 ≤ |L| := abs_nonneg L
    have hinner : 2 * ε + 8 * (|L| + ε) * (δ * K + (1 / 2 : ℝ) ^ w)
        ≤ 2 * ε + 8 * (|L| + ε) * ((1 + 1 / c) * δ + (1 / 2 : ℝ) ^ w) := by
      have : δ * K ≤ (1 + 1 / c) * δ := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hK hδ0
      have := mul_le_mul_of_nonneg_left (add_le_add_right this ((1 / 2 : ℝ) ^ w))
        (by positivity : (0 : ℝ) ≤ 8 * (|L| + ε))
      linarith
    calc hi' * K - lo' * K = (hi' - lo') * K := by ring
      _ ≤ (2 * ε + 8 * (|L| + ε) * (δ * K + (1 / 2 : ℝ) ^ w)) * K :=
          mul_le_mul_of_nonneg_right hwidth hK0.le
      _ ≤ (2 * ε + 8 * (|L| + ε) * ((1 + 1 / c) * δ + (1 / 2 : ℝ) ^ w)) * (1 + 1 / c) :=
          mul_le_mul hinner hK (by positivity) (by positivity)
      _ = divEps (1 / c) |L| ε δ w := by unfold divEps; ring

/-! ### The bracket of `ln b` -/

/-- The lower bound on `|ln b|` used by the clamped bracket. -/
noncomputable def lnKappa (bv : ℝ) : ℝ := if 1 < bv then (bv - 1) / (4 * bv) else (1 - bv) / 2

theorem lnKappa_pos {bv : ℝ} (hb1 : bv ≠ 1) : 0 < lnKappa bv := by
  unfold lnKappa
  split_ifs with h
  · exact div_pos (by linarith) (by linarith)
  · push Not at h
    exact div_pos (by linarith [lt_of_le_of_ne h hb1]) (by norm_num)

/-- `ln b` is bracketed with width `lnEps eb w`, and the end on the side of `ln b` is at least
`lnKappa b` in absolute value. -/
theorem lnBaseFloatBracket_spec {w : ℕ} (hw : 64 ≤ w) (eb : AzInt) {qb : ℕ} {mb : AzNat}
    (hvb : FiniteValid qb mb) (hb1 : finiteVal true eb mb ≠ 1) :
    ∃ c d : ℝ, (lnBaseFloatBracket (finite true eb qb mb hvb) eb w).1.toVal = some (c : EReal) ∧
      (lnBaseFloatBracket (finite true eb qb mb hvb) eb w).2.toVal = some (d : EReal) ∧
      c ≤ Real.log (finiteVal true eb mb) ∧ Real.log (finiteVal true eb mb) ≤ d ∧
      d - c ≤ lnEps eb.toInt w ∧
      (eb.sign = true ∧ eb.abs ≠ 0 → lnKappa (finiteVal true eb mb) ≤ c) ∧
      (¬ (eb.sign = true ∧ eb.abs ≠ 0) → d ≤ -lnKappa (finiteVal true eb mb)) := by
  have : NeZero w := ⟨by omega⟩
  set bv := finiteVal true eb mb with hbv
  have hb := toVal_finite true eb qb mb hvb
  rw [← hbv] at hb
  have hpos : 0 < bv := finiteVal_true_pos eb hvb
  have hu : (1 / 2 : ℝ) ^ w ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  obtain ⟨c₀, d₀, hc₀, hd₀, hlo, hhi, hwid⟩ := lnBracket_spec hw eb hvb
  rw [← hbv] at hlo hhi
  unfold lnBaseFloatBracket
  simp only []
  split_ifs with hge
  · -- `b > 1`
    have h1 : 1 ≤ bv := by
      have := finiteVal_false_le_neg_one eb hvb hge
      rw [finiteVal_false, ← hbv] at this
      linarith
    have hgt : 1 < bv := lt_of_le_of_ne h1 (Ne.symm hb1)
    obtain ⟨t, ht, hft⟩ := addFloor_err hb toVal_neg_one w (by linarith)
    have ht0 : 0 ≤ t := hft.nonneg
    obtain ⟨c', hc', hfc⟩ := divFloor_err ht hb hpos ht0 w
    refine ⟨max c₀ c', d₀, toVal_maxOf hc₀ hc', hd₀, ?_, hhi, ?_, ?_, fun h => absurd hge h⟩
    · apply max_le hlo
      calc c' ≤ t / bv := hfc.le
        _ ≤ (bv + -1) / bv := div_le_div_of_nonneg_right hft.le hpos.le
        _ = 1 - bv⁻¹ := by field_simp; ring
        _ ≤ Real.log bv := Real.one_sub_inv_le_log_of_pos hpos
    · linarith [le_max_left c₀ c']
    · intro _
      refine le_trans ?_ (le_max_right c₀ c')
      unfold lnKappa
      rw [ite_eq_left hgt]
      -- `t ≥ (b − 1)/2` and `c' ≥ (t/b)/2`
      have ht2 : (bv - 1) / 2 ≤ t := by
        have := hft.ge
        have hx : 0 ≤ bv + -1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hu hx]
      have hc2 : t / bv / 2 ≤ c' := by
        have := hfc.ge
        have hx : 0 ≤ t / bv := div_nonneg ht0 hpos.le
        nlinarith [mul_le_mul_of_nonneg_left hu hx]
      calc (bv - 1) / (4 * bv) = (bv - 1) / 2 / bv / 2 := by field_simp; ring
        _ ≤ t / bv / 2 := by gcongr
        _ ≤ c' := hc2
  · -- `b < 1`
    have hlt : bv < 1 := by
      have := finiteVal_false_gt_neg_one eb hvb hge
      rw [finiteVal_false, ← hbv] at this
      linarith
    have hnb : (-finite true eb qb mb hvb).toVal = some ((-bv : ℝ) : EReal) := by
      rw [toVal_neg, hb, Option.map_some, EReal.coe_neg]
    obtain ⟨t, ht, hft⟩ := addFloor_err toVal_one' hnb w (by linarith)
    have hnt : (-(addPrecRound one (-finite true eb qb mb hvb) w .Floor).1).toVal
        = some ((-t : ℝ) : EReal) := by
      rw [toVal_neg, ht, Option.map_some, EReal.coe_neg]
    refine ⟨c₀, min d₀ (-t), hc₀, toVal_minOf hd₀ hnt, hlo, ?_, ?_, fun h => absurd h hge, ?_⟩
    · apply le_min hhi
      calc Real.log bv ≤ bv - 1 := Real.log_le_sub_one_of_pos hpos
        _ ≤ -t := by linarith [hft.le]
    · linarith [min_le_left d₀ (-t)]
    · intro _
      refine le_trans (min_le_right d₀ (-t)) ?_
      unfold lnKappa
      rw [ite_eq_right (not_lt.mpr hlt.le)]
      have ht2 : (1 - bv) / 2 ≤ t := by
        have := hft.ge
        have hx : 0 ≤ 1 + -bv := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hu hx]
      linarith

/-! ### Dividing by a signed bracket -/

/-- `logBaseQuotCore` brackets `L / M` with width `divEps (1 / κ) |L| ε δ w`, given a bracket
`(c, d)` of `M` with `κ ≤ c` (`pos = true`) or `d ≤ −κ` (`pos = false`). -/
theorem logBaseQuotCore_spec {w : ℕ} (hw : 64 ≤ w) {X B : AzFloat × AzFloat}
    {a bv c d L M ε δ κ : ℝ} (ha : X.1.toVal = some (a : EReal))
    (hb' : X.2.toVal = some (bv : EReal)) (hc : B.1.toVal = some (c : EReal))
    (hd : B.2.toVal = some (d : EReal)) (hcM : c ≤ M) (hMd : M ≤ d) (hcd : d - c ≤ δ)
    (haL : a ≤ L) (hLb : L ≤ bv) (hwid : bv - a ≤ ε) (hκ : 0 < κ) (pos : Bool)
    (hpos : pos = true → κ ≤ c) (hneg : pos = false → d ≤ -κ) :
    ∃ lo hi : ℝ, (logBaseQuotCore X B pos w).1.toVal = some (lo : EReal) ∧
      (logBaseQuotCore X B pos w).2.toVal = some (hi : EReal) ∧
      lo ≤ L / M ∧ L / M ≤ hi ∧ hi - lo ≤ divEps (1 / κ) |L| ε δ w := by
  have hε0 : 0 ≤ ε := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  unfold logBaseQuotCore
  cases pos with
  | true =>
    simp only [↓reduceIte]
    have hκc' := hpos rfl
    have hc0 : 0 < c := lt_of_lt_of_le hκ hκc'
    obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ :=
      divBracketByPosBracket_spec hw ha hb' hc hd hc0 hcM hMd hcd haL hLb hwid
    refine ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth.trans ?_⟩
    exact divEps_mono w (one_div_le_one_div_of_le hκ hκc') (by positivity) (abs_nonneg L) hε0 hδ0
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hdκ' := hneg rfl
    have hd0 : 0 < -d := by linarith
    have hnc : (-B.1).toVal = some ((-c : ℝ) : EReal) := by
      rw [toVal_neg, hc, Option.map_some, EReal.coe_neg]
    have hnd : (-B.2).toVal = some ((-d : ℝ) : EReal) := by
      rw [toVal_neg, hd, Option.map_some, EReal.coe_neg]
    obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ :=
      divBracketByPosBracket_spec hw ha hb' (B := (_, _)) (M := -M) (δ := δ) hnd hnc hd0
        (by linarith) (by linarith) (by linarith) haL hLb hwid
    have hnlo : (-(divBracketByPosBracket X (-B.2, -B.1) w).2).toVal
        = some ((-hi : ℝ) : EReal) := by rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(divBracketByPosBracket X (-B.2, -B.1) w).1).toVal
        = some ((-lo : ℝ) : EReal) := by rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    refine ⟨-hi, -lo, hnlo, hnhi, ?_, ?_, ?_⟩
    · rw [div_neg] at hhi1; linarith
    · rw [div_neg] at hlo1; linarith
    · have := hwidth.trans (divEps_mono w (one_div_le_one_div_of_le hκ (by linarith))
        (by positivity) (abs_nonneg L) hε0 hδ0)
      linarith

/-- `logBaseQuotWith` rounds a strict bracket of `L / M` (given irrationality). -/
theorem logBaseQuotWith_spec {w : ℕ} (hw : 64 ≤ w) {X B : AzFloat × AzFloat}
    {a bv c d L M ε δ κ : ℝ} (ha : X.1.toVal = some (a : EReal))
    (hb' : X.2.toVal = some (bv : EReal)) (hc : B.1.toVal = some (c : EReal))
    (hd : B.2.toVal = some (d : EReal)) (hcM : c ≤ M) (hMd : M ≤ d) (hcd : d - c ≤ δ)
    (haL : a ≤ L) (hLb : L ≤ bv) (hwid : bv - a ≤ ε) (hκ : 0 < κ) (pos : Bool)
    (hpos : pos = true → κ ≤ c) (hneg : pos = false → d ≤ -κ) (hirr : Irrational (L / M)) :
    ∃ lv hv' : ℝ, Rounds (logBaseQuotWith X B pos w).1 lv ∧
      Rounds (logBaseQuotWith X B pos w).2 hv' ∧
      lv < L / M ∧ L / M < hv' ∧ hv' - lv ≤ divEps (1 / κ) |L| ε δ w := by
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ :=
    logBaseQuotCore_spec hw ha hb' hc hd hcM hMd hcd haL hLb hwid hκ pos hpos hneg
  unfold logBaseQuotWith
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, hwidth⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlo
    exact lt_of_le_of_ne hlo1 fun h => hirr.ne_rat r (h.symm.trans hr)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhi
    exact lt_of_le_of_ne hhi1 fun h => hirr.ne_rat r (h.trans hr)

/-! ### The bracket of `L / ln b` -/

/-- Dividing a bracket of `L` by the clamped bracket of `ln b` encloses `L / ln b` strictly (given
irrationality), with width `divEps (1 / lnKappa b) |L| ε (lnEps eb w) w`. -/
theorem logBaseFloatQuot_spec {w : ℕ} (hw : 64 ≤ w) {X : AzFloat × AzFloat} {a bv L ε : ℝ}
    (ha : X.1.toVal = some (a : EReal)) (hb' : X.2.toVal = some (bv : EReal)) (haL : a ≤ L)
    (hLb : L ≤ bv) (hwid : bv - a ≤ ε) (eb : AzInt) {qb : ℕ} {mb : AzNat}
    (hvb : FiniteValid qb mb) (hb1 : finiteVal true eb mb ≠ 1)
    (hirr : Irrational (L / Real.log (finiteVal true eb mb))) :
    ∃ lv hv' : ℝ, Rounds (logBaseFloatQuot X (finite true eb qb mb hvb) eb w).1 lv ∧
      Rounds (logBaseFloatQuot X (finite true eb qb mb hvb) eb w).2 hv' ∧
      lv < L / Real.log (finiteVal true eb mb) ∧ L / Real.log (finiteVal true eb mb) < hv' ∧
      hv' - lv ≤ divEps (1 / lnKappa (finiteVal true eb mb)) |L| ε (lnEps eb.toInt w) w := by
  obtain ⟨c, d, hc, hd, hcM, hMd, hcd, hκc, hdκ⟩ := lnBaseFloatBracket_spec hw eb hvb hb1
  exact logBaseQuotWith_spec hw ha hb' hc hd hcM hMd hcd haL hLb hwid (lnKappa_pos hb1) _
    (fun hp => hκc (decide_eq_true_iff.mp hp)) (fun hn => hdκ (of_decide_eq_false hn)) hirr

/-! ### The bracket of `ln b` for a rational `b` -/

/-- The lower bound on `|ln b|` used by the clamped rational bracket. -/
noncomputable def lnRatKappa (bv : ℝ) : ℝ := if 1 < bv then (bv - 1) / (6 * bv) else (1 - bv) / 2

theorem lnRatKappa_pos {bv : ℝ} (hb1 : bv ≠ 1) : 0 < lnRatKappa bv := by
  unfold lnRatKappa
  split_ifs with h
  · exact div_pos (by linarith) (by linarith)
  · push Not at h
    exact div_pos (by linarith [lt_of_le_of_ne h hb1]) (by norm_num)

/-- `ln b` is bracketed with the rational width `lnRatEps`, and the end on the side of `ln b` is at
least `lnRatKappa b` in absolute value. -/
theorem lnRatBaseBracket_spec {w : ℕ} (hw : 64 ≤ w) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1) :
    ∃ c d : ℝ, (lnRatBaseBracket b w).1.toVal = some (c : EReal) ∧
      (lnRatBaseBracket b w).2.toVal = some (d : EReal) ∧
      c ≤ Real.log (AzRat.toRat b : ℝ) ∧ Real.log (AzRat.toRat b : ℝ) ≤ d ∧
      d - c
        ≤ lnRatEps (⌊2 * |Real.log (AzRat.toRat b : ℝ)|⌋₊ + 2) |Real.log (AzRat.toRat b : ℝ)| w ∧
      (b.den < b.num → lnRatKappa (AzRat.toRat b : ℝ) ≤ c) ∧
      (¬ b.den < b.num → d ≤ -lnRatKappa (AzRat.toRat b : ℝ)) := by
  have : NeZero w := ⟨by omega⟩
  set bv : ℝ := (AzRat.toRat b : ℝ) with hbv
  have hpos : 0 < bv := by rw [hbv]; exact_mod_cast hb
  have hs := sign_eq_true_of_toRat_pos b hb
  have hlt_iff := one_lt_toRat_iff b hs
  rw [← hbv] at hlt_iff
  have hu : (1 / 2 : ℝ) ^ w ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs b w
  rw [← hbv] at hr1 hr2
  rw [abs_of_pos hpos] at hr2
  obtain ⟨c₀, d₀, hc₀, hd₀, hlo, hhi, hwid⟩ := lnFloorBracket_spec hw hr hpos hr1 hr2
  unfold lnRatBaseBracket
  simp only []
  split_ifs with hge
  · -- `b > 1`
    have hgt : 1 < bv := hlt_iff.mpr hge
    obtain ⟨t, ht, ht1, ht2⟩ := ofAzRatRound_floor_abs (b - 1) w
    rw [AzRat.toRat_sub, AzRat.toRat_one] at ht1 ht2
    push_cast at ht1 ht2
    rw [← hbv] at ht1 ht2
    rw [abs_of_pos (by linarith)] at ht2
    have ht0 : 0 ≤ t := by nlinarith [mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ bv - 1)]
    obtain ⟨bu, hbu, hbu1, hbu2⟩ := ofAzRatRound_ceiling_abs b w
    rw [← hbv] at hbu1 hbu2
    rw [abs_of_pos hpos] at hbu2
    have hbu0 : 0 < bu := by linarith
    obtain ⟨c', hc', hfc⟩ := divFloor_err ht hbu hbu0 ht0 w
    refine ⟨max c₀ c', d₀, toVal_maxOf hc₀ hc', hd₀, ?_, hhi, ?_, ?_, fun h => absurd hge h⟩
    · apply max_le hlo
      calc c' ≤ t / bu := hfc.le
        _ ≤ t / bv := div_le_div_of_nonneg_left ht0 hpos hbu1
        _ ≤ (bv - 1) / bv := div_le_div_of_nonneg_right ht1 hpos.le
        _ = 1 - bv⁻¹ := by field_simp
        _ ≤ Real.log bv := Real.one_sub_inv_le_log_of_pos hpos
    · linarith [le_max_left c₀ c']
    · intro _
      refine le_trans ?_ (le_max_right c₀ c')
      unfold lnRatKappa
      rw [ite_eq_left hgt]
      have ht2' : (bv - 1) / 2 ≤ t := by
        nlinarith [mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ bv - 1)]
      have hbu2' : bu ≤ 3 * bv / 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hu hpos.le]
      have hc2 : t / bu / 2 ≤ c' := by
        have := hfc.ge
        have hx : 0 ≤ t / bu := div_nonneg ht0 hbu0.le
        nlinarith [mul_le_mul_of_nonneg_left hu hx]
      calc (bv - 1) / (6 * bv) = (bv - 1) / 2 / (3 * bv / 2) / 2 := by field_simp; ring
        _ ≤ t / (3 * bv / 2) / 2 := by gcongr
        _ ≤ t / bu / 2 := by gcongr
        _ ≤ c' := hc2
  · -- `b < 1`
    have hlt : bv < 1 := lt_of_le_of_ne (not_lt.mp (mt hlt_iff.mp hge)) hb1
    obtain ⟨t, ht, ht1, ht2⟩ := ofAzRatRound_floor_abs (1 - b) w
    rw [AzRat.toRat_sub, AzRat.toRat_one] at ht1 ht2
    push_cast at ht1 ht2
    rw [← hbv] at ht1 ht2
    rw [abs_of_pos (by linarith)] at ht2
    have hnt : (-(ofAzRatRound (1 - b) w .Floor).1).toVal = some ((-t : ℝ) : EReal) := by
      rw [toVal_neg, ht, Option.map_some, EReal.coe_neg]
    refine ⟨c₀, min d₀ (-t), hc₀, toVal_minOf hd₀ hnt, hlo, ?_, ?_, fun h => absurd h hge, ?_⟩
    · apply le_min hhi
      calc Real.log bv ≤ bv - 1 := Real.log_le_sub_one_of_pos hpos
        _ ≤ -t := by linarith
    · linarith [min_le_left d₀ (-t)]
    · intro _
      refine le_trans (min_le_right d₀ (-t)) ?_
      unfold lnRatKappa
      rw [ite_eq_right (not_lt.mpr hlt.le)]
      have ht2' : (1 - bv) / 2 ≤ t := by
        nlinarith [mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ 1 - bv)]
      linarith

/-! ### The bracket of `log_b x` -/

/-- The width bound of `logBaseFloatApprox` (`K = 1 / lnKappa b`, `A = |ln x|`). -/
noncomputable def logBaseFloatEps (ex eb : ℤ) (K A : ℝ) (w : ℕ) : ℝ :=
  divEps K A (lnEps ex w) (lnEps eb w) w

theorem tendsto_logBaseFloatEps (ex eb : ℤ) (K A : ℝ) :
    Filter.Tendsto (logBaseFloatEps ex eb K A) Filter.atTop (nhds 0) := by
  have hx := tendsto_lnEps ex
  have hb := tendsto_lnEps eb
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (((hx.const_mul 2).add (((hA.add hx).const_mul 8).mul
    ((hb.const_mul (1 + K)).add hu)))).const_mul (1 + K)
  simp only [mul_zero, add_zero] at this
  exact this

/-- The bracket encloses `ln x / ln b` strictly (given irrationality), with the width bound. -/
theorem logBaseFloatApprox_spec {w : ℕ} (hw : 64 ≤ w) (ex : AzInt) {qx : ℕ} {mx : AzNat}
    (hvx : FiniteValid qx mx) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1)
    (hirr : Irrational (Real.log (finiteVal true ex mx) / Real.log (finiteVal true eb mb))) :
    ∃ lv hv' : ℝ,
      Rounds (logBaseFloatApprox (finite true ex qx mx hvx) ex (finite true eb qb mb hvb) eb w).1
        lv ∧
      Rounds (logBaseFloatApprox (finite true ex qx mx hvx) ex (finite true eb qb mb hvb) eb w).2
        hv' ∧
      lv < Real.log (finiteVal true ex mx) / Real.log (finiteVal true eb mb) ∧
      Real.log (finiteVal true ex mx) / Real.log (finiteVal true eb mb) < hv' ∧
      hv' - lv ≤ logBaseFloatEps ex.toInt eb.toInt (1 / lnKappa (finiteVal true eb mb))
        |Real.log (finiteVal true ex mx)| w := by
  obtain ⟨a, bv, ha, hb', haL, hLb, hwid⟩ := lnBracket_spec hw ex hvx
  exact logBaseFloatQuot_spec hw ha hb' haL hLb hwid eb hvb hb1 hirr

/-- The Ziv certificate for `log_b x` with a float base. -/
theorem logBaseFloatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (ex : AzInt)
    {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx) (eb : AzInt) {qb : ℕ} {mb : AzNat}
    (hvb : FiniteValid qb mb) (hb1 : finiteVal true eb mb ≠ 1)
    (hirr : Irrational (Real.log (finiteVal true ex mx) / Real.log (finiteVal true eb mb)))
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (logBaseFloatApprox (finite true ex qx mx hvx) ex (finite true eb qb mb hvb) eb
        (w₀ * 2 ^ f)).1
      (logBaseFloatApprox (finite true ex qx mx hvx) ex (finite true eb qb mb hvb) eb
        (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode
    (logBaseFloatApprox (finite true ex qx mx hvx) ex (finite true eb qb mb hvb) eb) hirr
    (logBaseFloatEps ex.toInt eb.toInt (1 / lnKappa (finiteVal true eb mb))
      |Real.log (finiteVal true ex mx)|)
    (tendsto_logBaseFloatEps _ _ _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ := logBaseFloatApprox_spec hw ex hvx eb hvb hb1 hirr
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The bracket of `log_b (1 + x)` -/

/-- The width bound of `logBaseFloatP1Approx` (`E` bounds the exponent of `ln (1 + x)`,
`K = 1 / lnKappa b`, `A = |ln (1 + x)|`). -/
noncomputable def logBaseFloatP1Eps (E : ℕ) (eb : ℤ) (K A : ℝ) (w : ℕ) : ℝ :=
  divEps K A (lnRatEps E A w) (lnEps eb w) w

theorem tendsto_logBaseFloatP1Eps (E : ℕ) (eb : ℤ) (K A : ℝ) :
    Filter.Tendsto (logBaseFloatP1Eps E eb K A) Filter.atTop (nhds 0) := by
  have hx := tendsto_lnRatEps E A
  have hb := tendsto_lnEps eb
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (((hx.const_mul 2).add (((hA.add hx).const_mul 8).mul
    ((hb.const_mul (1 + K)).add hu)))).const_mul (1 + K)
  simp only [mul_zero, add_zero] at this
  exact this

/-- The bracket encloses `ln (1 + x) / ln b` strictly (given irrationality), with the width
bound. -/
theorem logBaseFloatP1Approx_spec {w : ℕ} (hw : 64 ≤ w) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (eb : AzInt) {qb : ℕ} {mb : AzNat}
    (hvb : FiniteValid qb mb) (hb1 : finiteVal true eb mb ≠ 1)
    (hirr : Irrational (Real.log (1 + xv) / Real.log (finiteVal true eb mb))) :
    ∃ lv hv' : ℝ, Rounds (logBaseFloatP1Approx x (finite true eb qb mb hvb) eb w).1 lv ∧
      Rounds (logBaseFloatP1Approx x (finite true eb qb mb hvb) eb w).2 hv' ∧
      lv < Real.log (1 + xv) / Real.log (finiteVal true eb mb) ∧
      Real.log (1 + xv) / Real.log (finiteVal true eb mb) < hv' ∧
      hv' - lv ≤ logBaseFloatP1Eps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) eb.toInt
        (1 / lnKappa (finiteVal true eb mb)) |Real.log (1 + xv)| w := by
  have : NeZero w := ⟨by omega⟩
  have hpos : 0 < 1 + xv := by linarith
  obtain ⟨r, hr, hf⟩ := addFloor_err toVal_one' hx w hpos.le
  obtain ⟨a, bv, ha, hb', haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hpos hf.le hf.ge
  exact logBaseFloatQuot_spec hw ha hb' haL hLb hwid eb hvb hb1 hirr

/-- The Ziv certificate for `log_b (1 + x)` with a float base. -/
theorem logBaseFloatP1Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (eb : AzInt)
    {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb) (hb1 : finiteVal true eb mb ≠ 1)
    (hirr : Irrational (Real.log (1 + xv) / Real.log (finiteVal true eb mb))) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (logBaseFloatP1Approx x (finite true eb qb mb hvb) eb (w₀ * 2 ^ f)).1
      (logBaseFloatP1Approx x (finite true eb qb mb hvb) eb (w₀ * 2 ^ f)).2 p mode).isSome
        = true :=
  exists_isSome_of_irrational_threshold p mode
    (logBaseFloatP1Approx x (finite true eb qb mb hvb) eb) hirr
    (logBaseFloatP1Eps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) eb.toInt
      (1 / lnKappa (finiteVal true eb mb)) |Real.log (1 + xv)|)
    (tendsto_logBaseFloatP1Eps _ _ _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ :=
        logBaseFloatP1Approx_spec hw hx hx1 eb hvb hb1 hirr
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The bracket of `log_b q` -/

/-- The bracket encloses `ln q / ln b` strictly (given irrationality), with the width bound
`logBaseFloatP1Eps` (the rational `ln` bracket has the same width as the `lnP1` one). -/
theorem logBaseRatFloatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb) (hb1 : finiteVal true eb mb ≠ 1)
    (hirr : Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log (finiteVal true eb mb))) :
    ∃ lv hv' : ℝ, Rounds (logBaseRatFloatApprox q (finite true eb qb mb hvb) eb w).1 lv ∧
      Rounds (logBaseRatFloatApprox q (finite true eb qb mb hvb) eb w).2 hv' ∧
      lv < Real.log (AzRat.toRat q : ℝ) / Real.log (finiteVal true eb mb) ∧
      Real.log (AzRat.toRat q : ℝ) / Real.log (finiteVal true eb mb) < hv' ∧
      hv' - lv ≤ logBaseFloatP1Eps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2) eb.toInt
        (1 / lnKappa (finiteVal true eb mb)) |Real.log (AzRat.toRat q : ℝ)| w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q w
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  rw [abs_of_pos hqv0] at hr2
  obtain ⟨a, bv, ha, hb', haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hqv0 hr1 hr2
  exact logBaseFloatQuot_spec hw ha hb' haL hLb hwid eb hvb hb1 hirr

/-- The Ziv certificate for `log_b q` with a float base. -/
theorem logBaseRatFloatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (hq : (0 : ℚ) < AzRat.toRat q) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1)
    (hirr : Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log (finiteVal true eb mb))) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (logBaseRatFloatApprox q (finite true eb qb mb hvb) eb (w₀ * 2 ^ f)).1
      (logBaseRatFloatApprox q (finite true eb qb mb hvb) eb (w₀ * 2 ^ f)).2 p mode).isSome
        = true :=
  exists_isSome_of_irrational_threshold p mode
    (logBaseRatFloatApprox q (finite true eb qb mb hvb) eb) hirr
    (logBaseFloatP1Eps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2) eb.toInt
      (1 / lnKappa (finiteVal true eb mb)) |Real.log (AzRat.toRat q : ℝ)|)
    (tendsto_logBaseFloatP1Eps _ _ _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ :=
        logBaseRatFloatApprox_spec hw q hq eb hvb hb1 hirr
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The bracket of `log_b x` for a rational base -/

/-- The width bound of `logBaseRatBaseApprox` (`Eb` bounds the exponent of `ln b`,
`K = 1 / lnRatKappa b`, `A = |ln x|`, `Ab = |ln b|`). -/
noncomputable def logBaseRatBaseEps (ex : ℤ) (Eb : ℕ) (K A Ab : ℝ) (w : ℕ) : ℝ :=
  divEps K A (lnEps ex w) (lnRatEps Eb Ab w) w

theorem tendsto_logBaseRatBaseEps (ex : ℤ) (Eb : ℕ) (K A Ab : ℝ) :
    Filter.Tendsto (logBaseRatBaseEps ex Eb K A Ab) Filter.atTop (nhds 0) := by
  have hx := tendsto_lnEps ex
  have hb := tendsto_lnRatEps Eb Ab
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (((hx.const_mul 2).add (((hA.add hx).const_mul 8).mul
    ((hb.const_mul (1 + K)).add hu)))).const_mul (1 + K)
  simp only [mul_zero, add_zero] at this
  exact this

/-- The bracket encloses `ln x / ln b` strictly (given irrationality), with the width bound. -/
theorem logBaseRatBaseApprox_spec {w : ℕ} (hw : 64 ≤ w) (ex : AzInt) {qx : ℕ} {mx : AzNat}
    (hvx : FiniteValid qx mx) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1)
    (hirr : Irrational (Real.log (finiteVal true ex mx) / Real.log (AzRat.toRat b : ℝ))) :
    ∃ lv hv' : ℝ, Rounds (logBaseRatBaseApprox (finite true ex qx mx hvx) ex b w).1 lv ∧
      Rounds (logBaseRatBaseApprox (finite true ex qx mx hvx) ex b w).2 hv' ∧
      lv < Real.log (finiteVal true ex mx) / Real.log (AzRat.toRat b : ℝ) ∧
      Real.log (finiteVal true ex mx) / Real.log (AzRat.toRat b : ℝ) < hv' ∧
      hv' - lv ≤ logBaseRatBaseEps ex.toInt (⌊2 * |Real.log (AzRat.toRat b : ℝ)|⌋₊ + 2)
        (1 / lnRatKappa (AzRat.toRat b : ℝ)) |Real.log (finiteVal true ex mx)|
        |Real.log (AzRat.toRat b : ℝ)| w := by
  obtain ⟨a, bv, ha, hb', haL, hLb, hwid⟩ := lnBracket_spec hw ex hvx
  obtain ⟨c, d, hc, hd, hcM, hMd, hcd, hκc, hdκ⟩ := lnRatBaseBracket_spec hw b hb hb1
  exact logBaseQuotWith_spec hw ha hb' hc hd hcM hMd hcd haL hLb hwid (lnRatKappa_pos hb1) _
    (fun hp => hκc (decide_eq_true_iff.mp hp)) (fun hn => hdκ (of_decide_eq_false hn)) hirr

/-- The Ziv certificate for `log_b x` with a rational base. -/
theorem logBaseRatBaseApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (ex : AzInt)
    {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1)
    (hirr : Irrational (Real.log (finiteVal true ex mx) / Real.log (AzRat.toRat b : ℝ)))
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (logBaseRatBaseApprox (finite true ex qx mx hvx) ex b (w₀ * 2 ^ f)).1
      (logBaseRatBaseApprox (finite true ex qx mx hvx) ex b (w₀ * 2 ^ f)).2 p mode).isSome
        = true :=
  exists_isSome_of_irrational_threshold p mode
    (logBaseRatBaseApprox (finite true ex qx mx hvx) ex b) hirr
    (logBaseRatBaseEps ex.toInt (⌊2 * |Real.log (AzRat.toRat b : ℝ)|⌋₊ + 2)
      (1 / lnRatKappa (AzRat.toRat b : ℝ)) |Real.log (finiteVal true ex mx)|
      |Real.log (AzRat.toRat b : ℝ)|)
    (tendsto_logBaseRatBaseEps _ _ _ _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ :=
        logBaseRatBaseApprox_spec hw ex hvx b hb hb1 hirr
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The bracket of `log_b (1 + x)` for a rational base -/

/-- The width bound of `logBaseRatBaseP1Approx`. -/
noncomputable def logBaseRatBaseP1Eps (E Eb : ℕ) (K A Ab : ℝ) (w : ℕ) : ℝ :=
  divEps K A (lnRatEps E A w) (lnRatEps Eb Ab w) w

theorem tendsto_logBaseRatBaseP1Eps (E Eb : ℕ) (K A Ab : ℝ) :
    Filter.Tendsto (logBaseRatBaseP1Eps E Eb K A Ab) Filter.atTop (nhds 0) := by
  have hx := tendsto_lnRatEps E A
  have hb := tendsto_lnRatEps Eb Ab
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (((hx.const_mul 2).add (((hA.add hx).const_mul 8).mul
    ((hb.const_mul (1 + K)).add hu)))).const_mul (1 + K)
  simp only [mul_zero, add_zero] at this
  exact this

/-- The bracket encloses `ln (1 + x) / ln b` strictly (given irrationality), with the width
bound. -/
theorem logBaseRatBaseP1Approx_spec {w : ℕ} (hw : 64 ≤ w) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1)
    (hirr : Irrational (Real.log (1 + xv) / Real.log (AzRat.toRat b : ℝ))) :
    ∃ lv hv' : ℝ, Rounds (logBaseRatBaseP1Approx x b w).1 lv ∧
      Rounds (logBaseRatBaseP1Approx x b w).2 hv' ∧
      lv < Real.log (1 + xv) / Real.log (AzRat.toRat b : ℝ) ∧
      Real.log (1 + xv) / Real.log (AzRat.toRat b : ℝ) < hv' ∧
      hv' - lv ≤ logBaseRatBaseP1Eps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2)
        (⌊2 * |Real.log (AzRat.toRat b : ℝ)|⌋₊ + 2) (1 / lnRatKappa (AzRat.toRat b : ℝ))
        |Real.log (1 + xv)| |Real.log (AzRat.toRat b : ℝ)| w := by
  have : NeZero w := ⟨by omega⟩
  have hpos : 0 < 1 + xv := by linarith
  obtain ⟨r, hr, hf⟩ := addFloor_err toVal_one' hx w hpos.le
  obtain ⟨a, bv, ha, hb', haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hpos hf.le hf.ge
  obtain ⟨c, d, hc, hd, hcM, hMd, hcd, hκc, hdκ⟩ := lnRatBaseBracket_spec hw b hb hb1
  exact logBaseQuotWith_spec hw ha hb' hc hd hcM hMd hcd haL hLb hwid (lnRatKappa_pos hb1) _
    (fun hp => hκc (decide_eq_true_iff.mp hp)) (fun hn => hdκ (of_decide_eq_false hn)) hirr

/-- The Ziv certificate for `log_b (1 + x)` with a rational base. -/
theorem logBaseRatBaseP1Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (b : AzRat)
    (hb : (0 : ℚ) < AzRat.toRat b) (hb1 : (AzRat.toRat b : ℝ) ≠ 1)
    (hirr : Irrational (Real.log (1 + xv) / Real.log (AzRat.toRat b : ℝ))) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (logBaseRatBaseP1Approx x b (w₀ * 2 ^ f)).1
      (logBaseRatBaseP1Approx x b (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (logBaseRatBaseP1Approx x b) hirr
    (logBaseRatBaseP1Eps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2)
      (⌊2 * |Real.log (AzRat.toRat b : ℝ)|⌋₊ + 2) (1 / lnRatKappa (AzRat.toRat b : ℝ))
      |Real.log (1 + xv)| |Real.log (AzRat.toRat b : ℝ)|)
    (tendsto_logBaseRatBaseP1Eps _ _ _ _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ :=
        logBaseRatBaseP1Approx_spec hw hx hx1 b hb hb1 hirr
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The bracket of `log_b q` for rationals -/

/-- The bracket encloses `ln q / ln b` strictly (given irrationality), with the width bound
`logBaseRatBaseP1Eps` (both `ln` brackets are rational ones). -/
theorem logBaseRatRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b) (hb1 : (AzRat.toRat b : ℝ) ≠ 1)
    (hirr : Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log (AzRat.toRat b : ℝ))) :
    ∃ lv hv' : ℝ, Rounds (logBaseRatRatApprox q b w).1 lv ∧
      Rounds (logBaseRatRatApprox q b w).2 hv' ∧
      lv < Real.log (AzRat.toRat q : ℝ) / Real.log (AzRat.toRat b : ℝ) ∧
      Real.log (AzRat.toRat q : ℝ) / Real.log (AzRat.toRat b : ℝ) < hv' ∧
      hv' - lv ≤ logBaseRatBaseP1Eps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
        (⌊2 * |Real.log (AzRat.toRat b : ℝ)|⌋₊ + 2) (1 / lnRatKappa (AzRat.toRat b : ℝ))
        |Real.log (AzRat.toRat q : ℝ)| |Real.log (AzRat.toRat b : ℝ)| w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q w
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  rw [abs_of_pos hqv0] at hr2
  obtain ⟨a, bv, ha, hb', haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hqv0 hr1 hr2
  obtain ⟨c, d, hc, hd, hcM, hMd, hcd, hκc, hdκ⟩ := lnRatBaseBracket_spec hw b hb hb1
  exact logBaseQuotWith_spec hw ha hb' hc hd hcM hMd hcd haL hLb hwid (lnRatKappa_pos hb1) _
    (fun hp => hκc (decide_eq_true_iff.mp hp)) (fun hn => hdκ (of_decide_eq_false hn)) hirr

/-- The Ziv certificate for `log_b q` with rationals. -/
theorem logBaseRatRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (hq : (0 : ℚ) < AzRat.toRat q) (b : AzRat) (hb : (0 : ℚ) < AzRat.toRat b)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1)
    (hirr : Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log (AzRat.toRat b : ℝ))) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (logBaseRatRatApprox q b (w₀ * 2 ^ f)).1
      (logBaseRatRatApprox q b (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (logBaseRatRatApprox q b) hirr
    (logBaseRatBaseP1Eps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
      (⌊2 * |Real.log (AzRat.toRat b : ℝ)|⌋₊ + 2) (1 / lnRatKappa (AzRat.toRat b : ℝ))
      |Real.log (AzRat.toRat q : ℝ)| |Real.log (AzRat.toRat b : ℝ)|)
    (tendsto_logBaseRatBaseP1Eps _ _ _ _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ := logBaseRatRatApprox_spec hw q hq b hb hb1 hirr
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

end Azurite.AzFloat
