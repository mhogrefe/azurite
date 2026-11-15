/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2WithPeriodBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.Equiv.AtanWithPeriodBracket

/-!
# Equivalence: the bracket of `atan2 (y, x) u / (2π)`

* **`irrational_arg_mul_div_two_pi`**: for rationals `x`, `y ≠ 0` with `|y| ≠ |x|` and `U ≠ 0`,
  `arg (x + iy) U / (2π)` is irrational (Niven's theorem for the tangent: a rational fraction
  of a turn with a rational tangent has denominator `1, 2, 4, 8`, i.e. lies on an axis or a
  diagonal); `irrational_atan2Period_of_toVal`.
* `turnShift_spec`, `atan2PeriodBracket_spec` (width at most `4U 2^(−w)`),
  `atan2PeriodApprox_spec`, `atan2PeriodApprox_isSome_exists` (the Ziv certificate).
-/

open Real

namespace Azurite.AzFloat

/-! ### Irrationality -/

/-- The angle of a rational point off the axes and the diagonals is an irrational fraction of a
turn. -/
theorem irrational_arg_mul_div_two_pi {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : |(y : ℝ)| ≠ |(x : ℝ)|) {U : ℕ} (hU : U ≠ 0) :
    Irrational (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ * U / (2 * π)) := by
  rintro ⟨v, hv⟩
  have hU0 : (0 : ℝ) < U := by exact_mod_cast Nat.pos_of_ne_zero hU
  have hpi := pi_pos
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  set θ := Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ with hθ
  set r : ℚ := v / U with hrdef
  have hr : 2 * π * (r : ℝ) = θ := by
    rw [hrdef, Rat.cast_div, Rat.cast_natCast, hv]
    field_simp
  have htan : tan (2 * π * (r : ℝ)) = (y : ℝ) / x := by rw [hr, hθ, Complex.tan_arg]
  have hq0 : (y : ℝ) / x ≠ 0 := div_ne_zero hy' hx'
  have hq1 : (y : ℝ) / x ≠ 1 := fun h => hxy (by rw [(div_eq_one_iff_eq hx').mp h])
  have hqm : (y : ℝ) / x ≠ -1 := fun h => hxy (by
    rw [(div_eq_iff hx').mp h, neg_one_mul, abs_neg])
  have hlt : |(r : ℝ)| ≤ 1 / 2 := by
    have h1 := Complex.arg_le_pi ⟨(x : ℝ), (y : ℝ)⟩
    have h2 := Complex.neg_pi_lt_arg ⟨(x : ℝ), (y : ℝ)⟩
    rw [← hθ, ← hr] at h1 h2
    rw [abs_le]
    constructor <;> nlinarith
  have hden : r.den = 1 ∨ r.den = 2 ∨ r.den = 4 ∨ r.den = 8 := by
    by_contra h
    push Not at h
    exact (irrational_tan_two_pi_mul_rat h.1 h.2.1 h.2.2.1 h.2.2.2)
      ⟨y / x, by rw [htan]; push_cast; rfl⟩
  have hcast : (r : ℝ) = r.num / r.den := Rat.cast_def r
  have hcop := r.reduced
  have hneg4 : tan (-(π / 4)) = -1 := by rw [tan_neg, tan_pi_div_four]
  rcases hden with h | h | h | h
  · exact hq0 (by rw [← htan, tan_two_pi_mul_rat_of_den_dvd_two (by rw [h]; norm_num)])
  · exact hq0 (by rw [← htan, tan_two_pi_mul_rat_of_den_dvd_two (by rw [h])])
  · rw [h] at hcast hcop
    have hn : |r.num| ≤ 2 := by
      have h1 : |(r.num : ℝ)| ≤ 2 := by
        rw [hcast, abs_div] at hlt
        norm_num at hlt
        linarith
      exact_mod_cast h1
    rw [abs_le] at hn
    generalize r.num = n at hcast hcop hn
    obtain ⟨h1, h2⟩ := hn
    interval_cases n
    · exact absurd hcop (by decide)
    · have hr' : (r : ℝ) = -(1 / 4) := by rw [hcast]; norm_num
      rw [hr', show 2 * π * -(1 / 4) = -(π / 2) by ring, tan_neg, tan_pi_div_two,
        neg_zero] at htan
      exact hq0 htan.symm
    · exact absurd hcop (by decide)
    · have hr' : (r : ℝ) = 1 / 4 := by rw [hcast]; norm_num
      rw [hr', show 2 * π * (1 / 4) = π / 2 by ring, tan_pi_div_two] at htan
      exact hq0 htan.symm
    · exact absurd hcop (by decide)
  · rw [h] at hcast hcop
    have hn : |r.num| ≤ 4 := by
      have h1 : |(r.num : ℝ)| ≤ 4 := by
        rw [hcast, abs_div] at hlt
        norm_num at hlt
        linarith
      exact_mod_cast h1
    rw [abs_le] at hn
    generalize r.num = n at hcast hcop hn
    obtain ⟨h1, h2⟩ := hn
    interval_cases n
    · exact absurd hcop (by decide)
    · have hr' : (r : ℝ) = -(3 / 8) := by rw [hcast]; norm_num
      rw [hr', show 2 * π * -(3 / 8) = π / 4 - π by ring, tan_periodic.sub_eq,
        tan_pi_div_four] at htan
      exact hq1 htan.symm
    · exact absurd hcop (by decide)
    · have hr' : (r : ℝ) = -(1 / 8) := by rw [hcast]; norm_num
      rw [hr', show 2 * π * -(1 / 8) = -(π / 4) by ring, hneg4] at htan
      exact hqm htan.symm
    · exact absurd hcop (by decide)
    · have hr' : (r : ℝ) = 1 / 8 := by rw [hcast]; norm_num
      rw [hr', show 2 * π * (1 / 8) = π / 4 by ring, tan_pi_div_four] at htan
      exact hq1 htan.symm
    · exact absurd hcop (by decide)
    · have hr' : (r : ℝ) = 3 / 8 := by rw [hcast]; norm_num
      rw [hr', show 2 * π * (3 / 8) = -(π / 4) + π by ring, tan_periodic, hneg4] at htan
      exact hqm htan.symm
    · exact absurd hcop (by decide)

/-- `atan2 (y, x) U / (2π)` is irrational for finite nonzero floats with `|y| ≠ |x|`. -/
theorem irrational_atan2Period_of_toVal {y x : AzFloat} {yv xv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0)
    (hx0 : xv ≠ 0) (hxy : |yv| ≠ |xv|) {U : ℕ} (hU : U ≠ 0) :
    Irrational (Complex.arg ⟨xv, yv⟩ * U / (2 * π)) := by
  obtain ⟨qy, hqy⟩ := exists_rat_of_toVal hy
  obtain ⟨qx, hqx⟩ := exists_rat_of_toVal hx
  rw [hqy, hqx] at hxy ⊢
  refine irrational_arg_mul_div_two_pi ?_ ?_ hxy hU
  · rintro rfl
    exact hx0 (by rw [hqx, Rat.cast_zero])
  · rintro rfl
    exact hy0 (by rw [hqy, Rat.cast_zero])

/-! ### The enclosures -/

/-- **`c ± S`**: for a float `c` with `|c| ≤ M` and an enclosure `S` of `σ` with ends of absolute
value at most `2M`, an enclosure of width at most that of `S` plus `12 M 2^(−V)`. -/
theorem turnShift_spec (plus : Bool) {c : AzFloat} {S : Encl} {cv sl sh σ M : ℝ}
    (hc : c.toVal = some (cv : EReal)) (hsl : S.1.toVal = some (sl : EReal))
    (hsh : S.2.toVal = some (sh : EReal)) (h1 : sl ≤ σ) (h2 : σ ≤ sh) (hcM : |cv| ≤ M)
    (hslM : |sl| ≤ 2 * M) (hshM : |sh| ≤ 2 * M) (V : ℕ) [NeZero V] :
    ∃ lo hi : ℝ, (turnShift c plus S V).1.toVal = some (lo : EReal) ∧
      (turnShift c plus S V).2.toVal = some (hi : EReal) ∧
      lo ≤ cv + (if plus then σ else -σ) ∧ cv + (if plus then σ else -σ) ≤ hi ∧
      hi - lo ≤ (sh - sl) + 12 * M * (1 / 2 : ℝ) ^ V := by
  set e := (1 / 2 : ℝ) ^ V with he
  have he0 : 0 ≤ e := by positivity
  unfold turnShift
  cases plus with
  | true =>
    simp only [↓reduceIte]
    obtain ⟨lo, hlo, hlo1, hlo2⟩ := addFloor_abs hc hsl V
    obtain ⟨hi, hhi, hhi1, hhi2⟩ := addCeiling_abs hc hsh V
    rw [← he] at hlo2 hhi2
    have ha1 : |cv + sl| ≤ 3 * M := (abs_add_le _ _).trans (by linarith)
    have ha2 : |cv + sh| ≤ 3 * M := (abs_add_le _ _).trans (by linarith)
    have m1 := mul_le_mul_of_nonneg_right ha1 he0
    have m2 := mul_le_mul_of_nonneg_right ha2 he0
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hc hsh V
    obtain ⟨hi, hhi, hhi1, hhi2⟩ := subCeiling_abs hc hsl V
    rw [← he] at hlo2 hhi2
    have ha1 : |cv - sh| ≤ 3 * M := (abs_sub _ _).trans (by linarith)
    have ha2 : |cv - sl| ≤ 3 * M := (abs_sub _ _).trans (by linarith)
    have m1 := mul_le_mul_of_nonneg_right ha1 he0
    have m2 := mul_le_mul_of_nonneg_right ha2 he0
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩

/-- The scaled enclosure of `arctan (n/d)`, `0 < n ≤ d`, at level `w + 8`: an enclosure of
`arctan (n/d) U / (2π)` with ends of absolute value at most `2U` and width at most
`U 2^(−w)/64`. -/
theorem atanPeriodScale_atanQuot_spec {n d : AzFloat} {nv dv : ℝ}
    (hn : n.toVal = some (nv : EReal)) (hd : d.toVal = some (dv : EReal)) (hn0 : 0 < nv)
    (hnd : nv ≤ dv) (u : AzNat) (w : ℕ) :
    ∃ sl sh : ℝ, (atanPeriodScale (atanQuot n d (w + 8)) u (w + 72)).1.toVal
        = some (sl : EReal) ∧
      (atanPeriodScale (atanQuot n d (w + 8)) u (w + 72)).2.toVal = some (sh : EReal) ∧
      sl ≤ arctan (nv / dv) * u.toNat / (2 * π) ∧ arctan (nv / dv) * u.toNat / (2 * π) ≤ sh ∧
      |sl| ≤ 2 * u.toNat ∧ |sh| ≤ 2 * u.toNat ∧
      sh - sl ≤ u.toNat * ((1 / 2 : ℝ) ^ w / 64) := by
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 2 ^ 20 := by
    have h20 : (1 / 2 : ℝ) ^ (w + 20) = (1 / 2 : ℝ) ^ w / 2 ^ 20 := by
      rw [pow_add]
      norm_num
      ring
    rw [← h20]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h72' : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 72) := by positivity
  obtain ⟨al, ah, hal, hah, hal0, h1, h2, -, hδ⟩ := atanQuot_spec hn hd hn0 hnd (w + 8)
  rw [show w + 8 + 64 = w + 72 by ring, h8] at hδ
  have hA : IsEncl0W (atanQuot n d (w + 8)) (arctan (nv / dv)) ((1 / 2 : ℝ) ^ w / 256) :=
    ⟨al, ah, hal, hah, hal0, h1, h2, by linarith⟩
  have hd0 : 0 < dv := lt_of_lt_of_le hn0 hnd
  have hθ0 : 0 ≤ arctan (nv / dv) := arctan_nonneg.mpr (div_pos hn0 hd0).le
  have hθ : arctan (nv / dv) ≤ 2 := by
    have := arctan_lt_pi_div_two (nv / dv)
    linarith [pi_lt_four]
  obtain ⟨sl, sh, hsl, hsh, hs1, hs2, hsw⟩ :=
    atanPeriodScale_spec hA hθ (by linarith) u (V := w + 72) (by omega)
  set U := (u.toNat : ℝ) with hU
  have hU0 : 0 ≤ U := by positivity
  have hπ := pi_gt_three
  have hval0 : 0 ≤ arctan (nv / dv) * U / (2 * π) := by positivity
  have hval1 : arctan (nv / dv) * U / (2 * π) ≤ U := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hwb : U * (2 * ((1 / 2 : ℝ) ^ w / 256) + 108 * (1 / 2 : ℝ) ^ (w + 72))
      ≤ U * ((1 / 2 : ℝ) ^ w / 64) := by
    apply mul_le_mul_of_nonneg_left _ hU0
    linarith
  have hwb1 : U * ((1 / 2 : ℝ) ^ w / 64) ≤ U := by
    have := mul_le_mul_of_nonneg_left (by linarith : (1 / 2 : ℝ) ^ w / 64 ≤ 1) hU0
    linarith
  refine ⟨sl, sh, hsl, hsh, hs1, hs2, ?_, ?_, by linarith⟩
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-- **The bracket of `atan2 (|y|, x) u / (2π)`**: width at most `4U 2^(−w)`. -/
theorem atan2PeriodBracket_spec {y x : AzFloat} {yv xv : ℝ} (hy : y.toVal = some (yv : EReal))
    (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0) (hx0 : xv ≠ 0) {ey ex : AzInt}
    (hey : |yv| < (2 : ℝ) ^ ey.toInt) (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|) (xpos : Bool)
    (u : AzNat) (w : ℕ) :
    ∃ lo hi : ℝ, (atan2PeriodBracket y x ey ex xpos u w).1.toVal = some (lo : EReal) ∧
      (atan2PeriodBracket y x ey ex xpos u w).2.toVal = some (hi : EReal) ∧
      lo ≤ atan2Abs |yv| |xv| xpos * u.toNat / (2 * π) ∧
      atan2Abs |yv| |xv| xpos * u.toNat / (2 * π) ≤ hi ∧
      hi - lo ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  set a := |yv| with ha
  set b := |xv| with hb
  have ha0 : 0 < a := abs_pos.mpr hy0
  have hb0 : 0 < b := abs_pos.mpr hx0
  have hya : y.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hy, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hxa : x.abs.toVal = some ((b : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have : NeZero (w + 72) := ⟨by omega⟩
  set U := (u.toNat : ℝ) with hU
  have hU0 : 0 ≤ U := by positivity
  have hpi := pi_pos
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
    have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
      rw [pow_add]
      norm_num
      ring
    rw [← h10]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h72' : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 72) := by positivity
  have hUw : (0 : ℝ) ≤ U * (1 / 2 : ℝ) ^ w := mul_nonneg hU0 hw0
  have hU72 : U * (1 / 2 : ℝ) ^ (w + 72) ≤ U * ((1 / 2 : ℝ) ^ w / 1024) :=
    mul_le_mul_of_nonneg_left h72 hU0
  have hhalf : (ofAzNat u <<< AzInt.ofInt (-1)).toVal = some ((U / 2 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal (toVal_ofAzNat u) (AzInt.ofInt (-1))
    rw [h, AzInt.toInt_ofInt, zpow_neg_one, div_eq_mul_inv]
  have hquart : (ofAzNat u <<< AzInt.ofInt (-2)).toVal = some ((U / 4 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal (toVal_ofAzNat u) (AzInt.ofInt (-2))
    rw [h, AzInt.toInt_ofInt, show ((2 : ℝ) ^ (-2 : ℤ)) = 1 / 4 by norm_num, mul_one_div]
  have hcM2 : |U / 2| ≤ U := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hcM4 : |U / 4| ≤ U := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  unfold atan2PeriodBracket
  dsimp only
  by_cases hc : y.abs.le x.abs = true
  · simp only [hc, ↓reduceIte]
    have hab : a ≤ b := (le_eq_true_iff hya hxa).mp hc
    cases xpos with
    | true =>
      simp only [↓reduceIte, atan2Abs]
      have hlt := div_lt_two_zpow_exp hb0 hey hex1
      obtain ⟨al, ah, hal, hah, hal0, h1, h2, h3⟩ := atanQuotRel_spec hya hxa ha0 hab hlt w
      have hA : IsEncl0W (atanQuotRel y.abs x.abs (ey - ex + AzInt.ofInt 1) w)
          (arctan (a / b)) ((1 / 2 : ℝ) ^ w) := ⟨al, ah, hal, hah, hal0, h1, h2, h3⟩
      have hθ : arctan (a / b) ≤ 2 := by
        have := arctan_lt_pi_div_two (a / b)
        linarith [pi_lt_four]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        atanPeriodScale_spec hA hθ hw1 u (V := w + 72) (by omega)
      rw [← hU] at hl hh hwd
      refine ⟨lo, hi, hlo, hhi, hl, hh, hwd.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ hU0
      linarith
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, atan2Abs]
      obtain ⟨sl, sh, hsl, hsh, hs1, hs2, hslM, hshM, hsw⟩ :=
        atanPeriodScale_atanQuot_spec hya hxa ha0 hab u w
      rw [← hU] at hs1 hs2 hslM hshM hsw
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        turnShift_spec false hhalf hsl hsh hs1 hs2 hcM2 hslM hshM (w + 72)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      have hval : (π - arctan (a / b)) * U / (2 * π)
          = U / 2 + -(arctan (a / b) * U / (2 * π)) := by
        field_simp
        ring
      rw [hval]
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩
  · simp only [hc]
    have hab : b < a := not_le.mp fun h => hc ((le_eq_true_iff hya hxa).mpr h)
    obtain ⟨sl, sh, hsl, hsh, hs1, hs2, hslM, hshM, hsw⟩ :=
      atanPeriodScale_atanQuot_spec hxa hya hb0 hab.le u w
    rw [← hU] at hs1 hs2 hslM hshM hsw
    have hinv : arctan (a / b) = π / 2 - arctan (b / a) := by
      rw [← arctan_inv_of_pos (div_pos hb0 ha0), inv_div]
    cases xpos with
    | true =>
      simp only [Bool.not_true, ↓reduceIte, atan2Abs]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        turnShift_spec false hquart hsl hsh hs1 hs2 hcM4 hslM hshM (w + 72)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      have hval : arctan (a / b) * U / (2 * π)
          = U / 4 + -(arctan (b / a) * U / (2 * π)) := by
        rw [hinv]
        field_simp
        ring
      rw [hval]
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, atan2Abs]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ :=
        turnShift_spec true hquart hsl hsh hs1 hs2 hcM4 hslM hshM (w + 72)
      simp only [↓reduceIte] at hl hh
      have hval : (π - arctan (a / b)) * U / (2 * π)
          = U / 4 + arctan (b / a) * U / (2 * π) := by
        rw [hinv]
        field_simp
        ring
      rw [hval]
      exact ⟨lo, hi, hlo, hhi, hl, hh, by nlinarith⟩

/-- `atan2PeriodApprox neg` as a pair of `Roundable`s bracketing `± atan2 (|y|, x) u / (2π)`. -/
theorem atan2PeriodApprox_spec (neg : Bool) {y x : AzFloat} {yv xv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0)
    (hx0 : xv ≠ 0) {ey ex : AzInt} (hey : |yv| < (2 : ℝ) ^ ey.toInt)
    (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|) (xpos : Bool) (u : AzNat) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (atan2PeriodApprox neg y x ey ex xpos u w).1 lv ∧
      Rounds (atan2PeriodApprox neg y x ey ex xpos u w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * (atan2Abs |yv| |xv| xpos * u.toNat / (2 * π)) ∧
      (if neg then -1 else 1) * (atan2Abs |yv| |xv| xpos * u.toNat / (2 * π)) ≤ hv ∧
      hv - lv ≤ u.toNat * (4 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    atan2PeriodBracket_spec hy hx hy0 hx0 hey hex1 xpos u w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `arg (x + iy) U / (2π) = ± atan2Abs |y| |x| U / (2π)` with the sign of `y`. -/
theorem arg_period_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) {neg xpos : Bool}
    (hneg : neg = true ↔ y < 0) (hxpos : xpos = true ↔ 0 < x) (U : ℝ) :
    Complex.arg ⟨x, y⟩ * U / (2 * π)
      = (if neg then -1 else 1) * (atan2Abs |y| |x| xpos * U / (2 * π)) := by
  rw [arg_eq_atan2Abs hx hy hneg hxpos]
  ring

/-- `atan2 (|y|, x) U / (2π)` is irrational for finite nonzero floats with `|y| ≠ |x|`. -/
theorem irrational_atan2AbsPeriod_of_toVal {y x : AzFloat} {yv xv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0)
    (hx0 : xv ≠ 0) (hxy : |yv| ≠ |xv|) {xpos : Bool} (hxpos : xpos = true ↔ 0 < xv) {U : ℕ}
    (hU : U ≠ 0) : Irrational (atan2Abs |yv| |xv| xpos * U / (2 * π)) := by
  obtain ⟨qy, hqy⟩ := exists_rat_of_toVal hy
  obtain ⟨qx, hqx⟩ := exists_rat_of_toVal hx
  have hpos : 0 < |yv| := abs_pos.mpr hy0
  have h := arg_period_eq (x := xv) (y := |yv|) hx0 hpos.ne' (neg := false)
    (by simp [abs_nonneg]) hxpos (U : ℝ)
  rw [abs_abs] at h
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  rw [← h, hqy, hqx, ← Rat.cast_abs]
  refine irrational_arg_mul_div_two_pi ?_ ?_ ?_ hU
  · rintro rfl
    exact hx0 (by rw [hqx, Rat.cast_zero])
  · intro h0
    exact hy0 (by rw [hqy, abs_eq_zero.mp h0, Rat.cast_zero])
  · rw [Rat.cast_abs, abs_abs, ← hqy, ← hqx]
    exact hxy

/-- The Ziv certificate for `± atan2 (|y|, x) u / (2π)`: `y`, `x` finite and nonzero,
`|y| ≠ |x|`, `u ≠ 0`. -/
theorem atan2PeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {y x : AzFloat} {yv xv : ℝ} (hy : y.toVal = some (yv : EReal))
    (hx : x.toVal = some (xv : EReal)) (hy0 : yv ≠ 0) (hx0 : xv ≠ 0) (hxy : |yv| ≠ |xv|)
    {xpos : Bool} (hxpos : xpos = true ↔ 0 < xv) {ey ex : AzInt}
    (hey : |yv| < (2 : ℝ) ^ ey.toInt) (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|) {u : AzNat}
    (hu : u.toNat ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (atan2PeriodApprox neg y x ey ex xpos u (w₀ * 2 ^ f)).1
      (atan2PeriodApprox neg y x ey ex xpos u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  refine exists_isSome_of_irrational_threshold p mode (atan2PeriodApprox neg y x ey ex xpos u)
    (v := (if neg then -1 else 1) * (atan2Abs |yv| |xv| xpos * u.toNat / (2 * π))) ?_
    (fun w => u.toNat * (4 * (1 / 2 : ℝ) ^ w)) ?_ 0
    (fun w _ => atan2PeriodApprox_spec neg hy hx hy0 hx0 hey hex1 xpos u w) w₀ hw₀
  · have hirr := irrational_atan2AbsPeriod_of_toVal hy hx hy0 hx0 hxy hxpos hu
    cases neg with
    | false => simpa using hirr
    | true => simpa using hirr.neg
  · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 4).const_mul (u.toNat : ℝ)
    simpa using h

end Azurite.AzFloat
