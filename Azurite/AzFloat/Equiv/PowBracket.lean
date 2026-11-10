/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBracket
import Azurite.AzFloat.Equiv.PowBaseBracket
import Azurite.AzFloat.Equiv.PowInt
import Azurite.AzFloat.Equiv.RoundToInteger
import Azurite.AzInt.Equiv.DivMod
import Azurite.AzInt.Equiv.TrailingZeros
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.SqrtRem
import Azurite.AzNat.Equiv.TrailingZeros
import Azurite.AzNat.Equiv.TwoAdicPow
import Mathlib.NumberTheory.Multiplicity

/-!
# Equivalence: the bracket of `x^y` and the exact dyadic powers

* `lnMulBracket_spec`: `lnMulBracket b eb y ey w` encloses `y ln b` with width at most
  `mulLnEps ey eb w` (the bound of the natural-base power: `|y| < 2^ey` cancels against the
  `max(ey, 0)` extra bits of `W`, and `|ln b| ≤ |eb| + 1`).
* `powBracket_spec`, `powApprox_spec` (`b^y = exp (y ln b)`, through `expOfBracket_spec_width`),
  `powApprox_isSome_exists`: the Ziv certificate for a result that is not a rounding boundary
  (`exists_isSome_of_not_mem_threshold`).
* Non-boundaries: `not_mem_floatSet_of_odd_mul` (a dyadic `±a 2^k` with an odd `a ≥ 2^(p+1)`),
  `not_mem_floatSet_of_div_odd` (`±2^k/a`, `a ≥ 3` odd), `not_mem_floatSet_of_not_cheap`.
* Exact powers: `powExact?_some` (`x^y = z^N`) and `irrational_of_powExact?_none`, from
  `irrational_natCast_rpow_div_of_not_pow` (`M^(N/D)` is irrational for `M` not a `D`-th power
  and `gcd(N, D) = 1`, by `irrational_nrt_of_notint_nrt` and
  `Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow`).
-/

namespace Azurite.AzFloat

/-! ### Directed products of any sign -/

variable {u v : AzFloat} {uv vv : ℝ}

theorem mulFloor_abs (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (mulPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv * vv ∧
      uv * vv ≤ r + 2 * |uv * vv| * (1 / 2 : ℝ) ^ w := by
  rw [mulPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.mul_coe_coe]
  exact roundVal_floor_abs w _

theorem mulCeiling_abs (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (mulPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv * vv ≤ r ∧
      r ≤ uv * vv + 2 * |uv * vv| * (1 / 2 : ℝ) ^ w := by
  rw [mulPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.mul_coe_coe]
  exact roundVal_ceiling_abs w _

/-! ### The bracket of `y ln b` -/

/-- `|ln b| ≤ |eb| + 1` for a positive float of exponent `eb`. -/
theorem abs_log_finiteVal_le (eb : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    |Real.log (finiteVal true eb m)| ≤ |(eb.toInt : ℝ)| + 1 := by
  obtain ⟨h1, h2⟩ := abs_finiteVal_bounds true eb hv
  have hpos := finiteVal_true_pos eb hv
  rw [abs_of_pos hpos] at h1 h2
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hlo : ((eb.toInt - 1 : ℤ) : ℝ) * Real.log 2 ≤ Real.log (finiteVal true eb m) := by
    rw [← Real.log_zpow]; exact Real.log_le_log (by positivity) h1
  have hhi : Real.log (finiteVal true eb m) < (eb.toInt : ℝ) * Real.log 2 := by
    rw [← Real.log_zpow]; exact Real.log_lt_log hpos h2
  push_cast at hlo
  have ha := le_abs_self (eb.toInt : ℝ)
  have hb := neg_abs_le (eb.toInt : ℝ)
  have h0 := abs_nonneg (eb.toInt : ℝ)
  rw [abs_le]
  constructor <;> nlinarith

/-- `lnMulBracket b eb y ey w` encloses `y ln b` with width at most `mulLnEps ey eb w`
(`|y| < 2^ey`, `w ≥ 64`). -/
theorem lnMulBracket_spec (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    {y : AzFloat} {yv : ℝ} (hy : y.toVal = some (yv : EReal)) (ey : AzInt)
    (hye : |yv| < (2 : ℝ) ^ ey.toInt) (w : ℕ) (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (lnMulBracket (finite true eb qb mb hvb) eb y ey w).1.toVal = some (lo : EReal) ∧
      (lnMulBracket (finite true eb qb mb hvb) eb y ey w).2.toVal = some (hi : EReal) ∧
      lo ≤ yv * Real.log (finiteVal true eb mb) ∧ yv * Real.log (finiteVal true eb mb) ≤ hi ∧
      hi - lo ≤ mulLnEps ey.toInt eb.toInt w := by
  -- the working precision and the scale (as in `lnBaseMulBracket_spec`)
  obtain ⟨emax, hemax⟩ : ∃ n : ℕ, n = if ey.sign then ey.abs.toNat else 0 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = expWork ey w := ⟨_, rfl⟩
  have hWv : W = w + 16 + emax := by rw [hW, hemax]; rfl
  have hemaxM : (emax : ℤ) = max ey.toInt 0 := by rw [hemax]; exact expPos_eq_max ey
  have hemaxZ : ey.toInt ≤ (emax : ℤ) := by rw [hemaxM]; exact le_max_left _ _
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ emax := ⟨_, rfl⟩
  have hyE : |yv| < E := by
    calc |yv| < (2 : ℝ) ^ ey.toInt := hye
      _ ≤ (2 : ℝ) ^ (emax : ℤ) := zpow_le_zpow_right₀ (by norm_num) hemaxZ
      _ = E := by rw [hE, zpow_natCast]
  obtain ⟨uu, huu⟩ : ∃ uu : ℝ, uu = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have huu0 : 0 < uu := by rw [huu]; positivity
  have huu1 : uu ≤ 1 := by rw [huu]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have : NeZero W := ⟨by omega⟩
  have hδ : (1 / 2 : ℝ) ^ W = uu * (1 / 65536) * (1 / 2 : ℝ) ^ emax := by
    rw [hWv, pow_add, pow_add, huu, show ((1 : ℝ) / 2) ^ 16 = 1 / 65536 by norm_num]
  have hEu : E * (1 / 2 : ℝ) ^ emax = 1 := by
    rw [hE, one_div_pow, mul_one_div, div_self (by positivity)]
  have hhalf0 : 0 ≤ (1 / 2 : ℝ) ^ emax := by positivity
  have hya0 : 0 ≤ |yv| := abs_nonneg _
  have hX : |yv| * (1 / 2 : ℝ) ^ W ≤ uu / 65536 := by
    rw [hδ]
    have : |yv| * (1 / 2 : ℝ) ^ emax ≤ E * (1 / 2 : ℝ) ^ emax :=
      mul_le_mul_of_nonneg_right hyE.le hhalf0
    rw [hEu] at this
    calc |yv| * (uu * (1 / 65536) * (1 / 2 : ℝ) ^ emax)
        = uu / 65536 * (|yv| * (1 / 2 : ℝ) ^ emax) := by ring
      _ ≤ uu / 65536 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = uu / 65536 := mul_one _
  have hδ0 : 0 ≤ (1 / 2 : ℝ) ^ W := by positivity
  -- the bracket of `ln b`
  obtain ⟨c, d, hc, hd, hcL, hLd, hcd⟩ := lnBracket_spec (by omega : 64 ≤ W) eb hvb
  set L := Real.log (finiteVal true eb mb) with hLdef
  have hlogb := abs_log_finiteVal_le eb hvb
  rw [← hLdef] at hlogb
  have hlnE0 : 0 ≤ lnEps eb.toInt W := by unfold lnEps; positivity
  have hcabs : |c| ≤ |L| + lnEps eb.toInt W := by
    rw [abs_le]; constructor <;> linarith [le_abs_self L, neg_abs_le L]
  have hdabs : |d| ≤ |L| + lnEps eb.toInt W := by
    rw [abs_le]; constructor <;> linarith [le_abs_self L, neg_abs_le L]
  -- the key identity and the comparison of the two `lnEps`
  obtain ⟨Lw, hLw⟩ : ∃ Lw : ℝ, Lw = lnEps (|eb.toInt| + 16 + max ey.toInt 0) w := ⟨_, rfl⟩
  have hpoly : ((W : ℕ) : ℝ) + |(eb.toInt : ℝ)| + 8
      = (w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8 := by
    rw [← hemaxM, hWv]
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |(eb.toInt : ℝ)| + 16 + emax)]
    ring
  have hkey : |yv| * lnEps eb.toInt W ≤ Lw / 65536 := by
    rw [hLw]
    unfold lnEps
    rw [hpoly]
    have hP0 : 0 ≤ (2 : ℝ) ^ 40
        * ((w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5 := by positivity
    rw [← huu]
    calc |yv| * (2 ^ 40 * ((w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * (1 / 2 : ℝ) ^ W)
        = 2 ^ 40 * ((w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * (|yv| * (1 / 2 : ℝ) ^ W) := by ring
      _ ≤ 2 ^ 40 * ((w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * (uu / 65536) := mul_le_mul_of_nonneg_left hX hP0
      _ = _ := by ring
  have h8 : lnEps eb.toInt W ≤ Lw := by
    rw [hLw]
    unfold lnEps
    rw [hpoly]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hLw0 : 0 ≤ Lw := by rw [hLw]; unfold lnEps; positivity
  -- `(|eb| + 1) uu ≤ Lw`
  have hEb : (|(eb.toInt : ℝ)| + 1) * uu ≤ Lw := by
    rw [hLw]
    unfold lnEps
    rw [← huu]
    have hbase : |(eb.toInt : ℝ)| + 1
        ≤ (w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8 := by
      have hX : (|eb.toInt| : ℤ) + 1 ≤ |eb.toInt| + 16 + max ey.toInt 0 := by
        have := le_max_right ey.toInt 0; omega
      have hX' : ((|eb.toInt| + 1 : ℤ) : ℝ) ≤ ((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ) := by
        exact_mod_cast hX
      have hXabs := le_abs_self ((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)
      have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
      have hc : ((|eb.toInt| + 1 : ℤ) : ℝ) = |(eb.toInt : ℝ)| + 1 := by push_cast; ring
      linarith
    have hb1 : (1 : ℝ) ≤ (w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8 := by
      linarith [abs_nonneg (eb.toInt : ℝ)]
    have hpow5 : (w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8
        ≤ ((w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5 :=
      le_self_pow₀ hb1 (by norm_num)
    have h240 : (1 : ℝ) ≤ 2 ^ 40 := by norm_num
    have hu0 := huu0.le
    calc (|(eb.toInt : ℝ)| + 1) * uu
        ≤ ((w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5 * uu :=
          mul_le_mul_of_nonneg_right (hbase.trans hpow5) hu0
      _ ≤ 2 ^ 40 * ((w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5 * uu := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h240 (by positivity :
              (0 : ℝ) ≤ ((w : ℝ) + |((|eb.toInt| + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5)) hu0
          rwa [one_mul] at this
  -- the width from the two directed products, whatever the signs
  have hwidth : ∀ P₁ P₂ r₁ r₂ : ℝ, r₁ ≤ P₁ → P₁ ≤ r₁ + 2 * |P₁| * (1 / 2 : ℝ) ^ W → P₂ ≤ r₂ →
      r₂ ≤ P₂ + 2 * |P₂| * (1 / 2 : ℝ) ^ W → |P₁| ≤ |yv| * (|L| + lnEps eb.toInt W) →
      |P₂| ≤ |yv| * (|L| + lnEps eb.toInt W) → P₂ - P₁ ≤ |yv| * (d - c) →
      r₂ - r₁ ≤ mulLnEps ey.toInt eb.toInt w := by
    intro P₁ P₂ r₁ r₂ h1 h2 h3 h4 h5 h6 h7
    have hA : |yv| * (d - c) ≤ Lw / 65536 :=
      (mul_le_mul_of_nonneg_left hcd hya0).trans hkey
    have hB : 2 * |P₁| * (1 / 2 : ℝ) ^ W + 2 * |P₂| * (1 / 2 : ℝ) ^ W
        ≤ 4 * (|yv| * (|L| + lnEps eb.toInt W)) * (1 / 2 : ℝ) ^ W := by
      have := add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5
        (by norm_num : (0 : ℝ) ≤ 2)) hδ0) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 2)) hδ0)
      linarith
    have hC : |yv| * (|L| + lnEps eb.toInt W) * (1 / 2 : ℝ) ^ W
        ≤ (|(eb.toInt : ℝ)| + 1) * (uu / 65536) + Lw * (uu / 65536) := by
      have e1 : |yv| * (|L| + lnEps eb.toInt W) * (1 / 2 : ℝ) ^ W
          = (|L| + lnEps eb.toInt W) * (|yv| * (1 / 2 : ℝ) ^ W) := by ring
      rw [e1]
      have hLsum : |L| + lnEps eb.toInt W ≤ (|(eb.toInt : ℝ)| + 1) + Lw := by linarith
      have h0 : 0 ≤ |L| + lnEps eb.toInt W := by positivity
      calc (|L| + lnEps eb.toInt W) * (|yv| * (1 / 2 : ℝ) ^ W)
          ≤ (|L| + lnEps eb.toInt W) * (uu / 65536) := mul_le_mul_of_nonneg_left hX h0
        _ ≤ ((|(eb.toInt : ℝ)| + 1) + Lw) * (uu / 65536) :=
            mul_le_mul_of_nonneg_right hLsum (by positivity)
        _ = _ := by ring
    have hD : (|(eb.toInt : ℝ)| + 1) * (uu / 65536) ≤ Lw / 65536 := by
      have := hEb
      linarith
    have hE' : Lw * (uu / 65536) ≤ Lw / 65536 := by
      have := mul_le_mul_of_nonneg_left huu1 hLw0
      linarith
    unfold mulLnEps
    rw [← hLw, ← huu]
    nlinarith
  -- the sign of `y`
  simp only [lnMulBracket, mulBracketAny]
  rw [← hW]
  split_ifs with hneg
  · have hyneg : yv < 0 := (toVal_sign_of_isNegative hy).1 hneg
    have hay : |yv| = -yv := abs_of_neg hyneg
    obtain ⟨r₁, hr₁, hr₁a, hr₁b⟩ := mulFloor_abs hy hd W
    obtain ⟨r₂, hr₂, hr₂a, hr₂b⟩ := mulCeiling_abs hy hc W
    refine ⟨r₁, r₂, hr₁, hr₂, ?_, ?_, ?_⟩
    · exact hr₁a.trans (mul_le_mul_of_nonpos_left hLd hyneg.le)
    · exact (mul_le_mul_of_nonpos_left hcL hyneg.le).trans hr₂a
    · refine hwidth (yv * d) (yv * c) r₁ r₂ hr₁a hr₁b hr₂a hr₂b ?_ ?_ ?_
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdabs hya0
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hcabs hya0
      · rw [hay]; linarith
  · have hynn : 0 ≤ yv := (toVal_sign_of_isNegative hy).2 (by simpa using hneg)
    have hay : |yv| = yv := abs_of_nonneg hynn
    obtain ⟨r₁, hr₁, hr₁a, hr₁b⟩ := mulFloor_abs hy hc W
    obtain ⟨r₂, hr₂, hr₂a, hr₂b⟩ := mulCeiling_abs hy hd W
    refine ⟨r₁, r₂, hr₁, hr₂, ?_, ?_, ?_⟩
    · exact hr₁a.trans (mul_le_mul_of_nonneg_left hcL hynn)
    · exact (mul_le_mul_of_nonneg_left hLd hynn).trans hr₂a
    · refine hwidth (yv * c) (yv * d) r₁ r₂ hr₁a hr₁b hr₂a hr₂b ?_ ?_ ?_
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hcabs hya0
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdabs hya0
      · rw [hay]; linarith

/-- `powW₀ ey eb` as an integer. -/
theorem powW₀_eq (ey eb : AzInt) :
    ((powW₀ ey eb : ℕ) : ℤ) = 88 + max ey.toInt 0 + |eb.toInt| := by
  unfold powW₀
  rw [Nat.cast_add, Nat.cast_add, expPos_eq_max, AzInt.abs_toNat_eq]
  norm_num

/-- `b^y = exp (y ln b)` for `b > 0`. -/
theorem rpow_eq_exp_mul_log {b : ℝ} (hb : 0 < b) (yv : ℝ) :
    b ^ yv = Real.exp (yv * Real.log b) := by
  rw [Real.rpow_def_of_pos hb, mul_comm]

/-- `powBracket b eb y ey w` encloses `b^y` for `w ≥ powW₀ ey eb`, with width at most
`powBaseEps ey eb (y ln b) w`. -/
theorem powBracket_spec (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    {y : AzFloat} {yv : ℝ} (hy : y.toVal = some (yv : EReal)) (ey : AzInt)
    (hye : |yv| < (2 : ℝ) ^ ey.toInt) {w : ℕ} (hw : powW₀ ey eb ≤ w) :
    ∃ lo hi : ℝ, (powBracket (finite true eb qb mb hvb) eb y ey w).1.toVal = some (lo : EReal) ∧
      (powBracket (finite true eb qb mb hvb) eb y ey w).2.toVal = some (hi : EReal) ∧
      lo ≤ finiteVal true eb mb ^ yv ∧ finiteVal true eb mb ^ yv ≤ hi ∧
      hi - lo ≤ powBaseEps ey.toInt eb.toInt (yv * Real.log (finiteVal true eb mb)) w := by
  have hw64 : 64 ≤ w := by unfold powW₀ at hw; omega
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnMulBracket_spec eb hvb hy ey hye w hw64
  have hwZ : 88 + max ey.toInt 0 + |eb.toInt| ≤ (w : ℤ) := by
    rw [← powW₀_eq]; exact_mod_cast hw
  have hw1 : hi - lo ≤ 1 := hwid.trans (mulLnEps_le_one _ _ _ hwZ)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw64
  rw [rpow_eq_exp_mul_log (finiteVal_true_pos eb hvb)]
  refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
  unfold powBaseEps
  refine hab.trans ?_
  unfold expOfBracketEps
  have := Real.exp_pos (yv * Real.log (finiteVal true eb mb))
  nlinarith

/-- The sign factor of the result. -/
def powSign (neg : Bool) : ℝ := if neg then -1 else 1

theorem abs_powSign (neg : Bool) : |powSign neg| = 1 := by
  unfold powSign; split_ifs <;> simp

theorem powSign_ne_zero (neg : Bool) : powSign neg ≠ 0 := by
  unfold powSign; split_ifs <;> norm_num

/-- `powApprox neg b eb y ey w` brackets `± b^y`. -/
theorem powApprox_spec (neg : Bool) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    {y : AzFloat} {yv : ℝ} (hy : y.toVal = some (yv : EReal)) (ey : AzInt)
    (hye : |yv| < (2 : ℝ) ^ ey.toInt) {w : ℕ} (hw : powW₀ ey eb ≤ w) :
    ∃ lv hv : ℝ, Rounds (powApprox neg (finite true eb qb mb hvb) eb y ey w).1 lv ∧
      Rounds (powApprox neg (finite true eb qb mb hvb) eb y ey w).2 hv ∧
      lv ≤ powSign neg * finiteVal true eb mb ^ yv ∧
      powSign neg * finiteVal true eb mb ^ yv ≤ hv ∧
      hv - lv ≤ powBaseEps ey.toInt eb.toInt (yv * Real.log (finiteVal true eb mb)) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := powBracket_spec eb hvb hy ey hye hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [powApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, powSign, one_mul]
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | true =>
    simp only [↓reduceIte, powSign, neg_one_mul]
    have hnlo : (-(powBracket (finite true eb qb mb hvb) eb y ey w).2).toVal
        = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(powBracket (finite true eb qb mb hvb) eb y ey w).1).toVal
        = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- The Ziv certificate for `± b^y`, for a result that is not a rounding boundary. -/
theorem powApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb) {y : AzFloat} {yv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (ey : AzInt) (hye : |yv| < (2 : ℝ) ^ ey.toInt)
    (hvB : ((powSign neg * finiteVal true eb mb ^ yv : ℝ) : EReal) ∉ floatSet (p + 1))
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (powApprox neg (finite true eb qb mb hvb) eb y ey (w₀ * 2 ^ f)).1
      (powApprox neg (finite true eb qb mb hvb) eb y ey (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_not_mem_threshold p mode (powApprox neg (finite true eb qb mb hvb) eb y ey)
    (mul_ne_zero (powSign_ne_zero neg) (Real.rpow_pos_of_pos (finiteVal_true_pos eb hvb) yv).ne')
    hvB (powBaseEps ey.toInt eb.toInt (yv * Real.log (finiteVal true eb mb)))
    (tendsto_powBaseEps _ _ _) (powW₀ ey eb)
    (fun _ hw => powApprox_spec neg eb hvb hy ey hye hw) w₀ hw₀

/-! ### Dyadics that are not rounding boundaries -/

/-- Odd parts are unique: `a 2^i = b 2^j` with `a`, `b` odd gives `a = b` and `i = j`. -/
theorem odd_mul_two_pow_inj {a b i j : ℕ} (ha : Odd a) (hb : Odd b) (h : a * 2 ^ i = b * 2 ^ j) :
    a = b ∧ i = j := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hva : padicValNat 2 a = 0 :=
    padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])
  have hvb : padicValNat 2 b = 0 :=
    padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])
  have hij : i = j := by
    have := congrArg (padicValNat 2) h
    rwa [padicValNat.mul ha0 (by positivity), padicValNat.mul hb0 (by positivity),
      padicValNat.prime_pow, padicValNat.prime_pow, hva, hvb, zero_add, zero_add] at this
  subst hij
  exact ⟨Nat.eq_of_mul_eq_mul_right (by positivity) h, rfl⟩

/-- The real version with integer exponents: `a 2^i = b 2^j` with `a`, `b` odd gives `a = b`. -/
theorem odd_eq_of_mul_two_zpow_eq {a b : ℕ} (ha : Odd a) (hb : Odd b) {i j : ℤ}
    (h : (a : ℝ) * (2 : ℝ) ^ i = b * (2 : ℝ) ^ j) : a = b := by
  rcases le_total i j with hij | hij
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, j = i + d := ⟨(j - i).toNat, by omega⟩
    have h' : (a : ℝ) = b * 2 ^ d := by
      have h2 : (2 : ℝ) ^ j = 2 ^ i * 2 ^ d := by rw [hd, zpow_add₀ (by norm_num), zpow_natCast]
      rw [h2] at h
      have hi0 : (2 : ℝ) ^ i ≠ 0 := zpow_ne_zero _ (by norm_num)
      have : (a : ℝ) * 2 ^ i = (b * 2 ^ d) * 2 ^ i := by rw [h]; ring
      exact mul_right_cancel₀ hi0 this
    have hN : a * 2 ^ 0 = b * 2 ^ d := by
      rw [pow_zero, mul_one]; exact_mod_cast h'
    exact (odd_mul_two_pow_inj ha hb hN).1
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, i = j + d := ⟨(i - j).toNat, by omega⟩
    have h' : (a : ℝ) * 2 ^ d = b := by
      have h2 : (2 : ℝ) ^ i = 2 ^ j * 2 ^ d := by rw [hd, zpow_add₀ (by norm_num), zpow_natCast]
      rw [h2] at h
      have hj0 : (2 : ℝ) ^ j ≠ 0 := zpow_ne_zero _ (by norm_num)
      have : (a * 2 ^ d : ℝ) * 2 ^ j = b * 2 ^ j := by rw [← h]; ring
      exact mul_right_cancel₀ hj0 this
    have hN : a * 2 ^ d = b * 2 ^ 0 := by
      rw [pow_zero, mul_one]; exact_mod_cast h'
    exact (odd_mul_two_pow_inj ha hb hN).1

/-- A member of `floatSet (p + 1)` that is a real is `0` or `M 2^k` with `|M| < 2^(p+1)`. -/
theorem exists_of_mem_floatSet (p : ℕ) [NeZero p] {v : ℝ}
    (h : ((v : ℝ) : EReal) ∈ floatSet (p + 1)) :
    v = 0 ∨ ∃ M k : ℤ, M ≠ 0 ∧ |M| < 2 ^ (p + 1) ∧ (M : ℝ) * (2 : ℝ) ^ k = v := by
  rw [floatSet_eq] at h
  rcases h with h | h
  · rcases h with h0 | ⟨M, k, hM0, hMlt, hMk⟩
    · left; exact_mod_cast h0
    · right
      refine ⟨M, k, hM0, by exact_mod_cast hMlt, ?_⟩
      have := EReal.coe_eq_coe_iff.mp hMk
      rw [← this]
      norm_num
  · exfalso
    rcases h with h | h <;> simp at h

/-- `± a 2^k` with an odd `a ≥ 2^(p+1)` is not a rounding boundary at precision `p`. -/
theorem not_mem_floatSet_of_odd_mul (p : ℕ) [NeZero p] {a : ℕ} (ha : Odd a)
    (hap : 2 ^ (p + 1) ≤ a) (k : ℤ) {σ : ℝ} (hσ : |σ| = 1) :
    ((σ * a * (2 : ℝ) ^ k : ℝ) : EReal) ∉ floatSet (p + 1) := by
  intro h
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hσ0 : σ ≠ 0 := by intro h0; rw [h0, abs_zero] at hσ; norm_num at hσ
  rcases exists_of_mem_floatSet p h with h0 | ⟨M, j, hM0, hMlt, hMk⟩
  · have : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
    have h2 : (2 : ℝ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
    exact mul_ne_zero (mul_ne_zero hσ0 this) h2 h0
  · have habs : (M.natAbs : ℝ) * (2 : ℝ) ^ j = a * (2 : ℝ) ^ k := by
      have := congrArg (fun x : ℝ => |x|) hMk
      rw [abs_mul, abs_mul, abs_mul, hσ, one_mul,
        abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) j),
        abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k), Int.cast_abs.symm, ← Nat.cast_natAbs,
        Nat.abs_cast] at this
      exact this
    obtain ⟨c, M', hM', hMeq⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hM0)
    have heq : (M' : ℝ) * (2 : ℝ) ^ ((c : ℤ) + j) = a * (2 : ℝ) ^ k := by
      rw [zpow_add₀ (by norm_num), zpow_natCast, ← habs, hMeq]
      push_cast
      ring
    have hM'a := odd_eq_of_mul_two_zpow_eq hM' ha heq
    have hle : a ≤ M.natAbs := by
      rw [hMeq, ← hM'a]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    have hlt : M.natAbs < 2 ^ (p + 1) := by
      have := hMlt
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this
    omega

/-- `± 2^k / a` with an odd `a ≥ 3` is not a rounding boundary at any precision. -/
theorem not_mem_floatSet_of_div_odd (p : ℕ) [NeZero p] {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (k : ℤ) {σ : ℝ} (hσ : |σ| = 1) :
    ((σ * (2 : ℝ) ^ k / a : ℝ) : EReal) ∉ floatSet (p + 1) := by
  intro h
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hσ0 : σ ≠ 0 := by intro h0; rw [h0, abs_zero] at hσ; norm_num at hσ
  rcases exists_of_mem_floatSet p h with h0 | ⟨M, j, hM0, -, hMk⟩
  · have h2 : (2 : ℝ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
    exact div_ne_zero (mul_ne_zero hσ0 h2) ha0 h0
  · have habs : (M.natAbs : ℝ) * (2 : ℝ) ^ j * a = (2 : ℝ) ^ k := by
      have := congrArg (fun x : ℝ => |x|) hMk
      rw [abs_mul, abs_div, abs_mul, hσ, one_mul,
        abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) j),
        abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k), Int.cast_abs.symm, ← Nat.cast_natAbs,
        Nat.abs_cast] at this
      rw [this]
      field_simp
    obtain ⟨c, M', hM', hMeq⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hM0)
    have heq : ((M' * a : ℕ) : ℝ) * (2 : ℝ) ^ ((c : ℤ) + j) = (1 : ℕ) * (2 : ℝ) ^ k := by
      rw [zpow_add₀ (by norm_num), zpow_natCast, ← habs, hMeq]
      push_cast
      ring
    have h1 := odd_eq_of_mul_two_zpow_eq (hM'.mul ha) odd_one heq
    have : a ∣ 1 := ⟨M', by rw [mul_comm]; exact h1.symm⟩
    have := Nat.le_of_dvd one_pos this
    omega

/-! ### The odd part and the iterated square root -/

/-- `m = odd · 2^c` with `(odd, c) = splitOdd m`, for `m ≠ 0`. -/
theorem splitOdd_spec (m : AzNat) (hm : m ≠ 0) :
    m.toNat = (splitOdd m).1.toNat * 2 ^ (splitOdd m).2 ∧ Odd (splitOdd m).1.toNat := by
  have hm0 : m.toNat ≠ 0 := fun h => hm (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have htz : m.trailingZeros = some (padicValNat 2 m.toNat) :=
    AzNat.trailingZeros_eq_padicValNat m hm
  simp only [splitOdd, htz, Option.getD_some, AzNat.toNat_shiftRight]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ padicValNat 2 m.toNat ∣ m.toNat := pow_padicValNat_dvd
  refine ⟨(Nat.div_mul_cancel hdvd).symm, ?_⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  apply pow_succ_padicValNat_not_dvd (p := 2) hm0
  obtain ⟨q, hq⟩ := h2
  refine ⟨q, ?_⟩
  calc m.toNat = m.toNat / 2 ^ padicValNat 2 m.toNat * 2 ^ padicValNat 2 m.toNat :=
        (Nat.div_mul_cancel hdvd).symm
    _ = 2 * q * 2 ^ padicValNat 2 m.toNat := by rw [hq]
    _ = 2 ^ (padicValNat 2 m.toNat + 1) * q := by ring

theorem iterSqrt_some : ∀ (m : AzNat) (J : ℕ) {r : AzNat}, iterSqrt m J = some r →
    m.toNat = r.toNat ^ (2 ^ J)
  | m, 0, r, h => by
    simp only [iterSqrt, Option.some.injEq] at h
    rw [← h, pow_zero, pow_one]
  | m, J + 1, r, h => by
    simp only [iterSqrt] at h
    split_ifs at h with hrem
    have hsq : m.toNat = (m.sqrtRem).1.toNat ^ 2 := by
      have h2 := AzNat.toNat_sqrtRem_snd m
      rw [hrem, AzNat.toNat_zero] at h2
      have h3 := Nat.sqrt_le m.toNat
      rw [AzNat.toNat_sqrtRem_fst, sq]
      omega
    have ih := iterSqrt_some _ J h
    rw [hsq, ih, ← pow_mul, pow_succ]

theorem iterSqrt_none : ∀ (m : AzNat) (J : ℕ), iterSqrt m J = none →
    ¬ ∃ c : ℕ, m.toNat = c ^ (2 ^ J)
  | _, 0, h => by simp [iterSqrt] at h
  | m, J + 1, h => by
    simp only [iterSqrt] at h
    split_ifs at h with hrem
    · rintro ⟨c, hc⟩
      refine iterSqrt_none _ J h ⟨c, ?_⟩
      have h2 := AzNat.toNat_sqrtRem_snd m
      rw [hrem, AzNat.toNat_zero] at h2
      have h3 := Nat.sqrt_le m.toNat
      have hsq : m.toNat = (m.sqrtRem).1.toNat ^ 2 := by
        rw [AzNat.toNat_sqrtRem_fst, sq]; omega
      have : (m.sqrtRem).1.toNat ^ 2 = (c ^ (2 ^ J)) ^ 2 := by
        rw [← hsq, hc, ← pow_mul, ← pow_succ]
      exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp this
    · rintro ⟨c, hc⟩
      apply hrem
      apply AzNat.toNat_injective
      rw [AzNat.toNat_sqrtRem_snd, AzNat.toNat_zero, hc, pow_succ, pow_mul, Nat.sqrt_eq', sq,
        Nat.sub_self]

/-- `oddPow2Root m J = some u` gives `m = u^(2^J)`. -/
theorem oddPow2Root_some {m : AzNat} {J : ℕ} {u : AzNat} (h : oddPow2Root m J = some u) :
    m.toNat = u.toNat ^ (2 ^ J) := by
  unfold oddPow2Root at h
  split_ifs at h with h1 h2
  · rw [Option.some.injEq] at h
    rw [h1, ← h, AzNat.toNat_ofNat, one_pow]
  · exact iterSqrt_some m J h

/-- `oddPow2Root m J = none` for an odd `m`: `m` is not a `2^J`-th power. -/
theorem oddPow2Root_none {m : AzNat} (hm : Odd m.toNat) {J : ℕ} (h : oddPow2Root m J = none) :
    ¬ ∃ c : ℕ, m.toNat = c ^ (2 ^ J) := by
  unfold oddPow2Root at h
  split_ifs at h with h1 h2
  · rintro ⟨c, hc⟩
    have hm1 : m.toNat ≠ 1 := fun h' => h1 (AzNat.toNat_injective (by rw [h', AzNat.toNat_ofNat]))
    have hm0 : m.toNat ≠ 0 := by rintro h0; rw [h0] at hm; simp at hm
    have hc2 : 2 ≤ c := by
      rcases Nat.lt_or_ge c 2 with hc' | hc'
      · interval_cases c
        · rw [zero_pow (by positivity)] at hc; exact absurd hc hm0
        · rw [one_pow] at hc; exact absurd hc hm1
      · exact hc'
    have hsize : m.toNat < 2 ^ m.size := by rw [← AzNat.size_toNat]; exact Nat.lt_size_self _
    have hJ : 2 ^ m.size ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) h2
    have hJ2 : 2 ^ J < 2 ^ (2 ^ J) := Nat.lt_two_pow_self
    have hc : 2 ^ (2 ^ J) ≤ c ^ (2 ^ J) := Nat.pow_le_pow_left hc2 _
    omega
  · exact iterSqrt_none m J h

/-! ### Irrationality -/

/-- `M^(N/D)` is irrational for a natural `M ≥ 1` that is not a `D`-th power, `D ≥ 2`,
`N ≥ 1` and `gcd(D, N) = 1`. -/
theorem irrational_natCast_rpow_div_of_not_pow {M : ℕ} (hM : 1 ≤ M) {D N : ℕ} (hD : 2 ≤ D)
    (hcop : Nat.Coprime D N) (hnp : ¬ ∃ c : ℕ, M = c ^ D) :
    Irrational ((M : ℝ) ^ ((N : ℝ) / D)) := by
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hpow : ((M : ℝ) ^ ((N : ℝ) / D)) ^ D = ((M ^ N : ℕ) : ℤ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0, div_mul_cancel₀ _ hD0, Real.rpow_natCast]
    push_cast
    rfl
  refine irrational_nrt_of_notint_nrt D _ hpow ?_ (by omega)
  rintro ⟨y, hy⟩
  have hpos : (0 : ℝ) < (M : ℝ) ^ ((N : ℝ) / D) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hM) _
  rw [hy] at hpos hpow
  have hy0 : 0 < y := by exact_mod_cast hpos
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = y := ⟨y.toNat, Int.toNat_of_nonneg hy0.le⟩
  rw [← ha] at hpow
  have hNat : a ^ D = M ^ N := by exact_mod_cast hpow
  obtain ⟨c, -, hMc⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcop hNat
  exact hnp ⟨c, hMc⟩

/-- **The dyadic case**: for an odd `m ≥ 1`, `(m 2^t)^(N/2^J)` with `N` odd and `J ≥ 1` is
irrational unless `2^J ∣ t` and `m` is a `2^J`-th power. -/
theorem irrational_dyadic_rpow {m : ℕ} (hm : Odd m) (t : ℤ) {N : ℤ} (hN : Odd N) {J : ℕ}
    (hJ : 1 ≤ J) (h : ¬ ((2 : ℤ) ^ J ∣ t ∧ ∃ u : ℕ, m = u ^ (2 ^ J))) :
    Irrational (((m : ℝ) * (2 : ℝ) ^ t) ^ ((N : ℝ) / (2 : ℝ) ^ J)) := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hm)
  have hbase : (0 : ℝ) < (m : ℝ) * (2 : ℝ) ^ t := by positivity
  -- reduce to a positive `N`
  have hmain : ∀ N' : ℕ, Odd N' →
      Irrational (((m : ℝ) * (2 : ℝ) ^ t) ^ ((N' : ℝ) / (2 : ℝ) ^ J)) := by
    intro N' hN'
    -- scale the base to a natural number `M = m 2^(t + 2^J k)`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 ≤ t + 2 ^ J * k := by
      refine ⟨t.natAbs, ?_⟩
      have h2J : (1 : ℤ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
      have h1 : -t ≤ (t.natAbs : ℤ) := by omega
      have h2 : (t.natAbs : ℤ) ≤ 2 ^ J * t.natAbs :=
        le_mul_of_one_le_left (by positivity) h2J
      linarith
    obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = t + 2 ^ J * k :=
      ⟨(t + 2 ^ J * k).toNat, Int.toNat_of_nonneg hk⟩
    set M : ℕ := m * 2 ^ e with hM
    have hMpos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsplit : (m : ℝ) * (2 : ℝ) ^ t = (M : ℝ) * (2 : ℝ) ^ (-((2 : ℤ) ^ J * k)) := by
      rw [hM]
      push_cast
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num), he]
      congr 2
      ring
    have hD : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
    have hexp : ((2 : ℝ) ^ (-((2 : ℤ) ^ J * k))) ^ ((N' : ℝ) / (2 : ℝ) ^ J)
        = ((2 : ℝ) ^ (-((k : ℤ) * N')) : ℝ) := by
      rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast]
      congr 1
      push_cast
      field_simp
    have hrat : ∃ q : ℚ, (q : ℝ) = (2 : ℝ) ^ (-((k : ℤ) * N')) ∧ q ≠ 0 :=
      ⟨(2 : ℚ) ^ (-((k : ℤ) * N')), by push_cast; rfl, zpow_ne_zero _ (by norm_num)⟩
    obtain ⟨q, hq, hq0⟩ := hrat
    rw [hsplit, Real.mul_rpow (by positivity) (by positivity), hexp, ← hq]
    refine Irrational.mul_ratCast ?_ hq0
    -- the core: `M` is not a `2^J`-th power
    have hcore : Irrational ((M : ℝ) ^ ((N' : ℝ) / ((2 ^ J : ℕ) : ℝ))) := by
      refine irrational_natCast_rpow_div_of_not_pow hMpos (D := 2 ^ J) (N := N') ?_ ?_ ?_
      · calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ
      · exact Nat.Coprime.pow_left J (Nat.coprime_two_left.mpr hN')
      · rintro ⟨c, hc⟩
        apply h
        have hc0 : c ≠ 0 := by rintro rfl; rw [zero_pow (by positivity)] at hc; omega
        obtain ⟨i, c', hc', hci⟩ := Nat.exists_eq_two_pow_mul_odd hc0
        have heq : m * 2 ^ e = c' ^ (2 ^ J) * 2 ^ (i * 2 ^ J) := by
          rw [← hM, hc, hci, mul_pow, ← pow_mul]
          ring
        obtain ⟨hm', he'⟩ := odd_mul_two_pow_inj hm (hc'.pow) heq
        refine ⟨?_, c', hm'⟩
        have : (e : ℤ) = (i : ℤ) * 2 ^ J := by exact_mod_cast he'
        rw [he] at this
        exact ⟨(i : ℤ) - k, by linarith⟩
    push_cast at hcore
    exact hcore
  rcases le_or_gt 0 N with hN0 | hN0
  · obtain ⟨N', hN'⟩ : ∃ N' : ℕ, (N' : ℤ) = N := ⟨N.toNat, Int.toNat_of_nonneg hN0⟩
    have hodd : Odd N' := by rw [← Int.odd_coe_nat, hN']; exact hN
    have := hmain N' hodd
    rwa [show ((N : ℤ) : ℝ) = (N' : ℝ) by rw [← hN']; push_cast; rfl]
  · obtain ⟨N', hN'⟩ : ∃ N' : ℕ, (N' : ℤ) = -N := ⟨(-N).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hodd : Odd N' := by rw [← Int.odd_coe_nat, hN']; exact hN.neg
    have := hmain N' hodd
    have e : -(((N : ℤ) : ℝ)) = (N' : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hN'
      simp only [Int.cast_natCast, Int.cast_neg] at this
      exact this.symm
    rw [← irrational_inv_iff, ← Real.rpow_neg hbase.le, ← neg_div, e]
    exact this

/-! ### The exact powers -/


/-- The value of a positive float through the odd part of its significand: `m' 2^t`. -/
theorem finiteVal_true_eq_oddShift (ex : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    finiteVal true ex m
      = ((splitOdd m).1.toNat : ℝ) * (2 : ℝ) ^ (ex.toInt - m.size + (splitOdd m).2 : ℤ) := by
  have hm0 : m ≠ 0 := ne_zero_of_finiteValid 0 hv
  obtain ⟨hdec, -⟩ := splitOdd_spec m hm0
  show (1 : ℝ) * (m.toNat : ℝ) * (2 : ℝ) ^ (ex.toInt - m.size) = _
  rw [one_mul, hdec]
  push_cast
  rw [zpow_add₀ (by norm_num), zpow_natCast]
  ring

/-- The value of a float through the odd part of its significand: `±n' 2^(e − size + c)`. -/
theorem finiteVal_eq_oddShift (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    finiteVal s e m
      = ((AzInt.mkNorm s (splitOdd m).1).toInt : ℝ)
        * (2 : ℝ) ^ (e.toInt - m.size + (splitOdd m).2 : ℤ) := by
  have hm0 : m ≠ 0 := ne_zero_of_finiteValid 0 hv
  obtain ⟨hdec, hodd⟩ := splitOdd_spec m hm0
  have hodd0 : (splitOdd m).1 ≠ 0 := by
    intro h0
    rw [h0, AzNat.toNat_zero] at hodd
    simp at hodd
  cases s with
  | true =>
    show (1 : ℝ) * (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size) = _
    rw [hdec, AzInt.toInt_mkNorm_true]
    push_cast
    rw [zpow_add₀ (by norm_num), zpow_natCast]
    ring
  | false =>
    show (-1 : ℝ) * (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size) = _
    rw [hdec, AzInt.toInt_mkNorm_false _ hodd0]
    push_cast
    rw [zpow_add₀ (by norm_num), zpow_natCast]
    ring

/-- The integer `t = ex − size mx + c` of `powExact?`. -/
theorem toInt_powExact_t (ex : AzInt) (mx : AzNat) :
    (ex - (AzNat.ofNat mx.size).toAzInt + (AzNat.ofNat (splitOdd mx).2).toAzInt).toInt
      = ex.toInt - mx.size + (splitOdd mx).2 := by
  rw [AzInt.toInt_add, AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt,
    AzNat.toNat_ofNat, AzNat.toNat_ofNat]

/-- The integer `size my − cy − ey` of `powExact?`. -/
theorem toInt_powExact_J (ey : AzInt) (my : AzNat) :
    ((AzNat.ofNat my.size).toAzInt - (AzNat.ofNat (splitOdd my).2).toAzInt - ey).toInt
      = (my.size : ℤ) - (splitOdd my).2 - ey.toInt := by
  rw [AzInt.toInt_sub, AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt,
    AzNat.toNat_ofNat, AzNat.toNat_ofNat]

theorem toNat_abs_eq_natAbs (z : AzInt) : z.abs.toNat = z.toInt.natAbs :=
  AzInt.toNat_natAbs z

/-- A non-integer float `y = ±my 2^(ey − size my)` has `Jz = size my − cy − ey ≥ 1`, and then
`y = N / 2^J` with `N = ±(odd part of my)` and `J = Jz.natAbs`. -/
theorem finiteVal_eq_div_of_not_isInteger (sy : Bool) (ey : AzInt) {qy : ℕ} {my : AzNat}
    (hvy : FiniteValid qy my) (hni : isInteger (finite sy ey qy my hvy) = false) :
    1 ≤ (my.size : ℤ) - (splitOdd my).2 - ey.toInt ∧
      (((my.size : ℤ) - (splitOdd my).2 - ey.toInt).natAbs : ℤ)
        = (my.size : ℤ) - (splitOdd my).2 - ey.toInt ∧
      finiteVal sy ey my
        = ((AzInt.mkNorm sy (splitOdd my).1).toInt : ℝ)
          / (2 : ℝ) ^ ((my.size : ℤ) - (splitOdd my).2 - ey.toInt).natAbs := by
  have hval := finiteVal_eq_oddShift sy ey hvy
  have hnot : ¬ ∃ n : ℤ, finiteVal sy ey my = n := by
    intro hex
    have := (isInteger_finite sy ey hvy).mpr hex
    rw [hni] at this
    exact Bool.false_ne_true this
  set Jz : ℤ := (my.size : ℤ) - (splitOdd my).2 - ey.toInt with hJz
  have hJ1 : 1 ≤ Jz := by
    by_contra hle
    push Not at hle
    apply hnot
    refine ⟨(AzInt.mkNorm sy (splitOdd my).1).toInt * 2 ^ (-Jz).toNat, ?_⟩
    rw [hval]
    push_cast
    congr 1
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    congr 1
    rw [hJz]
    ring
  refine ⟨hJ1, Int.natAbs_of_nonneg (by omega), ?_⟩
  rw [hval, div_eq_mul_inv, ← zpow_natCast, ← zpow_neg, Int.natAbs_of_nonneg (by omega)]
  congr 2
  rw [hJz]
  ring

/-- `powExact? = some (z, N)`: `z` is a positive float with `x^y = z^N`, `N ≠ 0`. -/
theorem powExact?_some (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx) (sy : Bool)
    (ey : AzInt) {qy : ℕ} {my : AzNat} (hvy : FiniteValid qy my)
    (hni : isInteger (finite sy ey qy my hvy) = false) {z : AzFloat} {N : AzInt}
    (h : powExact? ex mx sy ey my = some (z, N)) :
    ∃ zv : ℝ, z.toVal = some (zv : EReal) ∧ 0 < zv ∧
      finiteVal true ex mx ^ finiteVal sy ey my = zv ^ N.toInt ∧ N.toInt ≠ 0 := by
  obtain ⟨hJ1, hJabs, hyv⟩ := finiteVal_eq_div_of_not_isInteger sy ey hvy hni
  have hxv := finiteVal_true_eq_oddShift ex hvx
  have hmx0 : mx ≠ 0 := ne_zero_of_finiteValid 0 hvx
  have hmy0 : my ≠ 0 := ne_zero_of_finiteValid 0 hvy
  obtain ⟨-, hmodd⟩ := splitOdd_spec mx hmx0
  obtain ⟨-, hnodd⟩ := splitOdd_spec my hmy0
  -- the pieces of the definition
  obtain ⟨t, ht⟩ : ∃ t : AzInt,
      t = ex - (AzNat.ofNat mx.size).toAzInt + (AzNat.ofNat (splitOdd mx).2).toAzInt := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℕ,
      J = ((AzNat.ofNat my.size).toAzInt - (AzNat.ofNat (splitOdd my).2).toAzInt - ey).abs.toNat :=
    ⟨_, rfl⟩
  have htI : t.toInt = ex.toInt - mx.size + (splitOdd mx).2 := by rw [ht, toInt_powExact_t]
  have hJI : (J : ℤ) = (my.size : ℤ) - (splitOdd my).2 - ey.toInt := by
    rw [hJ, toNat_abs_eq_natAbs, toInt_powExact_J]
    exact hJabs
  have hJnat : J = ((my.size : ℤ) - (splitOdd my).2 - ey.toInt).natAbs := by
    rw [hJ, toNat_abs_eq_natAbs, toInt_powExact_J]
  unfold powExact? at h
  simp only [] at h
  rw [← ht, ← hJ] at h
  split_ifs at h with hdiv
  cases hroot : oddPow2Root (splitOdd mx).1 J with
  | none => rw [hroot] at h; cases h
  | some u =>
    rw [hroot] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hz, hN⟩ := h
    have hu := oddPow2Root_some hroot
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, AzNat.toNat_zero, zero_pow (by positivity)] at hu
      rw [hu] at hmodd
      simp at hmodd
    have hupos : (0 : ℝ) < u.toNat := by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun h0 => hu0 (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])))
    -- `2^J ∣ t`
    have hdvd : (2 : ℤ) ^ J ∣ t.toInt := by
      rcases hdiv with h0 | hle
      · rw [h0, AzInt.toInt_zero]; exact dvd_zero _
      · by_cases ht0 : t = 0
        · rw [ht0, AzInt.toInt_zero]; exact dvd_zero _
        · rw [AzInt.trailingZeros_eq_padicValInt t ht0, Option.getD_some] at hle
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact (padicValInt_dvd_iff (p := 2) J t.toInt).mpr (Or.inr hle)
    obtain ⟨t', ht'⟩ := hdvd
    have htdiv : (t.ediv (AzNat.ofNat (2 ^ J)).toAzInt).toInt = t' := by
      rw [AzInt.toInt_ediv, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, ht']
      push_cast
      rw [Int.mul_ediv_cancel_left _ (by positivity)]
    -- the value of `z`
    have hzv : z.toVal = some (((u.toNat : ℝ) * (2 : ℝ) ^ t' : ℝ) : EReal) := by
      rw [← hz, toVal_mkFinite _ _ _ _ hu0]
      congr 2
      show (1 : ℝ) * (u.toNat : ℝ) * (2 : ℝ) ^ ((_ : AzInt).toInt - u.size) = _
      rw [one_mul, AzInt.toInt_add, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, htdiv]
      congr 2
      ring
    refine ⟨(u.toNat : ℝ) * (2 : ℝ) ^ t', hzv, by positivity, ?_, ?_⟩
    · -- `x = (u 2^t')^(2^J)` and `y = N / 2^J`
      have hx : finiteVal true ex mx = ((u.toNat : ℝ) * (2 : ℝ) ^ t') ^ (2 ^ J) := by
        rw [hxv, ← htI, ht', hu, mul_pow]
        push_cast
        congr 1
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
      rw [hx, hyv, ← hJnat, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← hN]
      have h2J : ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J := by push_cast; rfl
      rw [h2J, mul_div_cancel₀ _ (by positivity), Real.rpow_intCast]
    · rw [← hN]
      have hn0 : (splitOdd my).1 ≠ 0 := by
        intro h0
        rw [h0, AzNat.toNat_zero] at hnodd
        simp at hnodd
      have hn0' : (splitOdd my).1.toNat ≠ 0 :=
        fun h0 => hn0 (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero]))
      cases sy with
      | true => rw [AzInt.toInt_mkNorm_true]; exact_mod_cast hn0'
      | false => rw [AzInt.toInt_mkNorm_false _ hn0]; exact neg_ne_zero.mpr (by exact_mod_cast hn0')

/-- `powExact? = none` for a positive `x` and a non-integer `y`: `x^y` is irrational. -/
theorem irrational_of_powExact?_none (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx)
    (sy : Bool) (ey : AzInt) {qy : ℕ} {my : AzNat} (hvy : FiniteValid qy my)
    (hni : isInteger (finite sy ey qy my hvy) = false)
    (h : powExact? ex mx sy ey my = none) :
    Irrational (finiteVal true ex mx ^ finiteVal sy ey my) := by
  obtain ⟨hJ1, hJabs, hyv⟩ := finiteVal_eq_div_of_not_isInteger sy ey hvy hni
  have hxv := finiteVal_true_eq_oddShift ex hvx
  have hmx0 : mx ≠ 0 := ne_zero_of_finiteValid 0 hvx
  have hmy0 : my ≠ 0 := ne_zero_of_finiteValid 0 hvy
  obtain ⟨-, hmodd⟩ := splitOdd_spec mx hmx0
  obtain ⟨-, hnodd⟩ := splitOdd_spec my hmy0
  obtain ⟨t, ht⟩ : ∃ t : AzInt,
      t = ex - (AzNat.ofNat mx.size).toAzInt + (AzNat.ofNat (splitOdd mx).2).toAzInt := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℕ,
      J = ((AzNat.ofNat my.size).toAzInt - (AzNat.ofNat (splitOdd my).2).toAzInt - ey).abs.toNat :=
    ⟨_, rfl⟩
  have htI : t.toInt = ex.toInt - mx.size + (splitOdd mx).2 := by rw [ht, toInt_powExact_t]
  have hJnat : J = ((my.size : ℤ) - (splitOdd my).2 - ey.toInt).natAbs := by
    rw [hJ, toNat_abs_eq_natAbs, toInt_powExact_J]
  have hJ1' : 1 ≤ J := by
    have : (1 : ℤ) ≤ (J : ℤ) := by rw [hJnat, hJabs]; exact hJ1
    exact_mod_cast this
  have hNodd : Odd (AzInt.mkNorm sy (splitOdd my).1).toInt := by
    have hn0 : (splitOdd my).1 ≠ 0 := by
      intro h0
      rw [h0, AzNat.toNat_zero] at hnodd
      simp at hnodd
    cases sy with
    | true => rw [AzInt.toInt_mkNorm_true]; exact_mod_cast hnodd
    | false => rw [AzInt.toInt_mkNorm_false _ hn0]; exact (by exact_mod_cast hnodd : Odd _).neg
  rw [hxv, hyv, ← htI, ← hJnat]
  refine irrational_dyadic_rpow hmodd t.toInt hNodd hJ1' ?_
  rintro ⟨hdvd, u, hu⟩
  unfold powExact? at h
  simp only [] at h
  rw [← ht, ← hJ] at h
  split_ifs at h with hdiv
  · cases hroot : oddPow2Root (splitOdd mx).1 J with
    | none => exact oddPow2Root_none hmodd hroot ⟨u, hu⟩
    | some u' => rw [hroot] at h; cases h
  · apply hdiv
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    · right
      rw [AzInt.trailingZeros_eq_padicValInt t ht0, Option.getD_some]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rcases (padicValInt_dvd_iff (p := 2) J t.toInt).mp hdvd with h0 | hle
      · exact absurd h0 (toInt_ne_zero_of_ne_zero ht0)
      · exact hle

/-! ### The non-cheap powers are not boundaries -/

/-- `powIntCheap m n p = false`: `|n| (size m' − 1) > p + 1` for the odd part `m'` of `m`. -/
theorem lt_of_powIntCheap_false {m : AzNat} {n : AzInt} {p : ℕ} (h : powIntCheap m n p = false) :
    p + 1 < n.toInt.natAbs * ((splitOdd m).1.size - 1) := by
  unfold powIntCheap at h
  rw [decide_eq_false_iff_not, AzNat.le_iff_toNat_le, AzNat.toNat_mul, AzNat.toNat_ofNat,
    AzNat.toNat_ofNat, toNat_abs_eq_natAbs] at h
  omega

/-- The odd part of a valid significand is at least `2^(size − 1)` and at least `3` when its size
is at least `2`. -/
theorem oddShift_ge {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    2 ^ ((splitOdd m).1.size - 1) ≤ (splitOdd m).1.toNat ∧
      (2 ≤ (splitOdd m).1.size → 3 ≤ (splitOdd m).1.toNat) := by
  have hm0 : m ≠ 0 := ne_zero_of_finiteValid 0 hv
  obtain ⟨-, hodd⟩ := splitOdd_spec m hm0
  have hpos : 0 < (splitOdd m).1.toNat :=
    Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hodd; simp at hodd)
  have hsz : 0 < (splitOdd m).1.size := by
    rw [← AzNat.size_toNat]; exact Nat.size_pos.mpr hpos
  have hge : 2 ^ ((splitOdd m).1.size - 1) ≤ (splitOdd m).1.toNat := by
    rw [← AzNat.size_toNat] at hsz ⊢
    exact Nat.lt_size.mp (by omega)
  refine ⟨hge, fun h2 => ?_⟩
  have h4 : 2 ≤ (splitOdd m).1.toNat := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ((splitOdd m).1.size - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := hge
  rcases hodd with ⟨k, hk⟩
  omega

/-- A power `± (m 2^T)^n` that is not cheap is not a rounding boundary at precision `p`: its odd
part `m'^|n|` has more than `p + 1` bits for `n > 0`, and it is not dyadic for `n < 0`. -/
theorem not_mem_floatSet_of_not_cheap (p : ℕ) [NeZero p] (ez : AzInt) {qz : ℕ} {mz : AzNat}
    (hvz : FiniteValid qz mz) {n : AzInt} (hn : n ≠ 0) (hc : powIntCheap mz n p = false)
    {σ : ℝ} (hσ : |σ| = 1) :
    ((σ * finiteVal true ez mz ^ n.toInt : ℝ) : EReal) ∉ floatSet (p + 1) := by
  have hlt := lt_of_powIntCheap_false hc
  obtain ⟨hge, h3⟩ := oddShift_ge hvz
  have hmz0 : mz ≠ 0 := ne_zero_of_finiteValid 0 hvz
  obtain ⟨-, hodd⟩ := splitOdd_spec mz hmz0
  set m' := (splitOdd mz).1.toNat with hm'
  set T : ℤ := ez.toInt - mz.size + (splitOdd mz).2 with hT
  have hval : finiteVal true ez mz = (m' : ℝ) * (2 : ℝ) ^ T := finiteVal_true_eq_oddShift ez hvz
  set a := n.toInt.natAbs with ha
  have hsz2 : 2 ≤ (splitOdd mz).1.size := by
    by_contra hlt2
    push Not at hlt2
    have : (splitOdd mz).1.size - 1 = 0 := by omega
    rw [this, mul_zero] at hlt
    omega
  have hm3 := h3 hsz2
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, zero_mul] at hlt; omega
    · exact h0
  have hpowodd : Odd (m' ^ a) := hodd.pow
  have hpow3 : 3 ≤ m' ^ a := by
    calc 3 ≤ m' := hm3
      _ = m' ^ 1 := (pow_one _).symm
      _ ≤ m' ^ a := Nat.pow_le_pow_right (by omega) ha0
  have hpowbig : 2 ^ (p + 1) ≤ m' ^ a := by
    calc 2 ^ (p + 1) ≤ 2 ^ (a * ((splitOdd mz).1.size - 1)) :=
          Nat.pow_le_pow_right (by norm_num) hlt.le
      _ = (2 ^ ((splitOdd mz).1.size - 1)) ^ a := by rw [← pow_mul, mul_comm]
      _ ≤ m' ^ a := Nat.pow_le_pow_left hge a
  have hm'0 : (0 : ℝ) < m' := by exact_mod_cast (show 0 < m' by omega)
  rcases lt_or_gt_of_ne (toInt_ne_zero_of_ne_zero hn) with hneg | hpos
  · -- `n < 0`: `σ 2^(T n) / m'^a`
    have hna : n.toInt = -(a : ℤ) := by rw [ha, Int.ofNat_natAbs_of_nonpos hneg.le]; ring
    have heq : σ * finiteVal true ez mz ^ n.toInt
        = σ * (2 : ℝ) ^ (T * n.toInt) / ((m' ^ a : ℕ) : ℝ) := by
      rw [hval, mul_zpow, ← zpow_mul, hna, zpow_neg, zpow_natCast]
      push_cast
      field_simp
    rw [heq]
    exact not_mem_floatSet_of_div_odd p hpowodd hpow3 _ hσ
  · -- `n > 0`: `σ m'^a 2^(T n)`
    have hna : n.toInt = (a : ℤ) := by rw [ha, Int.natAbs_of_nonneg hpos.le]
    have heq : σ * finiteVal true ez mz ^ n.toInt
        = σ * ((m' ^ a : ℕ) : ℝ) * (2 : ℝ) ^ (T * n.toInt) := by
      rw [hval, mul_zpow, ← zpow_mul, hna, zpow_natCast]
      push_cast
      ring
    rw [heq]
    exact not_mem_floatSet_of_odd_mul p hpowodd hpowbig _ hσ

/-! ### The natural-base powers minus one -/

/-- `± a 2^k / b` with `b ≥ 3` odd and `gcd(a, b) = 1` is not a rounding boundary. -/
theorem not_mem_floatSet_of_div_odd_coprime (p : ℕ) [NeZero p] {a b : ℕ} (ha : a ≠ 0)
    (hb : Odd b) (hb3 : 3 ≤ b) (hcop : Nat.Coprime a b) (k : ℤ) {σ : ℝ} (hσ : |σ| = 1) :
    ((σ * a * (2 : ℝ) ^ k / b : ℝ) : EReal) ∉ floatSet (p + 1) := by
  intro h
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hσ0 : σ ≠ 0 := by intro h0; rw [h0, abs_zero] at hσ; norm_num at hσ
  rcases exists_of_mem_floatSet p h with h0 | ⟨M, j, hM0, -, hMk⟩
  · have h2 : (2 : ℝ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hσ0 ha') h2) hb0 h0
  · have habs : (M.natAbs : ℝ) * (2 : ℝ) ^ j * b = a * (2 : ℝ) ^ k := by
      have := congrArg (fun x : ℝ => |x|) hMk
      rw [abs_mul, abs_div, abs_mul, abs_mul, hσ, one_mul,
        abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) j),
        abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k), Int.cast_abs.symm,
        ← Nat.cast_natAbs, Nat.abs_cast, Nat.abs_cast] at this
      rw [this]
      field_simp
    obtain ⟨c, M', hM', hMeq⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hM0)
    obtain ⟨d, a', ha', haeq⟩ := Nat.exists_eq_two_pow_mul_odd ha
    have heq : ((M' * b : ℕ) : ℝ) * (2 : ℝ) ^ ((c : ℤ) + j)
        = (a' : ℝ) * (2 : ℝ) ^ ((d : ℤ) + k) := by
      have h2 : (2 : ℝ) ^ c * M' * 2 ^ j * b = 2 ^ d * a' * 2 ^ k := by
        have := habs
        rw [hMeq, haeq] at this
        push_cast at this
        linear_combination this
      rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_natCast, zpow_natCast]
      push_cast
      linear_combination h2
    have h1 := odd_eq_of_mul_two_zpow_eq (hM'.mul hb) ha' heq
    have hdvd : b ∣ a := ⟨2 ^ d * M', by rw [haeq, ← h1]; ring⟩
    have := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd
    omega

/-- `natPowM1Cheap r n p = false` forces `n ≠ 0`. -/
theorem ne_zero_of_natPowM1Cheap_false {r : AzNat} {n : AzInt} {p : ℕ}
    (hc : natPowM1Cheap r n p = false) : n ≠ 0 := by
  rintro rfl
  unfold natPowM1Cheap at hc
  rw [decide_eq_false_iff_not, AzNat.le_iff_toNat_le, AzNat.toNat_mul] at hc
  apply hc
  have : (0 : AzInt).abs.toNat = 0 := rfl
  rw [this, zero_mul]
  exact Nat.zero_le _

/-- `natPowM1Cheap r n p = false`: `|n| (size m' − 1) > p + 3 + 2 size r + size |n|`. -/
theorem lt_of_natPowM1Cheap_false {r : AzNat} {n : AzInt} {p : ℕ}
    (hc : natPowM1Cheap r n p = false) :
    p + 3 + 2 * r.size + n.toInt.natAbs.size < n.toInt.natAbs * ((splitOdd r).1.size - 1) := by
  unfold natPowM1Cheap at hc
  rw [decide_eq_false_iff_not, AzNat.le_iff_toNat_le, AzNat.toNat_mul, AzNat.toNat_ofNat,
    AzNat.toNat_ofNat, toNat_abs_eq_natAbs] at hc
  have hs : n.abs.size = n.toInt.natAbs.size := by rw [← AzNat.size_toNat, toNat_abs_eq_natAbs]
  rw [hs] at hc
  omega

/-- `r^n − 1 ≠ 0` for `r ≥ 2` and `n ≠ 0`. -/
theorem natPow_sub_one_ne_zero {r : ℕ} (hr : 2 ≤ r) {n : ℤ} (hn : n ≠ 0) :
    ((r : ℝ) ^ n - 1 : ℝ) ≠ 0 := by
  intro h
  have h1 : (r : ℝ) ^ n = 1 := by linarith
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hr1 : (r : ℝ) ≠ 1 := by exact_mod_cast (show r ≠ 1 by omega)
  exact hn ((zpow_eq_one_iff_right₀ hr0 hr1).mp h1)

/-- **A non-cheap `r^n − 1` is not a rounding boundary** at precision `p`. -/
theorem not_mem_floatSet_natPow_sub_one (p : ℕ) [NeZero p] {r : AzNat} (hr2 : 2 ≤ r.toNat)
    {n : AzInt} (hc : natPowM1Cheap r n p = false) :
    (((r.toNat : ℝ) ^ n.toInt - 1 : ℝ) : EReal) ∉ floatSet (p + 1) := by
  have hlt := lt_of_natPowM1Cheap_false hc
  have hr0 : r ≠ 0 := fun h => by rw [h, AzNat.toNat_zero] at hr2; omega
  obtain ⟨hdec, hodd⟩ := splitOdd_spec r hr0
  set m' := (splitOdd r).1.toNat with hm'
  set c := (splitOdd r).2 with hcdef
  set a := n.toInt.natAbs with ha
  have hsz2 : 2 ≤ (splitOdd r).1.size := by
    by_contra hlt2
    push Not at hlt2
    have : (splitOdd r).1.size - 1 = 0 := by omega
    rw [this, mul_zero] at hlt
    omega
  have hm'3 : 3 ≤ m' := by
    have hpos : 0 < m' := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hodd; simp at hodd)
    have hge : 2 ^ ((splitOdd r).1.size - 1) ≤ m' := by
      rw [hm', ← AzNat.size_toNat]
      exact Nat.lt_size.mp (by rw [AzNat.size_toNat]; omega)
    have h4 : 2 ≤ m' := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ ((splitOdd r).1.size - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ m' := hge
    rcases hodd with ⟨k, hk⟩
    omega
  have hge : 2 ^ ((splitOdd r).1.size - 1) ≤ m' := by
    rw [hm', ← AzNat.size_toNat]
    exact Nat.lt_size.mp (by rw [AzNat.size_toNat]; omega)
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, zero_mul] at hlt; omega
    · exact h0
  have hmpow : (2 ^ ((splitOdd r).1.size - 1)) ^ a ≤ m' ^ a := Nat.pow_le_pow_left hge a
  have hmpow' : 2 ^ (a * ((splitOdd r).1.size - 1)) ≤ m' ^ a := by
    rw [mul_comm, pow_mul]; exact hmpow
  have hmr : m' ^ a ≤ r.toNat ^ a :=
    Nat.pow_le_pow_left (by rw [hdec]; exact Nat.le_mul_of_pos_right _ (by positivity)) a
  have hbig : 2 ^ (p + 4 + 2 * r.size + a.size) ≤ r.toNat ^ a :=
    (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (hmpow'.trans hmr)
  have hra2 : 2 ≤ r.toNat ^ a := by
    calc 2 ≤ 2 ^ (p + 4 + 2 * r.size + a.size) :=
          le_self_pow₀ (by norm_num) (by omega)
      _ ≤ r.toNat ^ a := hbig
  have hra1 : r.toNat ^ a - 1 ≠ 0 := by omega
  rcases lt_or_gt_of_ne (toInt_ne_zero_of_ne_zero (ne_zero_of_natPowM1Cheap_false hc))
    with hneg | hpos
  · -- `n = −a`: `−(r^a − 1) 2^(−ca) / m'^a`, not dyadic
    have hna : n.toInt = -(a : ℤ) := by rw [ha, Int.ofNat_natAbs_of_nonpos hneg.le]; ring
    have hra' : (r.toNat : ℝ) ^ a = (m' : ℝ) ^ a * (2 : ℝ) ^ ((c : ℤ) * a) := by
      rw [hdec]
      push_cast
      rw [mul_pow, ← pow_mul, ← zpow_natCast]
      rfl
    have heq : (r.toNat : ℝ) ^ n.toInt - 1
        = (-1 : ℝ) * ((r.toNat ^ a - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((c : ℤ) * a))
          / ((m' ^ a : ℕ) : ℝ) := by
      rw [hna, zpow_neg, zpow_natCast, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_pow,
        Nat.cast_one, hra', zpow_neg]
      have hm0 : (m' : ℝ) ^ a ≠ 0 := by positivity
      have h2 : (2 : ℝ) ^ ((c : ℤ) * a) ≠ 0 := zpow_ne_zero _ (by norm_num)
      field_simp
      ring
    rw [heq]
    refine not_mem_floatSet_of_div_odd_coprime p hra1 hodd.pow
      (hm'3.trans (Nat.le_self_pow (by omega) m')) ?_ _ (by norm_num)
    have hdvd : m' ^ a ∣ r.toNat ^ a :=
      pow_dvd_pow_of_dvd ⟨2 ^ c, hdec⟩ a
    have hcop : Nat.Coprime (r.toNat ^ a - 1) (r.toNat ^ a) :=
      ((Nat.coprime_self_sub_right (m := 1) (n := r.toNat ^ a) (by omega)).mpr
        (Nat.coprime_one_right _)).symm
    exact hcop.coprime_dvd_right hdvd
  · -- `n = a`
    have hna : n.toInt = (a : ℤ) := by rw [ha, Int.natAbs_of_nonneg hpos.le]
    have hcast : (r.toNat : ℝ) ^ n.toInt - 1 = ((r.toNat ^ a - 1 : ℕ) : ℝ) := by
      rw [hna, zpow_natCast, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    rw [hcast]
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · -- `r` odd: lifting the exponent bounds the power of two in `r^a − 1`
      have hrm : r.toNat = m' := by rw [hdec, hc0, pow_zero, mul_one]
      have hrodd : Odd r.toNat := hrm ▸ hodd
      have hv := padicValNat_two_pow_sub_one_le hrodd (hrm ▸ hm'3) ha1
      obtain ⟨v, A, hA, hAeq⟩ := Nat.exists_eq_two_pow_mul_odd hra1
      have hvle : v ≤ padicValNat 2 (r.toNat ^ a - 1) := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact (padicValNat_dvd_iff_le hra1).mp ⟨A, hAeq⟩
      have hsize : r.size = r.toNat.size := (AzNat.size_toNat r).symm
      have hsz' : (splitOdd r).1.size = r.size := by
        rw [← AzNat.size_toNat, ← hm', ← hrm, AzNat.size_toNat]
      rw [hsz'] at hlt
      have hAbig : 2 ^ (p + 1) ≤ A := by
        have hlt' : 2 ^ (p + 3 + 2 * r.size + a.size) < 2 ^ (p + 4 + 2 * r.size + a.size) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        have h1 : 2 ^ (p + 3 + 2 * r.size + a.size) ≤ 2 ^ v * A := by
          rw [← hAeq]; omega
        have h2 : p + 1 + v ≤ p + 3 + 2 * r.size + a.size := by rw [hsize]; omega
        have h3 : 2 ^ (p + 1) * 2 ^ v ≤ 2 ^ v * A := by
          rw [← pow_add]
          exact (Nat.pow_le_pow_right (by norm_num) h2).trans h1
        rw [mul_comm (2 ^ v) A] at h3
        exact Nat.le_of_mul_le_mul_right h3 (by positivity)
      have heq : ((r.toNat ^ a - 1 : ℕ) : ℝ) = (1 : ℝ) * A * (2 : ℝ) ^ ((v : ℕ) : ℤ) := by
        rw [hAeq, zpow_natCast]; push_cast; ring
      rw [heq]
      exact not_mem_floatSet_of_odd_mul p hA hAbig _ (by norm_num)
    · -- `r` even: `r^a − 1` is odd
      have hreven : Even r.toNat := by
        rw [hdec]
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left _
      have hodd' : Odd (r.toNat ^ a - 1) := by
        have : Even (r.toNat ^ a) := Nat.even_pow.mpr ⟨hreven, by omega⟩
        exact Nat.Even.sub_odd (by omega) this odd_one
      have hbig' : 2 ^ (p + 1) ≤ r.toNat ^ a - 1 := by
        have : 2 ^ (p + 1) < 2 ^ (p + 4 + 2 * r.size + a.size) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have heq : ((r.toNat ^ a - 1 : ℕ) : ℝ)
          = (1 : ℝ) * ((r.toNat ^ a - 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((0 : ℕ) : ℤ) := by simp
      rw [heq]
      exact not_mem_floatSet_of_odd_mul p hodd' hbig' _ (by norm_num)

/-- The non-strict bracket of `u^x − 1`. -/
theorem powBaseM1Approx_spec' {w : ℕ} (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (u : UInt64) (hu : 2 ≤ u.toNat) (hw : powBaseM1W₀ e u ≤ w) :
    ∃ lv hv' : ℝ, Rounds (powBaseM1Approx (finite s e q m hv) e u w).1 lv ∧
      Rounds (powBaseM1Approx (finite s e q m hv) e u w).2 hv' ∧
      lv ≤ (u.toNat : ℝ) ^ finiteVal s e m - 1 ∧ (u.toNat : ℝ) ^ finiteVal s e m - 1 ≤ hv' ∧
      hv' - lv ≤ powBaseM1Eps e.toInt ((baseFloat u).exponent?.getD 0).toInt
        (expM1Comp (powBaseM1Exp e)) (finiteVal s e m * Real.log u.toNat) w := by
  obtain ⟨hb1, hb2⟩ := abs_finiteVal_bounds s e hv
  have hxe1 : (2 : ℝ) ^ e.toInt ≤ 2 * |finiteVal s e m| := by
    have : (2 : ℝ) ^ e.toInt = 2 * (2 : ℝ) ^ (e.toInt - 1) := by
      rw [zpow_sub_one₀ (by norm_num)]; ring
    rw [this]; linarith
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ :=
    powBaseM1Bracket_spec (toVal_finite s e q m hv) e hb2 hxe1 u hu hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  exact ⟨lo, hi, hR1, hR2, h1, h2, h3⟩

/-- The Ziv certificate for `u^x − 1` when `u^x = r^n` exactly but `r^n − 1` is not cheap. -/
theorem powBaseM1Approx_isSome_exists_of_not_cheap (p : ℕ) [NeZero p] (mode : RoundingMode)
    (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (u : UInt64)
    (hu : 2 ≤ u.toNat) {r : AzNat} {n : AzInt}
    (hx : powBaseExact? (finite s e q m hv) (AzNat.ofNat u.toNat) = some (r, n))
    (hc : natPowM1Cheap r n p = false) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (powBaseM1Approx (finite s e q m hv) e u (w₀ * 2 ^ f)).1
      (powBaseM1Approx (finite s e q m hv) e u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hu2 : 2 ≤ (AzNat.ofNat u.toNat).toNat := by rw [AzNat.toNat_ofNat]; exact hu
  obtain ⟨hr, hval⟩ := powBaseExact?_some _ _ hu2 (toVal_finite s e q m hv) hx
  rw [AzNat.toNat_ofNat] at hval
  obtain ⟨-, -, hc2, -⟩ := maxRootBase_spec (AzNat.ofNat u.toNat) hu2
  rw [← hr] at hc2
  refine exists_isSome_of_not_mem_threshold p mode (powBaseM1Approx (finite s e q m hv) e u)
    ?_ ?_ (powBaseM1Eps e.toInt ((baseFloat u).exponent?.getD 0).toInt
      (expM1Comp (powBaseM1Exp e)) (finiteVal s e m * Real.log u.toNat))
    (tendsto_powBaseM1Eps _ _ _ _) (powBaseM1W₀ e u)
    (fun _ hw => powBaseM1Approx_spec' s e hv u hu hw) w₀ hw₀
  · rw [hval]
    exact natPow_sub_one_ne_zero hc2
      (toInt_ne_zero_of_ne_zero (ne_zero_of_natPowM1Cheap_false hc))
  · rw [hval]
    exact not_mem_floatSet_natPow_sub_one p hc2 hc

/-- The non-strict bracket of `u^q − 1`. -/
theorem powBaseM1RatApprox_spec' {w : ℕ} (q : AzRat) (h0 : q.num ≠ 0) (u : UInt64)
    (hu : 2 ≤ u.toNat) (hw : powBaseM1RatW₀ q u ≤ w) :
    ∃ lv hv : ℝ, Rounds (powBaseM1RatApprox q u w).1 lv ∧ Rounds (powBaseM1RatApprox q u w).2 hv ∧
      lv ≤ (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1 ∧
      (u.toNat : ℝ) ^ (AzRat.toRat q : ℝ) - 1 ≤ hv ∧
      hv - lv ≤ powBaseM1Eps (q.num.size : ℤ) ((baseFloat u).exponent?.getD 0).toInt
        (expM1Comp (powBaseM1Exp (pow2M1RatExp q))) ((AzRat.toRat q : ℝ) * Real.log u.toNat)
        w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := powBaseM1RatBracket_spec q h0 u hu hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  exact ⟨lo, hi, hR1, hR2, h1, h2, h3⟩

/-- The Ziv certificate for `u^q − 1` when `u^q = r^n` exactly but `r^n − 1` is not cheap. -/
theorem powBaseM1RatApprox_isSome_exists_of_not_cheap (p : ℕ) [NeZero p] (mode : RoundingMode)
    (q : AzRat) (h0 : q.num ≠ 0) (u : UInt64) (hu : 2 ≤ u.toNat) {r : AzNat} {n : AzInt}
    (hx : powBaseRatExact? q (AzNat.ofNat u.toNat) = some (r, n))
    (hc : natPowM1Cheap r n p = false) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (powBaseM1RatApprox q u (w₀ * 2 ^ f)).1
      (powBaseM1RatApprox q u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hu2 : 2 ≤ (AzNat.ofNat u.toNat).toNat := by rw [AzNat.toNat_ofNat]; exact hu
  obtain ⟨hr, hval⟩ := powBaseRatExact?_some q _ hu2 hx
  rw [AzNat.toNat_ofNat] at hval
  obtain ⟨-, -, hc2, -⟩ := maxRootBase_spec (AzNat.ofNat u.toNat) hu2
  rw [← hr] at hc2
  refine exists_isSome_of_not_mem_threshold p mode (powBaseM1RatApprox q u) ?_ ?_
    (powBaseM1Eps (q.num.size : ℤ) ((baseFloat u).exponent?.getD 0).toInt
      (expM1Comp (powBaseM1Exp (pow2M1RatExp q))) ((AzRat.toRat q : ℝ) * Real.log u.toNat))
    (tendsto_powBaseM1Eps _ _ _ _) (powBaseM1RatW₀ q u)
    (fun _ hw => powBaseM1RatApprox_spec' q h0 u hu hw) w₀ hw₀
  · rw [hval]
    exact natPow_sub_one_ne_zero hc2
      (toInt_ne_zero_of_ne_zero (ne_zero_of_natPowM1Cheap_false hc))
  · rw [hval]
    exact not_mem_floatSet_natPow_sub_one p hc2 hc

end Azurite.AzFloat
