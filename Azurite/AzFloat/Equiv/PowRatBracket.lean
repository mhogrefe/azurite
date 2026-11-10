/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowRatBracket
import Azurite.AzFloat.Equiv.PowBracket
import Azurite.AzFloat.Equiv.RatPowBracket
import Azurite.AzFloat.Equiv.RatPow
import Azurite.AzNat.Equiv.RootInt

/-!
# Equivalence: the bracket of `x^q` and the exact powers with a rational exponent

* `lnMulRatBracket_spec`: `lnMulRatBracket b eb q w` encloses `q ln b` with width at most
  `powRatEps q eb w = 2 mulLnEps eq eb w + 2^(size(|eb| + 1)) 2^(−w)`, from `lnMulBracket_spec`
  at the float `⌊q⌋_W` and the slack `powRatSlack`.
* `powRatBracket_spec`, `powRatApprox_spec`, `powRatApprox_isSome_exists`.
* `oddRootD_some/none`, `irrational_dyadic_rpow_gen` (`(m 2^t)^(N/D)` is irrational for odd `m`,
  `gcd(D, N) = 1`, `D ≥ 2`, unless `D ∣ t` and `m` is a `D`-th power), `powRatExact?_some`,
  `irrational_of_powRatExact?_none`.
-/

namespace Azurite.AzFloat

/-! ### The slack and the exponent bound -/

theorem toInt_ratExpBound (q : AzRat) :
    (ratExpBound q).toInt = (q.num.size : ℤ) + 2 - q.den.size := by
  unfold ratExpBound
  rw [AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt, AzNat.toNat_ofNat,
    AzNat.toNat_ofNat]
  push_cast
  ring

/-- `|q| < 2^(eq − 1)` for `eq = ratExpBound q`. -/
theorem abs_toRat_lt_two_zpow (q : AzRat) :
    |(AzRat.toRat q : ℝ)| < (2 : ℝ) ^ ((ratExpBound q).toInt - 1) := by
  rw [abs_coe_toRat, toInt_ratExpBound]
  have hden := den_pos_real q
  have h1 : (q.num.toNat : ℝ) < (2 : ℝ) ^ q.num.size := by
    have := Nat.lt_size_self q.num.toNat
    rw [AzNat.size_toNat] at this
    exact_mod_cast this
  have h2 : (2 : ℝ) ^ (q.den.size - 1) ≤ (q.den.toNat : ℝ) := by
    have hpos : 0 < q.den.toNat := AzRat.den_toNat_pos q
    have hsz : 0 < q.den.size := by rw [← AzNat.size_toNat]; exact Nat.size_pos.mpr hpos
    have := Nat.lt_size.mp (show q.den.size - 1 < q.den.toNat.size by
      rw [AzNat.size_toNat]; omega)
    exact_mod_cast this
  rw [div_lt_iff₀ hden]
  calc (q.num.toNat : ℝ) < (2 : ℝ) ^ q.num.size := h1
    _ = (2 : ℝ) ^ ((q.num.size : ℤ) + 2 - q.den.size - 1) * (2 : ℝ) ^ (q.den.size - 1) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
        congr 1
        have : (1 : ℤ) ≤ q.den.size := by
          have hpos : 0 < q.den.toNat := AzRat.den_toNat_pos q
          have : 0 < q.den.size := by rw [← AzNat.size_toNat]; exact Nat.size_pos.mpr hpos
          omega
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
    _ ≤ (2 : ℝ) ^ ((q.num.size : ℤ) + 2 - q.den.size - 1) * q.den.toNat :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `|e| + 1 < 2^(size(|e| + 1))`. -/
theorem abs_add_one_lt_two_pow_size (e : AzInt) :
    |(e.toInt : ℝ)| + 1 < (2 : ℝ) ^ (e.abs + 1).size := by
  have h := Nat.lt_size_self (e.abs + 1).toNat
  rw [AzNat.size_toNat, AzNat.toNat_add, AzNat.toNat_one, toNat_abs_eq_natAbs] at h
  have : ((e.toInt.natAbs + 1 : ℕ) : ℝ) < (2 : ℝ) ^ (e.abs + 1).size := by exact_mod_cast h
  push_cast at this
  rwa [Nat.cast_natAbs, Int.cast_abs] at this

theorem toVal_powRatSlack (q : AzRat) (ex : AzInt) (W : ℕ) :
    (powRatSlack q ex W).toVal
      = some (((2 : ℝ) ^ ((ratExpBound q).toInt + (ex.abs + 1).size + 1 - W) : ℝ) : EReal) := by
  unfold powRatSlack
  rw [toVal_powerOf2, AzInt.toInt_sub, AzInt.toInt_add, AzInt.toInt_add, AzNat.toInt_toAzInt,
    AzNat.toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat, AzInt.toInt_one]

/-- The width bound of `lnMulRatBracket`. -/
noncomputable def powRatEps (q : AzRat) (eb : AzInt) (w : ℕ) : ℝ :=
  2 * mulLnEps (ratExpBound q).toInt eb.toInt w + (2 : ℝ) ^ (eb.abs + 1).size * (1 / 2 : ℝ) ^ w

theorem tendsto_powRatEps (q : AzRat) (eb : AzInt) :
    Filter.Tendsto (powRatEps q eb) Filter.atTop (nhds 0) := by
  unfold powRatEps
  have h1 := (tendsto_mulLnEps (ratExpBound q).toInt eb.toInt).const_mul 2
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((2 : ℝ) ^ (eb.abs + 1).size)
  simp only [mul_zero] at h1 h2
  have := h1.add h2
  rwa [add_zero] at this

theorem powRatEps_le_one (q : AzRat) (eb : AzInt) {w : ℕ} (hw : powRatW₀ q eb ≤ w) :
    powRatEps q eb w ≤ 1 := by
  unfold powRatW₀ at hw
  have h1 := powW₀_spec (ratExpBound q) eb (show powW₀ (ratExpBound q) eb ≤ w by omega)
  have h2 : (2 : ℝ) ^ (eb.abs + 1).size * (1 / 2 : ℝ) ^ w ≤ 1 / 2 := by
    have : (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ ((eb.abs + 1).size + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc (2 : ℝ) ^ (eb.abs + 1).size * (1 / 2 : ℝ) ^ w
        ≤ (2 : ℝ) ^ (eb.abs + 1).size * (1 / 2 : ℝ) ^ ((eb.abs + 1).size + 1) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / 2 := by rw [one_div_pow, pow_succ]; field_simp
  unfold powRatEps
  linarith

/-! ### The bracket of `q ln b` -/

/-- `2^a ≤ 2^b` for `a ≤ b`. -/
theorem two_zpow_le_two_zpow {a b : ℤ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  zpow_le_zpow_right₀ (by norm_num) h

/-- `lnMulRatBracket b eb q w` encloses `q ln b` with width at most `powRatEps q eb w`
(`w ≥ 64`). -/
theorem lnMulRatBracket_spec (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (q : AzRat) (w : ℕ) (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (lnMulRatBracket (finite true eb qb mb hvb) eb q w).1.toVal = some (lo : EReal) ∧
      (lnMulRatBracket (finite true eb qb mb hvb) eb q w).2.toVal = some (hi : EReal) ∧
      lo ≤ (AzRat.toRat q : ℝ) * Real.log (finiteVal true eb mb) ∧
      (AzRat.toRat q : ℝ) * Real.log (finiteVal true eb mb) ≤ hi ∧
      hi - lo ≤ powRatEps q eb w := by
  obtain ⟨eq, heq⟩ : ∃ eq : AzInt, eq = ratExpBound q := ⟨_, rfl⟩
  obtain ⟨emax, hemax⟩ : ∃ n : ℕ, n = if eq.sign then eq.abs.toNat else 0 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = expWork eq w := ⟨_, rfl⟩
  have hWv : W = w + 16 + emax := by rw [hW, hemax]; rfl
  have hemaxM : (emax : ℤ) = max eq.toInt 0 := by rw [hemax]; exact expPos_eq_max eq
  have hemaxZ : eq.toInt ≤ (emax : ℤ) := by rw [hemaxM]; exact le_max_left _ _
  have hW64 : 64 ≤ W := by omega
  have : NeZero W := ⟨by omega⟩
  set qv := (AzRat.toRat q : ℝ) with hqv
  set L := Real.log (finiteVal true eb mb) with hL
  set Ex := (eb.abs + 1).size with hEx
  -- the float below `q`
  obtain ⟨yv, hy, hy1, hy2⟩ := ofAzRatRound_floor_abs q W
  rw [← hqv] at hy1 hy2
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hu16 : u ≤ 1 / 16 := by
    rw [hu]
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have huz : u = (2 : ℝ) ^ (-(W : ℤ)) := by
    rw [hu, one_div_pow, one_div, ← zpow_natCast, ← zpow_neg]
  have hqlt : |qv| < (2 : ℝ) ^ (eq.toInt - 1) := by rw [heq]; exact abs_toRat_lt_two_zpow q
  have h2eq : (2 : ℝ) ^ eq.toInt = 2 * (2 : ℝ) ^ (eq.toInt - 1) := by
    rw [zpow_sub_one₀ (by norm_num)]; ring
  have hyabs : |yv| ≤ |qv| + 2 * |qv| * u := by
    rw [abs_le]
    constructor <;> cases abs_cases qv <;> nlinarith [abs_nonneg qv, le_abs_self qv, neg_abs_le qv]
  have hye : |yv| < (2 : ℝ) ^ eq.toInt := by
    rw [h2eq]
    have := abs_nonneg qv
    nlinarith
  -- the bracket of `y ln b`
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnMulBracket_spec eb hvb hy eq hye w hw
  -- the slack dominates `|q − y| |ln b|`
  have hlogb := abs_log_finiteVal_le eb hvb
  rw [← hL] at hlogb
  have hEx' := abs_add_one_lt_two_pow_size eb
  rw [← hEx] at hEx'
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (2 : ℝ) ^ (eq.toInt + Ex + 1 - W) := ⟨_, rfl⟩
  have hSval : (powRatSlack q eb W).toVal = some ((S : ℝ) : EReal) := by
    rw [toVal_powRatSlack, hS, heq, hEx]
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hδ : |qv - yv| ≤ 2 * |qv| * u := by
    rw [abs_le]; constructor <;> linarith
  have hslack : |qv - yv| * |L| ≤ S := by
    have hA : |qv - yv| * |L| ≤ (2 * |qv| * u) * (|(eb.toInt : ℝ)| + 1) :=
      mul_le_mul hδ hlogb (abs_nonneg _) (by positivity)
    have hB : (2 * |qv| * u) * (|(eb.toInt : ℝ)| + 1)
        ≤ (2 * (2 : ℝ) ^ (eq.toInt - 1) * u) * (2 : ℝ) ^ Ex := by
      apply mul_le_mul _ hEx'.le (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqlt.le (by norm_num)) hu0
    have hC : (2 * (2 : ℝ) ^ (eq.toInt - 1) * u) * (2 : ℝ) ^ Ex ≤ S := by
      rw [← h2eq, huz, ← zpow_natCast (2 : ℝ) Ex, ← zpow_add₀ (by norm_num),
        ← zpow_add₀ (by norm_num), hS]
      exact two_zpow_le_two_zpow (by omega)
    exact hA.trans (hB.trans hC)
  -- the widened ends
  obtain ⟨lo', hlo', hlo'1, hlo'2⟩ := subFloor_abs hlo hSval W
  obtain ⟨hi', hhi', hhi'1, hhi'2⟩ := addCeiling_abs hhi hSval W
  rw [← hu] at hlo'2 hhi'2
  refine ⟨lo', hi', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [lnMulRatBracket]; rw [← heq, ← hW]; exact hlo'
  · simp only [lnMulRatBracket]; rw [← heq, ← hW]; exact hhi'
  · have : qv * L ≥ yv * L - |qv - yv| * |L| := by
      have := neg_abs_le ((qv - yv) * L)
      rw [abs_mul] at this
      linarith
    linarith
  · have : qv * L ≤ yv * L + |qv - yv| * |L| := by
      have := le_abs_self ((qv - yv) * L)
      rw [abs_mul] at this
      linarith
    linarith
  · -- the width: `ML + 2S + 2u (|hi + S| + |lo − S|)`, each piece against `powRatEps`
    set ML := mulLnEps eq.toInt eb.toInt w with hML
    have hML0 : 0 ≤ ML := by rw [hML]; unfold mulLnEps lnEps; positivity
    set P := (2 : ℝ) ^ eq.toInt * (2 : ℝ) ^ Ex with hP
    have hP0 : 0 ≤ P := by rw [hP]; positivity
    set X := (2 : ℝ) ^ Ex * (1 / 2 : ℝ) ^ w with hX
    have hX0 : 0 ≤ X := by rw [hX]; positivity
    have hyL : |yv * L| ≤ P := by
      rw [abs_mul, hP]
      exact (mul_le_mul hye.le hlogb (abs_nonneg _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hEx'.le (by positivity))
    have hhi_abs : |hi + S| ≤ P + ML + S := by
      have := abs_add_le hi S
      rw [abs_of_nonneg hS0] at this
      have h3 : |hi| ≤ P + ML := by
        rw [abs_le]; constructor <;> cases abs_le.mp hyL <;> linarith
      linarith
    have hlo_abs : |lo - S| ≤ P + ML + S := by
      have := abs_sub lo S
      rw [abs_of_nonneg hS0] at this
      have h3 : |lo| ≤ P + ML := by
        rw [abs_le]; constructor <;> cases abs_le.mp hyL <;> linarith
      linarith
    have hb1 : |hi + S| * u ≤ (P + ML + S) * u := mul_le_mul_of_nonneg_right hhi_abs hu0
    have hb2 : |lo - S| * u ≤ (P + ML + S) * u := mul_le_mul_of_nonneg_right hlo_abs hu0
    have hPu : P * u ≤ X / 65536 := by
      rw [hP, hX, huz, ← zpow_natCast (2 : ℝ) Ex, mul_right_comm, ← zpow_add₀ (by norm_num)]
      have h1' : (2 : ℝ) ^ (eq.toInt + -(W : ℤ)) ≤ (2 : ℝ) ^ (-((w : ℤ) + 16)) :=
        two_zpow_le_two_zpow (by omega)
      have h2' : (2 : ℝ) ^ (-((w : ℤ) + 16)) = (1 / 2 : ℝ) ^ w / 65536 := by
        rw [zpow_neg, zpow_add₀ (by norm_num), zpow_natCast, one_div_pow, one_div]
        norm_num
        ring
      calc (2 : ℝ) ^ (eq.toInt + -(W : ℤ)) * (2 : ℝ) ^ (Ex : ℤ)
          ≤ (1 / 2 : ℝ) ^ w / 65536 * (2 : ℝ) ^ (Ex : ℤ) := by
            rw [← h2']
            exact mul_le_mul_of_nonneg_right h1' (by positivity)
        _ = (2 : ℝ) ^ (Ex : ℤ) * (1 / 2 : ℝ) ^ w / 65536 := by ring
        _ = _ := by rw [zpow_natCast]
    have hSX : S ≤ X / 32768 := by
      rw [hS, hX]
      have h1' : (2 : ℝ) ^ (eq.toInt + Ex + 1 - W) ≤ (2 : ℝ) ^ ((Ex : ℤ) - ((w : ℤ) + 15)) :=
        two_zpow_le_two_zpow (by omega)
      have h2' : (2 : ℝ) ^ ((Ex : ℤ) - ((w : ℤ) + 15))
          = (2 : ℝ) ^ Ex * (1 / 2 : ℝ) ^ w / 32768 := by
        rw [zpow_sub₀ (by norm_num), zpow_add₀ (by norm_num), zpow_natCast, zpow_natCast,
          one_div_pow, one_div]
        norm_num
        ring
      rw [← h2']
      exact h1'
    have hMLu : ML * u ≤ ML / 16 := by nlinarith
    have hSu : S * u ≤ S / 16 := by nlinarith
    have e : (P + ML + S) * u = P * u + ML * u + S * u := by ring
    rw [e] at hb1 hb2
    unfold powRatEps
    rw [← heq, ← hML, ← hEx, ← hX]
    linarith

/-- `powRatBracket b eb q w` encloses `b^q` for `w ≥ powRatW₀ q eb`. -/
theorem powRatBracket_spec (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (q : AzRat) {w : ℕ} (hw : powRatW₀ q eb ≤ w) :
    ∃ lo hi : ℝ, (powRatBracket (finite true eb qb mb hvb) eb q w).1.toVal = some (lo : EReal) ∧
      (powRatBracket (finite true eb qb mb hvb) eb q w).2.toVal = some (hi : EReal) ∧
      lo ≤ finiteVal true eb mb ^ (AzRat.toRat q : ℝ) ∧
      finiteVal true eb mb ^ (AzRat.toRat q : ℝ) ≤ hi ∧
      hi - lo ≤ expOfBracketEps ((AzRat.toRat q : ℝ) * Real.log (finiteVal true eb mb))
        (powRatEps q eb w) w := by
  have hw64 : 64 ≤ w := by unfold powRatW₀ powW₀ at hw; omega
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnMulRatBracket_spec eb hvb q w hw64
  have hw1 : hi - lo ≤ 1 := hwid.trans (powRatEps_le_one q eb hw)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw64
  rw [rpow_eq_exp_mul_log (finiteVal_true_pos eb hvb)]
  refine ⟨a, b, ha, hb, ha1, hb1, hab.trans ?_⟩
  unfold expOfBracketEps
  have := Real.exp_pos ((AzRat.toRat q : ℝ) * Real.log (finiteVal true eb mb))
  nlinarith

/-- The width bound of the `b^q` bracket tends to zero. -/
theorem tendsto_powRatBracketEps (q : AzRat) (eb : AzInt) (v : ℝ) :
    Filter.Tendsto (fun w => expOfBracketEps v (powRatEps q eb w) w) Filter.atTop (nhds 0) := by
  unfold expOfBracketEps
  have h1 := tendsto_expEps v
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 := (((tendsto_powRatEps q eb).const_mul 24).add (hu.div_const 4)).const_mul (Real.exp v)
  simp only [mul_zero, zero_div, add_zero] at h2
  have := h1.add h2
  rwa [add_zero] at this

/-- `powRatApprox neg b eb q w` brackets `± b^q`. -/
theorem powRatApprox_spec (neg : Bool) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (q : AzRat) {w : ℕ} (hw : powRatW₀ q eb ≤ w) :
    ∃ lv hv : ℝ, Rounds (powRatApprox neg (finite true eb qb mb hvb) eb q w).1 lv ∧
      Rounds (powRatApprox neg (finite true eb qb mb hvb) eb q w).2 hv ∧
      lv ≤ powSign neg * finiteVal true eb mb ^ (AzRat.toRat q : ℝ) ∧
      powSign neg * finiteVal true eb mb ^ (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ expOfBracketEps ((AzRat.toRat q : ℝ) * Real.log (finiteVal true eb mb))
        (powRatEps q eb w) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := powRatBracket_spec eb hvb q hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [powRatApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, powSign, one_mul]
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | true =>
    simp only [↓reduceIte, powSign, neg_one_mul]
    have hnlo : (-(powRatBracket (finite true eb qb mb hvb) eb q w).2).toVal
        = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(powRatBracket (finite true eb qb mb hvb) eb q w).1).toVal
        = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- The Ziv certificate for `± b^q`, for a result that is not a rounding boundary. -/
theorem powRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb) (q : AzRat)
    (hvB : ((powSign neg * finiteVal true eb mb ^ (AzRat.toRat q : ℝ) : ℝ) : EReal)
      ∉ floatSet (p + 1)) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (powRatApprox neg (finite true eb qb mb hvb) eb q (w₀ * 2 ^ f)).1
      (powRatApprox neg (finite true eb qb mb hvb) eb q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_not_mem_threshold p mode (powRatApprox neg (finite true eb qb mb hvb) eb q)
    (mul_ne_zero (powSign_ne_zero neg)
      (Real.rpow_pos_of_pos (finiteVal_true_pos eb hvb) _).ne')
    hvB (fun w => expOfBracketEps ((AzRat.toRat q : ℝ) * Real.log (finiteVal true eb mb))
      (powRatEps q eb w) w)
    (tendsto_powRatBracketEps q eb _) (powRatW₀ q eb)
    (fun _ hw => powRatApprox_spec neg eb hvb q hw) w₀ hw₀

/-! ### The `D`-th root of an odd natural -/

theorem oddRootD_some {m D : AzNat} {u : AzNat} (h : oddRootD m D = some u) :
    m.toNat = u.toNat ^ D.toNat := by
  unfold oddRootD at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  · rw [Option.some.injEq] at h
    rw [h1, ← h, AzNat.toNat_ofNat, one_pow]
  · rw [Option.some.injEq] at h
    have := congrArg AzNat.toNat h3
    rw [AzNat.toNat_pow] at this
    rw [← h]
    exact this.symm

theorem oddRootD_none {m D : AzNat} (hm : Odd m.toNat) (hD : 2 ≤ D.toNat)
    (h : oddRootD m D = none) : ¬ ∃ c : ℕ, m.toNat = c ^ D.toNat := by
  unfold oddRootD at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  · rintro ⟨c, hc⟩
    have hm1 : m.toNat ≠ 1 := fun h' => h1 (AzNat.toNat_injective (by rw [h', AzNat.toNat_ofNat]))
    have hm0 : m.toNat ≠ 0 := by rintro h0; rw [h0] at hm; simp at hm
    have hc2 : 2 ≤ c := by
      rcases Nat.lt_or_ge c 2 with hc' | hc'
      · interval_cases c
        · rw [zero_pow (by omega)] at hc; exact absurd hc hm0
        · rw [one_pow] at hc; exact absurd hc hm1
      · exact hc'
    have hsize : m.toNat < 2 ^ m.size := by rw [← AzNat.size_toNat]; exact Nat.lt_size_self _
    rw [AzNat.le_iff_toNat_le, AzNat.toNat_ofNat] at h2
    have hJ : 2 ^ m.size ≤ 2 ^ D.toNat := Nat.pow_le_pow_right (by norm_num) h2
    have hc : 2 ^ D.toNat ≤ c ^ D.toNat := Nat.pow_le_pow_left hc2 _
    omega
  · rintro ⟨c, hc⟩
    apply h3
    apply AzNat.toNat_injective
    rw [AzNat.toNat_pow, AzNat.toNat_rootInt]
    exact (AzNat.rootIntNat_pow_eq_iff m.toNat D.toNat (by omega)).mpr ⟨c, hc.symm⟩

/-! ### Irrationality for a general denominator -/

/-- **The dyadic case with a general denominator**: for an odd `m ≥ 1`, `(m 2^t)^(N/D)` with
`gcd(D, N) = 1`, `N ≠ 0` and `D ≥ 2` is irrational unless `D ∣ t` and `m` is a `D`-th power. -/
theorem irrational_dyadic_rpow_gen {m : ℕ} (hm : Odd m) (t : ℤ) {N : ℤ} (hN0 : N ≠ 0) {D : ℕ}
    (hD : 2 ≤ D) (hcop : Nat.Coprime D N.natAbs)
    (h : ¬ ((D : ℤ) ∣ t ∧ ∃ u : ℕ, m = u ^ D)) :
    Irrational (((m : ℝ) * (2 : ℝ) ^ t) ^ ((N : ℝ) / D)) := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hm)
  have hbase : (0 : ℝ) < (m : ℝ) * (2 : ℝ) ^ t := by positivity
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hmain : ∀ N' : ℕ, N' ≠ 0 → Nat.Coprime D N' →
      Irrational (((m : ℝ) * (2 : ℝ) ^ t) ^ ((N' : ℝ) / D)) := by
    intro N' hN' hcop'
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 ≤ t + D * k := by
      refine ⟨t.natAbs, ?_⟩
      have h1 : -t ≤ (t.natAbs : ℤ) := by omega
      have h2 : (t.natAbs : ℤ) ≤ D * t.natAbs :=
        le_mul_of_one_le_left (by positivity) (by exact_mod_cast (show 1 ≤ D by omega))
      linarith
    obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = t + D * k := ⟨(t + D * k).toNat, Int.toNat_of_nonneg hk⟩
    set M : ℕ := m * 2 ^ e with hM
    have hMpos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsplit : (m : ℝ) * (2 : ℝ) ^ t = (M : ℝ) * (2 : ℝ) ^ (-((D : ℤ) * k)) := by
      rw [hM]
      push_cast
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num), he]
      congr 2
      ring
    have hexp : ((2 : ℝ) ^ (-((D : ℤ) * k))) ^ ((N' : ℝ) / D)
        = ((2 : ℝ) ^ (-((k : ℤ) * N')) : ℝ) := by
      rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast]
      congr 1
      push_cast
      field_simp
    obtain ⟨qq, hqq, hqq0⟩ : ∃ qq : ℚ, (qq : ℝ) = (2 : ℝ) ^ (-((k : ℤ) * N')) ∧ qq ≠ 0 :=
      ⟨(2 : ℚ) ^ (-((k : ℤ) * N')), by push_cast; rfl, zpow_ne_zero _ (by norm_num)⟩
    rw [hsplit, Real.mul_rpow (by positivity) (by positivity), hexp, ← hqq]
    refine Irrational.mul_ratCast ?_ hqq0
    have hcore : Irrational ((M : ℝ) ^ ((N' : ℝ) / ((D : ℕ) : ℝ))) := by
      refine irrational_natCast_rpow_div_of_not_pow hMpos hD hcop' ?_
      rintro ⟨c, hc⟩
      apply h
      have hc0 : c ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hc; omega
      obtain ⟨i, c', hc', hci⟩ := Nat.exists_eq_two_pow_mul_odd hc0
      have heq : m * 2 ^ e = c' ^ D * 2 ^ (i * D) := by
        rw [← hM, hc, hci, mul_pow, ← pow_mul]
        ring
      obtain ⟨hm', he'⟩ := odd_mul_two_pow_inj hm (hc'.pow) heq
      refine ⟨?_, c', hm'⟩
      have : (e : ℤ) = (i : ℤ) * D := by exact_mod_cast he'
      rw [he] at this
      exact ⟨(i : ℤ) - k, by linarith⟩
    exact hcore
  rcases le_or_gt 0 N with hN0' | hN0'
  · obtain ⟨N', hN'⟩ : ∃ N' : ℕ, (N' : ℤ) = N := ⟨N.toNat, Int.toNat_of_nonneg hN0'⟩
    have hcop' : Nat.Coprime D N' := by rwa [← Int.natAbs_natCast N', hN']
    have := hmain N' (by rintro rfl; simp at hN'; exact hN0 hN'.symm) hcop'
    rwa [show ((N : ℤ) : ℝ) = (N' : ℝ) by rw [← hN']; push_cast; rfl]
  · obtain ⟨N', hN'⟩ : ∃ N' : ℕ, (N' : ℤ) = -N := ⟨(-N).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hcop' : Nat.Coprime D N' := by
      rwa [← Int.natAbs_natCast N', hN', Int.natAbs_neg]
    have := hmain N' (by rintro rfl; simp at hN'; exact hN0 (by omega)) hcop'
    have e : -(((N : ℤ) : ℝ)) = (N' : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hN'
      simp only [Int.cast_natCast, Int.cast_neg] at this
      exact this.symm
    rw [← irrational_inv_iff, ← Real.rpow_neg hbase.le, ← neg_div, e]
    exact this

/-! ### The exact powers -/

/-- `mkNorm s n ≠ 0` for `n ≠ 0`. -/
theorem mkNorm_ne_zero {s : Bool} {n : AzNat} (hn : n ≠ 0) : AzInt.mkNorm s n ≠ 0 := by
  intro h
  have hn' : n.toNat ≠ 0 := fun h0 => hn (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero]))
  have := congrArg AzInt.toInt h
  rw [AzInt.toInt_zero] at this
  cases s with
  | true => rw [AzInt.toInt_mkNorm_true] at this; exact hn' (by exact_mod_cast this)
  | false =>
    rw [AzInt.toInt_mkNorm_false _ hn] at this
    exact hn' (by exact_mod_cast (neg_eq_zero.mp this))

/-- The value of `mkNorm q.sign q.num` is `q · den`: `q = (mkNorm q.sign q.num).toInt / den`. -/
theorem coe_toRat_eq_mkNorm_div (q : AzRat) :
    (AzRat.toRat q : ℝ) = ((AzInt.mkNorm q.sign q.num).toInt : ℝ) / q.den.toNat := by
  rw [AzRat.toRat_cast_eq]
  by_cases h0 : q.num = 0
  · rw [h0, AzNat.toNat_zero]
    cases q.sign <;> simp [AzInt.mkNorm, AzInt.toInt, AzNat.toNat_zero]
  · cases hs : q.sign
    · rw [AzInt.toInt_mkNorm_false _ h0]; push_cast; rfl
    · rw [AzInt.toInt_mkNorm_true]; push_cast; rfl

/-- `powRatExact? = some (z, N)`: `z` is a positive float with `x^q = z^N`, `N ≠ 0`. -/
theorem powRatExact?_some (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx) (q : AzRat)
    (h0 : q.num ≠ 0) {z : AzFloat} {N : AzInt} (h : powRatExact? ex mx q = some (z, N)) :
    ∃ zv : ℝ, z.toVal = some (zv : EReal) ∧ 0 < zv ∧
      finiteVal true ex mx ^ (AzRat.toRat q : ℝ) = zv ^ N.toInt ∧ N.toInt ≠ 0 := by
  have hxv := finiteVal_true_eq_oddShift ex hvx
  have hmx0 : mx ≠ 0 := ne_zero_of_finiteValid 0 hvx
  obtain ⟨-, hmodd⟩ := splitOdd_spec mx hmx0
  obtain ⟨t, ht⟩ : ∃ t : AzInt,
      t = ex - (AzNat.ofNat mx.size).toAzInt + (AzNat.ofNat (splitOdd mx).2).toAzInt := ⟨_, rfl⟩
  have htI : t.toInt = ex.toInt - mx.size + (splitOdd mx).2 := by rw [ht, toInt_powExact_t]
  have hD : (q.den.toAzInt).toInt = (q.den.toNat : ℤ) := AzNat.toInt_toAzInt _
  have hDpos : 0 < q.den.toNat := AzRat.den_toNat_pos q
  unfold powRatExact? at h
  simp only [] at h
  rw [← ht] at h
  split_ifs at h with hdiv
  cases hroot : oddRootD (splitOdd mx).1 q.den with
  | none => rw [hroot] at h; cases h
  | some u =>
    rw [hroot] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hz, hN⟩ := h
    have hu := oddRootD_some hroot
    have hu0 : u ≠ 0 := by
      intro h0'
      rw [h0', AzNat.toNat_zero, zero_pow (by omega)] at hu
      rw [hu] at hmodd
      simp at hmodd
    have hupos : (0 : ℝ) < u.toNat := by
      exact_mod_cast Nat.pos_of_ne_zero
        (fun h0' => hu0 (AzNat.toNat_injective (by rw [h0', AzNat.toNat_zero])))
    -- `D ∣ t`
    have hdvd : (q.den.toNat : ℤ) ∣ t.toInt := by
      have := congrArg AzInt.toInt hdiv
      rw [AzInt.toInt_emod, hD, AzInt.toInt_zero] at this
      exact Int.dvd_of_emod_eq_zero this
    obtain ⟨t', ht'⟩ := hdvd
    have htdiv : (t.ediv q.den.toAzInt).toInt = t' := by
      rw [AzInt.toInt_ediv, hD, ht', Int.mul_ediv_cancel_left _ (by exact_mod_cast hDpos.ne')]
    have hzv : z.toVal = some (((u.toNat : ℝ) * (2 : ℝ) ^ t' : ℝ) : EReal) := by
      rw [← hz, toVal_mkFinite _ _ _ _ hu0]
      congr 2
      show (1 : ℝ) * (u.toNat : ℝ) * (2 : ℝ) ^ ((_ : AzInt).toInt - u.size) = _
      rw [one_mul, AzInt.toInt_add, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, htdiv]
      congr 2
      ring
    refine ⟨(u.toNat : ℝ) * (2 : ℝ) ^ t', hzv, by positivity, ?_, ?_⟩
    · have hx : finiteVal true ex mx = ((u.toNat : ℝ) * (2 : ℝ) ^ t') ^ q.den.toNat := by
        rw [hxv, ← htI, ht', hu, mul_pow]
        push_cast
        congr 1
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        ring
      rw [hx, coe_toRat_eq_mkNorm_div, ← hN, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        mul_div_cancel₀ _ (by exact_mod_cast hDpos.ne'), Real.rpow_intCast]
    · rw [← hN]
      exact toInt_ne_zero_of_ne_zero (mkNorm_ne_zero h0)

/-- `powRatExact? = none` for a positive `x` and `q` with `den ≥ 2`: `x^q` is irrational. -/
theorem irrational_of_powRatExact?_none (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx)
    (q : AzRat) (h0 : q.num ≠ 0) (hd : q.den ≠ 1) (h : powRatExact? ex mx q = none) :
    Irrational (finiteVal true ex mx ^ (AzRat.toRat q : ℝ)) := by
  have hxv := finiteVal_true_eq_oddShift ex hvx
  have hmx0 : mx ≠ 0 := ne_zero_of_finiteValid 0 hvx
  obtain ⟨-, hmodd⟩ := splitOdd_spec mx hmx0
  obtain ⟨t, ht⟩ : ∃ t : AzInt,
      t = ex - (AzNat.ofNat mx.size).toAzInt + (AzNat.ofNat (splitOdd mx).2).toAzInt := ⟨_, rfl⟩
  have htI : t.toInt = ex.toInt - mx.size + (splitOdd mx).2 := by rw [ht, toInt_powExact_t]
  have hD : (q.den.toAzInt).toInt = (q.den.toNat : ℤ) := AzNat.toInt_toAzInt _
  have hDpos : 0 < q.den.toNat := AzRat.den_toNat_pos q
  have hD2 : 2 ≤ q.den.toNat := by
    have : q.den.toNat ≠ 1 := fun h1 => hd (AzNat.toNat_injective (by rw [h1, AzNat.toNat_one]))
    omega
  have hcop : Nat.Coprime q.den.toNat (AzInt.mkNorm q.sign q.num).toInt.natAbs := by
    have hc := (AzNat.coprime_iff _ _).mp q.reduced
    have : (AzInt.mkNorm q.sign q.num).toInt.natAbs = q.num.toNat := by
      cases q.sign
      · rw [AzInt.toInt_mkNorm_false _ h0, Int.natAbs_neg, Int.natAbs_natCast]
      · rw [AzInt.toInt_mkNorm_true, Int.natAbs_natCast]
    rw [this]
    exact hc.symm
  rw [hxv, ← htI, coe_toRat_eq_mkNorm_div]
  refine irrational_dyadic_rpow_gen hmodd t.toInt (toInt_ne_zero_of_ne_zero (mkNorm_ne_zero h0))
    hD2 hcop ?_
  rintro ⟨hdvd, u, hu⟩
  unfold powRatExact? at h
  simp only [] at h
  rw [← ht] at h
  split_ifs at h with hdiv
  · cases hroot : oddRootD (splitOdd mx).1 q.den with
    | none => exact oddRootD_none hmodd hD2 hroot ⟨u, hu⟩
    | some u' => rw [hroot] at h; cases h
  · apply hdiv
    have hz : (t.emod q.den.toAzInt).toInt = 0 := by
      rw [AzInt.toInt_emod, hD]; exact Int.emod_eq_zero_of_dvd hdvd
    have h00 : AzInt.ofInt 0 = 0 := by
      have := AzInt.ofInt_toInt (0 : AzInt)
      rwa [AzInt.toInt_zero] at this
    rw [← AzInt.ofInt_toInt (t.emod q.den.toAzInt), hz, h00]

end Azurite.AzFloat
