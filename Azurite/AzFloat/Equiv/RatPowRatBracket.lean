/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RatPowRatBracket
import Azurite.AzFloat.Equiv.PowRatBracket

/-!
# Equivalence: the bracket of `q^r` and the exact rational powers with a rational exponent

* `lnRatMulRatBracket_spec`: `lnRatMulRatBracket q r w` encloses `r ln q` with width at most
  `ratPowRatEps r q w = 2 mulLnEps er (ratPowE q) w + 2^(size(size num_q + size den_q)) 2^(−w)`.
* `ratPowRatBracket_spec`, `ratPowRatApprox_spec`, `ratPowRatApprox_isSome_exists`.
* `natRootD?_some/none`, `irrational_div_rpow_of_not_pow_gen` (`(a/b)^(N/D)` is irrational for
  coprime `a`, `b` not both `D`-th powers, `gcd(D, N) = 1`), `ratPowRatExact?_some`,
  `irrational_of_ratPowRatExact?_none`.
-/

namespace Azurite.AzFloat

theorem toVal_ratPowRatSlack (r q : AzRat) (W : ℕ) :
    (ratPowRatSlack r q W).toVal
      = some (((2 : ℝ) ^ ((ratExpBound r).toInt + (q.num.size + q.den.size).size + 1 - W) : ℝ)
        : EReal) := by
  unfold ratPowRatSlack
  rw [toVal_powerOf2, AzInt.toInt_sub, AzInt.toInt_add, AzInt.toInt_add, AzNat.toInt_toAzInt,
    AzNat.toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat, AzInt.toInt_one]

/-- The width bound of `lnRatMulRatBracket`. -/
noncomputable def ratPowRatEps (r q : AzRat) (w : ℕ) : ℝ :=
  2 * mulLnEps (ratExpBound r).toInt (ratPowE q : ℤ) w
    + (2 : ℝ) ^ (q.num.size + q.den.size).size * (1 / 2 : ℝ) ^ w

theorem tendsto_ratPowRatEps (r q : AzRat) :
    Filter.Tendsto (ratPowRatEps r q) Filter.atTop (nhds 0) := by
  unfold ratPowRatEps
  have h1 := (tendsto_mulLnEps (ratExpBound r).toInt (ratPowE q : ℤ)).const_mul 2
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((2 : ℝ) ^ (q.num.size + q.den.size).size)
  simp only [mul_zero] at h1 h2
  have := h1.add h2
  rwa [add_zero] at this

theorem ratPowRatEps_le_one (r q : AzRat) {w : ℕ} (hw : ratPowRatW₀ r q ≤ w) :
    ratPowRatEps r q w ≤ 1 := by
  unfold ratPowRatW₀ at hw
  have hwZ : 136 + max (ratExpBound r).toInt 0 + |(ratPowE q : ℤ)| ≤ (w : ℤ) := by
    rw [← ratPowW₀_eq]; exact_mod_cast (show ratPowW₀ (ratExpBound r) q ≤ w by omega)
  have h1 := mulLnEps_le_inv256 _ _ _ hwZ
  set Ex := (q.num.size + q.den.size).size with hEx
  have h2 : (2 : ℝ) ^ Ex * (1 / 2 : ℝ) ^ w ≤ 1 / 2 := by
    have : (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ (Ex + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc (2 : ℝ) ^ Ex * (1 / 2 : ℝ) ^ w ≤ (2 : ℝ) ^ Ex * (1 / 2 : ℝ) ^ (Ex + 1) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / 2 := by rw [one_div_pow, pow_succ]; field_simp
  unfold ratPowRatEps
  rw [← hEx]
  linarith

/-- `lnRatMulRatBracket q r w` encloses `r ln q` for a positive `q`, with width at most
`ratPowRatEps r q w` (`w ≥ 64`). -/
theorem lnRatMulRatBracket_spec (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) (r : AzRat)
    (w : ℕ) (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (lnRatMulRatBracket q r w).1.toVal = some (lo : EReal) ∧
      (lnRatMulRatBracket q r w).2.toVal = some (hi : EReal) ∧
      lo ≤ (AzRat.toRat r : ℝ) * Real.log (AzRat.toRat q : ℝ) ∧
      (AzRat.toRat r : ℝ) * Real.log (AzRat.toRat q : ℝ) ≤ hi ∧
      hi - lo ≤ ratPowRatEps r q w := by
  obtain ⟨er, her⟩ : ∃ er : AzInt, er = ratExpBound r := ⟨_, rfl⟩
  obtain ⟨emax, hemax⟩ : ∃ n : ℕ, n = if er.sign then er.abs.toNat else 0 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = expWork er w := ⟨_, rfl⟩
  have hWv : W = w + 16 + emax := by rw [hW, hemax]; rfl
  have hemaxM : (emax : ℤ) = max er.toInt 0 := by rw [hemax]; exact expPos_eq_max er
  have hemaxZ : er.toInt ≤ (emax : ℤ) := by rw [hemaxM]; exact le_max_left _ _
  have hW64 : 64 ≤ W := by omega
  have : NeZero W := ⟨by omega⟩
  set rv := (AzRat.toRat r : ℝ) with hrv
  set L := Real.log (AzRat.toRat q : ℝ) with hL
  set Lb := q.num.size + q.den.size with hLb
  set Ex := Lb.size with hEx
  -- the float below `r`
  obtain ⟨yv, hy, hy1, hy2⟩ := ofAzRatRound_floor_abs r W
  rw [← hrv] at hy1 hy2
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  have hu16 : u ≤ 1 / 16 := by
    rw [hu]
    calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have huz : u = (2 : ℝ) ^ (-(W : ℤ)) := by
    rw [hu, one_div_pow, one_div, ← zpow_natCast, ← zpow_neg]
  have hrlt : |rv| < (2 : ℝ) ^ (er.toInt - 1) := by rw [her]; exact abs_toRat_lt_two_zpow r
  have h2er : (2 : ℝ) ^ er.toInt = 2 * (2 : ℝ) ^ (er.toInt - 1) := by
    rw [zpow_sub_one₀ (by norm_num)]; ring
  have hyabs : |yv| ≤ |rv| + 2 * |rv| * u := by
    rw [abs_le]
    constructor <;> cases abs_cases rv <;> nlinarith [abs_nonneg rv, le_abs_self rv, neg_abs_le rv]
  have hye : |yv| < (2 : ℝ) ^ er.toInt := by
    rw [h2er]
    have := abs_nonneg rv
    nlinarith
  -- the bracket of `y ln q`
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnRatMulBracket_spec q hs h0 hy er hye w hw
  -- `|ln q| ≤ Lb < 2^Ex`
  have hnum1 : 1 ≤ q.num.toNat :=
    Nat.one_le_iff_ne_zero.mpr (fun h => h0 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero])))
  have hden1 : 1 ≤ q.den.toNat := AzRat.den_toNat_pos q
  have hlogb : |L| ≤ (Lb : ℝ) := by
    rw [hL, coe_toRat_eq_div_pos q hs, hLb]
    have := abs_log_div_le hnum1 hden1
    rw [AzNat.size_toNat, AzNat.size_toNat] at this
    exact_mod_cast this
  have hEx' : (Lb : ℝ) < (2 : ℝ) ^ Ex := by rw [hEx]; exact_mod_cast Nat.lt_size_self Lb
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (2 : ℝ) ^ (er.toInt + Ex + 1 - W) := ⟨_, rfl⟩
  have hSval : (ratPowRatSlack r q W).toVal = some ((S : ℝ) : EReal) := by
    rw [toVal_ratPowRatSlack, hS, her, hEx, hLb]
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hδ : |rv - yv| ≤ 2 * |rv| * u := by
    rw [abs_le]; constructor <;> linarith
  have hslack : |rv - yv| * |L| ≤ S := by
    have hA : |rv - yv| * |L| ≤ (2 * |rv| * u) * (Lb : ℝ) :=
      mul_le_mul hδ hlogb (abs_nonneg _) (by positivity)
    have hB : (2 * |rv| * u) * (Lb : ℝ) ≤ (2 * (2 : ℝ) ^ (er.toInt - 1) * u) * (2 : ℝ) ^ Ex := by
      apply mul_le_mul _ hEx'.le (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrlt.le (by norm_num)) hu0
    have hC : (2 * (2 : ℝ) ^ (er.toInt - 1) * u) * (2 : ℝ) ^ Ex ≤ S := by
      rw [← h2er, huz, ← zpow_natCast (2 : ℝ) Ex, ← zpow_add₀ (by norm_num),
        ← zpow_add₀ (by norm_num), hS]
      exact two_zpow_le_two_zpow (by omega)
    exact hA.trans (hB.trans hC)
  -- the widened ends
  obtain ⟨lo', hlo', hlo'1, hlo'2⟩ := subFloor_abs hlo hSval W
  obtain ⟨hi', hhi', hhi'1, hhi'2⟩ := addCeiling_abs hhi hSval W
  rw [← hu] at hlo'2 hhi'2
  refine ⟨lo', hi', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [lnRatMulRatBracket]; rw [← her, ← hW]; exact hlo'
  · simp only [lnRatMulRatBracket]; rw [← her, ← hW]; exact hhi'
  · have : rv * L ≥ yv * L - |rv - yv| * |L| := by
      have := neg_abs_le ((rv - yv) * L)
      rw [abs_mul] at this
      linarith
    linarith
  · have : rv * L ≤ yv * L + |rv - yv| * |L| := by
      have := le_abs_self ((rv - yv) * L)
      rw [abs_mul] at this
      linarith
    linarith
  · set ML := mulLnEps er.toInt (ratPowE q : ℤ) w with hML
    have hML0 : 0 ≤ ML := by rw [hML]; unfold mulLnEps lnEps; positivity
    set P := (2 : ℝ) ^ er.toInt * (2 : ℝ) ^ Ex with hP
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
      have h1' : (2 : ℝ) ^ (er.toInt + -(W : ℤ)) ≤ (2 : ℝ) ^ (-((w : ℤ) + 16)) :=
        two_zpow_le_two_zpow (by omega)
      have h2' : (2 : ℝ) ^ (-((w : ℤ) + 16)) = (1 / 2 : ℝ) ^ w / 65536 := by
        rw [zpow_neg, zpow_add₀ (by norm_num), zpow_natCast, one_div_pow, one_div]
        norm_num
        ring
      calc (2 : ℝ) ^ (er.toInt + -(W : ℤ)) * (2 : ℝ) ^ (Ex : ℤ)
          ≤ (1 / 2 : ℝ) ^ w / 65536 * (2 : ℝ) ^ (Ex : ℤ) := by
            rw [← h2']
            exact mul_le_mul_of_nonneg_right h1' (by positivity)
        _ = (2 : ℝ) ^ (Ex : ℤ) * (1 / 2 : ℝ) ^ w / 65536 := by ring
        _ = _ := by rw [zpow_natCast]
    have hSX : S ≤ X / 32768 := by
      rw [hS, hX]
      have h1' : (2 : ℝ) ^ (er.toInt + Ex + 1 - W) ≤ (2 : ℝ) ^ ((Ex : ℤ) - ((w : ℤ) + 15)) :=
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
    unfold ratPowRatEps
    rw [← her, ← hML, ← hLb, ← hEx, ← hX]
    linarith

/-- `ratPowRatBracket q r w` encloses `q^r` for `w ≥ ratPowRatW₀ r q`. -/
theorem ratPowRatBracket_spec (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) (r : AzRat)
    {w : ℕ} (hw : ratPowRatW₀ r q ≤ w) :
    ∃ lo hi : ℝ, (ratPowRatBracket q r w).1.toVal = some (lo : EReal) ∧
      (ratPowRatBracket q r w).2.toVal = some (hi : EReal) ∧
      lo ≤ (AzRat.toRat q : ℝ) ^ (AzRat.toRat r : ℝ) ∧
      (AzRat.toRat q : ℝ) ^ (AzRat.toRat r : ℝ) ≤ hi ∧
      hi - lo ≤ expOfBracketEps ((AzRat.toRat r : ℝ) * Real.log (AzRat.toRat q : ℝ))
        (ratPowRatEps r q w) w := by
  have hw64 : 64 ≤ w := by unfold ratPowRatW₀ ratPowW₀ at hw; omega
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnRatMulRatBracket_spec q hs h0 r w hw64
  have hw1 : hi - lo ≤ 1 := hwid.trans (ratPowRatEps_le_one r q hw)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw64
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast toRat_pos_of_sign q hs h0
  rw [rpow_eq_exp_mul_log hqv0]
  refine ⟨a, b, ha, hb, ha1, hb1, hab.trans ?_⟩
  unfold expOfBracketEps
  have := Real.exp_pos ((AzRat.toRat r : ℝ) * Real.log (AzRat.toRat q : ℝ))
  nlinarith

theorem tendsto_ratPowRatBracketEps (r q : AzRat) (v : ℝ) :
    Filter.Tendsto (fun w => expOfBracketEps v (ratPowRatEps r q w) w) Filter.atTop (nhds 0) := by
  unfold expOfBracketEps
  have h1 := tendsto_expEps v
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 := (((tendsto_ratPowRatEps r q).const_mul 24).add (hu.div_const 4)).const_mul
    (Real.exp v)
  simp only [mul_zero, zero_div, add_zero] at h2
  have := h1.add h2
  rwa [add_zero] at this

/-- `ratPowRatApprox neg q r w` brackets `± q^r`. -/
theorem ratPowRatApprox_spec (neg : Bool) (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0)
    (r : AzRat) {w : ℕ} (hw : ratPowRatW₀ r q ≤ w) :
    ∃ lv hv : ℝ, Rounds (ratPowRatApprox neg q r w).1 lv ∧
      Rounds (ratPowRatApprox neg q r w).2 hv ∧
      lv ≤ powSign neg * (AzRat.toRat q : ℝ) ^ (AzRat.toRat r : ℝ) ∧
      powSign neg * (AzRat.toRat q : ℝ) ^ (AzRat.toRat r : ℝ) ≤ hv ∧
      hv - lv ≤ expOfBracketEps ((AzRat.toRat r : ℝ) * Real.log (AzRat.toRat q : ℝ))
        (ratPowRatEps r q w) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := ratPowRatBracket_spec q hs h0 r hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [ratPowRatApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, powSign, one_mul]
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | true =>
    simp only [↓reduceIte, powSign, neg_one_mul]
    have hnlo : (-(ratPowRatBracket q r w).2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(ratPowRatBracket q r w).1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- The Ziv certificate for `± q^r`, for a result that is not a rounding boundary. -/
theorem ratPowRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) (r : AzRat)
    (hvB : ((powSign neg * (AzRat.toRat q : ℝ) ^ (AzRat.toRat r : ℝ) : ℝ) : EReal)
      ∉ floatSet (p + 1)) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (ratPowRatApprox neg q r (w₀ * 2 ^ f)).1
      (ratPowRatApprox neg q r (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast toRat_pos_of_sign q hs h0
  exact exists_isSome_of_not_mem_threshold p mode (ratPowRatApprox neg q r)
    (mul_ne_zero (powSign_ne_zero neg) (Real.rpow_pos_of_pos hqv0 _).ne') hvB
    (fun w => expOfBracketEps ((AzRat.toRat r : ℝ) * Real.log (AzRat.toRat q : ℝ))
      (ratPowRatEps r q w) w)
    (tendsto_ratPowRatBracketEps r q _) (ratPowRatW₀ r q)
    (fun _ hw => ratPowRatApprox_spec neg q hs h0 r hw) w₀ hw₀

/-! ### The `D`-th root of a natural -/

theorem natRootD?_some {m : AzNat} (hm : m ≠ 0) {D : AzNat} {u : AzNat}
    (h : natRootD? m D = some u) : m.toNat = u.toNat ^ D.toNat := by
  obtain ⟨hdec, hodd⟩ := splitOdd_spec m hm
  unfold natRootD? at h
  simp only [] at h
  cases hroot : oddRootD (splitOdd m).1 D with
  | none => rw [hroot] at h; cases h
  | some u' =>
    rw [hroot] at h
    have hu' := oddRootD_some hroot
    split_ifs at h with hc0 hsz hdvd
    · rw [Option.some.injEq] at h
      rw [← h, hdec, hc0, pow_zero, mul_one, hu']
    · rw [Option.some.injEq] at h
      rw [← h, AzNat.toNat_shiftLeft, hdec, hu', mul_pow, ← pow_mul,
        Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdvd)]

theorem natRootD?_none {m : AzNat} (hm : m ≠ 0) {D : AzNat} (hD : 2 ≤ D.toNat)
    (h : natRootD? m D = none) : ¬ ∃ c : ℕ, m.toNat = c ^ D.toNat := by
  obtain ⟨hdec, hodd⟩ := splitOdd_spec m hm
  rintro ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hc
    exact hm (AzNat.toNat_injective (by rw [hc, AzNat.toNat_zero]))
  obtain ⟨i, c', hc', hci⟩ := Nat.exists_eq_two_pow_mul_odd hc0
  have heq : (splitOdd m).1.toNat * 2 ^ (splitOdd m).2 = c' ^ D.toNat * 2 ^ (i * D.toNat) := by
    rw [← hdec, hc, hci, mul_pow, ← pow_mul]
    ring
  obtain ⟨hm', he'⟩ := odd_mul_two_pow_inj hodd hc'.pow heq
  unfold natRootD? at h
  simp only [] at h
  cases hroot : oddRootD (splitOdd m).1 D with
  | none => exact oddRootD_none hodd hD hroot ⟨c', hm'⟩
  | some u' =>
    rw [hroot] at h
    split_ifs at h with hc0' hsz hdvd
    · have hi : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · rw [h0, zero_mul] at he'; exact absurd he' hc0'
        · exact h0
      have h1 : D.toNat ≤ (splitOdd m).2 := by rw [he']; exact Nat.le_mul_of_pos_left _ hi
      rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_ofNat] at hsz
      omega
    · apply hdvd
      rw [he']
      exact Nat.mul_mod_left _ _

/-! ### Irrationality -/

/-- `(a/b)^(N/D)` is irrational for coprime `a`, `b ≥ 1`, `N ≠ 0` coprime to `D ≥ 2`, unless `a`
and `b` are both `D`-th powers. -/
theorem irrational_div_rpow_of_not_pow_gen {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcop : Nat.Coprime a b) {N : ℤ} (hN0 : N ≠ 0) {D : ℕ} (hD : 2 ≤ D)
    (hcopD : Nat.Coprime D N.natAbs)
    (h : ¬ ((∃ u : ℕ, a = u ^ D) ∧ ∃ v : ℕ, b = v ^ D)) :
    Irrational (((a : ℝ) / b) ^ ((N : ℝ) / D)) := by
  have hbase : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hmain : ∀ N' : ℕ, N' ≠ 0 → Nat.Coprime D N' →
      Irrational (((a : ℝ) / b) ^ ((N' : ℝ) / D)) := by
    intro N' hN' hcop'
    set M : ℕ := a * b ^ (D - 1) with hM
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsplit : (a : ℝ) / b = (M : ℝ) / ((b : ℝ) ^ D) := by
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have hDpow : (b : ℝ) ^ D = (b : ℝ) ^ (D - 1) * b := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hM, hDpow]
      push_cast
      field_simp
    have hexp : ((b : ℝ) ^ D) ^ ((N' : ℝ) / D) = ((b : ℝ) ^ N' : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_div_cancel₀ _ hD0,
        Real.rpow_natCast]
    rw [hsplit, Real.div_rpow (by positivity) (by positivity), hexp]
    obtain ⟨qq, hqq, hqq0⟩ : ∃ qq : ℚ, (qq : ℝ) = (b : ℝ) ^ N' ∧ qq ≠ 0 :=
      ⟨(b : ℚ) ^ N', by push_cast; rfl, pow_ne_zero _ (by exact_mod_cast (show b ≠ 0 by omega))⟩
    rw [← hqq]
    refine Irrational.div_ratCast ?_ hqq0
    refine irrational_natCast_rpow_div_of_not_pow hM1 hD hcop' ?_
    rintro ⟨c, hc⟩
    apply h
    have hcop'' : Nat.Coprime a (b ^ (D - 1)) := hcop.pow_right _
    have hunit : IsUnit (gcd a (b ^ (D - 1))) := by
      rw [Nat.isUnit_iff]; exact hcop''
    obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit (by rw [← hM]; exact hc)
    have hunit' : IsUnit (gcd (b ^ (D - 1)) a) := by
      rw [Nat.isUnit_iff]; exact hcop''.symm
    obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow hunit' (by rw [mul_comm, ← hM]; exact hc)
    have hcopD' : Nat.Coprime (D - 1) D :=
      ((Nat.coprime_self_sub_right (m := 1) (n := D) (by omega)).mpr
        (Nat.coprime_one_right _)).symm
    obtain ⟨f, hf, -⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcopD' he
    exact ⟨⟨u, hu⟩, ⟨f, hf⟩⟩
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

/-- `ratPowRatExact? = some (u, v, N)`: `u`, `v ≠ 0` coprime, `N ≠ 0` and `(a/b)^r = (u/v)^N`. -/
theorem ratPowRatExact?_some {a b : AzNat} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a.toNat b.toNat) (r : AzRat) (hr0 : r.num ≠ 0) {u v : AzNat}
    {N : AzInt} (h : ratPowRatExact? a b r = some (u, v, N)) :
    u ≠ 0 ∧ v ≠ 0 ∧ Nat.Coprime u.toNat v.toNat ∧ N.toInt ≠ 0 ∧
      ((a.toNat : ℝ) / b.toNat) ^ (AzRat.toRat r : ℝ) = ((u.toNat : ℝ) / v.toNat) ^ N.toInt := by
  have hDpos : 0 < r.den.toNat := AzRat.den_toNat_pos r
  unfold ratPowRatExact? at h
  cases hra : natRootD? a r.den with
  | none => rw [hra] at h; cases h
  | some u' =>
    cases hrb : natRootD? b r.den with
    | none => rw [hra, hrb] at h; cases h
    | some v' =>
      rw [hra, hrb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hu, hv, hN⟩ := h
      rw [← hu, ← hv, ← hN]
      have hau := natRootD?_some ha hra
      have hbv := natRootD?_some hb hrb
      have hu0 : u' ≠ 0 := by
        intro h0
        rw [h0, AzNat.toNat_zero, zero_pow (by omega)] at hau
        exact ha (AzNat.toNat_injective (by rw [hau, AzNat.toNat_zero]))
      have hv0 : v' ≠ 0 := by
        intro h0
        rw [h0, AzNat.toNat_zero, zero_pow (by omega)] at hbv
        exact hb (AzNat.toNat_injective (by rw [hbv, AzNat.toNat_zero]))
      have hcopuv : Nat.Coprime u'.toNat v'.toNat := by
        have h1 : u'.toNat ∣ a.toNat := ⟨u'.toNat ^ (r.den.toNat - 1), by
          rw [hau, ← pow_succ', Nat.sub_add_cancel hDpos]⟩
        have h2 : v'.toNat ∣ b.toNat := ⟨v'.toNat ^ (r.den.toNat - 1), by
          rw [hbv, ← pow_succ', Nat.sub_add_cancel hDpos]⟩
        exact Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.coprime_dvd_right h2 hcop)
      refine ⟨hu0, hv0, hcopuv, toInt_ne_zero_of_ne_zero (mkNorm_ne_zero hr0), ?_⟩
      have hbase : ((a.toNat : ℝ) / b.toNat) = ((u'.toNat : ℝ) / v'.toNat) ^ r.den.toNat := by
        rw [hau, hbv, div_pow]
        push_cast
        rfl
      rw [hbase, coe_toRat_eq_mkNorm_div, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        mul_div_cancel₀ _ (by exact_mod_cast hDpos.ne'), Real.rpow_intCast]

/-- `ratPowRatExact? = none` for coprime `a`, `b ≥ 1` and `r` with `den ≥ 2`: `(a/b)^r` is
irrational. -/
theorem irrational_of_ratPowRatExact?_none {a b : AzNat} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a.toNat b.toNat) (r : AzRat) (hr0 : r.num ≠ 0) (hd : r.den ≠ 1)
    (h : ratPowRatExact? a b r = none) :
    Irrational (((a.toNat : ℝ) / b.toNat) ^ (AzRat.toRat r : ℝ)) := by
  have hDpos : 0 < r.den.toNat := AzRat.den_toNat_pos r
  have hD2 : 2 ≤ r.den.toNat := by
    have : r.den.toNat ≠ 1 := fun h1 => hd (AzNat.toNat_injective (by rw [h1, AzNat.toNat_one]))
    omega
  have hcopD : Nat.Coprime r.den.toNat (AzInt.mkNorm r.sign r.num).toInt.natAbs := by
    have hc := (AzNat.coprime_iff _ _).mp r.reduced
    have : (AzInt.mkNorm r.sign r.num).toInt.natAbs = r.num.toNat := by
      cases r.sign
      · rw [AzInt.toInt_mkNorm_false _ hr0, Int.natAbs_neg, Int.natAbs_natCast]
      · rw [AzInt.toInt_mkNorm_true, Int.natAbs_natCast]
    rw [this]
    exact hc.symm
  have ha1 : 1 ≤ a.toNat :=
    Nat.one_le_iff_ne_zero.mpr (fun h0 => ha (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])))
  have hb1 : 1 ≤ b.toNat :=
    Nat.one_le_iff_ne_zero.mpr (fun h0 => hb (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])))
  rw [coe_toRat_eq_mkNorm_div]
  refine irrational_div_rpow_of_not_pow_gen ha1 hb1 hcop
    (toInt_ne_zero_of_ne_zero (mkNorm_ne_zero hr0)) hD2 hcopD ?_
  rintro ⟨hau, hbv⟩
  unfold ratPowRatExact? at h
  cases hra : natRootD? a r.den with
  | none => exact natRootD?_none ha hD2 hra hau
  | some u' =>
    cases hrb : natRootD? b r.den with
    | none => exact natRootD?_none hb hD2 hrb hbv
    | some v' => rw [hra, hrb] at h; cases h

end Azurite.AzFloat
