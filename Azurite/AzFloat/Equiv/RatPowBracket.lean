/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RatPowBracket
import Azurite.AzFloat.Equiv.PowBracket
import Azurite.AzFloat.Equiv.LnRat
import Azurite.AzRat.Equiv.Div
import Azurite.AzNat.Equiv.ShiftLeft

/-!
# Equivalence: the bracket of `q^y` and the exact rational powers

* `mulBracketAny_spec`: `y` times any bracket `[c, d]` of `L`, with the width
  `|y| (d − c) + 2 |y| (|c| + |d|) 2^(−W)`.
* `lnRatMulBracket_spec`: `lnRatMulBracket q y ey w` encloses `y ln q` with width at most
  `mulLnEps ey (ratPowE q) w` (`|ln q| ≤ size num + size den`, `lnFloorBracket_spec`).
* `ratPowBracket_spec`, `ratPowApprox_spec`, `ratPowApprox_isSome_exists` (the Ziv certificate
  for a result outside `floatSet (p+1)`).
* Exact powers: `natPow2Root?_some/none`, `ratPowExact?_some` (`(a/b)^y = (u/v)^N`),
  `irrational_of_ratPowExact?_none` from `irrational_div_rpow_of_not_pow` (`(a/b)^(N/2^J)` is
  irrational for coprime `a`, `b` not both `2^J`-th powers: `a/b = a b^(2^J−1) / (b^(2^J))`, and
  `a b^(2^J−1)` is a `2^J`-th power only if `a` and `b` are, by `exists_eq_pow_of_mul_eq_pow`).
* `not_mem_floatSet_ratPow_of_not_cheap`: a non-cheap `± (a/b)^n` is not a rounding boundary.
-/

namespace Azurite.AzFloat

/-! ### `y` times a bracket -/

/-- `mulBracketAny y B W` for a bracket `B = [c, d]` of `L`: a bracket of `y L` of width at most
`|y| (d − c) + 2 |y| (|c| + |d|) 2^(−W)`. -/
theorem mulBracketAny_spec {y : AzFloat} {yv : ℝ} (hy : y.toVal = some (yv : EReal))
    {B : AzFloat × AzFloat} {c d L : ℝ} (hc : B.1.toVal = some (c : EReal))
    (hd : B.2.toVal = some (d : EReal)) (hcL : c ≤ L) (hLd : L ≤ d) (W : ℕ) [NeZero W] :
    ∃ lo hi : ℝ, (mulBracketAny y B W).1.toVal = some (lo : EReal) ∧
      (mulBracketAny y B W).2.toVal = some (hi : EReal) ∧ lo ≤ yv * L ∧ yv * L ≤ hi ∧
      hi - lo ≤ |yv| * (d - c) + 2 * |yv| * (|c| + |d|) * (1 / 2 : ℝ) ^ W := by
  have hδ0 : 0 ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hya0 : 0 ≤ |yv| := abs_nonneg _
  simp only [mulBracketAny]
  split_ifs with hneg
  · have hyneg : yv < 0 := (toVal_sign_of_isNegative hy).1 hneg
    have hay : |yv| = -yv := abs_of_neg hyneg
    obtain ⟨r₁, hr₁, hr₁a, hr₁b⟩ := mulFloor_abs hy hd W
    obtain ⟨r₂, hr₂, hr₂a, hr₂b⟩ := mulCeiling_abs hy hc W
    refine ⟨r₁, r₂, hr₁, hr₂, hr₁a.trans (mul_le_mul_of_nonpos_left hLd hyneg.le),
      (mul_le_mul_of_nonpos_left hcL hyneg.le).trans hr₂a, ?_⟩
    rw [abs_mul] at hr₁b hr₂b
    have h1 : |yv| * |d| * (1 / 2 : ℝ) ^ W ≤ |yv| * (|c| + |d|) * (1 / 2 : ℝ) ^ W := by
      apply mul_le_mul_of_nonneg_right _ hδ0
      apply mul_le_mul_of_nonneg_left _ hya0
      linarith [abs_nonneg c]
    have h2 : |yv| * |c| * (1 / 2 : ℝ) ^ W ≤ |yv| * (|c| + |d|) * (1 / 2 : ℝ) ^ W := by
      apply mul_le_mul_of_nonneg_right _ hδ0
      apply mul_le_mul_of_nonneg_left _ hya0
      linarith [abs_nonneg d]
    have h3 : yv * c - yv * d = |yv| * (d - c) := by rw [hay]; ring
    linarith
  · have hynn : 0 ≤ yv := (toVal_sign_of_isNegative hy).2 (by simpa using hneg)
    have hay : |yv| = yv := abs_of_nonneg hynn
    obtain ⟨r₁, hr₁, hr₁a, hr₁b⟩ := mulFloor_abs hy hc W
    obtain ⟨r₂, hr₂, hr₂a, hr₂b⟩ := mulCeiling_abs hy hd W
    refine ⟨r₁, r₂, hr₁, hr₂, hr₁a.trans (mul_le_mul_of_nonneg_left hcL hynn),
      (mul_le_mul_of_nonneg_left hLd hynn).trans hr₂a, ?_⟩
    rw [abs_mul] at hr₁b hr₂b
    have h1 : |yv| * |d| * (1 / 2 : ℝ) ^ W ≤ |yv| * (|c| + |d|) * (1 / 2 : ℝ) ^ W := by
      apply mul_le_mul_of_nonneg_right _ hδ0
      apply mul_le_mul_of_nonneg_left _ hya0
      linarith [abs_nonneg c]
    have h2 : |yv| * |c| * (1 / 2 : ℝ) ^ W ≤ |yv| * (|c| + |d|) * (1 / 2 : ℝ) ^ W := by
      apply mul_le_mul_of_nonneg_right _ hδ0
      apply mul_le_mul_of_nonneg_left _ hya0
      linarith [abs_nonneg d]
    have h3 : yv * d - yv * c = |yv| * (d - c) := by rw [hay]; ring
    linarith

/-! ### The bracket of `y ln q` -/

/-- `0 ≤ ln m < size m` for a natural `m ≥ 1`. -/
theorem log_nat_lt_size {m : ℕ} (hm : 1 ≤ m) : 0 ≤ Real.log m ∧ Real.log m < m.size := by
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨Real.log_nonneg h1, ?_⟩
  have h2 : (m : ℝ) < (2 : ℝ) ^ m.size := by exact_mod_cast Nat.lt_size_self m
  have hl2 := Real.log_two_lt_d9
  calc Real.log m < Real.log ((2 : ℝ) ^ m.size) := Real.log_lt_log (by linarith) h2
    _ = m.size * Real.log 2 := by rw [Real.log_pow]
    _ ≤ m.size * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = m.size := mul_one _

/-- `|ln (a/b)| ≤ size a + size b` for naturals `a`, `b ≥ 1`. -/
theorem abs_log_div_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Real.log ((a : ℝ) / b)| ≤ a.size + b.size := by
  obtain ⟨ha0, ha1⟩ := log_nat_lt_size ha
  obtain ⟨hb0, hb1⟩ := log_nat_lt_size hb
  rw [Real.log_div (by positivity) (by positivity), abs_le]
  constructor <;> linarith

/-- The value of a positive `AzRat`: `num / den`. -/
theorem coe_toRat_eq_div_pos (q : AzRat) (hs : q.sign = true) :
    (AzRat.toRat q : ℝ) = (q.num.toNat : ℝ) / q.den.toNat := by
  rw [AzRat.toRat_cast_eq, hs]
  simp

/-- `lnRatMulBracket q y ey w` encloses `y ln q` for a positive `q` and `|y| < 2^ey`, with width
at most `mulLnEps ey (ratPowE q) w` (`w ≥ 64`). -/
theorem lnRatMulBracket_spec (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) {y : AzFloat}
    {yv : ℝ} (hy : y.toVal = some (yv : EReal)) (ey : AzInt) (hye : |yv| < (2 : ℝ) ^ ey.toInt)
    (w : ℕ) (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (lnRatMulBracket q y ey w).1.toVal = some (lo : EReal) ∧
      (lnRatMulBracket q y ey w).2.toVal = some (hi : EReal) ∧
      lo ≤ yv * Real.log (AzRat.toRat q : ℝ) ∧ yv * Real.log (AzRat.toRat q : ℝ) ≤ hi ∧
      hi - lo ≤ mulLnEps ey.toInt (ratPowE q : ℤ) w := by
  -- the working precision and the scale
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
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ W := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu1 : u ≤ 1 := by rw [hu]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hδ : u = uu * (1 / 65536) * (1 / 2 : ℝ) ^ emax := by
    rw [hu, hWv, pow_add, pow_add, huu, show ((1 : ℝ) / 2) ^ 16 = 1 / 65536 by norm_num]
  have hEu : E * (1 / 2 : ℝ) ^ emax = 1 := by
    rw [hE, one_div_pow, mul_one_div, div_self (by positivity)]
  have hya0 : 0 ≤ |yv| := abs_nonneg _
  have hX : |yv| * u ≤ uu / 65536 := by
    rw [hδ]
    have : |yv| * (1 / 2 : ℝ) ^ emax ≤ E * (1 / 2 : ℝ) ^ emax :=
      mul_le_mul_of_nonneg_right hyE.le (by positivity)
    rw [hEu] at this
    calc |yv| * (uu * (1 / 65536) * (1 / 2 : ℝ) ^ emax)
        = uu / 65536 * (|yv| * (1 / 2 : ℝ) ^ emax) := by ring
      _ ≤ uu / 65536 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = uu / 65536 := mul_one _
  -- the bracket of `ln q` from the float below `q`
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast toRat_pos_of_sign q hs h0
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q W
  rw [abs_of_pos hqv0, ← hu] at hr2
  obtain ⟨c, d, hc, hd, hcL, hLd, hcd⟩ :=
    lnFloorBracket_spec (by omega : 64 ≤ W) hr hqv0 hr1 (by rw [← hu]; exact hr2)
  set A := |Real.log (AzRat.toRat q : ℝ)| with hA
  set Ez : ℕ := ⌊2 * A⌋₊ + 2 with hEz
  -- `A ≤ size num + size den` and `Ez ≤ ratPowE q`
  have hnum1 : 1 ≤ q.num.toNat :=
    Nat.one_le_iff_ne_zero.mpr (fun h => h0 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero])))
  have hden1 : 1 ≤ q.den.toNat := AzRat.den_toNat_pos q
  have hAle : A ≤ (q.num.size : ℝ) + q.den.size := by
    rw [hA, coe_toRat_eq_div_pos q hs]
    have := abs_log_div_le hnum1 hden1
    rw [AzNat.size_toNat, AzNat.size_toNat] at this
    exact_mod_cast this
  have hEc : (Ez : ℝ) ≤ ratPowE q := by
    unfold ratPowE
    rw [hEz]
    push_cast
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * A)
    linarith
  have hEcA : 2 * A ≤ (ratPowE q : ℝ) := by unfold ratPowE; push_cast; linarith
  have hA0 : 0 ≤ A := abs_nonneg _
  -- the key quantities
  obtain ⟨Lw, hLw⟩ : ∃ Lw : ℝ, Lw = lnEps ((ratPowE q : ℤ) + 16 + max ey.toInt 0) w := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = lnEps (ratPowE q : ℤ) W := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; unfold lnEps; positivity
  have hLw0 : 0 ≤ Lw := by rw [hLw]; unfold lnEps; positivity
  have hpoly : ((W : ℕ) : ℝ) + |((ratPowE q : ℤ) : ℝ)| + 8
      = (w : ℝ) + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8 := by
    rw [← hemaxM, hWv]
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ratPowE q : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ratPowE q : ℝ) + 16 + emax)]
    ring
  have hΛLw : Λ ≤ Lw := by
    rw [hΛ, hLw]
    unfold lnEps
    rw [hpoly, ← hu, ← huu]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hu, huu]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hkey : |yv| * Λ ≤ Lw / 65536 := by
    rw [hΛ, hLw]
    unfold lnEps
    rw [hpoly, ← hu, ← huu]
    have hP0 : 0 ≤ (2 : ℝ) ^ 40
        * ((w : ℝ) + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5 := by
      positivity
    calc |yv| * (2 ^ 40 * ((w : ℝ) + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * u)
        = 2 ^ 40 * ((w : ℝ) + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * (|yv| * u) := by ring
      _ ≤ 2 ^ 40 * ((w : ℝ) + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * (uu / 65536) := mul_le_mul_of_nonneg_left hX hP0
      _ = _ := by ring
  have hEb : ((ratPowE q : ℝ) + 24) * uu ≤ Lw := by
    rw [hLw]
    unfold lnEps
    rw [← huu]
    have hbase : (ratPowE q : ℝ) + 24
        ≤ (w : ℝ) + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8 := by
      have hX' : ((ratPowE q : ℤ) + 16 : ℤ) ≤ (ratPowE q : ℤ) + 16 + max ey.toInt 0 := by
        have := le_max_right ey.toInt 0; omega
      have hX'' : (((ratPowE q : ℤ) + 16 : ℤ) : ℝ)
          ≤ (((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ) := by exact_mod_cast hX'
      have hXabs := le_abs_self (((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)
      have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
      push_cast at hX'' hXabs ⊢
      linarith
    have hb1 : (1 : ℝ) ≤ (w : ℝ) + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8 := by
      linarith [abs_nonneg (((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ),
        (Nat.cast_nonneg w : (0 : ℝ) ≤ w)]
    have hpow5 := le_self_pow₀ hb1 (by norm_num : (5 : ℕ) ≠ 0)
    have h240 : (1 : ℝ) ≤ 2 ^ 40 := by norm_num
    have hu0' := huu0.le
    calc ((ratPowE q : ℝ) + 24) * uu
        ≤ ((w : ℝ) + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5 * uu :=
          mul_le_mul_of_nonneg_right (hbase.trans hpow5) hu0'
      _ ≤ 2 ^ 40 * ((w : ℝ) + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5
          * uu := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h240
            (by positivity : (0 : ℝ) ≤ ((w : ℝ)
              + |(((ratPowE q : ℤ) + 16 + max ey.toInt 0 : ℤ) : ℝ)| + 8) ^ 5)) hu0'
          rwa [one_mul] at this
  -- `lnEps Ez W ≤ Λ`
  have hEzΛ : lnEps (Ez : ℤ) W ≤ Λ := by
    rw [hΛ]
    apply lnEps_mono
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast hEc
  -- the width of the `ln q` bracket and the size of its ends
  have hdc : d - c ≤ 2 * Λ + ((ratPowE q : ℝ) + 20) * u := by
    unfold lnRatEps at hcd
    rw [← hu] at hcd
    have h1 : lnEps (Ez : ℤ) W ≤ Λ := hEzΛ
    have h2 : A ≤ (ratPowE q : ℝ) / 2 := by linarith
    have hl0 : 0 ≤ lnEps (Ez : ℤ) W := by unfold lnEps; positivity
    have hu_half : u ≤ 1 / 2 := by
      rw [hu]
      calc (1 / 2 : ℝ) ^ W ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _
    have hℓu : lnEps (Ez : ℤ) W * u ≤ lnEps (Ez : ℤ) W * (1 / 2) :=
      mul_le_mul_of_nonneg_left hu_half hl0
    have hAu : A * u ≤ (ratPowE q : ℝ) / 2 * u := mul_le_mul_of_nonneg_right h2 hu0
    have huu' : u * u ≤ u * 1 := mul_le_mul_of_nonneg_left hu1 hu0
    have e : lnEps (Ez : ℤ) W + 4 * u + 2 * (A + (lnEps (Ez : ℤ) W + 8 * u)) * u
        = lnEps (Ez : ℤ) W + 4 * u + 2 * (A * u) + 2 * (lnEps (Ez : ℤ) W * u) + 16 * (u * u) := by
      ring
    rw [e] at hcd
    linarith
  have hLA : Real.log (AzRat.toRat q : ℝ) ≤ A := by rw [hA]; exact le_abs_self _
  have hLA' : -A ≤ Real.log (AzRat.toRat q : ℝ) := by rw [hA]; exact neg_abs_le _
  have hcabs : |c| ≤ A + (d - c) := by
    rw [abs_le]; constructor <;> linarith
  have hdabs : |d| ≤ A + (d - c) := by
    rw [abs_le]; constructor <;> linarith
  -- the product bracket
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := mulBracketAny_spec hy hc hd hcL hLd W
  refine ⟨lo, hi, ?_, ?_, h1, h2, ?_⟩
  · simp only [lnRatMulBracket]; rw [← hW]; exact hlo
  · simp only [lnRatMulBracket]; rw [← hW]; exact hhi
  · rw [← hu] at hwid
    have hM : |c| + |d| ≤ (ratPowE q : ℝ) + 4 * Λ + 2 * ((ratPowE q : ℝ) + 20) * u := by
      linarith
    have hT1 : |yv| * (d - c) ≤ |yv| * (2 * Λ + ((ratPowE q : ℝ) + 20) * u) :=
      mul_le_mul_of_nonneg_left hdc hya0
    have hT2 : 2 * |yv| * (|c| + |d|) * u
        ≤ 2 * |yv| * ((ratPowE q : ℝ) + 4 * Λ + 2 * ((ratPowE q : ℝ) + 20) * u) * u := by
      apply mul_le_mul_of_nonneg_right _ hu0
      exact mul_le_mul_of_nonneg_left hM (by positivity)
    -- each monomial against `Lw`
    have hE0 : (0 : ℝ) ≤ ratPowE q := by positivity
    have m1 : |yv| * Λ ≤ Lw / 65536 := hkey
    have m2 : |yv| * u * ((ratPowE q : ℝ) + 20) ≤ Lw / 65536 := by
      have := mul_le_mul_of_nonneg_right hX (by positivity : (0 : ℝ) ≤ (ratPowE q : ℝ) + 20)
      have h' : uu / 65536 * ((ratPowE q : ℝ) + 20) ≤ Lw / 65536 := by linarith
      linarith
    have m3 : |yv| * u * Λ ≤ Lw / 65536 := by
      have := mul_le_mul_of_nonneg_right hX hΛ0
      have h' : uu / 65536 * Λ ≤ Lw / 65536 := by
        have := mul_le_mul_of_nonneg_left huu1 hΛ0
        linarith
      linarith
    have m4 : |yv| * u * u * ((ratPowE q : ℝ) + 20) ≤ Lw / 65536 := by
      have h' : |yv| * u * u ≤ |yv| * u := by
        have := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ |yv| * u)
        linarith
      have := mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ (ratPowE q : ℝ) + 20)
      linarith
    have m5 : |yv| * u * (ratPowE q : ℝ) ≤ Lw / 65536 := by
      have := mul_le_mul_of_nonneg_right hX hE0
      have h' : uu / 65536 * (ratPowE q : ℝ) ≤ Lw / 65536 := by linarith
      linarith
    have hmul : mulLnEps ey.toInt (ratPowE q : ℤ) w = Lw + uu := by
      unfold mulLnEps
      rw [hLw, huu, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (ratPowE q : ℤ))]
    rw [hmul]
    have e1 : |yv| * (2 * Λ + ((ratPowE q : ℝ) + 20) * u)
        = 2 * (|yv| * Λ) + |yv| * u * ((ratPowE q : ℝ) + 20) := by ring
    have e2 : 2 * |yv| * ((ratPowE q : ℝ) + 4 * Λ + 2 * ((ratPowE q : ℝ) + 20) * u) * u
        = 2 * (|yv| * u * (ratPowE q : ℝ)) + 8 * (|yv| * u * Λ)
          + 4 * (|yv| * u * u * ((ratPowE q : ℝ) + 20)) := by ring
    rw [e1] at hT1
    rw [e2] at hT2
    linarith

/-- `ratPowW₀ ey q` as an integer. -/
theorem ratPowW₀_eq (ey : AzInt) (q : AzRat) :
    ((ratPowW₀ ey q : ℕ) : ℤ) = 88 + max ey.toInt 0 + |(ratPowE q : ℤ)| := by
  unfold ratPowW₀
  rw [Nat.cast_add, Nat.cast_add, expPos_eq_max, abs_of_nonneg (by positivity)]
  norm_num

/-- `ratPowBracket q y ey w` encloses `q^y` for `w ≥ ratPowW₀ ey q`. -/
theorem ratPowBracket_spec (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) {y : AzFloat}
    {yv : ℝ} (hy : y.toVal = some (yv : EReal)) (ey : AzInt) (hye : |yv| < (2 : ℝ) ^ ey.toInt)
    {w : ℕ} (hw : ratPowW₀ ey q ≤ w) :
    ∃ lo hi : ℝ, (ratPowBracket q y ey w).1.toVal = some (lo : EReal) ∧
      (ratPowBracket q y ey w).2.toVal = some (hi : EReal) ∧
      lo ≤ (AzRat.toRat q : ℝ) ^ yv ∧ (AzRat.toRat q : ℝ) ^ yv ≤ hi ∧
      hi - lo ≤ powBaseEps ey.toInt (ratPowE q : ℤ) (yv * Real.log (AzRat.toRat q : ℝ)) w := by
  have hw64 : 64 ≤ w := by unfold ratPowW₀ at hw; omega
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := lnRatMulBracket_spec q hs h0 hy ey hye w hw64
  have hwZ : 88 + max ey.toInt 0 + |(ratPowE q : ℤ)| ≤ (w : ℤ) := by
    rw [← ratPowW₀_eq]; exact_mod_cast hw
  have hw1 : hi - lo ≤ 1 := hwid.trans (mulLnEps_le_one _ _ _ hwZ)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := expOfBracket_spec_width hlo hhi h1 h2 hw1 hw64
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast toRat_pos_of_sign q hs h0
  rw [rpow_eq_exp_mul_log hqv0]
  refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
  unfold powBaseEps
  refine hab.trans ?_
  unfold expOfBracketEps
  have := Real.exp_pos (yv * Real.log (AzRat.toRat q : ℝ))
  nlinarith

/-- `ratPowApprox neg q y ey w` brackets `± q^y`. -/
theorem ratPowApprox_spec (neg : Bool) (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0)
    {y : AzFloat} {yv : ℝ} (hy : y.toVal = some (yv : EReal)) (ey : AzInt)
    (hye : |yv| < (2 : ℝ) ^ ey.toInt) {w : ℕ} (hw : ratPowW₀ ey q ≤ w) :
    ∃ lv hv : ℝ, Rounds (ratPowApprox neg q y ey w).1 lv ∧
      Rounds (ratPowApprox neg q y ey w).2 hv ∧
      lv ≤ powSign neg * (AzRat.toRat q : ℝ) ^ yv ∧
      powSign neg * (AzRat.toRat q : ℝ) ^ yv ≤ hv ∧
      hv - lv ≤ powBaseEps ey.toInt (ratPowE q : ℤ) (yv * Real.log (AzRat.toRat q : ℝ)) w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := ratPowBracket_spec q hs h0 hy ey hye hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [ratPowApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, powSign, one_mul]
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | true =>
    simp only [↓reduceIte, powSign, neg_one_mul]
    have hnlo : (-(ratPowBracket q y ey w).2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(ratPowBracket q y ey w).1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- The Ziv certificate for `± q^y`, for a result that is not a rounding boundary. -/
theorem ratPowApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) {y : AzFloat} {yv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (ey : AzInt) (hye : |yv| < (2 : ℝ) ^ ey.toInt)
    (hvB : ((powSign neg * (AzRat.toRat q : ℝ) ^ yv : ℝ) : EReal) ∉ floatSet (p + 1))
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (ratPowApprox neg q y ey (w₀ * 2 ^ f)).1
      (ratPowApprox neg q y ey (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast toRat_pos_of_sign q hs h0
  exact exists_isSome_of_not_mem_threshold p mode (ratPowApprox neg q y ey)
    (mul_ne_zero (powSign_ne_zero neg) (Real.rpow_pos_of_pos hqv0 yv).ne') hvB
    (powBaseEps ey.toInt (ratPowE q : ℤ) (yv * Real.log (AzRat.toRat q : ℝ)))
    (tendsto_powBaseEps _ _ _) (ratPowW₀ ey q)
    (fun _ hw => ratPowApprox_spec neg q hs h0 hy ey hye hw) w₀ hw₀

/-! ### The `2^J`-th root of a natural -/

theorem natPow2Root?_some {m : AzNat} (hm : m ≠ 0) {J : ℕ} {u : AzNat}
    (h : natPow2Root? m J = some u) : m.toNat = u.toNat ^ (2 ^ J) := by
  obtain ⟨hdec, hodd⟩ := splitOdd_spec m hm
  unfold natPow2Root? at h
  simp only [] at h
  cases hroot : oddPow2Root (splitOdd m).1 J with
  | none => rw [hroot] at h; cases h
  | some u' =>
    rw [hroot] at h
    have hu' := oddPow2Root_some hroot
    split_ifs at h with hc0 hsz hdvd
    · rw [Option.some.injEq] at h
      rw [← h, hdec, hc0, pow_zero, mul_one, hu']
    · rw [Option.some.injEq] at h
      rw [← h, AzNat.toNat_shiftLeft, hdec, hu', mul_pow, ← pow_mul,
        Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdvd)]

theorem natPow2Root?_none {m : AzNat} (hm : m ≠ 0) {J : ℕ} (h : natPow2Root? m J = none) :
    ¬ ∃ c : ℕ, m.toNat = c ^ (2 ^ J) := by
  obtain ⟨hdec, hodd⟩ := splitOdd_spec m hm
  rintro ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hc
    exact hm (AzNat.toNat_injective (by rw [hc, AzNat.toNat_zero]))
  obtain ⟨i, c', hc', hci⟩ := Nat.exists_eq_two_pow_mul_odd hc0
  have heq : (splitOdd m).1.toNat * 2 ^ (splitOdd m).2 = c' ^ (2 ^ J) * 2 ^ (i * 2 ^ J) := by
    rw [← hdec, hc, hci, mul_pow, ← pow_mul]
    ring
  obtain ⟨hm', he'⟩ := odd_mul_two_pow_inj hodd hc'.pow heq
  unfold natPow2Root? at h
  simp only [] at h
  cases hroot : oddPow2Root (splitOdd m).1 J with
  | none => exact oddPow2Root_none hodd hroot ⟨c', hm'⟩
  | some u' =>
    rw [hroot] at h
    split_ifs at h with hc0' hsz hdvd
    · -- `c ≠ 0` and `size c ≤ J`: but `2^J ∣ c`
      have hi : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · rw [h0, zero_mul] at he'; exact absurd he' hc0'
        · exact h0
      have h1 : 2 ^ J ≤ (splitOdd m).2 := by rw [he']; exact Nat.le_mul_of_pos_left _ hi
      have h2 : (splitOdd m).2 < 2 ^ (splitOdd m).2.size := Nat.lt_size_self _
      have h3 : 2 ^ (splitOdd m).2.size ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hsz
      omega
    · apply hdvd
      rw [he']
      exact Nat.mul_mod_left _ _

/-! ### Irrationality -/

/-- `(a/b)^(N/2^J)` is irrational for coprime `a`, `b ≥ 1`, `N` odd, `J ≥ 1`, unless `a` and `b`
are both `2^J`-th powers. -/
theorem irrational_div_rpow_of_not_pow {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcop : Nat.Coprime a b) {N : ℤ} (hN : Odd N) {J : ℕ} (hJ : 1 ≤ J)
    (h : ¬ ((∃ u : ℕ, a = u ^ (2 ^ J)) ∧ ∃ v : ℕ, b = v ^ (2 ^ J))) :
    Irrational (((a : ℝ) / b) ^ ((N : ℝ) / (2 : ℝ) ^ J)) := by
  have hbase : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hD2 : 2 ≤ 2 ^ J := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ
  have hmain : ∀ N' : ℕ, Odd N' →
      Irrational (((a : ℝ) / b) ^ ((N' : ℝ) / (2 : ℝ) ^ J)) := by
    intro N' hN'
    set D := 2 ^ J with hD
    -- `a/b = M / b^D` with `M = a b^(D−1)`
    set M : ℕ := a * b ^ (D - 1) with hM
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsplit : (a : ℝ) / b = (M : ℝ) / ((b : ℝ) ^ D) := by
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have hDpow : (b : ℝ) ^ D = (b : ℝ) ^ (D - 1) * b := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hM, hDpow]
      push_cast
      field_simp
    have hexp : ((b : ℝ) ^ D) ^ ((N' : ℝ) / (2 : ℝ) ^ J) = ((b : ℝ) ^ N' : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hD]
      push_cast
      rw [mul_div_cancel₀ _ (by positivity), Real.rpow_natCast]
    rw [hsplit, Real.div_rpow (by positivity) (by positivity), hexp]
    have hq : ∃ q : ℚ, (q : ℝ) = (b : ℝ) ^ N' ∧ q ≠ 0 :=
      ⟨(b : ℚ) ^ N', by push_cast; rfl, pow_ne_zero _ (by exact_mod_cast (show b ≠ 0 by omega))⟩
    obtain ⟨q, hq, hq0⟩ := hq
    rw [← hq]
    refine Irrational.div_ratCast ?_ hq0
    have hcore : Irrational ((M : ℝ) ^ ((N' : ℝ) / ((D : ℕ) : ℝ))) := by
      refine irrational_natCast_rpow_div_of_not_pow hM1 hD2
        (Nat.Coprime.pow_left J (Nat.coprime_two_left.mpr hN')) ?_
      rintro ⟨c, hc⟩
      apply h
      have hcop' : Nat.Coprime a (b ^ (D - 1)) := hcop.pow_right _
      have hunit : IsUnit (gcd a (b ^ (D - 1))) := by
        rw [Nat.isUnit_iff]; exact hcop'
      obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit (by rw [← hM]; exact hc)
      have hunit' : IsUnit (gcd (b ^ (D - 1)) a) := by
        rw [Nat.isUnit_iff]; exact hcop'.symm
      obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow hunit' (by rw [mul_comm, ← hM]; exact hc)
      have hcopD : Nat.Coprime (D - 1) D :=
        ((Nat.coprime_self_sub_right (m := 1) (n := D) (by omega)).mpr
          (Nat.coprime_one_right _)).symm
      obtain ⟨f, hf, -⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcopD he
      exact ⟨⟨u, hu⟩, ⟨f, hf⟩⟩
    rw [hD] at hcore
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

/-- `ratPowExact? = some (u, v, N)`: `u`, `v ≠ 0` coprime, `N ≠ 0` and `(a/b)^y = (u/v)^N`. -/
theorem ratPowExact?_some {a b : AzNat} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a.toNat b.toNat) (sy : Bool) (ey : AzInt)
    {qy : ℕ} {my : AzNat} (hvy : FiniteValid qy my)
    (hni : isInteger (finite sy ey qy my hvy) = false) {u v : AzNat} {N : AzInt}
    (h : ratPowExact? a b sy ey my = some (u, v, N)) :
    u ≠ 0 ∧ v ≠ 0 ∧ Nat.Coprime u.toNat v.toNat ∧ N.toInt ≠ 0 ∧
      ((a.toNat : ℝ) / b.toNat) ^ finiteVal sy ey my
        = ((u.toNat : ℝ) / v.toNat) ^ N.toInt := by
  obtain ⟨hJ1, hJabs, hyv⟩ := finiteVal_eq_div_of_not_isInteger sy ey hvy hni
  have hmy0 : my ≠ 0 := ne_zero_of_finiteValid 0 hvy
  obtain ⟨-, hnodd⟩ := splitOdd_spec my hmy0
  obtain ⟨J, hJ⟩ : ∃ J : ℕ,
      J = ((AzNat.ofNat my.size).toAzInt - (AzNat.ofNat (splitOdd my).2).toAzInt - ey).abs.toNat :=
    ⟨_, rfl⟩
  have hJnat : J = ((my.size : ℤ) - (splitOdd my).2 - ey.toInt).natAbs := by
    rw [hJ, toNat_abs_eq_natAbs, toInt_powExact_J]
  unfold ratPowExact? at h
  simp only [] at h
  rw [← hJ] at h
  cases hra : natPow2Root? a J with
  | none => rw [hra] at h; cases h
  | some u' =>
    cases hrb : natPow2Root? b J with
    | none => rw [hra, hrb] at h; cases h
    | some v' =>
      rw [hra, hrb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hu, hv, hN⟩ := h
      rw [← hu, ← hv]
      have hau := natPow2Root?_some ha hra
      have hbv := natPow2Root?_some hb hrb
      have hu0 : u' ≠ 0 := by
        intro h0
        rw [h0, AzNat.toNat_zero, zero_pow (by positivity)] at hau
        exact ha (AzNat.toNat_injective (by rw [hau, AzNat.toNat_zero]))
      have hv0 : v' ≠ 0 := by
        intro h0
        rw [h0, AzNat.toNat_zero, zero_pow (by positivity)] at hbv
        exact hb (AzNat.toNat_injective (by rw [hbv, AzNat.toNat_zero]))
      have hn0 : (splitOdd my).1 ≠ 0 := by
        intro h0
        rw [h0, AzNat.toNat_zero] at hnodd
        simp at hnodd
      have hn0' : (splitOdd my).1.toNat ≠ 0 :=
        fun h0 => hn0 (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero]))
      have hcopuv : Nat.Coprime u'.toNat v'.toNat := by
        have hJpos : 0 < 2 ^ J := by positivity
        have h1 : u'.toNat ∣ a.toNat := ⟨u'.toNat ^ (2 ^ J - 1), by
          rw [hau, ← pow_succ', Nat.sub_add_cancel hJpos]⟩
        have h2 : v'.toNat ∣ b.toNat := ⟨v'.toNat ^ (2 ^ J - 1), by
          rw [hbv, ← pow_succ', Nat.sub_add_cancel hJpos]⟩
        exact Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.coprime_dvd_right h2 hcop)
      refine ⟨hu0, hv0, hcopuv, ?_, ?_⟩
      · rw [← hN]
        cases sy with
        | true => rw [AzInt.toInt_mkNorm_true]; exact_mod_cast hn0'
        | false =>
          rw [AzInt.toInt_mkNorm_false _ hn0]; exact neg_ne_zero.mpr (by exact_mod_cast hn0')
      · have hbase : ((a.toNat : ℝ) / b.toNat) = ((u'.toNat : ℝ) / v'.toNat) ^ (2 ^ J) := by
          rw [hau, hbv, div_pow]
          push_cast
          rfl
        rw [hbase, hyv, ← hJnat, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← hN]
        have h2J : ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J := by push_cast; rfl
        rw [h2J, mul_div_cancel₀ _ (by positivity), Real.rpow_intCast]

/-- `ratPowExact? = none` for coprime `a`, `b ≥ 1` and a non-integer `y`: `(a/b)^y` is
irrational. -/
theorem irrational_of_ratPowExact?_none {a b : AzNat} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a.toNat b.toNat) (sy : Bool) (ey : AzInt) {qy : ℕ} {my : AzNat}
    (hvy : FiniteValid qy my) (hni : isInteger (finite sy ey qy my hvy) = false)
    (h : ratPowExact? a b sy ey my = none) :
    Irrational (((a.toNat : ℝ) / b.toNat) ^ finiteVal sy ey my) := by
  obtain ⟨hJ1, hJabs, hyv⟩ := finiteVal_eq_div_of_not_isInteger sy ey hvy hni
  have hmy0 : my ≠ 0 := ne_zero_of_finiteValid 0 hvy
  obtain ⟨-, hnodd⟩ := splitOdd_spec my hmy0
  obtain ⟨J, hJ⟩ : ∃ J : ℕ,
      J = ((AzNat.ofNat my.size).toAzInt - (AzNat.ofNat (splitOdd my).2).toAzInt - ey).abs.toNat :=
    ⟨_, rfl⟩
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
  have ha1 : 1 ≤ a.toNat :=
    Nat.one_le_iff_ne_zero.mpr (fun h0 => ha (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])))
  have hb1 : 1 ≤ b.toNat :=
    Nat.one_le_iff_ne_zero.mpr (fun h0 => hb (AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])))
  rw [hyv, ← hJnat]
  refine irrational_div_rpow_of_not_pow ha1 hb1 hcop hNodd hJ1' ?_
  rintro ⟨hau, hbv⟩
  unfold ratPowExact? at h
  simp only [] at h
  rw [← hJ] at h
  cases hra : natPow2Root? a J with
  | none => exact natPow2Root?_none ha hra hau
  | some u' =>
    cases hrb : natPow2Root? b J with
    | none => exact natPow2Root?_none hb hrb hbv
    | some v' => rw [hra, hrb] at h; cases h

/-! ### The non-cheap integer powers are not boundaries -/

/-- A non-cheap `± (a/b)^n` for coprime `a`, `b ≥ 1` and `n ≠ 0` is not a rounding boundary. -/
theorem not_mem_floatSet_ratPow_of_not_cheap (p : ℕ) [NeZero p] {a b : AzNat} (ha : a ≠ 0)
    (hb : b ≠ 0) (hcop : Nat.Coprime a.toNat b.toNat) {n : AzInt} (hn : n ≠ 0)
    (hc : ratPowIntCheap a b n p = false) {σ : ℝ} (hσ : |σ| = 1) :
    ((σ * ((a.toNat : ℝ) / b.toNat) ^ n.toInt : ℝ) : EReal) ∉ floatSet (p + 1) := by
  -- the numerator and denominator of the result, by the sign of `n`
  obtain ⟨A, B, hAB, hval⟩ : ∃ A B : AzNat, ((A = a ∧ B = b) ∨ (A = b ∧ B = a)) ∧
      ((a.toNat : ℝ) / b.toNat) ^ n.toInt = ((A.toNat : ℝ) / B.toNat) ^ (n.toInt.natAbs : ℕ) := by
    rcases le_or_gt 0 n.toInt with hpos | hneg
    · exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, by rw [← zpow_natCast, Int.natAbs_of_nonneg hpos]⟩
    · refine ⟨b, a, Or.inr ⟨rfl, rfl⟩, ?_⟩
      rw [← zpow_natCast, Int.ofNat_natAbs_of_nonpos hneg.le, zpow_neg, ← inv_zpow, inv_div]
  have hA0 : A ≠ 0 := by rcases hAB with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have hB0 : B ≠ 0 := by rcases hAB with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  have hcopAB : Nat.Coprime A.toNat B.toNat := by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcop
    · exact hcop.symm
  have hcA : powIntCheap A n p = false ∨ powIntCheap B n p = false := by
    unfold ratPowIntCheap at hc
    rw [Bool.and_eq_false_iff] at hc
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hc
    · exact hc.symm
  rw [hval]
  set k := n.toInt.natAbs with hk
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (toInt_ne_zero_of_ne_zero hn))
  obtain ⟨hAdec, hAodd⟩ := splitOdd_spec A hA0
  obtain ⟨hBdec, hBodd⟩ := splitOdd_spec B hB0
  set A' := (splitOdd A).1.toNat with hA'
  set B' := (splitOdd B).1.toNat with hB'
  set cA := (splitOdd A).2 with hcA'
  set cB := (splitOdd B).2 with hcB'
  have hA'1 : 1 ≤ A' := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hAodd; simp at hAodd)
  have hB'1 : 1 ≤ B' := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hBodd; simp at hBodd)
  have hcopAB' : Nat.Coprime A' B' :=
    Nat.Coprime.coprime_dvd_left ⟨2 ^ cA, hAdec⟩
      (Nat.Coprime.coprime_dvd_right ⟨2 ^ cB, hBdec⟩ hcopAB)
  -- the value: `σ A'^k 2^(cA k − cB k) / B'^k`
  have heq : σ * ((A.toNat : ℝ) / B.toNat) ^ k
      = σ * ((A' ^ k : ℕ) : ℝ) * (2 : ℝ) ^ ((cA : ℤ) * k - (cB : ℤ) * k) / ((B' ^ k : ℕ) : ℝ) := by
    rw [hAdec, hBdec]
    push_cast
    have h2 : (2 : ℝ) ^ ((cA : ℤ) * k - (cB : ℤ) * k)
        = (2 : ℝ) ^ (cA * k) / (2 : ℝ) ^ (cB * k) := by
      rw [zpow_sub₀ (by norm_num), ← zpow_natCast, ← zpow_natCast]
      push_cast
      rfl
    rw [h2, div_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    have hB'0 : (B' : ℝ) ^ k ≠ 0 := by positivity
    have h20 : (2 : ℝ) ^ (cB * k) ≠ 0 := by positivity
    field_simp
  rw [heq]
  by_cases hB'3 : 3 ≤ B'
  · -- not dyadic
    exact not_mem_floatSet_of_div_odd_coprime p (by positivity) hBodd.pow
      (hB'3.trans (Nat.le_self_pow (by omega) _)) (hcopAB'.pow k k) _ hσ
  · -- `B' = 1`: the `A` part is the non-cheap one
    have hB'1' : B' = 1 := by
      rcases hBodd with ⟨m, hm⟩; omega
    have hcheapB : powIntCheap B n p = true := by
      unfold powIntCheap
      rw [decide_eq_true_iff, AzNat.le_iff_toNat_le, AzNat.toNat_mul, AzNat.toNat_ofNat,
        AzNat.toNat_ofNat, ← AzNat.size_toNat, ← hB', hB'1']
      simp
    have hcheapA : powIntCheap A n p = false := by
      rcases hcA with h | h
      · exact h
      · rw [h] at hcheapB; exact absurd hcheapB (by simp)
    have hlt := lt_of_powIntCheap_false hcheapA
    rw [← hk] at hlt
    have hsz2 : 2 ≤ (splitOdd A).1.size := by
      by_contra hlt2
      push Not at hlt2
      have : (splitOdd A).1.size - 1 = 0 := by omega
      rw [this, mul_zero] at hlt
      omega
    have hge : 2 ^ ((splitOdd A).1.size - 1) ≤ A' := by
      rw [hA', ← AzNat.size_toNat]
      exact Nat.lt_size.mp (by rw [AzNat.size_toNat]; omega)
    have hbig : 2 ^ (p + 1) ≤ A' ^ k := by
      calc 2 ^ (p + 1) ≤ 2 ^ (k * ((splitOdd A).1.size - 1)) :=
            Nat.pow_le_pow_right (by norm_num) hlt.le
        _ = (2 ^ ((splitOdd A).1.size - 1)) ^ k := by rw [← pow_mul, mul_comm]
        _ ≤ A' ^ k := Nat.pow_le_pow_left hge k
    have heq' : σ * ((A' ^ k : ℕ) : ℝ) * (2 : ℝ) ^ ((cA : ℤ) * k - (cB : ℤ) * k)
        / ((B' ^ k : ℕ) : ℝ)
        = σ * ((A' ^ k : ℕ) : ℝ) * (2 : ℝ) ^ ((cA : ℤ) * k - (cB : ℤ) * k) := by
      rw [hB'1', one_pow, Nat.cast_one, div_one]
    rw [heq']
    exact not_mem_floatSet_of_odd_mul p hAodd.pow hbig _ hσ

end Azurite.AzFloat
