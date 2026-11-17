/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnEncl
import Azurite.AzFloat.Equiv.LnBracket
import Azurite.AzFloat.Equiv.Interval
import Azurite.AzFloat.Equiv.DirectedRounding

/-!
# Equivalence: the logarithm of an enclosure

`lnOfEncl_core` (validity and width for a positive float lower end), `lnOfEncl_dummy` (the
dummy bracket otherwise), `lnOfEncl_valid` (one or the other), and `lnOfEncl_pos`: for an
enclosure with a positive lower end the result encloses the logarithm.
-/

namespace Azurite.AzFloat

open Real

/-- A float with a positive value is `finite true …`. -/
theorem exists_finite_true_of_toVal_pos {x : AzFloat} {v : ℝ} (hx : x.toVal = some (v : EReal))
    (hv : 0 < v) :
    ∃ (e : AzInt) (q : ℕ) (m : AzNat) (hm : FiniteValid q m), x = finite true e q m hm := by
  rcases x with _ | s | _ | ⟨s, e, q, m, hm⟩
  · simp at hx
  · simp only [toVal_infinity, Option.some.injEq] at hx
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx
    · exact absurd hx (EReal.bot_ne_coe _)
    · exact absurd hx (EReal.top_ne_coe _)
  · simp only [toVal_zero, Option.some.injEq] at hx
    exact absurd (EReal.coe_eq_zero.mp hx.symm) hv.ne'
  · cases s with
    | true => exact ⟨e, q, m, hm, rfl⟩
    | false =>
      exfalso
      simp only [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
      rw [finiteVal_false] at hx
      have := finiteVal_true_pos e hm
      linarith

/-- The dummy bracket for a lower end that is not positive. -/
theorem lnOfEncl_dummy {y : Encl} {lv : ℝ} (hl : y.1.toVal = some (lv : EReal)) (h : lv ≤ 0)
    (w : ℕ) : lnOfEncl y w = (-one, one) := by
  unfold lnOfEncl
  split
  · next e q m hv heq =>
    exfalso
    rw [heq, toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hl
    have := finiteVal_true_pos e hv
    linarith
  · rfl

/-- **The logarithm of an enclosure with a positive float lower end** `lo`: it encloses `ln v`
for `lo ≤ v ≤ hi`, with width at most
`lnEps e w + 2 (hi − lo)/lo + 2 (|ln lo| + lnEps e w + 2 (hi − lo)/lo) 2^(−w)`. -/
theorem lnOfEncl_core {e : AzInt} {q : ℕ} {m : AzNat} (hm : FiniteValid q m) {hiF : AzFloat}
    {hi v : ℝ} (hhi : hiF.toVal = some (hi : EReal)) (h1 : finiteVal true e m ≤ v) (h2 : v ≤ hi)
    {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv up : ℝ, (lnOfEncl (finite true e q m hm, hiF) w).1.toVal = some (lv : EReal) ∧
      (lnOfEncl (finite true e q m hm, hiF) w).2.toVal = some (up : EReal) ∧
      lv ≤ Real.log v ∧ Real.log v ≤ up ∧
      up - lv ≤ lnEps e.toInt w + 2 * ((hi - finiteVal true e m) / finiteVal true e m)
        + 2 * (|Real.log (finiteVal true e m)| + lnEps e.toInt w
          + 2 * ((hi - finiteVal true e m) / finiteVal true e m)) * (1 / 2 : ℝ) ^ w := by
  have : NeZero w := ⟨by omega⟩
  set lo := finiteVal true e m with hlo
  have hlo0 : 0 < lo := finiteVal_true_pos e hm
  have hloV : (finite true e q m hm).toVal = some (lo : EReal) := toVal_finite true e q m hm
  set u := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 8 := by
    calc u ≤ (1 / 2 : ℝ) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  obtain ⟨lv, hv', hlv, hhv, hl1, hl2, hlw⟩ := lnBracket_spec hw e hm
  rw [← hlo] at hl1 hl2
  have hd0 : 0 ≤ hi - lo := by linarith
  obtain ⟨dn, hdn, hdnc⟩ := subCeiling_err hhi hloV w hd0
  have hdn0 : 0 ≤ dn := hd0.trans hdnc.ge
  obtain ⟨d, hd, hdc⟩ := divCeiling_err hdn hloV hlo0 hdn0 w
  obtain ⟨up, hup, hup1, hup2⟩ := addCeiling_abs hhv hd w
  rw [← hu] at hup2
  set D := (hi - lo) / lo with hD
  have hD0 : 0 ≤ D := div_nonneg hd0 hlo0.le
  have hdnD : dn / lo ≤ D + 2 * D * u := by
    have h := div_le_div_of_nonneg_right hdnc.2 hlo0.le
    rw [← hu] at h
    calc dn / lo ≤ (hi - lo + 2 * (hi - lo) * u) / lo := h
      _ = D + 2 * D * u := by rw [hD]; ring
  have hdD : D ≤ d := (div_le_div_of_nonneg_right hdnc.ge hlo0.le).trans hdc.ge
  have hd2 : d ≤ 2 * D := by
    have h := hdc.2
    rw [← hu] at h
    have m1 : dn / lo * u ≤ (D + 2 * D * u) * u := mul_le_mul_of_nonneg_right hdnD hu0
    nlinarith [mul_nonneg hD0 hu0, mul_nonneg (mul_nonneg hD0 hu0) hu0]
  have hv0 : 0 < v := hlo0.trans_le h1
  have hlog : Real.log v ≤ Real.log lo + D := by
    have h3 := Real.log_le_sub_one_of_pos (div_pos hv0 hlo0)
    rw [Real.log_div hv0.ne' hlo0.ne'] at h3
    have h4 : v / lo - 1 ≤ D := by
      rw [hD, div_sub_one hlo0.ne']
      exact div_le_div_of_nonneg_right (by linarith) hlo0.le
    linarith
  have hlnE0 : 0 ≤ lnEps e.toInt w := by unfold lnEps; positivity
  have habs : |hv' + d| ≤ |Real.log lo| + lnEps e.toInt w + 2 * D := by
    rw [abs_le]
    have := neg_abs_le (Real.log lo)
    have := le_abs_self (Real.log lo)
    constructor <;> linarith
  have m2 := mul_le_mul_of_nonneg_right habs hu0
  have hdsimp : (lnOfEncl (finite true e q m hm, hiF) w) =
      ((lnBracket (finite true e q m hm) e w).1,
        (addPrecRound (lnBracket (finite true e q m hm) e w).2
          (divPrecRound (subPrecRound hiF (finite true e q m hm) w .Ceiling).1
            (finite true e q m hm) w .Ceiling).1 w .Ceiling).1) := rfl
  rw [hdsimp]
  refine ⟨lv, up, hlv, hup, hl1.trans (Real.log_le_log hlo0 h1), by linarith, by linarith⟩

/-- **`lnOfEncl` is the dummy bracket or encloses `ln v`**, for an enclosure of `v`. -/
theorem lnOfEncl_valid {y : Encl} {v : ℝ} (hy : IsEncl y v) {w : ℕ} (hw : 64 ≤ w) :
    lnOfEncl y w = (-one, one) ∨ IsEncl (lnOfEncl y w) (Real.log v) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := hy
  rcases le_or_gt lo 0 with hneg | hpos
  · exact Or.inl (lnOfEncl_dummy hlo hneg w)
  · right
    obtain ⟨e, q, m, hm, heq⟩ := exists_finite_true_of_toVal_pos hlo hpos
    have hyeq : y = (finite true e q m hm, y.2) := Prod.ext heq rfl
    rw [heq, toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hlo
    rw [hyeq]
    obtain ⟨lv, up, hlv, hup, k1, k2, -⟩ := lnOfEncl_core hm hhi (hlo ▸ h1) h2 hw
    exact ⟨lv, up, hlv, hup, k1, k2⟩

/-- The logarithm of an enclosure with a positive lower end encloses the logarithm. -/
theorem lnOfEncl_pos {y : Encl} {v : ℝ} (hy : IsEnclPos y v) {w : ℕ} (hw : 64 ≤ w) :
    IsEncl (lnOfEncl y w) (Real.log v) := by
  obtain ⟨lo, hi, hlo, hhi, h0, h1, h2⟩ := hy
  obtain ⟨e, q, m, hm, heq⟩ := exists_finite_true_of_toVal_pos hlo h0
  have hyeq : y = (finite true e q m hm, y.2) := Prod.ext heq rfl
  rw [heq, toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hlo
  rw [hyeq]
  obtain ⟨lv, up, hlv, hup, k1, k2, -⟩ := lnOfEncl_core hm hhi (hlo ▸ h1) h2 hw
  exact ⟨lv, up, hlv, hup, k1, k2⟩

end Azurite.AzFloat
