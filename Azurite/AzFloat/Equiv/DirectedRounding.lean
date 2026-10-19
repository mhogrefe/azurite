/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Agm
import Azurite.AzFloat.Equiv.GaussConstant
import Azurite.AzFloat.Equiv.Ziv

/-!
# Quantitative directed rounding

Rounding a nonnegative real `x` down or up at precision `w` moves it by at most one ulp, and an
ulp of `x` is at most `2x · 2^(−w)` (`roundVal_floor_err`, `roundVal_ceiling_err`).  The
operation-level versions (`addFloor_err`, …, `divCeiling_err`) give, for each directed
`addPrecRound`/`subPrecRound`/`mulPrecRound`/`sqrPrecRound`/`sqrtPrecRound`/`divPrecRound` of
floats with real values, a real value of the result enclosing the exact result from the right
side with this error (`FloorOf`, `CeilOf`).  They are the raw material for the width analysis
of interval iterations (Brent–Salamin `π`).
-/

namespace Azurite.AzFloat

open RoundingTarget

/-- `r` is a rounding down of `x ≥ 0` at precision `w`: `0 ≤ r ≤ x ≤ r + 2x·2^(−w)`. -/
def FloorOf (w : ℕ) (x r : ℝ) : Prop := 0 ≤ r ∧ r ≤ x ∧ x ≤ r + 2 * x * (1 / 2 : ℝ) ^ w

/-- `r` is a rounding up of `x ≥ 0` at precision `w`: `x ≤ r ≤ x + 2x·2^(−w)`. -/
def CeilOf (w : ℕ) (x r : ℝ) : Prop := x ≤ r ∧ r ≤ x + 2 * x * (1 / 2 : ℝ) ^ w

theorem FloorOf.nonneg {w : ℕ} {x r : ℝ} (h : FloorOf w x r) : 0 ≤ r := h.1
theorem FloorOf.le {w : ℕ} {x r : ℝ} (h : FloorOf w x r) : r ≤ x := h.2.1
theorem FloorOf.ge {w : ℕ} {x r : ℝ} (h : FloorOf w x r) : x ≤ r + 2 * x * (1 / 2 : ℝ) ^ w :=
  h.2.2
theorem CeilOf.ge {w : ℕ} {x r : ℝ} (h : CeilOf w x r) : x ≤ r := h.1
theorem CeilOf.le {w : ℕ} {x r : ℝ} (h : CeilOf w x r) : r ≤ x + 2 * x * (1 / 2 : ℝ) ^ w := h.2

/-- Rounding down with an absolute error bound from a bound `x ≤ B`. -/
theorem FloorOf.ge_of_le {w : ℕ} {x r B : ℝ} (h : FloorOf w x r) (hB : x ≤ B) :
    x ≤ r + 2 * B * (1 / 2 : ℝ) ^ w := by
  have := h.ge
  have h2 : 2 * x * (1 / 2 : ℝ) ^ w ≤ 2 * B * (1 / 2 : ℝ) ^ w := by
    gcongr
  linarith

theorem CeilOf.le_of_le {w : ℕ} {x r B : ℝ} (h : CeilOf w x r) (hB : x ≤ B) :
    r ≤ x + 2 * B * (1 / 2 : ℝ) ^ w := by
  have := h.le
  have h2 : 2 * x * (1 / 2 : ℝ) ^ w ≤ 2 * B * (1 / 2 : ℝ) ^ w := by
    gcongr
  linarith

/-- The truncation error of `x ≥ 0` at precision `w` is at most `2x · 2^(−w)`. -/
theorem floor_data (w : ℕ) [NeZero w] {x : ℝ} (hx : 0 ≤ x) :
    ∃ yv εv : ℝ, (roundVal w .Floor (some (x : EReal))).1.toVal = some (yv : EReal) ∧
      FloorOf w x yv ∧ x ≤ yv + εv ∧ 0 ≤ εv ∧ εv ≤ 2 * x * (1 / 2 : ℝ) ^ w ∧
      ((yv + εv : ℝ) : EReal) ∈ floatSet w := by
  obtain ⟨yv, εv, hy, -, hyx, hxy, -, hε0, hεeq, hmem⟩ := truncError_spec w x
  obtain ⟨v, hv, -, hv0⟩ := roundVal_floor_spec w x
  have hvy : v = yv := by
    have := hv.symm.trans hy
    exact EReal.coe_eq_coe_iff.mp (Option.some_injective _ this)
  subst hvy
  have hy0 : 0 ≤ v := hv0 hx
  have hεle : εv ≤ 2 * x * (1 / 2 : ℝ) ^ w := by
    rcases eq_or_ne εv 0 with h0 | h0
    · rw [h0]; positivity
    · obtain ⟨e, he, he1, -⟩ := hεeq h0
      rw [abs_of_nonneg hy0] at he1
      have hpow : (2 : ℝ) ^ (e - (w : ℤ)) = 2 ^ (e - 1) * (2 * (1 / 2 : ℝ) ^ w) := by
        rw [one_div_pow, one_div, ← zpow_natCast, ← zpow_neg, ← zpow_one_add₀ (by norm_num),
          ← zpow_add₀ (by norm_num)]
        congr 1; ring
      rw [he, hpow]
      have h2 : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ w := by positivity
      calc (2 : ℝ) ^ (e - 1) * (2 * (1 / 2 : ℝ) ^ w) ≤ v * (2 * (1 / 2 : ℝ) ^ w) :=
            mul_le_mul_of_nonneg_right he1 h2
        _ ≤ x * (2 * (1 / 2 : ℝ) ^ w) := mul_le_mul_of_nonneg_right hyx h2
        _ = 2 * x * (1 / 2 : ℝ) ^ w := by ring
  exact ⟨v, εv, hy, ⟨hy0, hyx, by linarith⟩, hxy, hε0, hεle, hmem⟩

theorem roundVal_floor_err (w : ℕ) [NeZero w] {x : ℝ} (hx : 0 ≤ x) :
    ∃ r : ℝ, (roundVal w .Floor (some (x : EReal))).1.toVal = some (r : EReal) ∧ FloorOf w x r := by
  obtain ⟨yv, -, hy, hf, -⟩ := floor_data w hx
  exact ⟨yv, hy, hf⟩

theorem roundVal_ceiling_err (w : ℕ) [NeZero w] {x : ℝ} (hx : 0 ≤ x) :
    ∃ r : ℝ, (roundVal w .Ceiling (some (x : EReal))).1.toVal = some (r : EReal) ∧
      CeilOf w x r := by
  obtain ⟨yv, εv, -, hf, hxy, -, hεle, hmem⟩ := floor_data w hx
  obtain ⟨v, hv⟩ : ∃ v : ℝ, ((v : ℝ) : EReal) = (roundCeiling (floatSet w) x).val := by
    rw [val_roundCeiling_floatSet]; exact precisionSet_exists_real _
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [(roundVal_coe w .Ceiling x).1]; exact congrArg some hv.symm
  · have := (isLeast_roundCeiling (floatSet w) x).1.2
    rw [← hv] at this
    exact EReal.coe_le_coe_iff.mp this
  · have := (isLeast_roundCeiling (floatSet w) x).2 ⟨hmem, EReal.coe_le_coe_iff.mpr hxy⟩
    rw [← hv] at this
    have h1 := EReal.coe_le_coe_iff.mp this
    linarith [hf.le]

/-! ### Operations -/

variable {u v : AzFloat} {uv vv : ℝ}

theorem Spec.sub_coe_coe (x y : ℝ) :
    Spec.sub (x : EReal) (y : EReal) = some ((x - y : ℝ) : EReal) := by
  unfold Spec.sub
  rw [← EReal.coe_neg, Spec.add_coe_coe, sub_eq_add_neg]

theorem addFloor_err (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] (h : 0 ≤ uv + vv) :
    ∃ r : ℝ, (addPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ FloorOf w (uv + vv) r := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact roundVal_floor_err w h

theorem addCeiling_err (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] (h : 0 ≤ uv + vv) :
    ∃ r : ℝ, (addPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ CeilOf w (uv + vv) r := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact roundVal_ceiling_err w h

/-- Rounding a difference down, without a sign assumption: the result is below the difference
and nonnegative when the difference is. -/
theorem subFloor_le (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (subPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv - vv ∧
      (0 ≤ uv - vv → 0 ≤ r) := by
  rw [subPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.sub_coe_coe]
  exact roundVal_floor_spec w _

theorem subFloor_err (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] (h : 0 ≤ uv - vv) :
    ∃ r : ℝ, (subPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ FloorOf w (uv - vv) r := by
  rw [subPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.sub_coe_coe]
  exact roundVal_floor_err w h

theorem subCeiling_err (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] (h : 0 ≤ uv - vv) :
    ∃ r : ℝ, (subPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ CeilOf w (uv - vv) r := by
  rw [subPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.sub_coe_coe]
  exact roundVal_ceiling_err w h

theorem mulFloor_err (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] (h : 0 ≤ uv * vv) :
    ∃ r : ℝ, (mulPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ FloorOf w (uv * vv) r := by
  rw [mulPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.mul_coe_coe]
  exact roundVal_floor_err w h

theorem mulCeiling_err (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] (h : 0 ≤ uv * vv) :
    ∃ r : ℝ, (mulPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ CeilOf w (uv * vv) r := by
  rw [mulPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.mul_coe_coe]
  exact roundVal_ceiling_err w h

theorem sqrFloor_err (hu : u.toVal = some (uv : EReal)) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (sqrPrecRound u w .Floor).1.toVal = some (r : EReal) ∧ FloorOf w (uv * uv) r := by
  rw [sqrPrecRound_eq_liftE, liftE, liftVal, hu, Option.bind_some, ← EReal.coe_mul]
  exact roundVal_floor_err w (mul_self_nonneg uv)

theorem sqrCeiling_err (hu : u.toVal = some (uv : EReal)) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (sqrPrecRound u w .Ceiling).1.toVal = some (r : EReal) ∧ CeilOf w (uv * uv) r := by
  rw [sqrPrecRound_eq_liftE, liftE, liftVal, hu, Option.bind_some, ← EReal.coe_mul]
  exact roundVal_ceiling_err w (mul_self_nonneg uv)

theorem sqrtFloor_err (hu : u.toVal = some (uv : EReal)) (h0 : 0 ≤ uv) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (sqrtPrecRound u w .Floor).1.toVal = some (r : EReal) ∧
      FloorOf w (Real.sqrt uv) r := by
  rw [sqrtPrecRound_eq_liftVal, liftVal, hu, Option.bind_some, Spec.sqrt_coe uv h0]
  exact roundVal_floor_err w (Real.sqrt_nonneg uv)

theorem sqrtCeiling_err (hu : u.toVal = some (uv : EReal)) (h0 : 0 ≤ uv) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (sqrtPrecRound u w .Ceiling).1.toVal = some (r : EReal) ∧
      CeilOf w (Real.sqrt uv) r := by
  rw [sqrtPrecRound_eq_liftVal, liftVal, hu, Option.bind_some, Spec.sqrt_coe uv h0]
  exact roundVal_ceiling_err w (Real.sqrt_nonneg uv)

theorem divFloor_err (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (hv0 : 0 < vv) (hu0 : 0 ≤ uv) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (divPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ FloorOf w (uv / vv) r := by
  rw [divPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.div_coe_coe uv vv hv0.ne']
  exact roundVal_floor_err w (div_nonneg hu0 hv0.le)

theorem divCeiling_err (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (hv0 : 0 < vv) (hu0 : 0 ≤ uv) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (divPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧
      CeilOf w (uv / vv) r := by
  rw [divPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.div_coe_coe uv vv hv0.ne']
  exact roundVal_ceiling_err w (div_nonneg hu0 hv0.le)

/-! ### Exact operations -/

/-- A shift by an arbitrary `AzInt` multiplies the value by the power of two. -/
theorem toVal_shiftLeft_of_toVal (hu : u.toVal = some (uv : EReal)) (k : AzInt) :
    (u <<< k).toVal = some ((uv * (2 : ℝ) ^ k.toInt : ℝ) : EReal) := by
  show (shiftLeft u k).toVal = _
  rw [toVal_shiftLeft, hu, Option.map_some, EReal.coe_mul]

theorem toVal_sign_of_isNegative {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    (x.isNegative = true → xv < 0) ∧ (x.isNegative = false → 0 ≤ xv) := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero =>
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    simp only [toVal_zero, Option.some.injEq] at hx
    have : xv = 0 := by exact_mod_cast hx.symm
    rw [this]
  | finite s e q m h =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    subst hx
    have hneg : (finite s e q m h).isNegative = !s := rfl
    rw [hneg]
    cases s with
    | true =>
      refine ⟨fun h' => absurd h' (by decide), fun _ => (finiteVal_true_pos e h).le⟩
    | false =>
      refine ⟨fun _ => ?_, fun h' => absurd h' (by decide)⟩
      rw [finiteVal_false]
      exact neg_neg_of_pos (finiteVal_true_pos e h)


/-! ### Signed values: the error is at most `2|x| · 2^(−w)` on either side -/

/-- The floor of `−x` is the negative of the ceiling of `x` (the float set is symmetric). -/
theorem val_roundFloor_neg (w : ℕ) [NeZero w] (x : ℝ) :
    (roundFloor (floatSet w) (-x)).val = -(roundCeiling (floatSet w) x).val := by
  apply (isGreatest_roundFloor (floatSet w) (-x)).unique
  constructor
  · refine ⟨floatSet_neg_mem w (isLeast_roundCeiling (floatSet w) x).1.1, ?_⟩
    have := (isLeast_roundCeiling (floatSet w) x).1.2
    rw [EReal.coe_neg]
    exact EReal.neg_le_neg_iff.mpr this
  · rintro s ⟨hs, hsx⟩
    have h1 : -s ∈ floatSet w := floatSet_neg_mem w hs
    rw [EReal.coe_neg] at hsx
    have h2 : (x : EReal) ≤ -s := EReal.le_neg_of_le_neg hsx
    exact EReal.le_neg_of_le_neg ((isLeast_roundCeiling (floatSet w) x).2 ⟨h1, h2⟩)

theorem roundVal_floor_abs (w : ℕ) [NeZero w] (x : ℝ) :
    ∃ v : ℝ, (roundVal w .Floor (some (x : EReal))).1.toVal = some (v : EReal) ∧ v ≤ x ∧
      x ≤ v + 2 * |x| * (1 / 2 : ℝ) ^ w := by
  rcases le_or_gt 0 x with hx | hx
  · obtain ⟨v, hv, hf⟩ := roundVal_floor_err w hx
    exact ⟨v, hv, hf.le, by rw [abs_of_nonneg hx]; exact hf.ge⟩
  · obtain ⟨c, hc, hcf⟩ := roundVal_ceiling_err w (neg_nonneg.mpr hx.le)
    refine ⟨-c, ?_, ?_, ?_⟩
    · rw [(roundVal_coe w .Floor x).1]
      have e : (round (floatSet w) .Floor x).val = (roundFloor (floatSet w) x).val := rfl
      have e2 : (round (floatSet w) .Ceiling (-x)).val = (roundCeiling (floatSet w) (-x)).val :=
        rfl
      rw [(roundVal_coe w .Ceiling (-x)).1, Option.some.injEq, e2] at hc
      have := val_roundFloor_neg w (-x)
      rw [neg_neg] at this
      rw [e, this, hc, EReal.coe_neg]
    · linarith [hcf.ge]
    · rw [abs_of_neg hx]; linarith [hcf.le]

theorem roundVal_ceiling_abs (w : ℕ) [NeZero w] (x : ℝ) :
    ∃ v : ℝ, (roundVal w .Ceiling (some (x : EReal))).1.toVal = some (v : EReal) ∧ x ≤ v ∧
      v ≤ x + 2 * |x| * (1 / 2 : ℝ) ^ w := by
  rcases le_or_gt 0 x with hx | hx
  · obtain ⟨v, hv, hc⟩ := roundVal_ceiling_err w hx
    exact ⟨v, hv, hc.ge, by rw [abs_of_nonneg hx]; exact hc.le⟩
  · obtain ⟨f, hf, hff⟩ := roundVal_floor_err w (neg_nonneg.mpr hx.le)
    refine ⟨-f, ?_, ?_, ?_⟩
    · rw [(roundVal_coe w .Ceiling x).1]
      have e : (round (floatSet w) .Ceiling x).val = (roundCeiling (floatSet w) x).val := rfl
      have e2 : (round (floatSet w) .Floor (-x)).val = (roundFloor (floatSet w) (-x)).val := rfl
      rw [(roundVal_coe w .Floor (-x)).1, Option.some.injEq, e2] at hf
      have := val_roundFloor_neg w x
      rw [hf] at this
      have h2 : (roundCeiling (floatSet w) x).val = -((f : ℝ) : EReal) := by
        rw [this, neg_neg]
      rw [e, h2, EReal.coe_neg]
    · linarith [hff.le]
    · rw [abs_of_neg hx]; linarith [hff.ge]

theorem subFloor_abs (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (subPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv - vv ∧
      uv - vv ≤ r + 2 * |uv - vv| * (1 / 2 : ℝ) ^ w := by
  rw [subPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.sub_coe_coe]
  exact roundVal_floor_abs w _

theorem subCeiling_abs (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (subPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv - vv ≤ r ∧
      r ≤ uv - vv + 2 * |uv - vv| * (1 / 2 : ℝ) ^ w := by
  rw [subPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.sub_coe_coe]
  exact roundVal_ceiling_abs w _

theorem addFloor_abs (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (addPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv + vv ∧
      uv + vv ≤ r + 2 * |uv + vv| * (1 / 2 : ℝ) ^ w := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact roundVal_floor_abs w _

theorem addCeiling_abs (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (addPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv + vv ≤ r ∧
      r ≤ uv + vv + 2 * |uv + vv| * (1 / 2 : ℝ) ^ w := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact roundVal_ceiling_abs w _

/-- Changing the precision of a nonnegative float with `Floor`: within `2x·2^(−k)` below. -/
theorem setPrecFloor_err {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : 0 ≤ xv)
    (k : ℕ) [NeZero k] :
    ∃ r : ℝ, (setPrecRound x k .Floor).1.toVal = some (r : EReal) ∧ FloorOf k xv r := by
  rw [setPrecRound_eq_roundVal hx]
  exact roundVal_floor_err k hx0

/-- Changing the precision of a nonnegative float with `Ceiling`: within `2x·2^(−k)` above. -/
theorem setPrecCeiling_err {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : 0 ≤ xv) (k : ℕ) [NeZero k] :
    ∃ r : ℝ, (setPrecRound x k .Ceiling).1.toVal = some (r : EReal) ∧ CeilOf k xv r := by
  rw [setPrecRound_eq_roundVal hx]
  exact roundVal_ceiling_err k hx0

theorem divFloor_abs (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (hv0 : vv ≠ 0) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (divPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv / vv ∧
      uv / vv ≤ r + 2 * |uv / vv| * (1 / 2 : ℝ) ^ w := by
  rw [divPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.div_coe_coe uv vv hv0]
  exact roundVal_floor_abs w _

theorem divCeiling_abs (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (hv0 : vv ≠ 0) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (divPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv / vv ≤ r ∧
      r ≤ uv / vv + 2 * |uv / vv| * (1 / 2 : ℝ) ^ w := by
  rw [divPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.div_coe_coe uv vv hv0]
  exact roundVal_ceiling_abs w _

theorem ofAzRatRound_floor_abs (q : AzRat) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (ofAzRatRound q w .Floor).1.toVal = some (r : EReal) ∧
      r ≤ ((AzRat.toRat q : ℚ) : ℝ) ∧
      ((AzRat.toRat q : ℚ) : ℝ) ≤ r + 2 * |((AzRat.toRat q : ℚ) : ℝ)| * (1 / 2 : ℝ) ^ w := by
  rw [ofAzRatRound_eq_roundVal]
  exact roundVal_floor_abs w _

theorem ofAzRatRound_ceiling_abs (q : AzRat) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (ofAzRatRound q w .Ceiling).1.toVal = some (r : EReal) ∧
      ((AzRat.toRat q : ℚ) : ℝ) ≤ r ∧
      r ≤ ((AzRat.toRat q : ℚ) : ℝ) + 2 * |((AzRat.toRat q : ℚ) : ℝ)| * (1 / 2 : ℝ) ^ w := by
  rw [ofAzRatRound_eq_roundVal]
  exact roundVal_ceiling_abs w _

end Azurite.AzFloat
