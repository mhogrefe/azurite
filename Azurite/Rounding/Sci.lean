/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Rounding.Int

/-!
# Rounding targets for scientific-notation output

The sets of values representable by `toSci` (`docs/to_sci_plan.md`), as `RoundingTarget`s:

* `scaleSet b s`: the numbers with at most `s` base-`b` digits after the point,
  `{ m / b^s : m ∈ ℤ }` — a rescaled copy of `intSet`.  `val_round_scaleSet` says rounding to
  it is rounding `x · b^s` to an integer and scaling back, for every mode (the tiebreak is the
  integer tiebreak on the scaled coordinates).
-/

namespace Azurite

namespace RoundingTarget

/-! ### `scaleSet` -/

/-- The multiples of `b^(−s)` in `EReal`. -/
def scaleSet (b s : ℕ) : Set EReal :=
  {e | ∃ m : ℤ, (((m : ℝ) / (b : ℝ) ^ s : ℝ) : EReal) = e}

variable {b s : ℕ}

/-- The integer coordinate `m` of an element `m / b^s` of `scaleSet b s`. Noncomputable. -/
noncomputable def toScaled (a : ↥(scaleSet b s)) : ℤ := Classical.choose a.property

lemma toScaled_spec (a : ↥(scaleSet b s)) :
    (((toScaled a : ℝ) / (b : ℝ) ^ s : ℝ) : EReal) = a.val :=
  Classical.choose_spec a.property

/-- An integer as an element of `intSet`. -/
noncomputable def ofIntSet (z : ℤ) : ↥intSet := ⟨((z : ℝ) : EReal), ⟨z, rfl⟩⟩

@[simp] lemma toInt_ofIntSet (z : ℤ) : toInt (ofIntSet z) = z :=
  toInt_eq_of_val rfl

/-- An integer coordinate as an element of `scaleSet b s`. -/
noncomputable def ofScaled (b s : ℕ) (m : ℤ) : ↥(scaleSet b s) :=
  ⟨(((m : ℝ) / (b : ℝ) ^ s : ℝ) : EReal), ⟨m, rfl⟩⟩

lemma toScaled_eq_of_val [NeZero b] {a : ↥(scaleSet b s)} {m : ℤ}
    (h : (((m : ℝ) / (b : ℝ) ^ s : ℝ) : EReal) = a.val) : toScaled a = m := by
  have hb : (0 : ℝ) < (b : ℝ) ^ s := by
    have : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne b)
    positivity
  have heq : (((toScaled a : ℝ) / (b : ℝ) ^ s : ℝ) : EReal)
      = (((m : ℝ) / (b : ℝ) ^ s : ℝ) : EReal) := (toScaled_spec a).trans h.symm
  have heq' : (toScaled a : ℝ) / (b : ℝ) ^ s = (m : ℝ) / (b : ℝ) ^ s := EReal.coe_eq_coe_iff.mp heq
  have := (div_left_inj' hb.ne').mp heq'
  exact_mod_cast this

@[simp] lemma toScaled_ofScaled [NeZero b] (m : ℤ) : toScaled (ofScaled b s m) = m :=
  toScaled_eq_of_val rfl

/-- The tiebreak: the integer tiebreak on the scaled coordinates. -/
noncomputable def scaleTiebreak (a c : ↥(scaleSet b s)) : ↥(scaleSet b s) :=
  ofScaled b s (toInt (intTiebreak (ofIntSet (toScaled a)) (ofIntSet (toScaled c))))

section
variable [NeZero b]

private lemma b_pow_pos (b s : ℕ) [NeZero b] : (0 : ℝ) < (b : ℝ) ^ s := by
  have : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne b)
  positivity

/-- `m / b^s ≤ x ↔ m ≤ ⌊x b^s⌋`. -/
private lemma div_le_iff_le_floor (m : ℤ) (x : ℝ) :
    (m : ℝ) / (b : ℝ) ^ s ≤ x ↔ m ≤ ⌊x * (b : ℝ) ^ s⌋ := by
  rw [div_le_iff₀ (b_pow_pos b s), Int.le_floor]

/-- `x ≤ m / b^s ↔ ⌈x b^s⌉ ≤ m`. -/
private lemma le_div_iff_ceil_le (m : ℤ) (x : ℝ) :
    x ≤ (m : ℝ) / (b : ℝ) ^ s ↔ ⌈x * (b : ℝ) ^ s⌉ ≤ m := by
  rw [le_div_iff₀ (b_pow_pos b s), Int.ceil_le]

noncomputable instance scaleRoundingTarget : RoundingTarget (scaleSet b s) where
  existsLeastGE x := by
    refine ⟨(((⌈x * (b : ℝ) ^ s⌉ : ℝ) / (b : ℝ) ^ s : ℝ) : EReal), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · exact EReal.coe_le_coe_iff.mpr ((le_div_iff_ceil_le _ x).mpr (le_refl _))
    · rintro e ⟨⟨m, rfl⟩, hm⟩
      have hm' : x ≤ (m : ℝ) / (b : ℝ) ^ s := EReal.coe_le_coe_iff.mp hm
      have hle : ⌈x * (b : ℝ) ^ s⌉ ≤ m := (le_div_iff_ceil_le m x).mp hm'
      have hleR : ((⌈x * (b : ℝ) ^ s⌉ : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
      exact EReal.coe_le_coe_iff.mpr (div_le_div_of_nonneg_right hleR (b_pow_pos b s).le)
  existsGreatestLE x := by
    refine ⟨(((⌊x * (b : ℝ) ^ s⌋ : ℝ) / (b : ℝ) ^ s : ℝ) : EReal), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · exact EReal.coe_le_coe_iff.mpr ((div_le_iff_le_floor _ x).mpr (le_refl _))
    · rintro e ⟨⟨m, rfl⟩, hm⟩
      have hm' : (m : ℝ) / (b : ℝ) ^ s ≤ x := EReal.coe_le_coe_iff.mp hm
      have hle : m ≤ ⌊x * (b : ℝ) ^ s⌋ := (div_le_iff_le_floor m x).mp hm'
      have hleR : (m : ℝ) ≤ ((⌊x * (b : ℝ) ^ s⌋ : ℤ) : ℝ) := by exact_mod_cast hle
      exact EReal.coe_le_coe_iff.mpr (div_le_div_of_nonneg_right hleR (b_pow_pos b s).le)
  tiebreak := scaleTiebreak
  tiebreak_mem a c := by
    unfold scaleTiebreak
    have hmem := RoundingTarget.tiebreak_mem (S := intSet) (ofIntSet (toScaled a))
      (ofIntSet (toScaled c))
    change intTiebreak _ _ = _ ∨ intTiebreak _ _ = _ at hmem
    rcases hmem with h | h
    · left
      apply Subtype.ext
      rw [show (ofScaled b s (toInt (intTiebreak (ofIntSet (toScaled a)) (ofIntSet (toScaled c))))).val
        = (((toInt (intTiebreak (ofIntSet (toScaled a)) (ofIntSet (toScaled c))) : ℝ)
          / (b : ℝ) ^ s : ℝ) : EReal) from rfl, h, toInt_ofIntSet, toScaled_spec]
    · right
      apply Subtype.ext
      rw [show (ofScaled b s (toInt (intTiebreak (ofIntSet (toScaled a)) (ofIntSet (toScaled c))))).val
        = (((toInt (intTiebreak (ofIntSet (toScaled a)) (ofIntSet (toScaled c))) : ℝ)
          / (b : ℝ) ^ s : ℝ) : EReal) from rfl, h, toInt_ofIntSet, toScaled_spec]

/-- The floor in `scaleSet b s` is `⌊x b^s⌋ / b^s`. -/
lemma val_roundFloor_scaleSet (x : ℝ) :
    (roundFloor (scaleSet b s) x).val = (((⌊x * (b : ℝ) ^ s⌋ : ℝ) / (b : ℝ) ^ s : ℝ) : EReal) := by
  apply (isGreatest_roundFloor (scaleSet b s) x).unique
  refine ⟨⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · exact EReal.coe_le_coe_iff.mpr ((div_le_iff_le_floor _ x).mpr (le_refl _))
  · rintro e ⟨⟨m, rfl⟩, hm⟩
    have hm' : (m : ℝ) / (b : ℝ) ^ s ≤ x := EReal.coe_le_coe_iff.mp hm
    have hle : m ≤ ⌊x * (b : ℝ) ^ s⌋ := (div_le_iff_le_floor m x).mp hm'
    have hleR : (m : ℝ) ≤ ((⌊x * (b : ℝ) ^ s⌋ : ℤ) : ℝ) := by exact_mod_cast hle
    exact EReal.coe_le_coe_iff.mpr (div_le_div_of_nonneg_right hleR (b_pow_pos b s).le)

/-- The ceiling in `scaleSet b s` is `⌈x b^s⌉ / b^s`. -/
lemma val_roundCeiling_scaleSet (x : ℝ) :
    (roundCeiling (scaleSet b s) x).val
      = (((⌈x * (b : ℝ) ^ s⌉ : ℝ) / (b : ℝ) ^ s : ℝ) : EReal) := by
  apply (isLeast_roundCeiling (scaleSet b s) x).unique
  refine ⟨⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · exact EReal.coe_le_coe_iff.mpr ((le_div_iff_ceil_le _ x).mpr (le_refl _))
  · rintro e ⟨⟨m, rfl⟩, hm⟩
    have hm' : x ≤ (m : ℝ) / (b : ℝ) ^ s := EReal.coe_le_coe_iff.mp hm
    have hle : ⌈x * (b : ℝ) ^ s⌉ ≤ m := (le_div_iff_ceil_le m x).mp hm'
    have hleR : ((⌈x * (b : ℝ) ^ s⌉ : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
    exact EReal.coe_le_coe_iff.mpr (div_le_div_of_nonneg_right hleR (b_pow_pos b s).le)

/-- `compare` is invariant under scaling both sides by a positive constant. -/
private lemma compare_mul_right (u v c : ℝ) (hc : 0 < c) :
    compare (u * c) (v * c) = compare u v := by
  rcases lt_trichotomy u v with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (mul_lt_mul_of_pos_right h hc)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (mul_lt_mul_of_pos_right h hc)]

/-- `compare` on real coercions into `EReal` is `compare` on the reals. -/
private lemma compare_coe_coe (u v : ℝ) :
    compare ((u : ℝ) : EReal) ((v : ℝ) : EReal) = compare u v := by
  rcases lt_trichotomy u v with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (EReal.coe_lt_coe_iff.mpr h)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (EReal.coe_lt_coe_iff.mpr h)]

/-- **Rounding to `scaleSet b s` is rounding `x · b^s` to an integer, scaled back.** -/
theorem val_round_scaleSet (mode : RoundingMode) (x : ℝ) :
    (round (scaleSet b s) mode x).val
      = (((toInt (round intSet mode (x * (b : ℝ) ^ s)) : ℝ) / (b : ℝ) ^ s : ℝ) : EReal) := by
  set y := x * (b : ℝ) ^ s with hy
  have hF := val_roundFloor_scaleSet (b := b) (s := s) x
  have hC := val_roundCeiling_scaleSet (b := b) (s := s) x
  have hFi : toInt (roundFloor intSet y) = ⌊y⌋ := toInt_eq_of_val (val_roundFloor_intSet y).symm
  have hCi : toInt (roundCeiling intSet y) = ⌈y⌉ :=
    toInt_eq_of_val (val_roundCeiling_intSet y).symm
  have h0 : (0 ≤ x) ↔ (0 ≤ y) := by
    rw [hy]; constructor
    · intro h; exact mul_nonneg h (b_pow_pos b s).le
    · intro h; exact nonneg_of_mul_nonneg_left h (b_pow_pos b s)
  cases mode with
  | Floor => rw [show round (scaleSet b s) .Floor x = roundFloor (scaleSet b s) x from rfl,
      show round intSet .Floor y = roundFloor intSet y from rfl, hF, hFi]
  | Ceiling => rw [show round (scaleSet b s) .Ceiling x = roundCeiling (scaleSet b s) x from rfl,
      show round intSet .Ceiling y = roundCeiling intSet y from rfl, hC, hCi]
  | Down =>
    show (if 0 ≤ x then roundFloor (scaleSet b s) x else roundCeiling (scaleSet b s) x).val
      = (((toInt (if 0 ≤ y then roundFloor intSet y else roundCeiling intSet y) : ℝ)
        / (b : ℝ) ^ s : ℝ) : EReal)
    by_cases hx : 0 ≤ x
    · rw [ite_eq_left hx, ite_eq_left (h0.mp hx), hF, hFi]
    · rw [ite_eq_right hx, ite_eq_right (fun h => hx (h0.mpr h)), hC, hCi]
  | Up =>
    show (if 0 ≤ x then roundCeiling (scaleSet b s) x else roundFloor (scaleSet b s) x).val
      = (((toInt (if 0 ≤ y then roundCeiling intSet y else roundFloor intSet y) : ℝ)
        / (b : ℝ) ^ s : ℝ) : EReal)
    by_cases hx : 0 ≤ x
    · rw [ite_eq_left hx, ite_eq_left (h0.mp hx), hC, hCi]
    · rw [ite_eq_right hx, ite_eq_right (fun h => hx (h0.mpr h)), hF, hFi]
  | Nearest =>
    show (let F := roundFloor (scaleSet b s) x
          let C := roundCeiling (scaleSet b s) x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val
      = (((toInt (let F := roundFloor intSet y
          let C := roundCeiling intSet y
          let dF : EReal := ((y : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((y : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C) : ℝ) / (b : ℝ) ^ s : ℝ) : EReal)
    simp only []
    rw [hF, hC, val_roundFloor_intSet, val_roundCeiling_intSet]
    -- The two comparisons agree.
    have hcmp : compare (((x : ℝ) : EReal) - (((⌊y⌋ : ℝ) / (b : ℝ) ^ s : ℝ) : EReal))
        ((((⌈y⌉ : ℝ) / (b : ℝ) ^ s : ℝ) : EReal) - ((x : ℝ) : EReal))
        = compare (((y : ℝ) : EReal) - ((⌊y⌋ : ℝ) : EReal)) (((⌈y⌉ : ℝ) : EReal) - ((y : ℝ) : EReal)) := by
      rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub]
      rw [compare_coe_coe, compare_coe_coe]
      rw [← compare_mul_right _ _ _ (b_pow_pos b s), sub_mul, sub_mul,
        div_mul_cancel₀ _ (b_pow_pos b s).ne', div_mul_cancel₀ _ (b_pow_pos b s).ne', ← hy]
    rw [hcmp]
    rcases h : compare (((y : ℝ) : EReal) - ((⌊y⌋ : ℝ) : EReal))
        (((⌈y⌉ : ℝ) : EReal) - ((y : ℝ) : EReal)) with _ | _ | _
    · simp only []; rw [hF, hFi]
    · -- tie
      simp only []
      show (scaleTiebreak (roundFloor (scaleSet b s) x) (roundCeiling (scaleSet b s) x)).val
        = (((toInt (intTiebreak (roundFloor intSet y) (roundCeiling intSet y)) : ℝ)
          / (b : ℝ) ^ s : ℝ) : EReal)
      unfold scaleTiebreak
      have hFs : toScaled (roundFloor (scaleSet b s) x) = ⌊y⌋ := toScaled_eq_of_val hF.symm
      have hCs : toScaled (roundCeiling (scaleSet b s) x) = ⌈y⌉ := toScaled_eq_of_val hC.symm
      rw [hFs, hCs]
      have hFe : ofIntSet ⌊y⌋ = roundFloor intSet y :=
        Subtype.ext (val_roundFloor_intSet y).symm
      have hCe : ofIntSet ⌈y⌉ = roundCeiling intSet y :=
        Subtype.ext (val_roundCeiling_intSet y).symm
      rw [hFe, hCe]
      rfl
    · simp only []; rw [hC, hCi]

end

end RoundingTarget

end Azurite
