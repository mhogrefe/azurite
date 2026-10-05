/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Add
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Ziv
import Azurite.Rounding.Between

/-!
# Correctness of Ziv's loop

`roundVal_eq_of_between` transports the squeeze `round_between` to `roundVal`: two reals that
round to the same float with the same tag determine the rounding of everything between them.
`roundingPossible_eq` is then the correctness of MCA Algorithm 3.1 in its two-roundings form,
and `zivLoop_eq` the correctness of the loop: whenever every approximation brackets the exact
value and the fallback is exact, the loop returns `roundVal` of the exact value.

The approximations themselves are truncations, whose error is one ulp of the result:
`lt_add_ulp_of_floor` (a float whose value is the floor of `x` at its precision lies less than
one of its ulps below `x`), `eq_zero_of_roundFloor_eq_zero` (only `0` truncates to `0` — the
exponent is unbounded), and `truncError_spec` packaging both for `truncError`.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The squeeze for `roundVal` -/

/-- Two reals rounding to the same float with the same tag determine the rounding of every
value between them. -/
theorem roundVal_eq_of_between (p : ℕ) [NeZero p] (mode : RoundingMode) {lo v hi : ℝ}
    (h₁ : lo ≤ v) (h₂ : v ≤ hi)
    (h : roundVal p mode (some (lo : EReal)) = roundVal p mode (some (hi : EReal))) :
    roundVal p mode (some (v : EReal)) = roundVal p mode (some (lo : EReal)) := by
  obtain ⟨hlo1, hlo2⟩ := roundVal_coe p mode lo
  obtain ⟨hhi1, hhi2⟩ := roundVal_coe p mode hi
  obtain ⟨hv1, hv2⟩ := roundVal_coe p mode v
  have hR : (round (floatSet p) mode lo).val = (round (floatSet p) mode hi).val := by
    have := congrArg (fun z : AzFloat × Ordering => z.1.toVal) h
    simp only [hlo1, hhi1, Option.some.injEq] at this
    exact this
  have ht : compare (round (floatSet p) mode lo).val (lo : EReal)
      = compare (round (floatSet p) mode hi).val (hi : EReal) := by
    have := congrArg Prod.snd h
    rwa [hlo2, hhi2] at this
  obtain ⟨hval, htag⟩ := round_between (floatSet p) mode h₁ h₂ hR ht
  refine Prod.ext ?_ ?_
  · rw [fst_roundVal, fst_roundVal]
    show ofEReal p mode v = ofEReal p mode lo
    exact toVal_injective p (ofEReal_spec p mode v).1 (ofEReal_spec p mode lo).1
      (by rw [(ofEReal_spec p mode v).2, (ofEReal_spec p mode lo).2, hval])
  · rw [hv2, hlo2]
    exact htag

/-! ### `roundingPossible` and `zivLoop` -/

/-- When `roundingPossible` answers, it answers with the rounding of every value in
`[y, y + ε]`. -/
theorem roundingPossible_eq (p : ℕ) [NeZero p] (mode : RoundingMode) {y ε : AzFloat}
    {yv εv v : ℝ} (hy : y.toVal = some (yv : EReal)) (hε : ε.toVal = some (εv : EReal))
    (h₁ : yv ≤ v) (h₂ : v ≤ yv + εv) {r : AzFloat × Ordering}
    (h : roundingPossible y ε p mode = some r) :
    r = roundVal p mode (some (v : EReal)) := by
  unfold roundingPossible at h
  simp only at h
  split_ifs at h with heq
  · rw [Option.some.injEq] at h
    rw [setPrecRound_eq_liftE, addPrecRound_eq_liftVal₂] at heq
    unfold liftE liftVal liftVal₂ at heq
    rw [hy, hε, Option.bind_some, Option.bind_some, Option.bind_some, Spec.add_coe_coe] at heq
    rw [← h, setPrecRound_eq_liftE]
    unfold liftE liftVal
    rw [hy, Option.bind_some]
    exact (roundVal_eq_of_between p mode h₁ h₂ heq).symm

/-- Correctness of Ziv's loop: if every approximation at a positive working precision brackets
the exact value `v` and the fallback is its rounding, the loop returns the rounding of `v`. -/
theorem zivLoop_eq (p : ℕ) [NeZero p] (mode : RoundingMode) (approx : Nat → AzFloat × AzFloat)
    (exact : Unit → AzFloat × Ordering) (v : ℝ)
    (happrox : ∀ w, 0 < w → ∃ yv εv : ℝ, yv ≤ v ∧ v ≤ yv + εv ∧
      (approx w).1.toVal = some (yv : EReal) ∧ (approx w).2.toVal = some (εv : EReal))
    (hexact : exact () = roundVal p mode (some (v : EReal))) :
    ∀ (fuel w : Nat), 0 < w →
      zivLoop approx exact p mode fuel w = roundVal p mode (some (v : EReal))
  | 0, _, _ => hexact
  | fuel + 1, w, hw => by
    obtain ⟨yv, εv, h₁, h₂, hy, hε⟩ := happrox w hw
    unfold zivLoop
    simp only
    split
    · rename_i r hr
      exact roundingPossible_eq p mode hy hε h₁ h₂ hr
    · exact zivLoop_eq p mode approx exact v happrox hexact fuel (2 * w) (by omega)

/-! ### The error of a truncation -/

/-- A float whose value is the floor of `x ≠ 0` at the float's precision lies less than one of
its ulps below `x`. -/
theorem lt_add_ulp_of_floor (s : Bool) (e : AzInt) {p : ℕ} [NeZero p] {m : AzNat}
    (hv : FiniteValid p m) (x : ℝ) (hx : x ≠ 0)
    (h : ((finiteVal s e m : ℝ) : EReal) = (roundFloor (precisionSet 2 p) x).val) :
    x < finiteVal s e m + (2 : ℝ) ^ (e.toInt - p) := by
  have hle : finiteVal s e m ≤ x :=
    EReal.coe_le_coe_iff.mp (h ▸ (isGreatest_roundFloor (precisionSet 2 p) x).1.2)
  have hfv0 := finiteVal_ne_zero s e hv
  rw [val_roundFloor_precision x hx, EReal.coe_eq_coe_iff] at h
  set u := precScale 2 p x with hu
  have hu0 : 0 < u := by
    rw [hu]; unfold precScale; positivity
  -- `x < ⌊x/u⌋·u + u`
  have h1 : x < (⌊x / u⌋ : ℝ) * u + u := by
    have hlt := Int.lt_floor_add_one (x / u)
    calc x = x / u * u := (div_mul_cancel₀ x hu0.ne').symm
      _ < ((⌊x / u⌋ : ℝ) + 1) * u := mul_lt_mul_of_pos_right hlt hu0
      _ = (⌊x / u⌋ : ℝ) * u + u := by ring
  -- `u ≤ 2^(e − p)`, the scale of the float's own binade
  have h2 : u ≤ (2 : ℝ) ^ (e.toInt - p) := by
    rw [← precScale_finiteVal s e hv p, hu]
    unfold precScale
    apply zpow_le_zpow_right₀ (by norm_num)
    have hlog : Int.log 2 |x| ≤ Int.log 2 |finiteVal s e m| := by
      apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hfv0)).mp
      push_cast
      set L := Int.log 2 |x| with hL
      have hpow : (2 : ℝ) ^ L ≤ |x| := Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hx)
      rcases lt_or_gt_of_ne hx with hneg | hpos
      · rw [abs_of_neg hneg] at hpow
        rw [abs_of_neg (lt_of_le_of_lt hle hneg)]
        linarith
      · -- `2^⌊log₂ x⌋` is in the set and below `x`, so below the floor
        rw [abs_of_pos hpos] at hpow
        have hmem : (((2 : ℝ) ^ L : ℝ) : EReal) ∈ precisionSet 2 p := by
          refine Or.inr ⟨1, L, one_ne_zero, ?_, ?_⟩
          · rw [abs_one]
            exact one_lt_pow₀ (by norm_num) (NeZero.ne p)
          · simp
        have hfl := (isGreatest_precision (b := 2) (p := p) x hx).2
          ⟨hmem, EReal.coe_le_coe_iff.mpr hpow⟩
        rw [← h] at hfl
        have hfl' := EReal.coe_le_coe_iff.mp hfl
        rw [abs_of_pos (lt_of_lt_of_le (zpow_pos (by norm_num) _) hfl')]
        exact hfl'
    omega
  rw [h]
  linarith

/-- Only `0` has floor `0` at a positive precision: the exponent is unbounded. -/
theorem eq_zero_of_roundFloor_eq_zero (p : ℕ) [NeZero p] (x : ℝ)
    (h : (roundFloor (precisionSet 2 p) x).val = 0) : x = 0 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  by_contra hx
  rw [val_roundFloor_precision x hx] at h
  set u := precScale 2 p x with hu
  have hu0 : 0 < u := by
    rw [hu]; unfold precScale; positivity
  have h' : (⌊x / u⌋ : ℝ) * u = 0 := EReal.coe_eq_zero.mp h
  have hfl : ⌊x / u⌋ = 0 := by
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact_mod_cast h0
    · exact absurd h0 hu0.ne'
  obtain ⟨h0, h1⟩ := Int.floor_eq_zero_iff.mp hfl
  have hb := (abs_div_precScale_bounds (b := 2) (p := p) x hx).1
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ ((p : ℤ) - 1) := one_le_zpow₀ (by norm_num) (by omega)
  rw [abs_of_nonneg h0] at hb
  push_cast at hb
  linarith

/-- The truncation of `x` at precision `p` and its `truncError` bracket `x`: the result `y`
and the bound `ε` are reals with `y ≤ x ≤ y + ε`. -/
theorem truncError_spec (p : ℕ) [NeZero p] (x : ℝ) :
    ∃ yv εv : ℝ, (ofEReal p .Floor x).toVal = some (yv : EReal) ∧
      (truncError (ofEReal p .Floor x)).toVal = some (εv : EReal) ∧ yv ≤ x ∧ x ≤ yv + εv := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨hprec, hval⟩ := ofEReal_spec p .Floor x
  rw [val_round_floatSet] at hval
  have hfl : (round (precisionSet 2 p) .Floor x).val = (roundFloor (precisionSet 2 p) x).val :=
    rfl
  rw [hfl] at hval
  have hle : (roundFloor (precisionSet 2 p) x).val ≤ (x : EReal) :=
    (isGreatest_roundFloor (precisionSet 2 p) x).1.2
  generalize hf : ofEReal p .Floor x = f at hprec hval
  cases f with
  | nan => simp at hval
  | infinity s =>
    exfalso
    obtain ⟨r, hr⟩ := precisionSet_exists_real (roundFloor (precisionSet 2 p) x)
    rw [toVal_infinity, ← hr, Option.some.injEq] at hval
    cases s <;> simp at hval
  | zero =>
    rw [toVal_zero, Option.some.injEq] at hval
    have hx0 : x = 0 := eq_zero_of_roundFloor_eq_zero p x hval.symm
    refine ⟨0, 0, by simp, by simp [truncError, ulp?], ?_, ?_⟩ <;> simp [hx0]
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq] at hval
    have hq : q = p := by
      rcases hprec with hprec | hprec <;> simp [precision?] at hprec
      exact hprec
    subst hq
    obtain ⟨y, hy, hyv, _⟩ := ulp?_spec s e q m hv
    refine ⟨finiteVal s e m, (2 : ℝ) ^ (e.toInt - q), rfl, ?_, ?_, ?_⟩
    · simp [truncError, hy, hyv]
    · exact EReal.coe_le_coe_iff.mp (hval ▸ hle)
    · by_cases hx : x = 0
      · exfalso
        have h0 : (roundFloor (precisionSet 2 q) x).val = 0 := by
          rw [hx]
          exact val_roundFloor_of_mem _ (Or.inl (by simp))
        rw [h0] at hval
        exact finiteVal_ne_zero s e hv (EReal.coe_eq_zero.mp hval)
      · exact (lt_add_ulp_of_floor s e hv x hx hval).le

end Azurite.AzFloat
