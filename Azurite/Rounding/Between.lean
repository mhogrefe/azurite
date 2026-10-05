/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Rounding.Symmetric

/-!
# Rounding is determined by two bracketing values

The squeeze behind Ziv's strategy (Brent and Zimmermann, *Modern Computer Arithmetic*, §3.1.10):
if two reals `lo ≤ hi` round to the same element of the target *and* compare with it in the same
way (both below it, both equal to it, or both above it), then every `v` between them rounds to
that element and compares with it in that same way.  Nothing about the geometry of the target
is used — only the defining extremal properties of the floor and the ceiling, so the result
holds for any `RoundingTarget`; the case of a rounding above both ends is reduced to the case
below them by the symmetry of a `SymmetricRoundingTarget`.

* `val_round_eq_floor_or_ceiling`: every rounding is the floor or the ceiling.
* `round_between_of_lt`: the squeeze when the common rounding lies below both ends.
* `round_between`: the squeeze with the comparison tags.
-/

namespace Azurite.RoundingTarget

section Target

variable (S : Set EReal) [RoundingTarget S]

/-- Every rounding is the floor or the ceiling. -/
theorem val_round_eq_floor_or_ceiling (mode : RoundingMode) (x : ℝ) :
    (round S mode x).val = (roundFloor S x).val ∨
      (round S mode x).val = (roundCeiling S x).val := by
  cases mode with
  | Floor => exact Or.inl rfl
  | Ceiling => exact Or.inr rfl
  | Down =>
    show (if 0 ≤ x then roundFloor S x else roundCeiling S x).val = _ ∨
      (if 0 ≤ x then roundFloor S x else roundCeiling S x).val = _
    split_ifs <;> simp
  | Up =>
    show (if 0 ≤ x then roundCeiling S x else roundFloor S x).val = _ ∨
      (if 0 ≤ x then roundCeiling S x else roundFloor S x).val = _
    split_ifs <;> simp
  | Nearest =>
    show (match compare ((x : EReal) - (roundFloor S x).val) ((roundCeiling S x).val - x) with
      | .lt => roundFloor S x
      | .gt => roundCeiling S x
      | .eq => tiebreak (roundFloor S x) (roundCeiling S x)).val = _ ∨
      (match compare ((x : EReal) - (roundFloor S x).val) ((roundCeiling S x).val - x) with
      | .lt => roundFloor S x
      | .gt => roundCeiling S x
      | .eq => tiebreak (roundFloor S x) (roundCeiling S x)).val = _
    cases compare ((x : EReal) - (roundFloor S x).val) ((roundCeiling S x).val - x) with
    | lt => exact Or.inl rfl
    | gt => exact Or.inr rfl
    | eq =>
      rcases tiebreak_mem (roundFloor S x) (roundCeiling S x) with h | h <;> rw [h] <;> simp

/-- The squeeze when the common rounding `R` of `lo` and `hi` lies below both: `R` is the floor
of both ends, hence of everything between them, and no mode can pick the ceiling of `v` when it
picked the floor of the ends. -/
theorem round_between_of_lt (mode : RoundingMode) {lo v hi : ℝ}
    (h₁ : lo ≤ v) (h₂ : v ≤ hi)
    (hR : (round S mode lo).val = (round S mode hi).val)
    (hlo : (round S mode lo).val < lo) (hhi : (round S mode hi).val < hi) :
    (round S mode v).val = (round S mode lo).val := by
  obtain ⟨R, hRdef⟩ : ∃ R, R = (round S mode lo).val := ⟨_, rfl⟩
  rw [← hRdef] at hR hlo ⊢
  rw [← hR] at hhi
  have hRS : R ∈ S := hRdef ▸ (round S mode lo).property
  have h₁' : (lo : EReal) ≤ v := EReal.coe_le_coe_iff.mpr h₁
  have h₂' : (v : EReal) ≤ hi := EReal.coe_le_coe_iff.mpr h₂
  have hRv : R < (v : EReal) := lt_of_lt_of_le hlo h₁'
  -- the rounding of both ends is their floor
  have hFlo : (roundFloor S lo).val = R := by
    rcases val_round_eq_floor_or_ceiling S mode lo with h | h
    · exact (hRdef.trans h).symm
    · exact absurd (show (roundCeiling S lo).val < lo by rw [← hRdef.trans h]; exact hlo)
        (not_lt.mpr (isLeast_roundCeiling S lo).1.2)
  have hFhi : (roundFloor S hi).val = R := by
    rcases val_round_eq_floor_or_ceiling S mode hi with h | h
    · exact (hR.trans h).symm
    · exact absurd (show (roundCeiling S hi).val < hi by rw [← hR.trans h]; exact hhi)
        (not_lt.mpr (isLeast_roundCeiling S hi).1.2)
  -- hence the floor of `v` is `R`
  have hFv : (roundFloor S v).val = R := by
    apply le_antisymm
    · rw [← hFhi]
      exact (isGreatest_roundFloor S hi).2
        ⟨(roundFloor S v).property, le_trans (isGreatest_roundFloor S v).1.2 h₂'⟩
    · exact (isGreatest_roundFloor S v).2 ⟨hRS, hRv.le⟩
  -- and the ceiling of `v` is the ceiling of `hi`: nothing of `S` lies in `(R, hi]`
  have hCv : (roundCeiling S v).val = (roundCeiling S hi).val := by
    apply le_antisymm
    · exact (isLeast_roundCeiling S v).2
        ⟨(roundCeiling S hi).property, le_trans h₂' (isLeast_roundCeiling S hi).1.2⟩
    · apply (isLeast_roundCeiling S hi).2
      refine ⟨(roundCeiling S v).property, ?_⟩
      by_contra hcon
      push Not at hcon
      have hle : (roundCeiling S v).val ≤ R := by
        rw [← hFhi]
        exact (isGreatest_roundFloor S hi).2 ⟨(roundCeiling S v).property, hcon.le⟩
      exact absurd (lt_of_lt_of_le hRv (isLeast_roundCeiling S v).1.2) (not_lt.mpr hle)
  have hClo : (lo : EReal) ≤ (roundCeiling S lo).val := (isLeast_roundCeiling S lo).1.2
  have hChi : (hi : EReal) ≤ (roundCeiling S hi).val := (isLeast_roundCeiling S hi).1.2
  cases mode with
  | Floor => exact hFv
  | Ceiling =>
    rw [hRdef] at hlo
    exact absurd hlo (not_lt.mpr hClo)
  | Down =>
    by_cases hlo0 : 0 ≤ lo
    · have hv0 : 0 ≤ v := le_trans hlo0 h₁
      show (if 0 ≤ v then roundFloor S v else roundCeiling S v).val = R
      rw [ite_eq_left hv0]
      exact hFv
    · have h : (round S .Down lo).val = (roundCeiling S lo).val := by
        show (if 0 ≤ lo then roundFloor S lo else roundCeiling S lo).val = _
        rw [ite_eq_right hlo0]
      rw [h] at hRdef
      rw [hRdef] at hlo
      exact absurd hlo (not_lt.mpr hClo)
  | Up =>
    by_cases hhi0 : 0 ≤ hi
    · have h : (round S .Up hi).val = (roundCeiling S hi).val := by
        show (if 0 ≤ hi then roundCeiling S hi else roundFloor S hi).val = _
        rw [ite_eq_left hhi0]
      rw [h] at hR
      exact absurd (show (roundCeiling S hi).val < hi by rw [← hR]; exact hhi)
        (not_lt.mpr hChi)
    · have hv0 : ¬ 0 ≤ v := fun h => hhi0 (le_trans h h₂)
      show (if 0 ≤ v then roundCeiling S v else roundFloor S v).val = R
      rw [ite_eq_right hv0]
      exact hFv
  | Nearest =>
    have key : ∀ x : ℝ, (round S .Nearest x).val =
        (match compare ((x : EReal) - (roundFloor S x).val) ((roundCeiling S x).val - x) with
          | .lt => roundFloor S x
          | .gt => roundCeiling S x
          | .eq => tiebreak (roundFloor S x) (roundCeiling S x)).val := fun _ => rfl
    rw [key] at hR ⊢
    rw [hFhi] at hR
    rw [hFv, hCv]
    have hFv' : roundFloor S v = roundFloor S hi := Subtype.ext (hFv.trans hFhi.symm)
    have hCv' : roundCeiling S v = roundCeiling S hi := Subtype.ext hCv
    rw [hFv', hCv']
    -- the distances for `v` are squeezed between those for `hi`
    have hd1 : (v : EReal) - R ≤ (hi : EReal) - R := EReal.sub_le_sub h₂' le_rfl
    have hd2 : (roundCeiling S hi).val - hi ≤ (roundCeiling S hi).val - v :=
      EReal.sub_le_sub le_rfl h₂'
    cases hc : compare ((hi : EReal) - R) ((roundCeiling S hi).val - hi) with
    | lt =>
      rw [hc] at hR
      have hlt : (v : EReal) - R < (roundCeiling S hi).val - v :=
        lt_of_le_of_lt hd1 (lt_of_lt_of_le (compare_lt_iff_lt.mp hc) hd2)
      rw [compare_lt_iff_lt.mpr hlt]
      exact hFhi
    | gt =>
      rw [hc] at hR
      exact absurd (show (roundCeiling S hi).val < hi by rw [← hR]; exact hhi)
        (not_lt.mpr hChi)
    | eq =>
      rw [hc] at hR
      have heq := compare_eq_iff_eq.mp hc
      rcases lt_or_eq_of_le (le_trans hd1 (heq ▸ hd2)) with hlt | heq'
      · rw [compare_lt_iff_lt.mpr hlt]
        exact hFhi
      · rw [compare_eq_iff_eq.mpr heq']
        exact hR.symm

end Target

section Symmetric

variable (S : Set EReal) [SymmetricRoundingTarget S]

private lemma neg_mode_neg (mode : RoundingMode) : -(-mode) = mode := by
  cases mode <;> rfl

private lemma coe_neg' (x : ℝ) : ((-x : ℝ) : EReal) = -((x : ℝ) : EReal) := by
  push_cast; rfl

/-- **The squeeze.**  If `lo ≤ v ≤ hi` and the two ends round to the same element with the same
comparison tag, then `v` rounds to that element with that tag. -/
theorem round_between (mode : RoundingMode) {lo v hi : ℝ} (h₁ : lo ≤ v) (h₂ : v ≤ hi)
    (hR : (round S mode lo).val = (round S mode hi).val)
    (ht : compare (round S mode lo).val (lo : EReal)
      = compare (round S mode hi).val (hi : EReal)) :
    (round S mode v).val = (round S mode lo).val ∧
      compare (round S mode v).val (v : EReal) = compare (round S mode lo).val (lo : EReal) := by
  have h₁' : (lo : EReal) ≤ v := EReal.coe_le_coe_iff.mpr h₁
  have h₂' : (v : EReal) ≤ hi := EReal.coe_le_coe_iff.mpr h₂
  cases hc : compare (round S mode lo).val (lo : EReal) with
  | lt =>
    rw [hc] at ht
    have hlo := compare_lt_iff_lt.mp hc
    have hhi := compare_lt_iff_lt.mp ht.symm
    have hv := round_between_of_lt S mode h₁ h₂ hR hlo hhi
    exact ⟨hv, by rw [hv, compare_lt_iff_lt.mpr (lt_of_lt_of_le hlo h₁')]⟩
  | eq =>
    rw [hc] at ht
    have hlo := compare_eq_iff_eq.mp hc
    have hhi := compare_eq_iff_eq.mp ht.symm
    have hlohi : lo = hi := EReal.coe_eq_coe_iff.mp (hlo.symm.trans (hR.trans hhi))
    obtain rfl : v = lo := le_antisymm (hlohi ▸ h₂) h₁
    exact ⟨rfl, hc⟩
  | gt =>
    rw [hc] at ht
    have hlo := compare_gt_iff_gt.mp hc
    have hhi := compare_gt_iff_gt.mp ht.symm
    -- mirror: `-hi ≤ -v ≤ -lo` with the negated mode, whose common rounding is `-R`
    have hn : ∀ x : ℝ, (round S (-mode) (-x)).val = -(round S mode x).val := fun x => by
      rw [round_neg S (-mode) x, neg_mode_neg]
    have hR' : (round S (-mode) (-hi)).val = (round S (-mode) (-lo)).val := by
      rw [hn, hn, hR]
    have hlo' : (round S (-mode) (-hi)).val < ((-hi : ℝ) : EReal) := by
      rw [hn, coe_neg']
      exact EReal.neg_lt_neg_iff.mpr hhi
    have hhi' : (round S (-mode) (-lo)).val < ((-lo : ℝ) : EReal) := by
      rw [hn, coe_neg']
      exact EReal.neg_lt_neg_iff.mpr hlo
    have hv := round_between_of_lt S (-mode)
      (neg_le_neg h₂) (neg_le_neg h₁) hR' hlo' hhi'
    rw [hn, hn] at hv
    have hv' : (round S mode v).val = (round S mode lo).val := (neg_inj.mp hv).trans hR.symm
    exact ⟨hv', by rw [hv', hR, compare_gt_iff_gt.mpr (lt_of_le_of_lt h₂' hhi)]⟩

end Symmetric

end Azurite.RoundingTarget
