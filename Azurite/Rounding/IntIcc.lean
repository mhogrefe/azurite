/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Rounding.Basic
import Mathlib.Algebra.Order.Floor.Defs

/-!
# `RoundingTarget` instance for a bounded range of integers together with `±∞`

For integers `a ≤ b`, the set `{z : ℤ | a ≤ z ≤ b}` viewed in `EReal`, adjoined with
`⊥ = -∞` and `⊤ = +∞`, is a `RoundingTarget`. When `x > b` the round-up target is `⊤`;
when `x < a` the round-down target is `⊥`. When `b < a` (empty range) every real rounds
up to `⊤` and down to `⊥`.

The tiebreaker prefers the even integer, analogous to the `ℤ` instance; when one
argument is `±∞` (`intIccToInt` returns `0`, which is even) the choice is not
spec-relevant.
-/

namespace Azurite
namespace RoundingTarget

/-- Integers in the range `[a, b]` viewed in `EReal`, together with `⊥` and `⊤`. -/
def intIccBotTopSet (a b : ℤ) : Set EReal :=
  {e | e = ⊥ ∨ e = ⊤ ∨ ∃ z : ℤ, a ≤ z ∧ z ≤ b ∧ ((z : ℝ) : EReal) = e}

open Classical in
/-- Recover the underlying integer, returning `0` on `±∞`. -/
noncomputable def intIccToInt {a b : ℤ} (s : ↥(intIccBotTopSet a b)) : ℤ :=
  if h : ∃ z : ℤ, ((z : ℝ) : EReal) = s.val then h.choose else 0

/-- Parity-based tiebreaker: prefers the even integer. -/
noncomputable def intIccTiebreak {a b : ℤ}
    (s t : ↥(intIccBotTopSet a b)) : ↥(intIccBotTopSet a b) :=
  if Even (intIccToInt s) then s else if Even (intIccToInt t) then t else s

noncomputable instance intIccBotTopRoundingTarget (a b : ℤ) :
    RoundingTarget (intIccBotTopSet a b) where
  existsLeastGE x := by
    by_cases hab : a ≤ b
    · by_cases hxb : x ≤ (b : ℝ)
      · -- Witness: (max ⌈x⌉ a : ℤ) cast to EReal
        set z : ℤ := max ⌈x⌉ a with hz_def
        have ha_le_z : a ≤ z := le_max_right _ _
        have hceil_le_z : ⌈x⌉ ≤ z := le_max_left _ _
        have hz_le_b : z ≤ b := by
          rcases le_or_gt ⌈x⌉ a with h | h
          · have : z = a := by rw [hz_def]; exact max_eq_right h
            rw [this]; exact hab
          · have : z = ⌈x⌉ := by rw [hz_def]; exact max_eq_left h.le
            rw [this]
            have : (⌈x⌉ : ℝ) ≤ b := by
              rcases le_or_gt (⌈x⌉ : ℝ) (b : ℝ) with h' | h'
              · exact h'
              · exfalso
                have hxlt : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
                have : (b : ℝ) < (⌈x⌉ : ℝ) := h'
                have hcb : b < ⌈x⌉ := by exact_mod_cast this
                have hceil_le_b : ⌈x⌉ ≤ b := Int.ceil_le.mpr hxb
                exact absurd hcb (not_lt_of_ge hceil_le_b)
            exact_mod_cast this
        refine ⟨((z : ℝ) : EReal),
          ⟨Or.inr (Or.inr ⟨z, ha_le_z, hz_le_b, rfl⟩), ?_⟩, ?_⟩
        · have : x ≤ (z : ℝ) := by
            have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
            have h2 : (⌈x⌉ : ℝ) ≤ (z : ℝ) := by exact_mod_cast hceil_le_z
            linarith
          exact_mod_cast this
        · rintro s ⟨hmem, hge⟩
          rcases hmem with rfl | rfl | ⟨w, haw, _, rfl⟩
          · exact absurd hge (not_le_of_gt (EReal.bot_lt_coe x))
          · exact le_top
          · have hxw : x ≤ (w : ℝ) := by exact_mod_cast hge
            have hcw : ⌈x⌉ ≤ w := Int.ceil_le.mpr hxw
            have : z ≤ w := by
              rcases le_or_gt ⌈x⌉ a with h | h
              · have hza : z = a := by rw [hz_def]; exact max_eq_right h
                rw [hza]; exact haw
              · have hzc : z = ⌈x⌉ := by rw [hz_def]; exact max_eq_left h.le
                rw [hzc]; exact hcw
            exact_mod_cast this
      · -- x > b, so least ≥ x in the set is ⊤
        push Not at hxb
        refine ⟨⊤, ⟨Or.inr (Or.inl rfl), le_top⟩, ?_⟩
        rintro s ⟨hmem, hge⟩
        rcases hmem with rfl | rfl | ⟨w, _, hwb, rfl⟩
        · exact absurd hge (not_le_of_gt (EReal.bot_lt_coe x))
        · exact le_refl ⊤
        · exfalso
          have hxw : x ≤ (w : ℝ) := by exact_mod_cast hge
          have hwbr : (w : ℝ) ≤ (b : ℝ) := by exact_mod_cast hwb
          linarith
    · -- a > b: empty range, witness ⊤
      push Not at hab
      refine ⟨⊤, ⟨Or.inr (Or.inl rfl), le_top⟩, ?_⟩
      rintro s ⟨hmem, hge⟩
      rcases hmem with rfl | rfl | ⟨w, haw, hwb, rfl⟩
      · exact absurd hge (not_le_of_gt (EReal.bot_lt_coe x))
      · exact le_refl ⊤
      · exfalso; omega
  existsGreatestLE x := by
    by_cases hab : a ≤ b
    · by_cases hax : (a : ℝ) ≤ x
      · set z : ℤ := min ⌊x⌋ b with hz_def
        have hz_le_b : z ≤ b := min_le_right _ _
        have hz_le_floor : z ≤ ⌊x⌋ := min_le_left _ _
        have ha_le_z : a ≤ z := by
          rcases le_or_gt ⌊x⌋ b with h | h
          · have : z = ⌊x⌋ := by rw [hz_def]; exact min_eq_left h
            rw [this]
            have : (a : ℝ) ≤ (⌊x⌋ : ℝ) := by
              have hfloor : (a : ℝ) ≤ (⌊x⌋ : ℝ) := by
                have : a ≤ ⌊x⌋ := Int.le_floor.mpr hax
                exact_mod_cast this
              exact hfloor
            exact_mod_cast this
          · have : z = b := by rw [hz_def]; exact min_eq_right h.le
            rw [this]; exact hab
        refine ⟨((z : ℝ) : EReal),
          ⟨Or.inr (Or.inr ⟨z, ha_le_z, hz_le_b, rfl⟩), ?_⟩, ?_⟩
        · have : (z : ℝ) ≤ x := by
            have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
            have h2 : (z : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hz_le_floor
            linarith
          exact_mod_cast this
        · rintro s ⟨hmem, hle⟩
          rcases hmem with rfl | rfl | ⟨w, _, hwb, rfl⟩
          · exact bot_le
          · exact absurd hle (not_le_of_gt (EReal.coe_lt_top x))
          · have hwx : (w : ℝ) ≤ x := by exact_mod_cast hle
            have hwf : w ≤ ⌊x⌋ := Int.le_floor.mpr hwx
            have : w ≤ z := by
              rcases le_or_gt ⌊x⌋ b with h | h
              · have hzf : z = ⌊x⌋ := by rw [hz_def]; exact min_eq_left h
                rw [hzf]; exact hwf
              · have hzb : z = b := by rw [hz_def]; exact min_eq_right h.le
                rw [hzb]; exact hwb
            exact_mod_cast this
      · push Not at hax
        refine ⟨⊥, ⟨Or.inl rfl, bot_le⟩, ?_⟩
        rintro s ⟨hmem, hle⟩
        rcases hmem with rfl | rfl | ⟨w, haw, _, rfl⟩
        · exact le_refl ⊥
        · exact absurd hle (not_le_of_gt (EReal.coe_lt_top x))
        · exfalso
          have hwx : (w : ℝ) ≤ x := by exact_mod_cast hle
          have hawr : (a : ℝ) ≤ (w : ℝ) := by exact_mod_cast haw
          linarith
    · push Not at hab
      refine ⟨⊥, ⟨Or.inl rfl, bot_le⟩, ?_⟩
      rintro s ⟨hmem, hle⟩
      rcases hmem with rfl | rfl | ⟨w, haw, hwb, rfl⟩
      · exact le_refl ⊥
      · exact absurd hle (not_le_of_gt (EReal.coe_lt_top x))
      · exfalso; omega
  tiebreak := intIccTiebreak
  tiebreak_mem s t := by
    unfold intIccTiebreak
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

end RoundingTarget
end Azurite
