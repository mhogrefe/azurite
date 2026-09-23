/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Rounding.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# `ℚ` is not a `RoundingTarget`

The image of `ℚ` in `EReal` fails both existence conditions: for an irrational `x` such
as `√2`, density of `ℚ` in `ℝ` gives an endless supply of rationals strictly below
(resp. above) `x`, so the set of rationals `≤ x` has no maximum (and the set of
rationals `≥ x` has no minimum).

We prove the `existsGreatestLE` failure; this already suffices to rule out a
`RoundingTarget` instance.
-/

namespace Azurite
namespace RoundingTarget

/-- The image of `ℚ` in `EReal` (via `ℚ → ℝ → EReal`). -/
def ratSet : Set EReal := {e | ∃ q : ℚ, ((q : ℝ) : EReal) = e}

/-- `{q ∈ ratSet | q ≤ √2}` has no maximum: density of `ℚ` in `ℝ` plus irrationality
of `√2` means any candidate rational is strictly below `√2`, hence strictly below a
larger rational that is also `≤ √2`. -/
theorem not_existsGreatestLE_ratSet :
    ¬ ∃ M, IsGreatest {s | s ∈ ratSet ∧ s ≤ ((Real.sqrt 2 : ℝ) : EReal)} M := by
  rintro ⟨M, ⟨⟨q, rfl⟩, hq_le⟩, hM⟩
  have hq_le_r : (q : ℝ) ≤ Real.sqrt 2 := by exact_mod_cast hq_le
  have hq_ne : (q : ℝ) ≠ Real.sqrt 2 := (irrational_sqrt_two.ne_rat q).symm
  have hq_lt : (q : ℝ) < Real.sqrt 2 := lt_of_le_of_ne hq_le_r hq_ne
  obtain ⟨q', hqq', hq'lt⟩ := exists_rat_btwn hq_lt
  have hmem : ((q' : ℝ) : EReal) ∈
      {s | s ∈ ratSet ∧ s ≤ ((Real.sqrt 2 : ℝ) : EReal)} := by
    refine ⟨⟨q', rfl⟩, ?_⟩
    exact_mod_cast hq'lt.le
  have hle_EReal : ((q' : ℝ) : EReal) ≤ ((q : ℝ) : EReal) := hM hmem
  have hle_R : (q' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle_EReal
  linarith

/-- `ratSet` cannot be equipped with a `RoundingTarget` structure: the
`existsGreatestLE` field has no witness at `x = √2`. -/
theorem not_nonempty_roundingTarget_ratSet :
    ¬ Nonempty (RoundingTarget ratSet) := by
  rintro ⟨inst⟩
  exact not_existsGreatestLE_ratSet (inst.existsGreatestLE (Real.sqrt 2))

end RoundingTarget
end Azurite
