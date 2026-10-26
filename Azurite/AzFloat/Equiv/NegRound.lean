/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Rounding
import Azurite.Rounding.Symmetric

/-!
# Rounding a negated value

`roundVal_neg`: rounding `−v` with `mode` is the negation of rounding `v` with `−mode`
(`RoundingMode.neg`), with the comparison swapped — the float-level form of
`RoundingTarget.round_neg` on the symmetric `floatSet p`.
-/

namespace Azurite.AzFloat

/-- `compare (−a) (−b)` is the swap of `compare a b` on `EReal`. -/
theorem compare_neg_neg_ereal (a b : EReal) : compare (-a) (-b) = (compare a b).swap := by
  rcases lt_trichotomy a b with h | h | h
  · rw [(compare_lt_iff_lt (a := a) (b := b)).mpr h]
    exact (compare_gt_iff_gt (a := -a) (b := -b)).mpr (EReal.neg_lt_neg_iff.mpr h)
  · subst h
    rw [(compare_eq_iff_eq (a := a) (b := a)).mpr rfl]
    exact (compare_eq_iff_eq (a := -a) (b := -a)).mpr rfl
  · rw [(compare_gt_iff_gt (a := a) (b := b)).mpr h]
    exact (compare_lt_iff_lt (a := -a) (b := -b)).mpr (EReal.neg_lt_neg_iff.mpr h)

/-- Rounding `−v` with `mode` is the negation of rounding `v` with `−mode`, the comparison
swapped. -/
theorem roundVal_neg (p : ℕ) [NeZero p] (mode : RoundingMode) (v : ℝ) :
    roundVal p mode (some ((-v : ℝ) : EReal))
      = (-(roundVal p (-mode) (some (v : EReal))).1,
        (roundVal p (-mode) (some (v : EReal))).2.swap) := by
  refine Prod.ext ?_ ?_
  · refine toVal_injective p (ofEReal_spec p mode (-v)).1 ?_ ?_
    · show (-(ofEReal p (-mode) (v : EReal))).precision? = some p
        ∨ (-(ofEReal p (-mode) (v : EReal))).precision? = none
      rw [precision?_neg]
      exact (ofEReal_spec p (-mode) v).1
    · show (ofEReal p mode ((-v : ℝ) : EReal)).toVal = (-(ofEReal p (-mode) (v : EReal))).toVal
      rw [(ofEReal_spec p mode (-v)).2, toVal_neg, (ofEReal_spec p (-mode) v).2, Option.map_some,
        RoundingTarget.round_neg]
  · show (roundVal p mode (some ((-v : ℝ) : EReal))).2
      = (roundVal p (-mode) (some (v : EReal))).2.swap
    rw [(roundVal_coe p mode (-v)).2, (roundVal_coe p (-mode) v).2, RoundingTarget.round_neg,
      EReal.coe_neg, compare_neg_neg_ereal]

end Azurite.AzFloat
