/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TreeT
import Azurite.AzFloat.Equiv.LambertW
import Azurite.AzFloat.Equiv.NegRound

/-!
# Equivalence: the tree function

`Spec.treeT a = (Spec.lambertW0 (−a)).map (−·)` on the extended reals: `T(−∞) = −∞`, `NaN`
above `e⁻¹` and at `+∞`, `Azurite.DLMF.treeT` in between (`Spec.treeT_coe_of_le`,
`Spec.treeT_coe_of_lt`).  `roundVal_map_neg` extends `roundVal_neg` to every value (`NaN`,
`±∞`); with it `treeTPrecRound_eq` and `treeTRatPrecRound_eq` follow from the specifications
of `W₀`.
-/

namespace Azurite.AzFloat

namespace Spec

/-- The tree function on the extended reals: `−W₀(−a)`. -/
noncomputable def treeT (a : EReal) : Option EReal := (lambertW0 (-a)).map fun v => -v

theorem treeT_bot : treeT ⊥ = some ⊥ := by
  simp [treeT, lambertW0_top]

theorem treeT_top : treeT ⊤ = none := by
  simp [treeT, lambertW0_bot]

/-- In the domain: the real tree function of DLMF §4.13. -/
theorem treeT_coe_of_le {xv : ℝ} (h : xv ≤ Real.exp (-1)) :
    treeT (xv : EReal) = some ((Azurite.DLMF.treeT xv : ℝ) : EReal) := by
  unfold treeT
  rw [← EReal.coe_neg, lambertW0_coe_of_le (by linarith), Option.map_some, ← EReal.coe_neg]
  rfl

/-- Above `e⁻¹`: `NaN`. -/
theorem treeT_coe_of_lt {xv : ℝ} (h : Real.exp (-1) < xv) : treeT (xv : EReal) = none := by
  unfold treeT
  rw [← EReal.coe_neg, lambertW0_coe_of_lt (by linarith), Option.map_none]

end Spec

/-- Rounding the negated value with `mode` is the negation of rounding the value with `−mode`,
the comparison swapped — for every value, `NaN` and `±∞` included. -/
theorem roundVal_map_neg (p : ℕ) [NeZero p] (mode : RoundingMode) (o : Option EReal) :
    roundVal p mode (o.map fun v => -v)
      = (-(roundVal p (-mode) o).1, (roundVal p (-mode) o).2.swap) := by
  cases o with
  | none => rfl
  | some v =>
    induction v using EReal.rec with
    | bot => rw [Option.map_some, EReal.neg_bot, roundVal_top, roundVal_bot]; rfl
    | top => rw [Option.map_some, EReal.neg_top, roundVal_top, roundVal_bot]; rfl
    | coe r => rw [Option.map_some, ← EReal.coe_neg, roundVal_neg]

/-- **The tree function is correctly rounded.** -/
theorem treeTPrecRound_eq (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    treeTPrecRound x p mode = liftVal Spec.treeT x p mode := by
  unfold treeTPrecRound
  dsimp only
  rw [lambertW0PrecRound_eq]
  unfold liftVal
  rw [← roundVal_map_neg]
  congr 1
  rw [toVal_neg]
  cases x.toVal <;> rfl

/-- **The tree function of a rational is correctly rounded.** -/
theorem treeTRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    treeTRatPrecRound q p mode
      = roundVal p mode (Spec.treeT (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold treeTRatPrecRound
  dsimp only
  rw [lambertW0RatPrecRound_eq, ← roundVal_map_neg]
  unfold Spec.treeT
  congr 3
  rw [AzRat.toRat_neg]
  push_cast
  rfl

end Azurite.AzFloat
