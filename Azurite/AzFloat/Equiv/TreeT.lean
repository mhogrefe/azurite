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

`Spec.treeT0 a = (Spec.lambertW0 (−a)).map (−·)` and `Spec.treeTm1 a =
(Spec.lambertWm1 (−a)).map (−·)` on the extended reals.  `T₀`: `T₀(−∞) = −∞`, `NaN` above
`e⁻¹` and at `+∞`, `Azurite.DLMF.treeT` in between (`Spec.treeT0_coe_of_le`,
`Spec.treeT0_coe_of_lt`).  `T₋₁`: `+∞` at `0`, `−W₋₁(−x)` on `(0, e⁻¹]`
(`Spec.treeTm1_coe_of_mem`), `NaN` elsewhere.  `roundVal_map_neg` extends `roundVal_neg` to
every value (`NaN`, `±∞`); with it the four specifications follow from those of `W`.
-/

namespace Azurite.AzFloat

namespace Spec

/-- The principal branch of the tree function on the extended reals: `−W₀(−a)`. -/
noncomputable def treeT0 (a : EReal) : Option EReal := (lambertW0 (-a)).map fun v => -v

theorem treeT0_bot : treeT0 ⊥ = some ⊥ := by
  simp [treeT0, lambertW0_top]

theorem treeT0_top : treeT0 ⊤ = none := by
  simp [treeT0, lambertW0_bot]

/-- In the domain: the real tree function of DLMF §4.13. -/
theorem treeT0_coe_of_le {xv : ℝ} (h : xv ≤ Real.exp (-1)) :
    treeT0 (xv : EReal) = some ((Azurite.DLMF.treeT xv : ℝ) : EReal) := by
  unfold treeT0
  rw [← EReal.coe_neg, lambertW0_coe_of_le (by linarith), Option.map_some, ← EReal.coe_neg]
  rfl

/-- Above `e⁻¹`: `NaN`. -/
theorem treeT0_coe_of_lt {xv : ℝ} (h : Real.exp (-1) < xv) : treeT0 (xv : EReal) = none := by
  unfold treeT0
  rw [← EReal.coe_neg, lambertW0_coe_of_lt (by linarith), Option.map_none]

/-- The branch `T₋₁` of the tree function on the extended reals: `−W₋₁(−a)`. -/
noncomputable def treeTm1 (a : EReal) : Option EReal := (lambertWm1 (-a)).map fun v => -v

theorem treeTm1_zero : treeTm1 0 = some ⊤ := by
  simp [treeTm1, lambertWm1_zero]

theorem treeTm1_top : treeTm1 ⊤ = none := by
  simp [treeTm1, lambertWm1_bot]

theorem treeTm1_bot : treeTm1 ⊥ = none := by
  simp [treeTm1, lambertWm1_top]

/-- On `(0, e⁻¹]`: `−W₋₁(−x)`. -/
theorem treeTm1_coe_of_mem {xv : ℝ} (h0 : 0 < xv) (h : xv ≤ Real.exp (-1)) :
    treeTm1 (xv : EReal) = some ((-Azurite.DLMF.lambertWm1 (-xv) : ℝ) : EReal) := by
  unfold treeTm1
  rw [← EReal.coe_neg, lambertWm1_coe_of_mem (by linarith) (by linarith), Option.map_some,
    ← EReal.coe_neg]

/-- Above `e⁻¹`: `NaN`. -/
theorem treeTm1_coe_of_lt {xv : ℝ} (h : Real.exp (-1) < xv) : treeTm1 (xv : EReal) = none := by
  unfold treeTm1
  rw [← EReal.coe_neg, lambertWm1_coe_of_lt (by linarith), Option.map_none]

/-- Below `0`: `NaN`. -/
theorem treeTm1_coe_of_neg {xv : ℝ} (h : xv < 0) : treeTm1 (xv : EReal) = none := by
  unfold treeTm1
  rw [← EReal.coe_neg, lambertWm1_coe_of_pos (by linarith), Option.map_none]

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

/-- **The tree function `T₀` is correctly rounded.** -/
theorem treeT0PrecRound_eq (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    treeT0PrecRound x p mode = liftVal Spec.treeT0 x p mode := by
  unfold treeT0PrecRound
  dsimp only
  rw [lambertW0PrecRound_eq]
  unfold liftVal
  rw [← roundVal_map_neg]
  congr 1
  rw [toVal_neg]
  cases x.toVal <;> rfl

/-- **`T₀` of a rational is correctly rounded.** -/
theorem treeT0RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    treeT0RatPrecRound q p mode
      = roundVal p mode (Spec.treeT0 (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold treeT0RatPrecRound
  dsimp only
  rw [lambertW0RatPrecRound_eq, ← roundVal_map_neg]
  unfold Spec.treeT0
  congr 3
  rw [AzRat.toRat_neg]
  push_cast
  rfl

/-- **The tree function `T₋₁` is correctly rounded.** -/
theorem treeTm1PrecRound_eq (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    treeTm1PrecRound x p mode = liftVal Spec.treeTm1 x p mode := by
  unfold treeTm1PrecRound
  dsimp only
  rw [lambertWm1PrecRound_eq]
  unfold liftVal
  rw [← roundVal_map_neg]
  congr 1
  rw [toVal_neg]
  cases x.toVal <;> rfl

/-- **`T₋₁` of a rational is correctly rounded.** -/
theorem treeTm1RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    treeTm1RatPrecRound q p mode
      = roundVal p mode (Spec.treeTm1 (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold treeTm1RatPrecRound
  dsimp only
  rw [lambertWm1RatPrecRound_eq, ← roundVal_map_neg]
  unfold Spec.treeTm1
  congr 3
  rw [AzRat.toRat_neg]
  push_cast
  rfl

end Azurite.AzFloat
