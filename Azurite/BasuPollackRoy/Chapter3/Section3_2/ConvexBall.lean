/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_2.Convex
import Azurite.BasuPollackRoy.Chapter3.Section3_1.EuclideanBall
import Mathlib.Tactic.Linarith

/-! # BPR §3.2 — balls are convex

Every open or closed euclidean ball in `R^k` is convex. Working with the squared norm
`euclideanNormSq`, the key is the coordinatewise convexity of squaring: a convex combination's
squared distance to the centre is bounded by the larger of the two endpoint squared distances. -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [IsRealClosed R] in
/-- Coordinatewise convexity of squaring, summed: the squared distance of a convex combination is at
most the corresponding convex combination of the squared distances. -/
private theorem normSq_sub_convex_le {x a b : Fin k → R} {l : R} (hl : l ∈ Set.Icc (0 : R) 1) :
    euclideanNormSq ((1 - l) • a + l • b - x)
      ≤ (1 - l) * euclideanNormSq (a - x) + l * euclideanNormSq (b - x) := by
  simp only [euclideanNormSq]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hl.2) hl.1) (sq_nonneg (a i - b i)),
    hl.1, hl.2]

omit [IsRealClosed R] in
/-- The squared distance of a convex combination to a centre is at most the larger of the two
endpoint squared distances. -/
private theorem normSq_sub_le_max {x a b : Fin k → R} {l : R} (hl : l ∈ Set.Icc (0 : R) 1) :
    euclideanNormSq ((1 - l) • a + l • b - x)
      ≤ max (euclideanNormSq (a - x)) (euclideanNormSq (b - x)) := by
  refine (normSq_sub_convex_le hl).trans ?_
  nlinarith [le_max_left (euclideanNormSq (a - x)) (euclideanNormSq (b - x)),
    le_max_right (euclideanNormSq (a - x)) (euclideanNormSq (b - x)),
    mul_nonneg (sub_nonneg.mpr hl.2)
      (sub_nonneg.mpr (le_max_left (euclideanNormSq (a - x)) (euclideanNormSq (b - x)))),
    mul_nonneg hl.1
      (sub_nonneg.mpr (le_max_right (euclideanNormSq (a - x)) (euclideanNormSq (b - x))))]

/-- **A closed ball in `R^k` is convex.** -/
theorem isConvex_closedBall (x : Fin k → R) (r : R) : IsConvex (closedBall x r) := by
  intro a ha b hb l hl
  rw [mem_closedBall] at ha hb ⊢
  exact (normSq_sub_le_max hl).trans (max_le ha hb)

/-- **An open ball in `R^k` is convex.** -/
theorem isConvex_openBall (x : Fin k → R) (r : R) : IsConvex (openBall x r) := by
  intro a ha b hb l hl
  rw [mem_openBall] at ha hb ⊢
  exact lt_of_le_of_lt (normSq_sub_le_max hl) (max_lt ha hb)

end Azurite.BPR
