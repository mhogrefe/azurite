/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Basic.Sign.Basic
import Mathlib.Tactic.Linarith

/-!
# BPR Example 2.30: Thom encoding of the roots of `X² − 2`

In any ordered field, the roots of `X² − 2` are distinguished by the sign of
the derivative `2X`. Since `sign(2r) = sign(r)` (as `2 > 0`), two roots
`r, s` with `sign(r) = sign(s)` must be equal. Each root therefore has a
unique Thom encoding `(σ(P) = 0, σ(P') = ±1)` — the canonical example of how
sign-of-derivative information distinguishes roots.

The Lean statement below is purely algebraic (no `R[X]` polynomial machinery
needed): it just records that two square roots of `2` with the same sign are
equal.
-/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A root of `X² − 2` is nonzero. -/
private lemma root_X_sq_sub_two_ne_zero {r : R} (hr : r ^ 2 = 2) : r ≠ 0 := by
  rintro rfl; norm_num at hr

/-- **BPR Example 2.30.** In any ordered field, the roots of `X² − 2` are
    distinguished by the sign of the derivative `2X`. Since `sign(2r) = sign(r)`
    (as `2 > 0`), two roots `r, s` with `sign(r) = sign(s)` must be equal.
    Each root has a unique Thom encoding `(σ(P) = 0, σ(P') = ±1)`. -/
theorem example_2_30 {r s : R} (hr : r ^ 2 = 2) (hs : s ^ 2 = 2)
    (hsign : SignType.sign r = SignType.sign s) : r = s := by
  have h : (r - s) * (r + s) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exfalso
    have hr_ne := root_X_sq_sub_two_ne_zero hr
    rw [show s = -r from by linarith, Left.sign_neg r] at hsign
    have : SignType.sign r ≠ 0 := by rwa [ne_eq, sign_eq_zero_iff]
    revert hsign this; generalize SignType.sign r = a; cases a <;> simp

end Azurite.BPR
