/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_35

/-!
# BPR Example 2.37: Budan-Fourier is not tight as an equality

The polynomial `P = X² − X + 1` has no real root (its discriminant `−3` is
negative), but `Var(Der(P); 0, 1) = 2`:

  * `Der(P) = [X² − X + 1, 2X − 1, 2]`.
  * Evaluating at `0` gives `[1, −1, 2]` with two sign changes.
  * Evaluating at `1` gives `[1, 1, 2]` with no sign change.
  * Hence `Var(Der(P); 0, 1) = 2 − 0 = 2`.

It is impossible to refine `(0, 1]` into `(0, a]` and `(a, 1]` with each
piece contributing one sign variation, since otherwise Budan–Fourier would
force `P` to have two real roots in `(0, 1]`. Any sub-interval containing
`1/2` (where `P` attains its minimum) necessarily contributes `2` sign
variations. This shows that the bound in Budan–Fourier is tight in the
sense of parity — here both sides have the same parity `2 ≡ 0 (mod 2)` —
but is not tight as an equality.

We record `Der(P)` as the explicit list `[X² − X + 1, 2X − 1, 2]` (bypassing
the `der` computation that would require unfolding iterated derivatives).
-/

namespace Azurite.BPR.Theorem2_35

open Polynomial Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

example :
    varAt ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X]) (.finite 0) = 2 := by
  simp [varAt_finite, Var]; norm_num [varNonzero]

example :
    varAt ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X]) (.finite 1) = 0 := by
  simp [varAt_finite, Var]; norm_num [varNonzero]

example :
    varBetween ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X])
      (.finite 0) (.finite 1) = 2 := by
  have h0 : varAt ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X]) (.finite 0) = 2 := by
    simp [varAt_finite, Var]; norm_num [varNonzero]
  have h1 : varAt ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X]) (.finite 1) = 0 := by
    simp [varAt_finite, Var]; norm_num [varNonzero]
  unfold varBetween
  rw [h0, h1]
  rfl

/-! ### Refinement impossibility

BPR Example 2.37 continues: "It is impossible to find `a ∈ (0, 1]` such
that `Var(Der(P); 0, a] = 1` and `Var(Der(P); a, 1] = 1`, since otherwise
`P` would have two real roots." We formalise this as a theorem over any
real-closed-style field `R` with the intermediate-value property.

The argument is: if both sub-intervals contributed exactly one variation,
Budan-Fourier would force `numRoots ≥ 1` on each (since `Var − numRoots`
is even and nonneg). Summed, `numRoots` on `(0, 1]` would be `≥ 2`. But
`X² − X + 1` has no real root at all: `4 (X² − X + 1) = (2X − 1)² + 3 ≥ 3`. -/

/-- `P := X² − X + 1` is strictly positive on `R` for any
    `IsStrictOrderedRing R`: `4·P(x) = (2x − 1)² + 3 ≥ 3 > 0`. -/
private lemma example_2_37_positive (x : R) :
    0 < ((X : R[X]) ^ 2 - X + 1).eval x := by
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
  nlinarith [sq_nonneg (2 * x - 1)]

/-- `P := X² − X + 1` is nonzero in `R[X]` (evaluation at `0` is `1`). -/
private lemma example_2_37_ne_zero : ((X : R[X]) ^ 2 - X + 1) ≠ 0 := fun h => by
  have h0 := example_2_37_positive (0 : R)
  rw [h] at h0; simp at h0

/-- `P := X² − X + 1` has no real root: `P.roots = 0` as a multiset. -/
private lemma example_2_37_roots_empty :
    ((X : R[X]) ^ 2 - X + 1).roots = 0 := by
  classical
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  exact ne_of_gt (example_2_37_positive r)
    ((Polynomial.mem_roots example_2_37_ne_zero).mp hr)

/-- **BPR Example 2.37 (refinement impossibility).** For `P = X² − X + 1`,
    there is no `a ∈ (0, 1]` such that each of the sub-intervals `(0, a]`
    and `(a, 1]` contributes exactly one sign variation to
    `Var(Der(P); ·, ·)`.

    If both `Var(Der(P); 0, a] = 1` and `Var(Der(P); a, 1] = 1`, then by
    Budan-Fourier each sub-interval would contain at least one real root of
    `P`, giving at least two roots in `(0, 1]`.  But `X² − X + 1` has no
    real root, since `4 (X² − X + 1) = (2X − 1)² + 3 ≥ 3 > 0`. -/
theorem example_2_37_no_refinement
    (hIVP : HasIntermediateValueProperty R) {a : R} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ¬ (varBetween (der ((X : R[X]) ^ 2 - X + 1)) (.finite 0) (.finite a) = 1 ∧
       varBetween (der ((X : R[X]) ^ 2 - X + 1)) (.finite a) (.finite 1) = 1) := by
  rintro ⟨hV0a, hVa1⟩
  set P : R[X] := X ^ 2 - X + 1
  have hP_ne : P ≠ 0 := example_2_37_ne_zero
  have hroots : P.roots = 0 := example_2_37_roots_empty
  have h_num_zero : ∀ c d : R, numRoots P (.finite c) (.finite d) = 0 := by
    intro c d
    rw [numRoots_finite_finite, hroots]
    simp
  rcases lt_or_eq_of_le ha1 with ha_lt1 | ha_eq1
  · -- Case `a < 1`: apply Budan-Fourier on `(0, a]`.
    have hBF0a := budan_fourier_finite hIVP hP_ne ha0
    rw [hV0a, h_num_zero 0 a] at hBF0a
    exact (by decide : ¬ Even (1 - (0 : ℤ))) hBF0a.2
  · -- Case `a = 1`: `varBetween (.finite 1) (.finite 1) = 0 ≠ 1`.
    subst ha_eq1
    unfold varBetween at hVa1
    simp at hVa1

end Azurite.BPR.Theorem2_35
