/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxSeries
import Mathlib.Algebra.Polynomial.Basic

/-! # BPR §2.6 — the Newton diagram of a polynomial over `R⟨⟨ε⟩⟩`

A polynomial `P(X) = ā₀ + ā₁ X + ⋯ + ā_p X^p ∈ R⟨⟨ε⟩⟩[X]` can be regarded as a formal sum of
monomials `X^i ε^r` (`i ∈ ℕ`, `r ∈ ℚ`) with coefficients in `R`: the coefficient of `X^i ε^r`
is the coefficient of `ε^r` in the Puiseux series `ā_i = P.coeff i`. The **Newton diagram** of
`P` is the set of points `(i, r)` for which `X^i ε^r` occurs with nonzero coefficient.

(`X`-degrees are natural numbers since `P` is an ordinary polynomial; the `ε`-exponents are
rational, ranging over the supports of the Puiseux-series coefficients.)
-/

namespace Azurite.BPR

open HahnSeries Polynomial

variable {R : Type*} [Field R]

/-- The coefficient of the monomial `X^i ε^r` in `P ∈ R⟨⟨ε⟩⟩[X]`: the coefficient of `ε^r`
in the Puiseux-series coefficient `P.coeff i`. -/
noncomputable def newtonCoeff (P : Polynomial (PuiseuxSeries R)) (i : ℕ) (r : ℚ) : R :=
  ((P.coeff i : PuiseuxSeries R) : HahnSeries ℚ R).coeff r

/-- **The Newton diagram of `P`** (BPR §2.6): the set of points `(i, r) ∈ ℕ × ℚ` for which the
monomial `X^i ε^r` occurs in `P` with nonzero coefficient. -/
def newtonDiagram (P : Polynomial (PuiseuxSeries R)) : Set (ℕ × ℚ) :=
  { p | newtonCoeff P p.1 p.2 ≠ 0 }

@[simp] theorem mem_newtonDiagram {P : Polynomial (PuiseuxSeries R)} {i : ℕ} {r : ℚ} :
    (i, r) ∈ newtonDiagram P ↔ newtonCoeff P i r ≠ 0 := Iff.rfl

@[simp] theorem newtonDiagram_zero :
    newtonDiagram (0 : Polynomial (PuiseuxSeries R)) = ∅ := by
  ext ⟨i, r⟩
  simp [newtonDiagram, newtonCoeff]

/-- The `X`-degree coordinate of any Newton-diagram point is at most `deg P`. -/
theorem fst_le_natDegree {P : Polynomial (PuiseuxSeries R)} {i : ℕ} {r : ℚ}
    (h : (i, r) ∈ newtonDiagram P) : i ≤ P.natDegree :=
  Polynomial.le_natDegree_of_ne_zero fun hc => h (by rw [newtonCoeff, hc]; simp)

/-- The `X`-degree coordinate of any Newton-diagram point lies in the support of `P`. -/
theorem fst_mem_support {P : Polynomial (PuiseuxSeries R)} {i : ℕ} {r : ℚ}
    (h : (i, r) ∈ newtonDiagram P) : i ∈ P.support :=
  Polynomial.mem_support_iff.mpr fun hc => h (by rw [newtonCoeff, hc]; simp)

/-- The `ε`-exponents occurring at a fixed `X`-degree `i` form exactly the support of the
Puiseux-series coefficient `P.coeff i` (which is partially well-ordered, as a Hahn-series
support). -/
theorem newtonDiagram_slice (P : Polynomial (PuiseuxSeries R)) (i : ℕ) :
    { r : ℚ | (i, r) ∈ newtonDiagram P }
      = ((P.coeff i : PuiseuxSeries R) : HahnSeries ℚ R).support := by
  ext r
  simp [newtonDiagram, newtonCoeff, HahnSeries.mem_support]

/-- The Newton diagram is empty exactly when `P = 0`. -/
theorem newtonDiagram_eq_empty_iff {P : Polynomial (PuiseuxSeries R)} :
    newtonDiagram P = ∅ ↔ P = 0 := by
  refine ⟨fun h => ?_, fun hP => hP ▸ newtonDiagram_zero⟩
  by_contra hP
  -- some `X`-degree `i` has a nonzero Puiseux coefficient
  obtain ⟨i, hi⟩ : ∃ i, P.coeff i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hP (Polynomial.ext fun n => by rw [hc n, Polynomial.coeff_zero])
  have hcoe : ((P.coeff i : PuiseuxSeries R) : HahnSeries ℚ R) ≠ 0 := by simpa using hi
  -- which in turn has some `ε`-exponent `r` with nonzero coefficient
  obtain ⟨r, hr⟩ := HahnSeries.support_nonempty_iff.mpr hcoe
  exact absurd (Set.eq_empty_iff_forall_notMem.mp h (i, r)) (by simpa [newtonDiagram, newtonCoeff,
    HahnSeries.mem_support] using hr)

/-! ## Slopes between Newton-diagram points -/

/-- The **slope** between two points `p, q ∈ ℕ × ℚ` of the Newton diagram with distinct
`x`-coordinates: the rise (difference of `ε`-exponents, the `y`-coordinates) over the run
(difference of `X`-degrees, the `x`-coordinates). For points sharing an `x`-coordinate the
value is the junk `0`; the lemma `newtonSlope_mul_sub` captures the intended rise-over-run
meaning exactly when the `x`-coordinates are distinct. -/
def newtonSlope (p q : ℕ × ℚ) : ℚ := (q.2 - p.2) / ((q.1 : ℚ) - p.1)

theorem newtonSlope_def (p q : ℕ × ℚ) :
    newtonSlope p q = (q.2 - p.2) / ((q.1 : ℚ) - p.1) := rfl

/-- The slope does not depend on the order of the two points. -/
theorem newtonSlope_symm (p q : ℕ × ℚ) : newtonSlope p q = newtonSlope q p := by
  rw [newtonSlope, newtonSlope, ← neg_div_neg_eq, neg_sub, neg_sub]

/-- For points with distinct `x`-coordinates, the slope satisfies `rise = slope · run`. -/
theorem newtonSlope_mul_sub {p q : ℕ × ℚ} (h : p.1 ≠ q.1) :
    newtonSlope p q * ((q.1 : ℚ) - p.1) = q.2 - p.2 := by
  have hrun : ((q.1 : ℚ) - p.1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h.symm)
  rw [newtonSlope, div_mul_cancel₀ _ hrun]

/-! ## Lying on or above a line -/

/-- **`C` lies on or above the line through `A` and `B`** (intended for `A`, `B` with distinct
`x`-coordinates, so that the line is non-vertical). The slope comparison is orientation
independent — it flips according to whether `C` is to the right of, level with, or to the left
of `A`:

* if `A` and `C` share an `x`-coordinate, then `C` is at least as high as `A`;
* if `C` is to the right of `A`, then the slope `A → C` is at least the slope `A → B`;
* if `C` is to the left of `A`, then the slope `A → C` is at most the slope `A → B`.

(With a negative run the rise-over-run inequality reverses, so the left-of case compares the
slopes the other way; `onOrAbove_iff` confirms all three cases amount to the single condition
that `C` sits at or above the line at `x = C.1`.) -/
def OnOrAbove (A B C : ℕ × ℚ) : Prop :=
  (A.1 = C.1 ∧ A.2 ≤ C.2) ∨
    (A.1 < C.1 ∧ newtonSlope A B ≤ newtonSlope A C) ∨
    (C.1 < A.1 ∧ newtonSlope A C ≤ newtonSlope A B)

instance (A B C : ℕ × ℚ) : Decidable (OnOrAbove A B C) := by unfold OnOrAbove; infer_instance

/-- **Orientation-independent characterization.** `C` lies on or above the line through `A` and
`B` exactly when `C` is at or above that line evaluated at `x = C.1`, i.e.
`slope(A,B)·(C.x − A.x) ≤ C.y − A.y`. -/
theorem onOrAbove_iff (A B C : ℕ × ℚ) :
    OnOrAbove A B C ↔ newtonSlope A B * ((C.1 : ℚ) - A.1) ≤ C.2 - A.2 := by
  rcases lt_trichotomy A.1 C.1 with h | h | h
  · have hrun : (0 : ℚ) < (C.1 : ℚ) - A.1 := sub_pos.mpr (by exact_mod_cast h)
    have hred : OnOrAbove A B C ↔ newtonSlope A B ≤ newtonSlope A C := by
      unfold OnOrAbove
      refine ⟨fun hh => ?_, fun hh => Or.inr (Or.inl ⟨h, hh⟩)⟩
      rcases hh with ⟨he, _⟩ | ⟨_, hle⟩ | ⟨hlt, _⟩
      · exact absurd he (ne_of_lt h)
      · exact hle
      · exact absurd hlt (asymm h)
    rw [hred, newtonSlope_def A C, le_div_iff₀ hrun]
  · have hrun : (C.1 : ℚ) - A.1 = 0 := by rw [h]; ring
    have hred : OnOrAbove A B C ↔ A.2 ≤ C.2 := by
      unfold OnOrAbove
      refine ⟨fun hh => ?_, fun hh => Or.inl ⟨h, hh⟩⟩
      rcases hh with ⟨_, hle⟩ | ⟨hlt, _⟩ | ⟨hlt, _⟩
      · exact hle
      · exact absurd h (ne_of_lt hlt)
      · exact absurd h.symm (ne_of_lt hlt)
    rw [hred, hrun, mul_zero, sub_nonneg]
  · have hrun : (C.1 : ℚ) - A.1 < 0 := sub_neg.mpr (by exact_mod_cast h)
    have hred : OnOrAbove A B C ↔ newtonSlope A C ≤ newtonSlope A B := by
      unfold OnOrAbove
      refine ⟨fun hh => ?_, fun hh => Or.inr (Or.inr ⟨h, hh⟩)⟩
      rcases hh with ⟨he, _⟩ | ⟨hlt, _⟩ | ⟨_, hle⟩
      · exact absurd he.symm (ne_of_lt h)
      · exact absurd hlt (asymm h)
      · exact hle
    rw [hred, newtonSlope_def A C, div_le_iff_of_neg hrun]

/-- `A` itself lies on (hence on or above) the line through `A` and `B`. -/
theorem onOrAbove_left (A B : ℕ × ℚ) : OnOrAbove A B A := Or.inl ⟨rfl, le_refl _⟩

/-- `B` itself lies on (hence on or above) the line through `A` and `B`, when `A` and `B` have
distinct `x`-coordinates. -/
theorem onOrAbove_right {A B : ℕ × ℚ} (h : A.1 ≠ B.1) : OnOrAbove A B B := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact Or.inr (Or.inl ⟨hlt, le_refl _⟩)
  · exact Or.inr (Or.inr ⟨hgt, le_refl _⟩)

/-- **`OnOrAbove` depends only on the line, not on the order of its two defining points.** In
particular it does not matter whether `A` is to the left or to the right of `B`. -/
theorem onOrAbove_swap {A B C : ℕ × ℚ} (h : A.1 ≠ B.1) :
    OnOrAbove A B C ↔ OnOrAbove B A C := by
  rw [onOrAbove_iff, onOrAbove_iff, newtonSlope_symm B A]
  have key : newtonSlope A B * ((B.1 : ℚ) - A.1) = B.2 - A.2 := newtonSlope_mul_sub h
  have heq : newtonSlope A B * ((C.1 : ℚ) - A.1) - (C.2 - A.2)
      = newtonSlope A B * ((C.1 : ℚ) - B.1) - (C.2 - B.2) := by linear_combination key
  constructor <;> intro hh <;> linarith [heq]

/-- **For a horizontal line** (when `A` and `B` share a `y`-coordinate), `C` lies on or above the
line through `A` and `B` exactly when `C` is at least as high as `A`, i.e. `C.2 ≥ A.2`. -/
theorem onOrAbove_horizontal {A B C : ℕ × ℚ} (h : A.2 = B.2) :
    OnOrAbove A B C ↔ A.2 ≤ C.2 := by
  rw [onOrAbove_iff]
  have hslope : newtonSlope A B = 0 := by rw [newtonSlope_def, ← h, sub_self, zero_div]
  rw [hslope, zero_mul, sub_nonneg]

end Azurite.BPR
