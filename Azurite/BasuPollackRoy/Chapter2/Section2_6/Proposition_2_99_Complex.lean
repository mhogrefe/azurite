import Azurite.BasuPollackRoy.Chapter2.Section2_6.Proposition_2_99
import Azurite.BasuPollackRoy.Chapter2.Section2_6.RiPuiseux
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Theorem_2_91

/-! # BPR §2.6 Proposition 2.99 (part 3) — the complex case `C⟨ε⟩_b`

For `C = R[i]` with `R` real closed, the elements of `C⟨ε⟩_b` are exactly the elements of
`C⟨ε⟩` whose *modulus* is bounded over `R`.

A Puiseux series `z` over `C = R[i]` has a real and imaginary part `riReP z`, `riImP z` over `R`
(`RiPuiseux`), and a modulus `puiseuxModulus z = \sqrt{(riReP z)^2 + (riImP z)^2}` — a non-negative
Puiseux series over `R` (the square root exists because `R⟨⟨ε⟩⟩` is real closed, Theorem 2.91). The
key fact is that `z` has non-negative order over `C` iff its modulus has non-negative order over `R`:
the modulus squared is the sum of squares of the parts, whose order is twice the minimum of the
parts' orders, and `z`'s order over `C` is the same minimum (its `C`-coefficients vanish below an
exponent exactly when both parts do). Combined with part 2 applied to the modulus, this gives the
characterization. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ## Order of sums of non-negative series and of squares -/

omit [IsRealClosed R] in
/-- For non-negative `a ≤ b`, the larger element has the smaller (or equal) order. -/
theorem puiseuxOrder_antitone_of_nonneg {a b : PuiseuxSeries R} (ha : 0 ≤ a) (hab : a ≤ b) :
    puiseuxOrder R b ≤ puiseuxOrder R a := by
  by_contra h; rw [not_le] at h
  have key : puiseuxInitCoeff R (b - a) = -puiseuxInitCoeff R a := by
    rw [sub_eq_add_neg, puiseuxInitCoeff_add_eq_right _ _ (by rw [puiseuxOrder_neg]; exact h),
      puiseuxInitCoeff_neg]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · rw [← ha0, puiseuxOrder_zero] at h; exact absurd h (by simp)
  · have hIna : 0 < puiseuxInitCoeff R a := (puiseux_pos_iff a).mp ha0
    by_cases hbae : b - a = 0
    · rw [sub_eq_zero] at hbae; rw [hbae] at h; exact absurd h (lt_irrefl _)
    · have : 0 < puiseuxInitCoeff R (b - a) :=
        (puiseux_pos_iff _).mp (lt_of_le_of_ne (sub_nonneg.mpr hab) (Ne.symm hbae))
      rw [key] at this; linarith

omit [IsRealClosed R] in
/-- Order of a sum of two non-negative Puiseux series is the minimum of their orders. -/
theorem puiseuxOrder_add_of_nonneg {u v : PuiseuxSeries R} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    puiseuxOrder R (u + v) = min (puiseuxOrder R u) (puiseuxOrder R v) :=
  le_antisymm (le_min (puiseuxOrder_antitone_of_nonneg hu (le_add_of_nonneg_right hv))
    (puiseuxOrder_antitone_of_nonneg hv (le_add_of_nonneg_left hu))) (min_le_puiseuxOrder_add u v)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem zero_le_puiseuxOrder_sq (u : PuiseuxSeries R) :
    0 ≤ puiseuxOrder R (u ^ 2) ↔ 0 ≤ puiseuxOrder R u := by
  rw [sq, puiseuxOrder_mul]
  refine ⟨fun h => ?_, fun h => add_nonneg h h⟩
  by_contra hc; rw [not_le] at hc
  lift puiseuxOrder R u to ℚ using ne_top_of_lt hc with q
  rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at h
  rw [← WithTop.coe_zero, WithTop.coe_lt_coe] at hc
  linarith

omit [IsRealClosed R] in
theorem zero_le_puiseuxOrder_add_sq (u v : PuiseuxSeries R) :
    0 ≤ puiseuxOrder R (u ^ 2 + v ^ 2) ↔ (0 ≤ puiseuxOrder R u ∧ 0 ≤ puiseuxOrder R v) := by
  rw [puiseuxOrder_add_of_nonneg (sq_nonneg u) (sq_nonneg v), le_min_iff,
    zero_le_puiseuxOrder_sq, zero_le_puiseuxOrder_sq]

/-! ## Order and real/imaginary parts -/

theorem zero_le_puiseuxOrder_iff_coeff {K : Type*} [Field K] (x : PuiseuxSeries K) :
    0 ≤ puiseuxOrder K x ↔ ∀ q : ℚ, q < 0 → (x : HahnSeries ℚ K).coeff q = 0 := by
  rw [puiseuxOrder, show ((0 : WithTop ℚ) ≤ HahnSeries.orderTop (x : HahnSeries ℚ K))
      ↔ ∀ j : ℚ, (j : WithTop ℚ) < 0 → (x : HahnSeries ℚ K).coeff j = 0 from
    HahnSeries.le_orderTop_iff_forall]
  exact forall_congr' (fun q => by rw [← WithTop.coe_zero, WithTop.coe_lt_coe])

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- A Puiseux series over `R[i]` has non-negative order iff both its real and imaginary parts do (its
`R[i]`-coefficients vanish below an exponent exactly when both `reL` and `imL` of them do). -/
theorem zero_le_puiseuxOrder_iff_reP_imP (z : PuiseuxSeries (Ri R)) :
    0 ≤ puiseuxOrder (Ri R) z ↔
      0 ≤ puiseuxOrder R (riReP z) ∧ 0 ≤ puiseuxOrder R (riImP z) := by
  rw [zero_le_puiseuxOrder_iff_coeff, zero_le_puiseuxOrder_iff_coeff, zero_le_puiseuxOrder_iff_coeff]
  refine ⟨fun h => ⟨fun q hq => by rw [riReP_coe_coeff, h q hq, map_zero],
    fun q hq => by rw [riImP_coe_coeff, h q hq, map_zero]⟩, fun ⟨hr, hi⟩ q hq => ?_⟩
  have hc := Ri.of_reL_add_of_imL_mul_i ((z : HahnSeries ℚ (Ri R)).coeff q)
  rw [← riReP_coe_coeff, ← riImP_coe_coeff, hr q hq, hi q hq] at hc
  simpa using hc.symm

/-! ## The modulus and the bounded characterization -/

/-- The **modulus** of a Puiseux series over `C = R[i]`, as a non-negative Puiseux series over `R`:
`|z| = \sqrt{\mathrm{Re}(z)^2 + \mathrm{Im}(z)^2}`. The square root exists because `R⟨⟨ε⟩⟩` is real
closed (Theorem 2.91). -/
noncomputable def puiseuxModulus (z : PuiseuxSeries (Ri R)) : PuiseuxSeries R :=
  |(isSquare_of_nonneg (add_nonneg (sq_nonneg (riReP z)) (sq_nonneg (riImP z)))).choose|

theorem puiseuxModulus_nonneg (z : PuiseuxSeries (Ri R)) : 0 ≤ puiseuxModulus z := abs_nonneg _

theorem puiseuxModulus_sq (z : PuiseuxSeries (Ri R)) :
    puiseuxModulus z ^ 2 = riReP z ^ 2 + riImP z ^ 2 := by
  rw [puiseuxModulus, sq_abs, sq]
  exact (Classical.choose_spec
    (isSquare_of_nonneg (add_nonneg (sq_nonneg (riReP z)) (sq_nonneg (riImP z))))).symm

/-- `z` has non-negative order over `C = R[i]` iff its modulus has non-negative order over `R`. -/
theorem zero_le_puiseuxOrder_modulus_iff (z : PuiseuxSeries (Ri R)) :
    0 ≤ puiseuxOrder R (puiseuxModulus z) ↔ 0 ≤ puiseuxOrder (Ri R) z := by
  rw [← zero_le_puiseuxOrder_sq, puiseuxModulus_sq, zero_le_puiseuxOrder_add_sq,
    ← zero_le_puiseuxOrder_iff_reP_imP]

/-- **Proposition 2.99 (part 3).** For `C = R[i]` with `R` real closed, an algebraic Puiseux series
over `C` lies in `C⟨ε⟩_b` exactly when its modulus is bounded over `R` (less than a positive element
of `R`). -/
theorem mem_puiseuxBounded_iff_modulus_bounded (z : algebraicPuiseux (Ri R)) :
    z ∈ puiseuxBounded (Ri R) ↔
      ∃ a : R, 0 < a ∧
        puiseuxModulus (z : PuiseuxSeries (Ri R)) < algebraMap R (PuiseuxSeries R) a := by
  rw [mem_puiseuxBounded, ← zero_le_puiseuxOrder_modulus_iff, ← bounded_iff_puiseuxOrder_nonneg]
  simp only [abs_of_nonneg (puiseuxModulus_nonneg _)]

end Azurite.BPR
