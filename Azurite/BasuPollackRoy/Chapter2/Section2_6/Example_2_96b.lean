import Azurite.BasuPollackRoy.Chapter2.Section2_6.Example_2_96
import Azurite.BasuPollackRoy.Chapter2.Section2_6.CharacteristicPolynomial

/-! # BPR §2.6 Example 2.96, continued — the next Newton-polygon step

The Newton polygon of `P₁` (Example 2.96) has the descending edge `E' = [M₀, M₁] = [(0,4/3),
(1,0)]`. Its slope is `−4/3` (so `ξ = 4/3`), and its characteristic polynomial is
`Q(P₁, E', X) = −3X + 1`. Choosing the root `x' = 1/3` and substituting `X = ε^{4/3}(1/3 + Y)`
yields the first two terms `ε^{1/3} + (1/3)ε^{5/3}` of a Puiseux-series root `x̄` of `P`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [CharZero R]

/-- The slope of the edge `E' = [(0,4/3), (1,0)]` is `−4/3` (so `ξ = 4/3`). -/
theorem slope_E1 : newtonSlope ((0 : ℕ), (4 / 3 : ℚ)) ((1 : ℕ), (0 : ℚ)) = -4 / 3 := by
  rw [newtonSlope]; norm_num

/-- `In(b₀) = 1` (the coefficient of the lowest-order term `ε^{4/3}` of `b₀`). -/
theorem initCoeff_b0 : puiseuxInitCoeff R (exP1.coeff 0) = 1 := by
  rw [puiseuxInitCoeff, coe_b0,
    HahnSeries.leadingCoeff_add_eq_right (by
      rw [HahnSeries.orderTop_single one_ne_zero, HahnSeries.orderTop_neg,
        HahnSeries.orderTop_single one_ne_zero, WithTop.coe_lt_coe]; norm_num),
    HahnSeries.leadingCoeff_of_single]

/-- `In(b₁) = −3` (the surviving order-`0` constant of `b₁`). -/
theorem initCoeff_b1 : puiseuxInitCoeff R (exP1.coeff 1) = -3 := by
  rw [puiseuxInitCoeff, coe_b1,
    show (HahnSeries.single (5 / 3) 1 - HahnSeries.single 0 3 + HahnSeries.single (4 / 3) 4
        : HahnSeries ℚ R)
      = -HahnSeries.single 0 3 + (HahnSeries.single (5 / 3) 1 + HahnSeries.single (4 / 3) 4)
      from by ring,
    HahnSeries.leadingCoeff_add_eq_left (by
      rw [HahnSeries.orderTop_neg, HahnSeries.orderTop_single (by norm_num : (3 : R) ≠ 0)]
      refine lt_of_lt_of_le ?_ HahnSeries.min_orderTop_le_orderTop_add
      rw [HahnSeries.orderTop_single one_ne_zero,
        HahnSeries.orderTop_single (by norm_num : (4 : R) ≠ 0), lt_min_iff]
      constructor <;> (rw [WithTop.coe_lt_coe]; norm_num)),
    HahnSeries.leadingCoeff_neg, HahnSeries.leadingCoeff_of_single]

open Classical in
/-- The columns on the edge `E'` are exactly its endpoints `0` and `1`. -/
theorem filter_E1 :
    (Finset.Icc (0 : ℕ) 1).filter (colOnLine (exP1 (R := R)) ((0 : ℕ), (4 / 3 : ℚ))
      ((1 : ℕ), (0 : ℚ))) = {0, 1} := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, hn1⟩, _⟩; interval_cases n
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨by omega, colOnLine_left order_exP1_coeff0⟩
    · exact ⟨by omega, colOnLine_right (by norm_num) order_exP1_coeff1⟩

/-- **The characteristic polynomial of `E'` is `−3X + 1`** (`= 1 − 3X`). -/
theorem charPoly_E1 :
    charPoly (exP1 (R := R)) ((0 : ℕ), (4 / 3 : ℚ)) ((1 : ℕ), (0 : ℚ)) = 1 - 3 * X := by
  rw [charPoly, filter_E1, Finset.sum_insert (by norm_num), Finset.sum_singleton, initCoeff_b0,
    initCoeff_b1, Polynomial.monomial_zero_left, map_one,
    show monomial 1 (-3 : R) = -3 * X from by
      rw [← C_mul_X_pow_eq_monomial, pow_one, map_neg, map_ofNat]]
  ring

/-- The root of `Q(P₁, E', X) = 1 − 3X` is `x' = 1/3`. -/
theorem charPoly_E1_root : (1 - 3 * X : Polynomial R).IsRoot (1 / 3) := by
  simp [Polynomial.IsRoot, Polynomial.eval_sub]

/-- The first two terms `ε^{1/3} + (1/3)ε^{5/3}` of the Puiseux-series root `x̄` of `P`,
obtained from `x̄ = ε^{1/3}(1 + ε^{4/3}(1/3 + Y))` by dropping the `Y`-term. -/
noncomputable def rootApprox : PuiseuxSeries R :=
  puiseuxMonomial (1 / 3) + (1 / 3) * puiseuxMonomial (5 / 3)

/-- The recentering `ε^{1/3}(1 + ε^{4/3}(1/3 + Y))` expands as
`ε^{1/3} + (1/3)ε^{5/3} + ε^{5/3} Y`, whose constant (`Y = 0`) part is `rootApprox`. -/
theorem rootApprox_eq :
    (puiseuxMonomial (1 / 3) * (1 + puiseuxMonomial (4 / 3) * (1 / 3)) : PuiseuxSeries R)
      = rootApprox := by
  rw [rootApprox, mul_add, mul_one, ← mul_assoc, puiseuxMonomial_mul,
    show (1 : ℚ) / 3 + 4 / 3 = 5 / 3 by norm_num, mul_comm (puiseuxMonomial (5 / 3)) (1 / 3)]

end Azurite.BPR
