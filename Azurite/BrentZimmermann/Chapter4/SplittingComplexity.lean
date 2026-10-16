/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.RectangularSplitting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Brent–Zimmermann §4.4.3: Complexity of rectangular series splitting

Rectangular splitting of a degree-`(jk − 1)` polynomial costs `O(j + k)` non-scalar
multiplications (`O(M(n))` each) and `O(jk)` scalar ones (`c(d) n` each, `c(d) = O(1)` in
practice); with `j ~ k ~ √d` this is `O(√d M(n) + d n c(d))` (4.24).  With argument reduction
first, the total is

  `T(n) = O((n/d) M(n) + √d M(n) + d n)`,

and the balance depends on `M(n)` against `n^(4/3)`:

1. `M(n) ≫ n^(4/3)` (schoolbook, Karatsuba, Toom–Cook 3 to 6, since `lg 3 > 4/3` … but not
   Toom–Cook 7, `log_7 13 < 4/3`): balance the first two terms, `d ~ n^(2/3)`,
   `T(n) = O(n^(1/3) M(n))`.
2. `M(n) ≪ n^(4/3)`: balance the first and last terms, `d ~ √M(n)`,
   `T(n) = Θ(n √M(n)) ≫ n^(3/2)`.  This does not reach the `O(n^(1+ε))` of AGM methods (§4.8).

Costs are modelled as real numbers; there is no operation-count model in the library, so what is
proven is the arithmetic of the balance:

* `splitCost n d M` — `(n/d) M + √d M + d n`; `splitCost_ge` — `≥ n^(1/3) M` for every `d ≥ 1`;
  `splitCost_le_case1` — `d = n^(2/3)`, `M ≥ n^(4/3)`: `≤ 3 n^(1/3) M`; `splitCost_le_case2` —
  `d = √M`, `n ≤ M ≤ n^(4/3)`: `≤ 3 n √M`; `rpow_three_halves_le_mul_sqrt` — `n √M ≥ n^(3/2)`.
* `four_thirds_lt_logb_iff` — `4/3 < log_b a ↔ b⁴ < a³`; the exponents `karatsuba_exponent`
  (`lg 3`), `toom3_exponent` (`log_3 5`), `toom4_exponent` (`log_4 7`), `toom5_exponent`
  (`log_5 9`), `toom6_exponent` (`log_6 11`, barely: `1331 > 1296`) are above `4/3`, and
  `toom7_exponent` (`log_7 13`) is below.
-/

namespace Azurite

namespace BZ

open Real

/-! ### The cost expression and its balance -/

/-- `T(n) = (n/d) M + √d M + d n`: argument reduction, non-scalar and scalar multiplications. -/
noncomputable def splitCost (n d M : ℝ) : ℝ := n / d * M + Real.sqrt d * M + d * n

theorem rpow_two_thirds_sqrt {n : ℝ} (hn : 0 ≤ n) :
    Real.sqrt (n ^ (2 / 3 : ℝ)) = n ^ (1 / 3 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn]; norm_num

theorem div_rpow_two_thirds {n : ℝ} (hn : 0 < n) : n / n ^ (2 / 3 : ℝ) = n ^ (1 / 3 : ℝ) := by
  rw [div_eq_iff (by positivity), ← Real.rpow_add hn]; norm_num

/-- For every `d ≥ 1` the cost is at least `n^(1/3) M`: below `d = n^(2/3)` the reduction term
is already that large, above it the non-scalar term is. -/
theorem splitCost_ge {n d M : ℝ} (hn : 1 ≤ n) (hd : 1 ≤ d) (hM : 0 ≤ M) :
    n ^ (1 / 3 : ℝ) * M ≤ splitCost n d M := by
  have hn0 : 0 < n := by linarith
  unfold splitCost
  have h3 : 0 ≤ d * n := by positivity
  rcases le_or_gt d (n ^ (2 / 3 : ℝ)) with h | h
  · have : n ^ (1 / 3 : ℝ) ≤ n / d := by
      rw [← div_rpow_two_thirds hn0]
      exact div_le_div_of_nonneg_left hn0.le (by linarith) h
    nlinarith [Real.sqrt_nonneg d, mul_le_mul_of_nonneg_right this hM]
  · have : n ^ (1 / 3 : ℝ) ≤ Real.sqrt d := by
      rw [← rpow_two_thirds_sqrt hn0.le]
      exact Real.sqrt_le_sqrt h.le
    have h1 : 0 ≤ n / d * M := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this hM]

/-- Case 1, `M ≥ n^(4/3)`, with `d = n^(2/3)`: `T ≤ 3 n^(1/3) M`, i.e. `T = O(n^(1/3) M(n))`. -/
theorem splitCost_le_case1 {n M : ℝ} (hn : 1 ≤ n) (hM : n ^ (4 / 3 : ℝ) ≤ M) :
    splitCost n (n ^ (2 / 3 : ℝ)) M ≤ 3 * n ^ (1 / 3 : ℝ) * M := by
  have hn0 : 0 < n := by linarith
  unfold splitCost
  rw [div_rpow_two_thirds hn0, rpow_two_thirds_sqrt hn0.le]
  have h3 : n ^ (2 / 3 : ℝ) * n = n ^ (1 / 3 : ℝ) * n ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_add hn0, show (1 / 3 : ℝ) + 4 / 3 = 2 / 3 + 1 by norm_num, Real.rpow_add hn0,
      Real.rpow_one]
  have h13 : 0 ≤ n ^ (1 / 3 : ℝ) := by positivity
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left hM h13]

/-- Case 2, `n ≤ M ≤ n^(4/3)`, with `d = √M`: `T ≤ 3 n √M`, i.e. `T = Θ(n √M(n))`. -/
theorem splitCost_le_case2 {n M : ℝ} (hn : 1 ≤ n) (hnM : n ≤ M) (hM : M ≤ n ^ (4 / 3 : ℝ)) :
    splitCost n (Real.sqrt M) M ≤ 3 * n * Real.sqrt M := by
  have hn0 : 0 < n := by linarith
  have hM0 : 0 < M := by linarith
  have hs0 : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  unfold splitCost
  -- `(n/√M) M = n √M`
  have h1 : n / Real.sqrt M * M = n * Real.sqrt M := by
    have : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0.le
    field_simp
    linear_combination (-1 : ℝ) * this
  -- `√(√M) M ≤ n √M` since `M^(1/4) ≤ n^(1/3)` and `n^(1/3) √M ≤ n`
  have h2 : Real.sqrt (Real.sqrt M) * M ≤ n * Real.sqrt M := by
    have hq : Real.sqrt (Real.sqrt M) = M ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hM0.le]; norm_num
    have hr : Real.sqrt M = M ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow M
    have hq_le : M ^ (1 / 4 : ℝ) ≤ n ^ (1 / 3 : ℝ) := by
      calc M ^ (1 / 4 : ℝ) ≤ (n ^ (4 / 3 : ℝ)) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow hM0.le hM (by norm_num)
        _ = n ^ (1 / 3 : ℝ) := by rw [← Real.rpow_mul hn0.le]; norm_num
    have hr_le : M ^ (1 / 2 : ℝ) ≤ n ^ (2 / 3 : ℝ) := by
      calc M ^ (1 / 2 : ℝ) ≤ (n ^ (4 / 3 : ℝ)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hM0.le hM (by norm_num)
        _ = n ^ (2 / 3 : ℝ) := by rw [← Real.rpow_mul hn0.le]; norm_num
    have hprod : n ^ (1 / 3 : ℝ) * n ^ (2 / 3 : ℝ) = n := by
      rw [← Real.rpow_add hn0]; norm_num
    rw [hq, hr]
    calc M ^ (1 / 4 : ℝ) * M ≤ n ^ (1 / 3 : ℝ) * M :=
          mul_le_mul_of_nonneg_right hq_le hM0.le
      _ = n ^ (1 / 3 : ℝ) * M ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hM0]; norm_num
      _ ≤ n ^ (1 / 3 : ℝ) * n ^ (2 / 3 : ℝ) * M ^ (1 / 2 : ℝ) := by gcongr
      _ = n * M ^ (1 / 2 : ℝ) := by rw [hprod]
  have h3 : Real.sqrt M * n = n * Real.sqrt M := mul_comm _ _
  rw [h1, h3]
  linarith

/-- `n √M ≥ n^(3/2)` once `M ≥ n`: case 2 is still well above `n^(3/2)`. -/
theorem rpow_three_halves_le_mul_sqrt {n M : ℝ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    n ^ (3 / 2 : ℝ) ≤ n * Real.sqrt M := by
  have hn0 : 0 < n := by linarith
  have : n ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, show n * n ^ (1 / 2 : ℝ) = n ^ (1 : ℝ) * n ^ (1 / 2 : ℝ) by
      rw [Real.rpow_one], ← Real.rpow_add hn0]
    norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnM) hn0.le

/-! ### Which multiplication algorithms fall in case 1 -/

/-- `4/3 < log_b a ↔ b⁴ < a³` for `b > 1`, `a > 0`. -/
theorem four_thirds_lt_logb_iff {a b : ℝ} (hb : 1 < b) (ha : 0 < a) :
    4 / 3 < Real.logb b a ↔ b ^ 4 < a ^ 3 := by
  have hlb : 0 < Real.log b := Real.log_pos hb
  rw [Real.logb, lt_div_iff₀ hlb]
  have h4 : Real.log (b ^ 4) = 4 * Real.log b := by rw [Real.log_pow]; norm_num
  have h3 : Real.log (a ^ 3) = 3 * Real.log a := by rw [Real.log_pow]; norm_num
  constructor
  · intro h
    have : Real.log (b ^ 4) < Real.log (a ^ 3) := by rw [h4, h3]; linarith
    exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp this
  · intro h
    have := Real.log_lt_log (by positivity) h
    rw [h4, h3] at this
    linarith

/-- Karatsuba: `lg 3 > 4/3` (`27 > 16`). -/
theorem karatsuba_exponent : 4 / 3 < Real.logb 2 3 :=
  (four_thirds_lt_logb_iff (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Toom–Cook 3: `log_3 5 > 4/3` (`125 > 81`). -/
theorem toom3_exponent : 4 / 3 < Real.logb 3 5 :=
  (four_thirds_lt_logb_iff (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Toom–Cook 4: `log_4 7 > 4/3` (`343 > 256`). -/
theorem toom4_exponent : 4 / 3 < Real.logb 4 7 :=
  (four_thirds_lt_logb_iff (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Toom–Cook 5: `log_5 9 > 4/3` (`729 > 625`). -/
theorem toom5_exponent : 4 / 3 < Real.logb 5 9 :=
  (four_thirds_lt_logb_iff (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Toom–Cook 6: `log_6 11 > 4/3` (`1331 > 1296`, barely). -/
theorem toom6_exponent : 4 / 3 < Real.logb 6 11 :=
  (four_thirds_lt_logb_iff (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Toom–Cook 7: `log_7 13 < 4/3` (`2197 < 2401`), so it falls in case 2. -/
theorem toom7_exponent : Real.logb 7 13 < 4 / 3 := by
  have hlb : 0 < Real.log 7 := Real.log_pos (by norm_num)
  rw [Real.logb, div_lt_iff₀ hlb]
  have : Real.log (13 ^ 3 : ℝ) < Real.log (7 ^ 4 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith

end BZ

end Azurite
