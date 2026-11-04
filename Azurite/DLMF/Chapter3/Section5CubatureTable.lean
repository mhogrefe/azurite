/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Cubature

/-!
# DLMF §3.5(x): Table 3.5.21

The seven rules (`diskRule1`–`diskRule4`, `squareRule1`–`squareRule3`, in the order of the table;
the last square rule with the corner coordinates `(±√(3/5) h, ±√(3/5) h)` as corrected in V1.0.7)
are exact on all monomials of degree `≤ 3` resp. `≤ 5` (`diskRule1_exact`, …, `squareRule3_exact`),
so `R = O(h⁴)` resp. `O(h⁶)` for `f ∈ C⁴` resp. `C⁶` (`dlmf_table_3_5_21_disk1`, …,
`dlmf_table_3_5_21_square3`). All entries are correct.
-/

open Filter Topology

namespace Azurite.DLMF

/-! ### The rules (`(w, ξ, η)`, nodes `(ξh, ηh)`) -/

/-- Disk, 5 points: `(0,0)` with `1/2`; `(±h,0)`, `(0,±h)` with `1/8`. -/
noncomputable def diskRule1 : List (ℝ × ℝ × ℝ) :=
  [(1 / 2, 0, 0), (1 / 8, 1, 0), (1 / 8, -1, 0), (1 / 8, 0, 1), (1 / 8, 0, -1)]

/-- Disk, 4 points: `(±h/2, ±h/2)` with `1/4`. -/
noncomputable def diskRule2 : List (ℝ × ℝ × ℝ) :=
  [(1 / 4, 1 / 2, 1 / 2), (1 / 4, 1 / 2, -1 / 2), (1 / 4, -1 / 2, 1 / 2), (1 / 4, -1 / 2, -1 / 2)]

/-- Disk, 9 points: `(0,0)` with `1/6`; `(±h,0)`, `(0,±h)` with `1/24`; `(±h/2, ±h/2)` with
`1/6`. -/
noncomputable def diskRule3 : List (ℝ × ℝ × ℝ) :=
  [(1 / 6, 0, 0), (1 / 24, 1, 0), (1 / 24, -1, 0), (1 / 24, 0, 1), (1 / 24, 0, -1),
    (1 / 6, 1 / 2, 1 / 2), (1 / 6, 1 / 2, -1 / 2), (1 / 6, -1 / 2, 1 / 2),
    (1 / 6, -1 / 2, -1 / 2)]

/-- Disk, 7 points: `(0,0)` with `1/4`; `(±√6 h/3, 0)` and `(±√6 h/6, ±√2 h/2)` with `1/8`. -/
noncomputable def diskRule4 : List (ℝ × ℝ × ℝ) :=
  [(1 / 4, 0, 0), (1 / 8, √6 / 3, 0), (1 / 8, -(√6 / 3), 0), (1 / 8, √6 / 6, √2 / 2),
    (1 / 8, √6 / 6, -(√2 / 2)), (1 / 8, -(√6 / 6), √2 / 2), (1 / 8, -(√6 / 6), -(√2 / 2))]

/-- Square, 9 points: `(0,0)` with `4/9`; `(±h,0)`, `(0,±h)` with `1/9`; `(±h, ±h)` with
`1/36`. -/
noncomputable def squareRule1 : List (ℝ × ℝ × ℝ) :=
  [(4 / 9, 0, 0), (1 / 9, 1, 0), (1 / 9, -1, 0), (1 / 9, 0, 1), (1 / 9, 0, -1),
    (1 / 36, 1, 1), (1 / 36, 1, -1), (1 / 36, -1, 1), (1 / 36, -1, -1)]

/-- Square, 4 points: `(±√3 h/3, ±√3 h/3)` with `1/4`. -/
noncomputable def squareRule2 : List (ℝ × ℝ × ℝ) :=
  [(1 / 4, √3 / 3, √3 / 3), (1 / 4, √3 / 3, -(√3 / 3)), (1 / 4, -(√3 / 3), √3 / 3),
    (1 / 4, -(√3 / 3), -(√3 / 3))]

/-- Square, 9 points: `(0,0)` with `16/81`; `(±√(3/5) h, 0)`, `(0, ±√(3/5) h)` with `10/81`;
`(±√(3/5) h, ±√(3/5) h)` with `25/324`. -/
noncomputable def squareRule3 : List (ℝ × ℝ × ℝ) :=
  [(16 / 81, 0, 0), (10 / 81, √(3 / 5), 0), (10 / 81, -√(3 / 5), 0), (10 / 81, 0, √(3 / 5)),
    (10 / 81, 0, -√(3 / 5)), (25 / 324, √(3 / 5), √(3 / 5)), (25 / 324, √(3 / 5), -√(3 / 5)),
    (25 / 324, -√(3 / 5), √(3 / 5)), (25 / 324, -√(3 / 5), -√(3 / 5))]

/-! ### Exactness on monomials -/

theorem sqrt6_sq : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

theorem sqrt6_pow4 : √6 ^ 4 = 36 := by
  calc √6 ^ 4 = (√6 ^ 2) ^ 2 := by ring
    _ = _ := by rw [sqrt6_sq]; norm_num

theorem sqrt2_sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt2_pow4 : √2 ^ 4 = 4 := by
  calc √2 ^ 4 = (√2 ^ 2) ^ 2 := by ring
    _ = _ := by rw [sqrt2_sq]; norm_num

theorem sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt3_pow4 : √3 ^ 4 = 9 := by
  calc √3 ^ 4 = (√3 ^ 2) ^ 2 := by ring
    _ = _ := by rw [sqrt3_sq]; norm_num

theorem sqrt35_sq : √(3 / 5 : ℝ) ^ 2 = 3 / 5 := Real.sq_sqrt (by norm_num)

theorem sqrt35_pow4 : √(3 / 5 : ℝ) ^ 4 = 9 / 25 := by
  calc √(3 / 5 : ℝ) ^ 4 = (√(3 / 5 : ℝ) ^ 2) ^ 2 := by ring
    _ = _ := by rw [sqrt35_sq]; norm_num

theorem sqrt5_sq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem sqrt5_pow4 : √5 ^ 4 = 25 := by
  calc √5 ^ 4 = (√5 ^ 2) ^ 2 := by ring
    _ = _ := by rw [sqrt5_sq]; norm_num

/-- Expand a rule on a monomial and simplify the square roots. -/
macro "cub_check" rule:ident : tactic =>
  `(tactic| (simp only [cubSum, $rule:ident, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] <;> norm_num [thetaQ] <;> ring_nf <;>
      simp only [sqrt6_sq, sqrt6_pow4, sqrt2_sq, sqrt2_pow4, sqrt3_sq, sqrt3_pow4, sqrt35_sq,
        sqrt35_pow4, sqrt5_sq, sqrt5_pow4] <;> norm_num [sqrt5_sq, sqrt5_pow4]))

theorem diskRule1_exact (a b : ℕ) (hab : a + b ≤ 3) :
    cubSum diskRule1 1 (fun p => p.1 ^ a * p.2 ^ b) = (thetaQ a b : ℝ) / (a + b + 2) := by
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> first | (exfalso; omega) | cub_check diskRule1

theorem diskRule2_exact (a b : ℕ) (hab : a + b ≤ 3) :
    cubSum diskRule2 1 (fun p => p.1 ^ a * p.2 ^ b) = (thetaQ a b : ℝ) / (a + b + 2) := by
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> first | (exfalso; omega) | cub_check diskRule2

theorem diskRule3_exact (a b : ℕ) (hab : a + b ≤ 5) :
    cubSum diskRule3 1 (fun p => p.1 ^ a * p.2 ^ b) = (thetaQ a b : ℝ) / (a + b + 2) := by
  have ha : a ≤ 5 := by omega
  have hb : b ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;> first | (exfalso; omega) | cub_check diskRule3

theorem diskRule4_exact (a b : ℕ) (hab : a + b ≤ 5) :
    cubSum diskRule4 1 (fun p => p.1 ^ a * p.2 ^ b) = (thetaQ a b : ℝ) / (a + b + 2) := by
  have ha : a ≤ 5 := by omega
  have hb : b ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;> first | (exfalso; omega) | cub_check diskRule4

/-- The normalized square moment `(1 − (−1)^{a+1})/(2(a+1))` (`1/(a+1)` for even `a`, else `0`). -/
theorem squareRule1_exact (a b : ℕ) (hab : a + b ≤ 3) :
    cubSum squareRule1 1 (fun p => p.1 ^ a * p.2 ^ b) =
      (1 - (-1) ^ (a + 1)) / (2 * (a + 1)) * ((1 - (-1) ^ (b + 1)) / (2 * (b + 1))) := by
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> first | (exfalso; omega) | cub_check squareRule1

theorem squareRule2_exact (a b : ℕ) (hab : a + b ≤ 3) :
    cubSum squareRule2 1 (fun p => p.1 ^ a * p.2 ^ b) =
      (1 - (-1) ^ (a + 1)) / (2 * (a + 1)) * ((1 - (-1) ^ (b + 1)) / (2 * (b + 1))) := by
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> first | (exfalso; omega) | cub_check squareRule2

theorem squareRule3_exact (a b : ℕ) (hab : a + b ≤ 5) :
    cubSum squareRule3 1 (fun p => p.1 ^ a * p.2 ^ b) =
      (1 - (-1) ^ (a + 1)) / (2 * (a + 1)) * ((1 - (-1) ^ (b + 1)) / (2 * (b + 1))) := by
  have ha : a ≤ 5 := by omega
  have hb : b ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;> first | (exfalso; omega) | cub_check squareRule3

/-! ### Table 3.5.21 -/

theorem abs_sqrt_div_le_one {x c : ℝ} (hc : 0 < c) (h : x ≤ c ^ 2) : |√x / c| ≤ 1 := by
  rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hc.le), div_le_one hc]
  calc √x ≤ √(c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc.le

theorem abs_sqrt_le_one {x : ℝ} (h : x ≤ 1) : |√x| ≤ 1 := by
  simpa using abs_sqrt_div_le_one (c := 1) one_pos (by simpa using h)

/-- Node bounds `|ξ|, |η| ≤ 1`. -/
macro "node_check" rule:ident : tactic =>
  `(tactic| (simp only [$rule:ident, List.forall_mem_cons, List.forall_mem_nil, and_true] <;>
    constructorm* _ ∧ _ <;> (try simp only [abs_neg]) <;>
      first
      | exact abs_sqrt_div_le_one (by norm_num) (by norm_num)
      | exact abs_sqrt_le_one (by norm_num)
      | norm_num))

theorem diskRule1_nodes : ∀ q ∈ diskRule1, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1 := by node_check diskRule1

theorem diskRule2_nodes : ∀ q ∈ diskRule2, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1 := by node_check diskRule2

theorem diskRule3_nodes : ∀ q ∈ diskRule3, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1 := by node_check diskRule3

theorem diskRule4_nodes : ∀ q ∈ diskRule4, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1 := by node_check diskRule4

theorem squareRule1_nodes : ∀ q ∈ squareRule1, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1 := by
  node_check squareRule1

theorem squareRule2_nodes : ∀ q ∈ squareRule2, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1 := by
  node_check squareRule2

theorem squareRule3_nodes : ∀ q ∈ squareRule3, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1 := by
  node_check squareRule3

/-- **Table 3.5.21**, disk, `(0,0)`, `(±h,0)`, `(0,±h)`: `R = O(h⁴)` for `f ∈ C⁴`. -/
theorem dlmf_table_3_5_21_disk1 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) :
    (fun h => diskRem diskRule1 h f) =O[𝓝[>] 0] fun h => h ^ 4 :=
  diskRem_isBigO (n := 3) (by norm_num) diskRule1_nodes diskRule1_exact hf

/-- **Table 3.5.21**, disk, `(±h/2, ±h/2)`: `R = O(h⁴)` for `f ∈ C⁴`. -/
theorem dlmf_table_3_5_21_disk2 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) :
    (fun h => diskRem diskRule2 h f) =O[𝓝[>] 0] fun h => h ^ 4 :=
  diskRem_isBigO (n := 3) (by norm_num) diskRule2_nodes diskRule2_exact hf

/-- **Table 3.5.21**, disk, 9 points: `R = O(h⁶)` for `f ∈ C⁶`. -/
theorem dlmf_table_3_5_21_disk3 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 6 f) :
    (fun h => diskRem diskRule3 h f) =O[𝓝[>] 0] fun h => h ^ 6 :=
  diskRem_isBigO (n := 5) le_rfl diskRule3_nodes diskRule3_exact hf

/-- **Table 3.5.21**, disk, 7 points (regular hexagon of radius `√(2/3) h` and center):
`R = O(h⁶)` for `f ∈ C⁶`. -/
theorem dlmf_table_3_5_21_disk4 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 6 f) :
    (fun h => diskRem diskRule4 h f) =O[𝓝[>] 0] fun h => h ^ 6 :=
  diskRem_isBigO (n := 5) le_rfl diskRule4_nodes diskRule4_exact hf

/-- **Table 3.5.21**, square, 9 points with weights `4/9, 1/9, 1/36`: `R = O(h⁴)` for `f ∈ C⁴`. -/
theorem dlmf_table_3_5_21_square1 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) :
    (fun h => squareRem squareRule1 h f) =O[𝓝[>] 0] fun h => h ^ 4 :=
  squareRem_isBigO (n := 3) squareRule1_nodes squareRule1_exact hf

/-- **Table 3.5.21**, square, `(±√3 h/3, ±√3 h/3)`: `R = O(h⁴)` for `f ∈ C⁴`. -/
theorem dlmf_table_3_5_21_square2 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) :
    (fun h => squareRem squareRule2 h f) =O[𝓝[>] 0] fun h => h ^ 4 :=
  squareRem_isBigO (n := 3) squareRule2_nodes squareRule2_exact hf

/-- **Table 3.5.21**, square, 9 points (product Gauss rule, corners as corrected in V1.0.7):
`R = O(h⁶)` for `f ∈ C⁶`. -/
theorem dlmf_table_3_5_21_square3 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 6 f) :
    (fun h => squareRem squareRule3 h f) =O[𝓝[>] 0] fun h => h ^ 6 :=
  squareRem_isBigO (n := 5) squareRule3_nodes squareRule3_exact hf

end Azurite.DLMF
