/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5GaussLaguerre

/-!
# DLMF §3.5(v): Tables 3.5.6–3.5.9 (Gauss–Laguerre nodes and weights)

All printed nodes and weights of Tables 3.5.6–3.5.9 (`α = 0`, `n = 5, 10, 15, 20`) are certified
by exact `Nat`/`Int` arithmetic in the kernel (`decide +kernel`).

* `lagS j m D = j! D^j L_j(m/D)` (`lagS_spec`), `lagH` (`lagH_spec`) for `∑_{j<n} L_j²`, and
  integer Lipschitz majorants `lagA`, `lagC`, `lagK` on `[0, R]` (`lagK_spec`).
* Each row (`lagRowOK`, `lagRowOK_sound`) brackets a sign change of `L_n` on `(a/D, (a+1)/D)`,
  checks the printed node, and checks the printed weight `1/∑ L_j(x)²` with the error bound.
* `lagNodes`, `lagWeight` (`mem_lagNodes_iff`, `card_lagNodes`, `lagWeight_eq`), `LagTableSpec`,
  and `lagTableOK_sound` (completeness: `n` disjoint brackets give all `n` nodes).
* `dlmf_table_3_5_6` … `dlmf_table_3_5_9`.
* Errata in Table 3.5.7 (`dlmf_table_3_5_7_erratum_0`, `dlmf_table_3_5_7_erratum_3`): the weights
  printed as `0.308441115765020141` and `0.620874560986777475 × 10⁻¹` should end in `…142` and
  `…474`.
-/

open Polynomial Finset Set Real

namespace Azurite.DLMF

/-! ### Exact integer evaluation of `L_j = ∑_i (−1)^i C(j, i) x^i/i!` -/

/-- `c(j, i) = C(j, i) j!/i! = (j!)²/((i!)² (j − i)!)`. -/
def lagc (j i : ℕ) : ℕ :=
  j.factorial * j.factorial / (i.factorial * i.factorial * (j - i).factorial)

theorem lagc_eq {j i : ℕ} (hi : i ≤ j) :
    (lagc j i : ℝ) = j.choose i * j.factorial / i.factorial := by
  have h1 : i.factorial * (j - i).factorial ∣ j.factorial :=
    Nat.factorial_mul_factorial_dvd_factorial hi
  have h2 : i.factorial ∣ j.factorial := Nat.factorial_dvd_factorial hi
  have hd : i.factorial * i.factorial * (j - i).factorial ∣ j.factorial * j.factorial := by
    rw [show i.factorial * i.factorial * (j - i).factorial =
      (i.factorial * (j - i).factorial) * i.factorial by ring]
    exact Nat.mul_dvd_mul h1 h2
  rw [lagc, Nat.cast_div hd (by positivity), Nat.choose_eq_factorial_div_factorial hi,
    Nat.cast_div h1 (by positivity)]
  push_cast
  have : (i.factorial : ℝ) ≠ 0 := by positivity
  have : ((j - i).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- `S_j(m, D) = j! Dʲ L_j(m/D)`. -/
def lagS (j : ℕ) (m D : ℤ) : ℤ :=
  ∑ i ∈ range (j + 1), (-1) ^ i * (lagc j i : ℤ) * m ^ i * D ^ (j - i)

theorem lagS_spec (j : ℕ) {m D : ℤ} {x : ℝ} (hm : (m : ℝ) = x * D) :
    (lagS j m D : ℝ) = j.factorial * (D : ℝ) ^ j * (lagL 0 j).eval x := by
  rw [lagS, eval_lagL_zero, mul_sum]
  push_cast
  refine sum_congr rfl fun i hi => ?_
  have hi := mem_range.mp hi
  rw [lagc_eq (by omega), hm, mul_pow, show (D : ℝ) ^ j = (D : ℝ) ^ (j - i) * (D : ℝ) ^ i by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]]
  have : (i.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- `G(x) = ∑_{j<n} L_j(x)²`, the reciprocal of the weight at a node. -/
noncomputable def lagG (n : ℕ) (x : ℝ) : ℝ := ∑ j ∈ range n, (lagL 0 j).eval x ^ 2

/-- `H = ((n−1)!)² D^{2(n−1)} G(m/D)`. -/
def lagH (n : ℕ) (m D : ℤ) : ℤ :=
  ∑ j ∈ range n, lagS j m D ^ 2 * (((n - 1).factorial / j.factorial : ℕ) : ℤ) ^ 2 *
    D ^ (2 * (n - 1 - j))

theorem lagH_spec (n : ℕ) {m D : ℤ} (hD : D ≠ 0) {x : ℝ} (hm : (m : ℝ) = x * D) :
    (lagH n m D : ℝ) = ((n - 1).factorial : ℝ) ^ 2 * (D : ℝ) ^ (2 * (n - 1)) * lagG n x := by
  rw [lagH, lagG, mul_sum, Int.cast_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [lagS_spec j hm, Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity)]
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  rw [show (D : ℝ) ^ (2 * (n - 1)) = (D : ℝ) ^ (2 * (n - 1 - j)) * ((D : ℝ) ^ j) ^ 2 by
    rw [← pow_mul, ← pow_add]; congr 1; omega]
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### Majorants on `[0, R]` -/

theorem abs_pow_sub_pow_le {x y R : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R) (hy : 0 ≤ y) (hyR : y ≤ R)
    (i : ℕ) : |x ^ i - y ^ i| ≤ i * R ^ (i - 1) * |x - y| := by
  rw [← geom_sum₂_mul, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ range i, |x ^ k * y ^ (i - 1 - k)| ≤ ∑ k ∈ range i, R ^ (i - 1) := by
        refine sum_le_sum fun k hk => ?_
        have hk := mem_range.mp hk
        rw [abs_of_nonneg (by positivity), show R ^ (i - 1) = R ^ k * R ^ (i - 1 - k) by
          rw [← pow_add]; congr 1; omega]
        exact mul_le_mul (pow_le_pow_left₀ hx hxR _) (pow_le_pow_left₀ hy hyR _)
          (pow_nonneg hy _) (pow_nonneg (hx.trans hxR) _)
    _ = i * R ^ (i - 1) := by simp

/-- `A_j = ∑_i c(j, i) Rⁱ ≥ j! |L_j|` on `[0, R]`. -/
def lagA (j R : ℕ) : ℕ := ∑ i ∈ range (j + 1), lagc j i * R ^ i

/-- `C_j = ∑_i c(j, i) i R^{i−1}`, a Lipschitz constant of `j! L_j` on `[0, R]`. -/
def lagC (j R : ℕ) : ℕ := ∑ i ∈ range (j + 1), lagc j i * i * R ^ (i - 1)

/-- `K = ∑_{j<n} 2 A_j C_j ((n−1)!/j!)²`, a Lipschitz constant of `((n−1)!)² G` on `[0, R]`. -/
def lagK (n R : ℕ) : ℕ :=
  ∑ j ∈ range n, 2 * lagA j R * lagC j R * ((n - 1).factorial / j.factorial) ^ 2

theorem fact_mul_eval_lagL (j : ℕ) (x : ℝ) :
    (j.factorial : ℝ) * (lagL 0 j).eval x =
      ∑ i ∈ range (j + 1), (-1) ^ i * (lagc j i : ℝ) * x ^ i := by
  rw [eval_lagL_zero, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [lagc_eq (by have := mem_range.mp hi; omega)]
  ring

theorem lagA_spec (j R : ℕ) {x : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R) :
    (j.factorial : ℝ) * |(lagL 0 j).eval x| ≤ lagA j R := by
  rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ j.factorial), ← abs_mul, fact_mul_eval_lagL,
    lagA]
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, abs_pow,
    abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxR _) (by positivity)

theorem lagC_spec (j R : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R) (hy : 0 ≤ y) (hyR : y ≤ R) :
    (j.factorial : ℝ) * |(lagL 0 j).eval x - (lagL 0 j).eval y| ≤ lagC j R * |x - y| := by
  rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ j.factorial), ← abs_mul, mul_sub,
    fact_mul_eval_lagL, fact_mul_eval_lagL, ← sum_sub_distrib, lagC]
  push_cast
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  calc (lagc j i : ℝ) * |x ^ i - y ^ i| ≤ lagc j i * (i * R ^ (i - 1) * |x - y|) :=
        mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le hx hxR hy hyR i) (by positivity)
    _ = _ := by ring

theorem lagK_spec (n R : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R) (hy : 0 ≤ y) (hyR : y ≤ R) :
    ((n - 1).factorial : ℝ) ^ 2 * |lagG n x - lagG n y| ≤ lagK n R * |x - y| := by
  rw [lagG, lagG, ← sum_sub_distrib, lagK]
  push_cast
  rw [sum_mul]
  rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n - 1).factorial : ℝ) ^ 2), ← abs_mul,
    mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  have hj := mem_range.mp hj
  rw [Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity)]
  have hf : (0 : ℝ) < j.factorial := by positivity
  set a := (lagL 0 j).eval x
  set b := (lagL 0 j).eval y
  have hA := lagA_spec j R hx hxR
  have hA' := lagA_spec j R hy hyR
  have hC := lagC_spec j R hx hxR hy hyR
  have hab : (j.factorial : ℝ) * |a + b| ≤ 2 * lagA j R := by
    have := abs_add_le a b; nlinarith
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n - 1).factorial : ℝ) ^ 2)]
  have key : (j.factorial : ℝ) ^ 2 * (|a - b| * |a + b|) ≤ lagC j R * |x - y| * (2 * lagA j R) := by
    calc (j.factorial : ℝ) ^ 2 * (|a - b| * |a + b|) =
        ((j.factorial : ℝ) * |a - b|) * ((j.factorial : ℝ) * |a + b|) := by ring
      _ ≤ (lagC j R * |x - y|) * (2 * lagA j R) :=
        mul_le_mul hC hab (by positivity) (by positivity)
  calc ((n - 1).factorial : ℝ) ^ 2 * (|a - b| * |a + b|) =
      (((n - 1).factorial : ℝ) / j.factorial) ^ 2 *
        ((j.factorial : ℝ) ^ 2 * (|a - b| * |a + b|)) := by
        field_simp
    _ ≤ (((n - 1).factorial : ℝ) / j.factorial) ^ 2 * (lagC j R * |x - y| * (2 * lagA j R)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

/-! ### Certified rows -/

/-- A row: the bracket `(a/D, (a+1)/D)` of a node, the printed node `X/10^{sx}` and the printed
weight `W/10^{sw}` (DLMF's mantissa-and-exponent form, `s = digits − exponent`). -/
structure LagRow where
  a : ℕ
  X : ℕ
  sx : ℕ
  W : ℕ
  sw : ℕ

/-- `((n−1)!)² D^{2(n−1)}` and the Lipschitz error `K D^{2n−3}` of `H` over the bracket. -/
def lagDen (n D : ℕ) : ℤ := ((n - 1).factorial : ℤ) ^ 2 * (D : ℤ) ^ (2 * (n - 1))
def lagE (n D R : ℕ) : ℤ := (lagK n R : ℤ) * (D : ℤ) ^ (2 * n - 3)

/-- The exact checks for one row. -/
def lagRowOK (n D R : ℕ) (r : LagRow) : Bool :=
  let H := lagH n r.a D
  decide (0 < r.W) && decide (0 < r.a) && decide (r.a + 1 ≤ R * D) &&
    decide (lagS n r.a D * lagS n (r.a + 1) D < 0) &&
    decide ((10 * (r.X : ℤ) - 5) * D ≤ r.a * 10 ^ (r.sx + 1)) &&
    decide (((r.a : ℤ) + 1) * 10 ^ (r.sx + 1) ≤ (10 * r.X + 5) * D) &&
    decide (10 ^ (r.sw + 1) * lagDen n D ≤ (10 * (r.W : ℤ) + 5) * (H - lagE n D R)) &&
    decide ((10 * (r.W : ℤ) - 5) * (H + lagE n D R) ≤ 10 ^ (r.sw + 1) * lagDen n D)

/-- The printed weight `Wp/10^{sw}` is too large. -/
def lagBelow (n D R : ℕ) (r : LagRow) (Wp : ℕ) : Bool :=
  decide (0 < Wp) &&
    decide (10 ^ (r.sw + 1) * lagDen n D < (10 * (Wp : ℤ) - 5) * (lagH n r.a D - lagE n D R))

/-- The printed weight `Wp/10^{sw}` is too small. -/
def lagAbove (n D R : ℕ) (r : LagRow) (Wp : ℕ) : Bool :=
  decide ((10 * (Wp : ℤ) + 5) * (lagH n r.a D + lagE n D R) < 10 ^ (r.sw + 1) * lagDen n D)

theorem lag_abs_le_half_ulp {x X : ℝ} {d : ℕ} (h1 : (10 * X - 5) / 10 ^ (d + 1) ≤ x)
    (h2 : x ≤ (10 * X + 5) / 10 ^ (d + 1)) : |x - X / 10 ^ d| ≤ 5 / 10 ^ (d + 1) := by
  have e1 : (10 * X - 5) / 10 ^ (d + 1) = X / 10 ^ d - 5 / 10 ^ (d + 1) := by
    rw [pow_succ]; field_simp
  have e2 : (10 * X + 5) / 10 ^ (d + 1) = X / 10 ^ d + 5 / 10 ^ (d + 1) := by
    rw [pow_succ]; field_simp
  rw [abs_le]; constructor <;> linarith

theorem lagRowOK_sound {n D R : ℕ} (hn : 2 ≤ n) {r : LagRow} (h : lagRowOK n D R r = true) :
    ∃ x : ℝ, (r.a : ℝ) / D < x ∧ x < ((r.a : ℝ) + 1) / D ∧ x ≤ R ∧
      (lagL 0 n).eval x = 0 ∧ |x - r.X / 10 ^ r.sx| ≤ 5 / 10 ^ (r.sx + 1) ∧
      |1 / lagG n x - r.W / 10 ^ r.sw| ≤ 5 / 10 ^ (r.sw + 1) ∧
      (∀ Wp, lagBelow n D R r Wp = true →
        1 / lagG n x < Wp / 10 ^ r.sw - 5 / 10 ^ (r.sw + 1)) ∧
      (∀ Wp, lagAbove n D R r Wp = true →
        (Wp : ℝ) / 10 ^ r.sw + 5 / 10 ^ (r.sw + 1) < 1 / lagG n x) := by
  simp only [lagRowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hW0, ha0⟩, hbR⟩, hsgn⟩, hX1⟩, hX2⟩, hW1⟩, hW2⟩ := h
  have hD0 : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · rw [h0, mul_zero] at hbR; omega
    · exact h0
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD0
  set l : ℝ := (r.a : ℝ) / D
  set u : ℝ := ((r.a : ℝ) + 1) / D
  have hl0 : 0 < l := div_pos (by exact_mod_cast ha0) hDr
  have hlu : l < u := div_lt_div_of_pos_right (by linarith) hDr
  have huR : u ≤ R := by
    rw [div_le_iff₀ hDr]; exact_mod_cast hbR
  have hlD : ((r.a : ℤ) : ℝ) = l * ((D : ℤ) : ℝ) := by simp only [l]; push_cast; field_simp
  have huD : (((r.a : ℤ) + 1 : ℤ) : ℝ) = u * ((D : ℤ) : ℝ) := by
    simp only [u]; push_cast; field_simp
  have hRa := lagS_spec n hlD
  have hRb := lagS_spec n huD
  have hHa := lagH_spec n (by exact_mod_cast hD0.ne') hlD
  simp only [Int.cast_natCast] at hRa hRb hHa
  -- a zero in `(l, u)`
  have hsgnR : (lagL 0 n).eval l * (lagL 0 n).eval u < 0 := by
    have : ((lagS n r.a D : ℤ) : ℝ) * (lagS n (r.a + 1) D : ℤ) < 0 := by exact_mod_cast hsgn
    rw [hRa, hRb] at this
    have e : (n.factorial : ℝ) * (D : ℝ) ^ n * (lagL 0 n).eval l *
        ((n.factorial : ℝ) * (D : ℝ) ^ n * (lagL 0 n).eval u) =
        (n.factorial * (D : ℝ) ^ n) ^ 2 * ((lagL 0 n).eval l * (lagL 0 n).eval u) := by ring
    rw [e] at this
    exact neg_of_mul_neg_right this (sq_nonneg _)
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ Ioo l u, (lagL 0 n).eval x = 0 := by
    have hc : ContinuousOn (fun t => (lagL 0 n).eval t) (Icc l u) :=
      (lagL 0 n).continuous.continuousOn
    rcases mul_neg_iff.mp hsgnR with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hlu.le hc ⟨h2, h1⟩
      exact ⟨x, hx, hx0⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hlu.le hc ⟨h1, h2⟩
      exact ⟨x, hx, hx0⟩
  refine ⟨x, hx.1, hx.2, hx.2.le.trans huR, hx0, ?_, ?_⟩
  · -- the node
    have h10 : (0 : ℝ) < 10 ^ (r.sx + 1) := by positivity
    apply lag_abs_le_half_ulp
    · rw [div_le_iff₀ h10]
      have : ((10 * (r.X : ℝ) - 5) * D : ℝ) ≤ r.a * 10 ^ (r.sx + 1) := by exact_mod_cast hX1
      have hl : (r.a : ℝ) = l * D := by simp only [l]; field_simp
      rw [hl] at this
      have h1 : (10 * (r.X : ℝ) - 5) ≤ l * 10 ^ (r.sx + 1) :=
        le_of_mul_le_mul_right (by linarith) hDr
      linarith [mul_le_mul_of_nonneg_right hx.1.le h10.le]
    · rw [le_div_iff₀ h10]
      have : (((r.a : ℝ) + 1) * 10 ^ (r.sx + 1)) ≤ (10 * r.X + 5) * D := by exact_mod_cast hX2
      have hu : ((r.a : ℝ) + 1) = u * D := by simp only [u]; field_simp
      rw [hu] at this
      have h1 : u * 10 ^ (r.sx + 1) ≤ 10 * (r.X : ℝ) + 5 :=
        le_of_mul_le_mul_right (by linarith) hDr
      linarith [mul_le_mul_of_nonneg_right hx.2.le h10.le]
  · -- the weight
    set F : ℝ := ((n - 1).factorial : ℝ)
    set H : ℝ := ((lagH n r.a D : ℤ) : ℝ)
    set Kh : ℝ := ((lagK n R : ℕ) : ℝ)
    set Den : ℝ := F ^ 2 * (D : ℝ) ^ (2 * (n - 1))
    set E : ℝ := Kh * (D : ℝ) ^ (2 * n - 3)
    have hDen : 0 < Den := by positivity
    have hDE : (D : ℝ) ^ (2 * n - 3) * D = (D : ℝ) ^ (2 * (n - 1)) := by
      rw [← pow_succ]; congr 1; omega
    have hxl : |x - l| ≤ 1 / D := by
      rw [abs_of_pos (by linarith [hx.1]), show (1 : ℝ) / D = u - l by simp only [u, l]; ring]
      linarith [hx.2]
    have hLip := lagK_spec n R (by linarith [hx.1]) (hx.2.le.trans huR) hl0.le
      (hx.1.le.trans (hx.2.le.trans huR))
    have hGl : H = Den * lagG n l := by rw [show H = _ from hHa]
    have hdiff : Den * |lagG n x - lagG n l| ≤ E := by
      have hKh : 0 ≤ Kh := by positivity
      calc Den * |lagG n x - lagG n l| =
          (D : ℝ) ^ (2 * (n - 1)) * (F ^ 2 * |lagG n x - lagG n l|) := by ring
        _ ≤ (D : ℝ) ^ (2 * (n - 1)) * (Kh * (1 / D)) :=
          mul_le_mul_of_nonneg_left (hLip.trans (mul_le_mul_of_nonneg_left hxl hKh))
            (by positivity)
        _ = E := by simp only [E]; rw [← hDE]; field_simp
    have hlo : H - E ≤ Den * lagG n x := by
      rw [hGl]; have := neg_abs_le (lagG n x - lagG n l); nlinarith
    have hhi : Den * lagG n x ≤ H + E := by
      rw [hGl]; have := le_abs_self (lagG n x - lagG n l); nlinarith
    have h1 : 10 ^ (r.sw + 1) * Den ≤ (10 * (r.W : ℝ) + 5) * (H - E) := by
      have := hW1; simp only [lagDen, lagE] at this; simp only [H, E, Den, F, Kh]
      exact_mod_cast this
    have h2 : (10 * (r.W : ℝ) - 5) * (H + E) ≤ 10 ^ (r.sw + 1) * Den := by
      have := hW2; simp only [lagDen, lagE] at this; simp only [H, E, Den, F, Kh]
      exact_mod_cast this
    have hW5 : (0 : ℝ) ≤ 10 * (r.W : ℝ) - 5 := by
      have : (1 : ℝ) ≤ r.W := by exact_mod_cast hW0
      linarith
    have h10 : (0 : ℝ) < 10 ^ (r.sw + 1) := by positivity
    have hGpos : 0 < lagG n x := by
      by_contra hneg
      push Not at hneg
      have : (10 * (r.W : ℝ) + 5) * (H - E) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith)
      nlinarith
    have hA : 10 ^ (r.sw + 1) ≤ (10 * (r.W : ℝ) + 5) * lagG n x := by
      have := h1.trans (mul_le_mul_of_nonneg_left hlo (by positivity))
      refine le_of_mul_le_mul_right (this.trans_eq ?_) hDen
      ring
    have hB : (10 * (r.W : ℝ) - 5) * lagG n x ≤ 10 ^ (r.sw + 1) := by
      have := (mul_le_mul_of_nonneg_left hhi hW5).trans h2
      refine le_of_mul_le_mul_right (le_of_eq_of_le ?_ this) hDen
      ring
    refine ⟨?_, fun Wp hWp => ?_, fun Wp hWp => ?_⟩
    · apply lag_abs_le_half_ulp
      · rw [div_le_div_iff₀ h10 hGpos]; linarith
      · rw [div_le_div_iff₀ hGpos h10]; linarith
    · simp only [lagBelow, Bool.and_eq_true, decide_eq_true_eq] at hWp
      obtain ⟨hWp0, hWp1⟩ := hWp
      have h3 : 10 ^ (r.sw + 1) * Den < (10 * (Wp : ℝ) - 5) * (H - E) := by
        have := hWp1; simp only [lagDen, lagE] at this; simp only [H, E, Den, F, Kh]
        exact_mod_cast this
      have hWp5 : (0 : ℝ) ≤ 10 * (Wp : ℝ) - 5 := by
        have : (1 : ℝ) ≤ Wp := by exact_mod_cast hWp0
        linarith
      have hC : 10 ^ (r.sw + 1) < (10 * (Wp : ℝ) - 5) * lagG n x := by
        have := h3.trans_le (mul_le_mul_of_nonneg_left hlo hWp5)
        refine lt_of_mul_lt_mul_right (this.trans_eq ?_) hDen.le
        ring
      rw [show (Wp : ℝ) / 10 ^ r.sw - 5 / 10 ^ (r.sw + 1) = (10 * Wp - 5) / 10 ^ (r.sw + 1) by
        rw [pow_succ]; field_simp, div_lt_div_iff₀ hGpos h10]
      linarith
    · simp only [lagAbove, decide_eq_true_eq] at hWp
      have h3 : (10 * (Wp : ℝ) + 5) * (H + E) < 10 ^ (r.sw + 1) * Den := by
        have := hWp; simp only [lagDen, lagE] at this; simp only [H, E, Den, F, Kh]
        exact_mod_cast this
      have hC : (10 * (Wp : ℝ) + 5) * lagG n x < 10 ^ (r.sw + 1) := by
        have := (mul_le_mul_of_nonneg_left hhi (by positivity)).trans_lt h3
        refine lt_of_mul_lt_mul_right (lt_of_eq_of_lt ?_ this) hDen.le
        ring
      rw [show (Wp : ℝ) / 10 ^ r.sw + 5 / 10 ^ (r.sw + 1) = (10 * Wp + 5) / 10 ^ (r.sw + 1) by
        rw [pow_succ]; field_simp, div_lt_div_iff₀ h10 hGpos]
      linarith

/-! ### Nodes, weights and tables -/

/-- The nodes of the `n`-point Gauss–Laguerre rule (`α = 0`). -/
noncomputable def lagNodes (n : ℕ) : Finset ℝ := (lagMonic 0 n).roots.toFinset

/-- The weights of the `n`-point Gauss–Laguerre rule (`α = 0`). -/
noncomputable def lagWeight (n : ℕ) (x : ℝ) : ℝ :=
  christoffel (Ioi 0) (lagW 0) (lagMonic 0 n) x

theorem mem_lagNodes_iff (n : ℕ) (x : ℝ) : x ∈ lagNodes n ↔ (lagL 0 n).eval x = 0 := by
  have hc : ((-1 : ℝ) ^ n * n.factorial) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (by positivity)
  rw [lagNodes, Multiset.mem_toFinset, mem_roots (lagMonic_monic (by norm_num) n).ne_zero,
    IsRoot.def, lagMonic_eq_lagL (by norm_num), eval_mul, eval_C, mul_eq_zero, or_iff_right hc]

theorem card_lagNodes (n : ℕ) : #(lagNodes n) = n := by
  obtain ⟨hnodup, hcard, -⟩ := (isOrthMonic_lagMonic (by norm_num : (-1 : ℝ) < 0) n).roots_spec
    (isGaussWeight_lagW (by norm_num))
  rw [lagNodes, Multiset.toFinset_card_of_nodup hnodup, hcard]

theorem lagWeight_eq {n : ℕ} {x : ℝ} (hx : x ∈ lagNodes n) : lagWeight n x = 1 / lagG n x := by
  rw [lagWeight, christoffel_laguerre n hx, lagG]

/-- A Gauss–Laguerre table `(X, sx, W, sw)` of printed nodes `X/10^{sx}` and weights `W/10^{sw}`
is correctly rounded and complete. -/
def LagTableSpec (n : ℕ) (tab : List (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  (∀ p ∈ tab, ∃ x ∈ lagNodes n, |x - p.1 / 10 ^ p.2.1| ≤ 5 / 10 ^ (p.2.1 + 1) ∧
      |lagWeight n x - p.2.2.1 / 10 ^ p.2.2.2| ≤ 5 / 10 ^ (p.2.2.2 + 1)) ∧
  ∀ x ∈ lagNodes n, ∃ p ∈ tab, |x - p.1 / 10 ^ p.2.1| ≤ 5 / 10 ^ (p.2.1 + 1)

/-- The exact checks for a whole table. -/
def lagTableOK (n D R : ℕ) (rows : List LagRow) : Bool :=
  decide (2 ≤ n) && rows.all (lagRowOK n D R) &&
    decide (rows.Pairwise fun r s => r.a + 1 ≤ s.a) && decide (rows.length = n)

/-- The printed table of a list of rows. -/
def lagTab (rows : List LagRow) : List (ℕ × ℕ × ℕ × ℕ) := rows.map fun r => (r.X, r.sx, r.W, r.sw)

theorem lagTableOK_sound {n D R : ℕ} {rows : List LagRow} (h : lagTableOK n D R rows = true) :
    LagTableSpec n (lagTab rows) := by
  classical
  simp only [lagTableOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hn, hrows⟩, hpw⟩, hcount⟩ := h
  have hrow : ∀ i : Fin rows.length, ∃ x : ℝ, (rows[i].a : ℝ) / D < x ∧
      x < ((rows[i].a : ℝ) + 1) / D ∧ x ∈ lagNodes n ∧
      |x - rows[i].X / 10 ^ rows[i].sx| ≤ 5 / 10 ^ (rows[i].sx + 1) ∧
      |lagWeight n x - rows[i].W / 10 ^ rows[i].sw| ≤ 5 / 10 ^ (rows[i].sw + 1) := fun i => by
    obtain ⟨x, hl, hu, -, hx0, hX, hW, -, -⟩ :=
      lagRowOK_sound hn (hrows rows[i] (List.getElem_mem _))
    have hmem : x ∈ lagNodes n := (mem_lagNodes_iff n x).mpr hx0
    exact ⟨x, hl, hu, hmem, hX, by rwa [lagWeight_eq hmem]⟩
  choose xs hxl hxu hxmem hxX hxW using hrow
  have hmono : StrictMono xs := by
    intro i j hij
    have hb : rows[i].a + 1 ≤ rows[j].a := List.pairwise_iff_getElem.mp hpw i j i.2 j.2 hij
    have hD : (0 : ℝ) ≤ D := by positivity
    have : ((rows[i].a : ℝ) + 1) / D ≤ (rows[j].a : ℝ) / D :=
      div_le_div_of_nonneg_right (by exact_mod_cast hb) hD
    linarith [hxu i, hxl j]
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [lagTab, List.mem_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    exact ⟨xs ⟨i, hi⟩, hxmem _, hxX _, hxW _⟩
  · set S : Finset ℝ := univ.image xs
    have hsub : S ⊆ lagNodes n := fun t ht => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      exact hxmem i
    have hcard : #S = n := by
      rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin,
        hcount]
    have heq : S = lagNodes n := eq_of_subset_of_card_le hsub (by rw [card_lagNodes, hcard])
    intro t ht
    rw [← heq] at ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    refine ⟨(rows[i].X, rows[i].sx, rows[i].W, rows[i].sw), ?_, hxX i⟩
    simp only [lagTab, List.mem_map]
    exact ⟨rows[i], List.getElem_mem _, rfl⟩

/-- An erratum row with a printed weight that is too large. -/
theorem lagErratum_below {n D R : ℕ} (hn : 2 ≤ n) {r : LagRow} {Wp : ℕ}
    (h : lagRowOK n D R r = true) (hb : lagBelow n D R r Wp = true) :
    ∃ x ∈ lagNodes n, |x - r.X / 10 ^ r.sx| ≤ 5 / 10 ^ (r.sx + 1) ∧
      |lagWeight n x - r.W / 10 ^ r.sw| ≤ 5 / 10 ^ (r.sw + 1) ∧
      lagWeight n x < Wp / 10 ^ r.sw - 5 / 10 ^ (r.sw + 1) := by
  obtain ⟨x, -, -, -, hx0, hX, hW, hB, -⟩ := lagRowOK_sound hn h
  have hmem : x ∈ lagNodes n := (mem_lagNodes_iff n x).mpr hx0
  rw [← lagWeight_eq hmem] at hW hB
  exact ⟨x, hmem, hX, hW, hB Wp hb⟩

/-- An erratum row with a printed weight that is too small. -/
theorem lagErratum_above {n D R : ℕ} (hn : 2 ≤ n) {r : LagRow} {Wp : ℕ}
    (h : lagRowOK n D R r = true) (ha : lagAbove n D R r Wp = true) :
    ∃ x ∈ lagNodes n, |x - r.X / 10 ^ r.sx| ≤ 5 / 10 ^ (r.sx + 1) ∧
      |lagWeight n x - r.W / 10 ^ r.sw| ≤ 5 / 10 ^ (r.sw + 1) ∧
      (Wp : ℝ) / 10 ^ r.sw + 5 / 10 ^ (r.sw + 1) < lagWeight n x := by
  obtain ⟨x, -, -, -, hx0, hX, hW, -, hA⟩ := lagRowOK_sound hn h
  have hmem : x ∈ lagNodes n := (mem_lagNodes_iff n x).mpr hx0
  rw [← lagWeight_eq hmem] at hW hA
  exact ⟨x, hmem, hX, hW, hA Wp ha⟩

/-! ### The certificates (`D = 10^100`; brackets `(a/D, (a+1)/D)`) -/

/-- A bracket numerator `hi · 10^50 + lo`, split for line length. -/
def lagN (hi lo : ℕ) : ℕ := hi * 10 ^ 50 + lo

/-- The brackets and printed values of Table 3.5.6. -/
def lagRows_3_5_6 : List LagRow := [
  ⟨lagN
    26356031971814091020306194336083333468900756990551
    69278626150283831131438046884853888014286367681424,
    263560319718141, 15, 521755610582809, 15⟩,
  ⟨lagN
    141340305910651679221840798018755774953909600438088
    2805544082979007423775923542946320718755491625047,
    141340305910652, 14, 398666811083176, 15⟩,
  ⟨lagN
    359642577104072208122318658878297166567115094071057
    45382530744194445950353402442837707236763545344635,
    359642577104072, 14, 759424496817076, 16⟩,
  ⟨lagN
    708581000585883755692212418110808600038593567078494
    8825789216557377366293170118613163813153310932022,
    708581000585884, 14, 361175867992205, 17⟩,
  ⟨lagN
    1264080084427578265943321930656055124971480981421808
    73707509805985338128139457010748920217041284416869,
    126408008442758, 13, 233699723857762, 19⟩]

set_option maxRecDepth 100000 in
theorem lagTableOK_3_5_6 : lagTableOK 5 (10 ^ 100) 13 lagRows_3_5_6 = true := by
  decide +kernel

/-- **Table 3.5.6** (5-point Gauss–Laguerre formula, `α = 0`): every node `x_k` and weight
`w_k` is correctly rounded as printed, and the table is complete. -/
theorem dlmf_table_3_5_6 : LagTableSpec 5 [
    (263560319718141, 15, 521755610582809, 15),
    (141340305910652, 14, 398666811083176, 15),
    (359642577104072, 14, 759424496817076, 16),
    (708581000585884, 14, 361175867992205, 17),
    (126408008442758, 13, 233699723857762, 19)] :=
  lagTableOK_sound lagTableOK_3_5_6

/-- The brackets and printed values of Table 3.5.7. -/
def lagRows_3_5_7 : List LagRow := [
  ⟨lagN
    13779347054049243083077250565271118810799168074578
    32941633665113734459644764620865625437524173411652,
    137793470540492431, 18, 308441115765020142, 18⟩,
  ⟨lagN
    72945454950317049816037312167607878107607273331224
    92460078110488062678230730515720465249917862963193,
    729454549503170498, 18, 401119929155273552, 18⟩,
  ⟨lagN
    180834290174031604823292007575060883328306028237144
    81516932097683732967664043428239153383606124012239,
    180834290174031605, 17, 218068287611809422, 18⟩,
  ⟨lagN
    340143369785489951448253222140839067927315661420347
    32294267661021823269228666946410395095870847780590,
    340143369785489951, 17, 620874560986777474, 19⟩,
  ⟨lagN
    555249614006380363241755848686876285797406428731781
    38284904788336252636084290435460571874259935064862,
    555249614006380363, 17, 950151697518110055, 20⟩,
  ⟨lagN
    833015274676449670023876719727452218270943897203098
    93447446294283573954320532476951665824491858289576,
    833015274676449670, 17, 753008388587538775, 21⟩,
  ⟨lagN
    1184378583790006556491853891914161398580281690946533
    58733395914952762201506971082327172125276032417051,
    118437858379000656, 16, 282592334959956557, 22⟩,
  ⟨lagN
    1627925783137810209953265393583362233525599560303305
    90777883921650028273509325979402258415075965191657,
    162792578313781021, 16, 424931398496268637, 24⟩,
  ⟨lagN
    2199658581198076195127709019559449397680673234000188
    77882415035116931063757989988230676865333469803611,
    219965858119807620, 16, 183956482397963078, 26⟩,
  ⟨lagN
    2992069701227389155990879334079919517971067057751796
    1661042511353098496052684526392015728643731065563,
    299206970122738916, 16, 991182721960900856, 30⟩]

set_option maxRecDepth 100000 in
theorem lagTableOK_3_5_7 : lagTableOK 10 (10 ^ 100) 30 lagRows_3_5_7 = true := by
  decide +kernel

/-- **Table 3.5.7** (10-point Gauss–Laguerre formula, `α = 0`): every node `x_k` and weight
`w_k` is correctly rounded as printed (with the corrected
last digits of the errata below), and the table is complete. -/
theorem dlmf_table_3_5_7 : LagTableSpec 10 [
    (137793470540492431, 18, 308441115765020142, 18),
    (729454549503170498, 18, 401119929155273552, 18),
    (180834290174031605, 17, 218068287611809422, 18),
    (340143369785489951, 17, 620874560986777474, 19),
    (555249614006380363, 17, 950151697518110055, 20),
    (833015274676449670, 17, 753008388587538775, 21),
    (118437858379000656, 16, 282592334959956557, 22),
    (162792578313781021, 16, 424931398496268637, 24),
    (219965858119807620, 16, 183956482397963078, 26),
    (299206970122738916, 16, 991182721960900856, 30)] :=
  lagTableOK_sound lagTableOK_3_5_7

set_option maxRecDepth 100000 in
/-- **Erratum to Table 3.5.7**: at the node `137793470540492431 × 10^-18` the printed weight
`308441115765020141 × 10^-18` is not correctly rounded; the
correct last digits give `308441115765020142 × 10^-18`. -/
theorem dlmf_table_3_5_7_erratum_0 :
    ∃ x ∈ lagNodes 10, |x - (137793470540492431 : ℕ) / 10 ^ 18| ≤ 5 / 10 ^ (18 + 1) ∧
      |lagWeight 10 x - (308441115765020142 : ℕ) / 10 ^ 18| ≤ 5 / 10 ^ (18 + 1) ∧
      ((308441115765020141 : ℕ) : ℝ) / 10 ^ 18 + 5 / 10 ^ (18 + 1) < lagWeight 10 x :=
  lagErratum_above (D := 10 ^ 100) (R := 30) (r := ⟨lagN
    13779347054049243083077250565271118810799168074578
    32941633665113734459644764620865625437524173411652,
    137793470540492431, 18, 308441115765020142, 18⟩) (by norm_num)
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **Erratum to Table 3.5.7**: at the node `340143369785489951 × 10^-17` the printed weight
`620874560986777475 × 10^-19` is not correctly rounded; the
correct last digits give `620874560986777474 × 10^-19`. -/
theorem dlmf_table_3_5_7_erratum_3 :
    ∃ x ∈ lagNodes 10, |x - (340143369785489951 : ℕ) / 10 ^ 17| ≤ 5 / 10 ^ (17 + 1) ∧
      |lagWeight 10 x - (620874560986777474 : ℕ) / 10 ^ 19| ≤ 5 / 10 ^ (19 + 1) ∧
      lagWeight 10 x < (620874560986777475 : ℕ) / 10 ^ 19 - 5 / 10 ^ (19 + 1) :=
  lagErratum_below (D := 10 ^ 100) (R := 30) (r := ⟨lagN
    340143369785489951448253222140839067927315661420347
    32294267661021823269228666946410395095870847780590,
    340143369785489951, 17, 620874560986777474, 19⟩) (by norm_num)
    (by decide +kernel) (by decide +kernel)

/-- The brackets and printed values of Table 3.5.8. -/
def lagRows_3_5_8 : List LagRow := [
  ⟨lagN
    9330781201728180476290303836720770027819707633045
    34930093601370583470640157761217616683036108990585,
    933078120172818047629, 22, 218234885940086889856, 21⟩,
  ⟨lagN
    49269174030188390896010179141240173099215246375371
    94160198850819350613466443301146193381369816786116,
    492691740301883908960, 21, 342210177922883329639, 21⟩,
  ⟨lagN
    121559541207094946372992716487900297498726815893770
    57427014003173216015106603771651065605856143208373,
    121559541207094946373, 20, 263027577941680097415, 21⟩,
  ⟨lagN
    226994952620374320247421741374817218856800484164787
    17117778472877455733945904832989178549502018189830,
    226994952620374320247, 20, 126425818105930535843, 21⟩,
  ⟨lagN
    366762272175143727724905959436028772903574309094107
    17845566428732064149379102861748582946304744040432,
    366762272175143727725, 20, 402068649210009148416, 22⟩,
  ⟨lagN
    542533662741355316534358132596053452084926239229277
    83354709435107483423740280199191227091479154617337,
    542533662741355316534, 20, 856387780361183836392, 23⟩,
  ⟨lagN
    756591622661306786049739555811855454823931080089993
    14491628694391139408365724029944489180550403629640,
    756591622661306786050, 20, 121243614721425207622, 23⟩,
  ⟨lagN
    1012022856801911273479273945681716974341091196705874
    49174574546010724878250476718762160886507218872433,
    101202285680191127348, 19, 111674392344251941993, 24⟩,
  ⟨lagN
    1313028248217572356409912041759653131018727002254845
    36960479745468637462292903629722800389962763870010,
    131302824821757235641, 19, 645992676202290092465, 26⟩,
  ⟨lagN
    1665440770832995782252024084298359965395157534103060
    87857644485254877497975394656935369160480163629455,
    166544077083299578225, 19, 222631690709627263033, 27⟩,
  ⟨lagN
    2077647889944876677291571756759343624770514125632719
    53600022213229459597679327468158843969535099619467,
    207764788994487667729, 19, 422743038497936500735, 29⟩,
  ⟨lagN
    2562389422672878014458682859766984139712394032241147
    69503176723153398242389313523511279174120812805027,
    256238942267287801446, 19, 392189726704108929038, 31⟩,
  ⟨lagN
    3140751916975393851524321962022140419634562280988966
    99259534388706654400739109622553666624335431206841,
    314075191697539385152, 19, 145651526407312640633, 33⟩,
  ⟨lagN
    3853068330648600941625151675951619379893211974459478
    42840503642828889752306128677896846900426725966063,
    385306833064860094163, 19, 148302705111330133546, 36⟩,
  ⟨lagN
    4802608557268579434657343085075566225939347971133553
    41477074768876065353723128944570679456533394568385,
    480260855726857943466, 19, 160059490621113323105, 40⟩]

set_option maxRecDepth 100000 in
theorem lagTableOK_3_5_8 : lagTableOK 15 (10 ^ 100) 49 lagRows_3_5_8 = true := by
  decide +kernel

/-- **Table 3.5.8** (15-point Gauss–Laguerre formula, `α = 0`): every node `x_k` and weight
`w_k` is correctly rounded as printed, and the table is complete. -/
theorem dlmf_table_3_5_8 : LagTableSpec 15 [
    (933078120172818047629, 22, 218234885940086889856, 21),
    (492691740301883908960, 21, 342210177922883329639, 21),
    (121559541207094946373, 20, 263027577941680097415, 21),
    (226994952620374320247, 20, 126425818105930535843, 21),
    (366762272175143727725, 20, 402068649210009148416, 22),
    (542533662741355316534, 20, 856387780361183836392, 23),
    (756591622661306786050, 20, 121243614721425207622, 23),
    (101202285680191127348, 19, 111674392344251941993, 24),
    (131302824821757235641, 19, 645992676202290092465, 26),
    (166544077083299578225, 19, 222631690709627263033, 27),
    (207764788994487667729, 19, 422743038497936500735, 29),
    (256238942267287801446, 19, 392189726704108929038, 31),
    (314075191697539385152, 19, 145651526407312640633, 33),
    (385306833064860094163, 19, 148302705111330133546, 36),
    (480260855726857943466, 19, 160059490621113323105, 40)] :=
  lagTableOK_sound lagTableOK_3_5_8

/-- The brackets and printed values of Table 3.5.9. -/
def lagRows_3_5_9 : List LagRow := [
  ⟨lagN
    7053988969198875336668900458421509586936062983531
    653769324757444175034174288193913648007275894088,
    705398896919887533667, 22, 168746801851113862149, 21⟩,
  ⟨lagN
    37212681800161144379424138876114663667402821015618
    41234158265441997833601228510157717239559517624843,
    372126818001611443794, 21, 291254362006068281717, 21⟩,
  ⟨lagN
    91658210248327356466771627707418318720560419804296
    62805750011627793207203461116130899466401870387934,
    916582102483273564668, 21, 266686102867001288550, 21⟩,
  ⟨lagN
    170730653102834388068768966741305070618793994821525
    46020965867734539573548684925182255205674385048005,
    170730653102834388069, 20, 166002453269506840031, 21⟩,
  ⟨lagN
    274919925530943212964503046049481338427561691740576
    44084722935372086363670600249671958283632328614629,
    274919925530943212965, 20, 748260646687923705401, 22⟩,
  ⟨lagN
    404892531385088692237495336913333219650665244703755
    61528482320928247806174355596760328339040254388728,
    404892531385088692237, 20, 249644173092832210728, 22⟩,
  ⟨lagN
    561517497086161651410453988565189234791775687664442
    71645073388930160187541513153998991524734960399127,
    561517497086161651410, 20, 620255084457223684745, 23⟩,
  ⟨lagN
    745901745367106330976886021837181759538447712017393
    63163280592734048106688692218671265677860731684757,
    745901745367106330977, 20, 114496238647690824204, 23⟩,
  ⟨lagN
    959439286958109677247367273428279837815063789421437
    95744527920039623103029150005819706172790476225419,
    959439286958109677247, 20, 155741773027811974780, 24⟩,
  ⟨lagN
    1203880254696431630962340929886551586822755387367529
    59590375363763724616454457472053283585342977024344,
    120388025469643163096, 19, 154014408652249156894, 25⟩,
  ⟨lagN
    1481429344263073997851267971004797567425075710564434
    74893293907739073382486409460157767759534819112018,
    148142934426307399785, 19, 108648636651798235148, 26⟩,
  ⟨lagN
    1794889552051937601736579099261250964867800442919938
    94907617834708948352334043321266358183972991716943,
    179488955205193760174, 19, 533012090955671475093, 28⟩,
  ⟨lagN
    2147878824028501097573517036959466921620975569710955
    14487816840935616369272633142260366473570468581557,
    214787882402850109757, 19, 175798117905058200358, 29⟩,
  ⟨lagN
    2545170279318690550351867748464154183816351122364590
    13305660294135421259158576523617832303252353326092,
    254517027931869055035, 19, 372550240251232087263, 31⟩,
  ⟨lagN
    2993255463170061200671365613516582325166056035059785
    53437387320959500316831512762129158515154849279796,
    299325546317006120067, 19, 476752925157819052449, 33⟩,
  ⟨lagN
    3501343424047900000628493590668813958176592873259733
    5637193035820448145055422930724627249287984969247,
    350134342404790000063, 19, 337284424336243841237, 35⟩,
  ⟨lagN
    4083305705672857106202956770780755267170765974919900
    888611901106921840974290499961483799190835976729,
    408330570567285710620, 19, 115501433950039883096, 37⟩,
  ⟨lagN
    4761999404734650213994162715285112111314397034257492
    87447928959612295630017946324187260656499872255347,
    476199940473465021399, 19, 153952214058234355346, 40⟩,
  ⟨lagN
    5581079575006389889075077344449723562838531124833353
    93933208546729183694832693805666354173227948748530,
    558107957500638988908, 19, 528644272556915782880, 44⟩,
  ⟨lagN
    6652441652561575381864031879146066597963491300569708
    14590175366922926036090153693388471743263098741859,
    665244165256157538186, 19, 165645661249902329591, 48⟩]

set_option maxRecDepth 100000 in
theorem lagTableOK_3_5_9 : lagTableOK 20 (10 ^ 100) 67 lagRows_3_5_9 = true := by
  decide +kernel

/-- **Table 3.5.9** (20-point Gauss–Laguerre formula, `α = 0`): every node `x_k` and weight
`w_k` is correctly rounded as printed, and the table is complete. -/
theorem dlmf_table_3_5_9 : LagTableSpec 20 [
    (705398896919887533667, 22, 168746801851113862149, 21),
    (372126818001611443794, 21, 291254362006068281717, 21),
    (916582102483273564668, 21, 266686102867001288550, 21),
    (170730653102834388069, 20, 166002453269506840031, 21),
    (274919925530943212965, 20, 748260646687923705401, 22),
    (404892531385088692237, 20, 249644173092832210728, 22),
    (561517497086161651410, 20, 620255084457223684745, 23),
    (745901745367106330977, 20, 114496238647690824204, 23),
    (959439286958109677247, 20, 155741773027811974780, 24),
    (120388025469643163096, 19, 154014408652249156894, 25),
    (148142934426307399785, 19, 108648636651798235148, 26),
    (179488955205193760174, 19, 533012090955671475093, 28),
    (214787882402850109757, 19, 175798117905058200358, 29),
    (254517027931869055035, 19, 372550240251232087263, 31),
    (299325546317006120067, 19, 476752925157819052449, 33),
    (350134342404790000063, 19, 337284424336243841237, 35),
    (408330570567285710620, 19, 115501433950039883096, 37),
    (476199940473465021399, 19, 153952214058234355346, 40),
    (558107957500638988908, 19, 528644272556915782880, 44),
    (665244165256157538186, 19, 165645661249902329591, 48)] :=
  lagTableOK_sound lagTableOK_3_5_9

end Azurite.DLMF
