/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5GaussLegendre

/-!
# DLMF §3.5(v): Tables 3.5.1–3.5.5 (Gauss–Legendre nodes and weights)

Every number in Tables 3.5.1–3.5.5 is certified by exact integer arithmetic, checked by the kernel
(`decide +kernel`, kernel `Nat`/`Int` arithmetic).

* `glRH`: Bonnet's recurrence at `x = m/D` scaled to integers, `R_k = k! Dᵏ P_k(x)` and
  `H_k = (k!)² D^{2k} ∑_{j≤k} (2j + 1) P_j(x)²` (`glRH_spec`).
* `glAC`: integer majorants on `[−1, 1]` of `k! |P_k|`, of the Lipschitz constant of `k! P_k`, and
  of that of `(k!)² ∑_{j≤k} (2j + 1) P_j²` (`glAC_spec`, by induction from Bonnet's recurrence).
* `glRowOK`/`glRowOK_sound`: a sign change of `P_n` across a bracket `(a/D, (a+1)/D)`, the bracket
  inside the rounding interval of the printed node, and the weight `2/∑_{j<n} (2j + 1) P_j²`
  (`christoffel_legendre`) inside that of the printed weight; `glZeroOK` for the node `0` of an odd
  rule; `glBelow` for a printed weight that is too large.
* `glTableOK`/`glTableOK_sound` → `GLTableSpec`: every row is a node and weight, correctly rounded,
  and every node `±x` (`glNodes`, `card_glNodes`) is a row (`n` disjoint certified zeros exhaust the
  zeros of `p_n`); the weights are even (`glWeight_neg`).
* Tables 3.5.1–3.5.5: `dlmf_table_3_5_1` … `dlmf_table_3_5_5` (`D = 10^90`).
* Errata (last digits): `dlmf_table_3_5_4_erratum_5`, `dlmf_table_3_5_4_erratum_15`,
  `dlmf_table_3_5_5_erratum_32`.
-/

open Polynomial Finset Set

namespace Azurite.DLMF

/-! ### Exact integer recurrences -/

/-- `(R_k, R_{k+1}, H_k)` at `x = m/D`: `R_k = k! Dᵏ P_k(x)` (Bonnet's recurrence scaled to
integers) and `H_k = (k!)² D^{2k} ∑_{j≤k} (2j + 1) P_j(x)²`. -/
def glRH (m D : ℤ) : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, m, 1)
  | k + 1 =>
    match glRH m D k with
    | (r0, r1, h) =>
      (r1, (2 * k + 3) * m * r1 - (k + 1) ^ 2 * D ^ 2 * r0,
        (k + 1) ^ 2 * D ^ 2 * h + (2 * k + 3) * r1 ^ 2)

/-- `∑_{j≤k} (2j + 1) P_j(x)²`. -/
noncomputable def glG (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), (2 * j + 1) * (legendrePoly j).eval x ^ 2

theorem glRH_spec (m D : ℤ) (x : ℝ) (hm : (m : ℝ) = x * D) (k : ℕ) :
    ((glRH m D k).1 : ℝ) = k.factorial * (D : ℝ) ^ k * (legendrePoly k).eval x ∧
    ((glRH m D k).2.1 : ℝ) = (k + 1).factorial * (D : ℝ) ^ (k + 1) * (legendrePoly (k + 1)).eval x ∧
    ((glRH m D k).2.2 : ℝ) = (k.factorial : ℝ) ^ 2 * (D : ℝ) ^ (2 * k) * glG k x := by
  induction k with
  | zero =>
    simp [glRH, glG, eval_legendreP_zero, eval_legendreP_one, hm]
    ring
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    simp only [glRH]
    refine ⟨h1, ?_, ?_⟩
    · push_cast
      rw [h1, h0, hm, show k + 1 + 1 = k + 2 by ring, Nat.factorial_succ (k + 1),
        Nat.factorial_succ k]
      have hb := eval_legendreP_succ_succ k x
      push_cast
      linear_combination (-(k.factorial : ℝ) * (k + 1) * (D : ℝ) ^ (k + 2)) * hb
    · push_cast
      rw [h2, h1, glG, glG, sum_range_succ (n := k + 1), Nat.factorial_succ k]
      push_cast
      ring

/-- Majorants `(Â_k, Â_{k+1}, Ĉ_k, Ĉ_{k+1}, K̂_k)` on `[−1, 1]`: `k! |P_k| ≤ Â_k`,
`k! |P_k(x) − P_k(y)| ≤ Ĉ_k |x − y|`, `(k!)² |G_k(x) − G_k(y)| ≤ K̂_k |x − y|`. -/
def glAC : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 0, 1, 0)
  | k + 1 =>
    match glAC k with
    | (a0, a1, c0, c1, kk) =>
      (a1, (2 * k + 3) * a1 + (k + 1) ^ 2 * a0, c1, (2 * k + 3) * (c1 + a1) + (k + 1) ^ 2 * c0,
        (k + 1) ^ 2 * kk + (2 * k + 3) * 2 * a1 * c1)

/-- Bonnet's recurrence with factorials: `(k+2)! P_{k+2} = (2k+3) (k+1)! x P_{k+1} −
(k+1)² k! P_k`. -/
theorem legendreP_fact (k : ℕ) (x : ℝ) :
    ((k + 2).factorial : ℝ) * (legendrePoly (k + 2)).eval x =
      (2 * k + 3) * ((k + 1).factorial * (x * (legendrePoly (k + 1)).eval x)) -
        (k + 1) ^ 2 * (k.factorial * (legendrePoly k).eval x) := by
  have hb := eval_legendreP_succ_succ k x
  rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]
  push_cast
  linear_combination ((k.factorial : ℝ) * (k + 1)) * hb

theorem abs_mul_sub_mul_le {α β : ℝ} (u v : ℝ) (ha : 0 ≤ α) (hb : 0 ≤ β) :
    |α * u - β * v| ≤ α * |u| + β * |v| :=
  calc |α * u - β * v| ≤ |α * u| + |β * v| := abs_sub _ _
    _ = α * |u| + β * |v| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

theorem glAC_spec (k : ℕ) : ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 →
    (k.factorial : ℝ) * |(legendrePoly k).eval x| ≤ (glAC k).1 ∧
    ((k + 1).factorial : ℝ) * |(legendrePoly (k + 1)).eval x| ≤ (glAC k).2.1 ∧
    (k.factorial : ℝ) * |(legendrePoly k).eval x - (legendrePoly k).eval y| ≤
      (glAC k).2.2.1 * |x - y| ∧
    ((k + 1).factorial : ℝ) * |(legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y| ≤
      (glAC k).2.2.2.1 * |x - y| ∧
    (k.factorial : ℝ) ^ 2 * |glG k x - glG k y| ≤ (glAC k).2.2.2.2 * |x - y| := by
  induction k with
  | zero =>
    intro x y hx hy
    simp only [glAC, glG, eval_legendreP_zero, eval_legendreP_one, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, one_mul, zero_add, sum_range_one]
    norm_num
    exact hx
  | succ k ih =>
    intro x y hx hy
    obtain ⟨-, hA1x, -, hC1, hK⟩ := ih x y hx hy
    obtain ⟨hA0x, -, hC0, -, -⟩ := ih x y hx hy
    obtain ⟨-, hA1y, -, -, -⟩ := ih y y hy hy
    simp only [glAC]
    set F1 := ((k + 1).factorial : ℝ)
    set F0 := (k.factorial : ℝ)
    have hF0 : 0 ≤ F0 := by positivity
    have hF1 : 0 ≤ F1 := by positivity
    set a0 := ((glAC k).1 : ℝ)
    set a1 := ((glAC k).2.1 : ℝ)
    set c0 := ((glAC k).2.2.1 : ℝ)
    set c1 := ((glAC k).2.2.2.1 : ℝ)
    have hxy : 0 ≤ |x - y| := abs_nonneg _
    have hk3 : (0 : ℝ) ≤ 2 * k + 3 := by positivity
    have hk1 : (0 : ℝ) ≤ (k + 1) ^ 2 := by positivity
    have hx0 : 0 ≤ |x| := abs_nonneg x
    refine ⟨hA1x, ?_, hC1, ?_, ?_⟩
    · -- `(k+2)! |P_{k+2}(x)| ≤ Â_{k+2}`
      rw [show k + 1 + 1 = k + 2 by ring]
      have hF2 : (0 : ℝ) ≤ (k + 2).factorial := by positivity
      have e : ((k + 2).factorial : ℝ) * |(legendrePoly (k + 2)).eval x| =
          |(2 * k + 3) * (F1 * (x * (legendrePoly (k + 1)).eval x)) -
            (k + 1) ^ 2 * (F0 * (legendrePoly k).eval x)| := by
        rw [← legendreP_fact, abs_mul, abs_of_nonneg hF2]
      have h1 : |F1 * (x * (legendrePoly (k + 1)).eval x)| ≤ a1 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hF1]
        have hp := abs_nonneg ((legendrePoly (k + 1)).eval x)
        calc F1 * (|x| * |(legendrePoly (k + 1)).eval x|) =
            |x| * (F1 * |(legendrePoly (k + 1)).eval x|) := by ring
          _ ≤ 1 * (F1 * |(legendrePoly (k + 1)).eval x|) :=
            mul_le_mul_of_nonneg_right hx (by positivity)
          _ ≤ a1 := by rw [one_mul]; exact hA1x
      have h0 : |F0 * (legendrePoly k).eval x| ≤ a0 := by
        rw [abs_mul, abs_of_nonneg hF0]; exact hA0x
      rw [e]
      push_cast
      calc _ ≤ (2 * k + 3) * |F1 * (x * (legendrePoly (k + 1)).eval x)| +
            (k + 1) ^ 2 * |F0 * (legendrePoly k).eval x| := abs_mul_sub_mul_le _ _ hk3 hk1
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 hk3) (mul_le_mul_of_nonneg_left h0 hk1)
    · -- `(k+2)! |P_{k+2}(x) − P_{k+2}(y)| ≤ Ĉ_{k+2} |x − y|`
      rw [show k + 1 + 1 = k + 2 by ring]
      have hF2 : (0 : ℝ) ≤ (k + 2).factorial := by positivity
      have e : ((k + 2).factorial : ℝ) *
          |(legendrePoly (k + 2)).eval x - (legendrePoly (k + 2)).eval y| =
          |(2 * k + 3) * (F1 * (x * ((legendrePoly (k + 1)).eval x -
              (legendrePoly (k + 1)).eval y)) +
              F1 * ((x - y) * (legendrePoly (k + 1)).eval y)) -
            (k + 1) ^ 2 * (F0 * ((legendrePoly k).eval x - (legendrePoly k).eval y))| := by
        rw [← abs_of_nonneg hF2, ← abs_mul, mul_sub, legendreP_fact, legendreP_fact]
        congr 1; ring
      have h1 : |F1 * (x * ((legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y)) +
          F1 * ((x - y) * (legendrePoly (k + 1)).eval y)| ≤ (c1 + a1) * |x - y| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hF1]
        have hd := abs_nonneg ((legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y)
        have hp := abs_nonneg ((legendrePoly (k + 1)).eval y)
        calc F1 * (|x| * |(legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y|) +
              F1 * (|x - y| * |(legendrePoly (k + 1)).eval y|) =
            |x| * (F1 * |(legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y|) +
              |x - y| * (F1 * |(legendrePoly (k + 1)).eval y|) := by ring
          _ ≤ 1 * (c1 * |x - y|) + |x - y| * a1 :=
            add_le_add (mul_le_mul hx hC1 (by positivity) zero_le_one)
              (mul_le_mul_of_nonneg_left hA1y hxy)
          _ = _ := by ring
      have h0 : |F0 * ((legendrePoly k).eval x - (legendrePoly k).eval y)| ≤ c0 * |x - y| := by
        rw [abs_mul, abs_of_nonneg hF0]; exact hC0
      rw [e]
      push_cast
      calc _ ≤ (2 * k + 3) * |F1 * (x * ((legendrePoly (k + 1)).eval x -
              (legendrePoly (k + 1)).eval y)) + F1 * ((x - y) * (legendrePoly (k + 1)).eval y)| +
            (k + 1) ^ 2 * |F0 * ((legendrePoly k).eval x - (legendrePoly k).eval y)| :=
          abs_mul_sub_mul_le _ _ hk3 hk1
        _ ≤ (2 * k + 3) * ((c1 + a1) * |x - y|) + (k + 1) ^ 2 * (c0 * |x - y|) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hk3) (mul_le_mul_of_nonneg_left h0 hk1)
        _ = _ := by ring
    · -- `((k+1)!)² |G_{k+1}(x) − G_{k+1}(y)| ≤ K̂_{k+1} |x − y|`
      have hG : glG (k + 1) x - glG (k + 1) y = (glG k x - glG k y) +
          (2 * (k + 1 : ℕ) + 1) * (((legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y) *
            ((legendrePoly (k + 1)).eval x + (legendrePoly (k + 1)).eval y)) := by
        simp only [glG]
        rw [Finset.sum_range_succ _ (k + 1), Finset.sum_range_succ _ (k + 1)]
        push_cast; ring
      have hF : F1 = (k + 1) * F0 := by simp only [F1, F0, Nat.factorial_succ]; push_cast; ring
      have hP : F1 * |(legendrePoly (k + 1)).eval x + (legendrePoly (k + 1)).eval y| ≤ 2 * a1 := by
        have := abs_add_le ((legendrePoly (k + 1)).eval x) ((legendrePoly (k + 1)).eval y)
        nlinarith
      have hsq : F1 ^ 2 * |((legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y) *
          ((legendrePoly (k + 1)).eval x + (legendrePoly (k + 1)).eval y)| ≤
            2 * a1 * c1 * |x - y| := by
        rw [abs_mul]
        have h1 := hC1
        have hpos1 := abs_nonneg ((legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y)
        have hpos2 := abs_nonneg ((legendrePoly (k + 1)).eval x + (legendrePoly (k + 1)).eval y)
        calc F1 ^ 2 * (|(legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y| *
              |(legendrePoly (k + 1)).eval x + (legendrePoly (k + 1)).eval y|) =
            (F1 * |(legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y|) *
              (F1 * |(legendrePoly (k + 1)).eval x + (legendrePoly (k + 1)).eval y|) := by ring
          _ ≤ (c1 * |x - y|) * (2 * a1) :=
            mul_le_mul h1 hP (by positivity) (by positivity)
          _ = _ := by ring
      rw [hG]
      push_cast
      calc F1 ^ 2 * |glG k x - glG k y + (2 * (k + 1 : ℝ) + 1) *
            (((legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y) *
              ((legendrePoly (k + 1)).eval x + (legendrePoly (k + 1)).eval y))|
          ≤ F1 ^ 2 * (|glG k x - glG k y| + (2 * (k + 1 : ℝ) + 1) *
            |((legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y) *
              ((legendrePoly (k + 1)).eval x + (legendrePoly (k + 1)).eval y)|) := by
            refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (le_of_eq ?_)) (by positivity)
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k + 1 : ℝ) + 1)]
        _ = (k + 1) ^ 2 * (F0 ^ 2 * |glG k x - glG k y|) + (2 * (k + 1 : ℝ) + 1) *
            (F1 ^ 2 * |((legendrePoly (k + 1)).eval x - (legendrePoly (k + 1)).eval y) *
              ((legendrePoly (k + 1)).eval x + (legendrePoly (k + 1)).eval y)|) := by rw [hF]; ring
        _ ≤ (k + 1) ^ 2 * ((glAC k).2.2.2.2 * |x - y|) + (2 * (k + 1 : ℝ) + 1) *
            (2 * a1 * c1 * |x - y|) :=
          add_le_add (mul_le_mul_of_nonneg_left hK hk1)
            (mul_le_mul_of_nonneg_left hsq (by positivity))
        _ = _ := by ring

/-! ### Certified rows -/

/-- A positive row of a table: the bracket `(a/D, b/D)` of a node, the printed node `X/10^{dx}` and
the printed weight `W/10^{dw}`. -/
structure GLRow where
  a : ℕ
  b : ℕ
  X : ℕ
  W : ℕ

/-- The exact integer checks for one row (`n ≥ 2`): a sign change of `P_n` across the bracket,
the bracket inside the rounding interval of the printed node, and the weight
`2/∑_{j<n} (2j+1) P_j²` inside the rounding interval of the printed weight (the sum transferred
from `a/D` to the node by the Lipschitz majorant `K̂`). -/
def glRowOK (n D dx dw : ℕ) (r : GLRow) : Bool :=
  let ra := glRH r.a D (n - 1)
  let rb := glRH r.b D (n - 1)
  let Den : ℤ := ((n - 1).factorial : ℤ) ^ 2 * (D : ℤ) ^ (2 * (n - 1))
  let E : ℤ := ((glAC (n - 1)).2.2.2.2 : ℤ) * ((r.b : ℤ) - r.a) * (D : ℤ) ^ (2 * n - 3)
  decide (0 < r.W) && decide (0 < r.a) && decide (r.a < r.b) && decide (r.b ≤ D) &&
    decide (ra.2.1 * rb.2.1 < 0) &&
    decide ((10 * (r.X : ℤ) - 5) * D ≤ r.a * 10 ^ (dx + 1)) &&
    decide ((r.b : ℤ) * 10 ^ (dx + 1) ≤ (10 * r.X + 5) * D) &&
    decide (2 * 10 ^ (dw + 1) * Den ≤ (10 * (r.W : ℤ) + 5) * (ra.2.2 - E)) &&
    decide ((10 * (r.W : ℤ) - 5) * (ra.2.2 + E) ≤ 2 * 10 ^ (dw + 1) * Den)

/-- The erratum check: the printed weight `Wp/10^{dw}` exceeds the true weight by more than half a
unit in the last place. -/
def glBelow (n D dw : ℕ) (r : GLRow) (Wp : ℕ) : Bool :=
  let ra := glRH r.a D (n - 1)
  let Den : ℤ := ((n - 1).factorial : ℤ) ^ 2 * (D : ℤ) ^ (2 * (n - 1))
  let E : ℤ := ((glAC (n - 1)).2.2.2.2 : ℤ) * ((r.b : ℤ) - r.a) * (D : ℤ) ^ (2 * n - 3)
  decide (0 < Wp) && decide (2 * 10 ^ (dw + 1) * Den < (10 * (Wp : ℤ) - 5) * (ra.2.2 - E))

theorem abs_sub_le_half_ulp {x X : ℝ} {d : ℕ} (h1 : (10 * X - 5) / 10 ^ (d + 1) ≤ x)
    (h2 : x ≤ (10 * X + 5) / 10 ^ (d + 1)) : |x - X / 10 ^ d| ≤ 5 / 10 ^ (d + 1) := by
  have e1 : (10 * X - 5) / 10 ^ (d + 1) = X / 10 ^ d - 5 / 10 ^ (d + 1) := by
    rw [pow_succ]; field_simp
  have e2 : (10 * X + 5) / 10 ^ (d + 1) = X / 10 ^ d + 5 / 10 ^ (d + 1) := by
    rw [pow_succ]; field_simp
  rw [abs_le]; constructor <;> linarith

/-- Soundness of `glRowOK`: a zero `x ∈ (a/D, b/D)` of `P_n`, within half a unit of the printed
node, with `2/∑_{j<n} (2j+1) P_j(x)²` within half a unit of the printed weight. -/
theorem glRowOK_sound {n D dx dw : ℕ} (hn : 2 ≤ n) {r : GLRow}
    (h : glRowOK n D dx dw r = true) :
    ∃ x : ℝ, (r.a : ℝ) / D < x ∧ x < (r.b : ℝ) / D ∧ x ≤ 1 ∧ (legendrePoly n).eval x = 0 ∧
      |x - r.X / 10 ^ dx| ≤ 5 / 10 ^ (dx + 1) ∧
      |2 / glG (n - 1) x - r.W / 10 ^ dw| ≤ 5 / 10 ^ (dw + 1) ∧
      ∀ Wp : ℕ, glBelow n D dw r Wp = true →
        2 / glG (n - 1) x < Wp / 10 ^ dw - 5 / 10 ^ (dw + 1) := by
  simp only [glRowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hW0, ha0⟩, hab⟩, hbD⟩, hsgn⟩, hX1⟩, hX2⟩, hW1⟩, hW2⟩ := h
  have hD0 : 0 < D := by omega
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD0
  set l : ℝ := (r.a : ℝ) / D
  set u : ℝ := (r.b : ℝ) / D
  have hl0 : 0 < l := div_pos (by exact_mod_cast ha0) hDr
  have hlu : l < u := div_lt_div_of_pos_right (by exact_mod_cast hab) hDr
  have hu1 : u ≤ 1 := (div_le_one hDr).mpr (by exact_mod_cast hbD)
  have hn1 : n - 1 + 1 = n := by omega
  -- the values of the recurrences
  obtain ⟨-, hRa, hHa⟩ := glRH_spec r.a D l (by simp only [l]; push_cast; field_simp) (n - 1)
  obtain ⟨-, hRb, -⟩ := glRH_spec r.b D u (by simp only [u]; push_cast; field_simp) (n - 1)
  simp only [Int.cast_natCast] at hRa hRb hHa
  rw [hn1] at hRa hRb
  -- sign change and a zero in `(l, u)`
  have hfac : (0 : ℝ) < n.factorial * (D : ℝ) ^ n := by positivity
  have hsgnR : (legendrePoly n).eval l * (legendrePoly n).eval u < 0 := by
    have : ((glRH r.a D (n - 1)).2.1 : ℝ) * (glRH r.b D (n - 1)).2.1 < 0 := by exact_mod_cast hsgn
    rw [hRa, hRb] at this
    have e : (n.factorial : ℝ) * (D : ℝ) ^ n * (legendrePoly n).eval l *
        ((n.factorial : ℝ) * (D : ℝ) ^ n * (legendrePoly n).eval u) =
        (n.factorial * (D : ℝ) ^ n) ^ 2 * ((legendrePoly n).eval l * (legendrePoly n).eval u) := by
          ring
    rw [e] at this
    exact neg_of_mul_neg_right this (sq_nonneg _)
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ Ioo l u, (legendrePoly n).eval x = 0 := by
    have hc : ContinuousOn (fun t => (legendrePoly n).eval t) (Icc l u) :=
      (legendrePoly n).continuous.continuousOn
    rcases mul_neg_iff.mp hsgnR with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hlu.le hc ⟨h2, h1⟩
      exact ⟨x, hx, hx0⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hlu.le hc ⟨h1, h2⟩
      exact ⟨x, hx, hx0⟩
  refine ⟨x, hx.1, hx.2, hx.2.le.trans hu1, hx0, ?_, ?_⟩
  · -- the node
    have h10 : (0 : ℝ) < 10 ^ (dx + 1) := by positivity
    apply abs_sub_le_half_ulp
    · rw [div_le_iff₀ h10]
      have : ((10 * (r.X : ℝ) - 5) * D : ℝ) ≤ r.a * 10 ^ (dx + 1) := by exact_mod_cast hX1
      have hl : (r.a : ℝ) = l * D := by simp only [l]; field_simp
      rw [hl] at this
      have h1 : (10 * (r.X : ℝ) - 5) ≤ l * 10 ^ (dx + 1) :=
        le_of_mul_le_mul_right (by linarith) hDr
      linarith [mul_le_mul_of_nonneg_right hx.1.le h10.le]
    · rw [le_div_iff₀ h10]
      have : ((r.b : ℝ) * 10 ^ (dx + 1)) ≤ (10 * r.X + 5) * D := by exact_mod_cast hX2
      have hu : (r.b : ℝ) = u * D := by simp only [u]; field_simp
      rw [hu] at this
      have h1 : u * 10 ^ (dx + 1) ≤ 10 * (r.X : ℝ) + 5 :=
        le_of_mul_le_mul_right (by linarith) hDr
      linarith [mul_le_mul_of_nonneg_right hx.2.le h10.le]
  · -- the weight
    set F : ℝ := ((n - 1).factorial : ℝ)
    set H : ℝ := ((glRH r.a D (n - 1)).2.2 : ℝ)
    set Kh : ℝ := ((glAC (n - 1)).2.2.2.2 : ℝ)
    set Den : ℝ := F ^ 2 * (D : ℝ) ^ (2 * (n - 1))
    set E : ℝ := Kh * ((r.b : ℝ) - r.a) * (D : ℝ) ^ (2 * n - 3)
    have hDen : 0 < Den := by positivity
    have hDE : (D : ℝ) ^ (2 * n - 3) * D = (D : ℝ) ^ (2 * (n - 1)) := by
      rw [← pow_succ]; congr 1; omega
    -- Lipschitz transfer from `l` to `x`
    have hxl : |x - l| ≤ ((r.b : ℝ) - r.a) / D := by
      rw [abs_of_pos (by linarith [hx.1]), show ((r.b : ℝ) - r.a) / D = u - l by
        simp only [u, l]; ring]
      linarith [hx.2]
    have hx1 : |x| ≤ 1 := by rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.2]
    have hl1 : |l| ≤ 1 := by rw [abs_of_pos hl0]; linarith
    have hLip := (glAC_spec (n - 1) x l hx1 hl1).2.2.2.2
    have hGl : H = Den * glG (n - 1) l := by rw [show H = _ from hHa]
    have hdiff : Den * |glG (n - 1) x - glG (n - 1) l| ≤ E := by
      have hKh : 0 ≤ Kh := by positivity
      calc Den * |glG (n - 1) x - glG (n - 1) l| =
          (D : ℝ) ^ (2 * (n - 1)) * (F ^ 2 * |glG (n - 1) x - glG (n - 1) l|) := by ring
        _ ≤ (D : ℝ) ^ (2 * (n - 1)) * (Kh * (((r.b : ℝ) - r.a) / D)) :=
          mul_le_mul_of_nonneg_left (hLip.trans (mul_le_mul_of_nonneg_left hxl hKh))
            (by positivity)
        _ = E := by
          simp only [E]; rw [← hDE]; field_simp
    have hlo : H - E ≤ Den * glG (n - 1) x := by
      rw [hGl]; have := neg_abs_le (glG (n - 1) x - glG (n - 1) l); nlinarith
    have hhi : Den * glG (n - 1) x ≤ H + E := by
      rw [hGl]; have := le_abs_self (glG (n - 1) x - glG (n - 1) l); nlinarith
    have h1 : 2 * 10 ^ (dw + 1) * Den ≤ (10 * (r.W : ℝ) + 5) * (H - E) := by
      have := hW1; simp only [H, E, Den, F, Kh]; exact_mod_cast this
    have h2 : (10 * (r.W : ℝ) - 5) * (H + E) ≤ 2 * 10 ^ (dw + 1) * Den := by
      have := hW2; simp only [H, E, Den, F, Kh]; exact_mod_cast this
    have hW5 : (0 : ℝ) ≤ 10 * (r.W : ℝ) - 5 := by
      have : (1 : ℝ) ≤ r.W := by exact_mod_cast hW0
      linarith
    have h10 : (0 : ℝ) < 10 ^ (dw + 1) := by positivity
    have hGpos : 0 < glG (n - 1) x := by
      by_contra hneg
      push Not at hneg
      have : (10 * (r.W : ℝ) + 5) * (H - E) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith)
      nlinarith
    have hA : 2 * 10 ^ (dw + 1) ≤ (10 * (r.W : ℝ) + 5) * glG (n - 1) x := by
      have := h1.trans (mul_le_mul_of_nonneg_left hlo (by positivity))
      refine le_of_mul_le_mul_right (this.trans_eq ?_) hDen
      ring
    have hB : (10 * (r.W : ℝ) - 5) * glG (n - 1) x ≤ 2 * 10 ^ (dw + 1) := by
      have := (mul_le_mul_of_nonneg_left hhi hW5).trans h2
      refine le_of_mul_le_mul_right (le_of_eq_of_le ?_ this) hDen
      ring
    refine ⟨?_, fun Wp hWp => ?_⟩
    · apply abs_sub_le_half_ulp
      · rw [div_le_div_iff₀ h10 hGpos]; linarith
      · rw [div_le_div_iff₀ hGpos h10]; linarith
    · simp only [glBelow, Bool.and_eq_true, decide_eq_true_eq] at hWp
      obtain ⟨hWp0, hWp1⟩ := hWp
      have h3 : 2 * 10 ^ (dw + 1) * Den < (10 * (Wp : ℝ) - 5) * (H - E) := by
        have := hWp1; simp only [H, E, Den, F, Kh]; exact_mod_cast this
      have hWp5 : (0 : ℝ) ≤ 10 * (Wp : ℝ) - 5 := by
        have : (1 : ℝ) ≤ Wp := by exact_mod_cast hWp0
        linarith
      have hC : 2 * 10 ^ (dw + 1) < (10 * (Wp : ℝ) - 5) * glG (n - 1) x := by
        have := h3.trans_le (mul_le_mul_of_nonneg_left hlo hWp5)
        refine lt_of_mul_lt_mul_right (this.trans_eq ?_) hDen.le
        ring
      have e : (Wp : ℝ) / 10 ^ dw - 5 / 10 ^ (dw + 1) = (10 * Wp - 5) / 10 ^ (dw + 1) := by
        rw [pow_succ]; field_simp
      rw [e, div_lt_div_iff₀ hGpos h10]
      linarith

/-! ### Nodes and weights of the Gauss–Legendre rule -/

/-- The nodes of the `n`-point Gauss–Legendre rule: the zeros of `p_n`. -/
noncomputable def glNodes (n : ℕ) : Finset ℝ := (legendreMonic n).roots.toFinset

/-- The weights (Christoffel numbers 3.5.18) of the `n`-point Gauss–Legendre rule. -/
noncomputable def glWeight (n : ℕ) (x : ℝ) : ℝ :=
  christoffel (Ioo (-1) 1) (fun _ => 1) (legendreMonic n) x

theorem mem_glNodes_iff (n : ℕ) (x : ℝ) : x ∈ glNodes n ↔ (legendrePoly n).eval x = 0 := by
  rw [glNodes, Multiset.mem_toFinset, mem_roots (legendreMonic_monic n).ne_zero, IsRoot.def,
    legendreP_eq, eval_mul, eval_C, mul_eq_zero, or_iff_right (legendreLead_pos n).ne']

theorem card_glNodes (n : ℕ) : #(glNodes n) = n := by
  obtain ⟨hnodup, hcard, -⟩ := (isOrthMonic_legendreMonic n).roots_spec isGaussWeight_legendre
  rw [glNodes, Multiset.toFinset_card_of_nodup hnodup, hcard]

theorem glWeight_eq {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ glNodes n) :
    glWeight n x = 2 / glG (n - 1) x := by
  rw [glWeight, christoffel_legendre n hx, glG, show n - 1 + 1 = n by omega]

theorem neg_mem_glNodes {n : ℕ} {x : ℝ} (hx : x ∈ glNodes n) : -x ∈ glNodes n := by
  rw [mem_glNodes_iff] at hx ⊢
  rw [eval_neg_legendreP, hx, mul_zero]

theorem glG_neg (k : ℕ) (x : ℝ) : glG k (-x) = glG k x := by
  simp only [glG, eval_neg_legendreP]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
  norm_num

/-- The weights are symmetric: `w(−x) = w(x)`. -/
theorem glWeight_neg {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ glNodes n) :
    glWeight n (-x) = glWeight n x := by
  rw [glWeight_eq hn (neg_mem_glNodes hx), glWeight_eq hn hx, glG_neg]

/-- The node `0` of an odd rule: the exact check of its weight (`m = 0`, `D = 1`). -/
def glZeroOK (n dw W : ℕ) : Bool :=
  let h := (glRH 0 1 (n - 1)).2.2
  let Den : ℤ := ((n - 1).factorial : ℤ) ^ 2
  decide (n % 2 = 1) && decide (0 < W) &&
    decide (2 * 10 ^ (dw + 1) * Den ≤ (10 * (W : ℤ) + 5) * h) &&
    decide ((10 * (W : ℤ) - 5) * h ≤ 2 * 10 ^ (dw + 1) * Den)

theorem glZeroOK_sound {n dw W : ℕ} (h : glZeroOK n dw W = true) :
    (0 : ℝ) ∈ glNodes n ∧ |glWeight n 0 - W / 10 ^ dw| ≤ 5 / 10 ^ (dw + 1) := by
  simp only [glZeroOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hodd, hW0⟩, hW1⟩, hW2⟩ := h
  have h0 : (0 : ℝ) ∈ glNodes n := by
    rw [mem_glNodes_iff]
    have := eval_neg_legendreP n 0
    rw [neg_zero, Odd.neg_one_pow (Nat.odd_iff.mpr hodd)] at this
    linarith
  refine ⟨h0, ?_⟩
  have hn : 1 ≤ n := by omega
  rw [glWeight_eq hn h0]
  obtain ⟨-, -, hH⟩ := glRH_spec 0 1 0 (by simp) (n - 1)
  simp only [Int.cast_one, one_pow, mul_one] at hH
  set F : ℝ := ((n - 1).factorial : ℝ)
  have hF : 0 < F ^ 2 := by positivity
  have h1 : 2 * 10 ^ (dw + 1) * F ^ 2 ≤ (10 * (W : ℝ) + 5) * (F ^ 2 * glG (n - 1) 0) := by
    have := (Int.cast_le (R := ℝ)).mpr hW1
    push_cast at this
    rwa [hH] at this
  have h2 : (10 * (W : ℝ) - 5) * (F ^ 2 * glG (n - 1) 0) ≤ 2 * 10 ^ (dw + 1) * F ^ 2 := by
    have := (Int.cast_le (R := ℝ)).mpr hW2
    push_cast at this
    rwa [hH] at this
  have hA : 2 * 10 ^ (dw + 1) ≤ (10 * (W : ℝ) + 5) * glG (n - 1) 0 :=
    le_of_mul_le_mul_right (h1.trans_eq (by ring)) hF
  have hB : (10 * (W : ℝ) - 5) * glG (n - 1) 0 ≤ 2 * 10 ^ (dw + 1) :=
    le_of_mul_le_mul_right (le_of_eq_of_le (by ring) h2) hF
  have h10 : (0 : ℝ) < 10 ^ (dw + 1) := by positivity
  have hGpos : 0 < glG (n - 1) 0 := by
    by_contra hneg; push Not at hneg
    have : (10 * (W : ℝ) + 5) * glG (n - 1) 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  apply abs_sub_le_half_ulp
  · rw [div_le_div_iff₀ h10 hGpos]; linarith
  · rw [div_le_div_iff₀ hGpos h10]; linarith

/-! ### Tables -/

/-- A Gauss–Legendre table `(X, W)` of printed nodes `X/10^{dx}` and weights `W/10^{dw}`
(nonnegative nodes, the negative ones by symmetry) is correctly rounded and complete: every row
is within half a unit of a node and its weight, and every node `±x` is a row. -/
def GLTableSpec (n dx dw : ℕ) (tab : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ tab, ∃ x ∈ glNodes n, 0 ≤ x ∧ |x - p.1 / 10 ^ dx| ≤ 5 / 10 ^ (dx + 1) ∧
      |glWeight n x - p.2 / 10 ^ dw| ≤ 5 / 10 ^ (dw + 1)) ∧
  ∀ x ∈ glNodes n, ∃ p ∈ tab, |abs x - p.1 / 10 ^ dx| ≤ 5 / 10 ^ (dx + 1)

/-- The exact checks for a whole table: every row, disjoint ordered brackets, the right count, and
the zero node for odd `n`. -/
def glTableOK (n D dx dw : ℕ) (zero : Option ℕ) (rows : List GLRow) : Bool :=
  decide (2 ≤ n) && rows.all (glRowOK n D dx dw) &&
    decide (rows.Pairwise fun r s => r.b < s.a) &&
    decide (2 * rows.length + (if zero.isSome then 1 else 0) = n) &&
    (match zero with
      | none => true
      | some W => glZeroOK n dw W)

/-- The printed table of a checked table. -/
def glTab (zero : Option ℕ) (rows : List GLRow) : List (ℕ × ℕ) :=
  (zero.map fun W => (0, W)).toList ++ rows.map fun r => (r.X, r.W)

theorem glTableOK_sound {n D dx dw : ℕ} {zero : Option ℕ} {rows : List GLRow}
    (h : glTableOK n D dx dw zero rows = true) : GLTableSpec n dx dw (glTab zero rows) := by
  classical
  simp only [glTableOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hn, hrows⟩, hpw⟩, hcount⟩, hzero⟩ := h
  have hn1 : 1 ≤ n := by omega
  -- the certified positive nodes
  have hrow : ∀ i : Fin rows.length, ∃ x : ℝ, (rows[i].a : ℝ) / D < x ∧ x < (rows[i].b : ℝ) / D ∧
      x ∈ glNodes n ∧ |x - rows[i].X / 10 ^ dx| ≤ 5 / 10 ^ (dx + 1) ∧
      |glWeight n x - rows[i].W / 10 ^ dw| ≤ 5 / 10 ^ (dw + 1) ∧ 0 < x := fun i => by
    have hok := hrows rows[i] (List.getElem_mem _)
    obtain ⟨x, hl, hu, -, hx0, hX, hW, -⟩ := glRowOK_sound hn hok
    have hmem : x ∈ glNodes n := (mem_glNodes_iff n x).mpr hx0
    have ha : 0 < rows[i].a := by
      simp only [glRowOK, Bool.and_eq_true, decide_eq_true_eq] at hok; omega
    have hD : 0 < D := by
      simp only [glRowOK, Bool.and_eq_true, decide_eq_true_eq] at hok; omega
    refine ⟨x, hl, hu, hmem, hX, by rwa [glWeight_eq hn1 hmem], ?_⟩
    exact lt_trans (div_pos (by exact_mod_cast ha) (by exact_mod_cast hD)) hl
  choose xs hxl hxu hxmem hxX hxW hxpos using hrow
  -- strictly increasing
  have hmono : StrictMono xs := by
    intro i j hij
    have hb : rows[i].b < rows[j].a := List.pairwise_iff_getElem.mp hpw i j i.2 j.2 hij
    have hD : (0 : ℝ) ≤ D := by positivity
    have : (rows[i].b : ℝ) / D ≤ (rows[j].a : ℝ) / D :=
      div_le_div_of_nonneg_right (by exact_mod_cast hb.le) hD
    linarith [hxu i, hxl j]
  refine ⟨?_, ?_⟩
  · -- every row is a node
    intro p hp
    simp only [glTab, List.mem_append, Option.mem_toList, Option.map_eq_some_iff,
      List.mem_map] at hp
    rcases hp with ⟨W, hW, rfl⟩ | ⟨r, hr, rfl⟩
    · subst hW
      obtain ⟨h0, hw⟩ := glZeroOK_sound hzero
      exact ⟨0, h0, le_rfl, by simp; positivity, hw⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      exact ⟨xs ⟨i, hi⟩, hxmem _, (hxpos _).le, hxX _, hxW _⟩
  · -- every node is a row
    set Spos : Finset ℝ := univ.image xs
    set Sneg : Finset ℝ := Spos.image (fun t => -t)
    set Z : Finset ℝ := if zero.isSome then {0} else ∅
    have hsub : Spos ∪ Sneg ∪ Z ⊆ glNodes n := by
      intro t ht
      simp only [Spos, Sneg, Z, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at ht
      rcases ht with (⟨i, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩) | hz
      · exact hxmem i
      · exact neg_mem_glNodes (hxmem i)
      · cases hzz : zero with
        | none => simp [hzz] at hz
        | some W =>
          simp [hzz] at hz; subst hz
          rw [hzz] at hzero
          exact (glZeroOK_sound hzero).1
    have hcpos : #Spos = rows.length := by
      rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
    have hcneg : #Sneg = rows.length := by
      rw [Finset.card_image_of_injective _ neg_injective, hcpos]
    have hdisj1 : Disjoint Spos Sneg := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      simp only [Spos, Sneg, Finset.mem_image, Finset.mem_univ, true_and] at ht ht'
      obtain ⟨i, rfl⟩ := ht
      obtain ⟨_, ⟨j, rfl⟩, hj⟩ := ht'
      linarith [hxpos i, hxpos j]
    have hdisj2 : Disjoint (Spos ∪ Sneg) Z := by
      rw [Finset.disjoint_left]
      intro t ht htz
      simp only [Z] at htz
      split_ifs at htz
      · rw [Finset.mem_singleton] at htz
        subst htz
        simp only [Spos, Sneg, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at ht
        rcases ht with ⟨i, hi⟩ | ⟨_, ⟨j, rfl⟩, hj⟩
        · linarith [hxpos i]
        · linarith [hxpos j]
      · simp at htz
    have hcard : #(Spos ∪ Sneg ∪ Z) = n := by
      rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1, hcpos, hcneg]
      simp only [Z]
      split_ifs <;> simp_all <;> omega
    have heq : Spos ∪ Sneg ∪ Z = glNodes n :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_glNodes, hcard])
    intro t ht
    rw [← heq] at ht
    simp only [Spos, Sneg, Z, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at ht
    rcases ht with (⟨i, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩) | hz
    · refine ⟨(rows[i].X, rows[i].W), ?_, by rw [abs_of_pos (hxpos i)]; exact hxX i⟩
      simp only [glTab, List.mem_append, List.mem_map]
      exact Or.inr ⟨rows[i], List.getElem_mem _, rfl⟩
    · refine ⟨(rows[i].X, rows[i].W), ?_, by rw [abs_neg, abs_of_pos (hxpos i)]; exact hxX i⟩
      simp only [glTab, List.mem_append, List.mem_map]
      exact Or.inr ⟨rows[i], List.getElem_mem _, rfl⟩
    · cases hzz : zero with
      | none => simp [hzz] at hz
      | some W =>
        simp [hzz] at hz; subst hz
        refine ⟨(0, W), ?_, by simp; positivity⟩
        simp [glTab]

/-- An erratum row: the certified node and weight, and the printed weight `Wp/10^{dw}` more than
half a unit above the true weight. -/
theorem glErratum_sound {n D dx dw : ℕ} (hn : 2 ≤ n) {r : GLRow} {Wp : ℕ}
    (h : glRowOK n D dx dw r = true) (hb : glBelow n D dw r Wp = true) :
    ∃ x ∈ glNodes n, |x - r.X / 10 ^ dx| ≤ 5 / 10 ^ (dx + 1) ∧
      |glWeight n x - r.W / 10 ^ dw| ≤ 5 / 10 ^ (dw + 1) ∧
      glWeight n x < Wp / 10 ^ dw - 5 / 10 ^ (dw + 1) := by
  obtain ⟨x, -, -, -, hx0, hX, hW, hB⟩ := glRowOK_sound hn h
  have hmem : x ∈ glNodes n := (mem_glNodes_iff n x).mpr hx0
  rw [← glWeight_eq (by omega) hmem] at hW hB
  exact ⟨x, hmem, hX, hW, hB Wp hb⟩

/-! ### The certificates (`D = 10^90`; brackets `(a/D, (a+1)/D)`) -/

/-- A row with the bracket `(a/D, (a + 1)/D)`. -/
def glRow (a X W : ℕ) : GLRow := ⟨a, a + 1, X, W⟩

/-- The brackets and printed values of Table 3.5.1. -/
def glRows_3_5_1 : List GLRow := [
  glRow
    538469310105683091036314420700208804967286606905559956202231627059471185367755291035803667
    538469310105683 478628670499366,
  glRow
    906179845938663992797626878299392965125651910762530862873762286543770794916686846941142989
    906179845938664 236926885056189]

set_option maxRecDepth 100000 in
theorem glTableOK_3_5_1 :
    glTableOK 5 (10 ^ 90) 15 15 (some 568888888888889) glRows_3_5_1 = true := by
  decide +kernel

/-- **Table 3.5.1** (5-point Gauss–Legendre formula): the nodes `±x_k` and the weights `w_k`
are correctly rounded to 15 decimals, and the table is complete. -/
theorem dlmf_table_3_5_1 : GLTableSpec 5 15 15 [
    (0, 568888888888889),
    (538469310105683, 478628670499366),
    (906179845938664, 236926885056189)] :=
  glTableOK_sound glTableOK_3_5_1

/-- The brackets and printed values of Table 3.5.2. -/
def glRows_3_5_2 : List GLRow := [
  glRow
    148874338981631210884826001129719984617564859420691695707989253515903617355668521371177629
    148874338981631211 295524224714752870,
  glRow
    433395394129247190799265943165784162200071837656246496502701513143766989077703501225102757
    433395394129247191 269266719309996355,
  glRow
    679409568299024406234327365114873575769294711834809467664817188952558575395074924615078573
    679409568299024406 219086362515982044,
  glRow
    865063366688984510732096688423493048527543014965330452521959731845374755138055561356790728
    865063366688984511 149451349150580593,
  glRow
    973906528517171720077964012084452053428269946692382119231212066696595203234636159625723564
    973906528517171720 66671344308688138]

set_option maxRecDepth 100000 in
theorem glTableOK_3_5_2 :
    glTableOK 10 (10 ^ 90) 18 18 none glRows_3_5_2 = true := by
  decide +kernel

/-- **Table 3.5.2** (10-point Gauss–Legendre formula): the nodes `±x_k` and the weights `w_k`
are correctly rounded to 18 decimals, and the table is complete. -/
theorem dlmf_table_3_5_2 : GLTableSpec 10 18 18 [
    (148874338981631211, 295524224714752870),
    (433395394129247191, 269266719309996355),
    (679409568299024406, 219086362515982044),
    (865063366688984511, 149451349150580593),
    (973906528517171720, 66671344308688138)] :=
  glTableOK_sound glTableOK_3_5_2

/-- The brackets and printed values of Table 3.5.3. -/
def glRows_3_5_3 : List GLRow := [
  glRow
    76526521133497333754640409398838211004796266813497500804795244384256342048336978241545114
    76526521133497333755 152753387130725850698,
  glRow
    227785851141645078080496195368574624743088937682927472314635739207171341863555827794952125
    227785851141645078080 149172986472603746788,
  glRow
    373706088715419560672548177024927237395746321705682711827948613515645764373059527895895683
    373706088715419560673 142096109318382051329,
  glRow
    510867001950827098004364050955250998425491329202426833472348619894734970390765728144031683
    510867001950827098004 131688638449176626898,
  glRow
    636053680726515025452836696226285936743389116799368463939446622546541262585430132558703195
    636053680726515025453 118194531961518417312,
  glRow
    746331906460150792614305070355641590310730679569176444139545906068535355038155064681104113
    746331906460150792614 101930119817240435037,
  glRow
    839116971822218823394529061701520685329629365065637373252492725532861093999324809919229340
    839116971822218823395 83276741576704748725,
  glRow
    912234428251325905867752441203298113049184797423691774795882219158070891208719078936444726
    912234428251325905868 62672048334109063570,
  glRow
    963971927277913791267666131197277221912060327806188856063537593892041580784383056980018125
    963971927277913791268 40601429800386941331,
  glRow
    993128599185094924786122388471320278222647130901655896148184131217984717627753780839449402
    993128599185094924786 17614007139152118312]

set_option maxRecDepth 100000 in
theorem glTableOK_3_5_3 :
    glTableOK 20 (10 ^ 90) 21 21 none glRows_3_5_3 = true := by
  decide +kernel

/-- **Table 3.5.3** (20-point Gauss–Legendre formula): the nodes `±x_k` and the weights `w_k`
are correctly rounded to 21 decimals, and the table is complete. -/
theorem dlmf_table_3_5_3 : GLTableSpec 20 21 21 [
    (76526521133497333755, 152753387130725850698),
    (227785851141645078080, 149172986472603746788),
    (373706088715419560673, 142096109318382051329),
    (510867001950827098004, 131688638449176626898),
    (636053680726515025453, 118194531961518417312),
    (746331906460150792614, 101930119817240435037),
    (839116971822218823395, 83276741576704748725),
    (912234428251325905868, 62672048334109063570),
    (963971927277913791268, 40601429800386941331),
    (993128599185094924786, 17614007139152118312)] :=
  glTableOK_sound glTableOK_3_5_3

/-- The brackets and printed values of Table 3.5.4. -/
def glRows_3_5_4 : List GLRow := [
  glRow
    38772417506050821933193444024623294679364634383141599168637181438006575000920756208604273
    38772417506050821933 77505947978424811264,
  glRow
    116084070675255208483451284408024113768728530854215949030297432161579163947867173515377113
    116084070675255208483 77039818164247965588,
  glRow
    192697580701371099715516852065149894814092021105208874885467592236502721663643411549924620
    192697580701371099716 76110361900626242372,
  glRow
    268152185007253681141184344808596183424804373236246981457259974873821193193734224352190375
    268152185007253681141 74723169057968264200,
  glRow
    341994090825758473007492481179194310066953620027325796463409584098143708942120883323195466
    341994090825758473007 72886582395804059061,
  glRow
    413779204371605001524879745803713682974099624052918238294402251068642663609220731437836058
    413779204371605001525 70611647391286779695,
  glRow
    483075801686178712908566574244823004599022395533114100789335243225943442741906859245875104
    483075801686178712909 67912045815233903826,
  glRow
    549467125095128202075931305529517970233975101595651464902565471721855745113483590471763292
    549467125095128202076 64804013456601038075,
  glRow
    612553889667980237952612450230694877380123781683149611135347562530190972424438235220121959
    612553889667980237953 61306242492928939167,
  glRow
    671956684614179548379354514961494109970325981383851150071092968986662475956619765946031944
    671956684614179548379 57439769099391551367,
  glRow
    727318255189927103280996451754930548557378673533328137547551244185929114646088472607541106
    727318255189927103281 53227846983936824355,
  glRow
    778305651426519387694971545506494848020691316126891794245342060629311941916180571441200091
    778305651426519387695 48695807635072232061,
  glRow
    824612230833311663196320230666098773907240384242987799691790963152807171842695724432449525
    824612230833311663196 43870908185673271992,
  glRow
    865959503212259503820781808354619963570546553011101649459940254806682078847082555300916562
    865959503212259503821 38782167974472017640,
  glRow
    902098806968874296728253330868493103584488081057669467725260111540370181400984707395893987
    902098806968874296728 33460195282547847393,
  glRow
    932812808278676533360852166845205716434753575282692449229343015415640523923346229533854687
    932812808278676533361 27937006980023401098,
  glRow
    957916819213791655804540999452759285094883490602747031569053843581758355623483729320420611
    957916819213791655805 22245849194166957262,
  glRow
    977259949983774262663370283712903806978667932037986096429262016011063214444214457187689300
    977259949983774262663 16421058381907888713,
  glRow
    990726238699457006453054352221372154962222081351086537883076244304078903238544596629110505
    990726238699457006453 10498284531152813615,
  glRow
    998237709710559200349622702420586492335770381595045906603336117096838863019727805077886187
    998237709710559200350 4521277098533191258]

set_option maxRecDepth 100000 in
theorem glTableOK_3_5_4 :
    glTableOK 40 (10 ^ 90) 21 21 none glRows_3_5_4 = true := by
  decide +kernel

/-- **Table 3.5.4** (40-point Gauss–Legendre formula): the nodes `±x_k` and the weights `w_k`
are correctly rounded to 21 decimals (with the corrected last digits of the errata below),
and the table is complete. -/
theorem dlmf_table_3_5_4 : GLTableSpec 40 21 21 [
    (38772417506050821933, 77505947978424811264),
    (116084070675255208483, 77039818164247965588),
    (192697580701371099716, 76110361900626242372),
    (268152185007253681141, 74723169057968264200),
    (341994090825758473007, 72886582395804059061),
    (413779204371605001525, 70611647391286779695),
    (483075801686178712909, 67912045815233903826),
    (549467125095128202076, 64804013456601038075),
    (612553889667980237953, 61306242492928939167),
    (671956684614179548379, 57439769099391551367),
    (727318255189927103281, 53227846983936824355),
    (778305651426519387695, 48695807635072232061),
    (824612230833311663196, 43870908185673271992),
    (865959503212259503821, 38782167974472017640),
    (902098806968874296728, 33460195282547847393),
    (932812808278676533361, 27937006980023401098),
    (957916819213791655805, 22245849194166957262),
    (977259949983774262663, 16421058381907888713),
    (990726238699457006453, 10498284531152813615),
    (998237709710559200350, 4521277098533191258)] :=
  glTableOK_sound glTableOK_3_5_4

set_option maxRecDepth 100000 in
/-- **Erratum to Table 3.5.4**: at the node `0.413779204371605001525` the printed weight
`0.070611647391286779696` is not correctly
rounded; the correct value is `0.070611647391286779695`. -/
theorem dlmf_table_3_5_4_erratum_5 :
    ∃ x ∈ glNodes 40, |x - (413779204371605001525 : ℕ) / 10 ^ 21| ≤ 5 / 10 ^ (21 + 1) ∧
      |glWeight 40 x - (70611647391286779695 : ℕ) / 10 ^ 21| ≤ 5 / 10 ^ (21 + 1) ∧
      glWeight 40 x < (70611647391286779696 : ℕ) / 10 ^ 21 - 5 / 10 ^ (21 + 1) :=
  glErratum_sound (D := 10 ^ 90) (r := glRow
    413779204371605001524879745803713682974099624052918238294402251068642663609220731437836058
    413779204371605001525 70611647391286779695) (by norm_num)
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **Erratum to Table 3.5.4**: at the node `0.932812808278676533361` the printed weight
`0.027937006980023401099` is not correctly
rounded; the correct value is `0.027937006980023401098`. -/
theorem dlmf_table_3_5_4_erratum_15 :
    ∃ x ∈ glNodes 40, |x - (932812808278676533361 : ℕ) / 10 ^ 21| ≤ 5 / 10 ^ (21 + 1) ∧
      |glWeight 40 x - (27937006980023401098 : ℕ) / 10 ^ 21| ≤ 5 / 10 ^ (21 + 1) ∧
      glWeight 40 x < (27937006980023401099 : ℕ) / 10 ^ 21 - 5 / 10 ^ (21 + 1) :=
  glErratum_sound (D := 10 ^ 90) (r := glRow
    932812808278676533360852166845205716434753575282692449229343015415640523923346229533854687
    932812808278676533361 27937006980023401098) (by norm_num)
    (by decide +kernel) (by decide +kernel)

/-- The brackets and printed values of Table 3.5.5. -/
def glRows_3_5_5 : List GLRow := [
  glRow
    19511383256793997654351234107454547933551301646997815134570447581884372245392999864015126
    19511383256793997654 39017813656306654811,
  glRow
    58504437152420668628993321883417794425398674701914398208795539637790408327052624975017123
    58504437152420668629 38958395962769531199,
  glRow
    97408398441584599063278450104936902017066184436766092590847635230667557850499973540265495
    97408398441584599063 38839651059051968932,
  glRow
    136164022809143886559241078000717067933136249634883110529029412073262722274689194897376528
    136164022809143886559 38661759774076463327,
  glRow
    174712291832646812559339048011286195718810774977062579504009119516370917509562986426713635
    174712291832646812559 38424993006959423185,
  glRow
    212994502857666132572388538666321823094788750834773702148596705813766447830045543310252225
    212994502857666132572 38129711314477638344,
  glRow
    250952358392272120493158816035004797363048927563799213064835366143802502660475959282857971
    250952358392272120493 37776364362001397490,
  glRow
    288528054884511853109139301434713898496405289013765936421046429298107146532487297068688565
    288528054884511853109 37365490238730490027,
  glRow
    325664370747701914619112943627358695036984755109080396761317809804057242240975123718816253
    325664370747701914619 36897714638276008839,
  glRow
    362304753499487315619043286358963588017109625123613371825487694348816713023341001003029839
    362304753499487315619 36373749905835978044,
  glRow
    398393405881969227024379642517533757117249124713572658748697688177075594507459230260377013
    398393405881969227024 35794393953416054603,
  glRow
    433875370831756093062386700363181958302108304345194745336508128705885110536440187487617702
    433875370831756093062 35160529044747593496,
  glRow
    468696615170544477036078364935808657293956006488266802317417567861837118679626265553983782
    468696615170544477036 34473120451753928794,
  glRow
    502804111888784987593672750367568003564940672499598159882670417372668570017442909481022294
    502804111888784987594 33733214984611522817,
  glRow
    536145920897131932019857253125400904911693125079156922726745282501350936403401112927063030
    536145920897131932020 32941939397645401383,
  glRow
    568671268122709784725485786624827158741993573659612861457380944176682551123756579664820054
    568671268122709784725 32100498673487773148,
  glRow
    600330622829751743154746299164006848430055094813786741685652028318545995970736278362106843
    600330622829751743155 31210174188114701642,
  glRow
    631075773046871966247928387289336863089063470073339188938360988398482369142622479801478922
    631075773046871966248 30272321759557980661,
  glRow
    660859898986119801735967122844317234805060118715519194875026769941056439543158774133982882
    660859898986119801736 29288369583267847693,
  glRow
    689637644342027600771207612438935266089722945470212805337565094123657749767155346340268200
    689637644342027600771 28259816057276862397,
  glRow
    717365185362099880254068258293815278566830552925811099070698325729238414265167714601505693
    717365185362099880254 27188227500486380674,
  glRow
    744000297583597272316540527930913673808679084668918214688948704190520271998187922249859324
    744000297583597272317 26075235767565117903,
  glRow
    769502420135041373865616068749026083985405945335283938547276051773536292296318270720162556
    769502420135041373866 24922535764115491105,
  glRow
    793832717504605449948639311738454358610603750752767387598119024413513913673660010702019034
    793832717504605449949 23731882865930101293,
  glRow
    816954138681463470371124994012295707742841200671466249305446789107962774345411130851044882
    816954138681463470371 22505090246332461926,
  glRow
    838831473580255275616623043902867064793623412611807714956704525602723268107444805453015405
    838831473580255275617 21244026115782006389,
  glRow
    859431406663111096977192123491656492839931489614644255445562976532651466091395800640150542
    859431406663111096977 19950610878141998929,
  glRow
    878722567678213828703773343639124407935851776676766267392623278242431205373143036454120997
    878722567678213828704 18626814208299031429,
  glRow
    896675579438770683194324071967395986307299702051986985196059564364339049620277639822432132
    896675579438770683194 17274652056269306359,
  glRow
    913263102571757654164733656150947478111452468310774734314103604613119921502450069251325512
    913263102571757654165 15896183583725688045,
  glRow
    928459877172445795953045959075453133792234988839582012054803009503138605172986383900264310
    928459877172445795953 14493508040509076117,
  glRow
    942242761309872674752266004500001735070833966241979363484039226541744981771963757030962367
    942242761309872674752 13068761592401339294,
  glRow
    954590766343634905493481517021029508783646814704099200519341188283341648378724213535189091
    954590766343634905493 11624114120797826916,
  glRow
    965485089043799251452273155671454998502903485848611304473289491364589414047323029988236834
    965485089043799251452 10161766041103064521,
  glRow
    974909140585727793385645230069136276244959716036304476853701567455782045440111005984160398
    974909140585727793386 8683945269260858426,
  glRow
    982848572738629070418288027709116473568694058814879837207539857969175853629473974710882380
    982848572738629070418 7192904768117312753,
  glRow
    989291302499755531026503167136631385282151777830901614537433877694405392137436995660571823
    989291302499755531027 5690922451403198649,
  glRow
    994227540965688277892063503664911698088808604954712035819943263588551149823067481386720688
    994227540965688277892 4180313124694895237,
  glRow
    997649864398237688899494208183122985331074834396563621481884029617399304187921842273625188
    997649864398237688899 2663533589512681669,
  glRow
    999553822651630629880080499094567184991693557685851817816371219867321146835621821104911933
    999553822651630629880 1144950003186941535]

set_option maxRecDepth 100000 in
theorem glTableOK_3_5_5 :
    glTableOK 80 (10 ^ 90) 21 21 none glRows_3_5_5 = true := by
  decide +kernel

/-- **Table 3.5.5** (80-point Gauss–Legendre formula): the nodes `±x_k` and the weights `w_k`
are correctly rounded to 21 decimals (with the corrected last digits of the errata below),
and the table is complete. -/
theorem dlmf_table_3_5_5 : GLTableSpec 80 21 21 [
    (19511383256793997654, 39017813656306654811),
    (58504437152420668629, 38958395962769531199),
    (97408398441584599063, 38839651059051968932),
    (136164022809143886559, 38661759774076463327),
    (174712291832646812559, 38424993006959423185),
    (212994502857666132572, 38129711314477638344),
    (250952358392272120493, 37776364362001397490),
    (288528054884511853109, 37365490238730490027),
    (325664370747701914619, 36897714638276008839),
    (362304753499487315619, 36373749905835978044),
    (398393405881969227024, 35794393953416054603),
    (433875370831756093062, 35160529044747593496),
    (468696615170544477036, 34473120451753928794),
    (502804111888784987594, 33733214984611522817),
    (536145920897131932020, 32941939397645401383),
    (568671268122709784725, 32100498673487773148),
    (600330622829751743155, 31210174188114701642),
    (631075773046871966248, 30272321759557980661),
    (660859898986119801736, 29288369583267847693),
    (689637644342027600771, 28259816057276862397),
    (717365185362099880254, 27188227500486380674),
    (744000297583597272317, 26075235767565117903),
    (769502420135041373866, 24922535764115491105),
    (793832717504605449949, 23731882865930101293),
    (816954138681463470371, 22505090246332461926),
    (838831473580255275617, 21244026115782006389),
    (859431406663111096977, 19950610878141998929),
    (878722567678213828704, 18626814208299031429),
    (896675579438770683194, 17274652056269306359),
    (913263102571757654165, 15896183583725688045),
    (928459877172445795953, 14493508040509076117),
    (942242761309872674752, 13068761592401339294),
    (954590766343634905493, 11624114120797826916),
    (965485089043799251452, 10161766041103064521),
    (974909140585727793386, 8683945269260858426),
    (982848572738629070418, 7192904768117312753),
    (989291302499755531027, 5690922451403198649),
    (994227540965688277892, 4180313124694895237),
    (997649864398237688899, 2663533589512681669),
    (999553822651630629880, 1144950003186941535)] :=
  glTableOK_sound glTableOK_3_5_5

set_option maxRecDepth 100000 in
/-- **Erratum to Table 3.5.5**: at the node `0.954590766343634905493` the printed weight
`0.011624114120797826917` is not correctly
rounded; the correct value is `0.011624114120797826916`. -/
theorem dlmf_table_3_5_5_erratum_32 :
    ∃ x ∈ glNodes 80, |x - (954590766343634905493 : ℕ) / 10 ^ 21| ≤ 5 / 10 ^ (21 + 1) ∧
      |glWeight 80 x - (11624114120797826916 : ℕ) / 10 ^ 21| ≤ 5 / 10 ^ (21 + 1) ∧
      glWeight 80 x < (11624114120797826917 : ℕ) / 10 ^ 21 - 5 / 10 ^ (21 + 1) :=
  glErratum_sound (D := 10 ^ 90) (r := glRow
    954590766343634905493481517021029508783646814704099200519341188283341648378724213535189091
    954590766343634905493 11624114120797826916) (by norm_num)
    (by decide +kernel) (by decide +kernel)

end Azurite.DLMF
