/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5GaussHermite
import Azurite.AzFloat.Equiv.Interval

/-!
# DLMF §3.5(v): Tables 3.5.10–3.5.13 (Gauss–Hermite nodes and weights)

Every number in Tables 3.5.10–3.5.13 (`n = 5, 10, 15, 20`) is certified by exact integer
arithmetic, checked by the kernel (`decide +kernel`, kernel `Nat`/`Int` arithmetic); all entries are
correctly rounded.

* `hermRH`: the recurrence 18.9.1 at `x = m/D` scaled to integers, `R_k = Dᵏ H_k(x)` and
  `S_k = 2ᵏ k! D^{2k} ∑_{j≤k} H_j(x)²/(2^j j!)` (`hermRH_spec`).
* `hermAC`: integer majorants on `[−R, R]` of `|H_k|`, of the Lipschitz constant of `H_k`, and of
  that of `2ᵏ k! ∑_{j≤k} H_j²/(2^j j!)` (`hermAC_spec`).
* `herm_pi_bounds`: rational bounds on `π` from the 128-bit AzFloat enclosure (`enclosesPos_pi`,
  kernel-evaluated); `hermWOK`/`hermWOK_sound` check a printed weight of `√π/g` by squaring.
* `hermRowOK`/`hermRowOK_sound`: a sign change of `H_n` across a bracket `(a/D, (a+1)/D)`, the
  bracket inside the rounding interval of the printed node, and the weight
  `√π/∑_{j<n} H_j²/(2^j j!)` (`christoffel_hermite`) inside that of the printed weight;
  `hermZeroOK` for the node `0` of an odd rule.
* `hermTableOK`/`hermTableOK_sound` → `HermTableSpec`: every row is a node and weight, correctly
  rounded, and every node `±x` (`hermNodes`, `card_hermNodes`) is a row; the weights are even
  (`hermWeight_neg`).
* Tables 3.5.10–3.5.13: `dlmf_table_3_5_10` … `dlmf_table_3_5_13` (`D = 10^100`).
-/

open Polynomial Finset Set Real

namespace Azurite.DLMF

/-! ### Exact integer recurrences -/

/-- `(R_k, R_{k+1}, S_k)` at `x = m/D`: `R_k = Dᵏ H_k(x)` (18.9.1 scaled to integers) and
`S_k = 2ᵏ k! D^{2k} ∑_{j≤k} H_j(x)²/(2^j j!)`. -/
def hermRH (m D : ℤ) : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, 2 * m, 1)
  | k + 1 =>
    match hermRH m D k with
    | (r0, r1, h) =>
      (r1, 2 * m * r1 - 2 * (k + 1) * D ^ 2 * r0, 2 * (k + 1) * D ^ 2 * h + r1 ^ 2)

/-- `∑_{j≤k} H_j(x)²/(2^j j!)`. -/
noncomputable def hermG (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), (hermiteH j).eval x ^ 2 / (2 ^ j * j.factorial)

theorem hermG_succ (k : ℕ) (x : ℝ) :
    hermG (k + 1) x =
      hermG k x + (hermiteH (k + 1)).eval x ^ 2 / (2 ^ (k + 1) * (k + 1).factorial) :=
  sum_range_succ _ (k + 1)

theorem hermRH_spec (m D : ℤ) (x : ℝ) (hm : (m : ℝ) = x * D) (k : ℕ) :
    ((hermRH m D k).1 : ℝ) = (D : ℝ) ^ k * (hermiteH k).eval x ∧
    ((hermRH m D k).2.1 : ℝ) = (D : ℝ) ^ (k + 1) * (hermiteH (k + 1)).eval x ∧
    ((hermRH m D k).2.2 : ℝ) = 2 ^ k * k.factorial * (D : ℝ) ^ (2 * k) * hermG k x := by
  induction k with
  | zero =>
    simp [hermRH, hermG, eval_hermiteH_zero, eval_hermiteH_one, hm]
    ring
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    simp only [hermRH]
    refine ⟨h1, ?_, ?_⟩
    · push_cast
      rw [h1, h0, hm, show k + 1 + 1 = k + 2 from rfl, eval_hermiteH_succ_succ]
      ring
    · push_cast
      rw [h2, h1, hermG_succ, Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- Majorants `(A_k, A_{k+1}, C_k, C_{k+1}, K_k)` on `[−R, R]`: `|H_k| ≤ A_k`,
`|H_k(x) − H_k(y)| ≤ C_k |x − y|`, `2ᵏ k! |G_k(x) − G_k(y)| ≤ K_k |x − y|`. -/
def hermAC (R : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 2 * R, 0, 2, 0)
  | k + 1 =>
    match hermAC R k with
    | (a0, a1, c0, c1, kk) =>
      (a1, 2 * R * a1 + 2 * (k + 1) * a0, c1, 2 * R * c1 + 2 * a1 + 2 * (k + 1) * c0,
        2 * (k + 1) * kk + 2 * a1 * c1)

theorem hermAC_spec (R k : ℕ) : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R →
    |(hermiteH k).eval x| ≤ (hermAC R k).1 ∧
    |(hermiteH (k + 1)).eval x| ≤ (hermAC R k).2.1 ∧
    |(hermiteH k).eval x - (hermiteH k).eval y| ≤ (hermAC R k).2.2.1 * |x - y| ∧
    |(hermiteH (k + 1)).eval x - (hermiteH (k + 1)).eval y| ≤ (hermAC R k).2.2.2.1 * |x - y| ∧
    2 ^ k * (k.factorial : ℝ) * |hermG k x - hermG k y| ≤ (hermAC R k).2.2.2.2 * |x - y| := by
  induction k with
  | zero =>
    intro x y hx hy
    simp only [hermAC, hermG, eval_hermiteH_zero, eval_hermiteH_one, zero_add, sum_range_one]
    refine ⟨by simp, ?_, by simp, ?_, by simp⟩
    · push_cast; rw [abs_mul, abs_two]; linarith
    · push_cast; rw [← mul_sub, abs_mul, abs_two]
  | succ k ih =>
    intro x y hx hy
    obtain ⟨hA0x, hA1x, hC0, hC1, hK⟩ := ih x y hx hy
    obtain ⟨-, hA1y, -, -, -⟩ := ih y y hy hy
    simp only [hermAC]
    set H0x := (hermiteH k).eval x
    set H0y := (hermiteH k).eval y
    set H1x := (hermiteH (k + 1)).eval x
    set H1y := (hermiteH (k + 1)).eval y
    set a0 := ((hermAC R k).1 : ℝ)
    set a1 := ((hermAC R k).2.1 : ℝ)
    set c0 := ((hermAC R k).2.2.1 : ℝ)
    set c1 := ((hermAC R k).2.2.2.1 : ℝ)
    have hxy : 0 ≤ |x - y| := abs_nonneg _
    have hk : (0 : ℝ) ≤ k + 1 := by positivity
    have e2x : (hermiteH (k + 1 + 1)).eval x = 2 * x * H1x - 2 * (k + 1) * H0x :=
      eval_hermiteH_succ_succ k x
    have e2y : (hermiteH (k + 1 + 1)).eval y = 2 * y * H1y - 2 * (k + 1) * H0y :=
      eval_hermiteH_succ_succ k y
    refine ⟨hA1x, ?_, hC1, ?_, ?_⟩
    · rw [e2x]
      push_cast
      calc |2 * x * H1x - 2 * (k + 1) * H0x| ≤ |2 * x * H1x| + |2 * (k + 1) * H0x| := abs_sub _ _
        _ = 2 * |x| * |H1x| + 2 * (k + 1) * |H0x| := by
          simp only [abs_mul, abs_two, abs_of_nonneg hk]
        _ ≤ 2 * R * a1 + 2 * (k + 1) * a0 := by gcongr
    · rw [e2x, e2y]
      push_cast
      calc |2 * x * H1x - 2 * (k + 1) * H0x - (2 * y * H1y - 2 * (k + 1) * H0y)|
          = |2 * x * (H1x - H1y) + 2 * (x - y) * H1y - 2 * (k + 1) * (H0x - H0y)| := by
            congr 1; ring
        _ ≤ |2 * x * (H1x - H1y)| + |2 * (x - y) * H1y| + |2 * (k + 1) * (H0x - H0y)| :=
            (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ = 2 * |x| * |H1x - H1y| + 2 * |x - y| * |H1y| + 2 * (k + 1) * |H0x - H0y| := by
            simp only [abs_mul, abs_two, abs_of_nonneg hk]
        _ ≤ 2 * R * (c1 * |x - y|) + 2 * |x - y| * a1 + 2 * (k + 1) * (c0 * |x - y|) := by
            gcongr
        _ = _ := by ring
    · have hG : (2 : ℝ) ^ (k + 1) * (k + 1).factorial * (hermG (k + 1) x - hermG (k + 1) y) =
          2 * (k + 1) * (2 ^ k * k.factorial * (hermG k x - hermG k y)) +
            (H1x - H1y) * (H1x + H1y) := by
        rw [hermG_succ, hermG_succ, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      have hF : (0 : ℝ) < 2 ^ (k + 1) * (k + 1).factorial := by positivity
      have hS : |H1x + H1y| ≤ 2 * a1 := by
        have := abs_add_le H1x H1y; linarith
      push_cast
      calc 2 ^ (k + 1) * ((k + 1).factorial : ℝ) * |hermG (k + 1) x - hermG (k + 1) y|
          = |2 * (k + 1) * (2 ^ k * k.factorial * (hermG k x - hermG k y)) +
              (H1x - H1y) * (H1x + H1y)| := by
            rw [← hG, abs_mul, abs_of_pos hF]
        _ ≤ 2 * (k + 1) * (2 ^ k * k.factorial * |hermG k x - hermG k y|) +
              |H1x - H1y| * |H1x + H1y| := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            simp only [abs_mul, abs_two, abs_of_nonneg hk, abs_pow, Nat.abs_cast]
        _ ≤ 2 * (k + 1) * ((hermAC R k).2.2.2.2 * |x - y|) + c1 * |x - y| * (2 * a1) := by
            gcongr
        _ = _ := by ring

/-! ### A bracket for `π` -/

/-- Rational bounds `L = L₁/L₂ ≤ π ≤ U₁/U₂` (the 128-bit AzFloat enclosure). -/
def hermPiL : ℕ × ℕ :=
  (66814286504060421741230023322616923953, 21267647932558653966460912964485513216)
def hermPiU : ℕ × ℕ :=
  (8351785813007552717653752915327115495, 2658455991569831745807614120560689152)

open Azurite.AzFloat in
set_option maxRecDepth 100000 in
theorem herm_pi_bounds :
    (hermPiL.1 : ℝ) / hermPiL.2 ≤ π ∧ π ≤ (hermPiU.1 : ℝ) / hermPiU.2 := by
  have h := (enclosesPos_pi (w := 128) (by norm_num)).encloses0.encloses
  obtain ⟨l, u⟩ := h.bounds (s₁ := true) (n₁ := hermPiL.1) (d₁ := hermPiL.2) (s₂ := true)
    (n₂ := hermPiU.1) (d₂ := hermPiU.2) (by decide +kernel) (by decide +kernel)
  simp only [signedVal, ↓reduceIte] at l u
  exact ⟨l, u⟩

/-! ### Certified weights -/

theorem herm_abs_le_half_ulp {x X : ℝ} {d : ℕ} (h1 : (10 * X - 5) / 10 ^ (d + 1) ≤ x)
    (h2 : x ≤ (10 * X + 5) / 10 ^ (d + 1)) : |x - X / 10 ^ d| ≤ 5 / 10 ^ (d + 1) := by
  have e1 : (10 * X - 5) / 10 ^ (d + 1) = X / 10 ^ d - 5 / 10 ^ (d + 1) := by
    rw [pow_succ]; field_simp
  have e2 : (10 * X + 5) / 10 ^ (d + 1) = X / 10 ^ d + 5 / 10 ^ (d + 1) := by
    rw [pow_succ]; field_simp
  rw [abs_le]; constructor <;> linarith

/-- The exact check of a printed weight `W/10^{sw}` of `√π/g`, given `Den·g ∈ [H − E, H + E]`. -/
def hermWOK (W sw : ℕ) (H E Den : ℤ) : Bool :=
  decide (0 < W) && decide (0 < H - E) &&
    decide ((10 * (W : ℤ) - 5) ^ 2 * (H + E) ^ 2 * hermPiL.2 ≤
      (10 ^ (sw + 1) * Den) ^ 2 * hermPiL.1) &&
    decide ((10 ^ (sw + 1) * Den) ^ 2 * hermPiU.1 ≤
      (10 * (W : ℤ) + 5) ^ 2 * (H - E) ^ 2 * hermPiU.2)

theorem hermWOK_sound {W sw : ℕ} {H E Den : ℤ} {g : ℝ} (hDen : 0 < Den)
    (h : hermWOK W sw H E Den = true) (hlo : (H : ℝ) - E ≤ Den * g) (hhi : Den * g ≤ H + E) :
    0 < g ∧ |√π / g - W / 10 ^ sw| ≤ 5 / 10 ^ (sw + 1) := by
  simp only [hermWOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hW0, hHE⟩, h1⟩, h2⟩ := h
  have hD : (0 : ℝ) < Den := by exact_mod_cast hDen
  have hHEr : (0 : ℝ) < H - E := by exact_mod_cast hHE
  have hg : 0 < g := by
    by_contra hneg; push Not at hneg
    nlinarith
  refine ⟨hg, ?_⟩
  have h10 : (0 : ℝ) < 10 ^ (sw + 1) := by positivity
  set T : ℝ := 10 ^ (sw + 1) * Den
  have hT : 0 < T := mul_pos h10 hD
  have hW5 : (0 : ℝ) ≤ 10 * (W : ℝ) - 5 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW0
    linarith
  obtain ⟨hpl, hpu⟩ := herm_pi_bounds
  have hL2 : (0 : ℝ) < hermPiL.2 := by norm_num [hermPiL]
  have hU2 : (0 : ℝ) < hermPiU.2 := by norm_num [hermPiU]
  have r1 : (10 * (W : ℝ) - 5) ^ 2 * (H + E) ^ 2 * hermPiL.2 ≤ T ^ 2 * hermPiL.1 := by
    simp only [T]; exact_mod_cast h1
  have r2 : T ^ 2 * hermPiU.1 ≤ (10 * (W : ℝ) + 5) ^ 2 * (H - E) ^ 2 * hermPiU.2 := by
    simp only [T]; exact_mod_cast h2
  apply herm_abs_le_half_ulp
  · -- `lo ≤ √π/g`
    rw [le_div_iff₀ hg]
    have hlg : (10 * (W : ℝ) - 5) / 10 ^ (sw + 1) * g ≤ (10 * W - 5) * (H + E) / T := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ h10 hT]
      simp only [T]
      have := mul_le_mul_of_nonneg_left hhi hW5
      nlinarith
    have hsq : ((10 * (W : ℝ) - 5) * (H + E) / T) ^ 2 ≤ π := by
      refine le_trans ?_ hpl
      rw [div_pow, div_le_div_iff₀ (pow_pos hT 2) hL2]
      linarith
    refine hlg.trans ?_
    have hHE' : (0 : ℝ) < H + E := by nlinarith [mul_pos hD hg]
    rw [le_sqrt (div_nonneg (mul_nonneg hW5 hHE'.le) hT.le) pi_pos.le]
    exact hsq
  · -- `√π/g ≤ hi`
    rw [div_le_iff₀ hg]
    have hhg : (10 * W + 5) * (H - E) / T ≤ (10 * (W : ℝ) + 5) / 10 ^ (sw + 1) * g := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hT h10]
      simp only [T]
      have := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ 10 * W + 5)
      nlinarith
    have hsq : π ≤ ((10 * W + 5) * (H - E) / T) ^ 2 := by
      refine hpu.trans ?_
      rw [div_pow, div_le_div_iff₀ hU2 (pow_pos hT 2)]
      linarith
    refine le_trans ?_ hhg
    rw [sqrt_le_left (div_nonneg (mul_nonneg (by positivity) hHEr.le) hT.le)]
    exact hsq

/-! ### Certified rows -/

/-- A positive row: the bracket `(a/D, (a + 1)/D)` of a node, the printed node `X/10^{sx}` and
the printed weight `W/10^{sw}`. -/
structure HermRow where
  a : ℕ
  X : ℕ
  sx : ℕ
  W : ℕ
  sw : ℕ

/-- `2^{n−1} (n−1)! D^{2(n−1)}` and the Lipschitz error `K D^{2n−3}` over a bracket. -/
def hermDen (n D : ℕ) : ℤ := 2 ^ (n - 1) * ((n - 1).factorial : ℤ) * (D : ℤ) ^ (2 * (n - 1))
def hermE (n D R : ℕ) : ℤ := ((hermAC R (n - 1)).2.2.2.2 : ℤ) * (D : ℤ) ^ (2 * n - 3)

/-- The exact checks for one row: a sign change of `H_n` across the bracket, the bracket inside
the rounding interval of the printed node, and the weight `√π/∑_{j<n} H_j²/(2^j j!)` inside that
of the printed weight. -/
def hermRowOK (n D R : ℕ) (r : HermRow) : Bool :=
  decide (0 < r.a) && decide (r.a + 1 ≤ R * D) &&
    decide ((hermRH r.a D (n - 1)).2.1 * (hermRH (r.a + 1) D (n - 1)).2.1 < 0) &&
    decide ((10 * (r.X : ℤ) - 5) * D ≤ r.a * 10 ^ (r.sx + 1)) &&
    decide (((r.a : ℤ) + 1) * 10 ^ (r.sx + 1) ≤ (10 * r.X + 5) * D) &&
    hermWOK r.W r.sw (hermRH r.a D (n - 1)).2.2 (hermE n D R) (hermDen n D)

theorem hermRowOK_sound {n D R : ℕ} (hn : 2 ≤ n) {r : HermRow} (h : hermRowOK n D R r = true) :
    ∃ x : ℝ, (r.a : ℝ) / D < x ∧ x < ((r.a : ℝ) + 1) / D ∧ (hermiteH n).eval x = 0 ∧
      |x - r.X / 10 ^ r.sx| ≤ 5 / 10 ^ (r.sx + 1) ∧
      |√π / hermG (n - 1) x - r.W / 10 ^ r.sw| ≤ 5 / 10 ^ (r.sw + 1) := by
  simp only [hermRowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨ha0, hbR⟩, hsgn⟩, hX1⟩, hX2⟩, hW⟩ := h
  have hD0 : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · rw [h0, mul_zero] at hbR; omega
    · exact h0
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD0
  have hn1 : n - 1 + 1 = n := by omega
  set l : ℝ := (r.a : ℝ) / D
  set u : ℝ := ((r.a : ℝ) + 1) / D
  have hl0 : 0 < l := div_pos (by exact_mod_cast ha0) hDr
  have hlu : l < u := div_lt_div_of_pos_right (by linarith) hDr
  have huR : u ≤ R := by
    rw [div_le_iff₀ hDr]; exact_mod_cast hbR
  have hlD : ((r.a : ℤ) : ℝ) = l * ((D : ℤ) : ℝ) := by simp only [l]; push_cast; field_simp
  have huD : (((r.a : ℤ) + 1 : ℤ) : ℝ) = u * ((D : ℤ) : ℝ) := by
    simp only [u]; push_cast; field_simp
  obtain ⟨-, hRa, hHa⟩ := hermRH_spec _ _ _ hlD (n - 1)
  obtain ⟨-, hRb, -⟩ := hermRH_spec _ _ _ huD (n - 1)
  simp only [Int.cast_natCast] at hRa hRb hHa
  rw [hn1] at hRa hRb
  -- a zero in `(l, u)`
  have hsgnR : (hermiteH n).eval l * (hermiteH n).eval u < 0 := by
    have : ((hermRH r.a D (n - 1)).2.1 : ℝ) * (hermRH (r.a + 1) D (n - 1)).2.1 < 0 := by
      exact_mod_cast hsgn
    rw [hRa, hRb] at this
    have e : (D : ℝ) ^ n * (hermiteH n).eval l * ((D : ℝ) ^ n * (hermiteH n).eval u) =
        ((D : ℝ) ^ n) ^ 2 * ((hermiteH n).eval l * (hermiteH n).eval u) := by ring
    rw [e] at this
    exact neg_of_mul_neg_right this (sq_nonneg _)
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ Ioo l u, (hermiteH n).eval x = 0 := by
    have hc : ContinuousOn (fun t => (hermiteH n).eval t) (Icc l u) :=
      (hermiteH n).continuous.continuousOn
    rcases mul_neg_iff.mp hsgnR with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hlu.le hc ⟨h2, h1⟩
      exact ⟨x, hx, hx0⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hlu.le hc ⟨h1, h2⟩
      exact ⟨x, hx, hx0⟩
  refine ⟨x, hx.1, hx.2, hx0, ?_, ?_⟩
  · -- the node
    have h10 : (0 : ℝ) < 10 ^ (r.sx + 1) := by positivity
    apply herm_abs_le_half_ulp
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
    set F : ℝ := 2 ^ (n - 1) * ((n - 1).factorial : ℝ)
    set Kh : ℝ := ((hermAC R (n - 1)).2.2.2.2 : ℝ)
    have hDE : (D : ℝ) ^ (2 * n - 3) * D = (D : ℝ) ^ (2 * (n - 1)) := by
      rw [← pow_succ]; congr 1; omega
    have hxl : |x - l| ≤ 1 / D := by
      rw [abs_of_pos (by linarith [hx.1]), show (1 : ℝ) / D = u - l by simp only [u, l]; ring]
      linarith [hx.2]
    have hxR : |x| ≤ R := by rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.2]
    have hlR : |l| ≤ R := by rw [abs_of_pos hl0]; linarith
    have hLip := (hermAC_spec R (n - 1) x l hxR hlR).2.2.2.2
    have hDen : ((hermDen n D : ℤ) : ℝ) = F * (D : ℝ) ^ (2 * (n - 1)) := by
      simp only [hermDen, F]; push_cast; ring
    have hE : ((hermE n D R : ℤ) : ℝ) = Kh * (D : ℝ) ^ (2 * n - 3) := by
      simp only [hermE, Kh]; push_cast; ring
    have hGl : ((hermRH r.a D (n - 1)).2.2 : ℝ) = (hermDen n D : ℝ) * hermG (n - 1) l := by
      rw [hHa, hDen]
    have hdiff : (hermDen n D : ℝ) * |hermG (n - 1) x - hermG (n - 1) l| ≤ hermE n D R := by
      have hKh : 0 ≤ Kh := by positivity
      rw [hDen, hE]
      calc F * (D : ℝ) ^ (2 * (n - 1)) * |hermG (n - 1) x - hermG (n - 1) l| =
          (D : ℝ) ^ (2 * (n - 1)) * (F * |hermG (n - 1) x - hermG (n - 1) l|) := by ring
        _ ≤ (D : ℝ) ^ (2 * (n - 1)) * (Kh * (1 / D)) :=
          mul_le_mul_of_nonneg_left (hLip.trans (mul_le_mul_of_nonneg_left hxl hKh))
            (by positivity)
        _ = _ := by rw [← hDE]; field_simp
    have hDpos : 0 < hermDen n D := by unfold hermDen; positivity
    refine (hermWOK_sound hDpos hW ?_ ?_).2
    · have hD' : (0 : ℝ) ≤ hermDen n D := by exact_mod_cast hDpos.le
      have := mul_le_mul_of_nonneg_left (neg_abs_le (hermG (n - 1) x - hermG (n - 1) l)) hD'
      rw [hGl]; nlinarith
    · have hD' : (0 : ℝ) ≤ hermDen n D := by exact_mod_cast hDpos.le
      have := mul_le_mul_of_nonneg_left (le_abs_self (hermG (n - 1) x - hermG (n - 1) l)) hD'
      rw [hGl]; nlinarith

/-! ### Nodes and weights of the Gauss–Hermite rule -/

/-- The nodes of the `n`-point Gauss–Hermite rule: the zeros of `p_n`. -/
noncomputable def hermNodes (n : ℕ) : Finset ℝ := (hermMonic n).roots.toFinset

/-- The weights (Christoffel numbers 3.5.18) of the `n`-point Gauss–Hermite rule. -/
noncomputable def hermWeight (n : ℕ) (x : ℝ) : ℝ := christoffel univ hermW (hermMonic n) x

theorem mem_hermNodes_iff (n : ℕ) (x : ℝ) : x ∈ hermNodes n ↔ (hermiteH n).eval x = 0 := by
  rw [hermNodes, Multiset.mem_toFinset, mem_roots (hermMonic_spec n).1.ne_zero, IsRoot.def,
    ← hermMonic_eq, eval_mul, eval_C, mul_eq_zero, or_iff_right (by positivity)]

theorem card_hermNodes (n : ℕ) : #(hermNodes n) = n := by
  obtain ⟨hnodup, hcard, -⟩ := (isOrthMonic_hermMonic n).roots_spec isGaussWeight_hermW
  rw [hermNodes, Multiset.toFinset_card_of_nodup hnodup, hcard]

theorem hermWeight_eq {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ hermNodes n) :
    hermWeight n x = √π / hermG (n - 1) x := by
  rw [hermWeight, christoffel_hermite n hx, hermG, show n - 1 + 1 = n by omega]

theorem neg_mem_hermNodes {n : ℕ} {x : ℝ} (hx : x ∈ hermNodes n) : -x ∈ hermNodes n := by
  rw [mem_hermNodes_iff] at hx ⊢
  rw [eval_neg_hermiteH, hx, mul_zero]

theorem hermG_neg (k : ℕ) (x : ℝ) : hermG k (-x) = hermG k x := by
  simp only [hermG, eval_neg_hermiteH]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
  norm_num

/-- The weights are symmetric: `w(−x) = w(x)`. -/
theorem hermWeight_neg {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ hermNodes n) :
    hermWeight n (-x) = hermWeight n x := by
  rw [hermWeight_eq hn (neg_mem_hermNodes hx), hermWeight_eq hn hx, hermG_neg]

/-- The node `0` of an odd rule: the exact check of its printed weight `W/10^{sw}`. -/
def hermZeroOK (n W sw : ℕ) : Bool :=
  decide (n % 2 = 1) && hermWOK W sw (hermRH 0 1 (n - 1)).2.2 0 (hermDen n 1)

theorem hermZeroOK_sound {n W sw : ℕ} (h : hermZeroOK n W sw = true) :
    (0 : ℝ) ∈ hermNodes n ∧ |hermWeight n 0 - W / 10 ^ sw| ≤ 5 / 10 ^ (sw + 1) := by
  simp only [hermZeroOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hodd, hW⟩ := h
  have h0 : (0 : ℝ) ∈ hermNodes n := by
    rw [mem_hermNodes_iff]
    have := eval_neg_hermiteH n 0
    rw [neg_zero, Odd.neg_one_pow (Nat.odd_iff.mpr hodd)] at this
    linarith
  refine ⟨h0, ?_⟩
  rw [hermWeight_eq (by omega) h0]
  obtain ⟨-, -, hH⟩ := hermRH_spec 0 1 0 (by simp) (n - 1)
  have hDen : ((hermDen n 1 : ℤ) : ℝ) = 2 ^ (n - 1) * ((n - 1).factorial : ℝ) := by
    simp [hermDen]
  have hGl : ((hermRH 0 1 (n - 1)).2.2 : ℝ) = (hermDen n 1 : ℝ) * hermG (n - 1) 0 := by
    rw [hH, hDen]; simp
  have hDpos : 0 < hermDen n 1 := by unfold hermDen; positivity
  refine (hermWOK_sound hDpos hW ?_ ?_).2 <;> simp [hGl]

/-! ### Tables -/

/-- A Gauss–Hermite table `(X, sx, W, sw)` of printed nodes `X/10^{sx}` and weights `W/10^{sw}`
(nonnegative nodes, the negative ones by symmetry) is correctly rounded and complete: every row
is within half a unit of a node and its weight, and every node `±x` is a row. -/
def HermTableSpec (n : ℕ) (tab : List (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  (∀ p ∈ tab, ∃ x ∈ hermNodes n, 0 ≤ x ∧ |x - p.1 / 10 ^ p.2.1| ≤ 5 / 10 ^ (p.2.1 + 1) ∧
      |hermWeight n x - p.2.2.1 / 10 ^ p.2.2.2| ≤ 5 / 10 ^ (p.2.2.2 + 1)) ∧
  ∀ x ∈ hermNodes n, ∃ p ∈ tab, |abs x - p.1 / 10 ^ p.2.1| ≤ 5 / 10 ^ (p.2.1 + 1)

/-- The exact checks for a whole table: every row, disjoint ordered brackets, the right count, and
the zero node `(sx, W, sw)` for odd `n`. -/
def hermTableOK (n D R : ℕ) (zero : Option (ℕ × ℕ × ℕ)) (rows : List HermRow) : Bool :=
  decide (2 ≤ n) && rows.all (hermRowOK n D R) &&
    decide (rows.Pairwise fun r s => r.a + 1 ≤ s.a) &&
    decide (2 * rows.length + (if zero.isSome then 1 else 0) = n) &&
    (match zero with
      | none => true
      | some z => hermZeroOK n z.2.1 z.2.2)

/-- The printed table of a checked table. -/
def hermTab (zero : Option (ℕ × ℕ × ℕ)) (rows : List HermRow) : List (ℕ × ℕ × ℕ × ℕ) :=
  (zero.map fun z => (0, z)).toList ++ rows.map fun r => (r.X, r.sx, r.W, r.sw)

theorem hermTableOK_sound {n D R : ℕ} {zero : Option (ℕ × ℕ × ℕ)} {rows : List HermRow}
    (h : hermTableOK n D R zero rows = true) : HermTableSpec n (hermTab zero rows) := by
  classical
  simp only [hermTableOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hn, hrows⟩, hpw⟩, hcount⟩, hzero⟩ := h
  have hn1 : 1 ≤ n := by omega
  -- the certified positive nodes
  have hrow : ∀ i : Fin rows.length, ∃ x : ℝ, (rows[i].a : ℝ) / D < x ∧
      x < ((rows[i].a : ℝ) + 1) / D ∧ x ∈ hermNodes n ∧
      |x - rows[i].X / 10 ^ rows[i].sx| ≤ 5 / 10 ^ (rows[i].sx + 1) ∧
      |hermWeight n x - rows[i].W / 10 ^ rows[i].sw| ≤ 5 / 10 ^ (rows[i].sw + 1) ∧ 0 < x :=
    fun i => by
    have hok := hrows rows[i] (List.getElem_mem _)
    obtain ⟨x, hl, hu, hx0, hX, hW⟩ := hermRowOK_sound hn hok
    have hmem : x ∈ hermNodes n := (mem_hermNodes_iff n x).mpr hx0
    have ha : 0 < rows[i].a := by
      simp only [hermRowOK, Bool.and_eq_true, decide_eq_true_eq] at hok; omega
    refine ⟨x, hl, hu, hmem, hX, by rwa [hermWeight_eq hn1 hmem], ?_⟩
    refine lt_of_le_of_lt (div_nonneg (by positivity) (by positivity)) hl
  choose xs hxl hxu hxmem hxX hxW hxpos using hrow
  -- strictly increasing
  have hmono : StrictMono xs := by
    intro i j hij
    have hb : rows[i].a + 1 ≤ rows[j].a := List.pairwise_iff_getElem.mp hpw i j i.2 j.2 hij
    have hD : (0 : ℝ) ≤ D := by positivity
    have : ((rows[i].a : ℝ) + 1) / D ≤ (rows[j].a : ℝ) / D :=
      div_le_div_of_nonneg_right (by exact_mod_cast hb) hD
    linarith [hxu i, hxl j]
  refine ⟨?_, ?_⟩
  · -- every row is a node
    intro p hp
    simp only [hermTab, List.mem_append, Option.mem_toList, Option.map_eq_some_iff,
      List.mem_map] at hp
    rcases hp with ⟨z, hz, rfl⟩ | ⟨r, hr, rfl⟩
    · subst hz
      obtain ⟨h0, hw⟩ := hermZeroOK_sound hzero
      exact ⟨0, h0, le_rfl, by simp; positivity, hw⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      exact ⟨xs ⟨i, hi⟩, hxmem _, (hxpos _).le, hxX _, hxW _⟩
  · -- every node is a row
    set Spos : Finset ℝ := univ.image xs
    set Sneg : Finset ℝ := Spos.image (fun t => -t)
    set Z : Finset ℝ := if zero.isSome then {0} else ∅
    have hsub : Spos ∪ Sneg ∪ Z ⊆ hermNodes n := by
      intro t ht
      simp only [Spos, Sneg, Z, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and] at ht
      rcases ht with (⟨i, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩) | hz
      · exact hxmem i
      · exact neg_mem_hermNodes (hxmem i)
      · cases hzz : zero with
        | none => simp [hzz] at hz
        | some z =>
          simp [hzz] at hz; subst hz
          rw [hzz] at hzero
          exact (hermZeroOK_sound hzero).1
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
        simp only [Spos, Sneg, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
          true_and] at ht
        rcases ht with ⟨i, hi⟩ | ⟨_, ⟨j, rfl⟩, hj⟩
        · linarith [hxpos i]
        · linarith [hxpos j]
      · simp at htz
    have hcard : #(Spos ∪ Sneg ∪ Z) = n := by
      rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1, hcpos,
        hcneg]
      simp only [Z]
      split_ifs <;> simp_all <;> omega
    have heq : Spos ∪ Sneg ∪ Z = hermNodes n :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_hermNodes, hcard])
    intro t ht
    rw [← heq] at ht
    simp only [Spos, Sneg, Z, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at ht
    rcases ht with (⟨i, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩) | hz
    · refine ⟨(rows[i].X, rows[i].sx, rows[i].W, rows[i].sw), ?_,
        by rw [abs_of_pos (hxpos i)]; exact hxX i⟩
      simp only [hermTab, List.mem_append, List.mem_map]
      exact Or.inr ⟨rows[i], List.getElem_mem _, rfl⟩
    · refine ⟨(rows[i].X, rows[i].sx, rows[i].W, rows[i].sw), ?_,
        by rw [abs_neg, abs_of_pos (hxpos i)]; exact hxX i⟩
      simp only [hermTab, List.mem_append, List.mem_map]
      exact Or.inr ⟨rows[i], List.getElem_mem _, rfl⟩
    · cases hzz : zero with
      | none => simp [hzz] at hz
      | some z =>
        simp [hzz] at hz; subst hz
        refine ⟨(0, z), ?_, by
          rw [abs_zero, Nat.cast_zero, zero_div, sub_zero, abs_zero]; positivity⟩
        simp [hermTab]

/-! ### The certificates (`D = 10^100`; brackets `(a/D, (a+1)/D)`) -/

/-- A bracket numerator `hi · 10^50 + lo`, split for line length. -/
def hermN (hi lo : ℕ) : ℕ := hi * 10 ^ 50 + lo

/-- The brackets and printed values of Table 3.5.10. -/
def hermRows_3_5_10 : List HermRow := [
  ⟨hermN
    95857246461381850711277059389298831818608885525818
    85315861435073024960334291329430216049978274590246,
    958572464613819, 15, 393619323152241, 15⟩,
  ⟨hermN
    202018287045608563292872408814464514705223214746504
    73926832631624059913801840332042107317658799264761,
    202018287045609, 14, 199532420590459, 16⟩]

set_option maxRecDepth 100000 in
theorem hermTableOK_3_5_10 :
    hermTableOK 5 (10 ^ 100) 3 (some (15, 945308720482942, 15)) hermRows_3_5_10 = true := by
  decide +kernel

/-- **Table 3.5.10** (5-point Gauss–Hermite formula): every node `±x_k` and weight `w_k` is
correctly rounded as printed, and the table is complete. -/
theorem dlmf_table_3_5_10 : HermTableSpec 5 [
    (0, 15, 945308720482942, 15),
    (958572464613819, 15, 393619323152241, 15),
    (202018287045609, 14, 199532420590459, 16)] :=
  hermTableOK_sound hermTableOK_3_5_10

/-- The brackets and printed values of Table 3.5.11. -/
def hermRows_3_5_11 : List HermRow := [
  ⟨hermN
    34290132722370460878916502555725803120830265867773
    6282057710390729201819231210156071352030544324806,
    342901327223704609, 18, 610862633735325799, 18⟩,
  ⟨hermN
    103661082978951365417749191675920901629825611065721
    57244372326874036404187243878992980306028243900733,
    103661082978951365, 17, 240138611082314686, 18⟩,
  ⟨hermN
    175668364929988177345140122010615676329547449373884
    71000872849560961705796098190771278266711469838314,
    175668364929988177, 17, 338743944554810631, 19⟩,
  ⟨hermN
    253273167423278979640896079775479348030784650815672
    49459332874134930859380473865340227292325941771646,
    253273167423278980, 17, 134364574678123269, 20⟩,
  ⟨hermN
    343615911883773760332672549431912138484067830939017
    72906871762944002361145649511153468627231618843292,
    343615911883773760, 17, 764043285523262063, 23⟩]

set_option maxRecDepth 100000 in
theorem hermTableOK_3_5_11 :
    hermTableOK 10 (10 ^ 100) 4 none hermRows_3_5_11 = true := by
  decide +kernel

/-- **Table 3.5.11** (10-point Gauss–Hermite formula): every node `±x_k` and weight `w_k` is
correctly rounded as printed, and the table is complete. -/
theorem dlmf_table_3_5_11 : HermTableSpec 10 [
    (342901327223704609, 18, 610862633735325799, 18),
    (103661082978951365, 17, 240138611082314686, 18),
    (175668364929988177, 17, 338743944554810631, 19),
    (253273167423278980, 17, 134364574678123269, 20),
    (343615911883773760, 17, 764043285523262063, 23)] :=
  hermTableOK_sound hermTableOK_3_5_11

/-- The brackets and printed values of Table 3.5.12. -/
def hermRows_3_5_12 : List HermRow := [
  ⟨hermN
    56506958325557574852602033719818886681552078800505
    78868093073968274505847091537515997352628303461029,
    565069583255575748526, 21, 412028687498898627026, 21⟩,
  ⟨hermN
    113611558521092066631913490555610212528352929478466
    50850648392599800715967101004409631966601830482707,
    113611558521092066632, 20, 158488915795935746884, 21⟩,
  ⟨hermN
    171999257518648893241583152515256151484291956306138
    88498938216300095132434761832428439718888176122448,
    171999257518648893242, 20, 307800338725460822287, 22⟩,
  ⟨hermN
    232573248617385774545404479448534701230709500956348
    28957721625948740238048583608727061841554643103134,
    232573248617385774545, 20, 277806884291277589608, 23⟩,
  ⟨hermN
    296716692790560324848896036354980631557051640763813
    81507212727522118956916046294049934561649283587290,
    296716692790560324849, 20, 100004441232499868127, 24⟩,
  ⟨hermN
    366995037340445253472922383311568148469585562601082
    68200827250197712929612325341525137596165272567610,
    366995037340445253473, 20, 105911554771106663578, 26⟩,
  ⟨hermN
    449999070730939155366438053053482421993198305349499
    5938271742846019366228525630586264389556919589962,
    449999070730939155366, 20, 152247580425351702016, 29⟩]

set_option maxRecDepth 100000 in
theorem hermTableOK_3_5_12 :
    hermTableOK 15 (10 ^ 100) 5 (some (21, 564100308726417532853, 21)) hermRows_3_5_12 = true := by
  decide +kernel

/-- **Table 3.5.12** (15-point Gauss–Hermite formula): every node `±x_k` and weight `w_k` is
correctly rounded as printed, and the table is complete. -/
theorem dlmf_table_3_5_12 : HermTableSpec 15 [
    (0, 21, 564100308726417532853, 21),
    (565069583255575748526, 21, 412028687498898627026, 21),
    (113611558521092066632, 20, 158488915795935746884, 21),
    (171999257518648893242, 20, 307800338725460822287, 22),
    (232573248617385774545, 20, 277806884291277589608, 23),
    (296716692790560324849, 20, 100004441232499868127, 24),
    (366995037340445253473, 20, 105911554771106663578, 26),
    (449999070730939155366, 20, 152247580425351702016, 29)] :=
  hermTableOK_sound hermTableOK_3_5_12

/-- The brackets and printed values of Table 3.5.13. -/
def hermRows_3_5_13 : List HermRow := [
  ⟨hermN
    24534070830090124990383653063361662396613385130348
    57348785924037753487947015036755489007014871859258,
    245340708300901249904, 21, 462243669600610089650, 21⟩,
  ⟨hermN
    73747372854539435870560514425210422907721620397679
    41872968422099956257623371318234537355646571045775,
    737473728545394358706, 21, 286675505362834129720, 21⟩,
  ⟨hermN
    123407621539532300788581834695941022958544593006936
    23871269654216903702823123912237174870060855460768,
    123407621539532300789, 20, 109017206020023320014, 21⟩,
  ⟨hermN
    173853771211658620678086566213640644295140941960039
    98944648185723824798213797395588350743881825308791,
    173853771211658620678, 20, 248105208874636108822, 22⟩,
  ⟨hermN
    225497400208927552308233334473456512808226531602639
    61513124221943516203923517835069476633657524932637,
    225497400208927552308, 20, 324377334223786183218, 23⟩,
  ⟨hermN
    278880605842813048052503375640318541067069888790204
    39739647127991676552374193715396129217956391740589,
    278880605842813048053, 20, 228338636016353967257, 24⟩,
  ⟨hermN
    334785456738321632691492452299646369851047859029367
    70565339899723093751567634666622504934099567462347,
    334785456738321632691, 20, 780255647853206369415, 26⟩,
  ⟨hermN
    394476404011562521037562880052441180714976812788831
    30206476623901177330863343239336184154950866089105,
    394476404011562521038, 20, 108606937076928169400, 27⟩,
  ⟨hermN
    460368244955074427307767524897834758511339848776192
    36535623309427977256632122875930744925681633503310,
    460368244955074427308, 20, 439934099227318055363, 30⟩,
  ⟨hermN
    538748089001123286201690041068112075399628644906591
    48897357653298097651440391233455464187010337610092,
    538748089001123286202, 20, 222939364553415129252, 33⟩]

set_option maxRecDepth 100000 in
theorem hermTableOK_3_5_13 :
    hermTableOK 20 (10 ^ 100) 6 none hermRows_3_5_13 = true := by
  decide +kernel

/-- **Table 3.5.13** (20-point Gauss–Hermite formula): every node `±x_k` and weight `w_k` is
correctly rounded as printed, and the table is complete. -/
theorem dlmf_table_3_5_13 : HermTableSpec 20 [
    (245340708300901249904, 21, 462243669600610089650, 21),
    (737473728545394358706, 21, 286675505362834129720, 21),
    (123407621539532300789, 20, 109017206020023320014, 21),
    (173853771211658620678, 20, 248105208874636108822, 22),
    (225497400208927552308, 20, 324377334223786183218, 23),
    (278880605842813048053, 20, 228338636016353967257, 24),
    (334785456738321632691, 20, 780255647853206369415, 26),
    (394476404011562521038, 20, 108606937076928169400, 27),
    (460368244955074427308, 20, 439934099227318055363, 30),
    (538748089001123286202, 20, 222939364553415129252, 33)] :=
  hermTableOK_sound hermTableOK_3_5_13

end Azurite.DLMF
