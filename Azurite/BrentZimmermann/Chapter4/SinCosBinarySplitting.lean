/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.ArctanBinarySplitting

/-!
# Brent–Zimmermann §4.9.1: A binary splitting algorithm for `sin`, `cos`

Algorithm 4.4 SinCos (a real variant of Brent's `O(M(n) log² n)` algorithm for `exp`, which
computed `sin x` from `exp(ix)`): for `0 < x < 1/2` write `x ≈ ∑_{i=0}^{k} p_i 2^(−2^(i+1))` with
`0 ≤ p_i < 2^(2^i)`, `k = ⌈lg n⌉ − 1`; put `x_j = ∑_{i=j}^{k} p_i 2^(−2^(i+1))` (so `x_{k+1} = 0`)
and `y_j = p_j 2^(−2^(j+1))`; start from `(S_{k+1}, C_{k+1}) = (0, 1)` and for `j = k, …, 0`
compute `sin y_j, cos y_j` by binary splitting and set
`S_j = sin y_j · C_{j+1} + cos y_j · S_{j+1}`, `C_j = cos y_j · C_{j+1} − sin y_j · S_{j+1}`;
return `(S₀, C₀)`.  Since `x_j = y_j + x_{j+1}`, `S_j = sin x_j` and `C_j = cos x_j` by the
addition formulae; `y_j` is a small rational, so all powers needed stay below `n` bits; the cost is
`O(M(n) log² n)`.

What is formalized (all proven):

* The block decomposition: `sinCosDigit x i = ⌊x 2^(2^(i+1))⌋ − 2^(2^i) ⌊x 2^(2^i)⌋` satisfies
  `0 ≤ p_i < 2^(2^i)` (`sinCosDigit_nonneg`, `sinCosDigit_lt`), and for `0 ≤ x < 1/2`
  `∑_{i≤k} p_i/2^(2^(i+1)) = ⌊x 2^(2^(k+1))⌋/2^(2^(k+1))` (`sum_sinCosDigit_div`), the truncation
  of `x` to `2^(k+1)` bits, with `0 ≤ x − ∑ < 2^(−2^(k+1)) ≤ 2^(−n)` once `n ≤ 2^(k+1)`
  (`sub_sum_sinCosDigit_bounds`, `sub_sum_sinCosDigit_lt_two_pow`).
* `tailSum y k j = ∑_{i=j}^{k} y_i` with `tailSum_eq_add : x_j = y_j + x_{j+1}` and
  `tailSum_top : x_{k+1} = 0`.
* Step 6 is multiplication by the rotation `cos y_j + i sin y_j`: with `sinCosProd c s k j =
  ∏_{i=j}^{k} (c_i + i s_i)` (so `C_j = ℜ`, `S_j = ℑ`), `sinCosProd_top` (`= 1`, i.e. `(S, C) =
  (0, 1)`), `sinCosProd_re`/`sinCosProd_im` (exactly the two formulae of step 6), and for exact
  inputs `sinCosProd_exact : ∏ (cos y_i + i sin y_i) = exp(i x_j)`, hence
  `sinCosProd_exact_im`/`_re` : `S_j = sin x_j`, `C_j = cos x_j`.
* Error propagation: `norm_prod_sub_prod_le` (`‖∏ a_i − ∏ b_i‖ ≤ m ε (1+ε)^m` for `‖b_i‖ = 1`,
  `‖a_i − b_i‖ ≤ ε`), hence `sinCos_error`: if every `sin y_i, cos y_i` is computed to within
  `ε`, then `|S₀ − sin x| ≤ 2(k+1) ε (1 + 2ε)^(k+1)` and likewise for `C₀` — the `O(2^(−n))`
  output error needs `ε = O(2^(−n)/lg n)`, i.e. `lg lg n` guard bits.
* `pow_lt_two_pow_of_digit`: `p^N < 2^(2^j N)` for `p < 2^(2^j)` — the powers in the binary
  splitting of `sin y_j` stay below `n` bits when `2^j N ≤ n`.

Not formalized: the `O(M(n) log² n)` cost accounting, Brent's Theorem 6.2, the use for `tan x`
and plane rotations (remarks); the algorithm itself (theory first).
-/

namespace Azurite

namespace BZ

open Finset Complex

variable {x : ℝ}

/-! ### The block decomposition of `x` -/

/-- `2^m ⌊y⌋ ≤ ⌊2^m y⌋ < 2^m (⌊y⌋ + 1)`. -/
theorem floor_mul_pow_bounds (y : ℝ) (m : ℕ) :
    2 ^ m * ⌊y⌋ ≤ ⌊(2 : ℝ) ^ m * y⌋ ∧ ⌊(2 : ℝ) ^ m * y⌋ < 2 ^ m * (⌊y⌋ + 1) := by
  constructor
  · rw [Int.le_floor]
    push_cast
    exact mul_le_mul_of_nonneg_left (Int.floor_le y) (by positivity)
  · rw [Int.floor_lt]
    push_cast
    exact mul_lt_mul_of_pos_left (Int.lt_floor_add_one y) (by positivity)

/-- The `i`-th block of bits of `x` (bits `2^i + 1, …, 2^(i+1)`):
`p_i = ⌊x 2^(2^(i+1))⌋ − 2^(2^i) ⌊x 2^(2^i)⌋`. -/
noncomputable def sinCosDigit (x : ℝ) (i : ℕ) : ℤ :=
  ⌊x * 2 ^ 2 ^ (i + 1)⌋ - 2 ^ 2 ^ i * ⌊x * 2 ^ 2 ^ i⌋

theorem two_pow_two_pow_succ (i : ℕ) : (2 : ℝ) ^ 2 ^ (i + 1) = 2 ^ 2 ^ i * 2 ^ 2 ^ i := by
  rw [← pow_add, pow_succ, mul_two]

theorem sinCosDigit_nonneg (x : ℝ) (i : ℕ) : 0 ≤ sinCosDigit x i := by
  unfold sinCosDigit
  have h := (floor_mul_pow_bounds (x * 2 ^ 2 ^ i) (2 ^ i)).1
  rw [show (2 : ℝ) ^ 2 ^ i * (x * 2 ^ 2 ^ i) = x * 2 ^ 2 ^ (i + 1) by
    rw [two_pow_two_pow_succ]; ring] at h
  linarith

theorem sinCosDigit_lt (x : ℝ) (i : ℕ) : sinCosDigit x i < 2 ^ 2 ^ i := by
  unfold sinCosDigit
  have h := (floor_mul_pow_bounds (x * 2 ^ 2 ^ i) (2 ^ i)).2
  rw [show (2 : ℝ) ^ 2 ^ i * (x * 2 ^ 2 ^ i) = x * 2 ^ 2 ^ (i + 1) by
    rw [two_pow_two_pow_succ]; ring] at h
  linarith

/-- The blocks reassemble the truncation of `x` to `2^(k+1)` bits (for `0 ≤ x < 1/2`). -/
theorem sum_sinCosDigit_div (hx0 : 0 ≤ x) (hx : x < 1 / 2) (k : ℕ) :
    ∑ i ∈ range (k + 1), (sinCosDigit x i : ℝ) / 2 ^ 2 ^ (i + 1)
      = (⌊x * 2 ^ 2 ^ (k + 1)⌋ : ℝ) / 2 ^ 2 ^ (k + 1) := by
  have hterm : ∀ i : ℕ, (sinCosDigit x i : ℝ) / 2 ^ 2 ^ (i + 1)
      = (⌊x * 2 ^ 2 ^ (i + 1)⌋ : ℝ) / 2 ^ 2 ^ (i + 1) - (⌊x * 2 ^ 2 ^ i⌋ : ℝ) / 2 ^ 2 ^ i := by
    intro i
    unfold sinCosDigit
    push_cast
    rw [two_pow_two_pow_succ]
    field_simp
  simp_rw [hterm]
  rw [sum_range_sub (fun i => (⌊x * 2 ^ 2 ^ i⌋ : ℝ) / 2 ^ 2 ^ i)]
  have h0 : ⌊x * 2⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by positivity, by linarith⟩
  simp [h0]

/-- `0 ≤ x − ∑_{i≤k} p_i/2^(2^(i+1)) < 2^(−2^(k+1))`. -/
theorem sub_sum_sinCosDigit_bounds (hx0 : 0 ≤ x) (hx : x < 1 / 2) (k : ℕ) :
    0 ≤ x - ∑ i ∈ range (k + 1), (sinCosDigit x i : ℝ) / 2 ^ 2 ^ (i + 1)
      ∧ x - ∑ i ∈ range (k + 1), (sinCosDigit x i : ℝ) / 2 ^ 2 ^ (i + 1)
        < 1 / 2 ^ 2 ^ (k + 1) := by
  rw [sum_sinCosDigit_div hx0 hx]
  have hM : (0 : ℝ) < 2 ^ 2 ^ (k + 1) := by positivity
  have h1 := Int.floor_le (x * 2 ^ 2 ^ (k + 1))
  have h2 := Int.lt_floor_add_one (x * 2 ^ 2 ^ (k + 1))
  constructor
  · rw [sub_nonneg, div_le_iff₀ hM]
    exact h1
  · rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hM]
    linarith

/-- With `n ≤ 2^(k+1)` (so `k = ⌈lg n⌉ − 1`), the truncation error is below `2^(−n)`. -/
theorem sub_sum_sinCosDigit_lt_two_pow (hx0 : 0 ≤ x) (hx : x < 1 / 2) {k n : ℕ}
    (hn : n ≤ 2 ^ (k + 1)) :
    x - ∑ i ∈ range (k + 1), (sinCosDigit x i : ℝ) / 2 ^ 2 ^ (i + 1) < (1 / 2) ^ n := by
  refine (sub_sum_sinCosDigit_bounds hx0 hx k).2.trans_le ?_
  rw [one_div, ← inv_pow, ← one_div]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn

/-! ### The partial angles `x_j = y_j + x_{j+1}` -/

/-- `x_j = ∑_{i=j}^{k} y_i`. -/
def tailSum (y : ℕ → ℝ) (k j : ℕ) : ℝ := ∑ i ∈ Ico j (k + 1), y i

theorem tailSum_top (y : ℕ → ℝ) (k : ℕ) : tailSum y k (k + 1) = 0 := by
  simp [tailSum]

theorem tailSum_eq_add (y : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    tailSum y k j = y j + tailSum y k (j + 1) := by
  unfold tailSum
  rw [sum_eq_sum_Ico_succ_bot (by omega)]

/-- Step 6 as the addition formulae. -/
theorem sin_cos_add_step (a b : ℝ) :
    Real.sin (a + b) = Real.sin a * Real.cos b + Real.cos a * Real.sin b
      ∧ Real.cos (a + b) = Real.cos a * Real.cos b - Real.sin a * Real.sin b :=
  ⟨Real.sin_add a b, Real.cos_add a b⟩

/-! ### The recurrence as a product of rotations -/

/-- The computed pair `(C_j, S_j)` as the complex number `C_j + i S_j = ∏_{i=j}^{k} (c_i + i s_i)`,
where `c_i, s_i` approximate `cos y_i, sin y_i`. -/
noncomputable def sinCosProd (c s : ℕ → ℝ) (k j : ℕ) : ℂ :=
  ∏ i ∈ Ico j (k + 1), ((c i : ℂ) + s i * I)

theorem sinCosProd_top (c s : ℕ → ℝ) (k : ℕ) : sinCosProd c s k (k + 1) = 1 := by
  simp [sinCosProd]

theorem sinCosProd_succ (c s : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    sinCosProd c s k j = ((c j : ℂ) + s j * I) * sinCosProd c s k (j + 1) := by
  unfold sinCosProd
  rw [prod_eq_prod_Ico_succ_bot (by omega)]

/-- Step 6, the cosine: `C_j = c_j C_{j+1} − s_j S_{j+1}`. -/
theorem sinCosProd_re (c s : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    (sinCosProd c s k j).re
      = c j * (sinCosProd c s k (j + 1)).re - s j * (sinCosProd c s k (j + 1)).im := by
  rw [sinCosProd_succ c s hj]
  simp

/-- Step 6, the sine: `S_j = s_j C_{j+1} + c_j S_{j+1}`. -/
theorem sinCosProd_im (c s : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    (sinCosProd c s k j).im
      = s j * (sinCosProd c s k (j + 1)).re + c j * (sinCosProd c s k (j + 1)).im := by
  rw [sinCosProd_succ c s hj]
  simp
  ring

/-- With exact `cos y_i, sin y_i`, the product is `exp(i x_j)`. -/
theorem sinCosProd_exact (y : ℕ → ℝ) (k j : ℕ) :
    sinCosProd (fun i => Real.cos (y i)) (fun i => Real.sin (y i)) k j
      = Complex.exp (tailSum y k j * I) := by
  unfold sinCosProd tailSum
  rw [Complex.ofReal_sum, sum_mul, Complex.exp_sum]
  exact prod_congr rfl fun i _ => (exp_mul_I_eq (y i)).symm

/-- The invariant `S_j = sin x_j`. -/
theorem sinCosProd_exact_im (y : ℕ → ℝ) (k j : ℕ) :
    (sinCosProd (fun i => Real.cos (y i)) (fun i => Real.sin (y i)) k j).im
      = Real.sin (tailSum y k j) := by
  rw [sinCosProd_exact, exp_ofReal_mul_I_im]

/-- The invariant `C_j = cos x_j`. -/
theorem sinCosProd_exact_re (y : ℕ → ℝ) (k j : ℕ) :
    (sinCosProd (fun i => Real.cos (y i)) (fun i => Real.sin (y i)) k j).re
      = Real.cos (tailSum y k j) := by
  rw [sinCosProd_exact, exp_ofReal_mul_I_re]

/-! ### Error propagation through the rotations -/

/-- Perturbing `m` unimodular factors by at most `ε` each perturbs the product by at most
`m ε (1 + ε)^m`. -/
theorem norm_prod_sub_prod_le {a b : ℕ → ℂ} {ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ i, ‖b i‖ = 1)
    (hab : ∀ i, ‖a i - b i‖ ≤ ε) (m : ℕ) :
    ‖∏ i ∈ range m, a i - ∏ i ∈ range m, b i‖ ≤ m * ε * (1 + ε) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ]
    have hbm : ‖∏ i ∈ range m, b i‖ = 1 := by
      rw [norm_prod]
      exact prod_eq_one fun i _ => hb i
    have ham : ‖a m‖ ≤ 1 + ε := by
      calc ‖a m‖ = ‖(a m - b m) + b m‖ := by ring_nf
        _ ≤ ‖a m - b m‖ + ‖b m‖ := norm_add_le _ _
        _ ≤ ε + 1 := by linarith [hab m, hb m]
        _ = 1 + ε := by ring
    have hsplit : (∏ i ∈ range m, a i) * a m - (∏ i ∈ range m, b i) * b m
        = (∏ i ∈ range m, a i - ∏ i ∈ range m, b i) * a m
          + (∏ i ∈ range m, b i) * (a m - b m) := by ring
    have hpow : (1 : ℝ) ≤ (1 + ε) ^ (m + 1) := one_le_pow₀ (by linarith)
    calc ‖(∏ i ∈ range m, a i) * a m - (∏ i ∈ range m, b i) * b m‖
        ≤ ‖∏ i ∈ range m, a i - ∏ i ∈ range m, b i‖ * ‖a m‖
          + ‖∏ i ∈ range m, b i‖ * ‖a m - b m‖ := by
          rw [hsplit]
          exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ m * ε * (1 + ε) ^ m * (1 + ε) + 1 * ε :=
          add_le_add (mul_le_mul ih ham (norm_nonneg _) (by positivity))
            (by rw [hbm, one_mul, one_mul]; exact hab m)
      _ = m * ε * (1 + ε) ^ (m + 1) + ε := by ring
      _ ≤ ((m + 1 : ℕ) : ℝ) * ε * (1 + ε) ^ (m + 1) := by
          push_cast
          nlinarith

/-- Algorithm SinCos with `sin y_i, cos y_i` computed to within `ε` returns `sin x`, `cos x` to
within `2(k+1) ε (1 + 2ε)^(k+1)`, `x = x₀ = ∑_{i≤k} y_i`. -/
theorem sinCos_error (y c s : ℕ → ℝ) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ i, |c i - Real.cos (y i)| ≤ ε) (hs : ∀ i, |s i - Real.sin (y i)| ≤ ε) :
    |(sinCosProd c s k 0).im - Real.sin (tailSum y k 0)|
        ≤ (k + 1) * (2 * ε) * (1 + 2 * ε) ^ (k + 1)
      ∧ |(sinCosProd c s k 0).re - Real.cos (tailSum y k 0)|
        ≤ (k + 1) * (2 * ε) * (1 + 2 * ε) ^ (k + 1) := by
  have hb : ∀ i, ‖Complex.exp (y i * I)‖ = 1 := fun i => norm_exp_ofReal_mul_I (y i)
  have hab : ∀ i, ‖((c i : ℂ) + s i * I) - Complex.exp (y i * I)‖ ≤ 2 * ε := by
    intro i
    rw [exp_mul_I_eq]
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    have hre : (((c i : ℂ) + s i * I) - (Real.cos (y i) + Real.sin (y i) * I)).re
        = c i - Real.cos (y i) := by
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    have him : (((c i : ℂ) + s i * I) - (Real.cos (y i) + Real.sin (y i) * I)).im
        = s i - Real.sin (y i) := by
      simp [Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im]
    rw [hre, him]
    linarith [hc i, hs i]
  have h := norm_prod_sub_prod_le (by positivity) hb hab (k + 1)
  have hexact : ∏ i ∈ range (k + 1), Complex.exp (y i * I)
      = Complex.exp (tailSum y k 0 * I) := by
    rw [← sinCosProd_exact, sinCosProd, range_eq_Ico]
    exact prod_congr rfl fun i _ => exp_mul_I_eq (y i)
  have hprod : sinCosProd c s k 0 = ∏ i ∈ range (k + 1), ((c i : ℂ) + s i * I) := by
    rw [sinCosProd, range_eq_Ico]
  rw [hexact] at h
  push_cast at h
  have hsin : Real.sin (tailSum y k 0) = (Complex.exp (tailSum y k 0 * I)).im :=
    (exp_ofReal_mul_I_im _).symm
  have hcos : Real.cos (tailSum y k 0) = (Complex.exp (tailSum y k 0 * I)).re :=
    (exp_ofReal_mul_I_re _).symm
  rw [hsin, hcos, hprod]
  constructor
  · exact (abs_im_le_norm _).trans (by simpa using h)
  · exact (abs_re_le_norm _).trans (by simpa using h)

/-! ### The powers in the binary splitting of `sin y_j` -/

/-- With `p < 2^(2^j)`, `p^N < 2^(2^j N)`: the powers needed for `sin y_j` have at most
`2^j N` bits, below `n` when `2^j N ≤ n`. -/
theorem pow_lt_two_pow_of_digit {p : ℕ} {j : ℕ} (hp : p < 2 ^ 2 ^ j) (N : ℕ) (hN : 0 < N) :
    p ^ N < 2 ^ (2 ^ j * N) := by
  rw [pow_mul]
  exact Nat.pow_lt_pow_left hp hN.ne'

end BZ

end Azurite
