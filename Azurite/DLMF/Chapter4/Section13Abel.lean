/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic

/-!
# An Abel identity (for the Taylor series of the Lambert `W`-function)

`abel_identity`: for `n ≥ 1` and `y ∈ ℂ`,
`∑_{k=1}^{n} C(n, k) k^{k−1} (y + n − k)^{n−k} = n (y + n)^{n−1}`.

Proof: both sides have the same `y`-derivative by induction (`C(n, k)(n − k) = n C(n − 1, k)`), and
at `y = −n` the left side is the `n`-th forward difference of `t^{n−1}`, which vanishes.
-/

open Finset

namespace Azurite.DLMF

/-- The left side `∑_{k=1}^{n} C(n, k) k^{k−1} (y + n − k)^{n−k}`. -/
noncomputable def abelSum (n : ℕ) (y : ℂ) : ℂ :=
  ∑ k ∈ Icc 1 n, (n.choose k : ℂ) * (k : ℂ) ^ (k - 1) * (y + n - k) ^ (n - k)

/-- `∑_{k=0}^{n} (−1)^{n−k} C(n, k) (x + k)^j = 0` for `j < n`. -/
theorem sum_alt_choose_pow_eq_zero {j n : ℕ} (h : j < n) (x : ℂ) :
    ∑ k ∈ range (n + 1), (-1 : ℂ) ^ (n - k) * n.choose k * (x + k) ^ j = 0 := by
  have h1 := fwdDiff_iter_eq_sum_shift (h := (1 : ℂ)) (fun r : ℂ => r ^ j) n x
  rw [fwdDiff_iter_pow_eq_zero_of_lt h] at h1
  simp only [Pi.zero_apply, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h1
  rw [h1]
  refine sum_congr rfl fun k _ => ?_
  push_cast; ring

theorem hasDerivAt_abelSum (n : ℕ) (y : ℂ) :
    HasDerivAt (abelSum (n + 1)) ((n + 1) * abelSum n (y + 1)) y := by
  have hterm : ∀ k ∈ Icc 1 (n + 1), HasDerivAt
      (fun y : ℂ => ((n + 1).choose k : ℂ) * (k : ℂ) ^ (k - 1) *
        (y + (n + 1 : ℕ) - k) ^ (n + 1 - k))
      (((n + 1).choose k : ℂ) * (k : ℂ) ^ (k - 1) *
        (((n + 1 - k : ℕ) : ℂ) * (y + (n + 1 : ℕ) - k) ^ (n + 1 - k - 1))) y := by
    intro k _
    have := ((((hasDerivAt_id y).add_const ((n + 1 : ℕ) : ℂ)).sub_const (k : ℂ)).pow
      (n + 1 - k)).const_mul (((n + 1).choose k : ℂ) * (k : ℂ) ^ (k - 1))
    simpa using this
  have h := HasDerivAt.fun_sum hterm
  have hfun : (fun y => ∑ k ∈ Icc 1 (n + 1), ((n + 1).choose k : ℂ) * (k : ℂ) ^ (k - 1) *
      (y + (n + 1 : ℕ) - k) ^ (n + 1 - k)) = abelSum (n + 1) := by
    funext y; simp only [abelSum]
  rw [hfun] at h
  convert h using 1
  -- reindex: `C(n+1, k)(n + 1 − k) = (n + 1) C(n, k)`, and the `k = n + 1` term vanishes
  rw [abelSum, mul_sum, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_Icc.mp hk
  have hc : ((n + 1).choose k : ℂ) * ((n + 1 - k : ℕ) : ℂ) = (n + 1) * (n.choose k : ℂ) := by
    have := Nat.choose_mul_succ_eq n k
    have h2 : (((n + 1).choose k * (n + 1 - k) : ℕ) : ℂ) = ((n.choose k * (n + 1) : ℕ) : ℂ) := by
      rw [this]
    push_cast at h2 ⊢
    rw [Nat.cast_sub (by omega)] at h2 ⊢
    push_cast at h2 ⊢
    linear_combination h2
  have he : n + 1 - k - 1 = n - k := by omega
  rw [he]
  have hb : y + ((n + 1 : ℕ) : ℂ) - k = y + 1 + n - k := by push_cast; ring
  rw [hb]
  linear_combination (-(k : ℂ) ^ (k - 1) * (y + 1 + n - k) ^ (n - k)) * hc

/-- **Abel identity**: `∑_{k=1}^{n} C(n, k) k^{k−1} (y + n − k)^{n−k} = n (y + n)^{n−1}`. -/
theorem abel_identity : ∀ (n : ℕ), 1 ≤ n → ∀ y : ℂ, abelSum n y = n * (y + n) ^ (n - 1)
  | 0, h, _ => absurd h (by omega)
  | 1, _, y => by simp [abelSum]
  | n + 2, _, y => by
    have ih := abel_identity (n + 1) (by omega)
    set f : ℂ → ℂ := fun y => abelSum (n + 2) y - (n + 2 : ℕ) * (y + (n + 2 : ℕ)) ^ (n + 1)
    have hf : ∀ y, HasDerivAt f 0 y := by
      intro y
      have h1 := hasDerivAt_abelSum (n + 1) y
      have h2 := ((((hasDerivAt_id y).add_const ((n + 2 : ℕ) : ℂ)).pow (n + 1)).const_mul
        ((n + 2 : ℕ) : ℂ))
      have := h1.sub h2
      convert this using 1
      case e'_8 => funext y; simp [f]
      rw [ih (y + 1)]
      push_cast
      simp only [id]
      ring
    have hconst := is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt)
      (fun y => (hf y).deriv) y (-((n + 2 : ℕ) : ℂ))
    have hval : f (-((n + 2 : ℕ) : ℂ)) = 0 := by
      have h0 := sum_alt_choose_pow_eq_zero (j := n + 1) (n := n + 2) (by omega) 0
      rw [sum_range_succ'] at h0
      simp only [Nat.cast_zero, zero_add, zero_pow (by omega : n + 1 ≠ 0), mul_zero, add_zero]
        at h0
      have e1 : abelSum (n + 2) (-((n + 2 : ℕ) : ℂ)) = ∑ k ∈ range (n + 2),
          ((n + 2).choose (k + 1) : ℂ) * ((k + 1 : ℕ) : ℂ) ^ k *
            (-((k + 1 : ℕ) : ℂ)) ^ (n + 1 - k) := by
        rw [abelSum, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
        refine sum_congr rfl fun k hk => ?_
        have hk' := mem_range.mp hk
        rw [show 1 + k = k + 1 by ring, show n + 2 - (k + 1) = n + 1 - k by omega,
          show k + 1 - 1 = k by omega]
        congr 2; push_cast; ring
      simp only [f, e1, neg_add_cancel, zero_pow (by omega : n + 1 ≠ 0), mul_zero, sub_zero]
      rw [← h0]
      refine sum_congr rfl fun k hk => ?_
      have hk' := mem_range.mp hk
      rw [show n + 2 - (k + 1) = n + 1 - k by omega, neg_pow ((((k + 1 : ℕ) : ℂ)))]
      have hp : ((k + 1 : ℕ) : ℂ) ^ k * ((k + 1 : ℕ) : ℂ) ^ (n + 1 - k) =
          ((k + 1 : ℕ) : ℂ) ^ (n + 1) := by rw [← pow_add]; congr 1; omega
      push_cast at hp ⊢
      linear_combination ((-1 : ℂ) ^ (n + 1 - k) * ((n + 2).choose (k + 1) : ℂ)) * hp
    rw [show abelSum (n + 2) y = f y + (n + 2 : ℕ) * (y + (n + 2 : ℕ)) ^ (n + 1) by simp [f],
      hconst, hval]
    push_cast; ring

end Azurite.DLMF
