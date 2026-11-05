/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section11Levin
import Azurite.DLMF.Chapter3.Section9
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# DLMF §3.9(v): Levin's and Weniger's transformations

* 3.9.13 (`levinGen`): `𝓛_k^{(n)}(s) = ∑ (−1)^j C(k, j) c_{j,k,n} s_{n+j}/a_{n+j+1} /
  ∑ (−1)^j C(k, j) c_{j,k,n}/a_{n+j+1}` with `c_{j,k,n} = w(n + j)/w(n + k)`; `sₙ = ∑_{j≤n} a_j`
  (`partialSum`, §1.9).
* 3.9.14 (`levin39W`, `levinL`): Levin, `c_{j,k,n} = (n + j + 1)^{k−1}/(n + k + 1)^{k−1}`.
  For `n = 0` it is the variant 2.11.32 of §2.11(vi) (`levinL_zero_eq_levinD`).
* 3.9.16, 3.9.17 (`wenigerW₁`, `wenigerW₂`): Weniger, `(β + n + j)_{k−1}/(β + n + k)_{k−1}` and
  `(−γ − n − j)_{k−1}/(−γ − n − k)_{k−1}` (Pochhammer symbols, `ascPochhammer`).
* The kernel: the transformation is exact (`= σ`) when `w(m)(s_m − σ)/a_{m+1}` is a polynomial
  in `m` of degree `< k` (`levinGen_eq_of_poly`, for any weights, including Weniger's); for
  Levin's weights this means
  `s_m = σ + a_{m+1} ∑_{i<k} d_i/(m + 1)^i` (`levinL_exact`).
* 3.9.15 (`IsLogConvergent`): logarithmic convergence `(s_{n+1} − σ)/(sₙ − σ) → 1`.
* "Sequences that are accelerated by Levin's transformation include logarithmically convergent
  sequences": **erratum** for the special form 3.9.13–3.9.14. The partial sums of `∑ 1/(j + 1)²`
  converge logarithmically to `π²/6` (`zeta2_isLogConvergent`), but for `k = 1`
  `𝓛_1^{(n)} = sₙ + (n + 3)²/((n + 2)²(2n + 5))` (`levinL_one_zeta2`) and
  `(𝓛_1^{(n)} − σ)/(sₙ − σ) → 1/2`
  (`levinL_one_zeta2_ratio`), so the transformation is not accelerating
  (`levinL_one_not_accelerating`). Numerically the ratio tends to `1/(k + 1)` for each fixed
  `k`; Levin's `u`-transformation (`c` with exponent `k − 2`) does accelerate this sequence.
* Brezinski and Redivo Zaglia (1991), Weniger (1989): not formalized.
-/

open Filter Topology Finset Polynomial

namespace Azurite.DLMF

/-! ### The transformations -/

section Defs

variable {𝕜 : Type*} [Field 𝕜]

/-- **DLMF 3.9.13** with `c_{j,k,n} = w(n + j)/w(n + k)`. -/
def levinGen (w : ℕ → 𝕜) (k n : ℕ) (s a : ℕ → 𝕜) : 𝕜 :=
  (∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : 𝕜) * (w (n + j) / w (n + k)) * s (n + j) /
      a (n + j + 1)) /
    ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : 𝕜) * (w (n + j) / w (n + k)) / a (n + j + 1)

/-- **DLMF 3.9.14**: Levin's weights `(m + 1)^{k−1}`. -/
def levin39W (k m : ℕ) : 𝕜 := ((m : 𝕜) + 1) ^ ((k : ℤ) - 1)

/-- **DLMF 3.9.13–3.9.14**: Levin's transformation of the partial sums of `∑ a_j`. -/
def levinL (k n : ℕ) (a : ℕ → 𝕜) : 𝕜 := levinGen (levin39W k) k n (partialSum a) a

theorem dlmf_3_9_14 (k n j : ℕ) :
    levin39W (𝕜 := 𝕜) k (n + j) / levin39W k (n + k) =
      ((n + j + 1 : ℕ) : 𝕜) ^ ((k : ℤ) - 1) / ((n + k + 1 : ℕ) : 𝕜) ^ ((k : ℤ) - 1) := by
  simp [levin39W]

/-- For `n = 0`, 3.9.13–3.9.14 is Levin's transformation 2.11.32 of §2.11(vi). -/
theorem levinL_zero_eq_levinD [CharZero 𝕜] (k : ℕ) (a : ℕ → 𝕜) : levinL k 0 a = levinD a k := by
  have hW : levin39W (𝕜 := 𝕜) k (0 + k) ≠ 0 := by
    simp only [levin39W, zero_add]
    exact zpow_ne_zero _ (Nat.cast_add_one_ne_zero k)
  set W := levin39W (𝕜 := 𝕜) k (0 + k)
  have hn : ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : 𝕜) * (levin39W k (0 + j) / W) *
      partialSum a (0 + j) / a (0 + j + 1) =
      (∑ j ∈ range (k + 1), levinW k j * partialSum a j / a (j + 1)) / W := by
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    simp only [levinW, levin39W, zero_add]
    ring
  have hd : ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : 𝕜) * (levin39W k (0 + j) / W) /
      a (0 + j + 1) = (∑ j ∈ range (k + 1), levinW k j / a (j + 1)) / W := by
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    simp only [levinW, levin39W, zero_add]
    ring
  rw [levinL, levinGen, hn, hd, div_div_div_cancel_right₀ hW, levinD]

/-- **DLMF 3.9.16**: Weniger's weights `(β + m)_{k−1}`. -/
noncomputable def wenigerW₁ (β : 𝕜) (k m : ℕ) : 𝕜 := (ascPochhammer 𝕜 (k - 1)).eval (β + m)

/-- **DLMF 3.9.17**: Weniger's weights `(−γ − m)_{k−1}`. -/
noncomputable def wenigerW₂ (γ : 𝕜) (k m : ℕ) : 𝕜 := (ascPochhammer 𝕜 (k - 1)).eval (-γ - m)

/-- The Pochhammer symbol: `(a)₀ = 1`, `(a)_j = a(a + 1)⋯(a + j − 1)`. -/
theorem pochhammer_eval (a : 𝕜) (j : ℕ) :
    (ascPochhammer 𝕜 j).eval a = ∏ i ∈ range j, (a + i) := by
  induction j with
  | zero => simp
  | succ j ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]

end Defs

/-! ### The kernel -/

section Kernel

variable {𝕜 : Type*} [Field 𝕜]

/-- `∑_{j ≤ k} (−1)^j C(k, j) P(j) = 0` for `deg P < k`. -/
theorem alt_choose_poly (P : 𝕜[X]) {k : ℕ} (hP : P.natDegree < k) :
    ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : 𝕜) * P.eval (j : 𝕜) = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [Pi.zero_apply, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h
  have h' := congrArg (fun x => (-1 : 𝕜) ^ k * x) h
  simp only [mul_zero, mul_sum] at h'
  rw [← h']
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
  push_cast
  rw [show j + d - j = d by omega, pow_add]
  ring_nf
  rw [pow_mul', neg_one_sq, one_pow, mul_one]

/-- The transformation is exact on its kernel: if `w(n + j)(s_{n+j} − σ)/a_{n+j+1} = P(j)` for
`j ≤ k` with `deg P < k`, then `𝓛 = σ` (when the denominator does not vanish). -/
theorem levinGen_eq_of_poly {w : ℕ → 𝕜} {k n : ℕ} {s a : ℕ → 𝕜} {σ : 𝕜} {P : 𝕜[X]}
    (hP : P.natDegree < k)
    (hden : ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : 𝕜) * (w (n + j) / w (n + k)) /
      a (n + j + 1) ≠ 0)
    (h : ∀ j ≤ k, w (n + j) * (s (n + j) - σ) / a (n + j + 1) = P.eval (j : 𝕜)) :
    levinGen w k n s a = σ := by
  rw [levinGen, div_eq_iff hden, ← sub_eq_zero, mul_sum, ← sum_sub_distrib]
  have : ∀ j ∈ range (k + 1),
      (-1) ^ j * (k.choose j : 𝕜) * (w (n + j) / w (n + k)) * s (n + j) / a (n + j + 1) -
        σ * ((-1) ^ j * (k.choose j : 𝕜) * (w (n + j) / w (n + k)) / a (n + j + 1)) =
      (w (n + k))⁻¹ * ((-1) ^ j * (k.choose j : 𝕜) * P.eval (j : 𝕜)) := by
    intro j hj
    rw [← h j (Nat.lt_succ_iff.mp (mem_range.mp hj))]
    ring
  rw [sum_congr rfl this, ← mul_sum, alt_choose_poly P hP, mul_zero]

end Kernel

section LevinKernel

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Levin's transformation is exact for `s_m = σ + a_{m+1} ∑_{i<k} d_i/(m + 1)^i`. -/
theorem levinL_exact {k n : ℕ} (hk : 1 ≤ k) {a : ℕ → 𝕜} {σ : 𝕜} (d : ℕ → 𝕜)
    (ha : ∀ j ≤ k, a (n + j + 1) ≠ 0)
    (hs : ∀ j ≤ k, partialSum a (n + j) =
      σ + a (n + j + 1) * ∑ i ∈ range k, d i / (((n + j : ℕ) : 𝕜) + 1) ^ i)
    (hden : ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : 𝕜) *
      (levin39W k (n + j) / levin39W k (n + k)) / a (n + j + 1) ≠ 0) :
    levinL k n a = σ := by
  set P : 𝕜[X] := ∑ i ∈ range k, C (d i) * (X + C ((n : 𝕜) + 1)) ^ (k - 1 - i)
  have hP : P.natDegree < k := by
    have : P.natDegree ≤ k - 1 := natDegree_sum_le_of_forall_le _ _ fun i _ => by
      refine (natDegree_C_mul_le _ _).trans ?_
      refine (natDegree_pow_le).trans ?_
      have : (X + C ((n : 𝕜) + 1)).natDegree ≤ 1 := by
        refine (natDegree_add_le _ _).trans ?_; simp
      calc (k - 1 - i) * (X + C ((n : 𝕜) + 1)).natDegree ≤ (k - 1 - i) * 1 := by gcongr
        _ ≤ k - 1 := by omega
    omega
  refine levinGen_eq_of_poly hP hden fun j hj => ?_
  have hx : (((n + j : ℕ) : 𝕜) + 1) ≠ 0 := Nat.cast_add_one_ne_zero (n + j)
  rw [hs j hj, add_sub_cancel_left, mul_comm (a _), ← mul_assoc, mul_div_assoc,
    div_self (ha j hj), mul_one, levin39W, mul_sum]
  simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_X]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < k := mem_range.mp hi
  rw [show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast,
    show (((n + j : ℕ) : 𝕜) + 1) ^ (k - 1) =
      (((n + j : ℕ) : 𝕜) + 1) ^ (k - 1 - i) * (((n + j : ℕ) : 𝕜) + 1) ^ i by
      rw [← pow_add]; congr 1; omega]
  field_simp
  push_cast
  ring

end LevinKernel

/-! ### Logarithmic convergence and `∑ 1/(j + 1)²` -/

/-- **DLMF 3.9.15**: `{sₙ}` converges logarithmically to `σ`. -/
def IsLogConvergent (s : ℕ → ℝ) (σ : ℝ) : Prop :=
  Tendsto s atTop (𝓝 σ) ∧ Tendsto (fun n => (s (n + 1) - σ) / (s n - σ)) atTop (𝓝 1)

/-- The terms `1/(j + 1)²`. -/
noncomputable def zeta2Term (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1) ^ 2

theorem hasSum_zeta2Term : HasSum zeta2Term (Real.pi ^ 2 / 6) := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  show HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) _
  simpa [one_div] using this

/-- Telescoping: `∑_i (1/(c + i) − 1/(c + i + 1)) = 1/c`. -/
theorem hasSum_telescope {c : ℝ} (hc : 0 < c) :
    HasSum (fun i : ℕ => 1 / (c + i) - 1 / (c + i + 1)) (1 / c) := by
  have hnn : ∀ i : ℕ, 0 ≤ 1 / (c + i) - 1 / (c + i + 1) := fun i => by
    have : 0 < c + i := by positivity
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le this (by linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hsum : ∀ N : ℕ, ∑ i ∈ range N, (1 / (c + i) - 1 / (c + i + 1)) = 1 / c - 1 / (c + N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ, ih]; push_cast; ring
  simp_rw [hsum]
  have : Tendsto (fun N : ℕ => 1 / (c + N)) atTop (𝓝 0) := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    have h := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ c this)
    simpa only [Function.comp_def, one_div] using h
  simpa using this.const_sub (1 / c)

/-- The remainder `rₙ = π²/6 − sₙ = ∑_{j>n} 1/(j + 1)²`. -/
theorem hasSum_zeta2_tail (n : ℕ) :
    HasSum (fun i : ℕ => zeta2Term (i + (n + 1))) (Real.pi ^ 2 / 6 - partialSum zeta2Term n) := by
  have := (hasSum_nat_add_iff' (n + 1)).mpr hasSum_zeta2Term
  simpa [partialSum] using this

/-- `1/(n + 2) ≤ rₙ ≤ 1/(n + 1)`. -/
theorem zeta2_tail_bounds (n : ℕ) :
    1 / ((n : ℝ) + 2) ≤ Real.pi ^ 2 / 6 - partialSum zeta2Term n ∧
      Real.pi ^ 2 / 6 - partialSum zeta2Term n ≤ 1 / ((n : ℝ) + 1) := by
  have ht := hasSum_zeta2_tail n
  constructor
  · refine hasSum_le (fun i => ?_) (hasSum_telescope (c := (n : ℝ) + 2) (by positivity)) ht
    simp only [zeta2Term]
    push_cast
    have h1 : 0 < (n : ℝ) + 2 + i := by positivity
    rw [div_sub_div _ _ h1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · refine hasSum_le (fun i => ?_) ht (hasSum_telescope (c := (n : ℝ) + 1) (by positivity))
    simp only [zeta2Term]
    push_cast
    have h1 : 0 < (n : ℝ) + 1 + i := by positivity
    rw [div_sub_div _ _ h1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem tendsto_zeta2 : Tendsto (partialSum zeta2Term) atTop (𝓝 (Real.pi ^ 2 / 6)) :=
  tendsto_partialSum hasSum_zeta2Term

/-- The partial sums of `∑ 1/(j + 1)²` converge logarithmically (3.9.15). -/
theorem zeta2_isLogConvergent : IsLogConvergent (partialSum zeta2Term) (Real.pi ^ 2 / 6) := by
  refine ⟨tendsto_zeta2, ?_⟩
  set r : ℕ → ℝ := fun n => Real.pi ^ 2 / 6 - partialSum zeta2Term n
  have hr : ∀ n, (partialSum zeta2Term (n + 1) - Real.pi ^ 2 / 6) /
      (partialSum zeta2Term n - Real.pi ^ 2 / 6) = r (n + 1) / r n := fun n => by
    simp only [r]; rw [← neg_div_neg_eq]; congr 1 <;> ring
  simp_rw [hr]
  have hlo : ∀ n : ℕ, ((n : ℝ) + 1) / (n + 3) ≤ r (n + 1) / r n := fun n => by
    obtain ⟨a1, -⟩ := zeta2_tail_bounds (n + 1)
    obtain ⟨-, b0⟩ := zeta2_tail_bounds n
    have hp : 0 < r n := lt_of_lt_of_le (by positivity) (zeta2_tail_bounds n).1
    rw [le_div_iff₀ hp]
    push_cast at a1
    calc ((n : ℝ) + 1) / (n + 3) * r n ≤ ((n : ℝ) + 1) / (n + 3) * (1 / (n + 1)) := by gcongr
      _ = 1 / ((n : ℝ) + 1 + 2) := by field_simp; ring
      _ ≤ r (n + 1) := a1
  have hhi : ∀ n : ℕ, r (n + 1) / r n ≤ 1 := fun n => by
    have hp : 0 < r n := lt_of_lt_of_le (by positivity) (zeta2_tail_bounds n).1
    rw [div_le_one hp]
    simp only [r, partialSum, sum_range_succ]
    have : 0 ≤ zeta2Term (n + 1) := by simp only [zeta2Term]; positivity
    linarith
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n + 3)) atTop (𝓝 1) := by
    have h := tendsto_natCast_atTop_atTop (R := ℝ)
    have : Tendsto (fun n : ℕ => 1 - 2 / ((n : ℝ) + 3)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 3 h))
    refine (this.congr fun n => ?_).trans (by simp)
    field_simp; ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlo hhi

/-- For `k = 1`, Levin's transformation of `∑ 1/(j + 1)²` is
`sₙ + (n + 3)²/((n + 2)²(2n + 5))`. -/
theorem levinL_one_zeta2 (n : ℕ) :
    levinL 1 n zeta2Term =
      partialSum zeta2Term n + ((n : ℝ) + 3) ^ 2 / (((n : ℝ) + 2) ^ 2 * (2 * n + 5)) := by
  have a1 : zeta2Term (n + 0 + 1) = 1 / ((n : ℝ) + 2) ^ 2 := by
    simp only [zeta2Term]; push_cast; ring_nf
  have a2 : zeta2Term (n + 1 + 1) = 1 / ((n : ℝ) + 3) ^ 2 := by
    simp only [zeta2Term]; push_cast; ring_nf
  have hs : partialSum zeta2Term (n + 1) = partialSum zeta2Term n + 1 / ((n : ℝ) + 2) ^ 2 := by
    simp only [partialSum, sum_range_succ, zeta2Term]; push_cast; ring_nf
  have hw : ∀ m, levin39W (𝕜 := ℝ) 1 m = 1 := fun m => by simp [levin39W]
  simp only [levinL, levinGen, sum_range_succ, sum_range_zero, hw, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_one, div_one, zero_add, pow_zero, pow_one, one_mul, mul_one,
    add_zero, a1, a2, hs]
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have hd : 1 / (1 / ((n : ℝ) + 2) ^ 2) + -1 / (1 / ((n : ℝ) + 3) ^ 2) = -(2 * n + 5) := by
    field_simp; ring
  rw [hd]
  field_simp
  ring

/-- `(𝓛_1^{(n)} − σ)/(sₙ − σ) → 1/2` for `sₙ = ∑_{j≤n} 1/(j + 1)²`. -/
theorem levinL_one_zeta2_ratio :
    Tendsto (fun n => (levinL 1 n zeta2Term - Real.pi ^ 2 / 6) /
      (partialSum zeta2Term n - Real.pi ^ 2 / 6)) atTop (𝓝 (1 / 2)) := by
  set r : ℕ → ℝ := fun n => Real.pi ^ 2 / 6 - partialSum zeta2Term n
  have hpos : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by positivity) (zeta2_tail_bounds n).1
  have he : ∀ n, (levinL 1 n zeta2Term - Real.pi ^ 2 / 6) /
      (partialSum zeta2Term n - Real.pi ^ 2 / 6) =
        1 - (((n : ℝ) + 3) / (n + 2)) ^ 2 / ((2 * n + 5) * r n) := fun n => by
    rw [levinL_one_zeta2]
    have hr := hpos n
    have h2 : (0 : ℝ) < 2 * n + 5 := by positivity
    have h3 : (0 : ℝ) < n + 2 := by positivity
    have h4' : partialSum zeta2Term n - Real.pi ^ 2 / 6 ≠ 0 := by
      intro h; simp only [r] at hr; linarith
    rw [show partialSum zeta2Term n + ((n : ℝ) + 3) ^ 2 / (((n : ℝ) + 2) ^ 2 * (2 * n + 5)) -
        Real.pi ^ 2 / 6 = (partialSum zeta2Term n - Real.pi ^ 2 / 6) +
          ((n : ℝ) + 3) ^ 2 / (((n : ℝ) + 2) ^ 2 * (2 * n + 5)) by ring, add_div, div_self h4',
      show partialSum zeta2Term n - Real.pi ^ 2 / 6 = -r n by simp only [r]; ring, div_neg,
      ← sub_eq_add_neg, div_pow]
    congr 1
    field_simp
  simp_rw [he]
  -- `(2n + 5) rₙ → 2`
  have hlo : ∀ n : ℕ, (2 * (n : ℝ) + 5) / (n + 2) ≤ (2 * n + 5) * r n := fun n => by
    have := (zeta2_tail_bounds n).1
    calc (2 * (n : ℝ) + 5) / (n + 2) = (2 * n + 5) * (1 / (n + 2)) := by ring
      _ ≤ _ := by gcongr
  have hhi : ∀ n : ℕ, (2 * n + 5) * r n ≤ (2 * (n : ℝ) + 5) / (n + 1) := fun n => by
    have := (zeta2_tail_bounds n).2
    calc (2 * (n : ℝ) + 5) * r n ≤ (2 * n + 5) * (1 / (n + 1)) := by gcongr
      _ = _ := by ring
  have h := tendsto_natCast_atTop_atTop (R := ℝ)
  have hc : ∀ c : ℝ, 0 ≤ c → Tendsto (fun n : ℕ => (2 * (n : ℝ) + 5) / (n + c + 1)) atTop
      (𝓝 2) := by
    intro c hc
    have : Tendsto (fun n : ℕ => 2 + (3 - 2 * c) / ((n : ℝ) + c + 1)) atTop (𝓝 (2 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 1 (tendsto_atTop_add_const_right _ c h)))
    refine (this.congr fun n => ?_).trans (by simp)
    have : (0 : ℝ) < n + c + 1 := by positivity
    field_simp; ring
  have h2 : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 5) * r n) atTop (𝓝 2) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ((hc 1 zero_le_one).congr fun n => ?_)
      ((hc 0 le_rfl).congr fun n => ?_) hlo hhi
    · ring_nf
    · ring_nf
  have hq : Tendsto (fun n : ℕ => ((n : ℝ) + 3) / (n + 2)) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 h))
    refine (this.congr fun n => ?_).trans (by simp)
    have : (0 : ℝ) < n + 2 := by positivity
    field_simp; ring
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub ((hq.pow 2).div h2 (by norm_num))
  convert this using 2
  norm_num

/-- **Erratum** (DLMF §3.9(v)): the special form 3.9.13–3.9.14 with `k = 1` does not accelerate
the logarithmically convergent partial sums of `∑ 1/(j + 1)²`. -/
theorem levinL_one_not_accelerating :
    IsLogConvergent (partialSum zeta2Term) (Real.pi ^ 2 / 6) ∧
      ¬ IsAccelerating (fun t n => levinGen (levin39W 1) 1 n t zeta2Term) (partialSum zeta2Term)
        (Real.pi ^ 2 / 6) := by
  refine ⟨zeta2_isLogConvergent, fun ⟨_, _, h⟩ => ?_⟩
  have := tendsto_nhds_unique h levinL_one_zeta2_ratio
  norm_num at this

end Azurite.DLMF
