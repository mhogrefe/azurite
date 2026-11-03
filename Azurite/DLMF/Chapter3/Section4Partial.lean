/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# DLMF §3.4(iii): partial derivatives

Notation `u_{t,s} = u(x₀ + th, y₀ + sh)`. Partial derivatives are taken `y` first:
`iterPartialXY u i j x₀ y₀ = ∂ⁱ/∂xⁱ (∂ʲu/∂yʲ)(x₀, y₀)` (`iterPartialY`); for the smooth `u`
considered the order does not matter, but no symmetry of higher derivatives is used (Mathlib
has it only for order 2).

* Infrastructure: `contDiff_iterPartialY` (`∂ʲu/∂yʲ ∈ C^{N−j}` for `u ∈ Cᴺ`),
  `taylor_lagrange_iteratedDeriv` (Lagrange remainder), `taylor2` (two-variable Taylor expansion
  along `(ah, bh)` with a remainder `O(|h|ᴺ)` uniform for `|h| ≤ 1`: Taylor in `y`, then in `x`,
  remainders bounded on compact boxes), `stencil_isBigO` (a stencil exact on all monomials of
  degree `< N` approximates `∑ T(i,j) ∂^{i+j}u` with error `O(h^{N−d})`).
* 3.4.20–3.4.26, 3.4.28–3.4.31, 3.4.33, 3.4.34: `dlmf_3_4_20`, …, as `=O[𝓝[≠] 0]` statements
  for `u ∈ C^{d+p}` on `ℝ²` (`d` the order of the derivative, `O(hᵖ)` the error), with the
  exactness conditions checked by case analysis. All orders are as stated by DLMF (and sharp).
* 3.4.27, 3.4.32: `laplacian`, `biharmonic`.
-/

open Finset Filter Topology Set Asymptotics

namespace Azurite.DLMF

/-! ### Partial derivatives and a two-variable Taylor expansion -/

/-- `∂ʲu/∂yʲ (x, y)`. -/
noncomputable def iterPartialY (u : ℝ → ℝ → ℝ) (j : ℕ) (x y : ℝ) : ℝ :=
  iteratedDeriv j (fun y' => u x y') y

/-- `∂^{i+j}u/∂xⁱ∂yʲ (x₀, y₀)`: `j` derivatives in `y`, then `i` in `x`. -/
noncomputable def iterPartialXY (u : ℝ → ℝ → ℝ) (i j : ℕ) (x₀ y₀ : ℝ) : ℝ :=
  iteratedDeriv i (fun x => iterPartialY u j x y₀) x₀

/-- If `u` is `Cᴺ`, then `∂ʲu/∂yʲ` is `C^{N−j}` in `(x, y)`. -/
theorem contDiff_iterPartialY {u : ℝ → ℝ → ℝ} {N : ℕ} (hu : ContDiff ℝ N (Function.uncurry u)) :
    ∀ j ≤ N, ContDiff ℝ (N - j : ℕ) (Function.uncurry (iterPartialY u j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : Function.uncurry (iterPartialY u 0) = Function.uncurry u := by
      funext ⟨x, y⟩; simp [iterPartialY]
    rw [h0]; simpa using hu
  | succ j ih =>
    intro hj
    have hW := ih (by omega)
    set W := Function.uncurry (iterPartialY u j)
    have hfun : Function.uncurry (iterPartialY u (j + 1)) = fun p => fderiv ℝ W p (0, 1) := by
      funext ⟨x, y⟩
      simp only [Function.uncurry_apply_pair, iterPartialY]
      rw [iteratedDeriv_succ]
      have hd : HasDerivAt (fun y' : ℝ => ((x, y') : ℝ × ℝ)) (0, 1) y :=
        (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
      exact ((hW.differentiable (by norm_cast; omega)) (x, y)).hasFDerivAt.comp_hasDerivAt y hd
        |>.deriv
    rw [hfun]
    exact (hW.fderiv_right (m := ((N - (j + 1) : ℕ) : WithTop ℕ∞)) (by norm_cast; omega)).clm_apply
      contDiff_const

/-- Taylor's theorem with the Lagrange remainder, for `C^{n+1}` functions on `ℝ`. -/
theorem taylor_lagrange_iteratedDeriv {φ : ℝ → ℝ} {n : ℕ} (hφ : ContDiff ℝ (n + 1) φ)
    (t₀ s : ℝ) :
    ∃ ξ ∈ uIcc t₀ (t₀ + s), φ (t₀ + s) =
      ∑ k ∈ range (n + 1), iteratedDeriv k φ t₀ * s ^ k / k.factorial +
        iteratedDeriv (n + 1) φ ξ * s ^ (n + 1) / (n + 1).factorial := by
  by_cases hs : s = 0
  · refine ⟨t₀, by simp [hs], ?_⟩
    subst hs
    rw [sum_range_succ']
    simp
  · have hne : t₀ ≠ t₀ + s := by simpa using hs
    obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hφ.contDiffOn
    refine ⟨ξ, Set.uIoo_subset_uIcc_self hξ, ?_⟩
    have hu : UniqueDiffOn ℝ (uIcc t₀ (t₀ + s)) := uniqueDiffOn_uIcc hne
    rw [taylor_within_apply] at h
    have hsum : ∑ k ∈ range (n + 1), ((k.factorial : ℝ)⁻¹ * (t₀ + s - t₀) ^ k) •
        iteratedDerivWithin k φ (uIcc t₀ (t₀ + s)) t₀ =
        ∑ k ∈ range (n + 1), iteratedDeriv k φ t₀ * s ^ k / k.factorial := by
      refine sum_congr rfl fun k hk => ?_
      have hk' : (k : WithTop ℕ∞) ≤ n + 1 := by
        have := mem_range.mp hk; norm_cast; omega
      rw [iteratedDerivWithin_eq_iteratedDeriv hu ((hφ.of_le hk').contDiffAt) left_mem_uIcc,
        smul_eq_mul, add_sub_cancel_left]
      ring
    rw [hsum] at h
    simp only [add_sub_cancel_left] at h
    linarith

theorem uIcc_subset_Icc_of_abs_le {t₀ s r : ℝ} (h : |s| ≤ r) :
    uIcc t₀ (t₀ + s) ⊆ Icc (t₀ - r) (t₀ + r) := by
  have hr := (abs_nonneg s).trans h
  apply Set.uIcc_subset_Icc <;> constructor <;> linarith [abs_le.mp h]

/-- **Two-variable Taylor expansion with a uniform remainder**: for `u ∈ Cᴺ`, `N ≥ 1`,
`u(x₀ + ah, y₀ + bh) = ∑_{i+j<N} ∂^{i+j}u/∂xⁱ∂yʲ (x₀, y₀) (ah)ⁱ/i! (bh)ʲ/j! + O(|h|ᴺ)`, uniformly
for `|h| ≤ 1`. -/
theorem taylor2 {u : ℝ → ℝ → ℝ} {N : ℕ} (hN : 1 ≤ N) (hu : ContDiff ℝ N (Function.uncurry u))
    (x₀ y₀ a b : ℝ) :
    ∃ C, ∀ h : ℝ, |h| ≤ 1 → |u (x₀ + a * h) (y₀ + b * h) -
      ∑ j ∈ range N, ∑ i ∈ range (N - j),
        iterPartialXY u i j x₀ y₀ * (a * h) ^ i / i.factorial * ((b * h) ^ j / j.factorial)| ≤
      C * |h| ^ N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  -- smoothness of `g_j(x) = ∂ʲu/∂yʲ (x, y₀)`
  have hg : ∀ j ∈ range (n + 1), ContDiff ℝ ((n - j : ℕ) + 1)
      (fun x => iterPartialY u j x y₀) := fun j hj => by
    have hj' := mem_range.mp hj
    have := (contDiff_iterPartialY hu j (by omega)).comp
      (contDiff_id.prodMk (contDiff_const (c := y₀)))
    rw [show (n + 1 - j : ℕ) = (n - j) + 1 by omega] at this
    exact_mod_cast this
  -- bounds on the remainders
  have hM : ∀ j ∈ range (n + 1), ∃ M, ∀ x ∈ Icc (x₀ - |a|) (x₀ + |a|),
      ‖iteratedDeriv ((n - j) + 1) (fun x => iterPartialY u j x y₀) x‖ ≤ M := fun j hj =>
    isCompact_Icc.exists_bound_of_continuousOn
      ((hg j hj).continuous_iteratedDeriv _ le_rfl).continuousOn
  choose! M hM using hM
  have hK : IsCompact (Icc (x₀ - |a|) (x₀ + |a|) ×ˢ Icc (y₀ - |b|) (y₀ + |b|)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn
    (contDiff_iterPartialY hu (n + 1) le_rfl).continuous.continuousOn
  refine ⟨∑ j ∈ range (n + 1), M j * |a| ^ ((n - j) + 1) / ((n - j) + 1).factorial *
      (|b| ^ j / j.factorial) + M2 * |b| ^ (n + 1) / (n + 1).factorial, fun h hh => ?_⟩
  -- Taylor in `y` at `x = x₀ + ah`
  have hφ : ContDiff ℝ (n + 1) (fun y => u (x₀ + a * h) y) := by
    have := hu.comp ((contDiff_const (c := x₀ + a * h)).prodMk contDiff_id)
    exact_mod_cast this
  obtain ⟨η, hη, hy⟩ := taylor_lagrange_iteratedDeriv hφ y₀ (b * h)
  -- Taylor in `x` for each `g_j`
  have hx : ∀ j ∈ range (n + 1), ∃ ξ ∈ uIcc x₀ (x₀ + a * h),
      iterPartialY u j (x₀ + a * h) y₀ = ∑ i ∈ range ((n - j) + 1),
        iterPartialXY u i j x₀ y₀ * (a * h) ^ i / i.factorial +
        iteratedDeriv ((n - j) + 1) (fun x => iterPartialY u j x y₀) ξ * (a * h) ^ ((n - j) + 1) /
          ((n - j) + 1).factorial := fun j hj =>
    taylor_lagrange_iteratedDeriv (hg j hj) x₀ (a * h)
  choose! ξ hξ hxe using hx
  have hah : |a * h| ≤ |a| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg a) hh
  have hbh : |b * h| ≤ |b| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg b) hh
  -- the difference is a combination of the remainders
  have key : u (x₀ + a * h) (y₀ + b * h) - ∑ j ∈ range (n + 1), ∑ i ∈ range (n + 1 - j),
      iterPartialXY u i j x₀ y₀ * (a * h) ^ i / i.factorial * ((b * h) ^ j / j.factorial) =
      ∑ j ∈ range (n + 1), iteratedDeriv ((n - j) + 1) (fun x => iterPartialY u j x y₀) (ξ j) *
          (a * h) ^ ((n - j) + 1) / ((n - j) + 1).factorial * ((b * h) ^ j / j.factorial) +
        iteratedDeriv (n + 1) (fun y => u (x₀ + a * h) y) η * (b * h) ^ (n + 1) /
          (n + 1).factorial := by
    rw [hy, add_sub_right_comm, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.mp hj
    rw [show n + 1 - j = (n - j) + 1 by omega]
    change iterPartialY u j (x₀ + a * h) y₀ * (b * h) ^ j / j.factorial - _ = _
    rw [hxe j hj, ← sum_mul]
    ring
  rw [key]
  have hRX : ∀ j ∈ range (n + 1),
      |iteratedDeriv ((n - j) + 1) (fun x => iterPartialY u j x y₀) (ξ j) *
      (a * h) ^ ((n - j) + 1) / ((n - j) + 1).factorial * ((b * h) ^ j / j.factorial)| ≤
      M j * |a| ^ ((n - j) + 1) / ((n - j) + 1).factorial * (|b| ^ j / j.factorial) *
        |h| ^ (n + 1) := fun j hj => by
    have hj' := mem_range.mp hj
    have hb := hM j hj (ξ j) (uIcc_subset_Icc_of_abs_le hah (hξ j hj))
    rw [Real.norm_eq_abs] at hb
    rw [abs_mul, abs_div, abs_mul, abs_div, abs_pow, abs_pow, abs_mul, abs_mul,
      Nat.abs_cast, Nat.abs_cast, mul_pow, mul_pow,
      show |h| ^ (n + 1) = |h| ^ ((n - j) + 1) * |h| ^ j by rw [← pow_add]; congr 1; omega]
    have h1 : (0 : ℝ) ≤ |a| ^ ((n - j) + 1) * |h| ^ ((n - j) + 1) /
        ((n - j) + 1).factorial := by positivity
    have h2 : (0 : ℝ) ≤ |b| ^ j * |h| ^ j / j.factorial := by positivity
    calc |iteratedDeriv ((n - j) + 1) (fun x => iterPartialY u j x y₀) (ξ j)| *
          (|a| ^ ((n - j) + 1) * |h| ^ ((n - j) + 1)) / ((n - j) + 1).factorial *
          (|b| ^ j * |h| ^ j / j.factorial)
        = |iteratedDeriv ((n - j) + 1) (fun x => iterPartialY u j x y₀) (ξ j)| *
          (|a| ^ ((n - j) + 1) * |h| ^ ((n - j) + 1) / ((n - j) + 1).factorial) *
          (|b| ^ j * |h| ^ j / j.factorial) := by ring
      _ ≤ M j * (|a| ^ ((n - j) + 1) * |h| ^ ((n - j) + 1) / ((n - j) + 1).factorial) *
          (|b| ^ j * |h| ^ j / j.factorial) := by gcongr
      _ = _ := by ring
  have hRY : |iteratedDeriv (n + 1) (fun y => u (x₀ + a * h) y) η * (b * h) ^ (n + 1) /
      (n + 1).factorial| ≤ M2 * |b| ^ (n + 1) / (n + 1).factorial * |h| ^ (n + 1) := by
    have hb := hM2 (x₀ + a * h, η) ⟨⟨by linarith [abs_le.mp hah], by linarith [abs_le.mp hah]⟩,
      uIcc_subset_Icc_of_abs_le hbh hη⟩
    rw [Real.norm_eq_abs] at hb
    change |iterPartialY u (n + 1) (x₀ + a * h) η| ≤ M2 at hb
    rw [abs_div, abs_mul, abs_pow, Nat.abs_cast, abs_mul, mul_pow]
    calc |iterPartialY u (n + 1) (x₀ + a * h) η| * (|b| ^ (n + 1) * |h| ^ (n + 1)) /
          (n + 1).factorial
        ≤ M2 * (|b| ^ (n + 1) * |h| ^ (n + 1)) / (n + 1).factorial := by gcongr
      _ = _ := by ring
  calc _ ≤ |∑ j ∈ range (n + 1),
          iteratedDeriv ((n - j) + 1) (fun x => iterPartialY u j x y₀) (ξ j) *
          (a * h) ^ ((n - j) + 1) / ((n - j) + 1).factorial * ((b * h) ^ j / j.factorial)| +
        |iteratedDeriv (n + 1) (fun y => u (x₀ + a * h) y) η * (b * h) ^ (n + 1) /
          (n + 1).factorial| := abs_add_le _ _
    _ ≤ ∑ j ∈ range (n + 1), M j * |a| ^ ((n - j) + 1) / ((n - j) + 1).factorial *
          (|b| ^ j / j.factorial) * |h| ^ (n + 1) +
        M2 * |b| ^ (n + 1) / (n + 1).factorial * |h| ^ (n + 1) :=
      add_le_add ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hRX)) hRY
    _ = _ := by rw [← sum_mul, ← add_mul]

/-- The value `∑_{i+j=d} T(i,j) ∂^{i+j}u/∂xⁱ∂yʲ (x₀, y₀)` approximated by a stencil. -/
noncomputable def stencilTarget (u : ℝ → ℝ → ℝ) (N d : ℕ) (T : ℕ → ℕ → ℝ) (x₀ y₀ : ℝ) : ℝ :=
  ∑ j ∈ range N, ∑ i ∈ range (N - j), if i + j = d then T i j * iterPartialXY u i j x₀ y₀ else 0

/-- **Finite-difference stencils**: if the weights `c_k` at the offsets `(A_k, B_k)` reproduce the
target on all monomials of degree `< N` (`∑ c_k A_kⁱ B_kʲ = i! j! T(i,j)` if `i + j = d`, `0` for
the other `i + j < N`), then
`∑_{i+j=d} T(i,j) ∂^{i+j}u(x₀, y₀) − h^{−d} ∑ c_k u(x₀ + A_k h, y₀ + B_k h) = O(h^{N−d})` for
`u ∈ Cᴺ`. -/
theorem stencil_isBigO {u : ℝ → ℝ → ℝ} {N d m : ℕ} (hN : 1 ≤ N) (hdN : d ≤ N)
    (hu : ContDiff ℝ N (Function.uncurry u)) (x₀ y₀ : ℝ) (A B c : Fin m → ℝ)
    (T : ℕ → ℕ → ℝ)
    (hex : ∀ i j, i + j < N → ∑ k, c k * A k ^ i * B k ^ j =
      if i + j = d then (i.factorial * j.factorial : ℝ) * T i j else 0) :
    (fun h : ℝ => stencilTarget u N d T x₀ y₀ -
        (h ^ d)⁻¹ * ∑ k, c k * u (x₀ + A k * h) (y₀ + B k * h)) =O[𝓝[≠] 0]
      fun h => h ^ (N - d) := by
  choose C hC using fun k => taylor2 hN hu x₀ y₀ (A k) (B k)
  set P : Fin m → ℝ → ℝ := fun k h => ∑ j ∈ range N, ∑ i ∈ range (N - j),
    iterPartialXY u i j x₀ y₀ * (A k * h) ^ i / i.factorial * ((B k * h) ^ j / j.factorial)
  have hP : ∀ h : ℝ, ∑ k, c k * P k h = h ^ d * stencilTarget u N d T x₀ y₀ := by
    intro h
    simp only [P, stencilTarget, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    have hij : i + j < N := by have := mem_range.mp hj; have := mem_range.mp hi; omega
    have hsum : ∑ k, c k * (iterPartialXY u i j x₀ y₀ * (A k * h) ^ i / i.factorial *
        ((B k * h) ^ j / j.factorial)) = iterPartialXY u i j x₀ y₀ * h ^ (i + j) /
          (i.factorial * j.factorial) * ∑ k, c k * A k ^ i * B k ^ j := by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by rw [mul_pow, mul_pow, pow_add]; ring
    have hi0 : (i.factorial : ℝ) ≠ 0 := by positivity
    have hj0 : (j.factorial : ℝ) ≠ 0 := by positivity
    rw [hsum, hex i j hij]
    split_ifs with h'
    · rw [h']; field_simp
    · simp
  refine IsBigO.of_bound (∑ k, |c k| * C k) ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) one_pos)]
    with h hh0 hh1
  have hh0' : h ≠ 0 := hh0
  have hh : |h| ≤ 1 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh1; exact hh1.le
  have hd0 : h ^ d ≠ 0 := pow_ne_zero _ hh0'
  have heq : stencilTarget u N d T x₀ y₀ - (h ^ d)⁻¹ * ∑ k, c k * u (x₀ + A k * h) (y₀ + B k * h) =
      -((h ^ d)⁻¹ * ∑ k, c k * (u (x₀ + A k * h) (y₀ + B k * h) - P k h)) := by
    have hs : ∑ k, c k * (u (x₀ + A k * h) (y₀ + B k * h) - P k h) =
        ∑ k, c k * u (x₀ + A k * h) (y₀ + B k * h) - h ^ d * stencilTarget u N d T x₀ y₀ := by
      rw [← hP, ← sum_sub_distrib]; exact sum_congr rfl fun k _ => by ring
    rw [hs]; field_simp; ring_nf
  have hb : |∑ k, c k * (u (x₀ + A k * h) (y₀ + B k * h) - P k h)| ≤
      (∑ k, |c k| * C k) * |h| ^ N := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC k h hh) (abs_nonneg _)
  rw [heq, norm_neg, norm_mul, norm_inv, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  have hpos : 0 < |h| := abs_pos.mpr hh0'
  calc (|h| ^ d)⁻¹ * |∑ k, c k * (u (x₀ + A k * h) (y₀ + B k * h) - P k h)|
      ≤ (|h| ^ d)⁻¹ * ((∑ k, |c k| * C k) * |h| ^ N) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (∑ k, |c k| * C k) * |h| ^ (N - d) := by
        rw [show |h| ^ N = |h| ^ d * |h| ^ (N - d) by rw [← pow_add]; congr 1; omega]
        field_simp

/-! ### The formulas 3.4.20–3.4.34 -/

/-- **DLMF 3.4.27**: the Laplacian `∇²u = ∂²u/∂x² + ∂²u/∂y²`. -/
noncomputable def laplacian (u : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) : ℝ :=
  iterPartialXY u 2 0 x₀ y₀ + iterPartialXY u 0 2 x₀ y₀

/-- **DLMF 3.4.32**: the biharmonic operator `∇⁴u = ∂⁴u/∂x⁴ + 2 ∂⁴u/∂x²∂y² + ∂⁴u/∂y⁴`. -/
noncomputable def biharmonic (u : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) : ℝ :=
  iterPartialXY u 4 0 x₀ y₀ + 2 * iterPartialXY u 2 2 x₀ y₀ + iterPartialXY u 0 4 x₀ y₀

/-- **DLMF 3.4.20**: `∂u_{0,0}/∂x = (u_{1,0} − u_{−1,0})/(2h) + O(h²)`, for `u ∈ C^3`. -/
theorem dlmf_3_4_20 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 3 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => iterPartialXY u 1 0 x₀ y₀ -
      1 / (2 * h) * (u (x₀ + h) y₀ - u (x₀ - h) y₀)) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 3) (d := 1) (by norm_num) (by norm_num) hu x₀ y₀
    ![1, (-1)]
    ![0, 0]
    ![(1 / 2), (-1 / 2)]
    (fun i j => if i = 1 ∧ j = 0 then 1 else 0) (by
      intro i j hij
      have hi : i < 3 := by omega
      have hj : j < 3 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf


/-- **DLMF 3.4.21**: `∂u_{0,0}/∂x = (u_{1,1} − u_{−1,1} + u_{1,−1} − u_{−1,−1})/(4h) +
  O(h²)`, for `u ∈ C^3`. -/
theorem dlmf_3_4_21 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 3 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => iterPartialXY u 1 0 x₀ y₀ -
      1 / (4 * h) * (u (x₀ + h) (y₀ + h) - u (x₀ - h) (y₀ + h) + u (x₀ + h) (y₀ - h) -
        u (x₀ - h) (y₀ - h))) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 3) (d := 1) (by norm_num) (by norm_num) hu x₀ y₀
    ![1, (-1), 1, (-1)]
    ![1, 1, (-1), (-1)]
    ![(1 / 4), (-1 / 4), (1 / 4), (-1 / 4)]
    (fun i j => if i = 1 ∧ j = 0 then 1 else 0) (by
      intro i j hij
      have hi : i < 3 := by omega
      have hj : j < 3 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf


/-- **DLMF 3.4.22**: `∂²u_{0,0}/∂x² = (u_{1,0} − 2u_{0,0} + u_{−1,0})/h² + O(h²)`, for `u ∈ C^4`. -/
theorem dlmf_3_4_22 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 4 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => iterPartialXY u 2 0 x₀ y₀ -
      1 / h ^ 2 * (u (x₀ + h) y₀ - 2 * u x₀ y₀ + u (x₀ - h) y₀)) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 4) (d := 2) (by norm_num) (by norm_num) hu x₀ y₀
    ![1, 0, (-1)]
    ![0, 0, 0]
    ![1, (-2), 1]
    (fun i j => if i = 2 ∧ j = 0 then 1 else 0) (by
      intro i j hij
      have hi : i < 4 := by omega
      have hj : j < 4 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf
  simp


/-- **DLMF 3.4.23**: `∂²u_{0,0}/∂x² = (−u_{2,0} + 16u_{1,0} − 30u_{0,0} +
  16u_{−1,0} − u_{−2,0})/(12h²) + O(h⁴)`, for `u ∈ C^6`. -/
theorem dlmf_3_4_23 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 6 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => iterPartialXY u 2 0 x₀ y₀ -
      1 / (12 * h ^ 2) * (-u (x₀ + 2 * h) y₀ + 16 * u (x₀ + h) y₀ - 30 * u x₀ y₀ +
        16 * u (x₀ - h) y₀ - u (x₀ - 2 * h) y₀)) =O[𝓝[≠] 0] fun h => h ^ 4 := by
  have hs := stencil_isBigO (N := 6) (d := 2) (by norm_num) (by norm_num) hu x₀ y₀
    ![2, 1, 0, (-1), (-2)]
    ![0, 0, 0, 0, 0]
    ![(-1 / 12), (4 / 3), (-5 / 2), (4 / 3), (-1 / 12)]
    (fun i j => if i = 2 ∧ j = 0 then 1 else 0) (by
      intro i j hij
      have hi : i < 6 := by omega
      have hj : j < 6 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf


/-- **DLMF 3.4.24**: `∂²u_{0,0}/∂x²` by the nine-point formula, `+ O(h²)`, for `u ∈ C^4`. -/
theorem dlmf_3_4_24 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 4 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => iterPartialXY u 2 0 x₀ y₀ -
      1 / (3 * h ^ 2) * (u (x₀ + h) (y₀ + h) - 2 * u x₀ (y₀ + h) + u (x₀ - h) (y₀ + h) +
        u (x₀ + h) y₀ - 2 * u x₀ y₀ + u (x₀ - h) y₀ + u (x₀ + h) (y₀ - h) -
        2 * u x₀ (y₀ - h) + u (x₀ - h) (y₀ - h))) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 4) (d := 2) (by norm_num) (by norm_num) hu x₀ y₀
    ![1, 0, (-1), 1, 0, (-1), 1, 0, (-1)]
    ![1, 1, 1, 0, 0, 0, (-1), (-1), (-1)]
    ![(1 / 3), (-2 / 3), (1 / 3), (1 / 3), (-2 / 3), (1 / 3), (1 / 3), (-2 / 3), (1 / 3)]
    (fun i j => if i = 2 ∧ j = 0 then 1 else 0) (by
      intro i j hij
      have hi : i < 4 := by omega
      have hj : j < 4 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf


/-- **DLMF 3.4.25**: `∂²u_{0,0}/∂x∂y = (u_{1,1} − u_{1,−1} − u_{−1,1} + u_{−1,−1})/(4h²) +
  O(h²)`, for `u ∈ C^4`. -/
theorem dlmf_3_4_25 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 4 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => iterPartialXY u 1 1 x₀ y₀ -
      1 / (4 * h ^ 2) * (u (x₀ + h) (y₀ + h) - u (x₀ + h) (y₀ - h) - u (x₀ - h) (y₀ + h) +
        u (x₀ - h) (y₀ - h))) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 4) (d := 2) (by norm_num) (by norm_num) hu x₀ y₀
    ![1, 1, (-1), (-1)]
    ![1, (-1), 1, (-1)]
    ![(1 / 4), (-1 / 4), (-1 / 4), (1 / 4)]
    (fun i j => if i = 1 ∧ j = 1 then 1 else 0) (by
      intro i j hij
      have hi : i < 4 := by omega
      have hj : j < 4 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf


/-- **DLMF 3.4.26**: `∂²u_{0,0}/∂x∂y = −(u_{1,0} + u_{−1,0} + u_{0,1} +
  u_{0,−1} − 2u_{0,0} − u_{1,1} − u_{−1,−1})/(2h²) + O(h²)`, for `u ∈ C^4`. -/
theorem dlmf_3_4_26 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 4 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => iterPartialXY u 1 1 x₀ y₀ -
      -(1 / (2 * h ^ 2)) * (u (x₀ + h) y₀ + u (x₀ - h) y₀ + u x₀ (y₀ + h) +
        u x₀ (y₀ - h) - 2 * u x₀ y₀ - u (x₀ + h) (y₀ + h) - u (x₀ - h) (y₀ -
          h))) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 4) (d := 2) (by norm_num) (by norm_num) hu x₀ y₀
    ![1, (-1), 0, 0, 0, 1, (-1)]
    ![0, 0, 1, (-1), 0, 1, (-1)]
    ![(-1 / 2), (-1 / 2), (-1 / 2), (-1 / 2), 1, (1 / 2), (1 / 2)]
    (fun i j => if i = 1 ∧ j = 1 then 1 else 0) (by
      intro i j hij
      have hi : i < 4 := by omega
      have hj : j < 4 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf


/-- **DLMF 3.4.28**: `∇²u_{0,0} = (u_{1,0} + u_{0,1} + u_{−1,0} + u_{0,−1} − 4u_{0,0})/h² +
  O(h²)`, for `u ∈ C^4`. -/
theorem dlmf_3_4_28 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 4 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => laplacian u x₀ y₀ -
      1 / h ^ 2 * (u (x₀ + h) y₀ + u x₀ (y₀ + h) + u (x₀ - h) y₀ + u x₀ (y₀ - h) -
        4 * u x₀ y₀)) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 4) (d := 2) (by norm_num) (by norm_num) hu x₀ y₀
    ![1, 0, (-1), 0, 0]
    ![0, 1, 0, (-1), 0]
    ![1, 1, 1, 1, (-4)]
    (fun i j => if i = 2 ∧ j = 0 ∨ i = 0 ∧ j = 2 then 1 else 0) (by
      intro i j hij
      have hi : i < 4 := by omega
      have hj : j < 4 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, laplacian, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf
  simp


/-- **DLMF 3.4.29**: `∇²u_{0,0}` by the thirteen-point formula, `+ O(h⁴)`, for `u ∈ C^6`. -/
theorem dlmf_3_4_29 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 6 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => laplacian u x₀ y₀ -
      1 / (12 * h ^ 2) * (-60 * u x₀ y₀ +
        16 * (u (x₀ + h) y₀ + u x₀ (y₀ + h) + u (x₀ - h) y₀ + u x₀ (y₀ - h)) -
        (u (x₀ + 2 * h) y₀ + u x₀ (y₀ + 2 * h) + u (x₀ - 2 * h) y₀ + u x₀ (y₀ -
          2 * h)))) =O[𝓝[≠] 0] fun h => h ^ 4 := by
  have hs := stencil_isBigO (N := 6) (d := 2) (by norm_num) (by norm_num) hu x₀ y₀
    ![0, 1, 0, (-1), 0, 2, 0, (-2), 0]
    ![0, 0, 1, 0, (-1), 0, 2, 0, (-2)]
    ![(-5), (4 / 3), (4 / 3), (4 / 3), (4 / 3), (-1 / 12), (-1 / 12), (-1 / 12), (-1 / 12)]
    (fun i j => if i = 2 ∧ j = 0 ∨ i = 0 ∧ j = 2 then 1 else 0) (by
      intro i j hij
      have hi : i < 6 := by omega
      have hj : j < 6 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, laplacian, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf


/-- **DLMF 3.4.30**: `∂⁴u_{0,0}/∂x⁴ = (u_{2,0} − 4u_{1,0} + 6u_{0,0} − 4u_{−1,0} + u_{−2,0})/h⁴ +
  O(h²)`, for `u ∈ C^6`. -/
theorem dlmf_3_4_30 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 6 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => iterPartialXY u 4 0 x₀ y₀ -
      1 / h ^ 4 * (u (x₀ + 2 * h) y₀ - 4 * u (x₀ + h) y₀ + 6 * u x₀ y₀ -
        4 * u (x₀ - h) y₀ + u (x₀ - 2 * h) y₀)) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 6) (d := 4) (by norm_num) (by norm_num) hu x₀ y₀
    ![2, 1, 0, (-1), (-2)]
    ![0, 0, 0, 0, 0]
    ![1, (-4), 6, (-4), 1]
    (fun i j => if i = 4 ∧ j = 0 then 1 else 0) (by
      intro i j hij
      have hi : i < 6 := by omega
      have hj : j < 6 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf
  simp


/-- **DLMF 3.4.31**: `∂⁴u_{0,0}/∂x²∂y²` by the nine-point formula, `+ O(h²)`, for `u ∈ C^6`. -/
theorem dlmf_3_4_31 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 6 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => iterPartialXY u 2 2 x₀ y₀ -
      1 / h ^ 4 * (u (x₀ + h) (y₀ + h) + u (x₀ - h) (y₀ + h) + u (x₀ + h) (y₀ - h) +
        u (x₀ - h) (y₀ -
        h) -
        2 * u (x₀ + h) y₀ - 2 * u (x₀ - h) y₀ - 2 * u x₀ (y₀ + h) -
        2 * u x₀ (y₀ - h) + 4 * u x₀ y₀)) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 6) (d := 4) (by norm_num) (by norm_num) hu x₀ y₀
    ![1, (-1), 1, (-1), 1, (-1), 0, 0, 0]
    ![1, 1, (-1), (-1), 0, 0, 1, (-1), 0]
    ![1, 1, 1, 1, (-2), (-2), (-2), (-2), 4]
    (fun i j => if i = 2 ∧ j = 2 then 1 else 0) (by
      intro i j hij
      have hi : i < 6 := by omega
      have hj : j < 6 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf
  simp


/-- **DLMF 3.4.33**: `∇⁴u_{0,0}` by the thirteen-point formula, `+ O(h²)`, for `u ∈ C^6`. -/
theorem dlmf_3_4_33 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 6 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => biharmonic u x₀ y₀ -
      1 / h ^ 4 * (20 * u x₀ y₀ -
        8 * (u (x₀ + h) y₀ + u x₀ (y₀ + h) + u (x₀ - h) y₀ + u x₀ (y₀ - h)) +
        2 * (u (x₀ + h) (y₀ + h) + u (x₀ + h) (y₀ - h) + u (x₀ - h) (y₀ + h) + u (x₀ - h) (y₀ -
          h)) +
        (u x₀ (y₀ + 2 * h) + u (x₀ + 2 * h) y₀ + u (x₀ - 2 * h) y₀ + u x₀ (y₀ -
          2 * h)))) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have hs := stencil_isBigO (N := 6) (d := 4) (by norm_num) (by norm_num) hu x₀ y₀
    ![0, 1, 0, (-1), 0, 1, 1, (-1), (-1), 0, 2, (-2), 0]
    ![0, 0, 1, 0, (-1), 1, (-1), 1, (-1), 2, 0, 0, (-2)]
    ![20, (-8), (-8), (-8), (-8), 2, 2, 2, 2, 1, 1, 1, 1]
    (fun i j => if i = 4 ∧ j = 0 ∨ i = 0 ∧ j = 4 then 1 else if i = 2 ∧ j = 2 then 2 else 0) (by
      intro i j hij
      have hi : i < 6 := by omega
      have hj : j < 6 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, biharmonic, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf
  simp


set_option maxHeartbeats 1000000 in
/-- **DLMF 3.4.34**: `∇⁴u_{0,0}` by the twenty-five-point formula, `+ O(h⁴)`, for `u ∈ C^8`. -/
theorem dlmf_3_4_34 {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 8 (Function.uncurry u)) (x₀ y₀ : ℝ) :
    (fun h : ℝ => biharmonic u x₀ y₀ -
      1 / (6 * h ^ 4) * (184 * u x₀ y₀ -
        (u x₀ (y₀ + 3 * h) + u x₀ (y₀ - 3 * h) + u (x₀ + 3 * h) y₀ + u (x₀ - 3 * h) y₀) +
        14 * (u x₀ (y₀ + 2 * h) + u x₀ (y₀ - 2 * h) + u (x₀ + 2 * h) y₀ + u (x₀ - 2 * h) y₀) -
        77 * (u x₀ (y₀ + h) + u x₀ (y₀ - h) + u (x₀ + h) y₀ + u (x₀ - h) y₀) +
        20 * (u (x₀ + h) (y₀ + h) + u (x₀ + h) (y₀ - h) + u (x₀ - h) (y₀ + h) + u (x₀ - h) (y₀ -
          h)) -
        (u (x₀ + h) (y₀ + 2 * h) + u (x₀ + 2 * h) (y₀ + h) + u (x₀ + h) (y₀ - 2 * h) + u (x₀ +
          2 * h) (y₀ - h) + u (x₀ - h) (y₀ + 2 * h) + u (x₀ - 2 * h) (y₀ + h) +
          u (x₀ - h) (y₀ - 2 * h) + u (x₀ - 2 * h) (y₀ - h)))) =O[𝓝[≠] 0] fun h => h ^ 4 := by
  have hs := stencil_isBigO (N := 8) (d := 4) (by norm_num) (by norm_num) hu x₀ y₀
    ![0, 0, 0, 3, (-3), 0, 0, 2, (-2), 0, 0, 1, (-1), 1, 1, (-1), (-1), 1, 2, 1, 2, (-1), (-2),
      (-1), (-2)]
    ![0, 3, (-3), 0, 0, 2, (-2), 0, 0, 1, (-1), 0, 0, 1, (-1), 1, (-1), 2, 1, (-2), (-1), 2, 1,
      (-2), (-1)]
    ![(92 / 3), (-1 / 6), (-1 / 6), (-1 / 6), (-1 / 6), (7 / 3), (7 / 3), (7 / 3), (7 / 3),
      (-77 / 6), (-77 / 6), (-77 / 6), (-77 / 6), (10 / 3), (10 / 3), (10 / 3), (10 / 3), (-1 / 6),
      (-1 / 6), (-1 / 6), (-1 / 6), (-1 / 6), (-1 / 6), (-1 / 6), (-1 / 6)]
    (fun i j => if i = 4 ∧ j = 0 ∨ i = 0 ∧ j = 4 then 1 else if i = 2 ∧ j = 2 then 2 else 0) (by
      intro i j hij
      have hi : i < 8 := by omega
      have hj : j < 8 := by omega
      interval_cases i <;> interval_cases j <;> simp_all [Fin.sum_univ_succ, Nat.factorial] <;>
        norm_num)
  refine hs.congr' ?_ (Eventually.of_forall fun h => rfl)
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [stencilTarget, biharmonic, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring_nf

end Azurite.DLMF
