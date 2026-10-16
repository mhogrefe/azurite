/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.Newton
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Brent–Zimmermann §4.2.1: Newton's method for inverse roots

Newton's method applied to `f(x) = y − x^(−m)` for a positive integer `m` and a positive constant
`y`.  Since `f'(x) = m x^(−(m+1))`, the step simplifies to

  `x_{j+1} = x_j + x_j (1 − x_j^m y) / m`                                              (4.4)

which involves no division except by the integer `m`, and converges to `ζ = y^(−1/m)` from any
start close enough to `ζ`.  The cases `m = 1` (reciprocal) and `m = 2` (reciprocal square root)
are the subjects of §4.2.2 and §4.2.3.

* `inverseRootFun m y`, `inverseRootFun' m`, `inverseRootFun'' m` — `f`, `f'`, `f''` as
  `y − 1/x^m`, `m / x^(m+1)`, `−m(m+1) / x^(m+2)`, with `hasDerivAt_inverseRootFun`,
  `hasDerivAt_inverseRootFun'`.
* `inverseRootStep m y` — the step (4.4); `newtonStep_inverseRootFun` says it is Newton's step
  for `f` at every `x ≠ 0`.  `inverseRootSeq` iterates it.
* `inverseRootFun_root` — `ζ = y^(−1/m)` is the zero, `ζ^m y = 1` (`rpow_neg_inv_pow_mul`).
* `inverseRootStep_rel` — the step in terms of the relative error, `x = ζ (1 + ε)` goes to
  `ζ (1 + ε) (1 + (1 − (1 + ε)^m) / m)`, which is how §4.2.2–4.2.3 analyse the error.
* `exists_tendsto_inverseRootSeq` — local convergence: there is `δ > 0` such that from every
  `x₀` with `|x₀ − ζ| ≤ δ` the iterates of (4.4) converge to `ζ`, staying within `ζ/2` of it.
-/

namespace Azurite

namespace BZ

open Set Filter Topology

/-- `f(x) = y − x^(−m)`, written with the inverse of the natural power. -/
noncomputable def inverseRootFun (m : ℕ) (y x : ℝ) : ℝ := y - (x ^ m)⁻¹

/-- `f'(x) = m x^(−(m+1))`. -/
noncomputable def inverseRootFun' (m : ℕ) (x : ℝ) : ℝ := m / x ^ (m + 1)

/-- `f''(x) = −m(m+1) x^(−(m+2))`. -/
noncomputable def inverseRootFun'' (m : ℕ) (x : ℝ) : ℝ := -(m * (m + 1)) / x ^ (m + 2)

/-- The division-free Newton step (4.4), `x + x (1 − x^m y) / m`. -/
noncomputable def inverseRootStep (m : ℕ) (y x : ℝ) : ℝ := x + x * (1 - x ^ m * y) / m

/-- The iterates of (4.4) from `x₀`. -/
noncomputable def inverseRootSeq (m : ℕ) (y x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => inverseRootStep m y (inverseRootSeq m y x₀ n)

@[simp] theorem inverseRootSeq_zero (m : ℕ) (y x₀ : ℝ) : inverseRootSeq m y x₀ 0 = x₀ := rfl

@[simp] theorem inverseRootSeq_succ (m : ℕ) (y x₀ : ℝ) (n : ℕ) :
    inverseRootSeq m y x₀ (n + 1) = inverseRootStep m y (inverseRootSeq m y x₀ n) := rfl

theorem hasDerivAt_inverseRootFun {m : ℕ} (hm : 0 < m) (y : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (inverseRootFun m y) (inverseRootFun' m x) x := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h : HasDerivAt (fun x => y - (x ^ (k + 1))⁻¹)
      (0 - -(((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1)) / (x ^ (k + 1)) ^ 2) x :=
    (hasDerivAt_const x y).sub ((hasDerivAt_pow (k + 1) x).inv (pow_ne_zero _ hx))
  refine h.congr_deriv ?_
  unfold inverseRootFun'
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

theorem hasDerivAt_inverseRootFun' (m : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (inverseRootFun' m) (inverseRootFun'' m x) x := by
  have h : HasDerivAt (fun x => (m : ℝ) * (x ^ (m + 1))⁻¹)
      ((m : ℝ) * (-(((m + 1 : ℕ) : ℝ) * x ^ (m + 1 - 1)) / (x ^ (m + 1)) ^ 2)) x :=
    ((hasDerivAt_pow (m + 1) x).inv (pow_ne_zero _ hx)).const_mul (m : ℝ)
  have hfun : inverseRootFun' m = fun x => (m : ℝ) * (x ^ (m + 1))⁻¹ := by
    funext x; simp [inverseRootFun', div_eq_mul_inv]
  rw [hfun]
  refine h.congr_deriv ?_
  unfold inverseRootFun''
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- (4.4) is Newton's step for `f(x) = y − x^(−m)` at every `x ≠ 0`. -/
theorem newtonStep_inverseRootFun {m : ℕ} (hm : 0 < m) (y : ℝ) {x : ℝ} (hx : x ≠ 0) :
    newtonStep (inverseRootFun m y) (inverseRootFun' m) x = inverseRootStep m y x := by
  unfold newtonStep inverseRootFun inverseRootFun' inverseRootStep
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

/-- `(y^(−1/m))^m · y = 1` for `y > 0`, `m > 0`. -/
theorem rpow_neg_inv_pow_mul {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 0 < y) :
    (y ^ (-(1 / (m : ℝ)))) ^ m * y = 1 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le,
    show -(1 / (m : ℝ)) * (m : ℕ) = -1 by field_simp, Real.rpow_neg_one, inv_mul_cancel₀ hy.ne']

/-- `ζ = y^(−1/m)` is a zero of `f`. -/
theorem inverseRootFun_root {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 0 < y) :
    inverseRootFun m y (y ^ (-(1 / (m : ℝ)))) = 0 := by
  unfold inverseRootFun
  have h := rpow_neg_inv_pow_mul hm hy
  rw [sub_eq_zero, eq_comm, inv_eq_iff_eq_inv]
  exact eq_inv_of_mul_eq_one_left h

/-- The step (4.4) in terms of the relative error: if `ζ^m y = 1` then
`x = ζ (1 + ε)` is sent to `ζ (1 + ε) (1 + (1 − (1 + ε)^m) / m)`. -/
theorem inverseRootStep_rel (m : ℕ) {y ζ : ℝ} (hζ : ζ ^ m * y = 1) (ε : ℝ) :
    inverseRootStep m y (ζ * (1 + ε)) = ζ * ((1 + ε) * (1 + (1 - (1 + ε) ^ m) / m)) := by
  have h : (ζ * (1 + ε)) ^ m * y = (1 + ε) ^ m := by rw [mul_pow, mul_right_comm, hζ, one_mul]
  unfold inverseRootStep
  rw [h]
  ring

/-- The zero `ζ = y^(−1/m)` is positive. -/
theorem inverseRoot_pos {m : ℕ} {y : ℝ} (hy : 0 < y) : 0 < y ^ (-(1 / (m : ℝ))) :=
  Real.rpow_pos_of_pos hy _

/-- Local convergence of (4.4): for `y > 0` there is `δ > 0` such that from every start `x₀`
with `|x₀ − ζ| ≤ δ`, `ζ = y^(−1/m)`, the iterates stay within `ζ/2` of `ζ`, agree with Newton's
iterates for `f`, and converge to `ζ`. -/
theorem exists_tendsto_inverseRootSeq {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 0 < y) :
    ∃ δ > 0, ∀ x₀, |x₀ - y ^ (-(1 / (m : ℝ)))| ≤ δ →
      (∀ n, |inverseRootSeq m y x₀ n - y ^ (-(1 / (m : ℝ)))| ≤ y ^ (-(1 / (m : ℝ))) / 2) ∧
      (∀ n, inverseRootSeq m y x₀ n
        = newtonSeq (inverseRootFun m y) (inverseRootFun' m) x₀ n) ∧
      Tendsto (inverseRootSeq m y x₀) atTop (𝓝 (y ^ (-(1 / (m : ℝ))))) := by
  set ζ := y ^ (-(1 / (m : ℝ))) with hζ_def
  have hζ : 0 < ζ := inverseRoot_pos hy
  have hroot : inverseRootFun m y ζ = 0 := inverseRootFun_root hm hy
  set r := ζ / 2 with hr
  have hr0 : 0 < r := by positivity
  -- every point of the interval is at least `ζ/2` and at most `3ζ/2`
  have hI : ∀ t ∈ Icc (ζ - r) (ζ + r), ζ / 2 ≤ t ∧ t ≤ 3 * ζ / 2 := by
    intro t ht; constructor <;> linarith [ht.1, ht.2]
  have hIpos : ∀ t ∈ Icc (ζ - r) (ζ + r), 0 < t := fun t ht => by linarith [(hI t ht).1]
  -- the derivative bounds
  set M : ℝ := (m * (m + 1) : ℝ) / (ζ / 2) ^ (m + 2) with hM_def
  set mlo : ℝ := (m : ℝ) / (3 * ζ / 2) ^ (m + 1) with hmlo_def
  have hmlo : 0 < mlo := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hM : ∀ t ∈ Icc (ζ - r) (ζ + r), |inverseRootFun'' m t| ≤ M := by
    intro t ht
    have ht0 := hIpos t ht
    unfold inverseRootFun''
    rw [abs_div, abs_neg, abs_of_nonneg (by positivity), abs_of_pos (by positivity), hM_def]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity) (hI t ht).1 _
  have hm' : ∀ t ∈ Icc (ζ - r) (ζ + r), mlo ≤ |inverseRootFun' m t| := by
    intro t ht
    have ht0 := hIpos t ht
    unfold inverseRootFun'
    rw [abs_of_pos (by positivity), hmlo_def]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ ht0.le (hI t ht).2 _
  have hf : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt (inverseRootFun m y) (inverseRootFun' m t) t :=
    fun t ht => hasDerivAt_inverseRootFun hm y (hIpos t ht).ne'
  have hf' : ∀ t ∈ Icc (ζ - r) (ζ + r),
      HasDerivAt (inverseRootFun' m) (inverseRootFun'' m t) t :=
    fun t ht => hasDerivAt_inverseRootFun' m (hIpos t ht).ne'
  set K := M / (2 * mlo) with hK_def
  have hK0 : 0 < K := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  refine ⟨min r (1 / (2 * K)), lt_min hr0 (by positivity), fun x₀ hx₀ => ?_⟩
  have hx₀r : |x₀ - ζ| ≤ r := hx₀.trans (min_le_left _ _)
  have hx₀K : K * |x₀ - ζ| ≤ 1 / 2 := by
    have h := hx₀.trans (min_le_right _ _)
    calc K * |x₀ - ζ| ≤ K * (1 / (2 * K)) := mul_le_mul_of_nonneg_left h hK0.le
      _ = 1 / 2 := by field_simp
  have hbounds := fun n => newtonSeq_bounds hmlo hroot hf hf' hM hm' hx₀r hx₀K n
  -- the iterates of (4.4) are Newton's iterates, since they never vanish
  have heq : ∀ n, inverseRootSeq m y x₀ n
      = newtonSeq (inverseRootFun m y) (inverseRootFun' m) x₀ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [inverseRootSeq_succ, newtonSeq_succ, ih]
      have hn := (hbounds n).1
      have hne : newtonSeq (inverseRootFun m y) (inverseRootFun' m) x₀ n ≠ 0 := by
        rw [abs_le] at hn
        have : 0 < newtonSeq (inverseRootFun m y) (inverseRootFun' m) x₀ n := by
          linarith [hn.1]
        exact this.ne'
      exact (newtonStep_inverseRootFun hm y hne).symm
  refine ⟨fun n => ?_, heq, ?_⟩
  · rw [heq]; exact (hbounds n).1
  · have h := tendsto_newtonSeq hmlo hroot hf hf' hM hm' hx₀r hx₀K
    exact h.congr (fun n => (heq n).symm)

end BZ

end Azurite
