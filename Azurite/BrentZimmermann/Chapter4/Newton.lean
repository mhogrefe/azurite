/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Brent–Zimmermann §4.2: Newton's method via linearization

The opening of *Modern Computer Arithmetic* (MCA) §4.2, for a real function `f` with a simple
zero `ζ`.  The text derives Newton's iteration `x_{j+1} = x_j − f(x_j) / f'(x_j)` (4.2) from
Taylor's theorem at `x_0` (4.1), states that the error at least halves once the start is close
enough, that the convergence is (at least) quadratic, `|e_{n+1}| ≤ K |e_n|²`, and (4.3) that the
error constant is `f''(ζ) / (2 f'(ζ))` when `f` is three times differentiable.

Everything is stated with explicit derivatives (`HasDerivAt f (f' t) t` on the relevant
interval) and explicit constants, which is what the later algorithms need; the `O(·)` statements
of the text are the special cases.

* `taylor_one`, `taylor_two`, `taylor_three` — Taylor's theorem with the Lagrange remainder,
  between any two distinct points in either order (`uIcc`), through the Cauchy mean value theorem.
* `newtonStep`, `newtonSeq` — the iteration (4.2).
* `newtonStep_sub_root` — (4.1) rearranged: `x_1 − ζ = (x_0 − ζ)² f''(ξ) / (2 f'(x_0))`.
* `abs_newtonStep_sub_root_le` — `|e_1| ≤ K e_0²` with `K = M / (2m)` for `|f''| ≤ M` and
  `|f'| ≥ m` near the zero.
* `newtonSeq_bounds` — from a start with `K |e_0| ≤ 1/2`: the iterates stay in the interval,
  each error at least halves, and `K |e_n| ≤ (K |e_0|)^(2^n)`; `abs_newtonSeq_sub_root_le`,
  `tendsto_newtonSeq`.
* `newtonStep_sub_root_cubic` — (4.3) with an explicit constant:
  `|e_1 − f''(ζ)/(2 f'(ζ)) · e_0²| ≤ (7 M₃ / (6 m) + M₂² / (2 m²)) |e_0|³`.
-/

namespace Azurite

namespace BZ

open Set Filter Topology

/-! ### Taylor's theorem with the Lagrange remainder, in either direction -/

/-- The Cauchy mean value theorem between two distinct points in either order. -/
theorem exists_uIoo_ratio_eq {g g' h h' : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hg : ∀ t ∈ uIcc a b, HasDerivAt g (g' t) t) (hh : ∀ t ∈ uIcc a b, HasDerivAt h (h' t) t) :
    ∃ c ∈ uIoo a b, (h b - h a) * g' c = (g b - g a) * h' c := by
  have hgc : ContinuousOn g (uIcc a b) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (uIcc a b) := fun t ht => (hh t ht).continuousAt.continuousWithinAt
  have hg' : ∀ t ∈ uIoo a b, HasDerivAt g (g' t) t := fun t ht => hg t (Ioo_subset_Icc_self ht)
  have hh' : ∀ t ∈ uIoo a b, HasDerivAt h (h' t) t := fun t ht => hh t (Ioo_subset_Icc_self ht)
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have hI : uIcc a b = Icc a b := uIcc_of_le hlt.le
    have hO : uIoo a b = Ioo a b := by
      rw [uIoo, inf_eq_left.mpr hlt.le, sup_eq_right.mpr hlt.le]
    rw [hI] at hgc hhc
    rw [hO] at hg' hh' ⊢
    exact exists_ratio_hasDerivAt_eq_ratio_slope g g' hlt hgc hg' h h' hhc hh'
  · have hI : uIcc a b = Icc b a := uIcc_of_ge hlt.le
    have hO : uIoo a b = Ioo b a := by
      rw [uIoo, inf_eq_right.mpr hlt.le, sup_eq_left.mpr hlt.le]
    rw [hI] at hgc hhc
    rw [hO] at hg' hh' ⊢
    obtain ⟨c, hc, h⟩ := exists_ratio_hasDerivAt_eq_ratio_slope g g' hlt hgc hg' h h' hhc hh'
    exact ⟨c, hc, by linear_combination -h⟩

/-- The mean value theorem: `f b = f a + (b − a) f'(ξ)`. -/
theorem taylor_one {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t) :
    ∃ ξ ∈ uIoo a b, f b = f a + (b - a) * f' ξ := by
  obtain ⟨c, hc, h⟩ := exists_uIoo_ratio_eq hab hf (h := id) (h' := fun _ => 1)
    (fun t _ => hasDerivAt_id t)
  exact ⟨c, hc, by simp only [id] at h; linear_combination -h⟩

/-- Taylor's theorem to order two (MCA (4.1)): `f b = f a + (b − a) f'(a) + (b − a)²/2 f''(ξ)`. -/
theorem taylor_two {f f' f'' : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ uIcc a b, HasDerivAt f' (f'' t) t) :
    ∃ ξ ∈ uIoo a b, f b = f a + (b - a) * f' a + (b - a) ^ 2 / 2 * f'' ξ := by
  -- `g t = f b − f t − (b − t) f'(t)` and `h t = (b − t)²` both vanish at `b`
  have hg : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t => f b - f t - (b - t) * f' t) (-((b - t) * f'' t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => f b - f t - (b - t) * f' t)
        (0 - f' t - (-1 * f' t + (b - t) * f'' t)) t :=
      ((hasDerivAt_const t (f b)).sub (hf t ht)).sub
        (((hasDerivAt_id t).const_sub b).mul (hf' t ht))
    exact h1.congr_deriv (by ring)
  have hh : ∀ t ∈ uIcc a b, HasDerivAt (fun t => (b - t) ^ 2) (-(2 * (b - t))) t := by
    intro t _
    have h1 : HasDerivAt (fun t => (b - t) ^ 2) (((2 : ℕ) : ℝ) * (b - t) ^ (2 - 1) * -1) t :=
      ((hasDerivAt_id t).const_sub b).pow 2
    exact h1.congr_deriv (by norm_num)
  obtain ⟨c, hc, h⟩ := exists_uIoo_ratio_eq hab hg hh
  refine ⟨c, hc, ?_⟩
  have hbc : b - c ≠ 0 := by
    rcases hc with ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · rw [sup_eq_right.mpr hlt.le] at h2; exact (sub_pos.mpr h2).ne'
    · rw [inf_eq_right.mpr hlt.le] at h1; exact (sub_neg.mpr h1).ne
  simp only [sub_self, zero_pow two_ne_zero, zero_sub] at h
  have h2 : (b - c) * (f b - f a - (b - a) * f' a - (b - a) ^ 2 / 2 * f'' c) = 0 := by
    linear_combination -h / 2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hbc
  · linear_combination h3

/-- Taylor's theorem to order three:
`f b = f a + (b − a) f'(a) + (b − a)²/2 f''(a) + (b − a)³/6 f'''(ξ)`. -/
theorem taylor_three {f f' f'' f''' : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ uIcc a b, HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t ∈ uIcc a b, HasDerivAt f'' (f''' t) t) :
    ∃ ξ ∈ uIoo a b,
      f b = f a + (b - a) * f' a + (b - a) ^ 2 / 2 * f'' a + (b - a) ^ 3 / 6 * f''' ξ := by
  have hg : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t => f b - f t - (b - t) * f' t - (b - t) ^ 2 / 2 * f'' t)
        (-((b - t) ^ 2 / 2 * f''' t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => f b - f t - (b - t) * f' t - (b - t) ^ 2 / 2 * f'' t)
        (0 - f' t - (-1 * f' t + (b - t) * f'' t)
          - (((2 : ℕ) : ℝ) * (b - t) ^ (2 - 1) * -1 / 2 * f'' t + (b - t) ^ 2 / 2 * f''' t)) t :=
      (((hasDerivAt_const t (f b)).sub (hf t ht)).sub
        (((hasDerivAt_id t).const_sub b).mul (hf' t ht))).sub
        ((((hasDerivAt_id t).const_sub b).pow 2).div_const 2 |>.mul (hf'' t ht))
    exact h1.congr_deriv (by norm_num; ring)
  have hh : ∀ t ∈ uIcc a b, HasDerivAt (fun t => (b - t) ^ 3) (-(3 * (b - t) ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun t => (b - t) ^ 3) (((3 : ℕ) : ℝ) * (b - t) ^ (3 - 1) * -1) t :=
      ((hasDerivAt_id t).const_sub b).pow 3
    exact h1.congr_deriv (by norm_num)
  obtain ⟨c, hc, h⟩ := exists_uIoo_ratio_eq hab hg hh
  refine ⟨c, hc, ?_⟩
  have hbc : b - c ≠ 0 := by
    rcases hc with ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · rw [sup_eq_right.mpr hlt.le] at h2; exact (sub_pos.mpr h2).ne'
    · rw [inf_eq_right.mpr hlt.le] at h1; exact (sub_neg.mpr h1).ne
  simp only [sub_self, zero_pow two_ne_zero, zero_pow three_ne_zero, zero_mul, zero_sub,
    zero_div] at h
  have h2 : (b - c) ^ 2 * (f b - f a - (b - a) * f' a - (b - a) ^ 2 / 2 * f'' a
      - (b - a) ^ 3 / 6 * f''' c) = 0 := by
    linear_combination -h / 3
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h3) hbc
  · linear_combination h3

/-! ### Newton's iteration -/

/-- One Newton step `x − f(x) / f'(x)`, (4.2). -/
noncomputable def newtonStep (f f' : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / f' x

/-- The Newton iterates `x_0, x_1, …` from `x₀`, (4.2). -/
noncomputable def newtonSeq (f f' : ℝ → ℝ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => newtonStep f f' (newtonSeq f f' x₀ n)

@[simp] theorem newtonSeq_zero (f f' : ℝ → ℝ) (x₀ : ℝ) : newtonSeq f f' x₀ 0 = x₀ := rfl

@[simp] theorem newtonSeq_succ (f f' : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    newtonSeq f f' x₀ (n + 1) = newtonStep f f' (newtonSeq f f' x₀ n) := rfl

/-- A zero is a fixed point of the step (when `f'` does not vanish there, or indeed always,
since `0 / f'(ζ) = 0`). -/
theorem newtonStep_root {f f' : ℝ → ℝ} {ζ : ℝ} (hζ : f ζ = 0) : newtonStep f f' ζ = ζ := by
  simp [newtonStep, hζ]

/-- (4.1) rearranged: the error after one Newton step from `x₀ ≠ ζ`,
`x_1 − ζ = (x_0 − ζ)² f''(ξ) / (2 f'(x_0))` for some `ξ` strictly between `x_0` and `ζ`. -/
theorem newtonStep_sub_root {f f' f'' : ℝ → ℝ} {x₀ ζ : ℝ} (hne : x₀ ≠ ζ) (hζ : f ζ = 0)
    (hd : f' x₀ ≠ 0) (hf : ∀ t ∈ uIcc x₀ ζ, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ uIcc x₀ ζ, HasDerivAt f' (f'' t) t) :
    ∃ ξ ∈ uIoo x₀ ζ, newtonStep f f' x₀ - ζ = (x₀ - ζ) ^ 2 * f'' ξ / (2 * f' x₀) := by
  obtain ⟨ξ, hξ, h⟩ := taylor_two hne hf hf'
  refine ⟨ξ, hξ, ?_⟩
  rw [hζ] at h
  have hfx : f x₀ = -(ζ - x₀) * f' x₀ - (ζ - x₀) ^ 2 / 2 * f'' ξ := by linear_combination -h
  unfold newtonStep
  rw [hfx]
  field_simp
  ring

/-- The quadratic error bound `|e_1| ≤ K e_0²`, `K = M / (2m)`, on the closed interval of radius
`r` about the zero, where `|f''| ≤ M` and `|f'| ≥ m > 0`. -/
theorem abs_newtonStep_sub_root_le {f f' f'' : ℝ → ℝ} {ζ r M m : ℝ} (hm : 0 < m) (hζ : f ζ = 0)
    (hf : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ Icc (ζ - r) (ζ + r), |f'' t| ≤ M)
    (hm' : ∀ t ∈ Icc (ζ - r) (ζ + r), m ≤ |f' t|) {x₀ : ℝ} (hx₀ : |x₀ - ζ| ≤ r) :
    |newtonStep f f' x₀ - ζ| ≤ M / (2 * m) * (x₀ - ζ) ^ 2 := by
  have hx₀I : x₀ ∈ Icc (ζ - r) (ζ + r) := by
    rw [abs_le] at hx₀; constructor <;> linarith [hx₀.1, hx₀.2]
  have hζI : ζ ∈ Icc (ζ - r) (ζ + r) := by
    have : 0 ≤ r := le_trans (abs_nonneg _) hx₀
    constructor <;> linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ζ hζI)
  by_cases hne : x₀ = ζ
  · subst hne
    rw [newtonStep_root hζ, sub_self, abs_zero]
    positivity
  have hsub : uIcc x₀ ζ ⊆ Icc (ζ - r) (ζ + r) := uIcc_subset_Icc hx₀I hζI
  have hd : f' x₀ ≠ 0 := by
    intro h; have := hm' x₀ hx₀I; rw [h, abs_zero] at this; exact absurd this (not_le.mpr hm)
  obtain ⟨ξ, hξ, h⟩ := newtonStep_sub_root hne hζ hd (fun t ht => hf t (hsub ht))
    (fun t ht => hf' t (hsub ht))
  have hξI : ξ ∈ Icc (ζ - r) (ζ + r) := hsub (Ioo_subset_Icc_self hξ)
  rw [h, abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow, sq_abs]
  have hfx : m ≤ |f' x₀| := hm' x₀ hx₀I
  have hfpos : 0 < |f' x₀| := lt_of_lt_of_le hm hfx
  rw [div_le_iff₀ (by positivity)]
  calc (x₀ - ζ) ^ 2 * |f'' ξ| ≤ (x₀ - ζ) ^ 2 * M :=
        mul_le_mul_of_nonneg_left (hM ξ hξI) (sq_nonneg _)
    _ = M / (2 * m) * (x₀ - ζ) ^ 2 * (2 * m) := by field_simp
    _ ≤ M / (2 * m) * (x₀ - ζ) ^ 2 * (2 * |f' x₀|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-- Newton's iteration from a start within `r` of the zero with `K |e_0| ≤ 1/2`, `K = M / (2m)`:
every iterate stays within `r`, every error at least halves (the text's
`|x_1 − ζ| ≤ |x_0 − ζ| / 2`), and `K |e_n| ≤ (K |e_0|)^(2^n)` (quadratic convergence). -/
theorem newtonSeq_bounds {f f' f'' : ℝ → ℝ} {ζ r M m : ℝ} (hm : 0 < m) (hζ : f ζ = 0)
    (hf : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ Icc (ζ - r) (ζ + r), |f'' t| ≤ M)
    (hm' : ∀ t ∈ Icc (ζ - r) (ζ + r), m ≤ |f' t|) {x₀ : ℝ} (hx₀ : |x₀ - ζ| ≤ r)
    (hK : M / (2 * m) * |x₀ - ζ| ≤ 1 / 2) (n : ℕ) :
    |newtonSeq f f' x₀ n - ζ| ≤ r ∧
      |newtonSeq f f' x₀ (n + 1) - ζ| ≤ |newtonSeq f f' x₀ n - ζ| / 2 ∧
      M / (2 * m) * |newtonSeq f f' x₀ n - ζ| ≤ (M / (2 * m) * |x₀ - ζ|) ^ (2 ^ n) := by
  set K := M / (2 * m) with hKdef
  have hζI : ζ ∈ Icc (ζ - r) (ζ + r) := by
    have : 0 ≤ r := le_trans (abs_nonneg _) hx₀
    constructor <;> linarith
  have hK0 : 0 ≤ K := by
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ζ hζI)
    positivity
  -- the step bound at any point of the interval
  have step : ∀ x, |x - ζ| ≤ r → |newtonStep f f' x - ζ| ≤ K * |x - ζ| ^ 2 := by
    intro x hx
    have := abs_newtonStep_sub_root_le hm hζ hf hf' hM hm' hx
    rwa [← sq_abs] at this
  -- the halving step from the doubly-exponential bound
  have half : ∀ x, |x - ζ| ≤ r → K * |x - ζ| ≤ 1 / 2 →
      |newtonStep f f' x - ζ| ≤ |x - ζ| / 2 := by
    intro x hx hKx
    calc |newtonStep f f' x - ζ| ≤ K * |x - ζ| ^ 2 := step x hx
      _ = (K * |x - ζ|) * |x - ζ| := by ring
      _ ≤ 1 / 2 * |x - ζ| := mul_le_mul_of_nonneg_right hKx (abs_nonneg _)
      _ = |x - ζ| / 2 := by ring
  -- the invariant
  have inv : ∀ n, |newtonSeq f f' x₀ n - ζ| ≤ r ∧
      K * |newtonSeq f f' x₀ n - ζ| ≤ (K * |x₀ - ζ|) ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨hx₀, by simp⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have hpow : (K * |x₀ - ζ|) ^ (2 ^ n) ≤ 1 / 2 := by
        calc (K * |x₀ - ζ|) ^ (2 ^ n) ≤ (1 / 2 : ℝ) ^ (2 ^ n) :=
              pow_le_pow_left₀ (by positivity) hK _
          _ ≤ (1 / 2 : ℝ) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) Nat.one_le_two_pow
          _ = 1 / 2 := pow_one _
      have hKn : K * |newtonSeq f f' x₀ n - ζ| ≤ 1 / 2 := h2.trans hpow
      refine ⟨?_, ?_⟩
      · rw [newtonSeq_succ]
        calc |newtonStep f f' (newtonSeq f f' x₀ n) - ζ| ≤ |newtonSeq f f' x₀ n - ζ| / 2 :=
              half _ h1 hKn
          _ ≤ r := by linarith [abs_nonneg (newtonSeq f f' x₀ n - ζ)]
      · rw [newtonSeq_succ, pow_succ, pow_mul]
        calc K * |newtonStep f f' (newtonSeq f f' x₀ n) - ζ|
            ≤ K * (K * |newtonSeq f f' x₀ n - ζ| ^ 2) :=
              mul_le_mul_of_nonneg_left (step _ h1) hK0
          _ = (K * |newtonSeq f f' x₀ n - ζ|) ^ 2 := by ring
          _ ≤ ((K * |x₀ - ζ|) ^ (2 ^ n)) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h2 2
  obtain ⟨h1, h2⟩ := inv n
  refine ⟨h1, ?_, h2⟩
  have hpow : (K * |x₀ - ζ|) ^ (2 ^ n) ≤ 1 / 2 := by
    calc (K * |x₀ - ζ|) ^ (2 ^ n) ≤ (1 / 2 : ℝ) ^ (2 ^ n) :=
          pow_le_pow_left₀ (by positivity) hK _
      _ ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) Nat.one_le_two_pow
      _ = 1 / 2 := pow_one _
  rw [newtonSeq_succ]
  exact half _ h1 (h2.trans hpow)

/-- Under the hypotheses of `newtonSeq_bounds`, `|e_n| ≤ |e_0| / 2^n`. -/
theorem abs_newtonSeq_sub_root_le {f f' f'' : ℝ → ℝ} {ζ r M m : ℝ} (hm : 0 < m) (hζ : f ζ = 0)
    (hf : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ Icc (ζ - r) (ζ + r), |f'' t| ≤ M)
    (hm' : ∀ t ∈ Icc (ζ - r) (ζ + r), m ≤ |f' t|) {x₀ : ℝ} (hx₀ : |x₀ - ζ| ≤ r)
    (hK : M / (2 * m) * |x₀ - ζ| ≤ 1 / 2) (n : ℕ) :
    |newtonSeq f f' x₀ n - ζ| ≤ |x₀ - ζ| / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (newtonSeq_bounds hm hζ hf hf' hM hm' hx₀ hK n).2.1
    calc |newtonSeq f f' x₀ (n + 1) - ζ| ≤ |newtonSeq f f' x₀ n - ζ| / 2 := h
      _ ≤ |x₀ - ζ| / 2 ^ n / 2 := by gcongr
      _ = |x₀ - ζ| / 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- Under the hypotheses of `newtonSeq_bounds`, the iterates converge to the zero. -/
theorem tendsto_newtonSeq {f f' f'' : ℝ → ℝ} {ζ r M m : ℝ} (hm : 0 < m) (hζ : f ζ = 0)
    (hf : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ Icc (ζ - r) (ζ + r), |f'' t| ≤ M)
    (hm' : ∀ t ∈ Icc (ζ - r) (ζ + r), m ≤ |f' t|) {x₀ : ℝ} (hx₀ : |x₀ - ζ| ≤ r)
    (hK : M / (2 * m) * |x₀ - ζ| ≤ 1 / 2) :
    Tendsto (newtonSeq f f' x₀) atTop (𝓝 ζ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => |x₀ - ζ| * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul |x₀ - ζ|
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [Real.norm_eq_abs, one_div, inv_pow, ← div_eq_mul_inv]
  exact abs_newtonSeq_sub_root_le hm hζ hf hf' hM hm' hx₀ hK n

/-- (4.3) with an explicit constant: for `f` three times differentiable between `x₀` and `ζ`,
with `|f''| ≤ M₂`, `|f'''| ≤ M₃` and `|f'| ≥ m > 0` there,
`|e_1 − f''(ζ) / (2 f'(ζ)) · e_0²| ≤ (7 M₃ / (6 m) + M₂² / (2 m²)) |e_0|³`.  In particular the
order of convergence is exactly two when `f''(ζ) ≠ 0`. -/
theorem newtonStep_sub_root_cubic {f f' f'' f''' : ℝ → ℝ} {x₀ ζ M₂ M₃ m : ℝ} (hne : x₀ ≠ ζ)
    (hm : 0 < m) (hζ : f ζ = 0)
    (hf : ∀ t ∈ uIcc x₀ ζ, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ uIcc x₀ ζ, HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t ∈ uIcc x₀ ζ, HasDerivAt f'' (f''' t) t)
    (hM₂ : ∀ t ∈ uIcc x₀ ζ, |f'' t| ≤ M₂) (hM₃ : ∀ t ∈ uIcc x₀ ζ, |f''' t| ≤ M₃)
    (hm' : ∀ t ∈ uIcc x₀ ζ, m ≤ |f' t|) :
    |newtonStep f f' x₀ - ζ - f'' ζ / (2 * f' ζ) * (x₀ - ζ) ^ 2|
      ≤ (7 * M₃ / (6 * m) + M₂ ^ 2 / (2 * m ^ 2)) * |x₀ - ζ| ^ 3 := by
  have hx₀I : x₀ ∈ uIcc x₀ ζ := left_mem_uIcc
  have hζI : ζ ∈ uIcc x₀ ζ := right_mem_uIcc
  have hd : f' x₀ ≠ 0 := by
    intro h; have := hm' x₀ hx₀I; rw [h, abs_zero] at this; exact absurd this (not_le.mpr hm)
  have hdζ : f' ζ ≠ 0 := by
    intro h; have := hm' ζ hζI; rw [h, abs_zero] at this; exact absurd this (not_le.mpr hm)
  -- third-order Taylor of `f` at `ζ`, evaluated at `x₀`
  have hsymm : uIcc ζ x₀ = uIcc x₀ ζ := uIcc_comm ζ x₀
  obtain ⟨ξ₁, hξ₁, h1⟩ := taylor_three hne.symm (fun t ht => hf t (hsymm ▸ ht))
    (fun t ht => hf' t (hsymm ▸ ht)) (fun t ht => hf'' t (hsymm ▸ ht))
  rw [hζ, zero_add] at h1
  have hξ₁I : ξ₁ ∈ uIcc x₀ ζ := by rw [← hsymm]; exact Ioo_subset_Icc_self hξ₁
  -- mean value theorem for `f'` between `ζ` and `x₀`
  obtain ⟨ξ₂, hξ₂, h2⟩ := taylor_one hne.symm (fun t ht => hf' t (hsymm ▸ ht))
  have hξ₂I : ξ₂ ∈ uIcc x₀ ζ := by rw [← hsymm]; exact Ioo_subset_Icc_self hξ₂
  -- mean value theorem for `f''` between `ζ` and `ξ₂`
  have hξ₂ne : ζ ≠ ξ₂ := by
    rcases hξ₂ with ⟨hl, hr⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [sup_eq_left.mpr hlt.le] at hr; exact hr.ne'
    · rw [inf_eq_left.mpr hlt.le] at hl; exact hl.ne
  have hsub : uIcc ζ ξ₂ ⊆ uIcc x₀ ζ := by
    rw [← hsymm]; exact uIcc_subset_uIcc left_mem_uIcc (Ioo_subset_Icc_self hξ₂)
  obtain ⟨ξ₃, hξ₃, h3⟩ := taylor_one hξ₂ne (fun t ht => hf'' t (hsub ht))
  have hξ₃I : ξ₃ ∈ uIcc x₀ ζ := hsub (Ioo_subset_Icc_self hξ₃)
  -- `|ξ₂ − ζ| ≤ |x₀ − ζ|`
  have hξ₂e : |ξ₂ - ζ| ≤ |x₀ - ζ| := by
    rcases hξ₂ with ⟨hl, hr⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [inf_eq_right.mpr hlt.le] at hl; rw [sup_eq_left.mpr hlt.le] at hr
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
    · rw [inf_eq_left.mpr hlt.le] at hl; rw [sup_eq_right.mpr hlt.le] at hr
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  -- the exact identity for the error
  have hid : newtonStep f f' x₀ - ζ - f'' ζ / (2 * f' ζ) * (x₀ - ζ) ^ 2
      = (x₀ - ζ) ^ 2 * (((ξ₂ - ζ) * f''' ξ₃ - (x₀ - ζ) * f''' ξ₁ / 6) / f' x₀
          - f'' ζ / 2 * (x₀ - ζ) * f'' ξ₂ / (f' x₀ * f' ζ)) := by
    unfold newtonStep
    have h2' : f' x₀ = f' ζ + (x₀ - ζ) * f'' ξ₂ := h2
    have h3' : f'' ξ₂ = f'' ζ + (ξ₂ - ζ) * f''' ξ₃ := h3
    generalize hA : f x₀ = A at h1 ⊢
    generalize hB : f' x₀ = B at h2' hd ⊢
    generalize hC : f'' ξ₂ = C at h3' h2' ⊢
    subst h1 h2' h3'
    field_simp
    ring
  -- bound the bracket
  have hfx : m ≤ |f' x₀| := hm' x₀ hx₀I
  have hfζ : m ≤ |f' ζ| := hm' ζ hζI
  have hA : |((ξ₂ - ζ) * f''' ξ₃ - (x₀ - ζ) * f''' ξ₁ / 6) / f' x₀|
      ≤ 7 * M₃ / (6 * m) * |x₀ - ζ| := by
    rw [abs_div, div_le_iff₀ (lt_of_lt_of_le hm hfx)]
    have hM₃0 : 0 ≤ M₃ := le_trans (abs_nonneg _) (hM₃ ξ₁ hξ₁I)
    calc |(ξ₂ - ζ) * f''' ξ₃ - (x₀ - ζ) * f''' ξ₁ / 6|
        ≤ |(ξ₂ - ζ) * f''' ξ₃| + |(x₀ - ζ) * f''' ξ₁ / 6| := abs_sub _ _
      _ = |ξ₂ - ζ| * |f''' ξ₃| + |x₀ - ζ| * |f''' ξ₁| / 6 := by
          rw [abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      _ ≤ |x₀ - ζ| * M₃ + |x₀ - ζ| * M₃ / 6 := by
          gcongr
          · exact hM₃ ξ₃ hξ₃I
          · exact hM₃ ξ₁ hξ₁I
      _ = 7 * M₃ / (6 * m) * |x₀ - ζ| * m := by field_simp; ring
      _ ≤ 7 * M₃ / (6 * m) * |x₀ - ζ| * |f' x₀| := by gcongr
  have hB : |f'' ζ / 2 * (x₀ - ζ) * f'' ξ₂ / (f' x₀ * f' ζ)|
      ≤ M₂ ^ 2 / (2 * m ^ 2) * |x₀ - ζ| := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      div_le_iff₀ (by positivity)]
    have hM₂0 : 0 ≤ M₂ := le_trans (abs_nonneg _) (hM₂ ζ hζI)
    calc |f'' ζ| / 2 * |x₀ - ζ| * |f'' ξ₂| ≤ M₂ / 2 * |x₀ - ζ| * M₂ := by
          gcongr
          · exact hM₂ ζ hζI
          · exact hM₂ ξ₂ hξ₂I
      _ = M₂ ^ 2 / (2 * m ^ 2) * |x₀ - ζ| * (m * m) := by field_simp
      _ ≤ M₂ ^ 2 / (2 * m ^ 2) * |x₀ - ζ| * (|f' x₀| * |f' ζ|) := by gcongr
  rw [hid, abs_mul, abs_pow]
  calc |x₀ - ζ| ^ 2 * |((ξ₂ - ζ) * f''' ξ₃ - (x₀ - ζ) * f''' ξ₁ / 6) / f' x₀
          - f'' ζ / 2 * (x₀ - ζ) * f'' ξ₂ / (f' x₀ * f' ζ)|
      ≤ |x₀ - ζ| ^ 2 * (|((ξ₂ - ζ) * f''' ξ₃ - (x₀ - ζ) * f''' ξ₁ / 6) / f' x₀|
          + |f'' ζ / 2 * (x₀ - ζ) * f'' ξ₂ / (f' x₀ * f' ζ)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ ≤ |x₀ - ζ| ^ 2 * (7 * M₃ / (6 * m) * |x₀ - ζ| + M₂ ^ 2 / (2 * m ^ 2) * |x₀ - ζ|) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = (7 * M₃ / (6 * m) + M₂ ^ 2 / (2 * m ^ 2)) * |x₀ - ζ| ^ 3 := by ring

end BZ

end Azurite
