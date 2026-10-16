/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.Newton
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Brent–Zimmermann §4.2.5: Newton's method for functional inverses

For a function `g` with functional inverse `h` (`g (h x) = x`), Newton's method on
`f(x) = y − g(x)` finds `ζ` with `g ζ = y`, i.e. `ζ = h y`, by

  `x_{j+1} = x_j + (y − g(x_j)) / g'(x_j)`,

which only evaluates `g` and `g'`: an efficient `g` gives an efficient `h` of the same order of
complexity, if `g'` and division cost no more than `g`.  The example is `g = ln`, `h = exp`:
`f(x) = y − ln x` gives

  `x_{j+1} = x_j + x_j (y − ln x_j)`                                                     (4.11)

and Algorithm 4.1 `LiftExp`: from an `n/2`-bit approximation `x_j` of `exp y`, compute
`t = ln x_j` to `n` bits, `u = y − t` and `v = x_j u` to `n/2` bits, and return `x_j + v`, an
`n`-bit approximation.

* `inverseStep`, `inverseSeq` — the iteration; `inverseStep_eq_newtonStep` (it is Newton's
  step for `y − g`, with derivative `−g'`), `inverseStep_root`.
* `tendsto_inverseSeq` — local quadratic convergence to the preimage `ζ` of `y`, from the
  generic theorem with `|g''| ≤ M`, `|g'| ≥ m`.
* `expStep`, `expSeq` — (4.11); `inverseStep_log` (it is the functional-inverse step for `ln`).
* `expStep_rel`, `abs_expStep_relError_le` — the relative error of (4.11): `x = e^y (1 + ε)`
  goes to `e^y (1 + ε')` with `ε' = (1 + ε)(1 − ln(1 + ε)) − 1`, and `|ε'| ≤ (9/4) ε²` for
  `|ε| ≤ 1/2`.
* `liftExp_rel`, `abs_liftExp_relError_le` — Algorithm `LiftExp` with its precisions modelled as
  perturbations: `t = ln x_j + δ` (absolute error `|δ| ≤ η²`, the `n`-bit logarithm), the
  products carrying a combined relative error `θ` with `|θ| ≤ η` (the `n/2`-bit `u` and `v`),
  from `|ε| ≤ η ≤ 1/2`; the result has relative error at most `9 η²`, i.e. `n` bits up to a
  constant from `η = 2^(−n/2)`.
* `abs_log_one_add_sub_le` — the second-order Taylor bound `|ln(1 + ε) − (ε − ε²/2)| ≤ 2|ε|³`
  for `|ε| ≤ 1/2`, from Mathlib's `Real.abs_log_sub_add_sum_range_le`.
-/

namespace Azurite

namespace BZ

open Set Filter Topology Real

/-! ### The iteration for a functional inverse -/

/-- Newton's step for `f(x) = y − g(x)`: `x + (y − g x) / g' x`. -/
noncomputable def inverseStep (g g' : ℝ → ℝ) (y x : ℝ) : ℝ := x + (y - g x) / g' x

/-- The iterates from `x₀`. -/
noncomputable def inverseSeq (g g' : ℝ → ℝ) (y x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => inverseStep g g' y (inverseSeq g g' y x₀ n)

@[simp] theorem inverseSeq_zero (g g' : ℝ → ℝ) (y x₀ : ℝ) : inverseSeq g g' y x₀ 0 = x₀ := rfl

@[simp] theorem inverseSeq_succ (g g' : ℝ → ℝ) (y x₀ : ℝ) (n : ℕ) :
    inverseSeq g g' y x₀ (n + 1) = inverseStep g g' y (inverseSeq g g' y x₀ n) := rfl

/-- The functional-inverse step is Newton's step for `f = y − g`, whose derivative is `−g'`. -/
theorem inverseStep_eq_newtonStep (g g' : ℝ → ℝ) (y x : ℝ) :
    inverseStep g g' y x = newtonStep (fun x => y - g x) (fun x => -g' x) x := by
  unfold inverseStep newtonStep
  rw [div_neg, sub_neg_eq_add]

theorem inverseSeq_eq_newtonSeq (g g' : ℝ → ℝ) (y x₀ : ℝ) (n : ℕ) :
    inverseSeq g g' y x₀ n = newtonSeq (fun x => y - g x) (fun x => -g' x) x₀ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [inverseSeq_succ, newtonSeq_succ, ih, inverseStep_eq_newtonStep]

/-- The preimage `ζ` of `y` is a fixed point. -/
theorem inverseStep_root {g g' : ℝ → ℝ} {y ζ : ℝ} (hζ : g ζ = y) : inverseStep g g' y ζ = ζ := by
  simp [inverseStep, hζ]

/-- Local quadratic convergence to the functional inverse: if `g ζ = y`, `g` has derivatives `g'`
and `g''` on the interval of radius `r` about `ζ` with `|g''| ≤ M` and `|g'| ≥ m > 0` there, then
from `x₀` within `r` with `M/(2m) · |x₀ − ζ| ≤ 1/2` the iterates stay within `r`, halve their
error at every step, and converge to `ζ`. -/
theorem tendsto_inverseSeq {g g' g'' : ℝ → ℝ} {y ζ r M m : ℝ} (hm : 0 < m) (hζ : g ζ = y)
    (hg : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt g' (g'' t) t)
    (hM : ∀ t ∈ Icc (ζ - r) (ζ + r), |g'' t| ≤ M)
    (hm' : ∀ t ∈ Icc (ζ - r) (ζ + r), m ≤ |g' t|) {x₀ : ℝ} (hx₀ : |x₀ - ζ| ≤ r)
    (hK : M / (2 * m) * |x₀ - ζ| ≤ 1 / 2) :
    (∀ n, |inverseSeq g g' y x₀ n - ζ| ≤ r ∧
      |inverseSeq g g' y x₀ (n + 1) - ζ| ≤ |inverseSeq g g' y x₀ n - ζ| / 2) ∧
    Tendsto (inverseSeq g g' y x₀) atTop (𝓝 ζ) := by
  have hf : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt (fun x => y - g x) (-g' t) t :=
    fun t ht => (hasDerivAt_const t y).sub (hg t ht) |>.congr_deriv (by ring)
  have hf' : ∀ t ∈ Icc (ζ - r) (ζ + r), HasDerivAt (fun x => -g' x) (-g'' t) t :=
    fun t ht => (hg' t ht).neg
  have hroot : (fun x => y - g x) ζ = 0 := by simp [hζ]
  have hM' : ∀ t ∈ Icc (ζ - r) (ζ + r), |-g'' t| ≤ M := fun t ht => by
    rw [abs_neg]; exact hM t ht
  have hm'' : ∀ t ∈ Icc (ζ - r) (ζ + r), m ≤ |-g' t| := fun t ht => by
    rw [abs_neg]; exact hm' t ht
  have hb := fun n => newtonSeq_bounds (f := fun x => y - g x) (f' := fun x => -g' x)
    (f'' := fun x => -g'' x) hm hroot hf hf' hM' hm'' hx₀ hK n
  refine ⟨fun n => ?_, ?_⟩
  · rw [inverseSeq_eq_newtonSeq, inverseSeq_eq_newtonSeq]
    exact ⟨(hb n).1, (hb n).2.1⟩
  · exact (tendsto_newtonSeq (f := fun x => y - g x) (f' := fun x => -g' x)
      (f'' := fun x => -g'' x) hm hroot hf hf' hM' hm'' hx₀ hK).congr
      (fun n => (inverseSeq_eq_newtonSeq g g' y x₀ n).symm)

/-! ### The exponential from the logarithm, (4.11) -/

/-- The step (4.11), `x + x (y − ln x)`. -/
noncomputable def expStep (y x : ℝ) : ℝ := x + x * (y - log x)

/-- The iterates of (4.11) from `x₀`. -/
noncomputable def expSeq (y x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => expStep y (expSeq y x₀ n)

@[simp] theorem expSeq_zero (y x₀ : ℝ) : expSeq y x₀ 0 = x₀ := rfl

@[simp] theorem expSeq_succ (y x₀ : ℝ) (n : ℕ) : expSeq y x₀ (n + 1) = expStep y (expSeq y x₀ n) :=
  rfl

/-- (4.11) is the functional-inverse step for `g = ln`, `g' = 1/x`. -/
theorem inverseStep_log (y x : ℝ) : inverseStep log (fun x => x⁻¹) y x = expStep y x := by
  unfold inverseStep expStep
  rw [div_inv_eq_mul, mul_comm]

/-- The second-order Taylor bound for the logarithm: `|ln(1 + ε) − (ε − ε²/2)| ≤ 2 |ε|³` for
`|ε| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le {ε : ℝ} (hε : |ε| ≤ 1 / 2) :
    |log (1 + ε) - (ε - ε ^ 2 / 2)| ≤ 2 * |ε| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -ε) (by rw [abs_neg]; linarith) 2
  rw [abs_neg, sub_neg_eq_add] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have h' : |log (1 + ε) - (ε - ε ^ 2 / 2)| ≤ |ε| ^ 3 / (1 - |ε|) := by
    convert h using 2
    push_cast
    ring
  refine h'.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ |ε| ^ 3 := by positivity
  nlinarith

/-- The relative error of (4.11): `x = e^y (1 + ε)` (with `1 + ε > 0`) is sent to
`e^y (1 + ε)(1 − ln(1 + ε))`. -/
theorem expStep_rel (y : ℝ) {ε : ℝ} (hε : 0 < 1 + ε) :
    expStep y (exp y * (1 + ε)) = exp y * ((1 + ε) * (1 - log (1 + ε))) := by
  unfold expStep
  rw [log_mul (exp_pos y).ne' hε.ne', log_exp]
  ring

/-- Quadratic convergence of (4.11) in relative terms: for `|ε| ≤ 1/2`,
`|(1 + ε)(1 − ln(1 + ε)) − 1| ≤ (9/4) ε²`. -/
theorem abs_expStep_relError_le {ε : ℝ} (hε : |ε| ≤ 1 / 2) :
    |(1 + ε) * (1 - log (1 + ε)) - 1| ≤ 9 / 4 * ε ^ 2 := by
  have hL := abs_log_one_add_sub_le hε
  set r := log (1 + ε) - (ε - ε ^ 2 / 2) with hr
  have hid : (1 + ε) * (1 - log (1 + ε)) - 1 = -ε ^ 2 / 2 + ε ^ 3 / 2 - (1 + ε) * r := by
    rw [hr]; ring
  rw [hid]
  have hε2 : |ε| ^ 2 = ε ^ 2 := sq_abs ε
  have hε3 : |ε| ^ 3 ≤ ε ^ 2 / 2 := by
    rw [pow_succ, hε2]; nlinarith [sq_nonneg ε]
  have h1ε : |1 + ε| ≤ 3 / 2 := by
    calc |1 + ε| ≤ |1| + |ε| := abs_add_le _ _
      _ ≤ 3 / 2 := by rw [abs_one]; linarith
  calc |-ε ^ 2 / 2 + ε ^ 3 / 2 - (1 + ε) * r|
      ≤ |-ε ^ 2 / 2 + ε ^ 3 / 2| + |(1 + ε) * r| := abs_sub _ _
    _ ≤ |-ε ^ 2 / 2| + |ε ^ 3 / 2| + |1 + ε| * |r| := by
        rw [abs_mul]; gcongr; exact abs_add_le _ _
    _ = ε ^ 2 / 2 + |ε| ^ 3 / 2 + |1 + ε| * |r| := by
        rw [abs_div, abs_div, abs_neg, abs_pow, abs_pow, sq_abs,
          abs_of_pos (by norm_num : (0:ℝ) < 2)]
    _ ≤ ε ^ 2 / 2 + (ε ^ 2 / 2) / 2 + 3 / 2 * (2 * (ε ^ 2 / 2)) := by
        gcongr
        exact hL.trans (by gcongr)
    _ = 9 / 4 * ε ^ 2 := by ring

/-! ### Algorithm 4.1 `LiftExp` with its precisions -/

/-- One `LiftExp` step with its roundings modelled as perturbations: the logarithm is computed
with absolute error `δ` and the correction `x (y − t)` with relative error `θ`.  From
`x = e^y (1 + ε)` the result is `e^y (1 + ε')` with
`ε' = ε − (1 + ε)(1 + θ)(ln(1 + ε) + δ)`. -/
theorem liftExp_rel (y δ θ : ℝ) {ε : ℝ} (hε : 0 < 1 + ε) :
    exp y * (1 + ε) + exp y * (1 + ε) * (y - (log (exp y * (1 + ε)) + δ)) * (1 + θ)
      = exp y * (1 + (ε - (1 + ε) * (1 + θ) * (log (1 + ε) + δ))) := by
  rw [log_mul (exp_pos y).ne' hε.ne', log_exp]
  ring

/-- The precision claim of `LiftExp`: from an approximation with relative error `|ε| ≤ η ≤ 1/2`,
a logarithm with absolute error `|δ| ≤ η²` and a correction product with relative error
`|θ| ≤ η`, the result has relative error at most `9 η²`.  With `η = 2^(−n/2)` this is the
`n`-bit result from `n/2`-bit `u` and `v` and an `n`-bit `t`, up to the constant. -/
theorem abs_liftExp_relError_le {ε δ θ η : ℝ} (hη : η ≤ 1 / 2) (hε : |ε| ≤ η) (hδ : |δ| ≤ η ^ 2)
    (hθ : |θ| ≤ η) :
    |ε - (1 + ε) * (1 + θ) * (log (1 + ε) + δ)| ≤ 9 * η ^ 2 := by
  have hη0 : 0 ≤ η := le_trans (abs_nonneg _) hε
  have hε' : |ε| ≤ 1 / 2 := hε.trans hη
  have hL := abs_log_one_add_sub_le hε'
  set r := log (1 + ε) - (ε - ε ^ 2 / 2) with hr
  -- `(1 + ε)(1 + θ) = 1 + s`
  set s := ε + θ + ε * θ with hs
  have hs_le : |s| ≤ 5 / 2 * η := by
    calc |s| ≤ |ε| + |θ| + |ε * θ| := by
          rw [hs]; exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ η + η + η * η := by rw [abs_mul]; gcongr
      _ ≤ 5 / 2 * η := by nlinarith
  -- `ε − L = ε²/2 − r`
  have hεL : |ε - log (1 + ε)| ≤ 3 / 2 * η ^ 2 := by
    have : ε - log (1 + ε) = ε ^ 2 / 2 - r := by rw [hr]; ring
    rw [this]
    have hε2 : ε ^ 2 ≤ η ^ 2 := by rw [← sq_abs]; gcongr
    have hε3 : |ε| ^ 3 ≤ η ^ 2 / 2 := by
      calc |ε| ^ 3 = |ε| ^ 2 * |ε| := by ring
        _ ≤ η ^ 2 * (1 / 2) := by gcongr
        _ = η ^ 2 / 2 := by ring
    calc |ε ^ 2 / 2 - r| ≤ |ε ^ 2 / 2| + |r| := abs_sub _ _
      _ ≤ ε ^ 2 / 2 + 2 * |ε| ^ 3 := by
          rw [abs_div, abs_pow, sq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)]; gcongr
      _ ≤ η ^ 2 / 2 + 2 * (η ^ 2 / 2) := by gcongr
      _ = 3 / 2 * η ^ 2 := by ring
  have hLd : |log (1 + ε) + δ| ≤ 9 / 4 * η := by
    have hLb : |log (1 + ε)| ≤ 7 / 4 * η := by
      calc |log (1 + ε)| = |ε - (ε - log (1 + ε))| := by ring_nf
        _ ≤ |ε| + |ε - log (1 + ε)| := abs_sub _ _
        _ ≤ η + 3 / 2 * η ^ 2 := by gcongr
        _ ≤ 7 / 4 * η := by nlinarith
    calc |log (1 + ε) + δ| ≤ |log (1 + ε)| + |δ| := abs_add_le _ _
      _ ≤ 7 / 4 * η + η ^ 2 := by gcongr
      _ ≤ 9 / 4 * η := by nlinarith
  have hid : ε - (1 + ε) * (1 + θ) * (log (1 + ε) + δ)
      = (ε - log (1 + ε)) - δ - s * (log (1 + ε) + δ) := by rw [hs]; ring
  rw [hid]
  calc |(ε - log (1 + ε)) - δ - s * (log (1 + ε) + δ)|
      ≤ |ε - log (1 + ε)| + |δ| + |s * (log (1 + ε) + δ)| := by
        exact (abs_sub _ _).trans (by gcongr; exact abs_sub _ _)
    _ ≤ 3 / 2 * η ^ 2 + η ^ 2 + 5 / 2 * η * (9 / 4 * η) := by
        rw [abs_mul]; gcongr
    _ ≤ 9 * η ^ 2 := by nlinarith

end BZ

end Azurite
