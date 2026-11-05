/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9Series
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# DLMF §3.9(i): Sequence transformations

Sequences are real or complex (`𝕜` a normed field).

* Limit-preserving transformations (`IsLimitPreserving`) and accelerating transformations, 3.9.1
  (`IsAccelerating`: limit-preserving with `(tₙ − σ)/(sₙ − σ) → 0`). When `sₙ ≠ σ` eventually,
  3.9.1 alone forces `tₙ → σ` (`tendsto_of_ratio`).
* Series: transformations act on the partial sums `∑_{k ≤ n} a_k` (`partialSum` of §1.9,
  `tendsto_partialSum`).
* The identity is limit-preserving but never accelerating (`id_not_accelerating`); the shift
  `tₙ = s_{n+1}` is limit-preserving (`shiftT_limitPreserving`).
* "A sequence transformation can be effective for one type of sequence but may not accelerate
  convergence for another type": the shift accelerates `sₙ = 1/n!` (`shiftT_accelerates_factorial`)
  but not the geometric `sₙ = qⁿ` (`shiftT_not_accelerating_geometric`).
* "It may even fail altogether by not being limit-preserving": the linear extrapolation
  `tₙ = sₙ + n(s_{n+1} − sₙ)` (`linExtrap`) accelerates `sₙ = 1/(n + 1)`
  (`linExtrap_accelerates`) but is not limit-preserving for `sₙ = (−1)ⁿ/(n + 1)`
  (`linExtrap_not_limitPreserving`).
-/

open Filter Topology Finset

namespace Azurite.DLMF

variable {𝕜 : Type*} [NormedField 𝕜]

/-- A sequence transformation `{sₙ} ↦ {tₙ}`. -/
abbrev SeqTransform (𝕜 : Type*) := (ℕ → 𝕜) → (ℕ → 𝕜)

/-- **DLMF §3.9(i)**: `T` is limit-preserving on the convergent sequence `s` if `T s` converges to
the same limit. -/
def IsLimitPreserving (T : SeqTransform 𝕜) (s : ℕ → 𝕜) : Prop :=
  ∀ σ, Tendsto s atTop (𝓝 σ) → Tendsto (T s) atTop (𝓝 σ)

/-- **DLMF 3.9.1**: `T` accelerates the convergence of `s → σ` if it is limit-preserving and
`(tₙ − σ)/(sₙ − σ) → 0`. -/
def IsAccelerating (T : SeqTransform 𝕜) (s : ℕ → 𝕜) (σ : 𝕜) : Prop :=
  Tendsto s atTop (𝓝 σ) ∧ IsLimitPreserving T s ∧
    Tendsto (fun n => (T s n - σ) / (s n - σ)) atTop (𝓝 0)

theorem IsAccelerating.tendsto {T : SeqTransform 𝕜} {s : ℕ → 𝕜} {σ : 𝕜}
    (h : IsAccelerating T s σ) : Tendsto (T s) atTop (𝓝 σ) := h.2.1 σ h.1

/-- If `sₙ ≠ σ` eventually, the ratio condition 3.9.1 by itself implies `tₙ → σ`. -/
theorem tendsto_of_ratio {s t : ℕ → 𝕜} {σ : 𝕜} (hs : Tendsto s atTop (𝓝 σ))
    (hne : ∀ᶠ n in atTop, s n ≠ σ)
    (hr : Tendsto (fun n => (t n - σ) / (s n - σ)) atTop (𝓝 0)) :
    Tendsto t atTop (𝓝 σ) := by
  have h0 : Tendsto (fun n => s n - σ) atTop (𝓝 0) := by
    simpa using hs.sub_const σ
  have hm := hr.mul h0
  rw [zero_mul] at hm
  have heq : (fun n => (t n - σ) / (s n - σ) * (s n - σ)) =ᶠ[atTop] fun n => t n - σ :=
    hne.mono fun n hn => div_mul_cancel₀ _ (sub_ne_zero.mpr hn)
  have := (hm.congr' heq).add_const σ
  simpa using this

/-- Series: a transformation of a series acts on its partial sums `∑_{k ≤ n} a_k` (`partialSum`
of §1.9). -/
theorem tendsto_partialSum {a : ℕ → 𝕜} {σ : 𝕜} (h : HasSum a σ) :
    Tendsto (partialSum a) atTop (𝓝 σ) :=
  (h.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

/-! ### Examples -/

/-- The identity is limit-preserving but does not accelerate any sequence with `sₙ ≠ σ`. -/
theorem id_not_accelerating {s : ℕ → 𝕜} {σ : 𝕜} (hne : ∀ n, s n ≠ σ) :
    IsLimitPreserving (fun s => s) s ∧ ¬ IsAccelerating (fun s => s) s σ := by
  refine ⟨fun _ h => h, fun ⟨_, _, h⟩ => ?_⟩
  have : (fun n => (s n - σ) / (s n - σ)) = fun _ => (1 : 𝕜) :=
    funext fun n => div_self (sub_ne_zero.mpr (hne n))
  rw [this] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- The shift `tₙ = s_{n+1}`. -/
def shiftT : SeqTransform 𝕜 := fun s n => s (n + 1)

theorem shiftT_limitPreserving (s : ℕ → 𝕜) : IsLimitPreserving shiftT s :=
  fun _ h => h.comp (tendsto_add_atTop_nat 1)

/-- The shift accelerates `sₙ = 1/n! → 0`: the error ratio is `1/(n + 1)`. -/
theorem shiftT_accelerates_factorial :
    IsAccelerating shiftT (fun n : ℕ => ((Nat.factorial n : ℝ))⁻¹) 0 := by
  have hs : Tendsto (fun n : ℕ => ((Nat.factorial n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop)
  have hr : (fun n : ℕ => (shiftT (fun n : ℕ => ((Nat.factorial n : ℝ))⁻¹) n - 0) /
      (((Nat.factorial n : ℝ))⁻¹ - 0)) = fun n : ℕ => ((n : ℝ) + 1)⁻¹ := funext fun n => by
    simp only [shiftT, sub_zero, Nat.factorial_succ]
    push_cast
    field_simp
  refine ⟨hs, shiftT_limitPreserving _, ?_⟩
  rw [hr]
  exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- The shift does not accelerate the geometric sequence `qⁿ → 0`, `0 < |q| < 1`: the error
ratio is `q`. -/
theorem shiftT_not_accelerating_geometric {q : 𝕜} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    Tendsto (fun n => q ^ n) atTop (𝓝 0) ∧ ¬ IsAccelerating shiftT (fun n => q ^ n) 0 := by
  refine ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq1, ?_⟩
  rintro ⟨-, -, h⟩
  have : (fun n => (shiftT (fun n => q ^ n) n - 0) / (q ^ n - 0)) = fun _ => q := by
    funext n
    simp only [shiftT, sub_zero, pow_succ]
    field_simp
  rw [this] at h
  exact hq0 (tendsto_nhds_unique tendsto_const_nhds h)

/-- Linear extrapolation `tₙ = sₙ + n(s_{n+1} − sₙ)`. -/
def linExtrap : SeqTransform ℝ := fun s n => s n + n * (s (n + 1) - s n)

/-- `linExtrap` accelerates `sₙ = 1/(n + 1)`: `tₙ = 2/((n + 1)(n + 2))`, ratio `2/(n + 2)`. -/
theorem linExtrap_accelerates :
    IsAccelerating linExtrap (fun n => ((n : ℝ) + 1)⁻¹) 0 := by
  have ht : ∀ n : ℕ, linExtrap (fun n => ((n : ℝ) + 1)⁻¹) n = 2 / (((n : ℝ) + 1) * (n + 2)) :=
    fun n => by
      simp only [linExtrap]
      push_cast
      field_simp
      ring
  have hs : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hr : (fun n : ℕ => (linExtrap (fun n => ((n : ℝ) + 1)⁻¹) n - 0) / (((n : ℝ) + 1)⁻¹ - 0)) =
      fun n : ℕ => 2 * ((n : ℝ) + 2)⁻¹ := funext fun n => by
    rw [ht, sub_zero, sub_zero]
    field_simp
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  refine ⟨hs, fun σ hσ => ?_, ?_⟩
  · rw [tendsto_nhds_unique hσ hs]
    refine tendsto_of_ratio hs (Eventually.of_forall fun n => by positivity) ?_
    rw [hr]; simpa using h2.const_mul 2
  · rw [hr]; simpa using h2.const_mul 2

/-- `linExtrap` is not limit-preserving for `sₙ = (−1)ⁿ/(n + 1) → 0`: `|tₙ| ≥ 2/3` for `n ≥ 2`. -/
theorem linExtrap_not_limitPreserving :
    Tendsto (fun n : ℕ => (-1 : ℝ) ^ n / (n + 1)) atTop (𝓝 0) ∧
      ¬ IsLimitPreserving linExtrap (fun n : ℕ => (-1 : ℝ) ^ n / (n + 1)) := by
  have hs : Tendsto (fun n : ℕ => (-1 : ℝ) ^ n / (n + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    refine squeeze_zero_norm (fun n => ?_) h1
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
      abs_of_pos (by positivity), one_div]
  refine ⟨hs, fun h => ?_⟩
  have ht := h 0 hs
  have hbig : ∀ n : ℕ, 2 ≤ n → 2 / 3 ≤ |linExtrap (fun n : ℕ => (-1 : ℝ) ^ n / (n + 1)) n| := by
    intro n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have e : linExtrap (fun n : ℕ => (-1 : ℝ) ^ n / (n + 1)) n =
        (-1) ^ n * (1 / (n + 1) - n * (1 / (n + 2) + 1 / (n + 1))) := by
      simp only [linExtrap]
      push_cast
      rw [pow_succ]
      ring
    rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hpos : (0 : ℝ) < n + 1 := by positivity
    have key : 2 / 3 ≤ (n : ℝ) * (1 / (n + 2) + 1 / (n + 1)) - 1 / (n + 1) := by
      have eq : (n : ℝ) * (1 / (n + 2) + 1 / (n + 1)) - 1 / (n + 1) =
          (2 * n ^ 2 + 2 * n - 2) / ((n + 1) * (n + 2)) := by
        field_simp; ring
      rw [eq, le_div_iff₀ (by positivity)]
      nlinarith
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  have := (ht.abs).eventually (gt_mem_nhds (show |(0 : ℝ)| < 2 / 3 by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp this
  have := hN (max N 2) (le_max_left _ _)
  have := hbig (max N 2) (le_max_right _ _)
  linarith

end Azurite.DLMF
