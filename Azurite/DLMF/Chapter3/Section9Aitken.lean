/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section9
import Mathlib.Algebra.Group.ForwardDiff

/-!
# DLMF §3.9(iii): Aitken's Δ²-process

* 3.9.7 (`aitken`, `dlmf_3_9_7`): `tₙ = sₙ − (Δsₙ)²/Δ²sₙ
  = sₙ − (s_{n+1} − sₙ)²/(s_{n+2} − 2s_{n+1} + sₙ)`.
* 3.9.8 (`IsLinearlyConvergent`): `(s_{n+1} − σ)/(sₙ − σ) → ρ`, `|ρ| < 1`.
* "This transformation is accelerating if `{sₙ}` is a linearly convergent sequence"
  (`dlmf_3_9_iii_accelerating`), for `sₙ ≠ σ` (so that 3.9.8 makes sense). The error ratio is
  `1 − (rₙ − 1)²/(r_{n+1}rₙ − 2rₙ + 1)` with `rₙ = (s_{n+1} − σ)/(sₙ − σ)` (`aitken_ratio`).
* Aitken's process is exact on geometric sequences `σ + cqⁿ` (`aitken_geometric`).
* The iterated Δ²-process (`aitkenIter`); Brezinski and Redivo Zaglia (1991) is not formalized.
-/

open Filter Topology

namespace Azurite.DLMF

variable {𝕜 : Type*} [NormedField 𝕜]

/-- **DLMF 3.9.7**: Aitken's Δ²-process. -/
def aitken : SeqTransform 𝕜 := fun s n =>
  s n - (s (n + 1) - s n) ^ 2 / (s (n + 2) - 2 * s (n + 1) + s n)

/-- **DLMF 3.9.7** with forward differences: `tₙ = sₙ − (Δsₙ)²/Δ²sₙ`. -/
theorem dlmf_3_9_7 (s : ℕ → 𝕜) (n : ℕ) :
    aitken s n = s n - (fwdDiff 1 s n) ^ 2 / ((fwdDiff 1)^[2] s n) := by
  simp only [aitken, Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  congr 2
  ring

/-- **DLMF 3.9.8**: `{sₙ}` converges linearly to `σ`: `(s_{n+1} − σ)/(sₙ − σ) → ρ`, `|ρ| < 1`. -/
def IsLinearlyConvergent (s : ℕ → 𝕜) (σ ρ : 𝕜) : Prop :=
  Tendsto s atTop (𝓝 σ) ∧ Tendsto (fun n => (s (n + 1) - σ) / (s n - σ)) atTop (𝓝 ρ) ∧ ‖ρ‖ < 1

/-- The error ratio of Aitken's process. -/
theorem aitken_ratio {s : ℕ → 𝕜} {σ : 𝕜} (hne : ∀ n, s n ≠ σ) (n : ℕ) :
    (aitken s n - σ) / (s n - σ) =
      1 - ((s (n + 1) - σ) / (s n - σ) - 1) ^ 2 /
        ((s (n + 2) - σ) / (s (n + 1) - σ) * ((s (n + 1) - σ) / (s n - σ)) -
          2 * ((s (n + 1) - σ) / (s n - σ)) + 1) := by
  have h0 : s n - σ ≠ 0 := sub_ne_zero.mpr (hne n)
  have h1 : s (n + 1) - σ ≠ 0 := sub_ne_zero.mpr (hne (n + 1))
  set e0 := s n - σ
  set r := (s (n + 1) - σ) / e0
  set r' := (s (n + 2) - σ) / (s (n + 1) - σ)
  have he1 : s (n + 1) = σ + r * e0 := by simp only [r]; field_simp; ring
  have he2 : s (n + 2) = σ + r' * r * e0 := by
    simp only [r', r]; field_simp; ring
  have hs0 : s n = σ + e0 := by simp only [e0]; ring
  have key : (s (n + 1) - s n) ^ 2 / (s (n + 2) - 2 * s (n + 1) + s n) =
      e0 * ((r - 1) ^ 2 / (r' * r - 2 * r + 1)) := by
    rw [he1, he2, hs0]
    rw [show (σ + r * e0 - (σ + e0)) ^ 2 = e0 * (e0 * (r - 1) ^ 2) by ring,
      show σ + r' * r * e0 - 2 * (σ + r * e0) + (σ + e0) = e0 * (r' * r - 2 * r + 1) by ring,
      mul_div_mul_left _ _ h0, mul_div_assoc]
  rw [aitken, key, show s n - e0 * ((r - 1) ^ 2 / (r' * r - 2 * r + 1)) - σ =
    e0 * (1 - (r - 1) ^ 2 / (r' * r - 2 * r + 1)) by rw [hs0]; ring, mul_div_cancel_left₀ _ h0]

/-- **DLMF §3.9(iii)**: Aitken's Δ²-process accelerates linearly convergent sequences (3.9.8)
with `sₙ ≠ σ`. -/
theorem dlmf_3_9_iii_accelerating {s : ℕ → 𝕜} {σ ρ : 𝕜} (h : IsLinearlyConvergent s σ ρ)
    (hne : ∀ n, s n ≠ σ) : IsAccelerating aitken s σ := by
  obtain ⟨hs, hr, hρ⟩ := h
  have hρ1 : ρ - 1 ≠ 0 := by
    intro h0
    rw [sub_eq_zero.mp h0, norm_one] at hρ
    exact lt_irrefl 1 hρ
  have hr' : Tendsto (fun n => (s (n + 2) - σ) / (s (n + 1) - σ)) atTop (𝓝 ρ) :=
    hr.comp (tendsto_add_atTop_nat 1)
  have hD : Tendsto (fun n => (s (n + 2) - σ) / (s (n + 1) - σ) * ((s (n + 1) - σ) / (s n - σ)) -
      2 * ((s (n + 1) - σ) / (s n - σ)) + 1) atTop (𝓝 ((ρ - 1) ^ 2)) := by
    have := ((hr'.mul hr).sub (hr.const_mul 2)).add_const 1
    convert this using 2
    ring
  have hN : Tendsto (fun n => ((s (n + 1) - σ) / (s n - σ) - 1) ^ 2) atTop (𝓝 ((ρ - 1) ^ 2)) :=
    (hr.sub_const 1).pow 2
  have hq := hN.div hD (pow_ne_zero 2 hρ1)
  rw [div_self (pow_ne_zero 2 hρ1)] at hq
  have hratio : Tendsto (fun n => (aitken s n - σ) / (s n - σ)) atTop (𝓝 0) := by
    simp_rw [aitken_ratio hne]
    simpa using hq.const_sub 1
  refine ⟨hs, fun σ' hσ' => ?_, hratio⟩
  rw [tendsto_nhds_unique hσ' hs]
  exact tendsto_of_ratio hs (Eventually.of_forall hne) hratio

/-- Aitken's process is exact on geometric sequences: `sₙ = σ + cqⁿ` (`c ≠ 0`, `q ≠ 0, 1`)
gives `tₙ = σ`. -/
theorem aitken_geometric {σ c q : 𝕜} (hc : c ≠ 0) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (n : ℕ) :
    aitken (fun n => σ + c * q ^ n) n = σ := by
  have hq1' : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  simp only [aitken]
  rw [show σ + c * q ^ (n + 1) - (σ + c * q ^ n) = c * q ^ n * (q - 1) by ring,
    show σ + c * q ^ (n + 2) - 2 * (σ + c * q ^ (n + 1)) + (σ + c * q ^ n) =
      c * q ^ n * (q - 1) ^ 2 by ring]
  have : c * q ^ n ≠ 0 := mul_ne_zero hc (pow_ne_zero n hq0)
  field_simp
  ring

/-- The iterated Δ²-process: Aitken's process applied `k` times. -/
def aitkenIter (k : ℕ) : SeqTransform 𝕜 := aitken^[k]

end Azurite.DLMF
