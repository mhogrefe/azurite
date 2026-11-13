/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# DLMF §5.19(iii): the `n`-dimensional sphere

Formalization of <https://dlmf.nist.gov/5.19>, subsection (iii). (§5.19(ii), Mellin–Barnes
integrals, is descriptive and has no equations.)

* 5.19.4, volume: `V = π^{n/2} rⁿ / Γ(½n + 1)` (`sphereVolume`) is the Lebesgue measure of the
  open and of the closed ball of radius `r ≥ 0` in `ℝⁿ`, `n ≥ 1` (`dlmf_5_19_4_volume`).
* 5.19.4, surface area: `S = 2π^{n/2} r^{n−1} / Γ(½n) = (n/r) V` (`sphereArea`,
  `dlmf_5_19_4_area`). `S` is the derivative `dV/dr` (`hasDerivAt_sphereVolume`), and for
  `r = 1` it is the total mass of Mathlib's surface measure on the unit sphere
  (`Measure.toSphere`, `dlmf_5_19_4_toSphere`).
-/

open MeasureTheory Metric
open scoped Real ENNReal

namespace Azurite.DLMF

/-- `V = π^{n/2} rⁿ / Γ(½n + 1)`. -/
noncomputable def sphereVolume (n : ℕ) (r : ℝ) : ℝ :=
  π ^ ((n : ℝ) / 2) * r ^ n / Real.Gamma (n / 2 + 1)

/-- `S = 2π^{n/2} r^{n−1} / Γ(½n)`. -/
noncomputable def sphereArea (n : ℕ) (r : ℝ) : ℝ :=
  2 * π ^ ((n : ℝ) / 2) * r ^ (n - 1) / Real.Gamma (n / 2)

theorem sqrt_pi_pow (n : ℕ) : √π ^ n = π ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  ring_nf

theorem sphereVolume_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ sphereVolume n r := by
  unfold sphereVolume
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < n / 2 + 1 by positivity)
  positivity

/-- DLMF 5.19.4 (volume): the open and the closed ball of radius `r ≥ 0` in `ℝⁿ` (`n ≥ 1`) have
volume `π^{n/2} rⁿ / Γ(½n + 1)`. -/
theorem dlmf_5_19_4_volume {n : ℕ} (hn : 1 ≤ n) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 ≤ r) :
    volume (ball x r) = ENNReal.ofReal (sphereVolume n r) ∧
      volume (closedBall x r) = ENNReal.ofReal (sphereVolume n r) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hG := Real.Gamma_pos_of_pos (show (0 : ℝ) < n / 2 + 1 by positivity)
  have key : ENNReal.ofReal r ^ n * ENNReal.ofReal (√π ^ n / Real.Gamma (n / 2 + 1)) =
      ENNReal.ofReal (sphereVolume n r) := by
    rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity), sphereVolume, sqrt_pi_pow]
    congr 1; ring
  constructor
  · rw [EuclideanSpace.volume_ball, Fintype.card_fin, key]
  · rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, key]

/-- DLMF 5.19.4 (surface area): `S = (n/r) V`. -/
theorem dlmf_5_19_4_area {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : r ≠ 0) :
    sphereArea n r = n / r * sphereVolume n r := by
  have hn2 : (n : ℝ) / 2 ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hG := Real.Gamma_pos_of_pos (show (0 : ℝ) < n / 2 by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity)
  have hpow : r ^ n = r ^ (n - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [sphereArea, sphereVolume, Real.Gamma_add_one hn2, hpow]
  field_simp

/-- `S = dV/dr`. -/
theorem hasDerivAt_sphereVolume {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    HasDerivAt (sphereVolume n) (sphereArea n r) r := by
  have hn2 : (n : ℝ) / 2 ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hG := Real.Gamma_pos_of_pos (show (0 : ℝ) < n / 2 by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity)
  have h : HasDerivAt (sphereVolume n)
      (π ^ ((n : ℝ) / 2) * (n * r ^ (n - 1)) / Real.Gamma (n / 2 + 1)) r :=
    ((hasDerivAt_pow n r).const_mul (π ^ ((n : ℝ) / 2))).div_const _
  refine h.congr_deriv ?_
  rw [sphereArea, Real.Gamma_add_one hn2]
  field_simp

/-- For `r = 1`, `S` is the total mass of Mathlib's surface measure on the unit sphere of `ℝⁿ`. -/
theorem dlmf_5_19_4_toSphere {n : ℕ} (hn : 1 ≤ n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ =
      ENNReal.ofReal (sphereArea n 1) := by
  rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
    (dlmf_5_19_4_volume hn 0 zero_le_one).1, dlmf_5_19_4_area hn one_ne_zero, div_one,
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

end Azurite.DLMF
