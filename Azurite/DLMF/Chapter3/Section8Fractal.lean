/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section8Poly

/-!
# DLMF §3.8(viii): Fixed-point iterations: fractals

* 3.8.17: the iteration `z_{n+1} = φ(zₙ)` is `φ^[n] z₀` (as throughout §3.8; fixed points are
  3.8.2, `dlmf_3_8_2`).
* For 3.8.9 (Newton's rule for `z⁴ − 1`), "starting this iteration in the neighborhood of one of
  the four zeros `±1, ±i`, sequences `{zₙ}` are generated that converge to these zeros"
  (`dlmf_3_8_viii_local`): each zero is simple, so Newton's rule converges locally and
  quadratically there.
* The basins of attraction (`basin`): each is a neighborhood of its zero (`basin_mem_nhds`), and
  the four are pairwise disjoint (`basin_disjoint`). The rule commutes with multiplication by `i`
  and with complex conjugation (`quartPhi_mul_I`, `quartPhi_conj`), so the basins are rotations
  of one another (`basin_I_mul`) — the symmetry visible in the pictures of the Julia set.
* The Julia set (the common boundary of the basins), its "very complicated structure", and the
  statement that Julia sets of analytic functions are fractals (self-similar) are not formalized
  (Julia 1918, Devaney 1986).
-/

open Filter Topology Set Metric

namespace Azurite.DLMF

/-- Newton's rule 3.8.9 for `z⁴ − 1` on `ℂ`. -/
noncomputable abbrev quartPhi : ℂ → ℂ := newtonStep (quartEx (𝕜 := ℂ))

theorem quartPhi_eq (z : ℂ) : quartPhi z = (3 * z ^ 4 + 1) / (4 * z ^ 3) := dlmf_3_8_9 z

/-- **DLMF §3.8(viii)**: started near any of the zeros `±1, ±i` of `z⁴ − 1`, the iteration 3.8.9
converges to that zero (locally and quadratically). -/
theorem dlmf_3_8_viii_local {ζ : ℂ} (hζ : quartEx ζ = 0) :
    ConvergesLocally quartPhi ζ ∧ ∃ δ > 0, ∃ K ≥ 0, ∀ z₀ ∈ ball ζ δ,
      ∀ n, ‖quartPhi^[n + 1] z₀ - ζ‖ ≤ K * ‖quartPhi^[n] z₀ - ζ‖ ^ 2 := by
  have hd : deriv quartEx ζ ≠ 0 := by
    rw [(hasDerivAt_quartEx ζ).deriv]
    have : ζ ≠ 0 := by rintro rfl; norm_num [quartEx] at hζ
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 this)
  obtain ⟨h1, δ, hδ, K, hK, h2⟩ := dlmf_3_8_ii_simple_of_contDiffAt
    (f := quartEx (𝕜 := ℂ)) (by unfold quartEx; fun_prop) hζ hd
  exact ⟨h1, δ, hδ, K, hK, fun z₀ hz => (h2 z₀ hz).1⟩

/-- The basin of attraction of `ζ` under `φ`: the starting points whose iterates tend to `ζ`. -/
def basin {E : Type*} [TopologicalSpace E] (φ : E → E) (ζ : E) : Set E :=
  {z₀ | Tendsto (fun n => φ^[n] z₀) atTop (𝓝 ζ)}

/-- Each zero's basin contains a neighborhood of the zero. -/
theorem basin_mem_nhds {ζ : ℂ} (hζ : quartEx ζ = 0) : basin quartPhi ζ ∈ 𝓝 ζ := by
  obtain ⟨⟨N, hN, hconv⟩, -⟩ := dlmf_3_8_viii_local hζ
  exact Filter.mem_of_superset hN fun z hz => hconv z hz

/-- Basins of distinct points are disjoint. -/
theorem basin_disjoint {E : Type*} [TopologicalSpace E] [T2Space E] (φ : E → E) {ζ₁ ζ₂ : E}
    (h : ζ₁ ≠ ζ₂) : Disjoint (basin φ ζ₁) (basin φ ζ₂) :=
  Set.disjoint_left.mpr fun _ h1 h2 => h (tendsto_nhds_unique h1 h2)

/-- 3.8.9 commutes with multiplication by `i`. -/
theorem quartPhi_mul_I (z : ℂ) : quartPhi (Complex.I * z) = Complex.I * quartPhi z := by
  rw [quartPhi_eq, quartPhi_eq]
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [mul_pow, mul_pow, h4, h3, one_mul, eq_comm, mul_div_assoc', div_eq_div_iff
      (by simp [hz]) (by simp [hz])]
    linear_combination (-(4 * z ^ 3 * (3 * z ^ 4 + 1))) * Complex.I_sq

/-- 3.8.9 commutes with complex conjugation. -/
theorem quartPhi_conj (z : ℂ) : quartPhi ((starRingEnd ℂ) z) = (starRingEnd ℂ) (quartPhi z) := by
  rw [quartPhi_eq, quartPhi_eq]
  simp [map_div₀, map_ofNat]

/-- The basin of `iζ` is `i` times the basin of `ζ`: the four basins are rotations of each
other. -/
theorem basin_I_mul (ζ : ℂ) :
    basin quartPhi (Complex.I * ζ) = (Complex.I * ·) '' basin quartPhi ζ := by
  have hit : ∀ n z, quartPhi^[n] (Complex.I * z) = Complex.I * quartPhi^[n] z := fun n => by
    induction n with
    | zero => exact fun _ => rfl
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, quartPhi_mul_I]
  have hc : Continuous (Complex.I * · : ℂ → ℂ) := continuous_const.mul continuous_id
  have hc' : Continuous ((-Complex.I) * · : ℂ → ℂ) := continuous_const.mul continuous_id
  have hII : ∀ w : ℂ, -Complex.I * (Complex.I * w) = w := fun w => by
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  ext w
  constructor
  · intro hw
    refine ⟨-Complex.I * w, ?_, by
      show Complex.I * (-Complex.I * w) = w
      rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]⟩
    have := (hc'.tendsto _).comp hw
    simp only [basin, mem_ofPred_eq]
    convert this using 1
    · funext n
      simp only [Function.comp_apply]
      rw [← hII (quartPhi^[n] (-Complex.I * w)), ← hit, ← mul_assoc, mul_neg, Complex.I_mul_I,
        neg_neg, one_mul]
    · rw [hII]
  · rintro ⟨z, hz, rfl⟩
    have := (hc.tendsto _).comp hz
    simp only [basin, mem_ofPred_eq]
    convert this using 1
    funext n
    exact hit n z

end Azurite.DLMF
