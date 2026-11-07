/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section19Log
import Azurite.DLMF.Chapter4.Section20
import Azurite.DLMF.Chapter4.Section21
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# DLMF §4.22 Infinite Products and Partial Fractions

* 4.22.1: `dlmf_4_22_1` (Euler's product, all `z`; Mathlib's `Complex.tendsto_euler_sin_prod`).
* 4.22.2: `dlmf_4_22_2` (all `z`).
  - For non-real `z`, the sine product at `2z/π` splits into its odd-indexed factors (the cosine
    product) and its even-indexed factors (the sine product at `z/π`).
  - The cosine product converges locally uniformly (`Summable.hasProdUniformlyOn_one_add`), so it is
    continuous, and the equality extends to all `z`.
* 4.22.3 (`z ≠ nπ`): `dlmf_4_22_3`, from the Mittag-Leffler series `cot_series_rep'`.
* 4.22.4 (`z ≠ nπ`): `dlmf_4_22_4`.
  - `G(w) = ∑ₙ 1/((z − nπ)(w − nπ))` equals `(cot z − cot w)/(w − z)` for `w ≠ z` near `z`
    (by 4.22.3).
  - `G` is continuous at `z` (Weierstrass M-test), so `G(z) = −cot′(z) = csc² z`.
* 4.22.5 (`z ≠ nπ`): `dlmf_4_22_5`, from `csc z = cot(z/2) − cot z` and 4.22.3.

The products and sums over `n ≥ 1` (and the odd numbers `2n − 1`) are indexed by `n + 1`
(respectively `2n + 1`), `n ≥ 0`.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

theorem pi_ne_zero' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero

theorem summable_norm_div_succ_sq (c : ℂ) :
    Summable fun n : ℕ => ‖c / ((n : ℂ) + 1) ^ 2‖ := by
  have hA : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine (hA.mul_left ‖c‖).congr fun n => ?_
  rw [norm_div, norm_pow, norm_natCast_add_one]; ring

/-! ### The sine product 4.22.1 -/

/-- **DLMF 4.22.1**: `sin z = z ∏_{n=1}^∞ (1 − z²/(n²π²))`. The partial products converge for
every `z`, the product is multipliable, and its value gives `sin z`. -/
theorem dlmf_4_22_1 (z : ℂ) :
    Tendsto (fun N : ℕ => z * ∏ n ∈ Finset.range N, (1 - z ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2)))
        atTop (𝓝 (sin z)) ∧
      Multipliable (fun n : ℕ => 1 - z ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2)) ∧
      sin z = z * ∏' n : ℕ, (1 - z ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2)) := by
  have hπ := pi_ne_zero'
  have hT : Tendsto (fun N : ℕ => z * ∏ n ∈ Finset.range N,
      (1 - z ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2))) atTop (𝓝 (sin z)) := by
    have h := Complex.tendsto_euler_sin_prod (z / π)
    rw [show (π : ℂ) * (z / π) = z by field_simp] at h
    convert h using 2 with N
    congr 1
    refine Finset.prod_congr rfl fun n _ => ?_
    field_simp
  have hM : Multipliable (fun n : ℕ => 1 - z ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2)) := by
    apply multipliable_one_sub_of_summable
    refine ((summable_norm_div_succ_sq (z ^ 2 / π ^ 2))).congr fun n => ?_
    congr 1; field_simp
  refine ⟨hT, hM, ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hP := (hM.hasProd_iff_tendsto_nat).mpr ((hT.const_mul z⁻¹).congr fun N => by
    rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul])
  rw [hP.tprod_eq]
  field_simp

/-! ### The cotangent series 4.22.3 -/

theorem mem_integerComplement_div_pi {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π) :
    z / π ∈ integerComplement := by
  rintro ⟨n, hn⟩
  exact hz n (by rw [hn]; field_simp [pi_ne_zero'])

/-- `cot z − 1/z = ∑_{n≥1} (1/(z − nπ) + 1/(z + nπ))`, `z ≠ nπ`. -/
theorem hasSum_cot_sub_inv {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π) :
    HasSum (fun n : ℕ => 1 / (z - ((n : ℂ) + 1) * π) + 1 / (z + ((n : ℂ) + 1) * π))
      (cot z - 1 / z) := by
  have hπ := pi_ne_zero'
  have hx := mem_integerComplement_div_pi hz
  have h := ((summable_cotTerm hx).hasSum).mul_left (1 / (π : ℂ))
  rw [← cot_series_rep' hx] at h
  convert h using 1
  · funext n
    simp only [cotTerm]
    have h1 : z - ((n : ℂ) + 1) * π ≠ 0 := by
      have := hz (n + 1); push_cast at this; exact sub_ne_zero.mpr this
    have h2 : z + ((n : ℂ) + 1) * π ≠ 0 := by
      have := hz (-(n + 1)); push_cast at this
      intro h0; apply this; linear_combination h0
    field_simp
  · rw [show (π : ℂ) * (z / π) = z by field_simp]
    field_simp

/-- **DLMF 4.22.3**: `cot z = 1/z + 2z ∑_{n=1}^∞ 1/(z² − n²π²)`, `z ≠ nπ`. -/
theorem dlmf_4_22_3 {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π) :
    HasSum (fun n : ℕ => 1 / (z ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2)) ((cot z - 1 / z) / (2 * z)) ∧
      cot z = 1 / z + 2 * z * ∑' n : ℕ, 1 / (z ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2) := by
  have hz0 : z ≠ 0 := by simpa using hz 0
  have h := (hasSum_cot_sub_inv hz).div_const (2 * z)
  have hS : HasSum (fun n : ℕ => 1 / (z ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2))
      ((cot z - 1 / z) / (2 * z)) := by
    convert h using 1
    funext n
    have h1 : z - ((n : ℂ) + 1) * π ≠ 0 := by
      have := hz (n + 1); push_cast at this; exact sub_ne_zero.mpr this
    have h2 : z + ((n : ℂ) + 1) * π ≠ 0 := by
      have := hz (-(n + 1)); push_cast at this
      intro h0; apply this; linear_combination h0
    have h3 : z ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2 ≠ 0 := by
      rw [show z ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2 =
        (z - ((n : ℂ) + 1) * π) * (z + ((n : ℂ) + 1) * π) by ring]
      exact mul_ne_zero h1 h2
    field_simp
    ring
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq]
  field_simp
  ring

/-! ### The cosecant series 4.22.5 -/

theorem not_int_mul_pi_half {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π) : ∀ n : ℤ, z / 2 ≠ n * π := by
  intro n h
  exact hz (2 * n) (by push_cast; linear_combination 2 * h)

/-- **DLMF 4.22.5**: `csc z = 1/z + 2z ∑_{n=1}^∞ (−1)ⁿ/(z² − n²π²)`, `z ≠ nπ`. -/
theorem dlmf_4_22_5 {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π) :
    ∃ T : ℂ, HasSum (fun n : ℕ => (-1) ^ (n + 1) / (z ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2)) T ∧
      cscC z = 1 / z + 2 * z * T := by
  have hz0 : z ≠ 0 := by simpa using hz 0
  have hz2 := not_int_mul_pi_half hz
  set a : ℕ → ℂ := fun m => 1 / (z ^ 2 - ((m : ℂ) + 1) ^ 2 * π ^ 2) with ha
  obtain ⟨hA, hcot⟩ := dlmf_4_22_3 hz
  obtain ⟨hA', hcot'⟩ := dlmf_4_22_3 hz2
  set A := (cot z - 1 / z) / (2 * z)
  set A' := (cot (z / 2) - 1 / (z / 2)) / (2 * (z / 2))
  -- the odd-indexed terms of `a` are the series of `cot(z/2)`
  have hodd : HasSum (fun k : ℕ => a (2 * k + 1)) (A' / 4) := by
    convert hA'.div_const 4 using 1
    funext k
    simp only [ha]
    push_cast
    have h1 : (z / 2) ^ 2 - ((k : ℂ) + 1) ^ 2 * π ^ 2 ≠ 0 := by
      have := hz2 (k + 1); have := hz2 (-(k + 1)); push_cast at *
      rw [show (z / 2) ^ 2 - ((k : ℂ) + 1) ^ 2 * π ^ 2 =
        (z / 2 - ((k : ℂ) + 1) * π) * (z / 2 + ((k : ℂ) + 1) * π) by ring]
      refine mul_ne_zero (sub_ne_zero.mpr ‹_›) ?_
      intro h0; apply ‹z / 2 ≠ (-((k : ℂ) + 1)) * π›; linear_combination h0
    have h2 : z ^ 2 - (2 * (k : ℂ) + 1 + 1) ^ 2 * π ^ 2 ≠ 0 := by
      intro h0; apply h1; linear_combination h0 / 4
    rw [div_div]
    congr 1
    ring
  obtain ⟨E, hE⟩ := (hA.summable.comp_injective (fun a b h => by simpa using h) :
    Summable fun k : ℕ => a (2 * k))
  have hAE : A = E + A' / 4 := hA.unique (hE.even_add_odd hodd)
  set b : ℕ → ℂ := fun m => (-1) ^ (m + 1) / (z ^ 2 - ((m : ℂ) + 1) ^ 2 * π ^ 2) with hb
  have he : HasSum (fun k : ℕ => b (2 * k)) (-E) := by
    convert hE.neg using 1
    funext k
    simp only [hb, Function.comp_apply, pow_succ, pow_mul]
    push_cast
    ring
  have ho : HasSum (fun k : ℕ => b (2 * k + 1)) (A' / 4) := by
    convert hodd using 1
    funext k
    simp only [hb, ha, pow_succ, pow_mul]
    push_cast
    ring
  refine ⟨-E + A' / 4, he.even_add_odd ho, ?_⟩
  -- `csc z = cot(z/2) − cot z`
  have hs : sin z ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp h; exact hz k hk
  have hs2 : sin (z / 2) ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp h; exact hz2 k hk
  have hc2 : cos (z / 2) ≠ 0 := fun h => hs (by rw [sin_eq_two_mul_half z, h, mul_zero])
  have hid : cscC z = cot (z / 2) - cot z := by
    rw [cscC, cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_eq_two_mul_half z]
    have hcz : cos z = 2 * cos (z / 2) ^ 2 - 1 := by
      rw [← cos_two_mul, show 2 * (z / 2) = z by ring]
    rw [hcz]
    field_simp
    ring
  have hAt : (∑' n : ℕ, 1 / (z ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2)) = A := hA.tsum_eq
  have hAt' : (∑' n : ℕ, 1 / ((z / 2) ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2)) = A' := hA'.tsum_eq
  rw [hid, hcot, hcot', hAt, hAt', hAE]
  field_simp
  ring

/-! ### The cosine product 4.22.2 -/

theorem norm_two_mul_add_one (n : ℕ) : ‖(2 * (n : ℂ) + 1)‖ = 2 * (n : ℝ) + 1 := by
  rw [show (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast; ring

theorem norm_cosTerm_le (z : ℂ) (n : ℕ) :
    ‖4 * z ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2)‖ ≤ ‖4 * z ^ 2 / π ^ 2‖ / ((n : ℝ) + 1) ^ 2 := by
  rw [show 4 * z ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2) = 4 * z ^ 2 / π ^ 2 / (2 * (n : ℂ) + 1) ^ 2
    by field_simp, norm_div, norm_pow, norm_two_mul_add_one]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

theorem summable_cosTerm (z : ℂ) :
    Summable fun n : ℕ => ‖4 * z ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_cosTerm_le z) ?_
  refine (summable_norm_div_succ_sq (4 * z ^ 2 / π ^ 2)).congr fun n => ?_
  rw [norm_div, norm_pow, norm_natCast_add_one]

theorem mem_integerComplement_of_im_ne {x : ℂ} (hx : x.im ≠ 0) : x ∈ integerComplement := by
  rintro ⟨n, rfl⟩; exact hx (by simp)

/-- The cosine product for non-real `w`, from the sine product at `2w/π`. -/
theorem hasProd_cos_of_im_ne {w : ℂ} (hw : w.im ≠ 0) :
    HasProd (fun n : ℕ => 1 - 4 * w ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2)) (cos w) := by
  have hπ := pi_ne_zero'
  set x : ℂ := w / π with hxdef
  have hxim : x.im ≠ 0 := by
    rw [hxdef, div_ofReal_im]; exact div_ne_zero hw Real.pi_ne_zero
  have hx := mem_integerComplement_of_im_ne hxim
  have h2x := mem_integerComplement_of_im_ne (x := 2 * x) (by simpa using hxim)
  have hπx : (π : ℂ) * x = w := by rw [hxdef]; field_simp
  have E1 := (multipliable_sineTerm x).hasProd
  rw [euler_sineTerm_tprod hx, hπx] at E1
  have E2 := (multipliable_sineTerm (2 * x)).hasProd
  rw [euler_sineTerm_tprod h2x, show (π : ℂ) * (2 * x) = 2 * w by rw [← hπx]; ring] at E2
  obtain ⟨C, hC⟩ := multipliable_one_sub_of_summable (summable_cosTerm w)
  have hodd : HasProd (fun k : ℕ => 1 + sineTerm (2 * x) (2 * k + 1)) (sin w / w) := by
    convert E1 using 1
    funext k
    simp only [sineTerm]
    rw [show ((2 * k + 1 : ℕ) : ℂ) + 1 = 2 * ((k : ℂ) + 1) by push_cast; ring, mul_pow, mul_pow,
      neg_div, neg_div, mul_div_mul_left _ _ (pow_ne_zero 2 two_ne_zero)]
  have heven : HasProd (fun k : ℕ => 1 + sineTerm (2 * x) (2 * k)) C := by
    convert hC using 1
    funext k
    simp only [sineTerm, hxdef]
    push_cast
    field_simp
    ring
  have hCS := E2.unique (heven.even_mul_odd hodd)
  have hs : sin w ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp h
    exact hw (by rw [hk]; simp)
  have hw0 : w ≠ 0 := fun h => hw (by rw [h]; simp)
  have hCw : C = cos w := by
    rw [sin_two_mul] at hCS
    field_simp at hCS
    exact hCS.symm
  rw [← hCw]; exact hC

/-- **DLMF 4.22.2**: `cos z = ∏_{n=1}^∞ (1 − 4z²/((2n − 1)²π²))`, all `z`. -/
theorem dlmf_4_22_2 (z₀ : ℂ) :
    HasProd (fun n : ℕ => 1 - 4 * z₀ ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2)) (cos z₀) := by
  set f : ℕ → ℂ → ℂ := fun n z => -(4 * z ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2)) with hf
  set F : ℂ → ℂ := fun z => ∏' n : ℕ, (1 + f n z) with hF
  have hterm : ∀ z n, 1 + f n z = 1 - 4 * z ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2) := fun z n => by
    simp only [hf]; ring
  set K := Metric.closedBall z₀ 1
  have hK : IsCompact K := isCompact_closedBall z₀ 1
  set c : ℂ := 4 * ((‖z₀‖ + 1 : ℝ) : ℂ) ^ 2 / π ^ 2 with hcdef
  have hbound : ∀ n : ℕ, ∀ z ∈ K, ‖f n z‖ ≤ ‖c / ((n : ℂ) + 1) ^ 2‖ := by
    intro n z hz
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := Metric.mem_closedBall.mp hz
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖z₀‖ := by rw [← dist_eq_norm]; linarith
        _ = ‖z₀‖ + 1 := by ring
    have hc : ‖4 * z ^ 2 / π ^ 2‖ ≤ ‖c‖ := by
      rw [hcdef, norm_div, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
        Complex.norm_real (‖z₀‖ + 1), Real.norm_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz' 2) (norm_nonneg _)
    calc ‖f n z‖ ≤ ‖4 * z ^ 2 / π ^ 2‖ / ((n : ℝ) + 1) ^ 2 := by
          simpa [hf] using norm_cosTerm_le z n
      _ ≤ ‖c‖ / ((n : ℝ) + 1) ^ 2 := div_le_div_of_nonneg_right hc (by positivity)
      _ = ‖c / ((n : ℂ) + 1) ^ 2‖ := by
          rw [norm_div c (((n : ℂ) + 1) ^ 2), norm_pow, norm_natCast_add_one]
  have hU := Summable.hasProdUniformlyOn_one_add (f := f) hK (summable_norm_div_succ_sq c)
    (Filter.Eventually.of_forall fun n z hz => hbound n z hz)
    (fun n => by simp only [hf]; fun_prop)
  have hFc : ContinuousAt F z₀ := by
    have := (hU.tendstoUniformlyOn_finsetRange).continuousOn
      (Frequently.of_forall fun N => by simp only [hf]; fun_prop)
    exact this.continuousAt (Metric.closedBall_mem_nhds z₀ one_pos)
  set S : Set ℂ := {w | w.im ≠ 0}
  have hne : (𝓝[S] z₀).NeBot := by
    by_cases h0 : 0 ≤ z₀.im
    · exact neBot_nhdsWithin_of_ray z₀ I fun t ht => by
        simp only [S, mem_ofPred_eq]; simp; linarith
    · exact neBot_nhdsWithin_of_ray z₀ (-I) fun t ht => by
        simp only [S, mem_ofPred_eq]; simp; linarith
  have hFS : ∀ w ∈ S, F w = cos w := fun w hw => by
    simp only [hF, hterm]; exact (hasProd_cos_of_im_ne hw).tprod_eq
  have h1 : Tendsto F (𝓝[S] z₀) (𝓝 (F z₀)) := hFc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto F (𝓝[S] z₀) (𝓝 (cos z₀)) :=
    ((continuous_cos.tendsto z₀).mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun w hw => (hFS w hw).symm)
  have hval : F z₀ = cos z₀ := tendsto_nhds_unique h1 h2
  have hM := multipliable_one_sub_of_summable (summable_cosTerm z₀)
  rw [← hval]
  simp only [hF, hterm]
  exact hM.hasProd

/-! ### The series for `csc² z` 4.22.4 -/

/-- A point off `πℤ` stays a fixed distance away from all of `πℤ`. -/
theorem exists_norm_sub_int_mul_pi_ge {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π) :
    ∃ δ > 0, ∀ n : ℤ, δ ≤ ‖z - n * π‖ := by
  have hpi := Real.pi_pos
  set m := ⌊z.re / π⌋
  have h1 : (m : ℝ) * π ≤ z.re := by
    have := Int.floor_le (z.re / π); rwa [le_div_iff₀ hpi] at this
  have h2 : z.re < ((m : ℝ) + 1) * π := by
    have := Int.lt_floor_add_one (z.re / π); rwa [div_lt_iff₀ hpi] at this
  have hp : ∀ n : ℤ, 0 < ‖z - n * π‖ := fun n => norm_pos_iff.mpr (sub_ne_zero.mpr (hz n))
  refine ⟨min π (min ‖z - m * π‖ ‖z - ((m + 1 : ℤ) : ℂ) * π‖),
    lt_min hpi (lt_min (hp m) (hp (m + 1))), fun n => ?_⟩
  by_cases hn : n = m
  · rw [hn]; exact (min_le_right _ _).trans (min_le_left _ _)
  by_cases hn' : n = m + 1
  · rw [hn']; exact (min_le_right _ _).trans (min_le_right _ _)
  refine (min_le_left _ _).trans ?_
  have hre : |z.re - n * π| ≤ ‖z - n * π‖ := by
    have := abs_re_le_norm (z - n * π); simpa using this
  refine le_trans ?_ hre
  rcases lt_or_gt_of_ne hn with h | h
  · have : (n : ℝ) ≤ m - 1 := by exact_mod_cast (by omega : n ≤ m - 1)
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  · have : (m : ℝ) + 2 ≤ n := by exact_mod_cast (by omega : m + 2 ≤ n)
    rw [abs_of_nonpos (by nlinarith)]; nlinarith

theorem summable_norm_inv_sub_sq (z : ℂ) :
    Summable fun n : ℤ => ‖((z - n * π) ^ 2)⁻¹‖ := by
  have hπ := pi_ne_zero'
  have h := EisensteinSeries.linear_right_summable (-z / π) 1 (k := 2) (by norm_num)
  have h' : Summable fun n : ℤ => ((z - n * π) ^ 2)⁻¹ := by
    refine (h.mul_left ((π : ℂ) ^ 2)⁻¹).congr fun n => ?_
    rw [show (1 : ℤ) * (-z / π) + (n : ℂ) = -(z - n * π) / π by push_cast; field_simp; ring,
      zpow_two, ← sq, neg_div, neg_sq, div_pow, inv_div, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hπ), one_mul]
  exact h'.norm

/-- **DLMF 4.22.4**: `csc² z = ∑_{n=−∞}^{∞} 1/(z − nπ)²`, `z ≠ nπ`. -/
theorem dlmf_4_22_4 {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π) :
    HasSum (fun n : ℤ => 1 / (z - n * π) ^ 2) (cscC z ^ 2) := by
  obtain ⟨δ, hδ, hδn⟩ := exists_norm_sub_int_mul_pi_ge hz
  set B := Metric.ball z (δ / 2)
  have hB : ∀ w ∈ B, ∀ n : ℤ, ‖z - n * π‖ / 2 ≤ ‖w - n * π‖ := by
    intro w hw n
    have h1 := hδn n
    have hwz : ‖w - z‖ < δ / 2 := by rw [← dist_eq_norm]; exact hw
    have : ‖z - n * π‖ ≤ ‖w - n * π‖ + ‖w - z‖ := by
      calc ‖z - n * π‖ = ‖(w - n * π) - (w - z)‖ := by ring_nf
        _ ≤ ‖w - n * π‖ + ‖w - z‖ := norm_sub_le _ _
    linarith
  have hzn : ∀ n : ℤ, z - n * π ≠ 0 := fun n => sub_ne_zero.mpr (hz n)
  have hwn : ∀ w ∈ B, ∀ n : ℤ, w - n * π ≠ 0 := fun w hw n => by
    apply norm_pos_iff.mp
    have := hB w hw n
    have := hδn n
    linarith
  set T : ℤ → ℂ → ℂ := fun n w => 1 / ((z - n * π) * (w - n * π)) with hTdef
  have hT : ∀ n : ℤ, ∀ w ∈ B, ‖T n w‖ ≤ 2 * ‖((z - n * π) ^ 2)⁻¹‖ := by
    intro n w hw
    have hp : 0 < ‖z - n * π‖ := norm_pos_iff.mpr (hzn n)
    have := hB w hw n
    have hq : 0 < ‖w - n * π‖ := norm_pos_iff.mpr (hwn w hw n)
    simp only [hTdef, norm_div, norm_one, norm_mul, norm_inv, norm_pow]
    rw [div_le_iff₀ (mul_pos hp hq)]
    field_simp
    nlinarith
  have hu := (summable_norm_inv_sub_sq z).mul_left 2
  set G : ℂ → ℂ := fun w => ∑' n : ℤ, T n w with hG
  have hGc : ContinuousOn G B :=
    continuousOn_tsum (fun n => continuousOn_const.div (by fun_prop)
      (fun w hw => mul_ne_zero (hzn n) (hwn w hw n))) hu (fun n w hw => hT n w hw)
  have hzB : z ∈ B := Metric.mem_ball_self (half_pos hδ)
  have hGz : ContinuousAt G z := hGc.continuousAt (Metric.ball_mem_nhds z (half_pos hδ))
  have hsumm : ∀ w ∈ B, Summable fun n => T n w := fun w hw =>
    Summable.of_norm_bounded hu (fun n => hT n w hw)
  -- `G(w) = (cot z − cot w)/(w − z)` for `w ≠ z` near `z`
  have key : ∀ w ∈ B, w ≠ z → G w = (cot z - cot w) / (w - z) := by
    intro w hw hwz
    have hw' : ∀ n : ℤ, w ≠ n * π := fun n => sub_ne_zero.mp (hwn w hw n)
    set f : ℤ → ℂ := fun n => 1 / (z - n * π) - 1 / (w - n * π) with hfdef
    have hfT : ∀ n, f n = (w - z) * T n w := fun n => by
      have := hzn n; have := hwn w hw n
      simp only [hfdef, hTdef]; field_simp; ring
    have hfs : Summable f := ((hsumm w hw).mul_left (w - z)).congr fun n => (hfT n).symm
    have hs1 : Summable fun n : ℕ => f (n + 1) :=
      hfs.comp_injective (fun a b h => by simpa using h)
    have hs2 : Summable fun n : ℕ => f (-(n + 1)) :=
      hfs.comp_injective (fun a b h => by simpa using h)
    have hpair := (hasSum_cot_sub_inv hz).sub (hasSum_cot_sub_inv hw')
    have hfsum : ∑' n : ℤ, f n = cot z - cot w := by
      rw [tsum_of_add_one_of_neg_add_one hs1 hs2, add_comm _ (f 0), add_assoc,
        ← Summable.tsum_add hs1 hs2]
      have : (∑' n : ℕ, (f (n + 1) + f (-(n + 1)))) = (cot z - 1 / z) - (cot w - 1 / w) := by
        rw [← hpair.tsum_eq]
        congr 1; funext n
        simp only [hfdef]
        push_cast
        rw [show z - -((n : ℂ) + 1) * π = z + ((n : ℂ) + 1) * π by ring,
          show w - -((n : ℂ) + 1) * π = w + ((n : ℂ) + 1) * π by ring]
        ring
      rw [this]
      simp only [hfdef]
      push_cast
      simp only [zero_mul, sub_zero]
      ring
    have hTsum : ∑' n : ℤ, f n = (w - z) * G w := by
      rw [hG, ← tsum_mul_left]; exact tsum_congr hfT
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr hwz
    rw [eq_div_iff hwz', mul_comm, ← hTsum, hfsum]
  have hs : sin z ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp h; exact hz k hk
  have hslope := hasDerivAt_iff_tendsto_slope.mp (dlmf_4_20_6 hs)
  have hlim : Tendsto G (𝓝[≠] z) (𝓝 (cscC z ^ 2)) := by
    have := hslope.neg
    rw [neg_neg] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds z (half_pos hδ))] with w hw hwB
    rw [key w hwB hw, slope_def_field]
    have : w - z ≠ 0 := sub_ne_zero.mpr hw
    field_simp
    ring
  have hGval : G z = cscC z ^ 2 :=
    tendsto_nhds_unique (hGz.tendsto.mono_left nhdsWithin_le_nhds) hlim
  have := (hsumm z hzB).hasSum
  rw [show (∑' n : ℤ, T n z) = G z from rfl, hGval] at this
  convert this using 1
  funext n
  simp only [hTdef, sq]

end Azurite.DLMF
