/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5LaplaceExample

/-!
# DLMF §2.5(iii), Example (2.5.45, 2.5.48–2.5.49): the expansion of `ℒ[1/(1+t)](ζ)`

* 2.5.45: `ℒh(ζ) = ∫₀^∞ e^{−ζt}/(1 + t) dt` (`dlmf_2_5_45`).
* 2.5.48: "insertion of these results into (2.5.43) yields"
  `ℒh(ζ) ∼ (−ln ζ) ∑ ζ^k/k! + ∑ ψ(k+1) ζ^k/k!` as `ζ → 0+` (`dlmf_2_5_48`): for every `K`,
  `ℒh(ζ) = ∑_{k≤K} (−ln ζ + ψ(k+1)) ζ^k/k! + O(ζ^{K+1/2})`. In 2.5.43 (with `L = K + 3/2`) the
  residues of the `𝓜h₁`- and `𝓜h₂`-terms at `z = k + 1` combine into the residue 2.5.46 of
  `−ζ^{z−1} Γ(1 − z) π csc(πz)`.
* 2.5.49: `ℒh(ζ) = e^ζ E₁(ζ)` with `E₁(ζ) = ∫_ζ^∞ e^{−v}/v dv` (6.2.2; `expIntegralE₁`,
  `dlmf_2_5_49`), by the substitutions `t ↦ t + 1` and `u ↦ ζu`. DLMF's verification of 2.5.48
  through the series 6.6.3 of `E₁` belongs to Chapter 6 and is not reproduced here.
-/

open MeasureTheory Filter Topology Set Complex Metric Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-- **DLMF 2.5.45**: `ℒh(ζ) = ∫₀^∞ e^{−ζt}/(1 + t) dt`. -/
theorem dlmf_2_5_45 (ζ : ℂ) :
    laplace oneDivOneAdd ζ = ∫ t in Ioi (0 : ℝ), cexp (-(ζ * t)) / (1 + t) := by
  simp only [laplace, oneDivOneAdd, mul_one_div]

/-! ### 2.5.48 -/

/-- The singularities of `Γ(1 − z) 𝓜h₂(z)` for `h = 1/(1+t)` are the positive integers. -/
theorem mem_sing_range_succ_iff {z : ℂ} :
    z ∈ sing (range fun s : ℕ => (s : ℂ) + 1) ↔ ∃ n : ℕ, z = n + 1 := by
  simp only [sing, mem_union, mem_range, mem_ofPred_eq]
  constructor
  · rintro (⟨n, rfl⟩ | ⟨n, rfl⟩) <;> exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact Or.inr ⟨n, rfl⟩

/-- A point with positive real part that is not a positive integer is not an integer. -/
theorem not_int_of_re_pos {z : ℂ} (hre : 0 < z.re) (hint : ∀ m : ℕ, z ≠ m + 1) :
    ∀ m : ℤ, z ≠ m := fun m hm => by
  rcases le_or_gt m 0 with hm0 | hm0
  · have := congrArg Complex.re hm
    simp at this
    have : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
    linarith
  · refine hint (m.toNat - 1) ?_
    have h' : ((m.toNat - 1 : ℕ) : ℤ) + 1 = m := by omega
    have h'' : (m : ℂ) = ((((m.toNat - 1 : ℕ) : ℤ) + 1 : ℤ) : ℂ) := by rw [h']
    rw [hm, h'']
    push_cast
    ring

/-- The combined residue at `z = n + 1` of the two terms of 2.5.43, for `h = 1/(1+t)`: it is the
residue 2.5.46 of `−ζ^{z−1} Γ(1 − z) π csc(πz)`. -/
theorem residue_add_eq_dlmf_2_5_46 {ζ : ℝ} (hζ : 0 < ζ) (n : ℕ) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁)
    (hR₂ : 0 < R₂)
    (h₁ : ∀ z ∈ ball ((n : ℂ) + 1) R₁, z ≠ n + 1 → 0 < z.re ∧ ∀ m : ℕ, z ≠ m + 1)
    (h₂ : ∀ z ∈ ball ((n : ℂ) + 1) R₂, z ≠ n + 1 → ∀ m : ℕ, z ≠ m + 1) :
    residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * mellin (trunc₁ oneDivOneAdd) z)))
        (n + 1) R₁ +
      residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * contH₂ z))) (n + 1) R₂ =
      (-(Real.log ζ : ℂ) + digamma (n + 1)) * (ζ : ℂ) ^ (n : ℂ) / n ! := by
  set r : ℝ := min (min R₁ R₂) 1 with hr
  have hr0 : 0 < r := lt_min (lt_min hR₁ hR₂) one_pos
  have hr1 : r ≤ R₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ R₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ 1 := min_le_right _ _
  have hball₁ : ball ((n : ℂ) + 1) r ⊆ ball ((n : ℂ) + 1) R₁ := ball_subset_ball hr1
  have hball₂ : ball ((n : ℂ) + 1) r ⊆ ball ((n : ℂ) + 1) R₂ := ball_subset_ball hr2
  have hannb : ∀ {ρ : ℝ} {z : ℂ}, z ∈ annulus ((n : ℂ) + 1) 0 ρ →
      z ∈ ball ((n : ℂ) + 1) ρ ∧ z ≠ n + 1 := fun hz =>
    ⟨by rw [mem_ball, dist_eq_norm]; exact hz.2, fun h => by
      have := hz.1
      rw [h, sub_self, norm_zero] at this
      exact lt_irrefl _ this⟩
  -- the two terms are analytic on the punctured discs
  have hF₁d : DifferentiableOn ℂ
      (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * mellin (trunc₁ oneDivOneAdd) z)))
      (annulus ((n : ℂ) + 1) 0 R₁) := fun z hz => by
    obtain ⟨hzb, hzn⟩ := hannb hz
    obtain ⟨hre, hint⟩ := h₁ z hzb hzn
    exact ((((differentiable_cpow_sub_one hζ) z).mul ((differentiableAt_Gamma_one_sub hint).mul
      (laplaceSmallSetup_oneDivOneAdd.differentiableAt_h₁
        (by simpa using hre)))).neg).differentiableWithinAt
  have hF₂d : DifferentiableOn ℂ (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * contH₂ z)))
      (annulus ((n : ℂ) + 1) 0 R₂) := fun z hz => by
    obtain ⟨hzb, hzn⟩ := hannb hz
    have hint := h₂ z hzb hzn
    exact ((((differentiable_cpow_sub_one hζ) z).mul ((differentiableAt_Gamma_one_sub hint).mul
      (differentiableAt_contH₂ hint))).neg).differentiableWithinAt
  have hsub₁ : annulus ((n : ℂ) + 1) 0 r ⊆ annulus ((n : ℂ) + 1) 0 R₁ :=
    fun z hz => ⟨hz.1, hz.2.trans_le hr1⟩
  have hsub₂ : annulus ((n : ℂ) + 1) 0 r ⊆ annulus ((n : ℂ) + 1) 0 R₂ :=
    fun z hz => ⟨hz.1, hz.2.trans_le hr2⟩
  rw [residue_eq_residue hF₁d hr0 hr1, residue_eq_residue hF₂d hr0 hr2,
    ← residue_add hr0 (hF₁d.mono hsub₁) (hF₂d.mono hsub₂)]
  rw [residue_congr hr0 (G := fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * (π / sin (π * z)))))
    fun z hz => by
      obtain ⟨hzb, hzn⟩ := hannb hz
      obtain ⟨hre, hint⟩ := h₁ z (hball₁ hzb) hzn
      rw [contH₂_eq_sub hre (not_int_of_re_pos hre hint)]
      ring]
  exact dlmf_2_5_46 hζ n hr0 hr3

/-- **DLMF 2.5.48**: `ℒh(ζ) ∼ (−ln ζ) ∑ ζ^k/k! + ∑ ψ(k+1) ζ^k/k!` as `ζ → 0+`, for
`h(t) = 1/(1 + t)`: for every `K`,
`ℒh(ζ) = ∑_{k≤K} (−ln ζ + ψ(k + 1)) ζ^k/k! + O(ζ^{K+1/2})`. -/
theorem dlmf_2_5_48 (K : ℕ) :
    ∃ E : ℝ → ℂ, IsBigODLMF (𝓝[>] (0 : ℝ)) E (fun ζ : ℝ => (ζ : ℂ) ^ ((K : ℂ) + 1 / 2)) ∧
      ∀ ζ : ℝ, 0 < ζ → laplace oneDivOneAdd ζ =
        ∑ k ∈ Finset.range (K + 1),
          (-(Real.log ζ : ℂ) + digamma (k + 1)) * (ζ : ℂ) ^ (k : ℂ) / k ! + E ζ := by
  have H := laplaceSmallSetup_oneDivOneAdd
  have hG := H.mellinH₂Cont_zero
  set L : ℝ := K + 3 / 2 with hLdef
  have hL1 : 1 < L := by rw [hLdef]; linarith [K.cast_nonneg (α := ℝ)]
  have hLint : ∀ n : ℕ, (n : ℝ) + 1 ≠ L := fun n h => by
    rw [hLdef] at h
    have : (2 : ℝ) * n + 2 = 2 * K + 3 := by linarith
    have : (2 : ℤ) * n + 2 = 2 * K + 3 := by exact_mod_cast this
    omega
  have hL : ∀ z ∈ sing (range fun s : ℕ => (s : ℂ) + 1), z.re ≠ L := fun z hz => by
    obtain ⟨n, rfl⟩ := mem_sing_range_succ_iff.mp hz
    simpa using hLint n
  have hp₂ : (-1 / 2 : ℝ) < min 1 ((fun s : ℕ => (s : ℂ) + 1) 0).re := by
    simp only [Nat.cast_zero, zero_add, one_re, min_self]
    norm_num
  have hp₂' : ∀ z ∈ sing (range fun s : ℕ => (s : ℂ) + 1), z.re ≠ -1 / 2 := fun z hz => by
    obtain ⟨n, rfl⟩ := mem_sing_range_succ_iff.mp hz
    simp
    linarith [n.cast_nonneg (α := ℝ)]
  refine ⟨fun ζ => (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (ζ : ℂ) ^ ((L : ℂ) + y * I - 1) *
    (Gamma (1 - (L + y * I)) * (mellin (trunc₁ oneDivOneAdd) (L + y * I) + contH₂ (L + y * I))),
    ?_, fun ζ hζ => ?_⟩
  · have := H.dlmf_2_5_43_remainder hG hL1 hL
    have e : (fun ζ : ℝ => (ζ : ℂ) ^ ((L : ℂ) - 1)) = fun ζ : ℝ => (ζ : ℂ) ^ ((K : ℂ) + 1 / 2) := by
      funext ζ
      congr 1
      rw [hLdef]
      push_cast
      ring
    rw [e] at this
    exact this
  obtain ⟨S₁, S₂, R₁, R₂, hS₁, hR₁, hS₂, hR₂, heq⟩ := H.dlmf_2_5_43 hG hp₂ hp₂' hL1 hL hζ
  rw [heq]
  congr 1
  -- both index sets are `{1, …, K + 1}`
  have hinj : Function.Injective fun n : ℕ => (n : ℂ) + 1 := fun m n hmn => by
    have := congrArg Complex.re hmn
    simp at this
    exact_mod_cast this
  have hlt : ∀ n : ℕ, (n : ℝ) + 1 < L ↔ n < K + 1 := fun n => by
    rw [hLdef]
    constructor
    · intro h
      have : (n : ℝ) < K + 1 := by linarith
      exact_mod_cast this
    · intro h
      have : (n : ℝ) + 1 ≤ K + 1 := by exact_mod_cast h
      linarith
  have hS₁' : S₁ = (Finset.range (K + 1)).image fun n : ℕ => (n : ℂ) + 1 := by
    ext z
    rw [hS₁, Finset.mem_image]
    constructor
    · rintro ⟨n, rfl, hn⟩
      exact ⟨n, Finset.mem_range.mpr ((hlt n).mp hn), rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, rfl, (hlt n).mpr (Finset.mem_range.mp hn)⟩
  have hS₂' : S₂ = (Finset.range (K + 1)).image fun n : ℕ => (n : ℂ) + 1 := by
    ext z
    rw [hS₂, Finset.mem_image]
    constructor
    · rintro ⟨hz, -, hzL⟩
      obtain ⟨n, rfl⟩ := mem_sing_range_succ_iff.mp hz
      exact ⟨n, Finset.mem_range.mpr ((hlt n).mp (by simpa using hzL)), rfl⟩
    · rintro ⟨n, hn, rfl⟩
      refine ⟨mem_sing_range_succ_iff.mpr ⟨n, rfl⟩, by simp; linarith [n.cast_nonneg (α := ℝ)],
        by simpa using (hlt n).mpr (Finset.mem_range.mp hn)⟩
  rw [hS₁', hS₂', Finset.sum_image fun m _ n _ hmn => hinj hmn,
    Finset.sum_image fun m _ n _ hmn => hinj hmn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hmem₁ : ((n : ℂ) + 1) ∈ S₁ := by rw [hS₁']; exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hmem₂ : ((n : ℂ) + 1) ∈ S₂ := by rw [hS₂']; exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  obtain ⟨hR₁0, hR₁'⟩ := hR₁ _ hmem₁
  obtain ⟨hR₂0, hR₂'⟩ := hR₂ _ hmem₂
  refine residue_add_eq_dlmf_2_5_46 hζ n hR₁0 hR₂0 (fun z hz hzn => ?_) fun z hz hzn => ?_
  · obtain ⟨hre, hint⟩ := hR₁' z hz hzn
    exact ⟨by simpa using hre, hint⟩
  · have hz' := hR₂' z hz hzn
    rw [mem_sing_range_succ_iff] at hz'
    push Not at hz'
    exact hz'

/-! ### 2.5.49 -/

/-- **DLMF 6.2.2**: the exponential integral `E₁(x) = ∫_x^∞ e^{−v}/v dv`, for real `x > 0`. -/
noncomputable def expIntegralE₁ (x : ℝ) : ℝ := ∫ v in Ioi x, Real.exp (-v) / v

/-- **DLMF 2.5.49**: `ℒ[1/(1+t)](ζ) = e^ζ E₁(ζ)` for `ζ > 0` (substitute `t ↦ t + 1`, then
`u ↦ ζu`). -/
theorem dlmf_2_5_49 {ζ : ℝ} (hζ : 0 < ζ) :
    laplace oneDivOneAdd ζ = ((Real.exp ζ * expIntegralE₁ ζ : ℝ) : ℂ) := by
  rw [dlmf_2_5_45]
  -- shift `t ↦ t + 1`
  set g : ℝ → ℂ := (Ioi 1).indicator fun u => cexp (-((ζ : ℂ) * (u - 1))) / u with hg
  have hζ0 : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  have h1 : (∫ t in Ioi (0 : ℝ), cexp (-((ζ : ℂ) * t)) / (1 + t)) = ∫ u in Ioi (1 : ℝ),
      cexp (-((ζ : ℂ) * (u - 1))) / u := by
    have e1 : (∫ t in Ioi (0 : ℝ), cexp (-((ζ : ℂ) * t)) / (1 + t)) = ∫ t, g (t + 1) := by
      rw [← integral_indicator measurableSet_Ioi]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hg]
      by_cases ht : 0 < t
      · rw [indicator_of_mem (mem_Ioi.mpr ht),
          indicator_of_mem (mem_Ioi.mpr (by linarith : (1 : ℝ) < t + 1))]
        push_cast
        ring_nf
      · rw [indicator_of_notMem (by simpa using ht),
          indicator_of_notMem (by simp only [mem_Ioi, not_lt]; linarith)]
    have e2 : (∫ t, g (t + 1)) = ∫ u in Ioi (1 : ℝ), cexp (-((ζ : ℂ) * (u - 1))) / u := by
      rw [integral_add_right_eq_self g 1, hg, integral_indicator measurableSet_Ioi]
    rw [e1, e2]
  -- factor `e^ζ` and scale `u ↦ ζu`
  have h2 : (∫ u in Ioi (1 : ℝ), cexp (-((ζ : ℂ) * (u - 1))) / u) =
      cexp ζ * ∫ u in Ioi (1 : ℝ), cexp (-((ζ : ℂ) * u)) / u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show -((ζ : ℂ) * (u - 1)) = ζ + -((ζ : ℂ) * u) by ring, Complex.exp_add]
    ring
  have h3 : (∫ u in Ioi (1 : ℝ), cexp (-((ζ : ℂ) * u)) / u) =
      ∫ v in Ioi ζ, cexp (-(v : ℂ)) / v := by
    have := integral_comp_mul_left_Ioi (fun v : ℝ => cexp (-(v : ℂ)) / v) 1 hζ
    rw [mul_one, Complex.real_smul, ofReal_inv] at this
    have e : (∫ u in Ioi (1 : ℝ), cexp (-((ζ : ℂ) * u)) / u) =
        (ζ : ℂ) * ∫ x in Ioi (1 : ℝ), cexp (-((ζ * x : ℝ) : ℂ)) / ((ζ * x : ℝ) : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu : (1 : ℝ) < u := hu
      have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
      push_cast
      field_simp
    rw [e, this, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  -- the real integral
  have h4 : (∫ v in Ioi ζ, cexp (-(v : ℂ)) / v) = ((expIntegralE₁ ζ : ℝ) : ℂ) := by
    rw [expIntegralE₁, show ((∫ v in Ioi ζ, Real.exp (-v) / v : ℝ) : ℂ) =
      @RCLike.ofReal ℂ _ (∫ v in Ioi ζ, Real.exp (-v) / v) from rfl, ← integral_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    show cexp (-(v : ℂ)) / v = ((Real.exp (-v) / v : ℝ) : ℂ)
    push_cast
    rfl
  rw [h1, h2, h3, h4, ← ofReal_exp]
  push_cast
  ring

end Azurite.DLMF
