/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5LaplaceExpansion

/-!
# DLMF §2.5(iii), 2.5.44: the explicit expansion for `κ = 0`

If `κ = 0` in 2.5.18, `c > −1` in 2.5.20 and no exponent `βₙ` is a positive integer, the residues
of 2.5.43 are explicit:

* at the poles `z = n + 1` of `Γ(1 − z)`: `res[−ζ^{z−1} Γ(1 − z) A(z)] = (−ζ)^n/n! · A(n + 1)`
  (`residue_neg_cpow_Gamma_mul`, from `Γ(w) = GammaNum n w/(w + n)` and
  `GammaNum n (−n) = (−1)^n/n!`);
* at the simple poles `βₙ` of `𝓜h₂` with principal part `−bₙ/(z − βₙ)`:
  `res[−ζ^{z−1} Γ(1 − z) 𝓜h₂(z)] = bₙ Γ(1 − βₙ) ζ^{βₙ−1}` (`residue_neg_cpow_Gamma_mul_pole`),

giving **2.5.44**:
`ℒh(ζ) = ∑_{ℜβₙ<L} bₙ Γ(1 − βₙ) ζ^{βₙ−1} + ∑_{n+1<L} ((−ζ)^n/n!) 𝓜h(n + 1) + O(ζ^{L−1})` as
`ζ → 0+`, for every `L > 1` off the real parts of the singularities (`dlmf_2_5_44`); here
`𝓜h(n + 1) = 𝓜h₁(n + 1) + 𝓜h₂(n + 1)` with `𝓜h₂` continued (2.5.27–2.5.28). DLMF's
`∼` with both sums infinite is this statement for every `L`.
-/

open MeasureTheory Filter Topology Set Complex Metric Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Residues at the poles of `Γ(1 − z)` -/

/-- If `F` is analytic on the punctured disc `annulus s 0 R`, its residue may be computed with any
smaller radius. -/
theorem residue_eq_residue_min {F : ℂ → ℂ} {s : ℂ} {R : ℝ} (hR : 0 < R) (r : ℝ) (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (annulus s 0 R)) : residue F s R = residue F s (min R r) :=
  residue_eq_residue hF (lt_min hR hr) (min_le_left _ _)

theorem differentiable_cpow_sub_one {ζ : ℝ} (hζ : 0 < ζ) :
    Differentiable ℂ fun z : ℂ => (ζ : ℂ) ^ (z - 1) :=
  (differentiable_id.sub_const 1).const_cpow (Or.inl (ofReal_ne_zero.mpr hζ.ne'))

/-- `res_{z=n+1} [−ζ^{z−1} Γ(1 − z) A(z)] = (−1)^n/n! · ζ^n · A(n + 1)` when `A` is analytic on the
disc and the punctured disc contains no pole of `Γ(1 − z)`. -/
theorem residue_neg_cpow_Gamma_mul {ζ : ℝ} (hζ : 0 < ζ) {A : ℂ → ℂ} (n : ℕ) {R : ℝ} (hR : 0 < R)
    (hA : DifferentiableOn ℂ A (ball ((n : ℂ) + 1) R))
    (hfree : ∀ z ∈ ball ((n : ℂ) + 1) R, z ≠ n + 1 → ∀ m : ℕ, z ≠ m + 1) :
    residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * A z))) (n + 1) R =
      (-1) ^ n / n ! * (ζ : ℂ) ^ (n : ℂ) * A (n + 1) := by
  have hpole : ∀ z ∈ ball ((n : ℂ) + 1) R, z ≠ n + 1 → ∀ j ≤ n, (1 - z) + (j : ℂ) ≠ 0 :=
    fun z hz hzn j _ h => hfree z hz hzn j (by linear_combination -h)
  -- `F` is analytic on the punctured disc
  have hF : DifferentiableOn ℂ (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * A z)))
      (annulus ((n : ℂ) + 1) 0 R) := by
    intro z hz
    have hzb : z ∈ ball ((n : ℂ) + 1) R := by rw [mem_ball, dist_eq_norm]; exact hz.2
    have hzn : z ≠ n + 1 := fun h => by
      have := hz.1
      rw [h, sub_self, norm_zero] at this
      exact lt_irrefl _ this
    exact (((differentiable_cpow_sub_one hζ z).mul ((differentiableAt_Gamma_one_sub
      (hfree z hzb hzn)).mul
        (hA.differentiableAt (isOpen_ball.mem_nhds hzb)))).neg).differentiableWithinAt
  rw [residue_eq_residue_min hR 1 one_pos hF]
  set R' : ℝ := min R 1 with hR'
  have hR'0 : 0 < R' := lt_min hR one_pos
  have hsub : ball ((n : ℂ) + 1) R' ⊆ ball ((n : ℂ) + 1) R := ball_subset_ball (min_le_left _ _)
  have hB : DifferentiableOn ℂ (fun z => (ζ : ℂ) ^ (z - 1) * A z * GammaNum n (1 - z))
      (ball ((n : ℂ) + 1) R') := by
    refine ((differentiable_cpow_sub_one hζ).differentiableOn.mul (hA.mono hsub)).mul ?_
    refine (differentiableOn_GammaNum n).comp
      ((differentiableOn_const _).sub differentiableOn_id) ?_
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    rw [show (1 : ℂ) - z - -(n : ℂ) = -(z - (n + 1)) by ring, norm_neg]
    exact hz.trans_le (min_le_right _ _)
  rw [residue_eq_of_eq_div_add hR'0 hB (differentiableOn_const 0) fun z hz => by
    have hzb : z ∈ ball ((n : ℂ) + 1) R := hsub (by rw [mem_ball, dist_eq_norm]; exact hz.2)
    have hzn : z ≠ n + 1 := fun h => by
      have := hz.1
      rw [h, sub_self, norm_zero] at this
      exact lt_irrefl _ this
    rw [show -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * A z)) =
      (ζ : ℂ) ^ (z - 1) * A z * -Gamma (1 - z) by ring, neg_Gamma_one_sub_eq (hpole z hzb hzn)]
    ring]
  rw [show (1 : ℂ) - ((n : ℂ) + 1) = -(n : ℂ) by ring, GammaNum_neg_nat, add_sub_cancel_right]
  ring

/-- `res_{z=β} [−ζ^{z−1} Γ(1 − z) G(z)] = b Γ(1 − β) ζ^{β−1}` when `G(z) = −b/(z − β) + g(z)` near
`β` with `g` analytic at `β`, and `β` is not a pole of `Γ(1 − z)`. -/
theorem residue_neg_cpow_Gamma_mul_pole {ζ : ℝ} (hζ : 0 < ζ) {G g : ℂ → ℂ} {b β : ℂ}
    (hg : AnalyticAt ℂ g β) (hGeq : ∀ᶠ z in 𝓝[≠] β, G z = -b / (z - β) + g z)
    (hβ : ∀ m : ℕ, β ≠ m + 1) {R : ℝ} (hR : 0 < R)
    (hG : DifferentiableOn ℂ G (annulus β 0 R))
    (hfree : ∀ z ∈ ball β R, z ≠ β → ∀ m : ℕ, z ≠ m + 1) :
    residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * G z))) β R =
      b * Gamma (1 - β) * (ζ : ℂ) ^ (β - 1) := by
  -- radii on which the principal part and the analyticity of `g` hold
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.mem_nhdsWithin_iff.mp hGeq
  obtain ⟨r₂, hr₂, hr₂'⟩ := Metric.isOpen_iff.mp (isOpen_analyticAt ℂ g) β hg
  have hΓd : ∀ z ∈ ball β R, DifferentiableAt ℂ (fun z => Gamma (1 - z)) z := fun z hz => by
    by_cases hzβ : z = β
    · subst hzβ
      exact differentiableAt_Gamma_one_sub hβ
    · exact differentiableAt_Gamma_one_sub (hfree z hz hzβ)
  have hF : DifferentiableOn ℂ (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * G z)))
      (annulus β 0 R) := by
    intro z hz
    have hzb : z ∈ ball β R := by rw [mem_ball, dist_eq_norm]; exact hz.2
    exact (((differentiable_cpow_sub_one hζ z).mul ((hΓd z hzb).mul
      (hG.differentiableAt ((isOpen_annulus β 0 R).mem_nhds hz)))).neg).differentiableWithinAt
  rw [residue_eq_residue_min hR (min r₁ r₂) (lt_min hr₁ hr₂) hF]
  set R' : ℝ := min R (min r₁ r₂) with hR'
  have hR'0 : 0 < R' := lt_min hR (lt_min hr₁ hr₂)
  have hsubR : ball β R' ⊆ ball β R := ball_subset_ball (min_le_left _ _)
  have hsub₁ : ball β R' ⊆ ball β r₁ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hsub₂ : ball β R' ⊆ ball β r₂ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hB : DifferentiableOn ℂ (fun z => b * ((ζ : ℂ) ^ (z - 1) * Gamma (1 - z))) (ball β R') :=
    fun z hz => (((differentiable_cpow_sub_one hζ z).mul
      (hΓd z (hsubR hz))).const_mul b).differentiableWithinAt
  have hg' : DifferentiableOn ℂ (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * g z)))
      (ball β R') :=
    fun z hz => (((differentiable_cpow_sub_one hζ z).mul ((hΓd z (hsubR hz)).mul
      (hr₂' (hsub₂ hz)).differentiableAt)).neg).differentiableWithinAt
  rw [residue_eq_of_eq_div_add hR'0 hB hg' fun z hz => by
    have hzb : z ∈ ball β R' := by rw [mem_ball, dist_eq_norm]; exact hz.2
    have hzβ : z ≠ β := fun h => by
      have := hz.1
      rw [h, sub_self, norm_zero] at this
      exact lt_irrefl _ this
    have hzeq : G z = -b / (z - β) + g z := hr₁' ⟨hsub₁ hzb, hzβ⟩
    have hzβ' : z - β ≠ 0 := sub_ne_zero.mpr hzβ
    rw [hzeq]
    field_simp
    ring]
  ring

/-! ### 2.5.44 -/

namespace LaplaceSmallSetup

variable {h : ℝ → ℂ} {bs β : ℕ → ℂ} {p c : ℝ} (H : LaplaceSmallSetup h bs β 0 p c)
include H

/-- The singularities of `Γ(1 − z) 𝓜h₂(z)` in `p₂ < ℜz < L` (`κ = 0`, no `βₛ` an integer) are the
`βₛ` with `ℜβₛ < L` and the integers `1 ≤ n + 1 < L`. -/
theorem sing_range_β_eq {p₂ L : ℝ} (hp₂ : p₂ < min 1 (β 0).re) {N K : ℕ}
    (hN : ∀ s, (β s).re < L ↔ s < N) (hK : ∀ n : ℕ, (n : ℝ) + 1 < L ↔ n < K) {S : Finset ℂ}
    (hS : ∀ z, z ∈ S ↔ z ∈ sing (range β) ∧ p₂ < z.re ∧ z.re < L) :
    S = (Finset.range K).image (fun n : ℕ => (n : ℂ) + 1) ∪ (Finset.range N).image β := by
  have h1 := (lt_min_iff.mp hp₂).1
  have h2 := (lt_min_iff.mp hp₂).2
  ext z
  rw [hS, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨hz, hp, hL⟩
    rcases hz with ⟨s, rfl⟩ | ⟨n, rfl⟩
    · exact Or.inr ⟨s, Finset.mem_range.mpr ((hN s).mp hL), rfl⟩
    · refine Or.inl ⟨n, Finset.mem_range.mpr ((hK n).mp ?_), rfl⟩
      simpa using hL
  · rintro (⟨n, hn, rfl⟩ | ⟨s, hs, rfl⟩)
    · refine ⟨Or.inr ⟨n, rfl⟩, ?_, ?_⟩
      · simp
        linarith [n.cast_nonneg (α := ℝ)]
      · simpa using (hK n).mpr (Finset.mem_range.mp hn)
    · refine ⟨Or.inl ⟨s, rfl⟩, ?_, (hN s).mpr (Finset.mem_range.mp hs)⟩
      exact lt_of_lt_of_le h2 (H.β_mono.monotone (Nat.zero_le s))

/-- **DLMF 2.5.44**: if `κ = 0`, `c > −1` and no `βₙ` is a positive integer, then for every
`L > 1` that is neither an integer nor a real part of a `βₙ`, with `N`, `K` counting the `βₙ` with
`ℜβₙ < L` and the integers `n + 1 < L`,
`ℒh(ζ) = ∑_{n<N} bₙ Γ(1 − βₙ) ζ^{βₙ−1} + ∑_{n<K} ((−ζ)^n/n!) 𝓜h(n + 1) + O(ζ^{L−1})`,
`ζ → 0+`, where `𝓜h(n + 1) = 𝓜h₁(n + 1) + 𝓜h₂(n + 1)` with `𝓜h₂` continued
(`mellinTrunc₂ContZero`). Letting `L → ∞` gives DLMF's expansion. -/
theorem dlmf_2_5_44 (hβℕ : ∀ s (n : ℕ), β s ≠ n + 1) {L : ℝ} (hL1 : 1 < L)
    (hLβ : ∀ s, (β s).re ≠ L) (hLn : ∀ n : ℕ, (n : ℝ) + 1 ≠ L) {N K : ℕ}
    (hN : ∀ s, (β s).re < L ↔ s < N) (hK : ∀ n : ℕ, (n : ℝ) + 1 < L ↔ n < K) :
    ∃ E : ℝ → ℂ, IsBigODLMF (𝓝[>] (0 : ℝ)) E (fun ζ : ℝ => (ζ : ℂ) ^ ((L : ℂ) - 1)) ∧
      ∀ ζ : ℝ, 0 < ζ → laplace h ζ =
        ∑ s ∈ Finset.range N, bs s * Gamma (1 - β s) * (ζ : ℂ) ^ (β s - 1) +
        ∑ n ∈ Finset.range K, (-(ζ : ℂ)) ^ n / n ! *
          (mellin (trunc₁ h) (n + 1) + mellinTrunc₂ContZero h bs β (n + 1)) +
        E ζ := by
  have hG := H.mellinH₂Cont_zero
  have hL : ∀ z ∈ sing (range β), z.re ≠ L := fun z hz => by
    rcases hz with ⟨s, rfl⟩ | ⟨n, rfl⟩
    · exact hLβ s
    · simpa using hLn n
  set p₂ : ℝ := min 1 (β 0).re - 1 with hp₂def
  have hp₂ : p₂ < min 1 (β 0).re := by rw [hp₂def]; linarith
  have hp₂' : ∀ z ∈ sing (range β), z.re ≠ p₂ := fun z hz => by
    rcases hz with ⟨s, rfl⟩ | ⟨n, rfl⟩
    · have := H.β_mono.monotone (Nat.zero_le s)
      have := min_le_right 1 (β 0).re
      rw [hp₂def]
      linarith
    · have := min_le_left 1 (β 0).re
      rw [hp₂def]
      simp
      linarith [n.cast_nonneg (α := ℝ)]
  refine ⟨fun ζ => (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (ζ : ℂ) ^ ((L : ℂ) + y * I - 1) *
    (Gamma (1 - (L + y * I)) *
      (mellin (trunc₁ h) (L + y * I) + mellinTrunc₂ContZero h bs β (L + y * I))),
    H.dlmf_2_5_43_remainder hG hL1 hL, fun ζ hζ => ?_⟩
  obtain ⟨S₁, S₂, R₁, R₂, hS₁, hR₁, hS₂, hR₂, heq⟩ := H.dlmf_2_5_43 hG hp₂ hp₂' hL1 hL hζ
  rw [heq]
  congr 1
  -- the two residue sums
  have hS₁' : S₁ = (Finset.range K).image fun n : ℕ => (n : ℂ) + 1 := by
    ext z
    rw [hS₁, Finset.mem_image]
    constructor
    · rintro ⟨n, rfl, hn⟩
      exact ⟨n, Finset.mem_range.mpr ((hK n).mp hn), rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, rfl, (hK n).mpr (Finset.mem_range.mp hn)⟩
  have hS₂' := H.sing_range_β_eq hp₂ hN hK hS₂
  have hinj : Function.Injective fun n : ℕ => (n : ℂ) + 1 := fun m n hmn => by
    have := congrArg Complex.re hmn
    simp at this
    exact_mod_cast this
  have hβinj : Function.Injective β := fun m n hmn => H.β_mono.injective (by simp [hmn])
  have hdisj : Disjoint ((Finset.range K).image fun n : ℕ => (n : ℂ) + 1)
      ((Finset.range N).image β) := by
    rw [Finset.disjoint_left]
    rintro z hz hz'
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hz'
    exact hβℕ s n hs
  -- the residues of the first sum, at `z = n + 1`
  have hres₁ : ∀ n ∈ Finset.range K,
      residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * mellin (trunc₁ h) z))) (n + 1)
        (R₁ (n + 1)) = (-1) ^ n / n ! * (ζ : ℂ) ^ (n : ℂ) * mellin (trunc₁ h) (n + 1) :=
      fun n hn => by
    have hmem : ((n : ℂ) + 1) ∈ S₁ := (hS₁ _).mpr ⟨n, rfl, (hK n).mpr (Finset.mem_range.mp hn)⟩
    obtain ⟨hRpos, hfree⟩ := hR₁ _ hmem
    refine residue_neg_cpow_Gamma_mul hζ n hRpos (fun z hz => ?_) fun z hz hzn => (hfree z hz hzn).2
    by_cases hzn : z = n + 1
    · subst hzn
      exact (H.differentiableAt_h₁ (by
        simp; linarith [H.c_gt, n.cast_nonneg (α := ℝ)])).differentiableWithinAt
    · exact (H.differentiableAt_h₁ (hfree z hz hzn).1).differentiableWithinAt
  -- the residues of the second sum
  have hres₂ : ∀ n ∈ Finset.range K,
      residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * mellinTrunc₂ContZero h bs β z)))
        (n + 1) (R₂ (n + 1)) =
        (-1) ^ n / n ! * (ζ : ℂ) ^ (n : ℂ) * mellinTrunc₂ContZero h bs β (n + 1) := fun n hn => by
    have hmem : ((n : ℂ) + 1) ∈ S₂ := by
      rw [hS₂', Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
    obtain ⟨hRpos, hfree⟩ := hR₂ _ hmem
    refine residue_neg_cpow_Gamma_mul hζ n hRpos (fun z hz => ?_)
      fun z hz hzn m => (notMem_sing_iff.mp (hfree z hz hzn)).2 m
    refine (differentiableAt_mellinTrunc₂ContZero H.h_loc H.β_mono H.β_tendsto H.h_exp_zero
      fun s hs => ?_).differentiableWithinAt
    by_cases hzn : z = n + 1
    · exact hβℕ s n (hzn ▸ hs.symm)
    · exact (notMem_sing_iff.mp (hfree z hz hzn)).1 ⟨s, hs.symm⟩
  have hres₃ : ∀ s ∈ Finset.range N,
      residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * mellinTrunc₂ContZero h bs β z)))
        (β s) (R₂ (β s)) = bs s * Gamma (1 - β s) * (ζ : ℂ) ^ (β s - 1) := fun s hs => by
    have hmem : β s ∈ S₂ := by
      rw [hS₂', Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    obtain ⟨hRpos, hfree⟩ := hR₂ _ hmem
    obtain ⟨g, hg, hgeq⟩ := mellinTrunc₂ContZero_principal H.h_loc H.β_mono H.β_tendsto
      H.h_exp_zero (bs := bs) s
    refine residue_neg_cpow_Gamma_mul_pole hζ hg hgeq (hβℕ s) hRpos (fun z hz => ?_)
      fun z hz hzβ m => (notMem_sing_iff.mp (hfree z hz hzβ)).2 m
    have hzb : z ∈ ball (β s) (R₂ (β s)) := by rw [mem_ball, dist_eq_norm]; exact hz.2
    have hzβ : z ≠ β s := fun h => by
      have := hz.1
      rw [h, sub_self, norm_zero] at this
      exact lt_irrefl _ this
    exact (differentiableAt_mellinTrunc₂ContZero H.h_loc H.β_mono H.β_tendsto H.h_exp_zero
      fun t ht => (notMem_sing_iff.mp (hfree z hzb hzβ)).1 ⟨t, ht.symm⟩).differentiableWithinAt
  rw [hS₁', hS₂', Finset.sum_union hdisj, Finset.sum_image fun m _ n _ hmn => hinj hmn,
    Finset.sum_image fun m _ n _ hmn => hβinj hmn, Finset.sum_image fun m _ n _ hmn => hinj hmn,
    Finset.sum_congr rfl hres₁, Finset.sum_congr rfl hres₂, Finset.sum_congr rfl hres₃,
    ← add_assoc, ← Finset.sum_add_distrib, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cpow_natCast, neg_pow]
  ring

end LaplaceSmallSetup

end Azurite.DLMF
