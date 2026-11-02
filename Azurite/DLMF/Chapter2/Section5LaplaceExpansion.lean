/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5LaplaceGrowth

/-!
# DLMF §2.5(iii), 2.5.42–2.5.43: the expansion of `ℒh(ζ)` as `ζ → 0+`

Let `G` be the continuation of `𝓜h₂` (2.5.27): `G = 𝓜h₂` on `ℜz < ℜβ₀`, analytic off a set
`P` of poles, polynomially bounded on strips (`MellinH₂Cont`; both continuations of 2.5.27
qualify, `mellinH₂Cont_ne`, `mellinH₂Cont_zero`).

* 2.5.42 (`dlmf_2_5_42`): with `ρ` chosen in `(1, 2)` so that `G` has no poles in `1 < ℜz ≤ ρ`,
  `I₂(x) = ∑_{ℜβ₀ ≤ ℜz ≤ 1} res[−x^{−z} Γ(1 − z) 𝓜h₂(z)] + (2πi)⁻¹ ∫_{ρ} x^{−z} Γ(1 − z) 𝓜h₂(z) dz`,
  the sum running over the singularities of `Γ(1 − z) G(z)` with `p₂ < ℜz ≤ 1`.
* 2.5.43 (`dlmf_2_5_43`): for `L = l − δ > 1` with no singularity on `ℜz = L`,
  `ℒh(ζ) = ∑_{1 ≤ n+1 < L} res[−ζ^{z−1} Γ(1 − z) 𝓜h₁(z)]
  + ∑_{p₂ < ℜz < L} res[−ζ^{z−1} Γ(1 − z) G(z)]
  + (2πi)⁻¹ ∫_{L} ζ^{z−1} Γ(1 − z) (𝓜h₁(z) + G(z)) dz`.
  DLMF groups the residues as `𝓜h₁(1)` (the residue of the first sum at `z = 1`, cf. 2.5.41)
  plus the residues of `Γ(1 − z) 𝓜h₂(z)` in `ℜβ₀ ≤ ℜz ≤ 1` plus those of `Γ(1 − z) 𝓜h(z)`,
  `𝓜h = 𝓜h₁ + 𝓜h₂`, in `1 < ℜz < l`; the two forms agree by additivity of residues.
* The remainder is `O(ζ^{L−1})` as `ζ → 0+` (`dlmf_2_5_43_remainder`): `|ζ^{z−1}| = ζ^{L−1}` on
  the line and `Γ(1 − z) 𝓜h(z)` is integrable there.
-/

open MeasureTheory Filter Topology Set Complex Metric Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### Continuations of `𝓜h₂` -/

/-- A continuation `G` of `𝓜h₂` to a function analytic off `P`, polynomially bounded on strips. -/
structure MellinH₂Cont (h : ℝ → ℂ) (β₀ : ℝ) (G : ℂ → ℂ) (P : Set ℂ) : Prop where
  eq : ∀ z : ℂ, z.re < β₀ → G z = mellin (trunc₂ h) z
  strip : ∀ a₀ : ℝ, StripData G P a₀

theorem LaplaceSmallSetup.mellinH₂Cont_ne {h : ℝ → ℂ} {bs β : ℕ → ℂ} {κ p c : ℝ}
    (H : LaplaceSmallSetup h bs β κ p c) (hκ : κ ≠ 0) :
    MellinH₂Cont h (β 0).re (mellinTrunc₂Cont h bs β κ p) ∅ where
  eq := fun z hz => (dlmf_2_5_27_ne hκ H.p_pos H.β_mono H.h_loc H.h_exp H.β_tendsto).2 z hz
  strip := stripData_mellinTrunc₂Cont hκ H.p_pos H.β_mono H.β_tendsto H.h_loc H.h_exp

theorem LaplaceSmallSetup.h_exp_zero {h : ℝ → ℂ} {bs β : ℕ → ℂ} {p c : ℝ}
    (H : LaplaceSmallSetup h bs β 0 p c) :
    IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
      fun s t => bs s * (t : ℂ) ^ (-β s) := by
  have := H.h_exp
  simpa only [ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] using this

theorem LaplaceSmallSetup.mellinH₂Cont_zero {h : ℝ → ℂ} {bs β : ℕ → ℂ} {p c : ℝ}
    (H : LaplaceSmallSetup h bs β 0 p c) :
    MellinH₂Cont h (β 0).re (mellinTrunc₂ContZero h bs β) (range β) where
  eq := fun _ hz => mellinTrunc₂ContZero_eq H.h_loc H.β_mono H.β_tendsto H.h_exp_zero hz
  strip := stripData_mellinTrunc₂ContZero H.h_loc H.β_mono H.β_tendsto H.h_exp_zero

/-! ### From `x = 1/ζ` back to `ζ` -/

theorem inv_mul_cpow_neg {ζ : ℝ} (hζ : 0 < ζ) (z : ℂ) :
    (ζ : ℂ)⁻¹ * ((1 / ζ : ℝ) : ℂ) ^ (-z) = (ζ : ℂ) ^ (z - 1) := by
  rw [one_div, ofReal_inv_cpow_neg hζ, cpow_sub _ _ (ofReal_ne_zero.mpr hζ.ne'), cpow_one,
    div_eq_inv_mul]

theorem natCast_add_one_mem_sing (P : Set ℂ) (n : ℕ) : ((n : ℂ) + 1) ∈ sing P :=
  Or.inr ⟨n, rfl⟩

theorem mem_sing_empty {z : ℂ} : z ∈ sing ∅ ↔ ∃ n : ℕ, z = n + 1 := by
  simp [sing]

namespace LaplaceSmallSetup

variable {h : ℝ → ℂ} {bs β : ℕ → ℂ} {κ p c : ℝ} (H : LaplaceSmallSetup h bs β κ p c)
  {G : ℂ → ℂ} {P : Set ℂ} (hG : MellinH₂Cont h (β 0).re G P)
include H hG

/-- The shift of `I₂`'s line of integration from `p₂` to any `q > p₂` free of singularities. -/
theorem I₂_shift {p₂ q : ℝ} (hp₂ : p₂ < min 1 (β 0).re) (hp₂' : ∀ z ∈ sing P, z.re ≠ p₂)
    (hpq : p₂ < q) (hq : ∀ z ∈ sing P, z.re ≠ q) {x : ℝ} (hx : 0 < x) :
    ∃ (S : Finset ℂ) (R : ℂ → ℝ),
      (∀ z, z ∈ S ↔ z ∈ sing P ∧ p₂ < z.re ∧ z.re < q) ∧
      (∀ s ∈ S, 0 < R s ∧ ∀ z ∈ ball s (R s), z ≠ s → z ∉ sing P) ∧
      mellinConvInt expNeg (trunc₂ h) x =
        ∑ s ∈ S, residue (fun z => -((x : ℂ) ^ (-z) * (Gamma (1 - z) * G z))) s (R s) +
          (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (x : ℂ) ^ (-((q : ℂ) + y * I)) *
            (Gamma (1 - (q + y * I)) * G (q + y * I)) := by
  obtain ⟨S, R, hS, hR, hshift⟩ := shift_Gamma_mul (hG.strip (p₂ - 1)) (by linarith : p₂ - 1 < p₂)
    hpq hp₂' hq hx
  refine ⟨S, R, hS, fun s hs => ⟨(hR s hs).1, fun z hz hzs => ((hR s hs).2 z hz hzs).2⟩, ?_⟩
  rw [H.dlmf_2_5_40_two hp₂ hx, ← hshift]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [hG.eq _ (by simp; linarith [(lt_min_iff.mp hp₂).2])]

/-- **DLMF 2.5.42**: with `1 < ρ < 2` chosen so that `G` has no poles in `1 < ℜz ≤ ρ`,
`I₂(x) = ∑_{p₂<ℜz≤1} res[−x^{−z} Γ(1 − z) 𝓜h₂(z)] + (2πi)⁻¹ ∫_{ρ} x^{−z} Γ(1 − z) 𝓜h₂(z) dz`,
the sum over the singularities of `Γ(1 − z) G(z)` (the poles `βₛ` with `ℜβₛ ≤ 1` and `z = 1`). -/
theorem dlmf_2_5_42 {p₂ ρ : ℝ} (hp₂ : p₂ < min 1 (β 0).re) (hp₂' : ∀ z ∈ sing P, z.re ≠ p₂)
    (hρ1 : 1 < ρ) (hρ2 : ρ < 2) (hρP : ∀ z ∈ P, ¬ (1 < z.re ∧ z.re ≤ ρ)) {x : ℝ} (hx : 0 < x) :
    ∃ (S : Finset ℂ) (R : ℂ → ℝ),
      (∀ z, z ∈ S ↔ z ∈ sing P ∧ p₂ < z.re ∧ z.re ≤ 1) ∧
      (∀ s ∈ S, 0 < R s ∧ ∀ z ∈ ball s (R s), z ≠ s → z ∉ sing P) ∧
      mellinConvInt expNeg (trunc₂ h) x =
        ∑ s ∈ S, residue (fun z => -((x : ℂ) ^ (-z) * (Gamma (1 - z) * G z))) s (R s) +
          (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (x : ℂ) ^ (-((ρ : ℂ) + y * I)) *
            (Gamma (1 - (ρ + y * I)) * G (ρ + y * I)) := by
  have h1 := (lt_min_iff.mp hp₂).1
  have hρ : ∀ z ∈ sing P, z.re ≠ ρ := fun z hz hzρ => by
    rcases hz with hzP | ⟨n, rfl⟩
    · exact hρP z hzP ⟨by linarith, hzρ.le⟩
    · simp at hzρ
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp at hzρ; linarith
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
        linarith
  obtain ⟨S, R, hS, hR, heq⟩ := H.I₂_shift hG hp₂ hp₂' (by linarith) hρ hx
  refine ⟨S, R, fun z => ?_, hR, heq⟩
  rw [hS]
  constructor
  · rintro ⟨hz, h2, h3⟩
    refine ⟨hz, h2, ?_⟩
    rcases hz with hzP | ⟨n, rfl⟩
    · by_contra hcon
      exact hρP z hzP ⟨lt_of_not_ge hcon, h3.le⟩
    · simp at h3 ⊢
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
        linarith
  · rintro ⟨hz, h2, h3⟩
    exact ⟨hz, h2, by linarith⟩

omit hG in
/-- The shift of `I₁`'s line of integration to `ℜz = L`, `L > 1` not an integer, across the poles
`1, 2, …` of `Γ(1 − z)` below `L`. -/
theorem I₁_shift {L : ℝ} (hL1 : 1 < L) (hL : ∀ n : ℕ, (n : ℝ) + 1 ≠ L) {x : ℝ} (hx : 0 < x) :
    ∃ (S : Finset ℂ) (R : ℂ → ℝ),
      (∀ z, z ∈ S ↔ ∃ n : ℕ, z = n + 1 ∧ (n : ℝ) + 1 < L) ∧
      (∀ s ∈ S, 0 < R s ∧ ∀ z ∈ ball s (R s), z ≠ s → -c < z.re ∧ ∀ n : ℕ, z ≠ n + 1) ∧
      mellinConvInt expNeg (trunc₁ h) x =
        ∑ s ∈ S, residue (fun z => -((x : ℂ) ^ (-z) * (Gamma (1 - z) * mellin (trunc₁ h) z))) s
            (R s) +
          (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (x : ℂ) ^ (-((L : ℂ) + y * I)) *
            (Gamma (1 - (L + y * I)) * mellin (trunc₁ h) (L + y * I)) := by
  have hc := H.c_gt
  set p₁ : ℝ := (1 - c) / 2 with hp₁def
  have hp₁ : -c < p₁ := by rw [hp₁def]; linarith
  have hp₁' : p₁ < 1 := by rw [hp₁def]; linarith
  have hsing : ∀ z ∈ sing (∅ : Set ℂ), 1 ≤ z.re := fun z hz => by
    obtain ⟨n, rfl⟩ := mem_sing_empty.mp hz
    simp
  obtain ⟨S, R, hS, hR, hshift⟩ := shift_Gamma_mul H.stripData_h₁ hp₁ (by linarith : p₁ < L)
    (fun z hz => by linarith [hsing z hz])
    (fun z hz => by obtain ⟨n, rfl⟩ := mem_sing_empty.mp hz; simpa using hL n) hx
  refine ⟨S, R, fun z => ?_, fun s hs => ⟨(hR s hs).1, fun z hz hzs => ?_⟩, ?_⟩
  · rw [hS, mem_sing_empty]
    constructor
    · rintro ⟨⟨n, rfl⟩, -, h3⟩
      exact ⟨n, rfl, by simpa using h3⟩
    · rintro ⟨n, rfl, hn⟩
      exact ⟨⟨n, rfl⟩, by simp; linarith, by simpa using hn⟩
  · obtain ⟨h1, h2⟩ := (hR s hs).2 z hz hzs
    exact ⟨h1, fun n hn => h2 (hn ▸ natCast_add_one_mem_sing _ n)⟩
  · rw [H.dlmf_2_5_40_one hp₁ hp₁' hx, hshift]

/-- **DLMF 2.5.43**: for `L = l − δ > 1` with no singularity on `ℜz = L` and `p₂ < min(1, ℜβ₀)`
with no singularity on `ℜz = p₂`,
`ℒh(ζ) = ∑_{1≤n+1<L} res[−ζ^{z−1} Γ(1 − z) 𝓜h₁(z)] + ∑_{p₂<ℜz<L} res[−ζ^{z−1} Γ(1 − z) G(z)] +
(2πi)⁻¹ ∫_{L} ζ^{z−1} Γ(1 − z) (𝓜h₁(z) + G(z)) dz`, each singularity with a radius whose
punctured disc is free of singularities. (DLMF's grouping of the residues is recovered by
additivity: the first sum's residue at `z = 1` is `𝓜h₁(1)`, and the residues with `ℜz > 1` of the
two sums combine into those of `Γ(1 − z) 𝓜h(z)`.) -/
theorem dlmf_2_5_43 {p₂ L : ℝ} (hp₂ : p₂ < min 1 (β 0).re) (hp₂' : ∀ z ∈ sing P, z.re ≠ p₂)
    (hL1 : 1 < L) (hL : ∀ z ∈ sing P, z.re ≠ L) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ (S₁ S₂ : Finset ℂ) (R₁ R₂ : ℂ → ℝ),
      (∀ z, z ∈ S₁ ↔ ∃ n : ℕ, z = n + 1 ∧ (n : ℝ) + 1 < L) ∧
      (∀ s ∈ S₁, 0 < R₁ s ∧ ∀ z ∈ ball s (R₁ s), z ≠ s → -c < z.re ∧ ∀ n : ℕ, z ≠ n + 1) ∧
      (∀ z, z ∈ S₂ ↔ z ∈ sing P ∧ p₂ < z.re ∧ z.re < L) ∧
      (∀ s ∈ S₂, 0 < R₂ s ∧ ∀ z ∈ ball s (R₂ s), z ≠ s → z ∉ sing P) ∧
      laplace h ζ =
        ∑ s ∈ S₁, residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * mellin (trunc₁ h) z)))
            s (R₁ s) +
          ∑ s ∈ S₂, residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * G z))) s (R₂ s) +
          (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (ζ : ℂ) ^ ((L : ℂ) + y * I - 1) *
            (Gamma (1 - (L + y * I)) * (mellin (trunc₁ h) (L + y * I) + G (L + y * I))) := by
  have hx : 0 < 1 / ζ := one_div_pos.mpr hζ
  have hLn : ∀ n : ℕ, (n : ℝ) + 1 ≠ L := fun n hn => hL _ (natCast_add_one_mem_sing P n) (by simpa)
  obtain ⟨S₁, R₁, hS₁, hR₁, h₁⟩ := H.I₁_shift hL1 hLn hx
  obtain ⟨S₂, R₂, hS₂, hR₂, h₂⟩ :=
    H.I₂_shift hG hp₂ hp₂' (by linarith [(lt_min_iff.mp hp₂).1]) hL hx
  refine ⟨S₁, S₂, R₁, R₂, hS₁, hR₁, hS₂, hR₂, ?_⟩
  have hζ0 : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  have hlap : laplace h ζ = (ζ : ℂ)⁻¹ * ((ζ : ℂ) * laplace h ζ) := by
    rw [← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]
  rw [hlap, H.dlmf_2_5_38 hζ, h₁, h₂]
  -- the residues
  have hres₁ : ∀ s ∈ S₁, (ζ : ℂ)⁻¹ * residue
      (fun z => -(((1 / ζ : ℝ) : ℂ) ^ (-z) * (Gamma (1 - z) * mellin (trunc₁ h) z))) s (R₁ s) =
      residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * mellin (trunc₁ h) z))) s (R₁ s) :=
    fun s hs => by
      rw [← residue_const_mul]
      exact residue_congr (hR₁ s hs).1 fun z _ => by rw [← inv_mul_cpow_neg hζ]; ring
  have hres₂ : ∀ s ∈ S₂, (ζ : ℂ)⁻¹ * residue
      (fun z => -(((1 / ζ : ℝ) : ℂ) ^ (-z) * (Gamma (1 - z) * G z))) s (R₂ s) =
      residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * G z))) s (R₂ s) :=
    fun s hs => by
      rw [← residue_const_mul]
      exact residue_congr (hR₂ s hs).1 fun z _ => by rw [← inv_mul_cpow_neg hζ]; ring
  -- the line integrals
  have hLc : -c < L := by linarith [H.c_gt]
  have hLs : ∀ z ∈ sing (∅ : Set ℂ), z.re ≠ L := fun z hz => by
    obtain ⟨n, rfl⟩ := mem_sing_empty.mp hz
    simpa using hLn n
  have hi₁ := integrable_Gamma_mul_line H.stripData_h₁ hLc hLs hx
  have hi₂ := integrable_Gamma_mul_line (hG.strip (L - 1)) (by linarith) hL hx
  have hint : (ζ : ℂ)⁻¹ * ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, ((1 / ζ : ℝ) : ℂ) ^ (-((L : ℂ) + y * I)) *
      (Gamma (1 - (L + y * I)) * mellin (trunc₁ h) (L + y * I))) +
      (ζ : ℂ)⁻¹ * ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, ((1 / ζ : ℝ) : ℂ) ^ (-((L : ℂ) + y * I)) *
      (Gamma (1 - (L + y * I)) * G (L + y * I))) =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (ζ : ℂ) ^ ((L : ℂ) + y * I - 1) *
        (Gamma (1 - (L + y * I)) * (mellin (trunc₁ h) (L + y * I) + G (L + y * I))) := by
    have e1 : ∀ f : ℝ → ℂ, (ζ : ℂ)⁻¹ * ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, f y) =
        (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (ζ : ℂ)⁻¹ * f y := fun f => by
      rw [integral_const_mul]
      ring
    rw [e1, e1, ← mul_add, ← integral_add (hi₁.const_mul _) (hi₂.const_mul _)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [← inv_mul_cpow_neg hζ]
    ring
  rw [mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_congr rfl hres₁,
    Finset.sum_congr rfl hres₂, ← hint]
  ring

omit H in
/-- The integrand of the remainder in 2.5.43 is integrable on the line `ℜz = L`. -/
theorem integrable_remainder_line (H : LaplaceSmallSetup h bs β κ p c) {L : ℝ} (hL1 : 1 < L)
    (hL : ∀ z ∈ sing P, z.re ≠ L) :
    Integrable fun y : ℝ => Gamma (1 - (L + y * I)) *
      (mellin (trunc₁ h) (L + y * I) + G (L + y * I)) := by
  have hLc : -c < L := by linarith [H.c_gt]
  have hLn : ∀ n : ℕ, (n : ℝ) + 1 ≠ L := fun n hn => hL _ (natCast_add_one_mem_sing P n) (by simpa)
  have hLs : ∀ z ∈ sing (∅ : Set ℂ), z.re ≠ L := fun z hz => by
    obtain ⟨n, rfl⟩ := mem_sing_empty.mp hz
    simpa using hLn n
  have hi₁ := integrable_Gamma_mul_line H.stripData_h₁ hLc hLs one_pos
  have hi₂ := integrable_Gamma_mul_line (hG.strip (L - 1)) (by linarith) hL one_pos
  have hsum : Integrable fun y : ℝ => ((1 : ℝ) : ℂ) ^ (-((L : ℂ) + y * I)) *
      (Gamma (1 - (L + y * I)) * mellin (trunc₁ h) (L + y * I)) +
      ((1 : ℝ) : ℂ) ^ (-((L : ℂ) + y * I)) * (Gamma (1 - (L + y * I)) * G (L + y * I)) :=
    hi₁.add hi₂
  refine hsum.congr (ae_of_all _ fun y => ?_)
  simp only [ofReal_one, one_cpow, one_mul]
  ring

/-- **DLMF 2.5.43**, the remainder: `(2πi)⁻¹ ∫_{L} ζ^{z−1} Γ(1 − z) 𝓜h(z) dz = O(ζ^{L−1})` as
`ζ → 0+`. -/
theorem dlmf_2_5_43_remainder {L : ℝ} (hL1 : 1 < L) (hL : ∀ z ∈ sing P, z.re ≠ L) :
    IsBigODLMF (𝓝[>] (0 : ℝ))
      (fun ζ : ℝ => (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (ζ : ℂ) ^ ((L : ℂ) + y * I - 1) *
        (Gamma (1 - (L + y * I)) * (mellin (trunc₁ h) (L + y * I) + G (L + y * I))))
      fun ζ : ℝ => (ζ : ℂ) ^ ((L : ℂ) - 1) := by
  have hint := H.integrable_remainder_line hG hL1 hL
  refine ⟨(2 * π)⁻¹ * ∫ y : ℝ, ‖Gamma (1 - (L + y * I)) *
    (mellin (trunc₁ h) (L + y * I) + G (L + y * I))‖, eventually_map.mpr ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  have hζ : (0 : ℝ) < ζ := hζ
  have hζ0 : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  have hpow : ∀ y : ℝ, (ζ : ℂ) ^ ((L : ℂ) + y * I - 1) =
      (ζ : ℂ) ^ ((L : ℂ) - 1) * (ζ : ℂ) ^ ((y : ℂ) * I) := fun y => by
    rw [← cpow_add _ _ hζ0]
    congr 1
    ring
  have hnorm : ∀ y : ℝ, ‖(ζ : ℂ) ^ ((y : ℂ) * I)‖ = 1 := fun y => by
    rw [norm_cpow_eq_rpow_re_of_pos hζ]
    simp
  have hL0 : (ζ : ℂ) ^ ((L : ℂ) - 1) ≠ 0 := cpow_ne_zero_of_ne_zero hζ0 _
  have hπ : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, norm_real,
      Real.norm_of_nonneg (by positivity)]
  have e : (∫ y : ℝ, (ζ : ℂ) ^ ((L : ℂ) + y * I - 1) *
      (Gamma (1 - (L + y * I)) * (mellin (trunc₁ h) (L + y * I) + G (L + y * I)))) =
      (ζ : ℂ) ^ ((L : ℂ) - 1) * ∫ y : ℝ, (ζ : ℂ) ^ ((y : ℂ) * I) *
        (Gamma (1 - (L + y * I)) * (mellin (trunc₁ h) (L + y * I) + G (L + y * I))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hpow y]
    ring
  rw [norm_div, norm_mul, norm_inv, hπ, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [e, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hL0)]
  refine norm_integral_le_of_norm_le hint.norm (ae_of_all _ fun y => ?_)
  rw [norm_mul, hnorm, one_mul]

end LaplaceSmallSetup

end Azurite.DLMF
