/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section7Formal

/-!
# DLMF §2.7(ii): Irregular Singularities of Rank 1 — Fabry's transformation 2.7.19

The exceptional case `f₀² = 4g₀` (equal characteristic roots) is handled by Fabry's
transformation 2.7.19, `w = e^{−f₀z/2} W`, `t = z^{1/2}`.

* `isODESolution_fabry`: if `w` solves 2.7.1 then `W(t) = e^{f₀t²/2} w(t²)` solves
  `W″ + F̃(t) W′ + G̃(t) W = 0` with `F̃(t) = −1/t + 2t (f(t²) − f₀)` (`fabryF`) and
  `G̃(t) = 4t² (g(t²) − f₀ f(t²)/2 + f₀²/4)` (`fabryG`); `fabry_inverse` recovers
  `w(z) = e^{−f₀z/2} W(z^{1/2})`.
* `RankOneData.fabry`: when `f₀² = 4g₀` the transformed coefficients again satisfy 2.7.7, for
  `|t| > √a`, with `F̃(t) = ∑ F̃ₛ t^{−s}`, `G̃(t) = ∑ G̃ₛ t^{−s}` (`fabryFc`, `fabryGc`):
  `F̃₀ = 0`, `F̃₁ = 2f₁ − 1`, `G̃₀ = 4(g₁ − f₀f₁/2)`, `G̃₁ = 0`.
* `RankOneData.fabry_dichotomy` (DLMF): the transformed equation either satisfies the
  regular-singularity condition at `t = ∞` (`G̃₀ = 0`), or `t = ∞` is an irregular singularity of
  rank 1 whose characteristic equation `λ² + G̃₀ = 0` has unequal roots. In the first case `t = ∞`
  may even be an ordinary point (`fabry_example_ordinary`), not a regular singularity as DLMF
  says.
-/

open Filter Topology Set Complex Metric Finset

namespace Azurite.DLMF

/-! ### The transformation of the equation -/

/-- `F̃(t) = −1/t + 2t (f(t²) − c)`. -/
noncomputable def fabryF (f : ℂ → ℂ) (c t : ℂ) : ℂ := -1 / t + 2 * t * (f (t ^ 2) - c)

/-- `G̃(t) = 4t² (g(t²) − c f(t²)/2 + c²/4)`. -/
noncomputable def fabryG (f g : ℂ → ℂ) (c t : ℂ) : ℂ :=
  4 * t ^ 2 * (g (t ^ 2) - c * f (t ^ 2) / 2 + c ^ 2 / 4)

/-- **DLMF 2.7.19**: if `w` solves 2.7.1 on `D`, then `W(t) = e^{ct²/2} w(t²)` (so that
`w = e^{−cz/2} W` with `t = z^{1/2}`) solves `W″ + F̃ W′ + G̃ W = 0` on `{t ≠ 0 | t² ∈ D}`. -/
theorem isODESolution_fabry {D : Set ℂ} {f g w : ℂ → ℂ} (hDo : IsOpen D)
    (hw : IsODESolution D f g w) (c : ℂ) :
    IsODESolution {t : ℂ | t ≠ 0 ∧ t ^ 2 ∈ D} (fabryF f c) (fabryG f g c)
      fun t => cexp (c * t ^ 2 / 2) * w (t ^ 2) := by
  have hopen : IsOpen {t : ℂ | t ≠ 0 ∧ t ^ 2 ∈ D} :=
    isOpen_ne.inter (hDo.preimage (continuous_pow 2))
  refine isODESolution_of_hasDerivAt hopen
    (w' := fun t => cexp (c * t ^ 2 / 2) * (c * t * w (t ^ 2) + 2 * t * deriv w (t ^ 2)))
    fun t ⟨ht0, htD⟩ => ?_
  obtain ⟨h1, h2⟩ := hw.hasDerivAt hDo htD
  have hsq : HasDerivAt (fun t : ℂ => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hE : HasDerivAt (fun t : ℂ => cexp (c * t ^ 2 / 2)) (cexp (c * t ^ 2 / 2) * (c * t)) t := by
    have := ((hsq.const_mul c).div_const 2).cexp
    convert this using 1
    ring
  have hw₁ : HasDerivAt (fun t : ℂ => w (t ^ 2)) (deriv w (t ^ 2) * (2 * t)) t := h1.comp t hsq
  have hw₂ := h2.comp t hsq
  constructor
  · exact (hE.mul hw₁).congr_deriv (by ring)
  · have hin := ((((hasDerivAt_id t).const_mul c).mul hw₁).add
      (((hasDerivAt_id t).const_mul 2).mul hw₂))
    refine (hE.mul hin).congr_deriv ?_
    simp only [fabryF, fabryG, id, Pi.add_apply, Pi.mul_apply, Function.comp_apply]
    field_simp
    ring

/-- The inverse substitution: `w(z) = e^{−cz/2} W(z^{1/2})`. -/
theorem fabry_inverse (w : ℂ → ℂ) (c z : ℂ) :
    w z = cexp (-(c * z) / 2) *
      (fun t => cexp (c * t ^ 2 / 2) * w (t ^ 2)) (z ^ (((2 : ℕ) : ℂ)⁻¹)) := by
  have h : (z ^ (((2 : ℕ) : ℂ)⁻¹)) ^ 2 = z := cpow_nat_inv_pow z two_ne_zero
  simp only [h]
  rw [← mul_assoc, ← Complex.exp_add]
  ring_nf
  rw [Complex.exp_zero, one_mul]

/-! ### Spreading a power series onto even or odd powers -/

/-- `∑ cₖ ζ^{2k}` as a power series in `ζ`. -/
def evenSpread (c : ℕ → ℂ) (n : ℕ) : ℂ := if n % 2 = 0 then c (n / 2) else 0

/-- `∑ cₖ ζ^{2k+1}` as a power series in `ζ`. -/
def oddSpread (c : ℕ → ℂ) (n : ℕ) : ℂ := if n % 2 = 1 then c (n / 2) else 0

theorem evenSpread_two_mul (c : ℕ → ℂ) (k : ℕ) : evenSpread c (2 * k) = c k := by
  simp [evenSpread, show 2 * k / 2 = k by omega]

theorem evenSpread_two_mul_add_one (c : ℕ → ℂ) (k : ℕ) : evenSpread c (2 * k + 1) = 0 := by
  simp [evenSpread, show (2 * k + 1) % 2 = 1 by omega]

theorem oddSpread_two_mul (c : ℕ → ℂ) (k : ℕ) : oddSpread c (2 * k) = 0 := by
  simp [oddSpread]

theorem oddSpread_two_mul_add_one (c : ℕ → ℂ) (k : ℕ) : oddSpread c (2 * k + 1) = c k := by
  simp [oddSpread, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]

theorem HasRadiusGE.hasSum {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c R) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) R) : HasSum (fun n => c n * ζ ^ n) (powerSeriesSum c 0 ζ) := by
  have : HasSum (fun n => c n * (ζ - 0) ^ n) (powerSeriesSum c 0 ζ) := (h.summable hζ).hasSum
  simp only [sub_zero] at this
  exact this

theorem sq_mem_ball {R : ℝ} {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) R) : ζ ^ 2 ∈ ball (0 : ℂ) (R ^ 2) := by
  rw [mem_ball, dist_zero_right] at hζ ⊢
  rw [norm_pow]
  exact pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero

theorem HasRadiusGE.hasSum_evenSpread {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c (R ^ 2)) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) R) :
    HasSum (fun n => evenSpread c n * ζ ^ n) (powerSeriesSum c 0 (ζ ^ 2)) := by
  have he : HasSum (fun k => evenSpread c (2 * k) * ζ ^ (2 * k)) (powerSeriesSum c 0 (ζ ^ 2)) := by
    convert h.hasSum (sq_mem_ball hζ) using 1
    funext k
    rw [evenSpread_two_mul, pow_mul]
  have ho : HasSum (fun k => evenSpread c (2 * k + 1) * ζ ^ (2 * k + 1)) 0 := by
    simpa only [evenSpread_two_mul_add_one, zero_mul] using hasSum_zero
  have := HasSum.even_add_odd (f := fun n => evenSpread c n * ζ ^ n) he ho
  rwa [add_zero] at this

theorem HasRadiusGE.hasSum_oddSpread {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c (R ^ 2)) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) R) :
    HasSum (fun n => oddSpread c n * ζ ^ n) (ζ * powerSeriesSum c 0 (ζ ^ 2)) := by
  have he : HasSum (fun k => oddSpread c (2 * k) * ζ ^ (2 * k)) 0 := by
    simpa only [oddSpread_two_mul, zero_mul] using hasSum_zero
  have ho : HasSum (fun k => oddSpread c (2 * k + 1) * ζ ^ (2 * k + 1))
      (ζ * powerSeriesSum c 0 (ζ ^ 2)) := by
    convert (h.hasSum (sq_mem_ball hζ)).mul_left ζ using 1
    funext k
    rw [oddSpread_two_mul_add_one, pow_succ, pow_mul]
    ring
  have := HasSum.even_add_odd (f := fun n => oddSpread c n * ζ ^ n) he ho
  rwa [zero_add] at this

theorem HasRadiusGE.evenSpread {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c (R ^ 2)) :
    HasRadiusGE (evenSpread c) R := by
  intro ρ hρ hρR
  obtain ⟨K, hK⟩ := h (ρ ^ 2) (by positivity) (pow_lt_pow_left₀ hρR hρ.le two_ne_zero)
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 0)
  refine ⟨K, fun n => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [evenSpread_two_mul, pow_mul]
    exact hK k
  · rw [evenSpread_two_mul_add_one, norm_zero, zero_mul]
    exact hK0

theorem HasRadiusGE.oddSpread {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c (R ^ 2)) :
    HasRadiusGE (oddSpread c) R := by
  intro ρ hρ hρR
  obtain ⟨K, hK⟩ := h (ρ ^ 2) (by positivity) (pow_lt_pow_left₀ hρR hρ.le two_ne_zero)
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 0)
  refine ⟨ρ * K, fun n => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [oddSpread_two_mul, norm_zero, zero_mul]
    positivity
  · rw [oddSpread_two_mul_add_one, pow_succ, pow_mul]
    calc ‖c k‖ * ((ρ ^ 2) ^ k * ρ) = ρ * (‖c k‖ * (ρ ^ 2) ^ k) := by ring
      _ ≤ ρ * K := mul_le_mul_of_nonneg_left (hK k) hρ.le

theorem HasRadiusGE.const_mul {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c R) (κ : ℂ) :
    HasRadiusGE (fun n => κ * c n) R := by
  intro ρ hρ hρR
  obtain ⟨K, hK⟩ := h ρ hρ hρR
  refine ⟨‖κ‖ * K, fun n => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK n) (norm_nonneg _)

/-! ### The transformed coefficients -/

/-- `F̃ₛ`: `F̃_{2k+1} = 2f_{k+1}` (`k ≥ 1`), `F̃₁ = 2f₁ − 1`, `F̃_{2k} = 0`. -/
def fabryFc (fc : ℕ → ℂ) : ℕ → ℂ :=
  (fun n => 2 * oddSpread (seqTail fc) n) + fun n => if n = 1 then -1 else 0

/-- `G̃ₛ`: `G̃_{2k} = 4 (g_{k+1} − f₀ f_{k+1}/2)`, `G̃_{2k+1} = 0`. -/
noncomputable def fabryGc (fc gc : ℕ → ℂ) : ℕ → ℂ :=
  fun n => 4 * evenSpread (fun k => gc (k + 1) - fc 0 / 2 * fc (k + 1)) n

theorem fabryFc_zero (fc : ℕ → ℂ) : fabryFc fc 0 = 0 := by
  simp [fabryFc, oddSpread]

theorem fabryFc_one (fc : ℕ → ℂ) : fabryFc fc 1 = 2 * fc 1 - 1 := by
  simp [fabryFc, oddSpread, seqTail]
  ring

theorem fabryGc_zero (fc gc : ℕ → ℂ) : fabryGc fc gc 0 = 4 * (gc 1 - fc 0 * fc 1 / 2) := by
  simp [fabryGc, evenSpread]
  ring

theorem fabryGc_one (fc gc : ℕ → ℂ) : fabryGc fc gc 1 = 0 := by
  simp [fabryGc, evenSpread]

namespace RankOneData

variable {f g : ℂ → ℂ} {a : ℝ} {fc gc : ℕ → ℂ} (D : RankOneData f g a fc gc)
include D

/-- **DLMF §2.7(ii)**: when `f₀² = 4g₀`, the coefficients of Fabry's transformed equation again
satisfy 2.7.7, for `|t| > √a`. -/
theorem fabry (h : fc 0 ^ 2 = 4 * gc 0) :
    RankOneData (fabryF f (fc 0)) (fabryG f g (fc 0)) (Real.sqrt a) (fabryFc fc)
      (fabryGc fc gc) := by
  have ha := D.a_pos
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hR2 : ((Real.sqrt a)⁻¹) ^ 2 = a⁻¹ := by rw [inv_pow, Real.sq_sqrt ha.le]
  have hRpos : 0 < (Real.sqrt a)⁻¹ := inv_pos.mpr hs
  have hf₁ : HasRadiusGE (seqTail fc) (((Real.sqrt a)⁻¹) ^ 2) := hR2 ▸ D.f_radius.tail
  have hg₁ : HasRadiusGE (seqTail gc) (((Real.sqrt a)⁻¹) ^ 2) := hR2 ▸ D.g_radius.tail
  have hδ : HasRadiusGE (fun n : ℕ => if n = 1 then (-1 : ℂ) else 0) (Real.sqrt a)⁻¹ :=
    hasRadiusGE_of_support (M := 1) (fun n hn => by simp only [ite_eq_right_iff]; omega) _
  set hc : ℕ → ℂ := fun k => gc (k + 1) - fc 0 / 2 * fc (k + 1) with hc_def
  have hh : HasRadiusGE hc (((Real.sqrt a)⁻¹) ^ 2) := by
    have := hg₁.add (hf₁.const_mul (-(fc 0 / 2)))
    refine fun ρ h1 h2 => (this ρ h1 h2).imp fun K hK s => ?_
    have := hK s
    simp only [Pi.add_apply, seqTail] at this
    rw [hc_def]
    convert this using 3
    ring
  -- points with `|t| > √a`
  have key : ∀ t : ℂ, Real.sqrt a < ‖t‖ →
      t ≠ 0 ∧ t⁻¹ ∈ ball (0 : ℂ) (Real.sqrt a)⁻¹ ∧ a < ‖t ^ 2‖ ∧ (t ^ 2)⁻¹ = t⁻¹ ^ 2 := by
    intro t ht
    have ht0 : 0 < ‖t‖ := hs.trans ht
    refine ⟨norm_pos_iff.mp ht0, ?_, ?_, (inv_pow t 2).symm⟩
    · rw [mem_ball, dist_zero_right, norm_inv]
      exact (inv_lt_inv₀ ht0 hs).mpr ht
    · rw [norm_pow]
      exact (Real.sqrt_lt' ht0).mp ht
  refine ⟨hs, (hf₁.oddSpread |>.const_mul 2).add hδ,
    hh.evenSpread |>.const_mul 4, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨ht0, hζ, ht2, hinv⟩ := key t ht
    have h₁ := ((hf₁.hasSum_oddSpread hζ).mul_left 2).add
      (hδ.hasSum hζ)
    have hδs : powerSeriesSum (fun n : ℕ => if n = 1 then (-1 : ℂ) else 0) 0 t⁻¹ = -t⁻¹ := by
      rw [powerSeriesSum, tsum_eq_single 1 fun n hn => by simp [hn]]
      simp
    rw [hδs] at h₁
    rw [powerSeriesSum, sub_zero]
    refine Eq.trans ?_ (h₁.tsum_eq.symm.trans (tsum_congr fun n => ?_))
    · rw [fabryF, D.f_eq _ ht2, hinv, D.f_radius.powerSeriesSum_eq_zero_add
        (by simpa [hR2] using sq_mem_ball hζ)]
      field_simp
      ring
    · simp only [fabryFc, Pi.add_apply]
      ring
  · obtain ⟨ht0, hζ, ht2, hinv⟩ := key t ht
    have h₁ := (hh.hasSum_evenSpread hζ).mul_left 4
    have hζ2 : t⁻¹ ^ 2 ∈ ball (0 : ℂ) a⁻¹ := by simpa [hR2] using sq_mem_ball hζ
    have hsplit : powerSeriesSum hc 0 (t⁻¹ ^ 2) = powerSeriesSum (seqTail gc) 0 (t⁻¹ ^ 2) -
        fc 0 / 2 * powerSeriesSum (seqTail fc) 0 (t⁻¹ ^ 2) := by
      have := ((D.g_radius.tail.hasSum hζ2).sub ((D.f_radius.tail.hasSum hζ2).mul_left (fc 0 / 2)))
      refine Eq.trans ?_ this.tsum_eq
      rw [powerSeriesSum, sub_zero]
      exact tsum_congr fun k => by simp only [hc_def, seqTail]; ring
    rw [powerSeriesSum, sub_zero]
    refine Eq.trans ?_ (h₁.tsum_eq.symm.trans (tsum_congr fun n => ?_))
    · rw [fabryG, D.f_eq _ ht2, D.g_eq _ ht2, hinv, D.f_radius.powerSeriesSum_eq_zero_add hζ2,
        D.g_radius.powerSeriesSum_eq_zero_add hζ2, hsplit]
      field_simp
      linear_combination (-(2 * t ^ 2)) * h
    · simp only [fabryGc]
      ring

/-- **DLMF §2.7(ii)**: after Fabry's transformation (case `f₀² = 4g₀`), either `t = ∞` satisfies
the regular-singularity condition, or it is an irregular singularity of rank 1 whose
characteristic equation has unequal roots. -/
theorem fabry_dichotomy (h : fc 0 ^ 2 = 4 * gc 0) :
    HasRegularCoefficients (infinityF (fabryF f (fc 0))) (infinityG (fabryG f g (fc 0))) 0 ∨
      (HasRank (infinityF (fabryF f (fc 0))) (infinityG (fabryG f g (fc 0))) 0 1 ∧
        ∃ l₁ l₂ : ℂ, l₁ ≠ l₂ ∧
          ∀ lam, rankOneChar (fabryFc fc) (fabryGc fc gc) lam = (lam - l₁) * (lam - l₂)) := by
  have D' := D.fabry h
  by_cases hG : fabryGc fc gc 0 = 0
  · exact Or.inl (D'.hasRegularCoefficients_iff.mpr ⟨fabryFc_zero fc, hG, fabryGc_one fc gc⟩)
  · refine Or.inr ⟨D'.hasRank_one_iff.mpr (Or.inr (Or.inl hG)), ?_⟩
    obtain ⟨l₁, l₂, hl⟩ := exists_charRoots (fabryFc fc) (fabryGc fc gc)
    refine ⟨l₁, l₂, fun heq => hG ?_, hl⟩
    have := (charRoots_eq_iff hl).mp heq
    rw [fabryFc_zero] at this
    linear_combination -this / 4

end RankOneData

/-- DLMF's dichotomy says the transformed equation "has a regular singularity at `t = ∞`" in the
first case; it can in fact be an ordinary point. For `f(z) = 2 + 3/(2z)`, `g(z) = 1 + 3/(2z)`
(rank 1 at infinity, `f₀ = 2`, `g₀ = 1`, `f₀² = 4g₀`) Fabry's transformation gives
`W″ + (2/t) W′ = 0`, for which `t = ∞` is an ordinary point. -/
theorem fabry_example_ordinary :
    IsOrdinaryPoint (infinityF (fabryF (fun z => 2 + 3 / (2 * z)) 2))
      (infinityG (fabryG (fun z => 2 + 3 / (2 * z)) (fun z => 1 + 3 / (2 * z)) 2)) 0 := by
  have hF : infinityF (fabryF (fun z => 2 + 3 / (2 * z)) 2) = fun _ => 0 := by
    funext ζ
    by_cases hζ : ζ = 0
    · subst hζ
      simp [infinityF]
    · simp only [infinityF, fabryF]
      field_simp
      ring
  have hG : infinityG (fabryG (fun z => 2 + 3 / (2 * z)) (fun z => 1 + 3 / (2 * z)) 2) =
      fun _ => 0 := by
    funext ζ
    by_cases hζ : ζ = 0
    · subst hζ
      simp [infinityG]
    · simp only [infinityG, fabryG]
      field_simp
      ring
  rw [IsOrdinaryPoint, hF, hG]
  exact ⟨analyticAt_const, analyticAt_const⟩

end Azurite.DLMF
