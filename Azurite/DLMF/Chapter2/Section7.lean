/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section13

/-!
# DLMF §2.7(i): Regular Singularities: Fuchs–Frobenius Theory — classification, 2.7.1–2.7.3, 2.7.5

The differential equation 2.7.1, `w″ + f(z) w′ + g(z) w = 0`, is `IsODESolution` of §1.13.

* Classification of a point `z₀`: `IsOrdinaryPoint` (`f`, `g` analytic at `z₀`),
  `IsRegularSingularity` (not ordinary, `(z − z₀) f` and `(z − z₀)² g` extend analytically to
  `z₀`), `IsIrregularSingularity` (all other points); `classify_point`.
* At an ordinary point all solutions are analytic (`IsOrdinaryPoint.analyticAt_solution`, from
  §1.13).
* 2.7.2 (`FrobeniusData`, `FrobeniusData.dlmf_2_7_2`): near a regular singularity
  `f(z) = ∑ fₛ (z−z₀)^{s−1}`, `g(z) = ∑ gₛ (z−z₀)^{s−2}`, the series `∑ fₛ (z−z₀)^s`,
  `∑ gₛ (z−z₀)^s` converging absolutely on a ball of radius `R`; such data exist
  (`IsRegularSingularity.exists_frobeniusData`). DLMF's side condition "at least one of
  `f₀, g₀, g₁` nonzero" (i.e. `z₀` is not an ordinary point) is not part of the data.
* 2.7.3 (`indicial`, `exists_indices`): the indicial polynomial `Q(α) = α(α−1) + f₀ α + g₀` and
  its two roots `α₁, α₂` (`Q(α) = (α − α₁)(α − α₂)`).
* 2.7.5 (`frobCoeff`, `frobCoeff_succ`): the Frobenius coefficients `a_{s}` with `a₀ = 1` and
  `Q(α + s) aₛ = −∑_{r<s} ((α + r) f_{s−r} + g_{s−r}) aᵣ`.
* The point at infinity (`infinityF`, `infinityG`, `isODESolution_comp_inv`): `W(ζ) = w(1/ζ)`
  solves `W″ + (2/ζ − f(1/ζ)/ζ²) W′ + g(1/ζ)/ζ⁴ W = 0`, which is how `∞` is classified.

The expansions 2.7.4 and their convergence are in `Section7Frobenius`.
-/

open Filter Topology Set Complex Metric

namespace Azurite.DLMF

/-! ### Classification of points -/

/-- An *ordinary point* of 2.7.1: `f` and `g` are analytic at `z₀`. -/
def IsOrdinaryPoint (f g : ℂ → ℂ) (z₀ : ℂ) : Prop := AnalyticAt ℂ f z₀ ∧ AnalyticAt ℂ g z₀

/-- `(z − z₀) f(z)` and `(z − z₀)² g(z)` extend analytically to `z₀`. -/
def HasRegularCoefficients (f g : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  (∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) * f z = F z) ∧
  ∃ G : ℂ → ℂ, AnalyticAt ℂ G z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) ^ 2 * g z = G z

/-- A *regular singularity* (singularity of the first kind): not an ordinary point, but
`(z − z₀) f(z)` and `(z − z₀)² g(z)` are analytic at `z₀`. -/
def IsRegularSingularity (f g : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ¬ IsOrdinaryPoint f g z₀ ∧ HasRegularCoefficients f g z₀

/-- An *irregular singularity*: all other points. -/
def IsIrregularSingularity (f g : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ¬ IsOrdinaryPoint f g z₀ ∧ ¬ HasRegularCoefficients f g z₀

/-- Every point is ordinary, a regular singularity, or an irregular singularity. -/
theorem classify_point (f g : ℂ → ℂ) (z₀ : ℂ) :
    IsOrdinaryPoint f g z₀ ∨ IsRegularSingularity f g z₀ ∨ IsIrregularSingularity f g z₀ := by
  by_cases h₁ : IsOrdinaryPoint f g z₀
  · exact Or.inl h₁
  by_cases h₂ : HasRegularCoefficients f g z₀
  · exact Or.inr (Or.inl ⟨h₁, h₂⟩)
  · exact Or.inr (Or.inr ⟨h₁, h₂⟩)

/-- At an ordinary point the regularity conditions hold trivially. -/
theorem IsOrdinaryPoint.hasRegularCoefficients {f g : ℂ → ℂ} {z₀ : ℂ} (h : IsOrdinaryPoint f g z₀) :
    HasRegularCoefficients f g z₀ :=
  ⟨⟨fun z => (z - z₀) * f z, (analyticAt_id.sub analyticAt_const).mul h.1,
    Eventually.of_forall fun _ => rfl⟩,
    ⟨fun z => (z - z₀) ^ 2 * g z, ((analyticAt_id.sub analyticAt_const).pow 2).mul h.2,
    Eventually.of_forall fun _ => rfl⟩⟩

/-- **DLMF §2.7(i)**: all solutions of 2.7.1 are analytic at an ordinary point (§1.13). -/
theorem IsOrdinaryPoint.analyticAt_solution {D : Set ℂ} {f g w : ℂ → ℂ} {z₀ : ℂ} (hDo : IsOpen D)
    (hz₀ : z₀ ∈ D) (hw : IsODESolution D f g w) : AnalyticAt ℂ w z₀ :=
  hw.analyticOnNhd hDo z₀ hz₀

/-! ### 2.7.2: the expansions at a regular singularity -/

/-- **DLMF 2.7.2**, quantitatively: on the punctured ball `0 < |z − z₀| < R`,
`f(z) = (∑ fₛ (z−z₀)^s)/(z − z₀)` and `g(z) = (∑ gₛ (z−z₀)^s)/(z − z₀)²`, the two power series
converging absolutely on the ball. -/
structure FrobeniusData (f g : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (fc gc : ℕ → ℂ) : Prop where
  R_pos : 0 < R
  f_summable : ∀ z ∈ ball z₀ R, Summable fun s => ‖fc s * (z - z₀) ^ s‖
  g_summable : ∀ z ∈ ball z₀ R, Summable fun s => ‖gc s * (z - z₀) ^ s‖
  f_eq : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z = (∑' s, fc s * (z - z₀) ^ s) / (z - z₀)
  g_eq : ∀ z ∈ ball z₀ R, z ≠ z₀ → g z = (∑' s, gc s * (z - z₀) ^ s) / (z - z₀) ^ 2

namespace FrobeniusData

variable {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} {fc gc : ℕ → ℂ} (F : FrobeniusData f g z₀ R fc gc)
include F

/-- **DLMF 2.7.2**: `f(z) = ∑ fₛ (z−z₀)^{s−1}` and `g(z) = ∑ gₛ (z−z₀)^{s−2}` on the punctured
ball. -/
theorem dlmf_2_7_2 {z : ℂ} (hz : z ∈ ball z₀ R) (hz₀ : z ≠ z₀) :
    f z = ∑' s : ℕ, fc s * (z - z₀) ^ ((s : ℤ) - 1) ∧
      g z = ∑' s : ℕ, gc s * (z - z₀) ^ ((s : ℤ) - 2) := by
  have hne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz₀
  constructor
  · rw [F.f_eq z hz hz₀, ← tsum_div_const]
    refine tsum_congr fun s => ?_
    rw [zpow_sub₀ hne, zpow_one, zpow_natCast, mul_div_assoc]
  · rw [F.g_eq z hz hz₀, ← tsum_div_const]
    refine tsum_congr fun s => ?_
    rw [zpow_sub₀ hne, zpow_ofNat, zpow_natCast, mul_div_assoc]

/-- The data shrink to any smaller radius. -/
theorem mono {R' : ℝ} (hR' : 0 < R') (hle : R' ≤ R) : FrobeniusData f g z₀ R' fc gc where
  R_pos := hR'
  f_summable z hz := F.f_summable z (ball_subset_ball hle hz)
  g_summable z hz := F.g_summable z (ball_subset_ball hle hz)
  f_eq z hz := F.f_eq z (ball_subset_ball hle hz)
  g_eq z hz := F.g_eq z (ball_subset_ball hle hz)

end FrobeniusData

/-- A function analytic at `z₀` is a power series `∑ cₛ (z − z₀)^s`, absolutely convergent on some
ball. -/
theorem exists_summable_tsum_of_analyticAt {F : ℂ → ℂ} {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀) :
    ∃ R > 0, ∃ c : ℕ → ℂ, (∀ z ∈ ball z₀ R, Summable fun s => ‖c s * (z - z₀) ^ s‖) ∧
      ∀ z ∈ ball z₀ R, F z = ∑' s, c s * (z - z₀) ^ s := by
  obtain ⟨p, r, hp⟩ := hF
  obtain ⟨R, -, hR0, hRr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp.r_pos
  refine ⟨R, ENNReal.ofReal_pos.mp hR0, fun s => p.coeff s, fun z hz => ?_, fun z hz => ?_⟩
  · have hz' : z - z₀ ∈ Metric.eball (0 : ℂ) r := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right, ← dist_eq_norm]
      exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr hz) hRr
    refine (p.summable_norm_apply (Metric.eball_subset_eball hp.r_le hz')).congr fun s => ?_
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  · have hz' : z ∈ Metric.eball z₀ r := by
      rw [Metric.mem_eball, edist_dist]
      exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr hz) hRr
    rw [← (hp.hasSum_sub hz').tsum_eq]
    refine tsum_congr fun s => ?_
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]

/-- At a regular singularity (or an ordinary point) the data 2.7.2 exist. -/
theorem HasRegularCoefficients.exists_frobeniusData {f g : ℂ → ℂ} {z₀ : ℂ}
    (h : HasRegularCoefficients f g z₀) :
    ∃ R > 0, ∃ fc gc : ℕ → ℂ, FrobeniusData f g z₀ R fc gc := by
  obtain ⟨⟨F, hF, hfF⟩, ⟨G, hG, hgG⟩⟩ := h
  obtain ⟨R₁, hR₁, fc, hfs, hfe⟩ := exists_summable_tsum_of_analyticAt hF
  obtain ⟨R₂, hR₂, gc, hgs, hge⟩ := exists_summable_tsum_of_analyticAt hG
  obtain ⟨ε₁, hε₁, hf'⟩ := Metric.mem_nhdsWithin_iff.mp hfF
  obtain ⟨ε₂, hε₂, hg'⟩ := Metric.mem_nhdsWithin_iff.mp hgG
  set R := min (min R₁ R₂) (min ε₁ ε₂) with hR
  have hR0 : 0 < R := lt_min (lt_min hR₁ hR₂) (lt_min hε₁ hε₂)
  have h1 : R ≤ R₁ := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : R ≤ R₂ := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : R ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have h4 : R ≤ ε₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R, hR0, fc, gc, ⟨hR0, fun z hz => hfs z (ball_subset_ball h1 hz),
    fun z hz => hgs z (ball_subset_ball h2 hz), fun z hz hz₀ => ?_, fun z hz hz₀ => ?_⟩⟩
  · have hne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz₀
    have : (z - z₀) * f z = F z := hf' ⟨ball_subset_ball h3 hz, hz₀⟩
    rw [← hfe z (ball_subset_ball h1 hz), ← this, mul_div_cancel_left₀ _ hne]
  · have hne : (z - z₀) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hz₀)
    have : (z - z₀) ^ 2 * g z = G z := hg' ⟨ball_subset_ball h4 hz, hz₀⟩
    rw [← hge z (ball_subset_ball h2 hz), ← this, mul_div_cancel_left₀ _ hne]

theorem IsRegularSingularity.exists_frobeniusData {f g : ℂ → ℂ} {z₀ : ℂ}
    (h : IsRegularSingularity f g z₀) : ∃ R > 0, ∃ fc gc : ℕ → ℂ, FrobeniusData f g z₀ R fc gc :=
  h.2.exists_frobeniusData

/-! ### 2.7.3: the indicial equation -/

/-- **DLMF 2.7.3**: the indicial polynomial `Q(α) = α(α − 1) + f₀ α + g₀`. -/
noncomputable def indicial (fc gc : ℕ → ℂ) (α : ℂ) : ℂ := α * (α - 1) + fc 0 * α + gc 0

/-- The indices (exponents) `α₁, α₂`: the roots of the indicial equation, `Q(α) = (α−α₁)(α−α₂)`. -/
theorem exists_indices (fc gc : ℕ → ℂ) :
    ∃ α₁ α₂ : ℂ, ∀ α, indicial fc gc α = (α - α₁) * (α - α₂) := by
  set d : ℂ := (1 - fc 0) ^ 2 - 4 * gc 0 with hd
  set s : ℂ := d ^ (((2 : ℕ) : ℂ)⁻¹) with hs
  have hs2 : s ^ 2 = d := cpow_nat_inv_pow d two_ne_zero
  refine ⟨(1 - fc 0 + s) / 2, (1 - fc 0 - s) / 2, fun α => ?_⟩
  simp only [indicial]
  linear_combination (1 / 4 : ℂ) * hs2

/-- `Q(α) = 0` iff `α` is one of the indices. -/
theorem indicial_eq_zero_iff {fc gc : ℕ → ℂ} {α₁ α₂ : ℂ}
    (h : ∀ α, indicial fc gc α = (α - α₁) * (α - α₂)) (α : ℂ) :
    indicial fc gc α = 0 ↔ α = α₁ ∨ α = α₂ := by
  rw [h, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- `Q(α₁ + s) ≠ 0` for every `s ≥ 1` iff `α₁ − α₂ ∉ {−1, −2, …}` (so the exponent `α₁` of 2.7.4
is the one with `α₁ − α₂ ∉ {−1, −2, …}`; when `α₁ − α₂` is not an integer both qualify). -/
theorem indicial_add_ne_zero_iff {fc gc : ℕ → ℂ} {α₁ α₂ : ℂ}
    (h : ∀ α, indicial fc gc α = (α - α₁) * (α - α₂)) :
    (∀ s : ℕ, 1 ≤ s → indicial fc gc (α₁ + s) ≠ 0) ↔ ∀ s : ℕ, 1 ≤ s → α₁ - α₂ ≠ -s := by
  simp only [Ne, indicial_eq_zero_iff h]
  constructor
  · intro H s hs hα
    exact H s hs (Or.inr (by linear_combination hα))
  · intro H s hs hα
    rcases hα with hα | hα
    · have : (s : ℂ) = 0 := by linear_combination hα
      have : s = 0 := by exact_mod_cast this
      omega
    · exact H s hs (by linear_combination hα)

/-! ### 2.7.5: the Frobenius coefficients -/

/-- **DLMF 2.7.5**: the coefficients `aₛ` of the Frobenius series `(z−z₀)^α ∑ aₛ (z−z₀)^s`:
`a₀ = 1` and `Q(α + s) aₛ = −∑_{r<s} ((α + r) f_{s−r} + g_{s−r}) aᵣ` for `s ≥ 1`. -/
noncomputable def frobCoeff (fc gc : ℕ → ℂ) (α : ℂ) : ℕ → ℂ
  | 0 => 1
  | s + 1 => -(∑ r : Fin (s + 1), ((α + (r : ℕ)) * fc (s + 1 - r) + gc (s + 1 - r)) *
      frobCoeff fc gc α r) / indicial fc gc (α + (s + 1 : ℕ))

theorem frobCoeff_zero (fc gc : ℕ → ℂ) (α : ℂ) : frobCoeff fc gc α 0 = 1 := by rw [frobCoeff]

/-- **DLMF 2.7.5** as a recurrence, for `s ≥ 1` with `Q(α + s) ≠ 0`. -/
theorem frobCoeff_succ (fc gc : ℕ → ℂ) (α : ℂ) (s : ℕ) (hQ : indicial fc gc (α + (s + 1 : ℕ)) ≠ 0) :
    indicial fc gc (α + (s + 1 : ℕ)) * frobCoeff fc gc α (s + 1) =
      -∑ r ∈ Finset.range (s + 1), ((α + r) * fc (s + 1 - r) + gc (s + 1 - r)) *
        frobCoeff fc gc α r := by
  rw [frobCoeff, Finset.sum_range, mul_div_assoc', mul_div_cancel_left₀ _ hQ]

/-! ### The point at infinity -/

/-- The coefficient `f` of the equation satisfied by `W(ζ) = w(1/ζ)`: `2/ζ − f(1/ζ)/ζ²`. -/
noncomputable def infinityF (f : ℂ → ℂ) (ζ : ℂ) : ℂ := 2 / ζ - f ζ⁻¹ / ζ ^ 2

/-- The coefficient `g` of the equation satisfied by `W(ζ) = w(1/ζ)`: `g(1/ζ)/ζ⁴`. -/
noncomputable def infinityG (g : ℂ → ℂ) (ζ : ℂ) : ℂ := g ζ⁻¹ / ζ ^ 4

/-- **DLMF §2.7(i)**, the point at infinity: if `w` solves 2.7.1 on `D` (with `0 ∉ D`), then
`W(ζ) = w(1/ζ)` solves `W″ + (2/ζ − f(1/ζ)/ζ²) W′ + g(1/ζ)/ζ⁴ W = 0` on `{ζ ≠ 0 | 1/ζ ∈ D}`; the
classification of `z = ∞` is that of `ζ = 0` for this equation. -/
theorem isODESolution_comp_inv {D : Set ℂ} {f g w : ℂ → ℂ} (hDo : IsOpen D)
    (hw : IsODESolution D f g w) :
    IsODESolution {ζ : ℂ | ζ ≠ 0 ∧ ζ⁻¹ ∈ D} (infinityF f) (infinityG g) fun ζ => w ζ⁻¹ := by
  have hopen : IsOpen {ζ : ℂ | ζ ≠ 0 ∧ ζ⁻¹ ∈ D} :=
    continuousOn_inv₀.isOpen_inter_preimage isOpen_ne hDo
  refine isODESolution_of_hasDerivAt hopen (w' := fun ζ => -(deriv w ζ⁻¹ * (ζ ^ 2)⁻¹))
    fun ζ hζ => ?_
  obtain ⟨hζ0, hζD⟩ := hζ
  have hinv : HasDerivAt (fun ζ : ℂ => ζ⁻¹) (-(ζ ^ 2)⁻¹) ζ := hasDerivAt_inv hζ0
  obtain ⟨h1, h2⟩ := hw.hasDerivAt hDo hζD
  constructor
  · convert h1.comp ζ hinv using 1
    · rfl
    · ring
  · have hsq : HasDerivAt (fun ζ : ℂ => (ζ ^ 2)⁻¹) (-(2 * ζ ^ (2 - 1)) / (ζ ^ 2) ^ 2) ζ :=
      (hasDerivAt_pow 2 ζ).inv (pow_ne_zero 2 hζ0)
    convert ((h2.comp ζ hinv).mul hsq).neg using 1
    · rfl
    · simp only [infinityF, infinityG, Function.comp_apply]
      field_simp
      ring

end Azurite.DLMF
