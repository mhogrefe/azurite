/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section13Change
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# DLMF §2.8(i): Differential Equations with a Parameter — Classification of Cases, 2.8.1–2.8.9

* 2.8.1 (`IsParamSolution`): `w″ = (u² f(z) + g(z)) w` with a parameter `u`.
* Transition points (`IsTransitionPoint`: zeros and singularities of `f`; zeros are turning
  points) and the three cases `IsCaseI` (no transition points in `D`, `g` analytic),
  `IsCaseII` (`f` has a simple zero at `z₀`, `g` analytic there), `IsCaseIII` (`f` has a simple
  pole at `z₀`, `(z − z₀)² g` analytic there); `IsCaseII.isTransitionPoint`,
  `IsCaseIII.isTransitionPoint`.
* 2.8.2–2.8.4 (`dlmf_2_8_3`, `liouvillePsi`): the Liouville transformation `W = ż^{−1/2} w`
  (with `q = ż^{−1/2}` any function with `q² ż = 1`) gives
  `d²W/dξ² = (u² ż² f(z) + ψ(ξ)) W`, `ψ = ż² g + ż^{1/2} d²(ż^{−1/2})/dξ²` (from §1.13(iv)).
* 2.8.5–2.8.7 (`dlmf_2_8_5`, `dlmf_2_8_6`, `dlmf_2_8_7`, from `liouville_choice`): the relations
  `ξ = ∫ f^{1/2}`, `⅔ ξ^{3/2} = ∫ f^{1/2}`, `2 ξ^{1/2} = ∫ f^{1/2}` give `ż² f = 1, ξ, 1/ξ`.
* 2.8.8 (`dlmf_2_8_8`): `d²W/dξ² = (u² ξ^m + ψ(ξ)) W`.
* Approximating equations: Case I, `e^{±uξ}` (`caseI_exp`); Case II, Airy functions
  (`caseII_airy`: if `A″(t) = t A(t)` then `A(cξ)` with `c³ = u²` solves `W″ = u² ξ W`);
  Case III, 2.8.9 (`dlmf_2_8_9`: if `y` solves the (modified) Bessel equation of order `ν`, then
  `ξ^{1/2} y(2uξ^{1/2})` solves `W″ = (±u²/ξ + ρ/ξ²) W` with `ρ = (ν² − 1)/4`, i.e.
  `ν = ±(1 + 4ρ)^{1/2}`).

Property (a) of the transformation (`ξ` and `z` analytic functions of each other at the
transition point) is in `Section8Transition`.
-/

open Filter Topology Set Complex

namespace Azurite.DLMF

/-! ### 2.8.1 and the classification -/

/-- **DLMF 2.8.1**: `w″ = (u² f(z) + g(z)) w` in `D`. -/
def IsParamSolution (D : Set ℂ) (u : ℂ) (f g w : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ w D ∧ ∀ z ∈ D, deriv (deriv w) z = (u ^ 2 * f z + g z) * w z

/-- A transition point: a zero (turning point) or a singularity of `f`. -/
def IsTransitionPoint (f : ℂ → ℂ) (z₀ : ℂ) : Prop := ¬ AnalyticAt ℂ f z₀ ∨ f z₀ = 0

/-- **Case I**: no transition points in `D`, and `g` analytic there. -/
def IsCaseI (D : Set ℂ) (f g : ℂ → ℂ) : Prop :=
  (∀ z ∈ D, ¬ IsTransitionPoint f z) ∧ ∀ z ∈ D, AnalyticAt ℂ g z

/-- **Case II**: `f` has a simple zero at `z₀` and `g` is analytic at `z₀`. -/
def IsCaseII (f g : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  AnalyticAt ℂ f z₀ ∧ f z₀ = 0 ∧ deriv f z₀ ≠ 0 ∧ AnalyticAt ℂ g z₀

/-- **Case III**: `f` has a simple pole at `z₀` (`f = h/(z − z₀)` with `h` analytic and nonzero
at `z₀`) and `(z − z₀)² g(z)` is analytic at `z₀`. -/
def IsCaseIII (f g : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  (∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ h z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] z₀, f z = h z / (z - z₀)) ∧
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) ^ 2 * g z = G z

theorem IsCaseI.analyticAt_ne_zero {D : Set ℂ} {f g : ℂ → ℂ} (h : IsCaseI D f g) {z : ℂ}
    (hz : z ∈ D) : AnalyticAt ℂ f z ∧ f z ≠ 0 := by
  have := h.1 z hz
  simp only [IsTransitionPoint, not_or, not_not] at this
  exact this

theorem IsCaseII.isTransitionPoint {f g : ℂ → ℂ} {z₀ : ℂ} (h : IsCaseII f g z₀) :
    IsTransitionPoint f z₀ :=
  Or.inr h.2.1

/-- In Case III, `z₀` is a singularity of `f`. -/
theorem IsCaseIII.isTransitionPoint {f g : ℂ → ℂ} {z₀ : ℂ} (h : IsCaseIII f g z₀) :
    IsTransitionPoint f z₀ := by
  refine Or.inl fun hf => ?_
  obtain ⟨⟨k, hk, hk0, hfk⟩, -⟩ := h
  -- `(z − z₀) f(z) → 0`, but `= k(z) → k(z₀) ≠ 0`
  have h1 : Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 0) := by
    have hc : ContinuousAt (fun z => (z - z₀) * f z) z₀ :=
      (continuousAt_id.sub continuousAt_const).mul hf.continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 (k z₀)) := by
    refine (hk.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hfk, self_mem_nhdsWithin] with z hz hz₀
    rw [hz, mul_div_cancel₀ _ (sub_ne_zero.mpr hz₀)]
  exact hk0 (tendsto_nhds_unique h2 h1)

/-! ### 2.8.2–2.8.4: the Liouville transformation -/

/-- **DLMF 2.8.4**: `ψ(ξ) = ż² g(z) + ż^{1/2} d²(ż^{−1/2})/dξ²`, with `z = φ(ξ)` and
`q = ż^{−1/2}` (so `ż^{1/2} = q⁻¹`). -/
noncomputable def liouvillePsi (φ q g : ℂ → ℂ) (ξ : ℂ) : ℂ :=
  deriv φ ξ ^ 2 * g (φ ξ) + (q ξ)⁻¹ * deriv (deriv q) ξ

/-- **DLMF 2.8.2–2.8.3**: with `z = φ(ξ)` and `W = ż^{−1/2} w = q(ξ) w(φ(ξ))` (`q² ż = 1`), a
solution `w` of 2.8.1 gives `d²W/dξ² = (u² ż² f(z) + ψ(ξ)) W`. -/
theorem dlmf_2_8_3 {D E : Set ℂ} (hEo : IsOpen E) (hDo : IsOpen D) {φ q f g w : ℂ → ℂ} (u : ℂ)
    (hφ : DifferentiableOn ℂ φ E) (hq : DifferentiableOn ℂ q E)
    (hqφ : ∀ ξ ∈ E, q ξ ^ 2 * deriv φ ξ = 1) (hφD : MapsTo φ E D)
    (hw : IsParamSolution D u f g w) {ξ : ℂ} (hξ : ξ ∈ E) :
    deriv (deriv fun ξ => q ξ * w (φ ξ)) ξ =
      (u ^ 2 * deriv φ ξ ^ 2 * f (φ ξ) + liouvillePsi φ q g ξ) * (q ξ * w (φ ξ)) := by
  rw [dlmf_1_13_19 hEo hDo hφ hq hqφ hφD hw.1 (H := fun z => u ^ 2 * f z + g z) hw.2 hξ,
    dlmf_1_13_20 hEo hφ hq hqφ hξ, liouvillePsi]
  ring

/-- **DLMF 2.8.8**: if `ż² f(z) = ξ^m`, the transformed equation is
`d²W/dξ² = (u² ξ^m + ψ(ξ)) W` (`m = 0, 1, −1` in Cases I, II, III). -/
theorem dlmf_2_8_8 {D E : Set ℂ} (hEo : IsOpen E) (hDo : IsOpen D) {φ q f g w : ℂ → ℂ} (u : ℂ)
    (m : ℤ) (hφ : DifferentiableOn ℂ φ E) (hq : DifferentiableOn ℂ q E)
    (hqφ : ∀ ξ ∈ E, q ξ ^ 2 * deriv φ ξ = 1) (hφD : MapsTo φ E D)
    (hw : IsParamSolution D u f g w) (hrel : ∀ ξ ∈ E, deriv φ ξ ^ 2 * f (φ ξ) = ξ ^ m) {ξ : ℂ}
    (hξ : ξ ∈ E) :
    deriv (deriv fun ξ => q ξ * w (φ ξ)) ξ =
      (u ^ 2 * ξ ^ m + liouvillePsi φ q g ξ) * (q ξ * w (φ ξ)) := by
  rw [dlmf_2_8_3 hEo hDo u hφ hq hqφ hφD hw hξ, mul_assoc (u ^ 2), hrel ξ hξ]

/-! ### 2.8.5–2.8.7: the choice of `ξ` -/

/-- If `F′ = s` with `s² = f` (`F = ∫ f^{1/2}`) and `F(z(ξ)) = H(ξ)` with `H′ = k`, then
`ż² f(z) = k(ξ)²`. -/
theorem liouville_choice {D E : Set ℂ} (hEo : IsOpen E) {F s f φ H k : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (s z) z) (hs : ∀ z ∈ D, s z ^ 2 = f z)
    (hφ : DifferentiableOn ℂ φ E) (hφD : MapsTo φ E D) (hrel : ∀ ξ ∈ E, F (φ ξ) = H ξ)
    (hH : ∀ ξ ∈ E, HasDerivAt H (k ξ) ξ) {ξ : ℂ} (hξ : ξ ∈ E) :
    deriv φ ξ ^ 2 * f (φ ξ) = k ξ ^ 2 := by
  have hφξ := (hφ.differentiableAt (hEo.mem_nhds hξ)).hasDerivAt
  have hc := (hF _ (hφD hξ)).comp ξ hφξ
  have heq : (F ∘ φ) =ᶠ[𝓝 ξ] H := Filter.eventually_of_mem (hEo.mem_nhds hξ) hrel
  have := (hc.congr_of_eventuallyEq heq.symm).unique (hH ξ hξ)
  rw [← this, ← hs _ (hφD hξ)]
  ring

/-- **DLMF 2.8.5** (Case I): `ξ = ∫ f^{1/2} dz` gives `ż² f(z) = 1`. -/
theorem dlmf_2_8_5 {D E : Set ℂ} (hEo : IsOpen E) {F s f φ : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (s z) z) (hs : ∀ z ∈ D, s z ^ 2 = f z)
    (hφ : DifferentiableOn ℂ φ E) (hφD : MapsTo φ E D) (hrel : ∀ ξ ∈ E, F (φ ξ) = ξ) {ξ : ℂ}
    (hξ : ξ ∈ E) : deriv φ ξ ^ 2 * f (φ ξ) = 1 := by
  rw [liouville_choice hEo hF hs hφ hφD hrel (fun ξ _ => hasDerivAt_id ξ) hξ, one_pow]

theorem cpow_one_half_sq (ξ : ℂ) : (ξ ^ (1 / 2 : ℂ)) ^ 2 = ξ := by
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact cpow_nat_inv_pow ξ two_ne_zero

/-- **DLMF 2.8.6** (Case II): `⅔ ξ^{3/2} = ∫_{z₀}^{z} f^{1/2}(t) dt` gives `ż² f(z) = ξ` (on a set
where the principal branch is used, `E ⊆ slitPlane`). -/
theorem dlmf_2_8_6 {D E : Set ℂ} (hEo : IsOpen E) (hEs : E ⊆ slitPlane) {F s f φ : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (s z) z) (hs : ∀ z ∈ D, s z ^ 2 = f z)
    (hφ : DifferentiableOn ℂ φ E) (hφD : MapsTo φ E D)
    (hrel : ∀ ξ ∈ E, F (φ ξ) = 2 / 3 * ξ ^ (3 / 2 : ℂ)) {ξ : ℂ} (hξ : ξ ∈ E) :
    deriv φ ξ ^ 2 * f (φ ξ) = ξ := by
  have hH : ∀ ξ ∈ E, HasDerivAt (fun ξ => 2 / 3 * ξ ^ (3 / 2 : ℂ)) (ξ ^ (1 / 2 : ℂ)) ξ := by
    intro ξ hξ
    refine (((hasDerivAt_id ξ).cpow_const (c := (3 / 2 : ℂ)) (hEs hξ)).const_mul
      (2 / 3 : ℂ)).congr_deriv ?_
    simp only [id]
    rw [show (3 / 2 : ℂ) - 1 = 1 / 2 by norm_num]
    ring
  rw [liouville_choice hEo hF hs hφ hφD hrel hH hξ, cpow_one_half_sq]

/-- **DLMF 2.8.7** (Case III): `2 ξ^{1/2} = ∫_{z₀}^{z} f^{1/2}(t) dt` gives `ż² f(z) = 1/ξ`. -/
theorem dlmf_2_8_7 {D E : Set ℂ} (hEo : IsOpen E) (hEs : E ⊆ slitPlane) {F s f φ : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (s z) z) (hs : ∀ z ∈ D, s z ^ 2 = f z)
    (hφ : DifferentiableOn ℂ φ E) (hφD : MapsTo φ E D)
    (hrel : ∀ ξ ∈ E, F (φ ξ) = 2 * ξ ^ (1 / 2 : ℂ)) {ξ : ℂ} (hξ : ξ ∈ E) :
    deriv φ ξ ^ 2 * f (φ ξ) = 1 / ξ := by
  have hH : ∀ ξ ∈ E, HasDerivAt (fun ξ => 2 * ξ ^ (1 / 2 : ℂ)) (ξ ^ (1 / 2 : ℂ))⁻¹ ξ := by
    intro ξ hξ
    refine (((hasDerivAt_id ξ).cpow_const (c := (1 / 2 : ℂ)) (hEs hξ)).const_mul
      (2 : ℂ)).congr_deriv ?_
    simp only [id]
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg]
    ring
  rw [liouville_choice hEo hF hs hφ hφD hrel hH hξ, inv_pow, cpow_one_half_sq, one_div]

/-! ### The approximating equations -/

/-- Case I (`m = 0`, `ψ = 0`): `W = e^{±uξ}` solves `W″ = u² W`. -/
theorem caseI_exp (u σ : ℂ) (hσ : σ ^ 2 = 1) (ξ : ℂ) :
    HasDerivAt (fun ξ => cexp (σ * u * ξ)) (σ * u * cexp (σ * u * ξ)) ξ ∧
      HasDerivAt (fun ξ => σ * u * cexp (σ * u * ξ)) (u ^ 2 * cexp (σ * u * ξ)) ξ := by
  have h := ((hasDerivAt_id ξ).const_mul (σ * u)).cexp
  refine ⟨h.congr_deriv (by simp only [id]; ring), (h.const_mul (σ * u)).congr_deriv ?_⟩
  simp only [id]
  linear_combination u ^ 2 * cexp (σ * u * ξ) * hσ

/-- Case II (`m = 1`, `ψ = 0`): Airy functions. If `A″(t) = t A(t)` (the Airy equation 9.2.1),
then `W(ξ) = A(cξ)` with `c³ = u²` solves `W″ = u² ξ W`. -/
theorem caseII_airy {A A' : ℂ → ℂ} (hA : ∀ t, HasDerivAt A (A' t) t)
    (hA' : ∀ t, HasDerivAt A' (t * A t) t) {u c : ℂ} (hc : c ^ 3 = u ^ 2) (ξ : ℂ) :
    HasDerivAt (fun ξ => A (c * ξ)) (c * A' (c * ξ)) ξ ∧
      HasDerivAt (fun ξ => c * A' (c * ξ)) (u ^ 2 * ξ * A (c * ξ)) ξ := by
  have hl : HasDerivAt (fun ξ : ℂ => c * ξ) c ξ := by simpa using (hasDerivAt_id ξ).const_mul c
  refine ⟨((hA (c * ξ)).comp ξ hl).congr_deriv (by ring),
    (((hA' (c * ξ)).comp ξ hl).const_mul c).congr_deriv ?_⟩
  rw [← hc]
  ring

/-- `d/dξ ξ^{1/2} = 1/(2 ξ^{1/2})` off the branch cut. -/
theorem hasDerivAt_cpow_half {ξ : ℂ} (hξ : ξ ∈ slitPlane) :
    HasDerivAt (fun ξ : ℂ => ξ ^ (1 / 2 : ℂ)) (1 / (2 * ξ ^ (1 / 2 : ℂ))) ξ := by
  refine ((hasDerivAt_id ξ).cpow_const (c := (1 / 2 : ℂ)) hξ).congr_deriv ?_
  simp only [id]
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg]
  ring

/-- **DLMF 2.8.9** (Case III): if `y` solves the Bessel-type equation
`t² y″ + t y′ − (σ t² + ν²) y = 0` (`σ = 1`: modified Bessel; `σ = −1`: Bessel), then
`W(ξ) = ξ^{1/2} y(2u ξ^{1/2})` solves `d²W/dξ² = (σ u²/ξ + ρ/ξ²) W` with `ρ = (ν² − 1)/4`, i.e.
the order is `ν = ±(1 + 4ρ)^{1/2}`. -/
theorem dlmf_2_8_9 {y y' y'' : ℂ → ℂ} {u σ ν : ℂ} {ξ : ℂ} (hξ : ξ ∈ slitPlane)
    (hy : HasDerivAt y (y' (2 * u * ξ ^ (1 / 2 : ℂ))) (2 * u * ξ ^ (1 / 2 : ℂ)))
    (hy' : HasDerivAt y' (y'' (2 * u * ξ ^ (1 / 2 : ℂ))) (2 * u * ξ ^ (1 / 2 : ℂ)))
    (hbes : (2 * u * ξ ^ (1 / 2 : ℂ)) ^ 2 * y'' (2 * u * ξ ^ (1 / 2 : ℂ)) +
      (2 * u * ξ ^ (1 / 2 : ℂ)) * y' (2 * u * ξ ^ (1 / 2 : ℂ)) -
      (σ * (2 * u * ξ ^ (1 / 2 : ℂ)) ^ 2 + ν ^ 2) * y (2 * u * ξ ^ (1 / 2 : ℂ)) = 0) :
    HasDerivAt (fun ξ => ξ ^ (1 / 2 : ℂ) * y (2 * u * ξ ^ (1 / 2 : ℂ)))
        ((2 * ξ ^ (1 / 2 : ℂ))⁻¹ * y (2 * u * ξ ^ (1 / 2 : ℂ)) +
          u * y' (2 * u * ξ ^ (1 / 2 : ℂ))) ξ ∧
      HasDerivAt (fun ξ => (2 * ξ ^ (1 / 2 : ℂ))⁻¹ * y (2 * u * ξ ^ (1 / 2 : ℂ)) +
          u * y' (2 * u * ξ ^ (1 / 2 : ℂ)))
        ((σ * u ^ 2 / ξ + (ν ^ 2 - 1) / 4 / ξ ^ 2) *
          (ξ ^ (1 / 2 : ℂ) * y (2 * u * ξ ^ (1 / 2 : ℂ)))) ξ := by
  have hr := hasDerivAt_cpow_half hξ
  have hr0 : ξ ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => slitPlane_ne_zero hξ h.1
  have hr2 : (ξ ^ (1 / 2 : ℂ)) ^ 2 = ξ := cpow_one_half_sq ξ
  have ht : HasDerivAt (fun ξ : ℂ => 2 * u * ξ ^ (1 / 2 : ℂ)) (2 * u * (1 / (2 * ξ ^ (1 / 2 : ℂ))))
      ξ := hr.const_mul (2 * u)
  have hyt := hy.comp ξ ht
  have hy't := hy'.comp ξ ht
  constructor
  · refine (hr.mul hyt).congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp
  · have hinv := (hr.const_mul (2 : ℂ)).inv (mul_ne_zero two_ne_zero hr0)
    refine ((hinv.mul hyt).add (hy't.const_mul u)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.inv_apply]
    set r := ξ ^ (1 / 2 : ℂ)
    set Y := y (2 * u * r)
    set Y1 := y' (2 * u * r)
    set Y2 := y'' (2 * u * r)
    rw [← hr2]
    field_simp
    linear_combination 4 * hbes

end Azurite.DLMF
