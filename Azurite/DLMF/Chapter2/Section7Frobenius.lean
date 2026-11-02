/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section7Series
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# DLMF §2.7(i): Regular Singularities: Fuchs–Frobenius Theory — the solutions 2.7.4

For data 2.7.2 (`FrobeniusData f g z₀ R fc gc`) and an index `α` with `Q(α) = 0` and
`Q(α + s) ≠ 0` for `s ≥ 1`:

* the Frobenius coefficients 2.7.5 satisfy `‖aₛ‖ ρ^s ≤ K` for every `ρ < R`
  (`FrobeniusData.frobCoeff_bound`), so `∑ aₛ (z − z₀)^s` converges absolutely on the whole ball
  `|z − z₀| < R` — the radius of convergence is at least the distance to the next singularity
  (`FrobeniusData.hasRadiusGE_frobCoeff`, `FrobeniusData.summable_frobCoeff`);
* `w(z) = (z − z₀)^α ∑ aₛ (z − z₀)^s` (`frobSolution`) solves 2.7.1 on the slit ball
  `{|z − z₀| < R, z − z₀ ∉ (−∞, 0]}` (`FrobeniusData.dlmf_2_7_4`), the power-series factor
  satisfying `(z−z₀)² u″ + (2α + F) (z−z₀) u′ + (α(α−1) + αF + G) u = 0`
  (`FrobeniusData.frobU_ode`);
* when `α₁ − α₂` is not an integer the two solutions `w₁, w₂` are linearly independent
  (`FrobeniusData.dlmf_2_7_4_independent`, via the Wronskian), and both exist
  (`FrobeniusData.dlmf_2_7_4_pair`).

The case `α₁ − α₂ ∈ ℕ` (2.7.6, logarithmic solution) is not formalized here.
-/

open Filter Topology Set Complex Metric Finset

namespace Azurite.DLMF

variable {f g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} {fc gc : ℕ → ℂ}

theorem FrobeniusData.hasRadiusGE_fc (F : FrobeniusData f g z₀ R fc gc) : HasRadiusGE fc R :=
  hasRadiusGE_of_summable F.f_summable

theorem FrobeniusData.hasRadiusGE_gc (F : FrobeniusData f g z₀ R fc gc) : HasRadiusGE gc R :=
  hasRadiusGE_of_summable F.g_summable

/-! ### Growth of the indicial polynomial -/

theorem indicial_add_eq (fc gc : ℕ → ℂ) (α : ℂ) (s : ℕ) :
    indicial fc gc (α + s) = (s : ℂ) ^ 2 + ((2 * α - 1 + fc 0) * s + indicial fc gc α) := by
  simp only [indicial]
  ring

/-- `|Q(α + s)| ≥ s² − C₁ s − C₂`. -/
theorem norm_indicial_add_ge (fc gc : ℕ → ℂ) (α : ℂ) (s : ℕ) :
    (s : ℝ) ^ 2 - ‖2 * α - 1 + fc 0‖ * s - ‖indicial fc gc α‖ ≤
      ‖indicial fc gc (α + s)‖ := by
  rw [indicial_add_eq]
  set X := (2 * α - 1 + fc 0) * s + indicial fc gc α with hX
  have h1 : ‖((s : ℂ)) ^ 2‖ = (s : ℝ) ^ 2 := by rw [norm_pow, Complex.norm_natCast]
  have h2 : ‖X‖ ≤ ‖2 * α - 1 + fc 0‖ * s + ‖indicial fc gc α‖ := by
    rw [hX]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast]
  have h3 := norm_sub_le ((s : ℂ) ^ 2 + X) X
  rw [add_sub_cancel_right, h1] at h3
  linarith

/-! ### The majorant bound for the Frobenius coefficients -/

/-- The Frobenius coefficients 2.7.5 satisfy `‖aₛ‖ ρ^s ≤ K` for every `ρ < R`. -/
theorem FrobeniusData.frobCoeff_bound (F : FrobeniusData f g z₀ R fc gc) {α : ℂ}
    (hα : ∀ s : ℕ, 1 ≤ s → indicial fc gc (α + s) ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ K, ∀ s, ‖frobCoeff fc gc α s‖ * ρ ^ s ≤ K := by
  set ρ₁ := (ρ + R) / 2 with hρ₁
  have hρ₁0 : 0 < ρ₁ := by linarith
  have hρ₁R : ρ₁ < R := by linarith
  have hρρ₁ : ρ < ρ₁ := by linarith
  clear_value ρ₁
  obtain ⟨M₁, hM₁⟩ := F.hasRadiusGE_fc ρ₁ hρ₁0 hρ₁R
  obtain ⟨M₂, hM₂⟩ := F.hasRadiusGE_gc ρ₁ hρ₁0 hρ₁R
  have hM₁0 : 0 ≤ M₁ := le_trans (by positivity) (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := le_trans (by positivity) (hM₂ 0)
  obtain ⟨M, hM0, hfM, hgM⟩ : ∃ M : ℝ, 0 ≤ M ∧ (∀ s, ‖fc s‖ ≤ M / ρ₁ ^ s) ∧
      ∀ s, ‖gc s‖ ≤ M / ρ₁ ^ s :=
    ⟨M₁ + M₂, by linarith,
      fun s => (le_div_iff₀ (pow_pos hρ₁0 s)).mpr ((hM₁ s).trans (by linarith)),
      fun s => (le_div_iff₀ (pow_pos hρ₁0 s)).mpr ((hM₂ s).trans (by linarith))⟩
  obtain ⟨q, hq, hq0, hq1⟩ : ∃ q : ℝ, q = ρ / ρ₁ ∧ 0 < q ∧ q < 1 :=
    ⟨ρ / ρ₁, rfl, by positivity, (div_lt_one hρ₁0).mpr hρρ₁⟩
  obtain ⟨A, hA, hA0⟩ : ∃ A : ℝ, A = 1 - q ∧ 0 < A := ⟨1 - q, rfl, by linarith⟩
  set C₁ := ‖2 * α - 1 + fc 0‖ with hC₁
  set C₂ := ‖indicial fc gc α‖ with hC₂
  obtain ⟨B, hB, hB0⟩ : ∃ B : ℝ, B = A * C₁ + M * q ∧ 0 ≤ B := ⟨_, rfl, by positivity⟩
  obtain ⟨C, hC, hC0⟩ : ∃ C : ℝ, C = A * C₂ + M * q * ‖α‖ ∧ 0 ≤ C := ⟨_, rfl, by positivity⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((B + C + 1) / A)
  -- the key inequality `M q (‖α‖ + s) ≤ A ‖Q(α + s)‖` for `s ≥ N₀ + 1`
  have hkey : ∀ s : ℕ, N₀ + 1 ≤ s → M * q * (‖α‖ + s) ≤ A * ‖indicial fc gc (α + s)‖ := by
    intro s hs
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
    have hsN : (N₀ : ℝ) + 1 ≤ s := by exact_mod_cast hs
    have hAs : B + C + 1 ≤ A * s := by
      have := (div_le_iff₀ hA0).mp hN₀
      nlinarith
    have hQ := norm_indicial_add_ge fc gc α s
    have h1 : B * s + C ≤ A * s ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hAs (by linarith : (0 : ℝ) ≤ s),
        mul_le_mul_of_nonneg_left hs1 hC0]
    have h2 := mul_le_mul_of_nonneg_left hQ hA0.le
    rw [← hC₁, ← hC₂] at h2
    nlinarith
  set K := ∑ r ∈ range (N₀ + 1), ‖frobCoeff fc gc α r‖ * ρ ^ r with hK
  have hK0 : 0 ≤ K := sum_nonneg fun r _ => by positivity
  clear_value K
  refine ⟨K, fun s => ?_⟩
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  rcases lt_or_ge s (N₀ + 1) with hsN | hsN
  · rw [hK]
    exact single_le_sum (f := fun r => ‖frobCoeff fc gc α r‖ * ρ ^ r) (fun r _ => by positivity)
      (mem_range.mpr hsN)
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hQne := hα (t + 1) (by omega)
  have hQpos : 0 < ‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ := norm_pos_iff.mpr hQne
  have hrec := frobCoeff_succ fc gc α t hQne
  -- the recurrence bounds `‖Q‖ ‖a_{t+1}‖`
  have h1 : ‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ * ‖frobCoeff fc gc α (t + 1)‖ ≤
      ∑ r ∈ range (t + 1), (‖α‖ + r + 1) * (M / ρ₁ ^ (t + 1 - r)) * ‖frobCoeff fc gc α r‖ := by
    rw [← norm_mul, hrec, norm_neg]
    refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hαr : ‖α + (r : ℂ)‖ ≤ ‖α‖ + r := by
      have := norm_add_le α (r : ℂ)
      rwa [Complex.norm_natCast] at this
    calc ‖(α + r) * fc (t + 1 - r) + gc (t + 1 - r)‖
        ≤ ‖α + (r : ℂ)‖ * ‖fc (t + 1 - r)‖ + ‖gc (t + 1 - r)‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ (‖α‖ + r) * (M / ρ₁ ^ (t + 1 - r)) + M / ρ₁ ^ (t + 1 - r) :=
          add_le_add (mul_le_mul hαr (hfM _) (norm_nonneg _) (by positivity)) (hgM _)
      _ = (‖α‖ + r + 1) * (M / ρ₁ ^ (t + 1 - r)) := by ring
  -- multiply by `ρ^(t+1)` and use the induction hypothesis
  have h2 : ∀ r ∈ range (t + 1),
      (‖α‖ + r + 1) * (M / ρ₁ ^ (t + 1 - r)) * ‖frobCoeff fc gc α r‖ * ρ ^ (t + 1) ≤
        (‖α‖ + ((t + 1 : ℕ) : ℝ)) * M * K * q ^ (t + 1 - r) := by
    intro r hr
    have hr' : r < t + 1 := mem_range.mp hr
    have har : ‖frobCoeff fc gc α r‖ ≤ K / ρ ^ r := (le_div_iff₀ (pow_pos hρ r)).mpr (ih r hr')
    have hr1 : ‖α‖ + r + 1 ≤ ‖α‖ + ((t + 1 : ℕ) : ℝ) := by
      have : (r : ℝ) + 1 ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast hr'
      linarith
    calc (‖α‖ + r + 1) * (M / ρ₁ ^ (t + 1 - r)) * ‖frobCoeff fc gc α r‖ * ρ ^ (t + 1)
        ≤ (‖α‖ + ((t + 1 : ℕ) : ℝ)) * (M / ρ₁ ^ (t + 1 - r)) * (K / ρ ^ r) * ρ ^ (t + 1) := by
          gcongr
      _ = (‖α‖ + ((t + 1 : ℕ) : ℝ)) * M * K * q ^ (t + 1 - r) := by
          rw [hq, div_pow, ← pow_sub_mul_pow ρ hr'.le]
          field_simp
  -- the geometric sum
  have h3 : ∑ r ∈ range (t + 1), q ^ (t + 1 - r) ≤ q / (1 - q) := by
    have : ∑ r ∈ range (t + 1), q ^ (t + 1 - r) = ∑ j ∈ range (t + 1), q ^ (j + 1) := by
      rw [← sum_range_reflect (fun j => q ^ (j + 1)) (t + 1)]
      refine sum_congr rfl fun r hr => ?_
      have := mem_range.mp hr
      congr 1
      omega
    rw [this]
    calc ∑ j ∈ range (t + 1), q ^ (j + 1) = q * ∑ j ∈ range (t + 1), q ^ j := by
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by ring
      _ ≤ q * (1 / (1 - q)) := by
          gcongr
          have := geom_sum_Ico_le_of_lt_one hq0.le hq1 (m := 0) (n := t + 1)
          rwa [pow_zero, ← range_eq_Ico] at this
      _ = q / (1 - q) := by ring
  have h4 : ‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ * (‖frobCoeff fc gc α (t + 1)‖ * ρ ^ (t + 1)) ≤
      (‖α‖ + ((t + 1 : ℕ) : ℝ)) * M * K * (q / (1 - q)) := by
    calc ‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ * (‖frobCoeff fc gc α (t + 1)‖ * ρ ^ (t + 1))
        = ‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ * ‖frobCoeff fc gc α (t + 1)‖ * ρ ^ (t + 1) := by
          ring
      _ ≤ (∑ r ∈ range (t + 1), (‖α‖ + r + 1) * (M / ρ₁ ^ (t + 1 - r)) *
            ‖frobCoeff fc gc α r‖) * ρ ^ (t + 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ∑ r ∈ range (t + 1), (‖α‖ + r + 1) * (M / ρ₁ ^ (t + 1 - r)) *
            ‖frobCoeff fc gc α r‖ * ρ ^ (t + 1) := by rw [sum_mul]
      _ ≤ ∑ r ∈ range (t + 1), (‖α‖ + ((t + 1 : ℕ) : ℝ)) * M * K * q ^ (t + 1 - r) :=
          sum_le_sum h2
      _ = (‖α‖ + ((t + 1 : ℕ) : ℝ)) * M * K * ∑ r ∈ range (t + 1), q ^ (t + 1 - r) := by
          rw [mul_sum]
      _ ≤ (‖α‖ + ((t + 1 : ℕ) : ℝ)) * M * K * (q / (1 - q)) := by gcongr
  have hk := hkey (t + 1) hsN
  have h5 : A * ‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ *
      (‖frobCoeff fc gc α (t + 1)‖ * ρ ^ (t + 1)) ≤
        A * ‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ * K := by
    calc A * ‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ *
          (‖frobCoeff fc gc α (t + 1)‖ * ρ ^ (t + 1))
        = (1 - q) * (‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ *
            (‖frobCoeff fc gc α (t + 1)‖ * ρ ^ (t + 1))) := by rw [hA]; ring
      _ ≤ (1 - q) * ((‖α‖ + ((t + 1 : ℕ) : ℝ)) * M * K * (q / (1 - q))) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
      _ = M * q * (‖α‖ + ((t + 1 : ℕ) : ℝ)) * K := by
          have : (1 : ℝ) - q ≠ 0 := by linarith
          field_simp
      _ ≤ A * ‖indicial fc gc (α + ((t + 1 : ℕ) : ℂ))‖ * K := mul_le_mul_of_nonneg_right hk hK0
  exact le_of_mul_le_mul_left h5 (by positivity)

/-- The Frobenius series converges on the whole ball: its radius of convergence is at least the
distance `R` to the next singularity. -/
theorem FrobeniusData.hasRadiusGE_frobCoeff (F : FrobeniusData f g z₀ R fc gc) {α : ℂ}
    (hα : ∀ s : ℕ, 1 ≤ s → indicial fc gc (α + s) ≠ 0) : HasRadiusGE (frobCoeff fc gc α) R :=
  fun _ hρ hρR => F.frobCoeff_bound hα hρ hρR

theorem FrobeniusData.summable_frobCoeff (F : FrobeniusData f g z₀ R fc gc) {α : ℂ}
    (hα : ∀ s : ℕ, 1 ≤ s → indicial fc gc (α + s) ≠ 0) {z : ℂ} (hz : z ∈ ball z₀ R) :
    Summable fun s => ‖frobCoeff fc gc α s * (z - z₀) ^ s‖ :=
  (F.hasRadiusGE_frobCoeff hα).summable_norm hz

/-! ### The Frobenius solution -/

/-- **DLMF 2.7.4**: the Frobenius solution `w(z) = (z − z₀)^α ∑ aₛ (z − z₀)^s`, `a₀ = 1`. -/
noncomputable def frobSolution (fc gc : ℕ → ℂ) (α z₀ z : ℂ) : ℂ :=
  (z - z₀) ^ α * ∑' s, frobCoeff fc gc α s * (z - z₀) ^ s

theorem frobSolution_eq (fc gc : ℕ → ℂ) (α z₀ z : ℂ) :
    frobSolution fc gc α z₀ z = (z - z₀) ^ α * powerSeriesSum (frobCoeff fc gc α) z₀ z := rfl

/-- The derivative of the Frobenius solution. -/
noncomputable def frobDeriv (fc gc : ℕ → ℂ) (α z₀ z : ℂ) : ℂ :=
  α * (z - z₀) ^ (α - 1) * powerSeriesSum (frobCoeff fc gc α) z₀ z +
    (z - z₀) ^ α * powerSeriesSum (shiftDeriv (frobCoeff fc gc α)) z₀ z

/-- The ball `|z − z₀| < R` slit along `z − z₀ ∈ (−∞, 0]`, on which `(z − z₀)^α` is analytic. -/
def slitBall (z₀ : ℂ) (R : ℝ) : Set ℂ := {z | z ∈ ball z₀ R ∧ z - z₀ ∈ slitPlane}

theorem isOpen_slitBall (z₀ : ℂ) (R : ℝ) : IsOpen (slitBall z₀ R) :=
  isOpen_ball.inter (isOpen_slitPlane.preimage (continuous_id.sub continuous_const))

theorem hasDerivAt_frobSolution {α : ℂ} (ha : HasRadiusGE (frobCoeff fc gc α) R) {z : ℂ}
    (hz : z ∈ slitBall z₀ R) :
    HasDerivAt (frobSolution fc gc α z₀) (frobDeriv fc gc α z₀ z) z := by
  obtain ⟨hzb, hzs⟩ := hz
  have hu := ha.hasDerivAt hzb
  have hp : HasDerivAt (fun z => (z - z₀) ^ α) (α * (z - z₀) ^ (α - 1) * 1) z :=
    ((hasDerivAt_id z).sub_const z₀).cpow_const hzs
  refine (hp.mul hu).congr_deriv ?_
  simp only [frobDeriv]
  ring

theorem hasDerivAt_frobDeriv {α : ℂ} (ha : HasRadiusGE (frobCoeff fc gc α) R) {z : ℂ}
    (hz : z ∈ slitBall z₀ R) :
    HasDerivAt (frobDeriv fc gc α z₀)
      (α * ((α - 1) * (z - z₀) ^ (α - 1 - 1)) * powerSeriesSum (frobCoeff fc gc α) z₀ z +
        2 * α * (z - z₀) ^ (α - 1) * powerSeriesSum (shiftDeriv (frobCoeff fc gc α)) z₀ z +
        (z - z₀) ^ α * powerSeriesSum (shiftDeriv (shiftDeriv (frobCoeff fc gc α))) z₀ z) z := by
  obtain ⟨hzb, hzs⟩ := hz
  have hu := ha.hasDerivAt hzb
  have hu' := ha.shift.hasDerivAt hzb
  have hp : HasDerivAt (fun z => (z - z₀) ^ α) (α * (z - z₀) ^ (α - 1) * 1) z :=
    ((hasDerivAt_id z).sub_const z₀).cpow_const hzs
  have hp' : HasDerivAt (fun z => (z - z₀) ^ (α - 1)) ((α - 1) * (z - z₀) ^ (α - 1 - 1) * 1) z :=
    ((hasDerivAt_id z).sub_const z₀).cpow_const hzs
  refine (((hp'.const_mul α).mul hu).add (hp.mul hu')).congr_deriv ?_
  ring

/-- The power-series identity behind 2.7.4: if `a₀ = 1` and `a` satisfies the recurrence 2.7.5
with `Q(α) = 0`, and `∑ aₛ (z−z₀)^s` converges on the ball, then `u = ∑ aₛ (z−z₀)^s` satisfies
`(z−z₀)² u″ + (2α + F(z)) (z−z₀) u′ + (α(α−1) + α F(z) + G(z)) u = 0`, where
`F = ∑ fₛ (z−z₀)^s`, `G = ∑ gₛ (z−z₀)^s`. -/
theorem FrobeniusData.series_ode (F : FrobeniusData f g z₀ R fc gc) {α : ℂ} {a : ℕ → ℂ}
    (hα0 : indicial fc gc α = 0) (ha : HasRadiusGE a R) (ha0 : a 0 = 1)
    (hrec : ∀ m : ℕ, indicial fc gc (α + ((m + 1 : ℕ) : ℂ)) * a (m + 1) =
      -∑ r ∈ range (m + 1), ((α + r) * fc (m + 1 - r) + gc (m + 1 - r)) * a r)
    {z : ℂ} (hz : z ∈ ball z₀ R) :
    (z - z₀) ^ 2 * powerSeriesSum (shiftDeriv (shiftDeriv a)) z₀ z +
      (2 * α + powerSeriesSum fc z₀ z) * ((z - z₀) * powerSeriesSum (shiftDeriv a) z₀ z) +
      (α * (α - 1) + α * powerSeriesSum fc z₀ z + powerSeriesSum gc z₀ z) *
        powerSeriesSum a z₀ z = 0 := by
  -- the series for `u`, `(z − z₀) u′`, `(z − z₀)² u″`
  have hu : HasSum (fun n => a n * (z - z₀) ^ n) (powerSeriesSum a z₀ z) := (ha.summable hz).hasSum
  have hu₁ := ha.hasSum_natCast_mul hz
  have hu₂ := ha.hasSum_natCast_mul_sub_one hz
  -- summability of norms for the Cauchy products
  have hun : Summable fun n => ‖a n * (z - z₀) ^ n‖ := ha.summable_norm hz
  have hdn : Summable fun n : ℕ => ‖(n : ℂ) * a n * (z - z₀) ^ n‖ := by
    rw [← summable_nat_add_iff 1]
    refine ((ha.shift.summable_norm hz).mul_left ‖z - z₀‖).congr fun n => ?_
    simp only [shiftDeriv]
    rw [← norm_mul]
    congr 1
    push_cast
    ring
  have hbn : Summable fun n : ℕ => ‖((n : ℂ) + α) * a n * (z - z₀) ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hdn.add (hun.mul_left ‖α‖))
    calc ‖((n : ℂ) + α) * a n * (z - z₀) ^ n‖
        = ‖(n : ℂ) * a n * (z - z₀) ^ n + α * (a n * (z - z₀) ^ n)‖ := by congr 1; ring
      _ ≤ ‖(n : ℂ) * a n * (z - z₀) ^ n‖ + ‖α * (a n * (z - z₀) ^ n)‖ := norm_add_le _ _
      _ = ‖(n : ℂ) * a n * (z - z₀) ^ n‖ + ‖α‖ * ‖a n * (z - z₀) ^ n‖ := by
          rw [norm_mul α]
  have hb : HasSum (fun n : ℕ => ((n : ℂ) + α) * a n * (z - z₀) ^ n)
      ((z - z₀) * powerSeriesSum (shiftDeriv a) z₀ z + α * powerSeriesSum a z₀ z) := by
    convert hu₁.add (hu.mul_left α) using 1
    funext n
    ring
  have hF := hasSum_mul_powerSeriesSum (F.f_summable z hz) hbn
  rw [show powerSeriesSum (fun s : ℕ => ((s : ℂ) + α) * a s) z₀ z =
    (z - z₀) * powerSeriesSum (shiftDeriv a) z₀ z + α * powerSeriesSum a z₀ z from hb.tsum_eq]
    at hF
  have hG := hasSum_mul_powerSeriesSum (F.g_summable z hz) hun
  have hP : HasSum
      (fun n : ℕ => ((n : ℂ) * ((n : ℂ) - 1) + 2 * α * n + α * (α - 1)) * a n * (z - z₀) ^ n)
      ((z - z₀) ^ 2 * powerSeriesSum (shiftDeriv (shiftDeriv a)) z₀ z +
        2 * α * ((z - z₀) * powerSeriesSum (shiftDeriv a) z₀ z) +
        α * (α - 1) * powerSeriesSum a z₀ z) := by
    convert (hu₂.add (hu₁.mul_left (2 * α))).add (hu.mul_left (α * (α - 1))) using 1
    funext n
    ring
  have htot := (hP.add hF).add hG
  -- every coefficient vanishes
  have hzero : ∀ n : ℕ,
      ((n : ℂ) * ((n : ℂ) - 1) + 2 * α * n + α * (α - 1)) * a n * (z - z₀) ^ n +
        (∑ r ∈ range (n + 1), fc (n - r) * (((r : ℂ) + α) * a r)) * (z - z₀) ^ n +
        (∑ r ∈ range (n + 1), gc (n - r) * a r) * (z - z₀) ^ n = 0 := by
    intro n
    rcases n with _ | m
    · simp only [zero_add, range_one, sum_singleton, Nat.sub_zero, Nat.cast_zero, pow_zero,
        mul_one, ha0]
      unfold indicial at hα0
      linear_combination hα0
    · have hrec' := hrec m
      rw [sum_range_succ _ (m + 1), sum_range_succ _ (m + 1), Nat.sub_self]
      have hS : ∑ r ∈ range (m + 1), ((α + r) * fc (m + 1 - r) + gc (m + 1 - r)) * a r =
          ∑ r ∈ range (m + 1), fc (m + 1 - r) * (((r : ℂ) + α) * a r) +
            ∑ r ∈ range (m + 1), gc (m + 1 - r) * a r := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun r _ => by ring
      rw [hS] at hrec'
      have hQ : indicial fc gc (α + ((m + 1 : ℕ) : ℂ)) =
          (α + ((m + 1 : ℕ) : ℂ)) * (α + ((m + 1 : ℕ) : ℂ) - 1) + fc 0 * (α + ((m + 1 : ℕ) : ℂ)) +
            gc 0 := rfl
      rw [hQ] at hrec'
      push_cast at hrec' ⊢
      linear_combination (z - z₀) ^ (m + 1) * hrec'
  simp only [hzero] at htot
  have := hasSum_zero.unique htot
  linear_combination -this

/-- The power-series factor `u` of 2.7.4 satisfies
`(z−z₀)² u″ + (2α + F(z)) (z−z₀) u′ + (α(α−1) + α F(z) + G(z)) u = 0`; this is 2.7.5 read as a
power-series identity. -/
theorem FrobeniusData.frobU_ode (F : FrobeniusData f g z₀ R fc gc) {α : ℂ}
    (hα0 : indicial fc gc α = 0) (hα : ∀ s : ℕ, 1 ≤ s → indicial fc gc (α + s) ≠ 0) {z : ℂ}
    (hz : z ∈ ball z₀ R) :
    (z - z₀) ^ 2 * powerSeriesSum (shiftDeriv (shiftDeriv (frobCoeff fc gc α))) z₀ z +
      (2 * α + powerSeriesSum fc z₀ z) *
        ((z - z₀) * powerSeriesSum (shiftDeriv (frobCoeff fc gc α)) z₀ z) +
      (α * (α - 1) + α * powerSeriesSum fc z₀ z + powerSeriesSum gc z₀ z) *
        powerSeriesSum (frobCoeff fc gc α) z₀ z = 0 :=
  F.series_ode hα0 (F.hasRadiusGE_frobCoeff hα) (frobCoeff_zero fc gc α)
    (fun m => frobCoeff_succ fc gc α m (hα (m + 1) (by omega))) hz

/-- **DLMF 2.7.4**: for an index `α` with `Q(α) = 0` and `Q(α + s) ≠ 0` (`s ≥ 1`), the Frobenius
series `w(z) = (z − z₀)^α ∑ aₛ (z − z₀)^s` with the coefficients 2.7.5 solves 2.7.1 on the slit
ball `|z − z₀| < R`, `z − z₀ ∉ (−∞, 0]`. -/
theorem FrobeniusData.dlmf_2_7_4 (F : FrobeniusData f g z₀ R fc gc) {α : ℂ}
    (hα0 : indicial fc gc α = 0) (hα : ∀ s : ℕ, 1 ≤ s → indicial fc gc (α + s) ≠ 0) :
    IsODESolution (slitBall z₀ R) f g (frobSolution fc gc α z₀) := by
  have ha : HasRadiusGE (frobCoeff fc gc α) R := F.hasRadiusGE_frobCoeff hα
  refine isODESolution_of_hasDerivAt (isOpen_slitBall z₀ R) (w' := frobDeriv fc gc α z₀)
    fun z hz => ⟨hasDerivAt_frobSolution ha hz, ?_⟩
  obtain ⟨hzb, hzs⟩ := hz
  have hne : z - z₀ ≠ 0 := slitPlane_ne_zero hzs
  have hz₀ : z ≠ z₀ := sub_ne_zero.mp hne
  refine (hasDerivAt_frobDeriv ha ⟨hzb, hzs⟩).congr_deriv ?_
  have hE := F.frobU_ode hα0 hα hzb
  rw [F.f_eq z hzb hz₀, F.g_eq z hzb hz₀]
  have h1 : (z - z₀) ^ (α - 1) = (z - z₀) ^ α / (z - z₀) := by rw [cpow_sub _ _ hne, cpow_one]
  have h2 : (z - z₀) ^ (α - 1 - 1) = (z - z₀) ^ α / (z - z₀) ^ 2 := by
    rw [show α - 1 - 1 = α - 2 by ring, cpow_sub _ _ hne, cpow_two]
  simp only [frobDeriv, frobSolution_eq, h1, h2]
  unfold powerSeriesSum at hE ⊢
  linear_combination (norm := skip) ((z - z₀) ^ α / (z - z₀) ^ 2) * hE
  field_simp
  ring

/-! ### Linear independence when `α₁ − α₂ ∉ ℤ` -/

/-- Both indices qualify for 2.7.4 when `α₁ − α₂` is not an integer. -/
theorem indicial_add_ne_zero_of_sub_not_int {α₁ α₂ : ℂ}
    (hQ : ∀ α, indicial fc gc α = (α - α₁) * (α - α₂)) (hne : ∀ n : ℤ, α₁ - α₂ ≠ n) :
    ∀ s : ℕ, 1 ≤ s → indicial fc gc (α₁ + s) ≠ 0 := by
  rw [indicial_add_ne_zero_iff hQ]
  intro s _ h
  apply hne (-(s : ℤ))
  rw [h]
  push_cast
  ring

/-- **DLMF 2.7.4**, independence: when `α₁ − α₂` is not an integer the two Frobenius solutions
are linearly independent on the slit ball (their Wronskian is `(z−z₀)^{α₁+α₂−1} (α₂ − α₁ + O(z −
z₀)) ≠ 0` near `z₀`). -/
theorem FrobeniusData.dlmf_2_7_4_independent (F : FrobeniusData f g z₀ R fc gc) {α₁ α₂ : ℂ}
    (hQ : ∀ α, indicial fc gc α = (α - α₁) * (α - α₂)) (hne : ∀ n : ℤ, α₁ - α₂ ≠ n) (A B : ℂ)
    (hAB : ∀ z ∈ slitBall z₀ R,
      A * frobSolution fc gc α₁ z₀ z + B * frobSolution fc gc α₂ z₀ z = 0) :
    A = 0 ∧ B = 0 := by
  have hQ' : ∀ α, indicial fc gc α = (α - α₂) * (α - α₁) := fun α => by rw [hQ, mul_comm]
  have hne' : ∀ n : ℤ, α₂ - α₁ ≠ n := fun n h => hne (-n) (by rw [Int.cast_neg, ← h]; ring)
  have ha₁ : HasRadiusGE (frobCoeff fc gc α₁) R :=
    F.hasRadiusGE_frobCoeff (indicial_add_ne_zero_of_sub_not_int hQ hne)
  have ha₂ : HasRadiusGE (frobCoeff fc gc α₂) R :=
    F.hasRadiusGE_frobCoeff (indicial_add_ne_zero_of_sub_not_int hQ' hne')
  set a₁ := frobCoeff fc gc α₁ with ha₁_def
  set a₂ := frobCoeff fc gc α₂ with ha₂_def
  have hz₀ : z₀ ∈ ball z₀ R := mem_ball_self F.R_pos
  -- the reduced Wronskian `V`
  set V : ℂ → ℂ := fun z => (α₂ - α₁) * (powerSeriesSum a₁ z₀ z * powerSeriesSum a₂ z₀ z) +
    (z - z₀) * (powerSeriesSum a₁ z₀ z * powerSeriesSum (shiftDeriv a₂) z₀ z -
      powerSeriesSum a₂ z₀ z * powerSeriesSum (shiftDeriv a₁) z₀ z) with hV
  have hVc : ContinuousAt V z₀ :=
    (continuousAt_const.mul ((ha₁.continuousAt hz₀).mul (ha₂.continuousAt hz₀))).add
      ((continuousAt_id.sub continuousAt_const).mul
        (((ha₁.continuousAt hz₀).mul (ha₂.shift.continuousAt hz₀)).sub
          ((ha₂.continuousAt hz₀).mul (ha₁.shift.continuousAt hz₀))))
  have hV₀ : V z₀ ≠ 0 := by
    simp only [hV, powerSeriesSum_self, ha₁_def, ha₂_def, frobCoeff_zero, sub_self, zero_mul,
      add_zero, mul_one]
    intro h
    exact hne 0 (by rw [Int.cast_zero]; linear_combination -h)
  obtain ⟨ε, hε, hVne⟩ := Metric.eventually_nhds_iff.mp (hVc.eventually_ne hV₀)
  -- the test point `z = z₀ + x`, `x > 0` small
  set x : ℝ := min ε R / 2 with hx
  have hx0 : 0 < x := by have := F.R_pos; positivity
  have hxε : x < ε := by have := min_le_left ε R; linarith
  have hxR : x < R := by have := min_le_right ε R; linarith
  set z := z₀ + (x : ℂ) with hz
  have hzz₀ : z - z₀ = x := by rw [hz, add_sub_cancel_left]
  have hzb : z ∈ ball z₀ R := by
    rw [mem_ball, dist_eq_norm, hzz₀, norm_real, Real.norm_of_nonneg hx0.le]; exact hxR
  have hzs : z - z₀ ∈ slitPlane := by rw [hzz₀]; exact ofReal_mem_slitPlane.mpr hx0
  have hzS : z ∈ slitBall z₀ R := ⟨hzb, hzs⟩
  have hVz : V z ≠ 0 := by
    apply hVne
    rw [dist_eq_norm, hzz₀, norm_real, Real.norm_of_nonneg hx0.le]; exact hxε
  have hne0 : z - z₀ ≠ 0 := slitPlane_ne_zero hzs
  -- the combination and its derivative vanish at `z`
  have h1 := hAB z hzS
  have hd₁ := hasDerivAt_frobSolution ha₁ hzS
  have hd₂ := hasDerivAt_frobSolution ha₂ hzS
  have hcomb := (hd₁.const_mul A).add (hd₂.const_mul B)
  have hzero : HasDerivAt (fun z => A * frobSolution fc gc α₁ z₀ z + B * frobSolution fc gc α₂ z₀ z)
      0 z := by
    refine (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_slitBall z₀ R).mem_nhds hzS] with y hy using hAB y hy
  have h2 := hcomb.unique hzero
  -- the Wronskian
  have hT₁ : (z - z₀) ^ (α₁ - 1) = (z - z₀) ^ α₁ / (z - z₀) := by rw [cpow_sub _ _ hne0, cpow_one]
  have hT₂ : (z - z₀) ^ (α₂ - 1) = (z - z₀) ^ α₂ / (z - z₀) := by rw [cpow_sub _ _ hne0, cpow_one]
  have hW : frobSolution fc gc α₁ z₀ z * frobDeriv fc gc α₂ z₀ z -
      frobSolution fc gc α₂ z₀ z * frobDeriv fc gc α₁ z₀ z =
        (z - z₀) ^ α₁ * (z - z₀) ^ α₂ / (z - z₀) * V z := by
    simp only [frobSolution_eq, frobDeriv, hT₁, hT₂, hV]
    field_simp
    ring
  have hWne : (z - z₀) ^ α₁ * (z - z₀) ^ α₂ / (z - z₀) * V z ≠ 0 := by
    have h₁ : (z - z₀) ^ α₁ ≠ 0 := fun h => hne0 ((cpow_eq_zero_iff _ _).mp h).1
    have h₂ : (z - z₀) ^ α₂ ≠ 0 := fun h => hne0 ((cpow_eq_zero_iff _ _).mp h).1
    exact mul_ne_zero (div_ne_zero (mul_ne_zero h₁ h₂) hne0) hVz
  rw [← hW] at hWne
  constructor
  · have : A * (frobSolution fc gc α₁ z₀ z * frobDeriv fc gc α₂ z₀ z -
        frobSolution fc gc α₂ z₀ z * frobDeriv fc gc α₁ z₀ z) = 0 := by
      linear_combination frobDeriv fc gc α₂ z₀ z * h1 - frobSolution fc gc α₂ z₀ z * h2
    exact (mul_eq_zero.mp this).resolve_right hWne
  · have : B * (frobSolution fc gc α₁ z₀ z * frobDeriv fc gc α₂ z₀ z -
        frobSolution fc gc α₂ z₀ z * frobDeriv fc gc α₁ z₀ z) = 0 := by
      linear_combination frobSolution fc gc α₁ z₀ z * h2 - frobDeriv fc gc α₁ z₀ z * h1
    exact (mul_eq_zero.mp this).resolve_right hWne

/-- **DLMF 2.7.4** in full: if the indices `α₁, α₂` (2.7.3) satisfy `α₁ − α₂ ∉ ℤ`, both Frobenius
series `w_j = (z − z₀)^{α_j} ∑ a_{s,j} (z − z₀)^s` solve 2.7.1 on the slit ball and are linearly
independent there. -/
theorem FrobeniusData.dlmf_2_7_4_pair (F : FrobeniusData f g z₀ R fc gc) {α₁ α₂ : ℂ}
    (hQ : ∀ α, indicial fc gc α = (α - α₁) * (α - α₂)) (hne : ∀ n : ℤ, α₁ - α₂ ≠ n) :
    IsODESolution (slitBall z₀ R) f g (frobSolution fc gc α₁ z₀) ∧
      IsODESolution (slitBall z₀ R) f g (frobSolution fc gc α₂ z₀) ∧
      ∀ A B : ℂ, (∀ z ∈ slitBall z₀ R,
        A * frobSolution fc gc α₁ z₀ z + B * frobSolution fc gc α₂ z₀ z = 0) → A = 0 ∧ B = 0 := by
  have hQ' : ∀ α, indicial fc gc α = (α - α₂) * (α - α₁) := fun α => by rw [hQ, mul_comm]
  have hne' : ∀ n : ℤ, α₂ - α₁ ≠ n := fun n h => hne (-n) (by rw [Int.cast_neg, ← h]; ring)
  refine ⟨F.dlmf_2_7_4 ?_ (indicial_add_ne_zero_of_sub_not_int hQ hne),
    F.dlmf_2_7_4 ?_ (indicial_add_ne_zero_of_sub_not_int hQ' hne'),
    fun A B hAB => F.dlmf_2_7_4_independent hQ hne A B hAB⟩
  · rw [hQ, sub_self, zero_mul]
  · rw [hQ', sub_self, zero_mul]

end Azurite.DLMF
