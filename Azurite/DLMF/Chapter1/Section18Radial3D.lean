/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18Radial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv

/-!
# DLMF (1.18.67): the radial reduction of the three-dimensional Schrödinger operator

https://dlmf.nist.gov/1.18.viii

DLMF says the operators (1.18.67) "appear in the quantum theory of binding or scattering of a
particle in a spherically symmetric potential `V(r)` in three dimensions". This file proves the
reduction. The Laplacian is `laplacianXYZ`, the sum of second derivatives along the coordinate
lines. For `r = √(x² + y² + z²) > 0`:

* `laplacianXYZ_radial`: `Δ(g(r)(x + iy)^ℓ) = (g″ + 2(ℓ + 1)g′/r)(x + iy)^ℓ`, by the chain and
  product rules along each line (`deriv_deriv_line`), Euler's identity `x∂ₓP + y∂_yP = ℓP`, and
  harmonicity of `P = (x + iy)^ℓ`.
* `dlmf_1_18_67`: for `ψ = (u(r)/r^{ℓ+1})(x + iy)^ℓ`,
  `−½Δψ + V(r)ψ = ((ℒ_ℓ u)(r)/r^{ℓ+1})(x + iy)^ℓ`.
* `dlmf_1_18_67_eigen`: eigenfunctions of `ℒ_ℓ` give eigenfunctions of `−½Δ + V(r)`.

`(x + iy)^ℓ` is `r^ℓ` times the spherical harmonic `Y_ℓ^ℓ` up to a constant. Other `Y_ℓ^m` are
not treated.
-/

open Set Filter Topology Complex

namespace Azurite.DLMF

/-- The Laplacian `∂²/∂x² + ∂²/∂y² + ∂²/∂z²` of a function of three real variables. -/
noncomputable def laplacianXYZ (F : ℝ → ℝ → ℝ → ℂ) (x y z : ℝ) : ℂ :=
  deriv (deriv fun t => F t y z) x + deriv (deriv fun t => F x t z) y +
    deriv (deriv fun t => F x y t) z

/-- The second derivative of `g(ρ(t)) P(t)` along a line, where `ρ′ = t/ρ`. -/
theorem deriv_deriv_line {g g1 g2 ρ : ℝ → ℝ} {P P1 P2 : ℝ → ℂ} {s : ℝ}
    (hρ : ∀ᶠ t in 𝓝 s, 0 < ρ t ∧ HasDerivAt ρ (t / ρ t) t)
    (hg : ∀ r > 0, HasDerivAt g (g1 r) r) (hg1 : ∀ r > 0, HasDerivAt g1 (g2 r) r)
    (hP : ∀ t, HasDerivAt P (P1 t) t) (hP1 : ∀ t, HasDerivAt P1 (P2 t) t) :
    deriv (deriv fun t => (g (ρ t) : ℂ) * P t) s =
      ((g2 (ρ s) * (s / ρ s) ^ 2 + g1 (ρ s) * (1 / ρ s - s ^ 2 / ρ s ^ 3) : ℝ) : ℂ) * P s +
        2 * ((g1 (ρ s) * (s / ρ s) : ℝ) : ℂ) * P1 s + (g (ρ s) : ℂ) * P2 s := by
  have hf : ∀ t, 0 < ρ t → HasDerivAt ρ (t / ρ t) t →
      HasDerivAt (fun t => (g (ρ t) : ℂ) * P t)
        (((g1 (ρ t) * (t / ρ t) : ℝ) : ℂ) * P t + (g (ρ t) : ℂ) * P1 t) t := fun t h0 h1 =>
    (((hg _ h0).comp t h1).ofReal_comp.mul (hP t)).congr_deriv (by simp)
  have heq : deriv (fun t => (g (ρ t) : ℂ) * P t) =ᶠ[𝓝 s]
      fun t => ((g1 (ρ t) * (t / ρ t) : ℝ) : ℂ) * P t + (g (ρ t) : ℂ) * P1 t :=
    hρ.mono fun t ht => (hf t ht.1 ht.2).deriv
  rw [heq.deriv_eq]
  obtain ⟨hρ0, hρd⟩ := hρ.self_of_nhds
  have h := (((((hg1 _ hρ0).comp s hρd).mul ((hasDerivAt_id s).div hρd hρ0.ne')).ofReal_comp.mul
    (hP s)).add (((hg _ hρ0).comp s hρd).ofReal_comp.mul (hP1 s)))
  refine (h.congr_deriv ?_).deriv
  simp only [Function.comp, id, Pi.mul_apply, Pi.div_apply]
  push_cast
  have : (ρ s : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  field_simp
  ring

theorem hasDerivAt_sqrt_sq_add {c t : ℝ} (h : 0 < t ^ 2 + c) :
    HasDerivAt (fun t => √(t ^ 2 + c)) (t / √(t ^ 2 + c)) t := by
  have h1 := (((hasDerivAt_id t).pow 2).add_const c).sqrt h.ne'
  refine h1.congr_deriv ?_
  have : √(t ^ 2 + c) ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  simp only [id, Pi.pow_apply]
  push_cast
  field_simp

theorem eventually_sqrt_sq_add {c s : ℝ} (h : 0 < s ^ 2 + c) :
    ∀ᶠ t in 𝓝 s, 0 < √(t ^ 2 + c) ∧ HasDerivAt (fun t => √(t ^ 2 + c)) (t / √(t ^ 2 + c)) t := by
  have hev : ∀ᶠ t in 𝓝 s, 0 < t ^ 2 + c :=
    (continuous_id.pow 2 |>.add continuous_const).continuousAt.eventually (lt_mem_nhds h)
  exact hev.mono fun t ht => ⟨Real.sqrt_pos.mpr ht, hasDerivAt_sqrt_sq_add ht⟩

/-- `Δ(g(r) (x + iy)^ℓ) = (g″ + 2(ℓ + 1)g′/r) (x + iy)^ℓ` away from the origin. -/
theorem laplacianXYZ_radial (ℓ : ℕ) {g g1 g2 : ℝ → ℝ} (hg : ∀ r > 0, HasDerivAt g (g1 r) r)
    (hg1 : ∀ r > 0, HasDerivAt g1 (g2 r) r) {x y z : ℝ} (h0 : 0 < x ^ 2 + y ^ 2 + z ^ 2) :
    laplacianXYZ (fun x y z => (g √(x ^ 2 + y ^ 2 + z ^ 2) : ℂ) * ((x : ℂ) + I * y) ^ ℓ) x y z =
      ((g2 √(x ^ 2 + y ^ 2 + z ^ 2) +
        2 * (ℓ + 1) * g1 √(x ^ 2 + y ^ 2 + z ^ 2) / √(x ^ 2 + y ^ 2 + z ^ 2) : ℝ) : ℂ) *
        ((x : ℂ) + I * y) ^ ℓ := by
  set ρ := √(x ^ 2 + y ^ 2 + z ^ 2)
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr h0
  have hρ2 : ρ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := Real.sq_sqrt h0.le
  -- the `x` line
  have ex : ∀ t, t ^ 2 + y ^ 2 + z ^ 2 = t ^ 2 + (y ^ 2 + z ^ 2) := fun t => by ring
  have hx : deriv (deriv fun t => (g √(t ^ 2 + y ^ 2 + z ^ 2) : ℂ) * ((t : ℂ) + I * y) ^ ℓ) x =
      ((g2 ρ * (x / ρ) ^ 2 + g1 ρ * (1 / ρ - x ^ 2 / ρ ^ 3) : ℝ) : ℂ) * ((x : ℂ) + I * y) ^ ℓ +
        2 * ((g1 ρ * (x / ρ) : ℝ) : ℂ) * ((ℓ : ℂ) * ((x : ℂ) + I * y) ^ (ℓ - 1)) +
        (g ρ : ℂ) * ((ℓ : ℂ) * ((ℓ - 1 : ℕ) : ℂ) * ((x : ℂ) + I * y) ^ (ℓ - 1 - 1)) := by
    simp_rw [ex]
    refine deriv_deriv_line (P1 := fun t => (ℓ : ℂ) * ((t : ℂ) + I * y) ^ (ℓ - 1))
      (P2 := fun t => (ℓ : ℂ) * ((ℓ - 1 : ℕ) : ℂ) * ((t : ℂ) + I * y) ^ (ℓ - 1 - 1))
      (eventually_sqrt_sq_add (by rw [← ex]; exact h0)) hg hg1 (fun t => ?_) (fun t => ?_)
      |>.trans ?_
    · exact (((hasDerivAt_id (t : ℂ)).comp_ofReal).add_const _).pow ℓ |>.congr_deriv (by simp)
    · exact ((((hasDerivAt_id (t : ℂ)).comp_ofReal).add_const _).pow (ℓ - 1)).const_mul _
        |>.congr_deriv (by simp [mul_assoc])
    · simp only [ρ, ex]
  -- the `y` line
  have ey : ∀ t, x ^ 2 + t ^ 2 + z ^ 2 = t ^ 2 + (x ^ 2 + z ^ 2) := fun t => by ring
  have hy : deriv (deriv fun t => (g √(x ^ 2 + t ^ 2 + z ^ 2) : ℂ) * ((x : ℂ) + I * t) ^ ℓ) y =
      ((g2 ρ * (y / ρ) ^ 2 + g1 ρ * (1 / ρ - y ^ 2 / ρ ^ 3) : ℝ) : ℂ) * ((x : ℂ) + I * y) ^ ℓ +
        2 * ((g1 ρ * (y / ρ) : ℝ) : ℂ) * ((ℓ : ℂ) * ((x : ℂ) + I * y) ^ (ℓ - 1) * I) +
        (g ρ : ℂ) * ((ℓ : ℂ) * ((ℓ - 1 : ℕ) : ℂ) * ((x : ℂ) + I * y) ^ (ℓ - 1 - 1) * I * I) := by
    simp_rw [ey]
    refine deriv_deriv_line (P1 := fun t => (ℓ : ℂ) * ((x : ℂ) + I * t) ^ (ℓ - 1) * I)
      (P2 := fun t => (ℓ : ℂ) * ((ℓ - 1 : ℕ) : ℂ) * ((x : ℂ) + I * t) ^ (ℓ - 1 - 1) * I * I)
      (eventually_sqrt_sq_add (by rw [← ey]; exact h0)) hg hg1 (fun t => ?_) (fun t => ?_)
      |>.trans ?_
    · exact ((((hasDerivAt_id (t : ℂ)).comp_ofReal).const_mul I).const_add _).pow ℓ
        |>.congr_deriv (by simp)
    · exact (((((hasDerivAt_id (t : ℂ)).comp_ofReal).const_mul I).const_add _).pow
        (ℓ - 1)).const_mul (ℓ : ℂ) |>.mul_const I |>.congr_deriv (by simp; ring)
    · simp only [ρ, ey]
  -- the `z` line
  have ez : ∀ t, x ^ 2 + y ^ 2 + t ^ 2 = t ^ 2 + (x ^ 2 + y ^ 2) := fun t => by ring
  have hz : deriv (deriv fun t => (g √(x ^ 2 + y ^ 2 + t ^ 2) : ℂ) * ((x : ℂ) + I * y) ^ ℓ) z =
      ((g2 ρ * (z / ρ) ^ 2 + g1 ρ * (1 / ρ - z ^ 2 / ρ ^ 3) : ℝ) : ℂ) * ((x : ℂ) + I * y) ^ ℓ +
        2 * ((g1 ρ * (z / ρ) : ℝ) : ℂ) * 0 + (g ρ : ℂ) * 0 := by
    simp_rw [ez]
    refine deriv_deriv_line (eventually_sqrt_sq_add (by rw [← ez]; exact h0)) hg hg1
      (fun t => hasDerivAt_const t _) (fun t => hasDerivAt_const t _) |>.trans ?_
    simp only [ρ, ez]
  simp only [laplacianXYZ]
  rw [hx, hy, hz]
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have hρ2c : (ρ : ℂ) ^ 2 = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 + (z : ℂ) ^ 2 := by exact_mod_cast hρ2
  have e1 : g2 ρ * (x / ρ) ^ 2 + g1 ρ * (1 / ρ - x ^ 2 / ρ ^ 3) +
      (g2 ρ * (y / ρ) ^ 2 + g1 ρ * (1 / ρ - y ^ 2 / ρ ^ 3)) +
      (g2 ρ * (z / ρ) ^ 2 + g1 ρ * (1 / ρ - z ^ 2 / ρ ^ 3)) = g2 ρ + 2 * g1 ρ / ρ := by
    field_simp
    linear_combination (g1 ρ - g2 ρ * ρ) * hρ2
  have hA : (((g2 ρ * (x / ρ) ^ 2 + g1 ρ * (1 / ρ - x ^ 2 / ρ ^ 3) : ℝ) : ℂ) +
      ((g2 ρ * (y / ρ) ^ 2 + g1 ρ * (1 / ρ - y ^ 2 / ρ ^ 3) : ℝ) : ℂ) +
      ((g2 ρ * (z / ρ) ^ 2 + g1 ρ * (1 / ρ - z ^ 2 / ρ ^ 3) : ℝ) : ℂ)) =
      ((g2 ρ + 2 * g1 ρ / ρ : ℝ) : ℂ) := by
    rw [← e1]; push_cast; ring
  rcases ℓ with _ | ℓ
  · simp only [CharP.cast_eq_zero, zero_mul, mul_zero, add_zero, pow_zero, mul_one]
    rw [hA]
    push_cast
    ring
  · simp only [Nat.add_sub_cancel]
    have hI : I * I = -1 := I_mul_I
    push_cast at hA ⊢
    linear_combination ((x : ℂ) + I * y) ^ (ℓ + 1) * hA +
      (g ρ : ℂ) * ((ℓ : ℂ) + 1) * (ℓ : ℂ) * ((x : ℂ) + I * y) ^ (ℓ - 1) * hI

section Reduction

variable {u : ℝ → ℝ} (hd : ∀ r > 0, HasDerivAt u (deriv u r) r)
  (hdd : ∀ r > 0, HasDerivAt (deriv u) (deriv (deriv u) r) r)

include hd in
theorem hasDerivAt_div_pow (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => u r / r ^ (ℓ + 1))
      (deriv u r / r ^ (ℓ + 1) - (ℓ + 1) * u r / r ^ (ℓ + 2)) r := by
  have hr0 : r ≠ 0 := hr.ne'
  refine ((hd r hr).div (hasDerivAt_pow (ℓ + 1) r) (pow_ne_zero _ hr0)).congr_deriv ?_
  field_simp
  push_cast
  ring

include hd hdd in
theorem hasDerivAt_div_pow_deriv (ℓ : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => deriv u r / r ^ (ℓ + 1) - (ℓ + 1) * u r / r ^ (ℓ + 2))
      (deriv (deriv u) r / r ^ (ℓ + 1) - 2 * (ℓ + 1) * deriv u r / r ^ (ℓ + 2) +
        (ℓ + 1) * (ℓ + 2) * u r / r ^ (ℓ + 3)) r := by
  have hr0 : r ≠ 0 := hr.ne'
  refine (((hdd r hr).div (hasDerivAt_pow (ℓ + 1) r) (pow_ne_zero _ hr0)).sub
    (((hd r hr).const_mul ((ℓ : ℝ) + 1)).div (hasDerivAt_pow (ℓ + 2) r)
      (pow_ne_zero _ hr0))).congr_deriv ?_
  field_simp
  push_cast
  ring

include hd hdd in
/-- **DLMF (1.18.67)**: the three-dimensional Schrödinger operator `−½Δ + V(r)` acting on
`ψ = (u(r)/r^{ℓ+1}) (x + iy)^ℓ`, `r = √(x² + y² + z²) > 0`, is `ℒ_ℓ u` in the same form:
`−½Δψ + Vψ = ((ℒ_ℓ u)(r)/r^{ℓ+1}) (x + iy)^ℓ`. (`(x + iy)^ℓ` is a harmonic polynomial of
degree `ℓ`, i.e. `r^ℓ` times a spherical harmonic of angular momentum `ℓ`.) -/
theorem dlmf_1_18_67 (ℓ : ℕ) (V : ℝ → ℝ) {x y z : ℝ} (h0 : 0 < x ^ 2 + y ^ 2 + z ^ 2) :
    -(1 / 2) * laplacianXYZ (fun x y z => ((u √(x ^ 2 + y ^ 2 + z ^ 2) /
        √(x ^ 2 + y ^ 2 + z ^ 2) ^ (ℓ + 1) : ℝ) : ℂ) * ((x : ℂ) + I * y) ^ ℓ) x y z +
      (V √(x ^ 2 + y ^ 2 + z ^ 2) : ℂ) * (((u √(x ^ 2 + y ^ 2 + z ^ 2) /
        √(x ^ 2 + y ^ 2 + z ^ 2) ^ (ℓ + 1) : ℝ) : ℂ) * ((x : ℂ) + I * y) ^ ℓ) =
      ((radialOp ℓ V u √(x ^ 2 + y ^ 2 + z ^ 2) / √(x ^ 2 + y ^ 2 + z ^ 2) ^ (ℓ + 1) : ℝ) : ℂ) *
        ((x : ℂ) + I * y) ^ ℓ := by
  have h := laplacianXYZ_radial ℓ (g := fun r => u r / r ^ (ℓ + 1))
    (fun r hr => hasDerivAt_div_pow hd ℓ hr)
    (fun r hr => hasDerivAt_div_pow_deriv hd hdd ℓ hr) h0
  rw [h]
  set ρ := √(x ^ 2 + y ^ 2 + z ^ 2)
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr h0
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  simp only [radialOp]
  push_cast
  field_simp
  ring

include hd hdd in
/-- An eigenfunction of `ℒ_ℓ` gives an eigenfunction of the three-dimensional operator
`−½Δ + V(r)` with the same eigenvalue. -/
theorem dlmf_1_18_67_eigen (ℓ : ℕ) {V : ℝ → ℝ} {E : ℝ}
    (heig : ∀ r > 0, radialOp ℓ V u r = E * u r) {x y z : ℝ} (h0 : 0 < x ^ 2 + y ^ 2 + z ^ 2) :
    -(1 / 2) * laplacianXYZ (fun x y z => ((u √(x ^ 2 + y ^ 2 + z ^ 2) /
        √(x ^ 2 + y ^ 2 + z ^ 2) ^ (ℓ + 1) : ℝ) : ℂ) * ((x : ℂ) + I * y) ^ ℓ) x y z +
      (V √(x ^ 2 + y ^ 2 + z ^ 2) : ℂ) * (((u √(x ^ 2 + y ^ 2 + z ^ 2) /
        √(x ^ 2 + y ^ 2 + z ^ 2) ^ (ℓ + 1) : ℝ) : ℂ) * ((x : ℂ) + I * y) ^ ℓ) =
      E * (((u √(x ^ 2 + y ^ 2 + z ^ 2) / √(x ^ 2 + y ^ 2 + z ^ 2) ^ (ℓ + 1) : ℝ) : ℂ) *
        ((x : ℂ) + I * y) ^ ℓ) := by
  rw [dlmf_1_18_67 hd hdd ℓ V h0, heig _ (Real.sqrt_pos.mpr h0)]
  push_cast
  ring

end Reduction

end Azurite.DLMF
