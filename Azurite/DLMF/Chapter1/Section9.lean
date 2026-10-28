/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.DerivedSet

/-!
# DLMF §1.9: Calculus of a Complex Variable

Formalizations of <https://dlmf.nist.gov/1.9>, one theorem per equation, named `dlmf_1_9_N`.
Complex numbers are Mathlib's `ℂ`; the principal phase `ph z` is `Complex.arg`.
Statements made in the prose are named `dlmf_1_9_ii_<topic>`.

## §1.9(i) Complex Numbers

* 1.9.1–1.9.4: `z = x + iy` with `i² = −1`, real and imaginary parts, polar form
  `x = r cos θ`, `y = r sin θ`, `r = (x² + y²)^{1/2}`.
* 1.9.5–1.9.6: the principal phase by quadrant, `θ = ω, π − ω, −π + ω, −ω` with
  `ω = arctan|y/x| ∈ [0, π/2]` (`dlmf_1_9_5_first`, …, `dlmf_1_9_5_fourth`).
  - The first and second quadrants include the positive and negative real axis.
  - The imaginary axis is excluded, since `|y/x|` is undefined there.
  - Proof: `arg z = arctan(y/x)` for `ℜz > 0` (`arg_eq_arctan_of_re_pos`), and
    `arcsin(b/(a² + b²)^{1/2}) = arctan(b/a)` (`arcsin_div_sqrt_eq_arctan`).
* 1.9.7: phases of `z ≠ 0` as a predicate, `IsPhase z θ : z = |z|e^{iθ}`; the phases are
  `ph z + 2nπ` (`dlmf_1_9_7`).
  - Range and uniqueness of the principal value: `dlmf_1_9_7_principal_range`,
    `dlmf_1_9_7_principal_unique`.  Mathlib's `arg` takes the value `π` on `(−∞, 0)`, DLMF's
    single-valued convention `−π < ph z ≤ π`.
  - Continuity off `(−∞, 0]`, and the jump on `(−∞, 0)`: `dlmf_1_9_7_continuousAt`,
    `dlmf_1_9_7_negative_axis`.
* 1.9.8–1.9.17, 1.9.19, 1.9.23: bounds, exponential form, conjugate, arithmetic, moduli, triangle
  inequality.
* 1.9.13, 1.9.18, 1.9.20: the phase rules hold for general phases (`IsPhase`).  For principal
  values they hold up to `2nπ`: `dlmf_1_9_13_principal` (off the negative real axis),
  `dlmf_1_9_18_principal`, `dlmf_1_9_20_principal`.  They can fail exactly:
  `dlmf_1_9_18_principal_counterexample`, `dlmf_1_9_20_principal_counterexample`.
* 1.9.21: real part over even `k`, imaginary part over odd `k`, sign `(−1)^⌊k/2⌋`
  (`re_I_pow`, `im_I_pow`).
* 1.9.22: De Moivre's theorem for `n ∈ ℤ`.

## §1.9(ii) Continuity, Point Sets, and Differentiation

* Continuity in ε–δ form, for one and two variables and relative to a region.
* Point sets:
  - open sets through disks, and limit points (`IsLimitPoint`, equivalent to `AccPt`);
  - every disk about a limit point holds infinitely many points of `S`;
  - the closure is `S` together with its limit points.
* Domains: an open set is connected iff any two points are joined by a polygonal arc
  (`PolygonallyJoined`, a finite chain of segments in the set) (`dlmf_1_9_ii_domain`).
* Boundary points through disks; the closed domain; regions (`IsRegion`), whose non-boundary points
  form the open domain.
* 1.9.24 `dlmf_1_9_24` (limit form of `f′`); differentiability implies continuity.
* 1.9.25 `dlmf_1_9_25` (Cauchy–Riemann, from `hasDerivAt_partials`).
  - The converse `dlmf_1_9_25_converse`: continuous partials satisfying (1.9.25) give complex
    differentiability.
  - Proof: a mean value estimate along horizontal segments plus the vertical derivative at the
    point.  Only `∂u/∂x`, `∂v/∂x` need to be continuous.
* Analyticity: `dlmf_1_9_ii_analyticAt` (differentiable near `z₀` ⇔ `AnalyticAt`),
  `dlmf_1_9_ii_entire`, `dlmf_1_9_ii_iterate_deriv` (all derivatives analytic).
* 1.9.26 `dlmf_1_9_26` and 1.9.27 `dlmf_1_9_27`: `u`, `v` are harmonic, in Cartesian and polar
  coordinates.  The second derivatives come from the chain rule for `f`, `f′`.
  `v = ℜ(−if)` reduces `v` to `u`.
-/

namespace Azurite.DLMF

open Complex Set Filter Topology
open scoped ComplexConjugate

/-! ### §1.9(i) Complex numbers -/

/-- **DLMF 1.9.1**: every complex number is `z = x + iy` with `x, y` real, where `i² = −1`. -/
theorem dlmf_1_9_1 (z : ℂ) : z = z.re + z.im * I ∧ I ^ 2 = -1 :=
  ⟨(re_add_im z).symm, I_sq⟩

/-- **DLMF 1.9.2**: `ℜz = x`, `ℑz = y`. -/
theorem dlmf_1_9_2 (x y : ℝ) : (x + y * I).re = x ∧ (x + y * I).im = y := by simp

/-- **DLMF 1.9.3**: `x = r cos θ`, `y = r sin θ` (with `r = |z|`, `θ = ph z`). -/
theorem dlmf_1_9_3 (z : ℂ) : z.re = ‖z‖ * Real.cos (arg z) ∧ z.im = ‖z‖ * Real.sin (arg z) :=
  ⟨(norm_mul_cos_arg z).symm, (norm_mul_sin_arg z).symm⟩

/-- **DLMF 1.9.4**: `r = (x² + y²)^{1/2}`. -/
theorem dlmf_1_9_4 (x y : ℝ) : ‖(x + y * I : ℂ)‖ = √(x ^ 2 + y ^ 2) := norm_add_mul_I x y

/-- `ph z = arctan(y/x)` in the right half-plane. -/
theorem arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) : arg z = Real.arctan (z.im / z.re) := by
  have h := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [abs_lt] at h
  rw [← tan_arg, Real.arctan_tan h.1 h.2]

/-- `arcsin(b / (a² + b²)^{1/2}) = arctan(b/a)` for `a > 0`. -/
theorem arcsin_div_sqrt_eq_arctan {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.arcsin (b / √(a ^ 2 + b ^ 2)) = Real.arctan (b / a) := by
  have h1 := arg_of_re_nonneg (x := (a + b * I : ℂ)) (by simp [ha.le])
  have h2 := arg_eq_arctan_of_re_pos (z := (a + b * I : ℂ)) (by simp [ha])
  rw [h1, norm_add_mul_I] at h2
  simpa using h2

/-- **DLMF 1.9.6**: `ω = arctan|y/x| ∈ [0, π/2]`. -/
theorem dlmf_1_9_6 (x y : ℝ) : Real.arctan |y / x| ∈ Icc 0 (Real.pi / 2) :=
  ⟨Real.arctan_nonneg.mpr (abs_nonneg _), (Real.arctan_lt_pi_div_two _).le⟩

/-- **DLMF 1.9.5**, first quadrant (with the positive real axis): `θ = ω`. -/
theorem dlmf_1_9_5_first {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    arg (x + y * I) = Real.arctan |y / x| := by
  rw [arg_eq_arctan_of_re_pos (by simp [hx]), abs_of_nonneg (div_nonneg hy hx.le)]
  simp

/-- **DLMF 1.9.5**, second quadrant (with the negative real axis): `θ = π − ω`. -/
theorem dlmf_1_9_5_second {x y : ℝ} (hx : x < 0) (hy : 0 ≤ y) :
    arg (x + y * I) = Real.pi - Real.arctan |y / x| := by
  have h := arcsin_div_sqrt_eq_arctan (neg_pos.mpr hx) y
  rw [neg_sq] at h
  have habs : |y / x| = y / -x := by
    rw [abs_of_nonpos (div_nonpos_of_nonneg_of_nonpos hy hx.le), div_neg]
  have him : (-((x : ℂ) + y * I)).im = -y := by simp
  rw [arg_of_re_neg_of_im_nonneg (by simp [hx]) (by simp [hy]), norm_add_mul_I, habs, ← h, him,
    neg_div, Real.arcsin_neg]
  ring

/-- **DLMF 1.9.5**, third quadrant: `θ = −π + ω`. -/
theorem dlmf_1_9_5_third {x y : ℝ} (hx : x < 0) (hy : y < 0) :
    arg (x + y * I) = -Real.pi + Real.arctan |y / x| := by
  have h := arcsin_div_sqrt_eq_arctan (neg_pos.mpr hx) (-y)
  rw [neg_sq, neg_sq, neg_div_neg_eq] at h
  have him : (-((x : ℂ) + y * I)).im = -y := by simp
  rw [arg_of_re_neg_of_im_neg (by simp [hx]) (by simp [hy]), norm_add_mul_I,
    abs_of_pos (div_pos_of_neg_of_neg hy hx), him, h]
  ring

/-- **DLMF 1.9.5**, fourth quadrant: `θ = −ω`. -/
theorem dlmf_1_9_5_fourth {x y : ℝ} (hx : 0 < x) (hy : y < 0) :
    arg (x + y * I) = -Real.arctan |y / x| := by
  rw [arg_eq_arctan_of_re_pos (by simp [hx]), abs_of_neg (div_neg_of_neg_of_pos hy hx),
    Real.arctan_neg, neg_neg]
  simp

/-- `θ` is a phase of `z ≠ 0`: `z = |z| e^{iθ}`. -/
def IsPhase (z : ℂ) (θ : ℝ) : Prop := z ≠ 0 ∧ z = ‖z‖ * exp (θ * I)

/-- **DLMF 1.9.7**: the phases of `z ≠ 0` are `θ + 2nπ`, `n ∈ ℤ`, with `θ` the principal value. -/
theorem dlmf_1_9_7 {z : ℂ} (hz : z ≠ 0) (θ : ℝ) :
    IsPhase z θ ↔ ∃ n : ℤ, θ = arg z + 2 * n * Real.pi := by
  have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  constructor
  · rintro ⟨-, h⟩
    have h2 : exp (θ * I) = exp (arg z * I) := by
      apply mul_left_cancel₀ hr
      rw [← h, norm_mul_exp_arg_mul_I]
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp h2
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  · rintro ⟨n, rfl⟩
    refine ⟨hz, ?_⟩
    rw [show ((arg z + 2 * n * Real.pi : ℝ) : ℂ) * I = arg z * I + n * (2 * Real.pi * I) by
      push_cast; ring, exp_add, exp_int_mul_two_pi_mul_I, mul_one, norm_mul_exp_arg_mul_I]

/-- **DLMF 1.9.7**: `|z| = r`, and the principal phase is a phase. -/
theorem dlmf_1_9_7_principal_isPhase {z : ℂ} (hz : z ≠ 0) : IsPhase z (arg z) :=
  (dlmf_1_9_7 hz _).mpr ⟨0, by simp⟩

/-- **DLMF §1.9(i)**: the principal value satisfies `−π < ph z ≤ π`. -/
theorem dlmf_1_9_7_principal_range (z : ℂ) : -Real.pi < arg z ∧ arg z ≤ Real.pi :=
  ⟨neg_pi_lt_arg z, arg_le_pi z⟩

/-- **DLMF §1.9(i)**: the principal value is the only phase in `(−π, π]`. -/
theorem dlmf_1_9_7_principal_unique {z : ℂ} {θ : ℝ} (h : IsPhase z θ)
    (hθ : θ ∈ Ioc (-Real.pi) Real.pi) : θ = arg z := by
  obtain ⟨n, hn⟩ := (dlmf_1_9_7 h.1 θ).mp h
  have h1 := neg_pi_lt_arg z
  have h2 := arg_le_pi z
  have hn0 : n = 0 := by
    have hlt : (n : ℝ) < 1 := by nlinarith [Real.pi_pos, hθ.1, hθ.2]
    have hgt : (-1 : ℝ) < n := by nlinarith [Real.pi_pos, hθ.1, hθ.2]
    have : n < 1 := by exact_mod_cast hlt
    have : -1 < n := by exact_mod_cast hgt
    omega
  rw [hn, hn0]
  simp

/-- **DLMF §1.9(i)**: the principal phase is continuous off `(−∞, 0]`. -/
theorem dlmf_1_9_7_continuousAt {z : ℂ} (hz : z ∈ slitPlane) : ContinuousAt arg z :=
  continuousAt_arg hz

/-- **DLMF §1.9(i)**: on `(−∞, 0)` the principal phase is `π`, but its limit from the lower
half-plane is `−π`, so it is discontinuous there (two-valued). -/
theorem dlmf_1_9_7_negative_axis {x : ℝ} (hx : x < 0) :
    arg x = Real.pi ∧ Tendsto arg (𝓝[{w : ℂ | w.im < 0}] (x : ℂ)) (𝓝 (-Real.pi)) :=
  ⟨arg_ofReal_of_neg hx, tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero (by simpa using hx)
    (by simp)⟩

/-- **DLMF 1.9.8**: `|ℜz| ≤ |z|`, `|ℑz| ≤ |z|`. -/
theorem dlmf_1_9_8 (z : ℂ) : |z.re| ≤ ‖z‖ ∧ |z.im| ≤ ‖z‖ := ⟨abs_re_le_norm z, abs_im_le_norm z⟩

/-- **DLMF 1.9.9**: `z = r e^{iθ}`. -/
theorem dlmf_1_9_9 (z : ℂ) : z = ‖z‖ * exp (arg z * I) := (norm_mul_exp_arg_mul_I z).symm

/-- **DLMF 1.9.10**: `e^{iθ} = cos θ + i sin θ`. -/
theorem dlmf_1_9_10 (θ : ℝ) : exp (θ * I) = Real.cos θ + I * Real.sin θ := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  ring

/-- **DLMF 1.9.11**: `z̄ = x − iy`. -/
theorem dlmf_1_9_11 (x y : ℝ) : conj (x + y * I : ℂ) = x - y * I := by
  simp [map_add, map_mul, conj_ofReal, conj_I]
  ring

/-- **DLMF 1.9.12**: `|z̄| = |z|`. -/
theorem dlmf_1_9_12 (z : ℂ) : ‖conj z‖ = ‖z‖ := norm_conj z

theorem isPhase_conj {z : ℂ} {θ : ℝ} (h : IsPhase z θ) : IsPhase (conj z) (-θ) := by
  refine ⟨(map_ne_zero _).mpr h.1, ?_⟩
  conv_lhs => rw [h.2]
  rw [map_mul, conj_ofReal, ← exp_conj, map_mul, conj_ofReal, conj_I, norm_conj]
  push_cast
  ring_nf

/-- **DLMF 1.9.13**: `ph z̄ = −ph z` (for phases in general). -/
theorem dlmf_1_9_13 (z : ℂ) (θ : ℝ) : IsPhase (conj z) (-θ) ↔ IsPhase z θ :=
  ⟨fun h => by simpa using isPhase_conj h, isPhase_conj⟩

/-- **DLMF 1.9.13** for the principal value, off the negative real axis. -/
theorem dlmf_1_9_13_principal {z : ℂ} (hz : arg z ≠ Real.pi) : arg (conj z) = -arg z := by
  simp [arg_conj, hz]

/-- **DLMF 1.9.14**: `z₁ ± z₂ = x₁ ± x₂ + i(y₁ ± y₂)`. -/
theorem dlmf_1_9_14 (x₁ y₁ x₂ y₂ : ℝ) :
    (x₁ + y₁ * I) + (x₂ + y₂ * I) = (x₁ + x₂ : ℝ) + (y₁ + y₂ : ℝ) * I ∧
      (x₁ + y₁ * I) - (x₂ + y₂ * I) = (x₁ - x₂ : ℝ) + (y₁ - y₂ : ℝ) * I := by
  constructor <;> push_cast <;> ring

/-- **DLMF 1.9.15**: `z₁z₂ = x₁x₂ − y₁y₂ + i(x₁y₂ + x₂y₁)`. -/
theorem dlmf_1_9_15 (x₁ y₁ x₂ y₂ : ℝ) :
    (x₁ + y₁ * I) * (x₂ + y₂ * I) = (x₁ * x₂ - y₁ * y₂ : ℝ) + (x₁ * y₂ + x₂ * y₁ : ℝ) * I := by
  push_cast
  linear_combination y₁ * y₂ * I_sq

/-- **DLMF 1.9.16**: `z₁/z₂ = z₁z̄₂/|z₂|² = (x₁x₂ + y₁y₂ + i(x₂y₁ − x₁y₂))/(x₂² + y₂²)`. -/
theorem dlmf_1_9_16 (x₁ y₁ x₂ y₂ : ℝ) (h : (x₂ + y₂ * I : ℂ) ≠ 0) :
    (x₁ + y₁ * I) / (x₂ + y₂ * I) = (x₁ + y₁ * I) * conj (x₂ + y₂ * I : ℂ) /
        (‖(x₂ + y₂ * I : ℂ)‖ ^ 2 : ℝ) ∧
      (x₁ + y₁ * I) / (x₂ + y₂ * I) =
        ((x₁ * x₂ + y₁ * y₂ : ℝ) + (x₂ * y₁ - x₁ * y₂ : ℝ) * I) / (x₂ ^ 2 + y₂ ^ 2 : ℝ) := by
  have hn : (x₂ : ℝ) ^ 2 + y₂ ^ 2 ≠ 0 := by
    intro h0
    apply h
    have hx : x₂ = 0 := by nlinarith [sq_nonneg x₂, sq_nonneg y₂]
    have hy : y₂ = 0 := by nlinarith [sq_nonneg x₂, sq_nonneg y₂]
    simp [hx, hy]
  have hnC : ((x₂ ^ 2 + y₂ ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hn
  have hsq : ‖(x₂ + y₂ * I : ℂ)‖ ^ 2 = x₂ ^ 2 + y₂ ^ 2 := by
    rw [norm_add_mul_I, Real.sq_sqrt (by positivity)]
  have hmain : (x₁ + y₁ * I) / (x₂ + y₂ * I) =
      ((x₁ * x₂ + y₁ * y₂ : ℝ) + (x₂ * y₁ - x₁ * y₂ : ℝ) * I) / (x₂ ^ 2 + y₂ ^ 2 : ℝ) := by
    rw [div_eq_div_iff h hnC]
    push_cast
    linear_combination ((x₁ : ℂ) * y₂ ^ 2 - x₂ * y₁ * y₂) * I_sq
  refine ⟨?_, hmain⟩
  rw [hmain, hsq, dlmf_1_9_11]
  congr 1
  push_cast
  linear_combination ((y₁ : ℂ) * y₂) * I_sq

/-- **DLMF 1.9.17**: `|z₁z₂| = |z₁||z₂|`. -/
theorem dlmf_1_9_17 (z₁ z₂ : ℂ) : ‖z₁ * z₂‖ = ‖z₁‖ * ‖z₂‖ := norm_mul z₁ z₂

/-- **DLMF 1.9.18**: `ph(z₁z₂) = ph z₁ + ph z₂` for general phases. -/
theorem dlmf_1_9_18 {z₁ z₂ : ℂ} {θ₁ θ₂ : ℝ} (h₁ : IsPhase z₁ θ₁) (h₂ : IsPhase z₂ θ₂) :
    IsPhase (z₁ * z₂) (θ₁ + θ₂) := by
  refine ⟨mul_ne_zero h₁.1 h₂.1, ?_⟩
  conv_lhs => rw [h₁.2, h₂.2]
  rw [norm_mul]
  push_cast
  rw [add_mul, exp_add]
  ring

/-- **DLMF 1.9.19**: `|z₁/z₂| = |z₁|/|z₂|`. -/
theorem dlmf_1_9_19 (z₁ z₂ : ℂ) : ‖z₁ / z₂‖ = ‖z₁‖ / ‖z₂‖ := norm_div z₁ z₂

/-- **DLMF 1.9.20**: `ph(z₁/z₂) = ph z₁ − ph z₂` for general phases. -/
theorem dlmf_1_9_20 {z₁ z₂ : ℂ} {θ₁ θ₂ : ℝ} (h₁ : IsPhase z₁ θ₁) (h₂ : IsPhase z₂ θ₂) :
    IsPhase (z₁ / z₂) (θ₁ - θ₂) := by
  refine ⟨div_ne_zero h₁.1 h₂.1, ?_⟩
  have hn : ((‖z₂‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h₂.1)
  conv_lhs => rw [h₁.2, h₂.2]
  rw [norm_div]
  push_cast
  rw [sub_mul, exp_sub]
  field_simp

/-- **DLMF §1.9(i)**: for principal values, 1.9.18 holds up to a multiple of `2π`. -/
theorem dlmf_1_9_18_principal {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    ∃ n : ℤ, arg (z₁ * z₂) = arg z₁ + arg z₂ + 2 * n * Real.pi := by
  obtain ⟨n, hn⟩ := (dlmf_1_9_7 (mul_ne_zero h₁ h₂) _).mp
    (dlmf_1_9_18 (dlmf_1_9_7_principal_isPhase h₁) (dlmf_1_9_7_principal_isPhase h₂))
  exact ⟨-n, by push_cast; linarith⟩

/-- **DLMF §1.9(i)**: for principal values, 1.9.20 holds up to a multiple of `2π`. -/
theorem dlmf_1_9_20_principal {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    ∃ n : ℤ, arg (z₁ / z₂) = arg z₁ - arg z₂ + 2 * n * Real.pi := by
  obtain ⟨n, hn⟩ := (dlmf_1_9_7 (div_ne_zero h₁ h₂) _).mp
    (dlmf_1_9_20 (dlmf_1_9_7_principal_isPhase h₁) (dlmf_1_9_7_principal_isPhase h₂))
  exact ⟨-n, by push_cast; linarith⟩

/-- **DLMF §1.9(i)**: 1.9.18 fails for principal values: `ph((−1)(−1)) ≠ ph(−1) + ph(−1)`. -/
theorem dlmf_1_9_18_principal_counterexample : arg ((-1) * (-1) : ℂ) ≠ arg (-1) + arg (-1) := by
  rw [neg_one_mul, neg_neg, arg_one, arg_neg_one]
  linarith [Real.pi_pos]

/-- **DLMF §1.9(i)**: 1.9.20 fails for principal values: `ph((−1)/(−i)) ≠ ph(−1) − ph(−i)`. -/
theorem dlmf_1_9_20_principal_counterexample : arg ((-1) / (-I) : ℂ) ≠ arg (-1) - arg (-I) := by
  rw [neg_div_neg_eq, one_div, inv_I, arg_neg_I, arg_neg_one]
  linarith [Real.pi_pos]

theorem I_pow_even (m : ℕ) : I ^ (2 * m) = ((-1 : ℝ) ^ m : ℝ) := by
  rw [pow_mul, I_sq]; push_cast; rfl

theorem I_pow_odd (m : ℕ) : I ^ (2 * m + 1) = ((-1 : ℝ) ^ m : ℝ) * I := by
  rw [pow_succ, I_pow_even]

theorem re_I_pow (k : ℕ) : (I ^ k).re = if Even k then (-1 : ℝ) ^ (k / 2) else 0 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [I_pow_even, ofReal_re]
    simp [Nat.mul_div_cancel_left m two_pos]
  · have : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    rw [I_pow_odd, re_ofReal_mul, I_re, mul_zero]
    simp [this]

theorem im_I_pow (k : ℕ) : (I ^ k).im = if Even k then 0 else (-1 : ℝ) ^ (k / 2) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [I_pow_even, ofReal_im]
    simp
  · have : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    rw [I_pow_odd, im_ofReal_mul, I_im, mul_one]
    simp only [this, ite_false]
    congr 1
    omega

/-- **DLMF 1.9.21**: `zⁿ = (xⁿ − C(n,2)xⁿ⁻²y² + C(n,4)xⁿ⁻⁴y⁴ − ⋯) +
i(C(n,1)xⁿ⁻¹y − C(n,3)xⁿ⁻³y³ + ⋯)`: the real part sums the even `k`, the imaginary part the odd
`k`, with sign `(−1)^⌊k/2⌋`. -/
theorem dlmf_1_9_21 (x y : ℝ) (n : ℕ) :
    ((x + y * I) ^ n).re = ∑ k ∈ (Finset.range (n + 1)).filter Even,
        (-1) ^ (k / 2) * (n.choose k : ℝ) * x ^ (n - k) * y ^ k ∧
      ((x + y * I) ^ n).im = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Even k),
        (-1) ^ (k / 2) * (n.choose k : ℝ) * x ^ (n - k) * y ^ k := by
  have hterm : ∀ k : ℕ, ((y : ℂ) * I) ^ k * (x : ℂ) ^ (n - k) * (n.choose k : ℂ) =
      ((y ^ k * x ^ (n - k) * n.choose k : ℝ) : ℂ) * I ^ k := fun k => by
    push_cast; ring
  rw [add_comm, add_pow]
  simp only [hterm, re_sum, im_sum, re_ofReal_mul, im_ofReal_mul, re_I_pow, im_I_pow,
    Finset.sum_filter]
  constructor
  · refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring

/-- **DLMF 1.9.22** (De Moivre's theorem): `cos nθ + i sin nθ = (cos θ + i sin θ)ⁿ`, `n ∈ ℤ`. -/
theorem dlmf_1_9_22 (θ : ℝ) (n : ℤ) :
    (Real.cos (n * θ) : ℂ) + I * Real.sin (n * θ) = ((Real.cos θ : ℂ) + I * Real.sin θ) ^ n := by
  rw [← dlmf_1_9_10, ← dlmf_1_9_10, ← exp_int_mul]
  push_cast
  ring_nf

/-- **DLMF 1.9.23** (triangle inequality): `||z₁| − |z₂|| ≤ |z₁ + z₂| ≤ |z₁| + |z₂|`. -/
theorem dlmf_1_9_23 (z₁ z₂ : ℂ) : |‖z₁‖ - ‖z₂‖| ≤ ‖z₁ + z₂‖ ∧ ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := by
  refine ⟨?_, norm_add_le z₁ z₂⟩
  have := abs_norm_sub_norm_le z₁ (-z₂)
  rwa [norm_neg, sub_neg_eq_add] at this

/-! ### §1.9(ii) Continuity, point sets, and differentiation -/

section Continuity

/-- **DLMF §1.9(ii)**: `f` is continuous at `z₀` iff for every `ε > 0` there is `δ > 0` with
`|f(z) − f(z₀)| < ε` on the disk `|z − z₀| < δ`. -/
theorem dlmf_1_9_ii_continuousAt {f : ℂ → ℂ} {z₀ : ℂ} :
    ContinuousAt f z₀ ↔ ∀ ε > 0, ∃ δ > 0, ∀ z, ‖z - z₀‖ < δ → ‖f z - f z₀‖ < ε := by
  rw [Metric.continuousAt_iff]
  simp only [dist_eq_norm]

/-- **DLMF §1.9(ii)**: continuity of a function of two complex variables at `(z₀, w₀)`. -/
theorem dlmf_1_9_ii_continuousAt₂ {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ} :
    ContinuousAt f (z₀, w₀) ↔ ∀ ε > 0, ∃ δ > 0, ∀ z w, ‖z - z₀‖ < δ → ‖w - w₀‖ < δ →
      ‖f (z, w) - f (z₀, w₀)‖ < ε := by
  rw [Metric.continuousAt_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    refine ⟨δ, hδ, fun z w hz hw => ?_⟩
    have := @h' (z, w) (by rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]; exact max_lt hz hw)
    rwa [dist_eq_norm] at this
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    refine ⟨δ, hδ, fun {p} hp => ?_⟩
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hp
    rw [dist_eq_norm]
    exact h' p.1 p.2 hp.1 hp.2

/-- **DLMF §1.9(ii)**: continuity on a region `R`, relative to `R`. -/
theorem dlmf_1_9_ii_continuousOn {f : ℂ → ℂ} {R : Set ℂ} :
    ContinuousOn f R ↔ ∀ z₀ ∈ R, ∀ ε > 0, ∃ δ > 0, ∀ z ∈ R, ‖z - z₀‖ < δ →
      ‖f z - f z₀‖ < ε := by
  rw [Metric.continuousOn_iff]
  simp only [dist_eq_norm]

end Continuity

section PointSets

open Metric

/-- **DLMF §1.9(ii)**: an open set is one in which each point has a neighbourhood (disk) contained
in the set. -/
theorem dlmf_1_9_ii_isOpen {S : Set ℂ} :
    IsOpen S ↔ ∀ z ∈ S, ∃ δ > 0, {w | ‖w - z‖ < δ} ⊆ S := by
  rw [Metric.isOpen_iff]
  simp only [Metric.ball, dist_eq_norm]

/-- **DLMF §1.9(ii)**: `z₀` is a limit point of `S`: every neighbourhood of `z₀` contains a point
of `S` other than `z₀`. -/
def IsLimitPoint (S : Set ℂ) (z₀ : ℂ) : Prop := ∀ δ > 0, ∃ z ∈ S, z ≠ z₀ ∧ ‖z - z₀‖ < δ

theorem isLimitPoint_iff_accPt {S : Set ℂ} {z₀ : ℂ} : IsLimitPoint S z₀ ↔ AccPt z₀ (𝓟 S) := by
  rw [accPt_iff_nhds]
  constructor
  · intro h U hU
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨z, hz, hne, hd⟩ := h δ hδ
    exact ⟨z, ⟨hball (by rw [mem_ball, dist_eq_norm]; exact hd), hz⟩, hne⟩
  · intro h δ hδ
    obtain ⟨z, ⟨hzU, hzS⟩, hne⟩ := h _ (Metric.ball_mem_nhds z₀ hδ)
    rw [mem_ball, dist_eq_norm] at hzU
    exact ⟨z, hzS, hne, hzU⟩

/-- **DLMF §1.9(ii)**: every neighbourhood of a limit point of `S` contains infinitely many points
of `S`. -/
theorem dlmf_1_9_ii_limitPoint_infinite {S : Set ℂ} {z₀ : ℂ} (h : IsLimitPoint S z₀) {δ : ℝ}
    (hδ : 0 < δ) : (S ∩ {z | ‖z - z₀‖ < δ}).Infinite := by
  intro hfin
  set F := (S ∩ {z | ‖z - z₀‖ < δ}) \ {z₀}
  have hF : F.Finite := hfin.sdiff
  have hU : Fᶜ ∈ 𝓝 z₀ := hF.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨z, hz, hne, hd⟩ := h (min ε δ) (lt_min hε hδ)
  exact hball (show z ∈ ball z₀ ε by
      rw [mem_ball, dist_eq_norm]; exact hd.trans_le (min_le_left _ _))
    ⟨⟨hz, show ‖z - z₀‖ < δ from hd.trans_le (min_le_right _ _)⟩, hne⟩

/-- **DLMF §1.9(ii)**: the closure of `S` is `S` together with its limit points. -/
theorem dlmf_1_9_ii_closure (S : Set ℂ) : closure S = S ∪ {z | IsLimitPoint S z} := by
  rw [closure_eq_self_union_derivedSet]
  congr 1
  ext z
  exact isLimitPoint_iff_accPt.symm

/-- `a` and `b` are joined in `D` by a polygonal arc: a finite chain of straight-line segments
lying in `D`. -/
def PolygonallyJoined (D : Set ℂ) : ℂ → ℂ → Prop :=
  Relation.ReflTransGen fun p q => segment ℝ p q ⊆ D

theorem joinedIn_of_polygonallyJoined {D : Set ℂ} {a b : ℂ} (ha : a ∈ D)
    (h : PolygonallyJoined D a b) : JoinedIn D a b := by
  induction h with
  | refl => exact JoinedIn.refl ha
  | tail _ hseg ih =>
    exact ih.trans (((convex_segment _ _).isPathConnected ⟨_, left_mem_segment ℝ _ _⟩).joinedIn
      _ (left_mem_segment ℝ _ _) _ (right_mem_segment ℝ _ _) |>.mono hseg)

/-- **DLMF §1.9(ii)**: an open set is connected (a domain) iff any two of its points can be
joined by a polygonal arc lying in the set. -/
theorem dlmf_1_9_ii_domain {D : Set ℂ} (hD : IsOpen D) :
    IsConnected D ↔ D.Nonempty ∧ ∀ a ∈ D, ∀ b ∈ D, PolygonallyJoined D a b := by
  constructor
  · intro hc
    refine ⟨hc.nonempty, fun a ha b hb => ?_⟩
    refine hc.isPreconnected.induction₂' (PolygonallyJoined D) (fun x hx => ?_)
      (fun x y z _ _ _ h1 h2 => h1.trans h2) ha hb
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD x hx
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x hr)] with y hy
    have hseg : segment ℝ x y ⊆ D :=
      ((convex_ball x r).segment_subset (mem_ball_self hr) hy).trans hball
    exact ⟨Relation.ReflTransGen.single hseg,
      Relation.ReflTransGen.single (by rw [segment_symm]; exact hseg)⟩
  · rintro ⟨hne, h⟩
    exact (isPathConnected_iff.mpr ⟨hne, fun x hx y hy =>
      joinedIn_of_polygonallyJoined hx (h x hx y hy)⟩).isConnected

/-- **DLMF §1.9(ii)**: `z` is a boundary point of `D` iff every neighbourhood of `z` contains
members and nonmembers of `D`. -/
theorem dlmf_1_9_ii_boundary {D : Set ℂ} {z : ℂ} :
    z ∈ frontier D ↔ ∀ δ > 0, (∃ w ∈ D, ‖w - z‖ < δ) ∧ ∃ w, w ∉ D ∧ ‖w - z‖ < δ := by
  rw [frontier_eq_closure_inter_closure, Set.mem_inter_iff, Metric.mem_closure_iff,
    Metric.mem_closure_iff]
  constructor
  · rintro ⟨h1, h2⟩ δ hδ
    obtain ⟨w, hw, hd⟩ := h1 δ hδ
    obtain ⟨w', hw', hd'⟩ := h2 δ hδ
    rw [dist_comm, dist_eq_norm] at hd hd'
    exact ⟨⟨w, hw, hd⟩, w', hw', hd'⟩
  · intro h
    refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
    · obtain ⟨w, hw, hd⟩ := (h δ hδ).1
      exact ⟨w, hw, by rwa [dist_comm, dist_eq_norm]⟩
    · obtain ⟨w, hw, hd⟩ := (h δ hδ).2
      exact ⟨w, hw, by rwa [dist_comm, dist_eq_norm]⟩

/-- **DLMF §1.9(ii)**: adding its boundary points to a domain gives its closure (the closed
domain). -/
theorem dlmf_1_9_ii_closed_domain {D : Set ℂ} (hD : IsOpen D) : D ∪ frontier D = closure D := by
  rw [frontier, hD.interior_eq, Set.union_sdiff_self, Set.union_eq_right.mpr subset_closure]

/-- **DLMF §1.9(ii)**: a region is an open domain `D` together with none, some, or all of its
boundary points. -/
def IsRegion (D R : Set ℂ) : Prop := IsOpen D ∧ IsConnected D ∧ D ⊆ R ∧ R ⊆ closure D

/-- **DLMF §1.9(ii)**: the interior points of a region, those that are not boundary points, form
the open domain. -/
theorem dlmf_1_9_ii_interior_points {D R : Set ℂ} (h : IsRegion D R) :
    {z | z ∈ R ∧ z ∉ frontier D} = D := by
  ext z
  constructor
  · rintro ⟨hzR, hzf⟩
    rw [frontier, Set.mem_sdiff, not_and, not_not] at hzf
    rw [← h.1.interior_eq]
    exact hzf (h.2.2.2 hzR)
  · intro hz
    exact ⟨h.2.2.1 hz, fun hf => hf.2 (by rw [h.1.interior_eq]; exact hz)⟩

end PointSets

section Differentiation

/-- **DLMF 1.9.24**: `f′(z) = lim_{h→0} (f(z + h) − f(z))/h`, the limit taken for `h → 0` in
`ℂ`. -/
theorem dlmf_1_9_24 {f : ℂ → ℂ} {f' z : ℂ} :
    HasDerivAt f f' z ↔ Tendsto (fun h => (f (z + h) - f z) / h) (𝓝[≠] 0) (𝓝 f') := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [smul_eq_mul, inv_mul_eq_div]

/-- **DLMF §1.9(ii)**: complex differentiability implies continuity. -/
theorem dlmf_1_9_ii_continuousAt_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (h : DifferentiableAt ℂ f z) : ContinuousAt f z :=
  h.continuousAt

theorem hasDerivAt_re_of {F : ℝ → ℂ} {F' : ℂ} {t : ℝ} (h : HasDerivAt F F' t) :
    HasDerivAt (fun s => (F s).re) F'.re t := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_im_of {F : ℝ → ℂ} {F' : ℂ} {t : ℝ} (h : HasDerivAt F F' t) :
    HasDerivAt (fun s => (F s).im) F'.im t := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_of_re_im {F : ℝ → ℂ} {a b t : ℝ} (hre : HasDerivAt (fun s => (F s).re) a t)
    (him : HasDerivAt (fun s => (F s).im) b t) : HasDerivAt F (a + b * I) t := by
  have h := (hre.ofReal_comp).add ((him.ofReal_comp).mul_const I)
  convert h using 1
  funext s
  simp [re_add_im]

theorem hasDerivAt_horizontal {f : ℂ → ℂ} {c : ℂ} {x y : ℝ} (h : HasDerivAt f c (x + y * I)) :
    HasDerivAt (fun s : ℝ => f (s + y * I)) c x := by
  have h1 : HasDerivAt (fun w : ℂ => f (w + y * I)) c (x : ℂ) := by
    have := h.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I))
    rwa [mul_one] at this
  exact h1.comp_ofReal

theorem hasDerivAt_vertical {f : ℂ → ℂ} {c : ℂ} {x y : ℝ} (h : HasDerivAt f c (x + y * I)) :
    HasDerivAt (fun t : ℝ => f (x + t * I)) (c * I) y := by
  have h1 : HasDerivAt (fun w : ℂ => f (x + w * I)) (c * I) (y : ℂ) := by
    have := h.comp (y : ℂ) (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ))
    rwa [one_mul] at this
  exact h1.comp_ofReal

/-- The four partial derivatives of `u = ℜf`, `v = ℑf` at a point of complex differentiability. -/
theorem hasDerivAt_partials {f : ℂ → ℂ} {c : ℂ} {x y : ℝ} (h : HasDerivAt f c (x + y * I)) :
    HasDerivAt (fun s : ℝ => (f (s + y * I)).re) c.re x ∧
      HasDerivAt (fun s : ℝ => (f (s + y * I)).im) c.im x ∧
      HasDerivAt (fun t : ℝ => (f (x + t * I)).re) (-c.im) y ∧
      HasDerivAt (fun t : ℝ => (f (x + t * I)).im) c.re y := by
  have hh := hasDerivAt_horizontal h
  have hv := hasDerivAt_vertical h
  refine ⟨hasDerivAt_re_of hh, hasDerivAt_im_of hh, ?_, ?_⟩
  · simpa using hasDerivAt_re_of hv
  · simpa using hasDerivAt_im_of hv

/-- **DLMF 1.9.25** (Cauchy–Riemann equations): if `f′(z)` exists at `z = x + iy` and
`f = u + iv`, then `∂u/∂x = ∂v/∂y` and `∂u/∂y = −∂v/∂x` at `(x, y)`. -/
theorem dlmf_1_9_25 {f : ℂ → ℂ} {x y : ℝ} (h : DifferentiableAt ℂ f (x + y * I)) :
    deriv (fun s : ℝ => (f (s + y * I)).re) x = deriv (fun t : ℝ => (f (x + t * I)).im) y ∧
      deriv (fun t : ℝ => (f (x + t * I)).re) y = -deriv (fun s : ℝ => (f (s + y * I)).im) x := by
  obtain ⟨h1, h2, h3, h4⟩ := hasDerivAt_partials h.hasDerivAt
  rw [h1.deriv, h2.deriv, h3.deriv, h4.deriv]
  exact ⟨rfl, rfl⟩

/-- **DLMF §1.9(ii)** (converse of 1.9.25): if at `(x₀, y₀)` the partial derivatives of
`u = ℜf`, `v = ℑf` exist (near the point), are continuous and satisfy the Cauchy–Riemann
equations, then `f` is complex differentiable at `x₀ + iy₀`, with `f′ = ∂u/∂x + i ∂v/∂x`.
(Continuity of `∂u/∂x` and `∂v/∂x` at the point suffices; DLMF asks for all four.) -/
theorem dlmf_1_9_25_converse {f : ℂ → ℂ} {x₀ y₀ : ℝ} {ux uy vx vy : ℝ × ℝ → ℝ}
    (hux : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, y₀),
      HasDerivAt (fun s : ℝ => (f (s + p.2 * I)).re) (ux p) p.1)
    (hvx : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, y₀),
      HasDerivAt (fun s : ℝ => (f (s + p.2 * I)).im) (vx p) p.1)
    (huy : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, y₀),
      HasDerivAt (fun t : ℝ => (f (p.1 + t * I)).re) (uy p) p.2)
    (hvy : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, y₀),
      HasDerivAt (fun t : ℝ => (f (p.1 + t * I)).im) (vy p) p.2)
    (hcux : ContinuousAt ux (x₀, y₀)) (hcvx : ContinuousAt vx (x₀, y₀))
    (hcr1 : ux (x₀, y₀) = vy (x₀, y₀)) (hcr2 : uy (x₀, y₀) = -vx (x₀, y₀)) :
    HasDerivAt f (ux (x₀, y₀) + vx (x₀, y₀) * I) (x₀ + y₀ * I) := by
  set p₀ : ℝ × ℝ := (x₀, y₀)
  set c : ℂ := ux p₀ + vx p₀ * I
  have hvert : HasDerivAt (fun t : ℝ => f (x₀ + t * I)) (c * I) y₀ := by
    have h := hasDerivAt_of_re_im huy.self_of_nhds hvy.self_of_nhds
    convert h using 1
    simp only [c]
    rw [hcr2, ← hcr1]
    push_cast
    linear_combination (vx p₀ : ℂ) * I_sq
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  -- horizontal partials near `p₀`, with complex derivative within `ε/2` of `c`
  have hcomb : ∀ᶠ p in 𝓝 p₀, HasDerivAt (fun s : ℝ => f (s + p.2 * I)) (ux p + vx p * I) p.1 ∧
      ‖((ux p : ℂ) + vx p * I) - c‖ ≤ ε / 2 := by
    have h4 : 0 < ε / 4 := by positivity
    filter_upwards [hux, hvx, hcux.eventually (Metric.ball_mem_nhds _ h4),
      hcvx.eventually (Metric.ball_mem_nhds _ h4)] with p h1 h2 h3 h4'
    refine ⟨hasDerivAt_of_re_im h1 h2, ?_⟩
    simp only [Real.dist_eq] at h3 h4'
    have : ((ux p : ℂ) + vx p * I) - c =
        ((ux p - ux p₀ : ℝ) : ℂ) + ((vx p - vx p₀ : ℝ) : ℂ) * I := by
      simp only [c]; push_cast; ring
    rw [this]
    calc ‖((ux p - ux p₀ : ℝ) : ℂ) + ((vx p - vx p₀ : ℝ) : ℂ) * I‖
        ≤ ‖((ux p - ux p₀ : ℝ) : ℂ)‖ + ‖((vx p - vx p₀ : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = |ux p - ux p₀| + |vx p - vx p₀| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ε / 2 := by linarith
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp hcomb
  have hv := (hasDerivAt_iff_isLittleO_nhds_zero.mp hvert)
  rw [Asymptotics.isLittleO_iff] at hv
  obtain ⟨δ', hδ', hδ'P⟩ := Metric.eventually_nhds_iff.mp (hv hε2)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (lt_min hδ hδ')] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  set a := h.re
  set b := h.im
  have ha : |a| ≤ ‖h‖ := abs_re_le_norm h
  have hb : |b| ≤ ‖h‖ := abs_im_le_norm h
  have hbδ : |b| < δ := hb.trans_lt (hh.trans_le (min_le_left _ _))
  -- the horizontal step, by the mean value theorem
  have hhor : ‖f (↑(x₀ + a) + ↑(y₀ + b) * I) - f (↑x₀ + ↑(y₀ + b) * I) - a * c‖ ≤ ε / 2 * |a| := by
    set φ : ℝ → ℂ := fun s => f (s + ↑(y₀ + b) * I) - s * c
    have hφ : ∀ s ∈ uIcc x₀ (x₀ + a), HasDerivWithinAt φ
        ((ux (s, y₀ + b) + vx (s, y₀ + b) * I) - c) (uIcc x₀ (x₀ + a)) s ∧
        ‖((ux (s, y₀ + b) : ℂ) + vx (s, y₀ + b) * I) - c‖ ≤ ε / 2 := fun s hs => by
      have hsd : |s - x₀| ≤ |a| := by
        rw [Set.mem_uIcc] at hs
        rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have hP := hδP (y := (s, y₀ + b)) (by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, show y₀ + b - y₀ = b by ring]
        exact max_lt (hsd.trans_lt (ha.trans_lt (hh.trans_le (min_le_left _ _)))) hbδ)
      refine ⟨?_, hP.2⟩
      have h1 := hP.1
      have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * c) c s := by
        simpa using (hasDerivAt_id (s : ℝ)).ofReal_comp.mul_const c
      exact (h1.sub h2).hasDerivWithinAt
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun s hs => (hφ s hs).1)
      (fun s hs => (hφ s hs).2) (convex_uIcc x₀ (x₀ + a)) left_mem_uIcc right_mem_uIcc
    simp only [φ, add_sub_cancel_left, Real.norm_eq_abs] at hmvt
    calc ‖f (↑(x₀ + a) + ↑(y₀ + b) * I) - f (↑x₀ + ↑(y₀ + b) * I) - a * c‖
        = ‖f (↑(x₀ + a) + ↑(y₀ + b) * I) - ↑(x₀ + a) * c -
            (f (↑x₀ + ↑(y₀ + b) * I) - ↑x₀ * c)‖ := by
          congr 1; push_cast; ring
      _ ≤ ε / 2 * |a| := hmvt
  -- the vertical step, from the derivative at the point
  have hver : ‖f (↑x₀ + ↑(y₀ + b) * I) - f (↑x₀ + ↑y₀ * I) - b * (c * I)‖ ≤ ε / 2 * |b| := by
    have := hδ'P (y := b) (by
      rw [Real.dist_eq, sub_zero]; exact hb.trans_lt (hh.trans_le (min_le_right _ _)))
    simpa [Real.norm_eq_abs, Complex.real_smul] using this
  have hsplit : f (↑x₀ + ↑y₀ * I + h) - f (↑x₀ + ↑y₀ * I) - h • c =
      (f (↑(x₀ + a) + ↑(y₀ + b) * I) - f (↑x₀ + ↑(y₀ + b) * I) - a * c) +
        (f (↑x₀ + ↑(y₀ + b) * I) - f (↑x₀ + ↑y₀ * I) - b * (c * I)) := by
    have hh' : h = a + b * I := (re_add_im h).symm
    rw [show (↑x₀ + ↑y₀ * I + h : ℂ) = ↑(x₀ + a) + ↑(y₀ + b) * I by rw [hh']; push_cast; ring,
      smul_eq_mul]
    rw [hh']
    ring
  rw [hsplit]
  calc ‖(f (↑(x₀ + a) + ↑(y₀ + b) * I) - f (↑x₀ + ↑(y₀ + b) * I) - a * c) +
        (f (↑x₀ + ↑(y₀ + b) * I) - f (↑x₀ + ↑y₀ * I) - b * (c * I))‖
      ≤ ε / 2 * |a| + ε / 2 * |b| := (norm_add_le _ _).trans (add_le_add hhor hver)
    _ ≤ ε * ‖h‖ := by nlinarith

end Differentiation

/-! ### Analyticity and harmonic functions -/

section Analyticity

/-- **DLMF §1.9(ii)**: `f` is analytic (holomorphic) at `z₀` iff it is complex differentiable in a
neighbourhood of `z₀`. -/
theorem dlmf_1_9_ii_analyticAt {f : ℂ → ℂ} {z₀ : ℂ} :
    (∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ f z) ↔ AnalyticAt ℂ f z₀ :=
  analyticAt_iff_eventually_differentiableAt.symm

/-- **DLMF §1.9(ii)**: entire functions are those analytic at every point of `ℂ`. -/
theorem dlmf_1_9_ii_entire {f : ℂ → ℂ} : Differentiable ℂ f ↔ ∀ z, AnalyticAt ℂ f z :=
  ⟨fun h z => h.analyticAt z, fun h z => (h z).differentiableAt⟩

/-- **DLMF §1.9(ii)**: if `f` is analytic in an open domain `D`, so are `f′, f″, …`. -/
theorem dlmf_1_9_ii_iterate_deriv {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : DifferentiableOn ℂ f D) (n : ℕ) : DifferentiableOn ℂ (deriv^[n] f) D := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.deriv hD

theorem laplace_re {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    {x y : ℝ} (hz : (x + y * I : ℂ) ∈ D) :
    deriv (fun s : ℝ => deriv (fun s' : ℝ => (f (s' + y * I)).re) s) x +
      deriv (fun t : ℝ => deriv (fun t' : ℝ => (f (x + t' * I)).re) t) y = 0 := by
  have hf' := hf.deriv hD
  have hd : ∀ w ∈ D, HasDerivAt f (deriv f w) w := fun w hw =>
    (hf.differentiableAt (hD.mem_nhds hw)).hasDerivAt
  have hd' : ∀ w ∈ D, HasDerivAt (deriv f) (deriv (deriv f) w) w := fun w hw =>
    (hf'.differentiableAt (hD.mem_nhds hw)).hasDerivAt
  have hx : ∀ᶠ s : ℝ in 𝓝 x, ((s : ℂ) + y * I) ∈ D :=
    (continuous_ofReal.add continuous_const).continuousAt.preimage_mem_nhds (hD.mem_nhds hz)
  have hy : ∀ᶠ t : ℝ in 𝓝 y, ((x : ℂ) + t * I) ∈ D :=
    (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousAt.preimage_mem_nhds
      (hD.mem_nhds hz)
  have e1 : deriv (fun s : ℝ => deriv (fun s' : ℝ => (f (s' + y * I)).re) s) x =
      (deriv (deriv f) (x + y * I)).re := by
    have heq : (fun s : ℝ => deriv (fun s' : ℝ => (f (s' + y * I)).re) s) =ᶠ[𝓝 x]
        fun s : ℝ => (deriv f (s + y * I)).re := by
      filter_upwards [hx] with s hs
      exact (hasDerivAt_partials (hd _ hs)).1.deriv
    rw [heq.deriv_eq]
    exact (hasDerivAt_partials (hd' _ hz)).1.deriv
  have e2 : deriv (fun t : ℝ => deriv (fun t' : ℝ => (f (x + t' * I)).re) t) y =
      -(deriv (deriv f) (x + y * I)).re := by
    have heq : (fun t : ℝ => deriv (fun t' : ℝ => (f (x + t' * I)).re) t) =ᶠ[𝓝 y]
        fun t : ℝ => -(deriv f (x + t * I)).im := by
      filter_upwards [hy] with t ht
      exact (hasDerivAt_partials (hd _ ht)).2.2.1.deriv
    rw [heq.deriv_eq]
    exact (hasDerivAt_partials (hd' _ hz)).2.2.2.neg.deriv
  rw [e1, e2]
  ring

theorem re_neg_I_mul (w : ℂ) : (-I * w).re = w.im := by simp

/-- **DLMF 1.9.26**: if `f = u + iv` is analytic in an open domain `D`, then `u` and `v` are
harmonic in `D`: `∂²u/∂x² + ∂²u/∂y² = ∂²v/∂x² + ∂²v/∂y² = 0`. -/
theorem dlmf_1_9_26 {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    {x y : ℝ} (hz : (x + y * I : ℂ) ∈ D) :
    deriv (fun s : ℝ => deriv (fun s' : ℝ => (f (s' + y * I)).re) s) x +
        deriv (fun t : ℝ => deriv (fun t' : ℝ => (f (x + t' * I)).re) t) y = 0 ∧
      deriv (fun s : ℝ => deriv (fun s' : ℝ => (f (s' + y * I)).im) s) x +
        deriv (fun t : ℝ => deriv (fun t' : ℝ => (f (x + t' * I)).im) t) y = 0 := by
  refine ⟨laplace_re hD hf hz, ?_⟩
  have := laplace_re (f := fun w => -I * f w) hD (hf.const_mul _) hz
  simpa only [re_neg_I_mul] using this

theorem laplace_polar_re {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    {r θ : ℝ} (hr : r ≠ 0) (hz : (r * exp (θ * I) : ℂ) ∈ D) :
    deriv (fun ρ : ℝ => deriv (fun ρ' : ℝ => (f (ρ' * exp (θ * I))).re) ρ) r +
        1 / r * deriv (fun ρ : ℝ => (f (ρ * exp (θ * I))).re) r +
        1 / r ^ 2 * deriv (fun φ : ℝ => deriv (fun φ' : ℝ => (f (r * exp (φ' * I))).re) φ) θ =
      0 := by
  have hf' := hf.deriv hD
  have hd : ∀ w ∈ D, HasDerivAt f (deriv f w) w := fun w hw =>
    (hf.differentiableAt (hD.mem_nhds hw)).hasDerivAt
  have hd' : ∀ w ∈ D, HasDerivAt (deriv f) (deriv (deriv f) w) w := fun w hw =>
    (hf'.differentiableAt (hD.mem_nhds hw)).hasDerivAt
  set E := exp (θ * I)
  set z := (r : ℂ) * E
  -- the radial line
  have hrad : ∀ (g : ℂ → ℂ) (g' : ℂ) (ρ : ℝ), HasDerivAt g g' ((ρ : ℂ) * E) →
      HasDerivAt (fun ρ' : ℝ => g (ρ' * E)) (g' * E) ρ := fun g g' ρ h => by
    have := h.comp (ρ : ℂ) ((hasDerivAt_id (ρ : ℂ)).mul_const E)
    rw [one_mul] at this
    exact this.comp_ofReal
  -- the circle
  have hexp : ∀ φ : ℝ, HasDerivAt (fun φ' : ℝ => (r : ℂ) * exp (φ' * I))
      (r * (exp (φ * I) * I)) φ := fun φ => by
    have := ((hasDerivAt_exp ((φ : ℂ) * I)).comp (φ : ℂ)
      ((hasDerivAt_id (φ : ℂ)).mul_const I)).const_mul (r : ℂ)
    rw [one_mul] at this
    exact this.comp_ofReal
  have hang : ∀ (g : ℂ → ℂ) (g' : ℂ) (φ : ℝ), HasDerivAt g g' ((r : ℂ) * exp (φ * I)) →
      HasDerivAt (fun φ' : ℝ => g (r * exp (φ' * I))) (g' * (r * (exp (φ * I) * I))) φ :=
    fun g g' φ h => h.comp φ (hexp φ)
  have hrn : ∀ᶠ ρ : ℝ in 𝓝 r, ((ρ : ℂ) * E) ∈ D :=
    (continuous_ofReal.mul continuous_const).continuousAt.preimage_mem_nhds (hD.mem_nhds hz)
  have han : ∀ᶠ φ : ℝ in 𝓝 θ, ((r : ℂ) * exp (φ * I)) ∈ D :=
    (continuous_const.mul ((continuous_ofReal.mul continuous_const).cexp)).continuousAt
      |>.preimage_mem_nhds (hD.mem_nhds hz)
  have e1 : deriv (fun ρ : ℝ => (f (ρ * E)).re) r = (deriv f z * E).re :=
    (hasDerivAt_re_of (hrad f _ r (hd _ hz))).deriv
  have e2 : deriv (fun ρ : ℝ => deriv (fun ρ' : ℝ => (f (ρ' * E)).re) ρ) r =
      (deriv (deriv f) z * E * E).re := by
    have heq : (fun ρ : ℝ => deriv (fun ρ' : ℝ => (f (ρ' * E)).re) ρ) =ᶠ[𝓝 r]
        fun ρ : ℝ => (deriv f (ρ * E) * E).re := by
      filter_upwards [hrn] with ρ hρ
      exact (hasDerivAt_re_of (hrad f _ ρ (hd _ hρ))).deriv
    rw [heq.deriv_eq]
    exact (hasDerivAt_re_of ((hrad (deriv f) _ r (hd' _ hz)).mul_const E)).deriv
  have e3 : deriv (fun φ : ℝ => deriv (fun φ' : ℝ => (f (r * exp (φ' * I))).re) φ) θ =
      (deriv (deriv f) z * (r * (E * I)) * (r * (E * I)) +
        deriv f z * (r * (E * I) * I)).re := by
    have heq : (fun φ : ℝ => deriv (fun φ' : ℝ => (f (r * exp (φ' * I))).re) φ) =ᶠ[𝓝 θ]
        fun φ : ℝ => (deriv f (r * exp (φ * I)) * (r * (exp (φ * I) * I))).re := by
      filter_upwards [han] with φ hφ
      exact (hasDerivAt_re_of (hang f _ φ (hd _ hφ))).deriv
    rw [heq.deriv_eq]
    have h1 := hang (deriv f) _ θ (hd' _ hz)
    have h2 : HasDerivAt (fun φ : ℝ => (r : ℂ) * (exp (φ * I) * I)) (r * (E * I) * I) θ := by
      have := (hexp θ).mul_const I
      convert this using 1
      funext φ; ring
    exact (hasDerivAt_re_of (h1.mul h2)).deriv
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have key : deriv (deriv f) z * E * E + ((1 / r : ℝ) : ℂ) * (deriv f z * E) +
      ((1 / r ^ 2 : ℝ) : ℂ) * (deriv (deriv f) z * (r * (E * I)) * (r * (E * I)) +
        deriv f z * (r * (E * I) * I)) = 0 := by
    set q : ℂ := ((1 / r : ℝ) : ℂ)
    have hq : q * r = 1 := by simp only [q]; push_cast; field_simp
    have hq2 : ((1 / r ^ 2 : ℝ) : ℂ) = q ^ 2 := by simp only [q]; push_cast; ring
    rw [hq2]
    linear_combination (deriv (deriv f) z * E ^ 2 + q * deriv f z * E) * I_sq +
      (E ^ 2 * I ^ 2 * deriv (deriv f) z * (q * r + 1) + q * E * I ^ 2 * deriv f z) * hq
  rw [e1, e2, e3]
  have := congrArg Complex.re key
  simpa only [add_re, re_ofReal_mul, zero_re] using this

/-- **DLMF 1.9.27**: in polar form, `u` and `v` satisfy
`∂²u/∂r² + (1/r) ∂u/∂r + (1/r²) ∂²u/∂θ² = 0` at all points of `D` (`r > 0`). -/
theorem dlmf_1_9_27 {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    {r θ : ℝ} (hr : 0 < r) (hz : (r * exp (θ * I) : ℂ) ∈ D) :
    deriv (fun ρ : ℝ => deriv (fun ρ' : ℝ => (f (ρ' * exp (θ * I))).re) ρ) r +
        1 / r * deriv (fun ρ : ℝ => (f (ρ * exp (θ * I))).re) r +
        1 / r ^ 2 * deriv (fun φ : ℝ => deriv (fun φ' : ℝ => (f (r * exp (φ' * I))).re) φ) θ =
      0 ∧
    deriv (fun ρ : ℝ => deriv (fun ρ' : ℝ => (f (ρ' * exp (θ * I))).im) ρ) r +
        1 / r * deriv (fun ρ : ℝ => (f (ρ * exp (θ * I))).im) r +
        1 / r ^ 2 * deriv (fun φ : ℝ => deriv (fun φ' : ℝ => (f (r * exp (φ' * I))).im) φ) θ =
      0 := by
  refine ⟨laplace_polar_re hD hf hr.ne' hz, ?_⟩
  have := laplace_polar_re (f := fun w => -I * f w) hD (hf.const_mul _) hr.ne' hz
  simpa only [re_neg_I_mul] using this

end Analyticity

end Azurite.DLMF
