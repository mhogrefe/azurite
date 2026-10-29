/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section13

/-!
# DLMF §1.13(iv): Change of Variables

Formalizations of <https://dlmf.nist.gov/1.13#iv>. All statements are local calculus identities on
open sets; DLMF's indefinite integrals `∫ f dz` are represented by any primitive `P` (`P′ = f`),
which exists on simply-connected domains by `exists_primitive_of_simplyConnected`.

**Results.**
* 1.13.11–1.13.12: the substitution `ξ = 1/z` (`dlmf_1_13_11`), on the image of `D` under
  `z ↦ 1/z`.
* 1.13.13–1.13.15: `w = W e^{−P/2}` turns (1.13.1) into `W″ − H W = 0` with
  `H = ¼ f² + ½ f′ − g` (`dlmfH`); both directions (`dlmf_1_13_14`).
* 1.13.16–1.13.17: with `η′ = e^{−P}`, `w = v ∘ η` gives
  `w″ + f w′ + g w = e^{−2P}(v̈ + g e^{2P} v)` (`dlmf_1_13_17_identity`), so `w` solves (1.13.1)
  if and only if `v̈ + g e^{2P} v = 0` (`dlmf_1_13_17`).
* 1.13.18–1.13.20: the Liouville transformation and the Schwarzian derivative. The change of
  variable is written `z = φ(ζ)`, so dots are derivatives of `φ`. `(dζ/dz)^{1/2}` is any `q` with
  `q² ż = 1`, so no branch of the square root is needed. `schwarzian` is the second form of
  (1.13.20); the first form is `dlmf_1_13_20`, and `dlmf_1_13_19` is the transformed equation.
* 1.13.21–1.13.22: Cayley's identity for compositions (`dlmf_1_13_21`, from the third-order chain
  rule `deriv_comp_three`) and the inverse-function form (`dlmf_1_13_22`).
-/

open Filter Topology Set Complex

namespace Azurite.DLMF

variable {D : Set ℂ} {f g : ℂ → ℂ}

theorem hasDerivAt_of_differentiableOn {s : Set ℂ} (hs : IsOpen s) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ s) {x : ℂ} (hx : x ∈ s) : HasDerivAt φ (deriv φ x) x :=
  (hφ.differentiableAt (hs.mem_nhds hx)).hasDerivAt

/-! ### Transformation of the point at infinity -/

/-- **DLMF (1.13.11)–(1.13.12)**: with `ξ = 1/z`, `W(ξ) = w(1/ξ)` solves
`W″ + F(ξ) W′ + G(ξ) W = 0` with `F(ξ) = 2/ξ − ξ⁻² f(1/ξ)` and `G(ξ) = ξ⁻⁴ g(1/ξ)`, on the image
of `D \ {0}` under `z ↦ 1/z`. -/
theorem dlmf_1_13_11 (hDo : IsOpen D) {w : ℂ → ℂ} (hw : IsODESolution D f g w) :
    IsODESolution ({ξ : ℂ | ξ ≠ 0} ∩ (fun ξ : ℂ => 1 / ξ) ⁻¹' D)
      (fun ξ => 2 / ξ - 1 / ξ ^ 2 * f (1 / ξ)) (fun ξ => 1 / ξ ^ 4 * g (1 / ξ))
      (fun ξ => w (1 / ξ)) := by
  have hopen : IsOpen ({ξ : ℂ | ξ ≠ 0} ∩ (fun ξ : ℂ => 1 / ξ) ⁻¹' D) :=
    ContinuousOn.isOpen_inter_preimage (fun ξ hξ => (continuousAt_const.div continuousAt_id
      hξ).continuousWithinAt) isOpen_ne hDo
  refine isODESolution_of_hasDerivAt hopen (w' := fun ξ => -(1 / ξ ^ 2) * deriv w (1 / ξ))
    fun ξ hξ => ?_
  obtain ⟨hξ0, hξD⟩ := hξ
  have hξ0 : ξ ≠ 0 := hξ0
  have hinv : HasDerivAt (fun ξ : ℂ => 1 / ξ) (-(1 / ξ ^ 2)) ξ := by
    simpa [one_div] using hasDerivAt_inv hξ0
  obtain ⟨a1, a2⟩ := hw.hasDerivAt hDo hξD
  have hp : HasDerivAt (fun ξ : ℂ => -(1 / ξ ^ 2)) (2 / ξ ^ 3) ξ := by
    have := ((hasDerivAt_pow 2 ξ).inv (pow_ne_zero 2 hξ0)).neg
    convert this using 1
    · funext x; simp [one_div]
    · field_simp; ring
  refine ⟨(a1.comp ξ hinv).congr_deriv (by ring), (hp.mul (a2.comp ξ hinv)).congr_deriv ?_⟩
  simp only [Function.comp_apply]
  field_simp
  ring

/-! ### Elimination of the first derivative by a change of dependent variable -/

/-- **DLMF (1.13.15)**: `H(z) = ¼ f²(z) + ½ f′(z) − g(z)`. -/
noncomputable def dlmfH (f g : ℂ → ℂ) (z : ℂ) : ℂ := 1 / 4 * f z ^ 2 + 1 / 2 * deriv f z - g z

/-- **DLMF (1.13.13)–(1.13.15)**: if `P′ = f` (`P = ∫ f dz`) and `w = W e^{−P/2}`, then `w` solves
(1.13.1) if and only if `W″ − H W = 0`. -/
theorem dlmf_1_13_14 (hDo : IsOpen D) (hf : DifferentiableOn ℂ f D) {P : ℂ → ℂ}
    (hP : ∀ z ∈ D, HasDerivAt P (f z) z) {w W : ℂ → ℂ}
    (hwW : ∀ z ∈ D, w z = W z * exp (-(1 / 2) * P z)) :
    IsODESolution D f g w ↔
      DifferentiableOn ℂ W D ∧ ∀ z ∈ D, deriv (deriv W) z - dlmfH f g z * W z = 0 := by
  have he : ∀ (c : ℂ), ∀ z ∈ D, HasDerivAt (fun z => exp (c * P z)) (exp (c * P z) * (c * f z))
      z := fun c z hz => ((hP z hz).const_mul c).cexp
  have hf' : ∀ z ∈ D, HasDerivAt f (deriv f z) z := fun z hz =>
    hasDerivAt_of_differentiableOn hDo hf hz
  have hWw : ∀ z ∈ D, W z = w z * exp ((1 / 2) * P z) := fun z hz => by
    rw [hwW z hz, mul_assoc, ← Complex.exp_add]
    ring_nf
    rw [Complex.exp_zero, mul_one]
  constructor
  · intro hw
    have hd : ∀ z ∈ D, HasDerivAt W
        ((deriv w z + 1 / 2 * (f z * w z)) * exp (1 / 2 * P z)) z := fun z hz => by
      have h : HasDerivAt (fun y => w y * exp (1 / 2 * P y))
          (deriv w z * exp (1 / 2 * P z) + w z * (exp (1 / 2 * P z) * (1 / 2 * f z))) z :=
        (hw.hasDerivAt hDo hz).1.mul (he (1 / 2) z hz)
      refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
      filter_upwards [hDo.mem_nhds hz] with y hy using hWw y hy
    refine ⟨fun z hz => (hd z hz).differentiableAt.differentiableWithinAt, fun z hz => ?_⟩
    have heq : deriv W =ᶠ[𝓝 z] fun z => (deriv w z + 1 / 2 * (f z * w z)) * exp (1 / 2 * P z) :=
      by filter_upwards [hDo.mem_nhds hz] with y hy using (hd y hy).deriv
    obtain ⟨a1, a2⟩ := hw.hasDerivAt hDo hz
    have h2 : HasDerivAt (fun z => (deriv w z + 1 / 2 * (f z * w z)) * exp (1 / 2 * P z))
        ((-(f z * deriv w z + g z * w z) + 1 / 2 * (deriv f z * w z + f z * deriv w z)) *
          exp (1 / 2 * P z) + (deriv w z + 1 / 2 * (f z * w z)) *
          (exp (1 / 2 * P z) * (1 / 2 * f z))) z :=
      (a2.add (((hf' z hz).mul a1).const_mul (1 / 2))).mul (he (1 / 2) z hz)
    rw [heq.deriv_eq, h2.deriv, hWw z hz, dlmfH]
    ring
  · rintro ⟨hW, hHW⟩
    have hW1 : ∀ z ∈ D, HasDerivAt W (deriv W z) z := fun z hz =>
      hasDerivAt_of_differentiableOn hDo hW hz
    have hW2 : ∀ z ∈ D, HasDerivAt (deriv W) (deriv (deriv W) z) z := fun z hz =>
      hasDerivAt_of_differentiableOn hDo (hW.deriv hDo) hz
    refine isODESolution_of_hasDerivAt hDo
      (w' := fun z => (deriv W z - 1 / 2 * (f z * W z)) * exp (-(1 / 2) * P z))
      fun z hz => ⟨?_, ?_⟩
    · have h : HasDerivAt (fun y => W y * exp (-(1 / 2) * P y))
          (deriv W z * exp (-(1 / 2) * P z) + W z * (exp (-(1 / 2) * P z) * (-(1 / 2) * f z)))
          z := (hW1 z hz).mul (he (-(1 / 2)) z hz)
      refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
      filter_upwards [hDo.mem_nhds hz] with y hy using hwW y hy
    · have h : HasDerivAt (fun z => (deriv W z - 1 / 2 * (f z * W z)) * exp (-(1 / 2) * P z))
          ((deriv (deriv W) z - 1 / 2 * (deriv f z * W z + f z * deriv W z)) *
            exp (-(1 / 2) * P z) + (deriv W z - 1 / 2 * (f z * W z)) *
            (exp (-(1 / 2) * P z) * (-(1 / 2) * f z))) z :=
        ((hW2 z hz).sub (((hf' z hz).mul (hW1 z hz)).const_mul (1 / 2))).mul
          (he (-(1 / 2)) z hz)
      refine h.congr_deriv ?_
      rw [hwW z hz]
      have := hHW z hz
      unfold dlmfH at this
      linear_combination exp (-(1 / 2) * P z) * this

/-! ### Elimination of the first derivative by a change of independent variable -/

/-- **DLMF (1.13.16)–(1.13.17)**: with `P′ = f` and `η′ = e^{−P}` (`η = ∫ e^{−∫ f dz} dz`), the
function `w(z) = v(η(z))` satisfies
`w″ + f w′ + g w = e^{−2P} (d²v/dη² + g(z) e^{2P} v)`. -/
theorem dlmf_1_13_17_identity (hDo : IsOpen D) {P η : ℂ → ℂ}
    (hP : ∀ z ∈ D, HasDerivAt P (f z) z) (hη : ∀ z ∈ D, HasDerivAt η (exp (-P z)) z)
    {E : Set ℂ} (hEo : IsOpen E) {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v E)
    (hηE : MapsTo η D E) {z : ℂ} (hz : z ∈ D) :
    deriv (deriv (fun z => v (η z))) z + f z * deriv (fun z => v (η z)) z + g z * v (η z) =
      exp (-(2 * P z)) * (deriv (deriv v) (η z) + g z * exp (2 * P z) * v (η z)) := by
  have hv1 : ∀ z ∈ D, HasDerivAt (fun z => v (η z)) (deriv v (η z) * exp (-P z)) z :=
    fun z hz => (hasDerivAt_of_differentiableOn hEo hv (hηE hz)).comp z (hη z hz)
  have heq : deriv (fun z => v (η z)) =ᶠ[𝓝 z] fun z => deriv v (η z) * exp (-P z) := by
    filter_upwards [hDo.mem_nhds hz] with y hy using (hv1 y hy).deriv
  have h2 : HasDerivAt (fun z => deriv v (η z) * exp (-P z))
      (deriv (deriv v) (η z) * exp (-P z) * exp (-P z) + deriv v (η z) * (exp (-P z) * -f z))
      z := ((hasDerivAt_of_differentiableOn hEo (hv.deriv hEo) (hηE hz)).comp z
        (hη z hz)).mul (hP z hz).neg.cexp
  rw [heq.deriv_eq, h2.deriv, (hv1 z hz).deriv]
  have e1 : exp (-(2 * P z)) = exp (-P z) * exp (-P z) := by
    rw [← Complex.exp_add]; ring_nf
  have e2 : exp (-(2 * P z)) * exp (2 * P z) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [e1] at e2 ⊢
  linear_combination (-(g z * v (η z))) * e2

/-- **DLMF (1.13.17)**: `w = v ∘ η` solves (1.13.1) if and only if
`d²v/dη² + g(z) e^{2 ∫ f dz} v = 0`. -/
theorem dlmf_1_13_17 (hDo : IsOpen D) {P η : ℂ → ℂ}
    (hP : ∀ z ∈ D, HasDerivAt P (f z) z) (hη : ∀ z ∈ D, HasDerivAt η (exp (-P z)) z)
    {E : Set ℂ} (hEo : IsOpen E) {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v E)
    (hηE : MapsTo η D E) :
    IsODESolution D f g (fun z => v (η z)) ↔
      ∀ z ∈ D, deriv (deriv v) (η z) + g z * exp (2 * P z) * v (η z) = 0 := by
  have hdiff : DifferentiableOn ℂ (fun z => v (η z)) D := fun z hz =>
    ((hasDerivAt_of_differentiableOn hEo hv (hηE hz)).comp z
      (hη z hz)).differentiableAt.differentiableWithinAt
  constructor
  · intro hw z hz
    have := dlmf_1_13_17_identity (g := g) hDo hP hη hEo hv hηE hz
    rw [hw.2 z hz] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (Complex.exp_ne_zero _)
  · intro h
    refine ⟨hdiff, fun z hz => ?_⟩
    rw [dlmf_1_13_17_identity hDo hP hη hEo hv hηE hz, h z hz, mul_zero]

/-! ### The Schwarzian derivative and the Liouville transformation -/

/-- **DLMF (1.13.20)**: the Schwarzian derivative `{z, ζ} = z⃛/ż − (3/2)(z̈/ż)²` of `z = φ(ζ)`. -/
noncomputable def schwarzian (φ : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  deriv (deriv (deriv φ)) ζ / deriv φ ζ - 3 / 2 * (deriv (deriv φ) ζ / deriv φ ζ) ^ 2

theorem eq_zero_of_hasDerivAt_of_eventuallyEq_const {F : ℂ → ℂ} {F' c x : ℂ}
    (h : HasDerivAt F F' x) (hc : F =ᶠ[𝓝 x] fun _ => c) : F' = 0 :=
  h.unique ((hasDerivAt_const x c).congr_of_eventuallyEq hc)

theorem schwarzian_alg {q q1 q2 p1 p2 p3 : ℂ} (h0 : q ^ 2 * p1 = 1)
    (ha : 2 * q * q1 * p1 + q ^ 2 * p2 = 0)
    (hb : 2 * q1 ^ 2 * p1 + 2 * q * q2 * p1 + 4 * q * q1 * p2 + q ^ 2 * p3 = 0) :
    p3 / p1 - 3 / 2 * (p2 / p1) ^ 2 = -2 * q⁻¹ * q2 := by
  have hq : q ≠ 0 := by rintro rfl; simp at h0
  have hp : p1 ≠ 0 := by rintro rfl; simp at h0
  have hq1 : q1 = -(q * p2) / (2 * p1) := by
    field_simp
    refine mul_left_cancel₀ hq ?_
    linear_combination ha
  subst hq1
  field_simp
  field_simp at hb
  refine mul_left_cancel₀ hq ?_
  linear_combination hb

/-- From `q² ż = 1` on an open set: `2 q q̇ ż + q² z̈ = 0` and its derivative. -/
theorem sq_mul_deriv_relations {E : Set ℂ} (hEo : IsOpen E) {φ q : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ E) (hq : DifferentiableOn ℂ q E)
    (hqφ : ∀ ζ ∈ E, q ζ ^ 2 * deriv φ ζ = 1) :
    (∀ ζ ∈ E, 2 * q ζ * deriv q ζ * deriv φ ζ + q ζ ^ 2 * deriv (deriv φ) ζ = 0) ∧
    ∀ ζ ∈ E, 2 * deriv q ζ ^ 2 * deriv φ ζ + 2 * q ζ * deriv (deriv q) ζ * deriv φ ζ +
      4 * q ζ * deriv q ζ * deriv (deriv φ) ζ + q ζ ^ 2 * deriv (deriv (deriv φ)) ζ = 0 := by
  have hφ1 := hφ.deriv hEo
  have hφ2 := hφ1.deriv hEo
  have hq1 := hq.deriv hEo
  have d := fun {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F E) {x} (hx : x ∈ E) =>
    hasDerivAt_of_differentiableOn hEo hF hx
  have ha : ∀ ζ ∈ E, 2 * q ζ * deriv q ζ * deriv φ ζ + q ζ ^ 2 * deriv (deriv φ) ζ = 0 :=
    fun ζ hζ => by
      have h := ((d hq hζ).pow 2).mul (d hφ1 hζ)
      have h0 := eq_zero_of_hasDerivAt_of_eventuallyEq_const h (c := 1) (by
        filter_upwards [hEo.mem_nhds hζ] with y hy
        show q y ^ 2 * deriv φ y = 1
        exact hqφ y hy)
      simp only [Pi.pow_apply, Nat.cast_ofNat] at h0
      linear_combination h0
  refine ⟨ha, fun ζ hζ => ?_⟩
  have h := ((((d hq hζ).const_mul 2).mul (d hq1 hζ)).mul (d hφ1 hζ)).add
    (((d hq hζ).pow 2).mul (d hφ2 hζ))
  have h0 := eq_zero_of_hasDerivAt_of_eventuallyEq_const h (c := 0) (by
    filter_upwards [hEo.mem_nhds hζ] with y hy
    show 2 * q y * deriv q y * deriv φ y + q y ^ 2 * deriv (deriv φ) y = 0
    exact ha y hy)
  simp only [Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat] at h0
  linear_combination h0

/-- **DLMF (1.13.20)**, first form: `{z, ζ} = −2 ż^{1/2} d²(ż^{−1/2})/dζ²`, with `q = ż^{−1/2}`
any function with `q² ż = 1` (no branch of the square root needs to be chosen). -/
theorem dlmf_1_13_20 {E : Set ℂ} (hEo : IsOpen E) {φ q : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ E) (hq : DifferentiableOn ℂ q E)
    (hqφ : ∀ ζ ∈ E, q ζ ^ 2 * deriv φ ζ = 1) {ζ : ℂ} (hζ : ζ ∈ E) :
    schwarzian φ ζ = -2 * (q ζ)⁻¹ * deriv (deriv q) ζ := by
  obtain ⟨ha, hb⟩ := sq_mul_deriv_relations hEo hφ hq hqφ
  exact schwarzian_alg (hqφ ζ hζ) (ha ζ hζ) (hb ζ hζ)

/-- **DLMF (1.13.18)–(1.13.19)** (Liouville transformation): let `W″ = H W` (1.13.14) and let
`z = φ(ζ)` be a change of variable, with `U(ζ) = q(ζ) W(φ(ζ))` where `q² ż = 1`, i.e.
`q = (dζ/dz)^{1/2}` (1.13.18). Then `d²U/dζ² = (ż² H(z) − ½ {z, ζ}) U`. -/
theorem dlmf_1_13_19 {E : Set ℂ} (hEo : IsOpen E) (hDo : IsOpen D) {φ q W H : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ E) (hq : DifferentiableOn ℂ q E)
    (hqφ : ∀ ζ ∈ E, q ζ ^ 2 * deriv φ ζ = 1) (hφD : MapsTo φ E D)
    (hW : DifferentiableOn ℂ W D) (hWH : ∀ z ∈ D, deriv (deriv W) z = H z * W z) {ζ : ℂ}
    (hζ : ζ ∈ E) :
    deriv (deriv (fun ζ => q ζ * W (φ ζ))) ζ =
      ((deriv φ ζ) ^ 2 * H (φ ζ) - 1 / 2 * schwarzian φ ζ) * (q ζ * W (φ ζ)) := by
  have dE := fun {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F E) {x} (hx : x ∈ E) =>
    hasDerivAt_of_differentiableOn hEo hF hx
  have dD := fun {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D) {x} (hx : x ∈ D) =>
    hasDerivAt_of_differentiableOn hDo hF hx
  have hU : ∀ x ∈ E, HasDerivAt (fun ζ => q ζ * W (φ ζ))
      (deriv q x * W (φ x) + q x * (deriv W (φ x) * deriv φ x)) x := fun x hx =>
    (dE hq hx).mul ((dD hW (hφD hx)).comp x (dE hφ hx))
  have heq : deriv (fun ζ => q ζ * W (φ ζ)) =ᶠ[𝓝 ζ]
      fun x => deriv q x * W (φ x) + q x * (deriv W (φ x) * deriv φ x) := by
    filter_upwards [hEo.mem_nhds hζ] with y hy using (hU y hy).deriv
  have h2 : HasDerivAt
      (fun x => deriv q x * W (φ x) + q x * (deriv W (φ x) * deriv φ x))
      (deriv (deriv q) ζ * W (φ ζ) + deriv q ζ * (deriv W (φ ζ) * deriv φ ζ) +
        (deriv q ζ * (deriv W (φ ζ) * deriv φ ζ) + q ζ * (deriv (deriv W) (φ ζ) * deriv φ ζ *
          deriv φ ζ + deriv W (φ ζ) * deriv (deriv φ) ζ))) ζ :=
    ((dE (hq.deriv hEo) hζ).mul ((dD hW (hφD hζ)).comp ζ (dE hφ hζ))).add
      ((dE hq hζ).mul (((dD (hW.deriv hDo) (hφD hζ)).comp ζ (dE hφ hζ)).mul
        (dE (hφ.deriv hEo) hζ)))
  rw [heq.deriv_eq, h2.deriv, dlmf_1_13_20 hEo hφ hq hqφ hζ]
  have ha := (sq_mul_deriv_relations hEo hφ hq hqφ).1 ζ hζ
  have hq0 : q ζ ≠ 0 := by
    intro h0
    have := hqφ ζ hζ
    rw [h0] at this
    simp at this
  have hinv := mul_inv_cancel₀ hq0
  have hH := hWH (φ ζ) (hφD hζ)
  linear_combination q ζ * deriv φ ζ ^ 2 * hH + (deriv W (φ ζ) * (q ζ)⁻¹) * ha +
    (-(deriv (deriv q) ζ * W (φ ζ)) - (2 * deriv q ζ * deriv W (φ ζ) * deriv φ ζ +
      q ζ * deriv W (φ ζ) * deriv (deriv φ) ζ)) * hinv

/-! ### Cayley's identity -/

/-- Derivatives of a composition up to third order. -/
theorem deriv_comp_three {A B : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) {φ ψ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ A) (hψ : DifferentiableOn ℂ ψ B) (hψA : MapsTo ψ B A) {ζ : ℂ}
    (hζ : ζ ∈ B) :
    deriv (fun x => φ (ψ x)) ζ = deriv φ (ψ ζ) * deriv ψ ζ ∧
    deriv (deriv (fun x => φ (ψ x))) ζ =
      deriv (deriv φ) (ψ ζ) * deriv ψ ζ ^ 2 + deriv φ (ψ ζ) * deriv (deriv ψ) ζ ∧
    deriv (deriv (deriv (fun x => φ (ψ x)))) ζ =
      deriv (deriv (deriv φ)) (ψ ζ) * deriv ψ ζ ^ 3 +
        3 * deriv (deriv φ) (ψ ζ) * deriv ψ ζ * deriv (deriv ψ) ζ +
        deriv φ (ψ ζ) * deriv (deriv (deriv ψ)) ζ := by
  have dA := fun {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F A) {x} (hx : x ∈ A) =>
    hasDerivAt_of_differentiableOn hAo hF hx
  have dB := fun {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F B) {x} (hx : x ∈ B) =>
    hasDerivAt_of_differentiableOn hBo hF hx
  have hφ1 := hφ.deriv hAo
  have hφ2 := hφ1.deriv hAo
  have hψ1 := hψ.deriv hBo
  have hψ2 := hψ1.deriv hBo
  have e1 : ∀ x ∈ B, HasDerivAt (fun x => φ (ψ x)) (deriv φ (ψ x) * deriv ψ x) x :=
    fun x hx => (dA hφ (hψA hx)).comp x (dB hψ hx)
  have e1' : ∀ x ∈ B, deriv (fun x => φ (ψ x)) =ᶠ[𝓝 x]
      fun x => deriv φ (ψ x) * deriv ψ x := fun x hx => by
    filter_upwards [hBo.mem_nhds hx] with y hy using (e1 y hy).deriv
  have e2 : ∀ x ∈ B, HasDerivAt (fun x => deriv φ (ψ x) * deriv ψ x)
      (deriv (deriv φ) (ψ x) * deriv ψ x ^ 2 + deriv φ (ψ x) * deriv (deriv ψ) x) x :=
    fun x hx => (((dA hφ1 (hψA hx)).comp x (dB hψ hx)).mul (dB hψ1 hx)).congr_deriv
      (by simp only [Function.comp_apply]; ring)
  have e2' : deriv (deriv (fun x => φ (ψ x))) =ᶠ[𝓝 ζ]
      fun x => deriv (deriv φ) (ψ x) * deriv ψ x ^ 2 + deriv φ (ψ x) * deriv (deriv ψ) x := by
    filter_upwards [hBo.mem_nhds hζ] with y hy
    rw [(e1' y hy).deriv_eq, (e2 y hy).deriv]
  have e3 : HasDerivAt
      (fun x => deriv (deriv φ) (ψ x) * deriv ψ x ^ 2 + deriv φ (ψ x) * deriv (deriv ψ) x)
      (deriv (deriv (deriv φ)) (ψ ζ) * deriv ψ ζ ^ 3 +
        3 * deriv (deriv φ) (ψ ζ) * deriv ψ ζ * deriv (deriv ψ) ζ +
        deriv φ (ψ ζ) * deriv (deriv (deriv ψ)) ζ) ζ :=
    ((((dA hφ2 (hψA hζ)).comp ζ (dB hψ hζ)).mul ((dB hψ1 hζ).pow 2)).add
      (((dA hφ1 (hψA hζ)).comp ζ (dB hψ hζ)).mul (dB hψ2 hζ))).congr_deriv (by
        simp only [Function.comp_apply, Pi.pow_apply]
        push_cast
        ring)
  refine ⟨(e1 ζ hζ).deriv, e2'.self_of_nhds, ?_⟩
  rw [e2'.deriv_eq, e3.deriv]

/-- **DLMF (1.13.21)** (Cayley's identity): for `z = φ(ξ)` and `ξ = ψ(ζ)`,
`{z, ζ} = (dξ/dζ)² {z, ξ} + {ξ, ζ}`. -/
theorem dlmf_1_13_21 {A B : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) {φ ψ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ A) (hψ : DifferentiableOn ℂ ψ B) (hψA : MapsTo ψ B A) {ζ : ℂ}
    (hζ : ζ ∈ B) (hφ0 : deriv φ (ψ ζ) ≠ 0) (hψ0 : deriv ψ ζ ≠ 0) :
    schwarzian (fun x => φ (ψ x)) ζ =
      deriv ψ ζ ^ 2 * schwarzian φ (ψ ζ) + schwarzian ψ ζ := by
  obtain ⟨d1, d2, d3⟩ := deriv_comp_three hAo hBo hφ hψ hψA hζ
  unfold schwarzian
  rw [d1, d2, d3]
  field_simp
  ring

/-- **DLMF (1.13.22)**: for inverse changes of variable `z = φ(ζ)`, `ζ = ψ(z)`,
`{z, ζ} = −(dz/dζ)² {ζ, z}`. -/
theorem dlmf_1_13_22 {A B : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) {φ ψ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ A) (hψ : DifferentiableOn ℂ ψ B) (hψA : MapsTo ψ B A)
    (hinv : ∀ z ∈ B, φ (ψ z) = z) {z : ℂ} (hz : z ∈ B) :
    schwarzian φ (ψ z) = -(deriv φ (ψ z)) ^ 2 * schwarzian ψ z := by
  have hid : (fun x => φ (ψ x)) =ᶠ[𝓝 z] fun x => x := by
    filter_upwards [hBo.mem_nhds hz] with y hy using hinv y hy
  have h1 := hid.deriv
  have h2 := h1.deriv
  have h3 := h2.deriv
  have hS : schwarzian (fun x => φ (ψ x)) z = 0 := by
    unfold schwarzian
    rw [h1.self_of_nhds, h2.self_of_nhds, h3.self_of_nhds]
    simp
  have hprod : deriv φ (ψ z) * deriv ψ z = 1 := by
    rw [← (deriv_comp_three hAo hBo hφ hψ hψA hz).1, h1.self_of_nhds]
    simp
  have hφ0 : deriv φ (ψ z) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hψ0 : deriv ψ z ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hc := dlmf_1_13_21 hAo hBo hφ hψ hψA hz hφ0 hψ0
  rw [hS] at hc
  linear_combination (-(deriv φ (ψ z) ^ 2)) * hc +
    (-(schwarzian φ (ψ z)) * (deriv φ (ψ z) * deriv ψ z + 1)) * hprod

end Azurite.DLMF
