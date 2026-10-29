/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section13Change

/-!
# DLMF §1.13(v): Products of Solutions

Formalizations of <https://dlmf.nist.gov/1.13#v>.

**Results.**
* `deriv_three_mul`: the first three derivatives of `U V` when `U″ = −(a U′ + b U)` and
  `V″ = −(c V′ + d V)`.
* 1.13.23: the product of any two solutions of (1.13.1) solves
  `w‴ + 3f w″ + (2f² + f′ + 4g) w′ + (4fg + 2g′) w = 0` (`dlmf_1_13_23`).
* 1.13.24–1.13.25: if `U″ + I U = 0`, `V″ + J V = 0` and `I ≠ J`, then `W = U V` satisfies
  `(d/dz)((W‴ + 2(I + J) W′ + (I′ + J′) W)/(I − J)) = −(I − J) W` (`dlmf_1_13_25`); the quotient
  is `U′V − UV′` (`dlmf_1_13_25_quotient`).
-/

open Filter Topology Set Complex

namespace Azurite.DLMF

variable {D : Set ℂ}

/-- The first three derivatives of a product of solutions of two second-order equations. -/
theorem deriv_three_mul (hDo : IsOpen D) {U V U1 V1 a b c d : ℂ → ℂ}
    (hU : ∀ z ∈ D, HasDerivAt U (U1 z) z ∧ HasDerivAt U1 (-(a z * U1 z + b z * U z)) z)
    (hV : ∀ z ∈ D, HasDerivAt V (V1 z) z ∧ HasDerivAt V1 (-(c z * V1 z + d z * V z)) z)
    (ha : DifferentiableOn ℂ a D) (hb : DifferentiableOn ℂ b D) (hc : DifferentiableOn ℂ c D)
    (hd : DifferentiableOn ℂ d D) {z : ℂ} (hz : z ∈ D) :
    deriv (fun z => U z * V z) z = U1 z * V z + U z * V1 z ∧
    deriv (deriv (fun z => U z * V z)) z =
      -(a z * U1 z + b z * U z) * V z + 2 * U1 z * V1 z + U z * -(c z * V1 z + d z * V z) ∧
    deriv (deriv (deriv (fun z => U z * V z))) z =
      -(deriv a z * U1 z + a z * -(a z * U1 z + b z * U z) + deriv b z * U z + b z * U1 z) * V z
        - (a z * U1 z + b z * U z) * V1 z
        + 2 * (-(a z * U1 z + b z * U z) * V1 z + U1 z * -(c z * V1 z + d z * V z))
        + U1 z * -(c z * V1 z + d z * V z)
        + U z * -(deriv c z * V1 z + c z * -(c z * V1 z + d z * V z) + deriv d z * V z +
          d z * V1 z) := by
  have dD := fun {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D) {x} (hx : x ∈ D) =>
    hasDerivAt_of_differentiableOn hDo hF hx
  have e1 : ∀ x ∈ D, HasDerivAt (fun z => U z * V z) (U1 x * V x + U x * V1 x) x :=
    fun x hx => (hU x hx).1.mul (hV x hx).1
  have e2 : ∀ x ∈ D, HasDerivAt (fun z => U1 z * V z + U z * V1 z)
      (-(a x * U1 x + b x * U x) * V x + 2 * U1 x * V1 x + U x * -(c x * V1 x + d x * V x)) x :=
    fun x hx => (((hU x hx).2.mul (hV x hx).1).add ((hU x hx).1.mul (hV x hx).2)).congr_deriv
      (by ring)
  have e1' : deriv (fun z => U z * V z) =ᶠ[𝓝 z] fun z => U1 z * V z + U z * V1 z := by
    filter_upwards [hDo.mem_nhds hz] with y hy using (e1 y hy).deriv
  have e2' : deriv (deriv (fun z => U z * V z)) =ᶠ[𝓝 z]
      fun x => -(a x * U1 x + b x * U x) * V x + 2 * U1 x * V1 x +
        U x * -(c x * V1 x + d x * V x) := by
    filter_upwards [hDo.mem_nhds hz] with y hy
    have : deriv (fun z => U z * V z) =ᶠ[𝓝 y] fun z => U1 z * V z + U z * V1 z := by
      filter_upwards [hDo.mem_nhds hy] with x hx using (e1 x hx).deriv
    rw [this.deriv_eq, (e2 y hy).deriv]
  obtain ⟨u0, u1⟩ := hU z hz
  obtain ⟨v0, v1⟩ := hV z hz
  have e3 : HasDerivAt (fun x => -(a x * U1 x + b x * U x) * V x + 2 * U1 x * V1 x +
      U x * -(c x * V1 x + d x * V x))
      (-(deriv a z * U1 z + a z * -(a z * U1 z + b z * U z) + deriv b z * U z + b z * U1 z) * V z
        - (a z * U1 z + b z * U z) * V1 z
        + 2 * (-(a z * U1 z + b z * U z) * V1 z + U1 z * -(c z * V1 z + d z * V z))
        + U1 z * -(c z * V1 z + d z * V z)
        + U z * -(deriv c z * V1 z + c z * -(c z * V1 z + d z * V z) + deriv d z * V z +
          d z * V1 z)) z :=
    (((((dD ha hz).mul u1).add ((dD hb hz).mul u0)).neg.mul v0).add
      (((u1.const_mul 2).mul v1)) |>.add (u0.mul ((((dD hc hz).mul v1).add
        ((dD hd hz).mul v0)).neg))).congr_deriv (by
          simp only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
          ring)
  exact ⟨(e1 z hz).deriv, e2'.self_of_nhds, by rw [e2'.deriv_eq, e3.deriv]⟩

/-- **DLMF (1.13.23)**: the product `w = w₁ w₂` of two solutions of (1.13.1) satisfies
`w‴ + 3f w″ + (2f² + f′ + 4g) w′ + (4fg + 2g′) w = 0`. -/
theorem dlmf_1_13_23 (hDo : IsOpen D) {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) {w₁ w₂ : ℂ → ℂ} (h₁ : IsODESolution D f g w₁)
    (h₂ : IsODESolution D f g w₂) {z : ℂ} (hz : z ∈ D) :
    deriv (deriv (deriv (fun z => w₁ z * w₂ z))) z +
      3 * f z * deriv (deriv (fun z => w₁ z * w₂ z)) z +
      (2 * f z ^ 2 + deriv f z + 4 * g z) * deriv (fun z => w₁ z * w₂ z) z +
      (4 * f z * g z + 2 * deriv g z) * (w₁ z * w₂ z) = 0 := by
  obtain ⟨d1, d2, d3⟩ := deriv_three_mul hDo (fun z hz => h₁.hasDerivAt hDo hz)
    (fun z hz => h₂.hasDerivAt hDo hz) hf hg hf hg hz
  rw [d1, d2, d3]
  ring

/-- `W‴ + 2(I + J) W′ + (I′ + J′) W = (I − J)(U′V − UV′)` for `W = U V`. -/
theorem dlmf_1_13_25_quotient (hDo : IsOpen D) {I J U V : ℂ → ℂ} (hI : DifferentiableOn ℂ I D)
    (hJ : DifferentiableOn ℂ J D) (hU : IsODESolution D (fun _ => 0) I U)
    (hV : IsODESolution D (fun _ => 0) J V) {z : ℂ} (hz : z ∈ D) :
    deriv (deriv (deriv (fun z => U z * V z))) z +
      2 * (I z + J z) * deriv (fun z => U z * V z) z + (deriv I z + deriv J z) * (U z * V z) =
      (I z - J z) * (deriv U z * V z - U z * deriv V z) := by
  obtain ⟨d1, -, d3⟩ := deriv_three_mul hDo (fun z hz => hU.hasDerivAt hDo hz)
    (fun z hz => hV.hasDerivAt hDo hz) (differentiableOn_const 0) hI (differentiableOn_const 0)
    hJ hz
  rw [d1, d3]
  simp only [deriv_const]
  ring

/-- **DLMF (1.13.24)–(1.13.25)**: if `U″ + I U = 0`, `V″ + J V = 0` and `I ≠ J` in `D`, then
`W = U V` satisfies `(d/dz)((W‴ + 2(I + J) W′ + (I′ + J′) W)/(I − J)) = −(I − J) W`. -/
theorem dlmf_1_13_25 (hDo : IsOpen D) {I J U V : ℂ → ℂ} (hI : DifferentiableOn ℂ I D)
    (hJ : DifferentiableOn ℂ J D) (hIJ : ∀ z ∈ D, I z ≠ J z)
    (hU : IsODESolution D (fun _ => 0) I U) (hV : IsODESolution D (fun _ => 0) J V) {z : ℂ}
    (hz : z ∈ D) :
    deriv (fun z => (deriv (deriv (deriv (fun z => U z * V z))) z +
      2 * (I z + J z) * deriv (fun z => U z * V z) z + (deriv I z + deriv J z) * (U z * V z)) /
        (I z - J z)) z = -(I z - J z) * (U z * V z) := by
  have heq : (fun z => (deriv (deriv (deriv (fun z => U z * V z))) z +
      2 * (I z + J z) * deriv (fun z => U z * V z) z + (deriv I z + deriv J z) * (U z * V z)) /
        (I z - J z)) =ᶠ[𝓝 z] fun z => deriv U z * V z - U z * deriv V z := by
    filter_upwards [hDo.mem_nhds hz] with y hy
    rw [dlmf_1_13_25_quotient hDo hI hJ hU hV hy]
    field_simp [sub_ne_zero.mpr (hIJ y hy)]
  obtain ⟨u0, u1⟩ := hU.hasDerivAt hDo hz
  obtain ⟨v0, v1⟩ := hV.hasDerivAt hDo hz
  have hQ : HasDerivAt (fun z => deriv U z * V z - U z * deriv V z)
      (-(0 * deriv U z + I z * U z) * V z + deriv U z * deriv V z -
        (deriv U z * deriv V z + U z * -(0 * deriv V z + J z * V z))) z :=
    (u1.mul v0).sub (u0.mul v1)
  rw [heq.deriv_eq, hQ.deriv]
  ring

end Azurite.DLMF
