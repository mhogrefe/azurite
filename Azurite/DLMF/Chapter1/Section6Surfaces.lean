/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section6

/-!
# DLMF §1.6(v): Surfaces and Integrals over Surfaces

Formalizations of <https://dlmf.nist.gov/1.6.v> (a companion to `Section6.lean`, which holds
§1.6(i)–(iv)).  A parametrized surface is a map `Φ : ℝ × ℝ → ℝ³` (points of `ℝ³` are
`Fin 3 → ℝ`, as in §1.6(i)) on an open set `D` of the `(u, v)` plane.

* 1.6.45 `surfaceParam`; 1.6.46–1.6.47 `tangentU`, `tangentV` (`DΦ(u₀, v₀)` applied to the
  coordinate directions), `tangentU_surfaceParam`, `tangentV_surfaceParam`, `dlmf_1_6_46`,
  `dlmf_1_6_47`, tangency `hasDerivAt_tangentU`, `hasDerivAt_tangentV`; smoothness
  `IsSmoothAt`, `IsSmoothSurface`; the normal `dlmf_1_6_v_normal`.
* 1.6.48 `surfaceArea`; 1.6.49 `dlmf_1_6_49`; independence of the parametrization
  (`cross_tangent_comp`: `T_u × T_v` scales by the Jacobian of a change of parameters,
  `surfaceIntegral_comp`, `dlmf_1_6_v_area_reparam`).
* 1.6.50 sphere `dlmf_1_6_50`; 1.6.51 graphs `dlmf_1_6_51`; 1.6.52–1.6.53 surfaces of
  revolution `dlmf_1_6_52`, `dlmf_1_6_53`.
* 1.6.54 `surfaceIntegral`; 1.6.55 `fluxIntegral`; orientation `IsOrientationPreserving`,
  `IsOrientationReversing`, `IsOrientable`; 1.6.56 `dlmf_1_6_56`, `dlmf_1_6_56_neg`.  A second
  parametrization of `S` is written `Φ ∘ ψ` for a one-to-one differentiable change of
  parameters `ψ`.
* 1.6.57 Stokes's theorem `dlmf_1_6_57` for `S = Φ(D)` with `D` the region bounded by a
  positively oriented closed piecewise-`C¹` curve `γ` and `Φ` of class `C²` near `D ∪ γ`; the
  boundary `∂S` is traversed by `Φ ∘ γ`.  The pull-back `(F ∘ Φ) · T_u du + (F ∘ Φ) · T_v dv`
  turns it into Green's theorem 1.6.44 (`dlmf_1_6_44_nhds`): `partialX_sub_partialY_pullback`,
  `lineIntegral2_pullback`.  Only single-chart surfaces are covered.
* 1.6.58 Gauss's theorem `dlmf_1_6_58` and Green's theorem for volume 1.6.59–1.6.60
  (`dlmf_1_6_59`, `dlmf_1_6_60`) for boxes `V = [a, b] ⊂ ℝ³` (`boxFace`, `boxFlux`,
  `boxNormalDerivIntegral`), from Mathlib's divergence theorem on boxes.  Bounded regions with
  a closed piecewise smooth boundary: `Section6Gauss.lean`, `Section6GaussOrientation.lean`.
-/

namespace Azurite.DLMF

open Matrix MeasureTheory Set

/-! ### Parametrized surfaces and tangent vectors -/

/-- **DLMF 1.6.45**: the parametrized surface `Φ(u, v) = (x(u, v), y(u, v), z(u, v))`. -/
def surfaceParam (x y z : ℝ → ℝ → ℝ) : ℝ × ℝ → Fin 3 → ℝ :=
  fun p => ![x p.1 p.2, y p.1 p.2, z p.1 p.2]

/-- The tangent vector `T_u = ∂Φ/∂u` at `p` (DLMF 1.6.46). -/
noncomputable def tangentU (Φ : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  fderiv ℝ Φ p (1, 0)

/-- The tangent vector `T_v = ∂Φ/∂v` at `p` (DLMF 1.6.47). -/
noncomputable def tangentV (Φ : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  fderiv ℝ Φ p (0, 1)

theorem fderiv_apply_component {Φ : ℝ × ℝ → Fin 3 → ℝ} {p : ℝ × ℝ}
    (hΦ : DifferentiableAt ℝ Φ p) (k : Fin 3) (w : ℝ × ℝ) :
    fderiv ℝ Φ p w k = fderiv ℝ (fun q => Φ q k) p w := by
  rw [((hasFDerivAt_pi'.mp hΦ.hasFDerivAt) k).fderiv]
  rfl

theorem differentiableAt_surfaceParam {x y z : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hx : DifferentiableAt ℝ (Function.uncurry x) p)
    (hy : DifferentiableAt ℝ (Function.uncurry y) p)
    (hz : DifferentiableAt ℝ (Function.uncurry z) p) :
    DifferentiableAt ℝ (surfaceParam x y z) p := by
  refine differentiableAt_pi.mpr fun k => ?_
  fin_cases k
  exacts [hx, hy, hz]

/-- `T_u = (∂x/∂u, ∂y/∂u, ∂z/∂u)`. -/
theorem tangentU_surfaceParam {x y z : ℝ → ℝ → ℝ} {u v : ℝ}
    (hx : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hy : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hz : DifferentiableAt ℝ (Function.uncurry z) (u, v)) :
    tangentU (surfaceParam x y z) (u, v) =
      ![partialX x u v, partialX y u v, partialX z u v] := by
  have hΦ := differentiableAt_surfaceParam hx hy hz
  ext k
  rw [tangentU, fderiv_apply_component hΦ]
  fin_cases k
  · exact (partialX_of_hasFDerivAt hx.hasFDerivAt).symm
  · exact (partialX_of_hasFDerivAt hy.hasFDerivAt).symm
  · exact (partialX_of_hasFDerivAt hz.hasFDerivAt).symm

/-- `T_v = (∂x/∂v, ∂y/∂v, ∂z/∂v)`. -/
theorem tangentV_surfaceParam {x y z : ℝ → ℝ → ℝ} {u v : ℝ}
    (hx : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hy : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hz : DifferentiableAt ℝ (Function.uncurry z) (u, v)) :
    tangentV (surfaceParam x y z) (u, v) =
      ![partialY x u v, partialY y u v, partialY z u v] := by
  have hΦ := differentiableAt_surfaceParam hx hy hz
  ext k
  rw [tangentV, fderiv_apply_component hΦ]
  fin_cases k
  · exact (partialY_of_hasFDerivAt hx.hasFDerivAt).symm
  · exact (partialY_of_hasFDerivAt hy.hasFDerivAt).symm
  · exact (partialY_of_hasFDerivAt hz.hasFDerivAt).symm

/-- **DLMF 1.6.46**: `T_u = (∂x/∂u) i + (∂y/∂u) j + (∂z/∂u) k` at `(u₀, v₀)`. -/
theorem dlmf_1_6_46 {x y z : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hx : DifferentiableAt ℝ (Function.uncurry x) (u₀, v₀))
    (hy : DifferentiableAt ℝ (Function.uncurry y) (u₀, v₀))
    (hz : DifferentiableAt ℝ (Function.uncurry z) (u₀, v₀)) :
    tangentU (surfaceParam x y z) (u₀, v₀) =
      partialX x u₀ v₀ • unitI + partialX y u₀ v₀ • unitJ + partialX z u₀ v₀ • unitK := by
  rw [tangentU_surfaceParam hx hy hz]
  ext k
  fin_cases k <;> simp [unitI, unitJ, unitK]

/-- **DLMF 1.6.47**: `T_v = (∂x/∂v) i + (∂y/∂v) j + (∂z/∂v) k` at `(u₀, v₀)`. -/
theorem dlmf_1_6_47 {x y z : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hx : DifferentiableAt ℝ (Function.uncurry x) (u₀, v₀))
    (hy : DifferentiableAt ℝ (Function.uncurry y) (u₀, v₀))
    (hz : DifferentiableAt ℝ (Function.uncurry z) (u₀, v₀)) :
    tangentV (surfaceParam x y z) (u₀, v₀) =
      partialY x u₀ v₀ • unitI + partialY y u₀ v₀ • unitJ + partialY z u₀ v₀ • unitK := by
  rw [tangentV_surfaceParam hx hy hz]
  ext k
  fin_cases k <;> simp [unitI, unitJ, unitK]

/-- **DLMF §1.6(v)**: `T_u` is tangent to the surface: it is the velocity of the curve
`u ↦ Φ(u, v₀)`. -/
theorem hasDerivAt_tangentU {Φ : ℝ × ℝ → Fin 3 → ℝ} {u₀ v₀ : ℝ}
    (hΦ : DifferentiableAt ℝ Φ (u₀, v₀)) :
    HasDerivAt (fun u => Φ (u, v₀)) (tangentU Φ (u₀, v₀)) u₀ :=
  hΦ.hasFDerivAt.comp_hasDerivAt u₀ ((hasDerivAt_id u₀).prodMk (hasDerivAt_const u₀ v₀))

/-- **DLMF §1.6(v)**: `T_v` is the velocity of the curve `v ↦ Φ(u₀, v)`. -/
theorem hasDerivAt_tangentV {Φ : ℝ × ℝ → Fin 3 → ℝ} {u₀ v₀ : ℝ}
    (hΦ : DifferentiableAt ℝ Φ (u₀, v₀)) :
    HasDerivAt (fun v => Φ (u₀, v)) (tangentV Φ (u₀, v₀)) v₀ :=
  hΦ.hasFDerivAt.comp_hasDerivAt v₀ ((hasDerivAt_const v₀ u₀).prodMk (hasDerivAt_id v₀))

/-- **DLMF §1.6(v)**: the surface is smooth at `Φ(u₀, v₀)` if `T_u × T_v ≠ 0`. -/
def IsSmoothAt (Φ : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Prop :=
  tangentU Φ p ⨯₃ tangentV Φ p ≠ 0

/-- **DLMF §1.6(v)**: a surface is smooth if it is smooth at every point. -/
def IsSmoothSurface (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ D, IsSmoothAt Φ p

/-- **DLMF §1.6(v)**: `T_u × T_v` is normal to the surface (orthogonal to both tangents). -/
theorem dlmf_1_6_v_normal (Φ : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) :
    (tangentU Φ p ⨯₃ tangentV Φ p) ⬝ᵥ tangentU Φ p = 0 ∧
      (tangentU Φ p ⨯₃ tangentV Φ p) ⬝ᵥ tangentV Φ p = 0 := by
  rw [dotProduct_comm, dotProduct_comm _ (tangentV Φ p)]
  exact ⟨dot_self_cross _ _, dot_cross_self _ _⟩

/-! ### Area and integrals over surfaces -/

/-- **DLMF 1.6.48**: the area `A(S) = ∬_D ‖T_u × T_v‖ du dv`. -/
noncomputable def surfaceArea (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, vnorm (tangentU Φ p ⨯₃ tangentV Φ p)

/-- **DLMF 1.6.54**: `∬_S f dS = ∬_D f(Φ(u, v)) ‖T_u × T_v‖ du dv`. -/
noncomputable def surfaceIntegral (f : (Fin 3 → ℝ) → ℝ) (Φ : ℝ × ℝ → Fin 3 → ℝ)
    (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, f (Φ p) * vnorm (tangentU Φ p ⨯₃ tangentV Φ p)

/-- **DLMF 1.6.55**: `∬_S F · dS = ∬_D F · (T_u × T_v) du dv`. -/
noncomputable def fluxIntegral (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (Φ : ℝ × ℝ → Fin 3 → ℝ)
    (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, F (Φ p) ⬝ᵥ (tangentU Φ p ⨯₃ tangentV Φ p)

theorem dlmf_1_6_48 (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) :
    surfaceArea Φ D = ∫ p in D, vnorm (tangentU Φ p ⨯₃ tangentV Φ p) := rfl

theorem dlmf_1_6_54 (f : (Fin 3 → ℝ) → ℝ) (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) :
    surfaceIntegral f Φ D = ∫ p in D, f (Φ p) * vnorm (tangentU Φ p ⨯₃ tangentV Φ p) := rfl

theorem dlmf_1_6_55 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (Φ : ℝ × ℝ → Fin 3 → ℝ)
    (D : Set (ℝ × ℝ)) :
    fluxIntegral F Φ D = ∫ p in D, F (Φ p) ⬝ᵥ (tangentU Φ p ⨯₃ tangentV Φ p) := rfl

/-- The area is the surface integral of `1`. -/
theorem surfaceArea_eq_surfaceIntegral (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) :
    surfaceArea Φ D = surfaceIntegral (fun _ => 1) Φ D := by
  simp [surfaceArea, surfaceIntegral]

/-- **DLMF 1.6.49**: `‖T_u × T_v‖ = √((∂(x,y)/∂(u,v))² + (∂(y,z)/∂(u,v))² + (∂(x,z)/∂(u,v))²)`. -/
theorem dlmf_1_6_49 {x y z : ℝ → ℝ → ℝ} {u v : ℝ}
    (hx : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hy : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hz : DifferentiableAt ℝ (Function.uncurry z) (u, v)) :
    vnorm (tangentU (surfaceParam x y z) (u, v) ⨯₃ tangentV (surfaceParam x y z) (u, v)) =
      √(jacobian2 x y u v ^ 2 + jacobian2 y z u v ^ 2 + jacobian2 x z u v ^ 2) := by
  rw [tangentU_surfaceParam hx hy hz, tangentV_surfaceParam hx hy hz, vnorm,
    dlmf_1_5_38, dlmf_1_5_38, dlmf_1_5_38]
  congr 1
  simp only [cross_apply, dotProduct, Fin.sum_univ_three]
  simp
  ring

/-! ### Independence of the parametrization -/

theorem clm_apply_prod (L : ℝ × ℝ →L[ℝ] (Fin 3 → ℝ)) (w : ℝ × ℝ) :
    L w = w.1 • L (1, 0) + w.2 • L (0, 1) := by
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

/-- Under a change of parameters `ψ`, `T_u × T_v` is multiplied by the Jacobian `det Dψ`. -/
theorem cross_tangent_comp {Φ : ℝ × ℝ → Fin 3 → ℝ} {ψ : ℝ × ℝ → ℝ × ℝ} {p : ℝ × ℝ}
    (hΦ : DifferentiableAt ℝ Φ (ψ p)) (hψ : DifferentiableAt ℝ ψ p) :
    tangentU (Φ ∘ ψ) p ⨯₃ tangentV (Φ ∘ ψ) p =
      (fderiv ℝ ψ p).det • (tangentU Φ (ψ p) ⨯₃ tangentV Φ (ψ p)) := by
  have hc : fderiv ℝ (Φ ∘ ψ) p = (fderiv ℝ Φ (ψ p)).comp (fderiv ℝ ψ p) := fderiv_comp p hΦ hψ
  simp only [tangentU, tangentV, hc, ContinuousLinearMap.comp_apply]
  rw [clm_apply_prod (fderiv ℝ Φ (ψ p)) (fderiv ℝ ψ p (1, 0)),
    clm_apply_prod (fderiv ℝ Φ (ψ p)) (fderiv ℝ ψ p (0, 1)),
    ContinuousLinearMap.det_prod_two]
  ext k
  fin_cases k <;> simp [cross_apply] <;> ring

/-- Surface integrals do not depend on the parametrization: for a change of parameters `ψ`,
one-to-one and differentiable on `D₂`, `∬ f dS` over `Φ ∘ ψ` on `D₂` equals that over `Φ` on
`ψ(D₂)`. -/
theorem surfaceIntegral_comp {Φ : ℝ × ℝ → Fin 3 → ℝ} {ψ : ℝ × ℝ → ℝ × ℝ} {D₂ : Set (ℝ × ℝ)}
    (hD₂ : MeasurableSet D₂) (hψ : ∀ p ∈ D₂, DifferentiableAt ℝ ψ p) (hinj : InjOn ψ D₂)
    (hΦ : ∀ p ∈ D₂, DifferentiableAt ℝ Φ (ψ p)) (f : (Fin 3 → ℝ) → ℝ) :
    surfaceIntegral f (Φ ∘ ψ) D₂ = surfaceIntegral f Φ (ψ '' D₂) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [surfaceIntegral, surfaceIntegral, integral_image_eq_integral_abs_det_fderiv_smul volume hD₂
    (fun p hp => (hψ p hp).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setIntegral_congr_fun hD₂ fun p hp => ?_
  simp only [cross_tangent_comp (hΦ p hp) (hψ p hp), vnorm_smul, Function.comp_apply,
    smul_eq_mul]
  ring

/-- **DLMF §1.6(v)**: the area is independent of the parametrization. -/
theorem dlmf_1_6_v_area_reparam {Φ : ℝ × ℝ → Fin 3 → ℝ} {ψ : ℝ × ℝ → ℝ × ℝ}
    {D₂ : Set (ℝ × ℝ)} (hD₂ : MeasurableSet D₂) (hψ : ∀ p ∈ D₂, DifferentiableAt ℝ ψ p)
    (hinj : InjOn ψ D₂) (hΦ : ∀ p ∈ D₂, DifferentiableAt ℝ Φ (ψ p)) :
    surfaceArea (Φ ∘ ψ) D₂ = surfaceArea Φ (ψ '' D₂) := by
  rw [surfaceArea_eq_surfaceIntegral, surfaceArea_eq_surfaceIntegral,
    surfaceIntegral_comp hD₂ hψ hinj hΦ]

/-- Flux integrals under a change of parameters: the Jacobian appears with its sign. -/
theorem fluxIntegral_comp {Φ : ℝ × ℝ → Fin 3 → ℝ} {ψ : ℝ × ℝ → ℝ × ℝ} {D₂ : Set (ℝ × ℝ)}
    (hD₂ : MeasurableSet D₂) (hψ : ∀ p ∈ D₂, DifferentiableAt ℝ ψ p) (hinj : InjOn ψ D₂)
    (hΦ : ∀ p ∈ D₂, DifferentiableAt ℝ Φ (ψ p)) (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) :
    fluxIntegral F Φ (ψ '' D₂) =
      ∫ p in D₂, |(fderiv ℝ ψ p).det| * (F (Φ (ψ p)) ⬝ᵥ
        (tangentU Φ (ψ p) ⨯₃ tangentV Φ (ψ p))) ∧
    fluxIntegral F (Φ ∘ ψ) D₂ =
      ∫ p in D₂, (fderiv ℝ ψ p).det * (F (Φ (ψ p)) ⬝ᵥ
        (tangentU Φ (ψ p) ⨯₃ tangentV Φ (ψ p))) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  constructor
  · rw [fluxIntegral, integral_image_eq_integral_abs_det_fderiv_smul volume hD₂
      (fun p hp => (hψ p hp).hasFDerivAt.hasFDerivWithinAt) hinj]
    rfl
  · refine setIntegral_congr_fun hD₂ fun p hp => ?_
    simp only [cross_tangent_comp (hΦ p hp) (hψ p hp), Function.comp_apply, dotProduct_smul,
      smul_eq_mul]

/-! ### Orientation -/

/-- **DLMF §1.6(v)**: `Φ` is orientation preserving for the normal field `N` if `T_u × T_v` is a
positive multiple of `N` at each point. -/
def IsOrientationPreserving (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ))
    (N : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  ∀ p ∈ D, ∃ r : ℝ, 0 < r ∧ tangentU Φ p ⨯₃ tangentV Φ p = r • N (Φ p)

/-- **DLMF §1.6(v)**: `Φ` is orientation reversing if `T_u × T_v` is a negative multiple of `N`. -/
def IsOrientationReversing (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ))
    (N : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  ∀ p ∈ D, ∃ r : ℝ, r < 0 ∧ tangentU Φ p ⨯₃ tangentV Φ p = r • N (Φ p)

/-- **DLMF §1.6(v)**: a surface is orientable if it has a continuous unit normal field. -/
def IsOrientable (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ∃ N : (Fin 3 → ℝ) → (Fin 3 → ℝ), ContinuousOn N (Φ '' D) ∧
    (∀ p ∈ D, vnorm (N (Φ p)) = 1) ∧ IsOrientationPreserving Φ D N

/-- The sign of the Jacobian of the change of parameters between two parametrizations that
agree or disagree with a normal field. -/
theorem det_pos_or_neg {Φ : ℝ × ℝ → Fin 3 → ℝ} {ψ : ℝ × ℝ → ℝ × ℝ} {p : ℝ × ℝ}
    {N : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hΦ : DifferentiableAt ℝ Φ (ψ p))
    (hψ : DifferentiableAt ℝ ψ p) (hs : IsSmoothAt (Φ ∘ ψ) p) {r₁ r₂ : ℝ}
    (h₁ : tangentU Φ (ψ p) ⨯₃ tangentV Φ (ψ p) = r₁ • N (Φ (ψ p)))
    (h₂ : tangentU (Φ ∘ ψ) p ⨯₃ tangentV (Φ ∘ ψ) p = r₂ • N (Φ (ψ p))) :
    r₂ = (fderiv ℝ ψ p).det * r₁ := by
  have hN : N (Φ (ψ p)) ≠ 0 := fun h0 => hs (by rw [h₂, h0, smul_zero])
  rw [cross_tangent_comp hΦ hψ, h₁, smul_smul] at h₂
  exact (smul_left_injective ℝ hN h₂).symm

/-- **DLMF 1.6.56**: two parametrizations of an oriented surface that are both orientation
preserving (or both orientation reversing) give the same flux integral.  The second
parametrization is `Φ ∘ ψ` for a one-to-one differentiable change of parameters `ψ`. -/
theorem dlmf_1_6_56 {Φ : ℝ × ℝ → Fin 3 → ℝ} {ψ : ℝ × ℝ → ℝ × ℝ} {D₂ : Set (ℝ × ℝ)}
    {N : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hD₂ : MeasurableSet D₂)
    (hψ : ∀ p ∈ D₂, DifferentiableAt ℝ ψ p) (hinj : InjOn ψ D₂)
    (hΦ : ∀ p ∈ D₂, DifferentiableAt ℝ Φ (ψ p)) (hs : IsSmoothSurface (Φ ∘ ψ) D₂)
    (horient : (IsOrientationPreserving Φ (ψ '' D₂) N ∧ IsOrientationPreserving (Φ ∘ ψ) D₂ N) ∨
      (IsOrientationReversing Φ (ψ '' D₂) N ∧ IsOrientationReversing (Φ ∘ ψ) D₂ N))
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) :
    fluxIntegral F (Φ ∘ ψ) D₂ = fluxIntegral F Φ (ψ '' D₂) := by
  obtain ⟨h1, h2⟩ := fluxIntegral_comp hD₂ hψ hinj hΦ F
  rw [h1, h2]
  refine setIntegral_congr_fun hD₂ fun p hp => ?_
  have hdet : 0 < (fderiv ℝ ψ p).det := by
    rcases horient with ⟨ho₁, ho₂⟩ | ⟨ho₁, ho₂⟩
    · obtain ⟨r₁, hr₁, e₁⟩ := ho₁ (ψ p) (mem_image_of_mem ψ hp)
      obtain ⟨r₂, hr₂, e₂⟩ := ho₂ p hp
      have := det_pos_or_neg (hΦ p hp) (hψ p hp) (hs p hp) e₁ e₂
      nlinarith
    · obtain ⟨r₁, hr₁, e₁⟩ := ho₁ (ψ p) (mem_image_of_mem ψ hp)
      obtain ⟨r₂, hr₂, e₂⟩ := ho₂ p hp
      have := det_pos_or_neg (hΦ p hp) (hψ p hp) (hs p hp) e₁ e₂
      nlinarith
  rw [abs_of_pos hdet]

/-- **DLMF 1.6.56** (otherwise): if one parametrization preserves and the other reverses the
orientation, the flux integrals are negatives of each other. -/
theorem dlmf_1_6_56_neg {Φ : ℝ × ℝ → Fin 3 → ℝ} {ψ : ℝ × ℝ → ℝ × ℝ} {D₂ : Set (ℝ × ℝ)}
    {N : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hD₂ : MeasurableSet D₂)
    (hψ : ∀ p ∈ D₂, DifferentiableAt ℝ ψ p) (hinj : InjOn ψ D₂)
    (hΦ : ∀ p ∈ D₂, DifferentiableAt ℝ Φ (ψ p)) (hs : IsSmoothSurface (Φ ∘ ψ) D₂)
    (horient : (IsOrientationPreserving Φ (ψ '' D₂) N ∧ IsOrientationReversing (Φ ∘ ψ) D₂ N) ∨
      (IsOrientationReversing Φ (ψ '' D₂) N ∧ IsOrientationPreserving (Φ ∘ ψ) D₂ N))
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) :
    fluxIntegral F (Φ ∘ ψ) D₂ = -fluxIntegral F Φ (ψ '' D₂) := by
  obtain ⟨h1, h2⟩ := fluxIntegral_comp hD₂ hψ hinj hΦ F
  rw [h1, h2, ← integral_neg]
  refine setIntegral_congr_fun hD₂ fun p hp => ?_
  have hdet : (fderiv ℝ ψ p).det < 0 := by
    rcases horient with ⟨ho₁, ho₂⟩ | ⟨ho₁, ho₂⟩
    · obtain ⟨r₁, hr₁, e₁⟩ := ho₁ (ψ p) (mem_image_of_mem ψ hp)
      obtain ⟨r₂, hr₂, e₂⟩ := ho₂ p hp
      have := det_pos_or_neg (hΦ p hp) (hψ p hp) (hs p hp) e₁ e₂
      nlinarith
    · obtain ⟨r₁, hr₁, e₁⟩ := ho₁ (ψ p) (mem_image_of_mem ψ hp)
      obtain ⟨r₂, hr₂, e₂⟩ := ho₂ p hp
      have := det_pos_or_neg (hΦ p hp) (hψ p hp) (hs p hp) e₁ e₂
      nlinarith
  rw [abs_of_neg hdet]
  ring

/-! ### Spheres, graphs and surfaces of revolution -/

/-- The sphere of radius `ρ`: `x = ρ sin θ cos φ`, `y = ρ sin θ sin φ`, `z = ρ cos θ`. -/
noncomputable def sphereParam (ρ : ℝ) : ℝ × ℝ → Fin 3 → ℝ :=
  surfaceParam (fun θ φ => ρ * Real.sin θ * Real.cos φ) (fun θ φ => ρ * Real.sin θ * Real.sin φ)
    (fun θ _ => ρ * Real.cos θ)

/-- **DLMF 1.6.50**: for the sphere, `‖T_θ × T_φ‖ = ρ² |sin θ|`. -/
theorem dlmf_1_6_50 (ρ θ φ : ℝ) :
    vnorm (tangentU (sphereParam ρ) (θ, φ) ⨯₃ tangentV (sphereParam ρ) (θ, φ)) =
      ρ ^ 2 * |Real.sin θ| := by
  have hx : DifferentiableAt ℝ
      (Function.uncurry fun θ φ => ρ * Real.sin θ * Real.cos φ) (θ, φ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => ρ * Real.sin p.1 * Real.cos p.2) (θ, φ)
    fun_prop
  have hy : DifferentiableAt ℝ
      (Function.uncurry fun θ φ => ρ * Real.sin θ * Real.sin φ) (θ, φ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => ρ * Real.sin p.1 * Real.sin p.2) (θ, φ)
    fun_prop
  have hz : DifferentiableAt ℝ (Function.uncurry fun θ (_ : ℝ) => ρ * Real.cos θ) (θ, φ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => ρ * Real.cos p.1) (θ, φ)
    fun_prop
  rw [sphereParam, tangentU_surfaceParam hx hy hz, tangentV_surfaceParam hx hy hz]
  have a1 : partialX (fun θ φ => ρ * Real.sin θ * Real.cos φ) θ φ =
      ρ * Real.cos θ * Real.cos φ :=
    (((Real.hasDerivAt_sin θ).const_mul ρ).mul_const (Real.cos φ)).deriv
  have a2 : partialY (fun θ φ => ρ * Real.sin θ * Real.cos φ) θ φ =
      ρ * Real.sin θ * -Real.sin φ :=
    ((Real.hasDerivAt_cos φ).const_mul (ρ * Real.sin θ)).deriv
  have b1 : partialX (fun θ φ => ρ * Real.sin θ * Real.sin φ) θ φ =
      ρ * Real.cos θ * Real.sin φ :=
    (((Real.hasDerivAt_sin θ).const_mul ρ).mul_const (Real.sin φ)).deriv
  have b2 : partialY (fun θ φ => ρ * Real.sin θ * Real.sin φ) θ φ =
      ρ * Real.sin θ * Real.cos φ :=
    ((Real.hasDerivAt_sin φ).const_mul (ρ * Real.sin θ)).deriv
  have c1 : partialX (fun θ (_ : ℝ) => ρ * Real.cos θ) θ φ = ρ * -Real.sin θ :=
    ((Real.hasDerivAt_cos θ).const_mul ρ).deriv
  have c2 : partialY (fun θ (_ : ℝ) => ρ * Real.cos θ) θ φ = 0 :=
    deriv_const φ (ρ * Real.cos θ)
  rw [a1, a2, b1, b2, c1, c2, vnorm]
  have hdot : (![ρ * Real.cos θ * Real.cos φ, ρ * Real.cos θ * Real.sin φ, ρ * -Real.sin θ] ⨯₃
      ![ρ * Real.sin θ * -Real.sin φ, ρ * Real.sin θ * Real.cos φ, 0]) ⬝ᵥ
      (![ρ * Real.cos θ * Real.cos φ, ρ * Real.cos θ * Real.sin φ, ρ * -Real.sin θ] ⨯₃
      ![ρ * Real.sin θ * -Real.sin φ, ρ * Real.sin θ * Real.cos φ, 0]) =
      (ρ ^ 2 * Real.sin θ) ^ 2 := by
    simp only [cross_apply, dotProduct, Fin.sum_univ_three]
    simp
    linear_combination (ρ ^ 4 * Real.sin θ ^ 4 + ρ ^ 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2 *
      (Real.sin φ ^ 2 + Real.cos φ ^ 2 + 1)) * Real.sin_sq_add_cos_sq φ +
      ρ ^ 4 * Real.sin θ ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [hdot, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ρ)]

/-- The graph `z = f(x, y)` as a parametrized surface. -/
def graphParam (f : ℝ → ℝ → ℝ) : ℝ × ℝ → Fin 3 → ℝ :=
  surfaceParam (fun x _ => x) (fun _ y => y) f

theorem vnorm_cross_graphParam {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    vnorm (tangentU (graphParam f) (x, y) ⨯₃ tangentV (graphParam f) (x, y)) =
      √(1 + partialX f x y ^ 2 + partialY f x y ^ 2) := by
  have hx : DifferentiableAt ℝ (Function.uncurry fun (x : ℝ) (_ : ℝ) => x) (x, y) :=
    differentiableAt_fst
  have hy : DifferentiableAt ℝ (Function.uncurry fun (_ : ℝ) (y : ℝ) => y) (x, y) :=
    differentiableAt_snd
  rw [graphParam, tangentU_surfaceParam hx hy hf, tangentV_surfaceParam hx hy hf, vnorm]
  have a1 : partialX (fun (x : ℝ) (_ : ℝ) => x) x y = 1 := deriv_id x
  have a2 : partialY (fun (x : ℝ) (_ : ℝ) => x) x y = 0 := deriv_const y x
  have b1 : partialX (fun (_ : ℝ) (y : ℝ) => y) x y = 0 := deriv_const x y
  have b2 : partialY (fun (_ : ℝ) (y : ℝ) => y) x y = 1 := deriv_id y
  rw [a1, a2, b1, b2]
  congr 1
  simp only [cross_apply, dotProduct, Fin.sum_univ_three]
  simp
  ring

/-- **DLMF 1.6.51**: the area of the graph `z = f(x, y)` over `D` is
`∬_D √(1 + (∂f/∂x)² + (∂f/∂y)²) dA`. -/
theorem dlmf_1_6_51 {f : ℝ → ℝ → ℝ} {D : Set (ℝ × ℝ)} (hD : MeasurableSet D)
    (hf : ∀ p ∈ D, DifferentiableAt ℝ (Function.uncurry f) p) :
    surfaceArea (graphParam f) D =
      ∫ p in D, √(1 + partialX f p.1 p.2 ^ 2 + partialY f p.1 p.2 ^ 2) := by
  refine setIntegral_congr_fun hD fun p hp => ?_
  exact vnorm_cross_graphParam (hf p hp)

/-- The surface of revolution of `y = f(x)` about the `x`-axis. -/
noncomputable def revolutionXParam (f : ℝ → ℝ) : ℝ × ℝ → Fin 3 → ℝ :=
  surfaceParam (fun x _ => x) (fun x θ => f x * Real.cos θ) (fun x θ => f x * Real.sin θ)

/-- The surface of revolution of `y = f(x)` about the `y`-axis. -/
noncomputable def revolutionYParam (f : ℝ → ℝ) : ℝ × ℝ → Fin 3 → ℝ :=
  surfaceParam (fun x θ => x * Real.cos θ) (fun x _ => f x) (fun x θ => x * Real.sin θ)

theorem vnorm_cross_revolutionXParam {f : ℝ → ℝ} {x θ : ℝ} (hf : DifferentiableAt ℝ f x) :
    vnorm (tangentU (revolutionXParam f) (x, θ) ⨯₃ tangentV (revolutionXParam f) (x, θ)) =
      |f x| * √(1 + deriv f x ^ 2) := by
  have hx : DifferentiableAt ℝ (Function.uncurry fun (x : ℝ) (_ : ℝ) => x) (x, θ) :=
    differentiableAt_fst
  have hy : DifferentiableAt ℝ (Function.uncurry fun x θ => f x * Real.cos θ) (x, θ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 * Real.cos p.2) (x, θ)
    exact (hf.comp (x, θ) differentiableAt_fst).mul
      ((Real.differentiable_cos _).comp (x, θ) differentiableAt_snd)
  have hz : DifferentiableAt ℝ (Function.uncurry fun x θ => f x * Real.sin θ) (x, θ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 * Real.sin p.2) (x, θ)
    exact (hf.comp (x, θ) differentiableAt_fst).mul
      ((Real.differentiable_sin _).comp (x, θ) differentiableAt_snd)
  rw [revolutionXParam, tangentU_surfaceParam hx hy hz, tangentV_surfaceParam hx hy hz, vnorm]
  have a1 : partialX (fun (x : ℝ) (_ : ℝ) => x) x θ = 1 := deriv_id x
  have a2 : partialY (fun (x : ℝ) (_ : ℝ) => x) x θ = 0 := deriv_const θ x
  have b1 : partialX (fun x θ => f x * Real.cos θ) x θ = deriv f x * Real.cos θ :=
    (hf.hasDerivAt.mul_const (Real.cos θ)).deriv
  have b2 : partialY (fun x θ => f x * Real.cos θ) x θ = f x * -Real.sin θ :=
    ((Real.hasDerivAt_cos θ).const_mul (f x)).deriv
  have c1 : partialX (fun x θ => f x * Real.sin θ) x θ = deriv f x * Real.sin θ :=
    (hf.hasDerivAt.mul_const (Real.sin θ)).deriv
  have c2 : partialY (fun x θ => f x * Real.sin θ) x θ = f x * Real.cos θ :=
    ((Real.hasDerivAt_sin θ).const_mul (f x)).deriv
  rw [a1, a2, b1, b2, c1, c2]
  have hdot : (![1, deriv f x * Real.cos θ, deriv f x * Real.sin θ] ⨯₃
      ![0, f x * -Real.sin θ, f x * Real.cos θ]) ⬝ᵥ
      (![1, deriv f x * Real.cos θ, deriv f x * Real.sin θ] ⨯₃
      ![0, f x * -Real.sin θ, f x * Real.cos θ]) = f x ^ 2 * (1 + deriv f x ^ 2) := by
    simp only [cross_apply, dotProduct, Fin.sum_univ_three]
    simp
    linear_combination (f x ^ 2 * deriv f x ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2 + 1) +
      f x ^ 2) * Real.sin_sq_add_cos_sq θ
  rw [hdot, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem vnorm_cross_revolutionYParam {f : ℝ → ℝ} {x θ : ℝ} (hf : DifferentiableAt ℝ f x) :
    vnorm (tangentU (revolutionYParam f) (x, θ) ⨯₃ tangentV (revolutionYParam f) (x, θ)) =
      |x| * √(1 + deriv f x ^ 2) := by
  have hx : DifferentiableAt ℝ (Function.uncurry fun x θ => x * Real.cos θ) (x, θ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 * Real.cos p.2) (x, θ)
    fun_prop
  have hy : DifferentiableAt ℝ (Function.uncurry fun x (_ : ℝ) => f x) (x, θ) :=
    hf.comp (x, θ) differentiableAt_fst
  have hz : DifferentiableAt ℝ (Function.uncurry fun x θ => x * Real.sin θ) (x, θ) := by
    show DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 * Real.sin p.2) (x, θ)
    fun_prop
  rw [revolutionYParam, tangentU_surfaceParam hx hy hz, tangentV_surfaceParam hx hy hz, vnorm]
  have a1 : partialX (fun x θ => x * Real.cos θ) x θ = Real.cos θ :=
    ((hasDerivAt_id x).mul_const (Real.cos θ)).deriv.trans (one_mul _)
  have a2 : partialY (fun x θ => x * Real.cos θ) x θ = x * -Real.sin θ :=
    ((Real.hasDerivAt_cos θ).const_mul x).deriv
  have b1 : partialX (fun x (_ : ℝ) => f x) x θ = deriv f x := rfl
  have b2 : partialY (fun x (_ : ℝ) => f x) x θ = 0 := deriv_const θ (f x)
  have c1 : partialX (fun x θ => x * Real.sin θ) x θ = Real.sin θ :=
    ((hasDerivAt_id x).mul_const (Real.sin θ)).deriv.trans (one_mul _)
  have c2 : partialY (fun x θ => x * Real.sin θ) x θ = x * Real.cos θ :=
    ((Real.hasDerivAt_sin θ).const_mul x).deriv
  rw [a1, a2, b1, b2, c1, c2]
  have hdot : (![Real.cos θ, deriv f x, Real.sin θ] ⨯₃
      ![x * -Real.sin θ, 0, x * Real.cos θ]) ⬝ᵥ
      (![Real.cos θ, deriv f x, Real.sin θ] ⨯₃
      ![x * -Real.sin θ, 0, x * Real.cos θ]) = x ^ 2 * (1 + deriv f x ^ 2) := by
    simp only [cross_apply, dotProduct, Fin.sum_univ_three]
    simp
    linear_combination (x ^ 2 * deriv f x ^ 2 + x ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2 + 1)) *
      Real.sin_sq_add_cos_sq θ
  rw [hdot, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- Integrating a function of `x` alone over `(a, b) × (0, 2π)`. -/
theorem setIntegral_Ioo_prod_angle (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ p in Ioo a b ×ˢ Ioo 0 (2 * Real.pi), g p.1 = 2 * Real.pi * ∫ x in a..b, g x := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have h := integral_prod_mul (μ := volume.restrict (Ioo a b))
    (ν := volume.restrict (Ioo 0 (2 * Real.pi))) g (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo, integral_const,
    smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal (by positivity), mul_comm]

/-- **DLMF 1.6.52**: the surface of revolution of `y = f(x)`, `x ∈ [a, b]`, about the `x`-axis
has area `2π ∫_a^b |f(x)| √(1 + f'(x)²) dx` (parameters `(x, θ) ∈ (a, b) × (0, 2π)`). -/
theorem dlmf_1_6_52 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) :
    surfaceArea (revolutionXParam f) (Ioo a b ×ˢ Ioo 0 (2 * Real.pi)) =
      2 * Real.pi * ∫ x in a..b, |f x| * √(1 + deriv f x ^ 2) := by
  rw [← setIntegral_Ioo_prod_angle (fun x => |f x| * √(1 + deriv f x ^ 2)) hab]
  refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp => ?_
  exact vnorm_cross_revolutionXParam (hf p.1 hp.1)

/-- **DLMF 1.6.53**: about the `y`-axis the area is `2π ∫_a^b |x| √(1 + f'(x)²) dx`. -/
theorem dlmf_1_6_53 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) :
    surfaceArea (revolutionYParam f) (Ioo a b ×ˢ Ioo 0 (2 * Real.pi)) =
      2 * Real.pi * ∫ x in a..b, |x| * √(1 + deriv f x ^ 2) := by
  rw [← setIntegral_Ioo_prod_angle (fun x => |x| * √(1 + deriv f x ^ 2)) hab]
  refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp => ?_
  exact vnorm_cross_revolutionYParam (hf p.1 hp.1)

/-! ### Stokes's theorem -/

/-- Product rule for the dot product of two vector-valued functions of one variable. -/
theorem hasDerivAt_dotProduct {f g : ℝ → Fin 3 → ℝ} {f' g' : Fin 3 → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := by
  have hf' := hasDerivAt_pi.mp hf
  have hg' := hasDerivAt_pi.mp hg
  have h := HasDerivAt.sum (u := Finset.univ) fun k _ => (hf' k).mul (hg' k)
  simp only [dotProduct, ← Finset.sum_add_distrib]
  exact h

theorem fderiv_apply_component3 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F x) (k : Fin 3) (w : Fin 3 → ℝ) :
    fderiv ℝ F x w k = grad3 (fun q => F q k) x ⬝ᵥ w := by
  rw [← fderiv_apply_eq_grad, ((hasFDerivAt_pi'.mp hF.hasFDerivAt) k).fderiv]
  rfl

/-- `(DF a) · b − (DF b) · a = (∇ × F) · (a × b)`. -/
theorem dot_fderiv_sub {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F x) (a b : Fin 3 → ℝ) :
    fderiv ℝ F x a ⬝ᵥ b - fderiv ℝ F x b ⬝ᵥ a = curl3 F x ⬝ᵥ (a ⨯₃ b) := by
  have e : ∀ w : Fin 3 → ℝ, ∀ k, fderiv ℝ F x w k = grad3 (fun q => F q k) x ⬝ᵥ w :=
    fun w k => fderiv_apply_component3 hF k w
  simp only [dotProduct, Fin.sum_univ_three] at e ⊢
  simp only [e, grad3, curl3, cross_apply]
  simp
  ring

/-- The pulled-back curl: with `P₁ = (F ∘ Φ) · T_u` and `P₂ = (F ∘ Φ) · T_v`,
`∂P₂/∂u − ∂P₁/∂v = (∇ × F)(Φ) · (T_u × T_v)` for `Φ` of class `C²`. -/
theorem partialX_sub_partialY_pullback {Φ : ℝ × ℝ → Fin 3 → ℝ}
    {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {q : ℝ × ℝ} (hΦ : ContDiffAt ℝ 2 Φ q)
    (hF : Differentiable ℝ F) :
    partialX (fun u v => F (Φ (u, v)) ⬝ᵥ tangentV Φ (u, v)) q.1 q.2 -
      partialY (fun u v => F (Φ (u, v)) ⬝ᵥ tangentU Φ (u, v)) q.1 q.2 =
      curl3 F (Φ q) ⬝ᵥ (tangentU Φ q ⨯₃ tangentV Φ q) := by
  obtain ⟨u, v⟩ := q
  have hΦd : DifferentiableAt ℝ Φ (u, v) := hΦ.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ Φ) (u, v) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  set H := fderiv ℝ (fderiv ℝ Φ) (u, v) with hH
  have hsymm : H (1, 0) (0, 1) = H (0, 1) (1, 0) := hΦ.isSymmSndFDerivAt (by simp) _ _
  have hTv : HasDerivAt (fun t => tangentV Φ (t, v)) (H (1, 0) (0, 1)) u := by
    have h1 : HasDerivAt (fun t => fderiv ℝ Φ (t, v)) (H (1, 0)) u :=
      hD.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))
    have h2 := h1.clm_apply (hasDerivAt_const u ((0 : ℝ), (1 : ℝ)))
    simp only [map_zero, add_zero] at h2
    exact h2
  have hTu : HasDerivAt (fun t => tangentU Φ (u, t)) (H (0, 1) (1, 0)) v := by
    have h1 : HasDerivAt (fun t => fderiv ℝ Φ (u, t)) (H (0, 1)) v :=
      hD.hasFDerivAt.comp_hasDerivAt v ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))
    have h2 := h1.clm_apply (hasDerivAt_const v ((1 : ℝ), (0 : ℝ)))
    simp only [map_zero, add_zero] at h2
    exact h2
  have hFu : HasDerivAt (fun t => F (Φ (t, v)))
      (fderiv ℝ F (Φ (u, v)) (tangentU Φ (u, v))) u :=
    (hF _).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_tangentU hΦd)
  have hFv : HasDerivAt (fun t => F (Φ (u, t)))
      (fderiv ℝ F (Φ (u, v)) (tangentV Φ (u, v))) v :=
    (hF _).hasFDerivAt.comp_hasDerivAt v (hasDerivAt_tangentV hΦd)
  have e1 : partialX (fun u v => F (Φ (u, v)) ⬝ᵥ tangentV Φ (u, v)) u v =
      fderiv ℝ F (Φ (u, v)) (tangentU Φ (u, v)) ⬝ᵥ tangentV Φ (u, v) +
        F (Φ (u, v)) ⬝ᵥ H (1, 0) (0, 1) :=
    (hasDerivAt_dotProduct hFu hTv).deriv
  have e2 : partialY (fun u v => F (Φ (u, v)) ⬝ᵥ tangentU Φ (u, v)) u v =
      fderiv ℝ F (Φ (u, v)) (tangentV Φ (u, v)) ⬝ᵥ tangentU Φ (u, v) +
        F (Φ (u, v)) ⬝ᵥ H (0, 1) (1, 0) :=
    (hasDerivAt_dotProduct hFv hTu).deriv
  rw [e1, e2, hsymm, ← dot_fderiv_sub (hF _)]
  ring

theorem contDiffOn_dotProduct {U : Set (ℝ × ℝ)} {f g : ℝ × ℝ → Fin 3 → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    ContDiffOn ℝ 1 (fun p => f p ⬝ᵥ g p) U := by
  have e : (fun p => f p ⬝ᵥ g p) = fun p => f p 0 * g p 0 + f p 1 * g p 1 + f p 2 * g p 2 := by
    funext p
    simp [dotProduct, Fin.sum_univ_three]
  rw [e]
  have hf' := contDiffOn_pi.mp hf
  have hg' := contDiffOn_pi.mp hg
  exact (((hf' 0).mul (hg' 0)).add ((hf' 1).mul (hg' 1))).add ((hf' 2).mul (hg' 2))

/-- Along a closed piecewise-`C¹` parameter curve `γ`, the planar line integral of
`(F ∘ Φ) · T_u du + (F ∘ Φ) · T_v dv` is the line integral of `F` along the image curve
`Φ ∘ γ`. -/
theorem lineIntegral2_pullback {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath γ) a b) {Φ : ℝ × ℝ → Fin 3 → ℝ}
    (hΦ : ∀ t ∈ Icc a b, DifferentiableAt ℝ Φ (γ t)) (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) :
    lineIntegral2 (fun u v => F (Φ (u, v)) ⬝ᵥ tangentU Φ (u, v))
        (fun u v => F (Φ (u, v)) ⬝ᵥ tangentV Φ (u, v)) γ a b =
      lineIntegral F (fun t => Φ (γ t)) a b := by
  unfold lineIntegral2 lineIntegral
  refine intervalIntegral.integral_congr_ae ?_
  set S : Finset ℝ := (Finset.range (P.n + 1)).image P.t with hS
  filter_upwards [S.finite_toSet.countable.ae_notMem volume] with t htS htI
  have hab : a ≤ b := P.a_le_b
  rw [uIoc_of_le hab] at htI
  have hn : 0 < P.n := by
    rcases Nat.eq_zero_or_pos P.n with h0 | h0
    · have h1 := P.first
      have h2 := P.last
      rw [h0] at h2
      have := h1.symm.trans h2
      exact absurd (htI.1.trans_le (this ▸ htI.2)) (lt_irrefl _)
    · exact h0
  obtain ⟨k, hk, htk⟩ := P.exists_piece (Ioc_subset_Icc_self htI) hn
  have hmem : ∀ j ≤ P.n, P.t j ∈ (S : Set ℝ) := fun j hj =>
    Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
  have htk' : t ∈ Ioo (P.t k) (P.t (k + 1)) :=
    ⟨lt_of_le_of_ne htk.1 fun h => htS (h ▸ hmem k hk.le),
      lt_of_le_of_ne htk.2 fun h => htS (h ▸ hmem (k + 1) hk)⟩
  have hcg : toComplexPath γ =ᶠ[nhds t] P.g k :=
    Filter.eventuallyEq_of_mem (Icc_mem_nhds htk'.1 htk'.2) (P.eqOn k hk)
  have hg : HasDerivAt (toComplexPath γ) (deriv (P.g k) t) t :=
    (((P.contDiff k hk).differentiable one_ne_zero t).hasDerivAt).congr_of_eventuallyEq hcg
  have hγ : HasDerivAt γ (Complex.equivRealProdCLM (deriv (P.g k) t)) t :=
    Complex.equivRealProdCLM.hasFDerivAt.comp_hasDerivAt t hg
  set γ' := Complex.equivRealProdCLM (deriv (P.g k) t)
  have h1 : deriv (fun s => (γ s).1) t = γ'.1 :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t hγ).deriv
  have h2 : deriv (fun s => (γ s).2) t = γ'.2 :=
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t hγ).deriv
  have h3 : deriv (fun s => Φ (γ s)) t = γ'.1 • tangentU Φ (γ t) + γ'.2 • tangentV Φ (γ t) := by
    have hc : HasDerivAt (fun s => Φ (γ s)) (fderiv ℝ Φ (γ t) γ') t :=
      (hΦ t (Ioc_subset_Icc_self htI)).hasFDerivAt.comp_hasDerivAt t hγ
    rw [hc.deriv]
    exact clm_apply_prod _ _
  rw [h1, h2, h3]
  simp only [Prod.mk.eta, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

/-- **DLMF 1.6.57** (Stokes's theorem) for the surface `S = Φ(D)` parametrized over the region
`D = planeInterior γ a b` bounded by a positively oriented closed piecewise-`C¹` curve `γ` in the
parameter plane, with `Φ` of class `C²` on an open set containing `D ∪ γ` and `F` continuously
differentiable.  The boundary `∂S` is traversed by `Φ ∘ γ`, anticlockwise relative to the normal
`T_u × T_v`:  `∬_S (∇ × F) · dS = ∫_{∂S} F · ds`.  Proof: the pull-back reduces Stokes to
Green's theorem 1.6.44 in the parameter plane (`dlmf_1_6_44_nhds`), via
`partialX_sub_partialY_pullback` and `lineIntegral2_pullback`. -/
theorem dlmf_1_6_57 {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath γ) a b) (hpos : P.IsPositivelyOriented)
    {Φ : ℝ × ℝ → Fin 3 → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hSU : planeInterior γ a b ∪ γ '' Icc a b ⊆ U) (hΦ : ContDiffOn ℝ 2 Φ U)
    {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiff ℝ 1 F) :
    fluxIntegral (curl3 F) Φ (planeInterior γ a b) = lineIntegral F (fun t => Φ (γ t)) a b := by
  have hT : ContDiffOn ℝ 1 (fun p => fderiv ℝ Φ p) U := hΦ.fderiv_of_isOpen hU (by norm_num)
  have hTu : ContDiffOn ℝ 1 (tangentU Φ) U := hT.clm_apply contDiffOn_const
  have hTv : ContDiffOn ℝ 1 (tangentV Φ) U := hT.clm_apply contDiffOn_const
  have hFΦ : ContDiffOn ℝ 1 (fun p => F (Φ p)) U := hF.comp_contDiffOn (hΦ.of_le (by norm_num))
  have hP₁ : ContDiffOn ℝ 1
      (Function.uncurry fun u v => F (Φ (u, v)) ⬝ᵥ tangentU Φ (u, v)) U :=
    contDiffOn_dotProduct hFΦ hTu
  have hP₂ : ContDiffOn ℝ 1
      (Function.uncurry fun u v => F (Φ (u, v)) ⬝ᵥ tangentV Φ (u, v)) U :=
    contDiffOn_dotProduct hFΦ hTv
  have hΦat : ∀ q ∈ U, ContDiffAt ℝ 2 Φ q := fun q hq => hΦ.contDiffAt (hU.mem_nhds hq)
  rw [← lineIntegral2_pullback P (fun t ht => (hΦat _ (hSU (Or.inr ⟨t, ht, rfl⟩))).differentiableAt
      (by norm_num)) F, dlmf_1_6_44_nhds P hpos hU hSU hP₁ hP₂, fluxIntegral]
  refine setIntegral_congr_fun (isOpen_planeInterior P).measurableSet fun q hq => ?_
  exact (partialX_sub_partialY_pullback (hΦat q (hSU (Or.inl hq)))
    (hF.differentiable one_ne_zero)).symm

/-! ### Gauss's (divergence) theorem and Green's theorem for volume, on boxes -/

/-- The face `xᵢ = c` of a box, parametrized by the two remaining coordinates. -/
def boxFace (i : Fin 3) (c : ℝ) (y : Fin 2 → ℝ) : Fin 3 → ℝ := Fin.insertNth i c y

theorem continuous_boxFace (i : Fin 3) (c : ℝ) : Continuous (boxFace i c) :=
  continuous_const.finInsertNth i continuous_id

/-- The outward flux `∬_S F · dS` through the boundary `S` of the box `V = [a, b] ⊂ ℝ³`: on the
faces `xᵢ = bᵢ` and `xᵢ = aᵢ` the outward unit normals are `eᵢ` and `−eᵢ`, so
`F · n dA = ±Fᵢ dA`. -/
noncomputable def boxFlux (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (a b : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (boxFace i (b i) y) i) -
    ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (boxFace i (a i) y) i)

/-- `∬_S f ∂g/∂n dA` over the boundary of the box `[a, b]`: the outward normal derivative is
`∂g/∂n = ∇g · n = ±∂g/∂xᵢ` on the faces `xᵢ = bᵢ`, `xᵢ = aᵢ`. -/
noncomputable def boxNormalDerivIntegral (f g : (Fin 3 → ℝ) → ℝ) (a b : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      f (boxFace i (b i) y) * pd i g (boxFace i (b i) y)) -
    ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      f (boxFace i (a i) y) * pd i g (boxFace i (a i) y))

theorem continuous_pd_of_contDiff {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (pd i f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_div3 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiff ℝ 1 F) :
    Continuous (div3 F) :=
  continuous_finsetSum _ fun i _ => continuous_pd_of_contDiff ((contDiff_pi.mp hF) i) i

theorem pd_component_eq {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {x : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F x) (i : Fin 3) :
    pd i (fun q => F q i) x = fderiv ℝ F x (Pi.single i 1) i := by
  show fderiv ℝ (fun q => F q i) x (unitE i) = _
  rw [((hasFDerivAt_pi'.mp hF.hasFDerivAt) i).fderiv]
  rfl

/-- **DLMF 1.6.58** (Gauss's or the divergence theorem) for a box `V = [a, b] ⊂ ℝ³`, whose
boundary `S` is piecewise smooth (six faces) and oriented by the outward normal, and `F`
continuously differentiable: `∭_V ∇ · F dV = ∬_S F · dS`.  From Mathlib's divergence theorem
on boxes `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. -/
theorem dlmf_1_6_58 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiff ℝ 1 F)
    {a b : Fin 3 → ℝ} (hab : a ≤ b) :
    ∫ x in Icc a b, div3 F x = boxFlux F a b := by
  have hd := hF.differentiable one_ne_zero
  have hdiv : ∀ x, ∑ i, fderiv ℝ F x (Pi.single i 1) i = div3 F x := fun x =>
    Finset.sum_congr rfl fun i _ => (pd_component_eq (hd x) i).symm
  have key := integral_divergence_of_hasFDerivAt_off_countable a b hab F (fun x => fderiv ℝ F x)
    ∅ countable_empty hF.continuous.continuousOn (fun x _ => (hd x).hasFDerivAt)
    (by simp_rw [hdiv]; exact (continuous_div3 hF).continuousOn.integrableOn_compact isCompact_Icc)
  simp_rw [hdiv] at key
  rw [key]
  rfl

/-- **DLMF 1.6.59** (Green's theorem for volume) on a box `V = [a, b]`, for `f`, `g` twice
continuously differentiable: `∭_V (f ∇²g + ∇f · ∇g) dV = ∬_S f ∂g/∂n dA`. -/
theorem dlmf_1_6_59 {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    {a b : Fin 3 → ℝ} (hab : a ≤ b) :
    ∫ x in Icc a b, (f x * lap3 g x + grad3 f x ⬝ᵥ grad3 g x) = boxNormalDerivIntegral f g a b := by
  have hG : ContDiff ℝ 1 (grad3 g) := contDiff_pi.mpr fun i => contDiff_pd hg i
  have hF : ContDiff ℝ 1 (fun x => f x • grad3 g x) := (hf.of_le one_le_two).smul hG
  have h := dlmf_1_6_58 hF hab
  have hdiv : ∀ x, div3 (fun x => f x • grad3 g x) x =
      f x * lap3 g x + grad3 f x ⬝ᵥ grad3 g x := fun x => by
    rw [dlmf_1_6_25 ((hf.differentiable two_ne_zero) x) ((hG.differentiable one_ne_zero) x),
      dotProduct_comm]
    rfl
  simp_rw [hdiv] at h
  rw [h]
  simp only [boxFlux, boxNormalDerivIntegral, Pi.smul_apply, smul_eq_mul]
  rfl

/-- **DLMF 1.6.60** (Green's theorem for volume) on a box `V = [a, b]`:
`∭_V (f ∇²g − g ∇²f) dV = ∬_S (f ∂g/∂n − g ∂f/∂n) dA`. -/
theorem dlmf_1_6_60 {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    {a b : Fin 3 → ℝ} (hab : a ≤ b) :
    ∫ x in Icc a b, (f x * lap3 g x - g x * lap3 f x) =
      ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          (f (boxFace i (b i) y) * pd i g (boxFace i (b i) y) -
            g (boxFace i (b i) y) * pd i f (boxFace i (b i) y))) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          (f (boxFace i (a i) y) * pd i g (boxFace i (a i) y) -
            g (boxFace i (a i) y) * pd i f (boxFace i (a i) y))) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le one_le_two
  have hg1 : ContDiff ℝ 1 g := hg.of_le one_le_two
  have hGf : ContDiff ℝ 1 (grad3 f) := contDiff_pi.mpr fun i => contDiff_pd hf i
  have hGg : ContDiff ℝ 1 (grad3 g) := contDiff_pi.mpr fun i => contDiff_pd hg i
  have hcf : Continuous (grad3 f) := hGf.continuous
  have hcg : Continuous (grad3 g) := hGg.continuous
  have hA : Continuous fun x => f x * lap3 g x + grad3 f x ⬝ᵥ grad3 g x :=
    (hf1.continuous.mul (continuous_div3 hGg)).add (hcf.dotProduct hcg)
  have hB : Continuous fun x => g x * lap3 f x + grad3 g x ⬝ᵥ grad3 f x :=
    (hg1.continuous.mul (continuous_div3 hGf)).add (hcg.dotProduct hcf)
  have hface : ∀ (h : (Fin 3 → ℝ) → ℝ), Continuous h → ∀ (i : Fin 3) (c : ℝ),
      IntegrableOn (fun y => h (boxFace i c y)) (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    fun h hh i c => (hh.comp (continuous_boxFace i c)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hfg : ∀ i, Continuous fun x => f x * pd i g x := fun i =>
    hf1.continuous.mul (continuous_pd_of_contDiff hg1 i)
  have hgf : ∀ i, Continuous fun x => g x * pd i f x := fun i =>
    hg1.continuous.mul (continuous_pd_of_contDiff hf1 i)
  calc ∫ x in Icc a b, (f x * lap3 g x - g x * lap3 f x)
      = (∫ x in Icc a b, (f x * lap3 g x + grad3 f x ⬝ᵥ grad3 g x)) -
          ∫ x in Icc a b, (g x * lap3 f x + grad3 g x ⬝ᵥ grad3 f x) := by
        rw [← integral_sub (hA.continuousOn.integrableOn_compact isCompact_Icc)
          (hB.continuousOn.integrableOn_compact isCompact_Icc)]
        congr 1
        funext x
        rw [dotProduct_comm (grad3 g x)]
        ring
    _ = boxNormalDerivIntegral f g a b - boxNormalDerivIntegral g f a b := by
        rw [dlmf_1_6_59 hf hg hab, dlmf_1_6_59 hg hf hab]
    _ = _ := by
        unfold boxNormalDerivIntegral
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_sub (hface _ (hfg i) i (b i)) (hface _ (hgf i) i (b i)),
          integral_sub (hface _ (hfg i) i (a i)) (hface _ (hgf i) i (a i))]
        ring

end Azurite.DLMF
