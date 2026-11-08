/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.Geometry.Euclidean.Volume.MeasureSimplex
import Mathlib.Geometry.Euclidean.Altitude

/-!
# DLMF §4.42 Solution of Triangles

## §4.42(i)–(ii) Planar triangles

Mathlib's Euclidean geometry is used. The vertices `A B C` are points of a Euclidean affine space
`P` (for instance `EuclideanSpace ℝ (Fin 2)`; a triangle spans a plane in any case). The angles
are the unoriented angles `A = ∠ B A C`, `B = ∠ A B C`, `C = ∠ A C B` (`EuclideanGeometry.angle`, a
function of the ordered triple of points, with values in `[0, π]`). The sides are
`a = dist B C`, `b = dist C A`, `c = dist A B`, opposite `A`, `B`, `C` (Figures 4.42.1–4.42.2).

* 4.42.1–4.42.3 (right angle at `C`): `dlmf_4_42_1`, `dlmf_4_42_2`, `dlmf_4_42_3`, from Mathlib's
  right-angle trigonometry. `csc`, `sec`, `cot` are `1/sin`, `1/cos`, `1/tan`.
* 4.42.4 (law of sines, nondegenerate triangle): `dlmf_4_42_4`.
* 4.42.5 (law of cosines, any three points): `dlmf_4_42_5`.
* 4.42.6 (`B ≠ C`): `dlmf_4_42_6`, from 4.42.5 twice.
* 4.42.7: `dlmf_4_42_7` for a triangle given as a 2-simplex `s` (affinely independent vertices):
  its area `s.volume` (Mathlib's `Affine.Simplex.volume`, half base times height) is
  `½ bc sin A = (σ(σ − a)(σ − b)(σ − c))^{1/2}`, `σ = ½(a + b + c)`. The height from `A` is computed
  from the foot of the altitude (`height_mul_dist_eq`). In the plane `ℝ²` the area is the Lebesgue
  measure of the closed triangle (`dlmf_4_42_7_lebesgue`).

## §4.42(iii) Spherical triangles

Mathlib has no spherical trigonometry. The vertices are unit vectors `u, v, w` of a real inner
product space (for instance the unit sphere of `EuclideanSpace ℝ (Fin 3)`). The sides are the
great-circle arcs `a = angle v w`, `b = angle w u`, `c = angle u v`
(`InnerProductGeometry.angle`). The angle at a vertex is the angle between the tangent vectors of
the two arcs there: `sphAngle x y z = angle (y − ⟪x, y⟫x) (z − ⟪x, z⟫x)`, so `A = sphAngle u v w`,
`B = sphAngle v w u`, `C = sphAngle w u v`. Everything follows from two relations at each vertex
(`sphAngle_props`, `sph_master`): `cos A sin b sin c = cos a − cos b cos c` and
`sin A sin b sin c = √G` with the symmetric `G = 1 − cos²a − cos²b − cos²c + 2 cos a cos b cos c`.

* 4.42.8 (all unit vectors): `dlmf_4_42_8`.
* 4.42.9–4.42.12 (sides not `0` or `π`, i.e. no vertex equal or antipodal to another; for 4.42.11
  also `sin B ≠ 0`, so that `cot B` is defined): `dlmf_4_42_9`, `dlmf_4_42_10`, `dlmf_4_42_11`,
  `dlmf_4_42_12`.
-/

open Real EuclideanGeometry
open scoped RealInnerProductSpace

namespace Azurite.DLMF

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ### §4.42(i) Planar right triangles -/

/-- **DLMF 4.42.1**: `sin A = a/c = 1/csc A` (right angle at `C`). -/
theorem dlmf_4_42_1 {A B C : P} (h : ∠ A C B = π / 2) (h0 : A ≠ C ∨ B ≠ C) :
    Real.sin (∠ B A C) = dist B C / dist A B ∧ Real.sin (∠ B A C) = 1 / (1 / Real.sin (∠ B A C)) :=
  by
  refine ⟨?_, by rw [one_div_one_div]⟩
  have h' : ∠ B C A = π / 2 := by rw [angle_comm]; exact h
  rw [angle_comm, sin_angle_of_angle_eq_pi_div_two h' h0.symm, dist_comm B A]

/-- **DLMF 4.42.2**: `cos A = b/c = 1/sec A` (right angle at `C`). -/
theorem dlmf_4_42_2 {A B C : P} (h : ∠ A C B = π / 2) :
    Real.cos (∠ B A C) = dist C A / dist A B ∧ Real.cos (∠ B A C) = 1 / (1 / Real.cos (∠ B A C)) :=
  by
  refine ⟨?_, by rw [one_div_one_div]⟩
  have h' : ∠ B C A = π / 2 := by rw [angle_comm]; exact h
  rw [angle_comm, cos_angle_of_angle_eq_pi_div_two h', dist_comm B A, dist_comm A C]

/-- **DLMF 4.42.3**: `tan A = a/b = 1/cot A` (right angle at `C`). -/
theorem dlmf_4_42_3 {A B C : P} (h : ∠ A C B = π / 2) :
    Real.tan (∠ B A C) = dist B C / dist C A ∧ Real.tan (∠ B A C) = 1 / (1 / Real.tan (∠ B A C)) :=
  by
  refine ⟨?_, by rw [one_div_one_div]⟩
  have h' : ∠ B C A = π / 2 := by rw [angle_comm]; exact h
  rw [angle_comm, tan_angle_of_angle_eq_pi_div_two h', dist_comm A C]

/-! ### §4.42(ii) Planar triangles -/

/-- **DLMF 4.42.4** (law of sines): `a/sin A = b/sin B = c/sin C` (vertices not collinear). -/
theorem dlmf_4_42_4 {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) :
    dist B C / Real.sin (∠ B A C) = dist C A / Real.sin (∠ A B C) ∧
      dist C A / Real.sin (∠ A B C) = dist A B / Real.sin (∠ A C B) := by
  have hA : 0 < Real.sin (∠ B A C) := sin_pos_of_not_collinear (by
    rwa [Set.insert_comm])
  have hB : 0 < Real.sin (∠ A B C) := sin_pos_of_not_collinear h
  have hC : 0 < Real.sin (∠ A C B) := sin_pos_of_not_collinear (by
    have e : ({A, C, B} : Set P) = {A, B, C} := by rw [Set.pair_comm]
    rwa [e])
  have l1 := law_sin A B C
  have l2 := law_sin B C A
  rw [angle_comm C A B] at l1
  rw [angle_comm B C A] at l2
  constructor
  · rw [div_eq_div_iff hA.ne' hB.ne']; linarith
  · rw [div_eq_div_iff hB.ne' hC.ne']; linarith

/-- **DLMF 4.42.5** (law of cosines): `c² = a² + b² − 2ab cos C`. -/
theorem dlmf_4_42_5 (A B C : P) :
    dist A B ^ 2 = dist B C ^ 2 + dist C A ^ 2 - 2 * dist B C * dist C A * Real.cos (∠ A C B) := by
  have h := law_cos A C B
  rw [dist_comm B C, dist_comm C A] at *
  nlinarith [h]

/-- **DLMF 4.42.6**: `a = b cos C + c cos B` (`B ≠ C`). -/
theorem dlmf_4_42_6 {A B C : P} (h : B ≠ C) :
    dist B C = dist C A * Real.cos (∠ A C B) + dist A B * Real.cos (∠ A B C) := by
  have ha : dist B C ≠ 0 := dist_ne_zero.mpr h
  have h1 := dlmf_4_42_5 A B C
  have h2 := law_cos A B C
  rw [dist_comm C B, dist_comm A C] at h2
  refine mul_left_cancel₀ ha ?_
  nlinarith [h1, h2]


/-! ### 4.42.7 -/

/-- In a triangle `s`, `a · h_A = bc sin A` (`h_A` the height from `A = s.points 0`). -/
theorem height_mul_dist_eq (s : Affine.Simplex ℝ P 2) :
    s.height 0 * dist (s.points 1) (s.points 2) =
      dist (s.points 2) (s.points 0) * dist (s.points 0) (s.points 1) *
        Real.sin (∠ (s.points 1) (s.points 0) (s.points 2)) := by
  set A := s.points 0
  set B := s.points 1
  set C := s.points 2
  set F := s.altitudeFoot 0
  set b' : V := B -ᵥ F
  set c' : V := C -ᵥ F
  set y : V := A -ᵥ F
  have E1 : ⟪b', y⟫ = 0 := s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i := 0) (j := 1)
    (by decide)
  have E2 : ⟪c', y⟫ = 0 := s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i := 0) (j := 2)
    (by decide)
  have Eh : s.height 0 ^ 2 = ⟪y, y⟫ := by
    rw [Affine.Simplex.height, dist_eq_norm_vsub V, real_inner_self_eq_norm_sq]
  -- the foot lies on the line `BC`
  have himg : s.points '' {0}ᶜ = {B, C} := by
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i
      · exact absurd rfl hi
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
  have hF := s.altitudeFoot_mem_affineSpan_image_compl 0
  rw [himg] at hF
  have hB : B ∈ affineSpan ℝ ({B, C} : Set P) := mem_affineSpan ℝ (by simp)
  have hv := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hF hB
  rw [vectorSpan_pair, Submodule.mem_span_singleton] at hv
  obtain ⟨t, ht⟩ := hv
  -- `F − B = t (B − C)`, i.e. `(1 + t) b' = t c'`
  have hcol : (1 + t) • b' = t • c' := by
    have e1 : F -ᵥ B = -b' := (neg_vsub_eq_vsub_rev B F).symm
    have e2 : B -ᵥ C = b' - c' := (vsub_sub_vsub_cancel_right B C F).symm
    rw [e1, e2] at ht
    rw [add_smul, one_smul, smul_sub] at *
    linear_combination (norm := module) ht
  have hP := congrArg (fun z => ⟪z, b'⟫) hcol
  have hQ := congrArg (fun z => ⟪z, c'⟫) hcol
  simp only [inner_smul_left, RCLike.conj_to_real] at hP hQ
  set Pb := ⟪b', b'⟫
  set Qc := ⟪c', c'⟫
  set R := ⟪b', c'⟫
  have hR : ⟪c', b'⟫ = R := real_inner_comm _ _
  rw [hR] at hP
  have hG : Pb * Qc - R ^ 2 = 0 := by
    rcases eq_or_ne (1 + t) 0 with h1 | h1
    · have ht' : t = -1 := by linarith
      rw [ht'] at hQ
      norm_num at hQ
      have hc0' : c' = 0 := inner_self_eq_zero.mp (by linarith [hQ] : ⟪c', c'⟫ = 0)
      simp [R, Qc, hc0']
    · have : (1 + t) ^ 2 * (Pb * Qc - R ^ 2) = 0 := by
        linear_combination (1 + t) * Qc * hP - (1 + t) * R * hQ
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) h1
      · exact h
  -- the sides and the angle at `A` in terms of `b'`, `c'`, `y`
  have hu : B -ᵥ A = b' - y := (vsub_sub_vsub_cancel_right B A F).symm
  have hv : C -ᵥ A = c' - y := (vsub_sub_vsub_cancel_right C A F).symm
  have hbc : B -ᵥ C = b' - c' := (vsub_sub_vsub_cancel_right B C F).symm
  set u : V := b' - y
  set v : V := c' - y
  set θ := ∠ B A C
  have hθ : θ = InnerProductGeometry.angle u v := by
    simp only [θ, EuclideanGeometry.angle, hu, hv]
  have dAB : dist A B = ‖u‖ := by rw [dist_comm, dist_eq_norm_vsub V, hu]
  have dCA : dist C A = ‖v‖ := by rw [dist_eq_norm_vsub V, hv]
  have dBC : dist B C = ‖b' - c'‖ := by rw [dist_eq_norm_vsub V, hbc]
  rw [dAB, dCA, dBC]
  have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
  rw [← hθ] at hcos
  have hsq : (‖v‖ * ‖u‖ * Real.sin θ) ^ 2 = ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 := by
    rw [← hcos, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    linear_combination (‖u‖ ^ 2 * ‖v‖ ^ 2) * Real.sin_sq_add_cos_sq θ
  have huu : ⟪u, u⟫ = Pb + ⟪y, y⟫ := by
    simp only [u, inner_sub_left, inner_sub_right, real_inner_comm b' y, E1]; ring
  have hvv : ⟪v, v⟫ = Qc + ⟪y, y⟫ := by
    simp only [v, inner_sub_left, inner_sub_right, real_inner_comm c' y, E2]; ring
  have huv : ⟪u, v⟫ = R + ⟪y, y⟫ := by
    simp only [u, v, inner_sub_left, inner_sub_right, real_inner_comm c' y, E1, E2]; ring
  have hbb : ‖b' - c'‖ ^ 2 = Pb - 2 * R + Qc := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, hR]; ring
  refine (pow_left_inj₀ (by positivity) (mul_nonneg (by positivity)
    (InnerProductGeometry.sin_angle_nonneg u v |>.trans_eq (by rw [hθ]))) two_ne_zero).mp ?_
  rw [hsq, huu, hvv, huv, mul_pow, Eh, hbb]
  linear_combination (-1 : ℝ) * hG


/-- **DLMF 4.42.7**: `area = ½ bc sin A = (σ(σ − a)(σ − b)(σ − c))^{1/2}`, `σ = ½(a + b + c)`
(Heron), for a triangle `s` with vertices `A, B, C = s.points 0, 1, 2`; the area is Mathlib's
`Affine.Simplex.volume`. -/
theorem dlmf_4_42_7 (s : Affine.Simplex ℝ P 2) :
    s.volume = 1 / 2 * dist (s.points 2) (s.points 0) * dist (s.points 0) (s.points 1) *
        Real.sin (∠ (s.points 1) (s.points 0) (s.points 2)) ∧
      s.volume = √((dist (s.points 1) (s.points 2) + dist (s.points 2) (s.points 0) +
          dist (s.points 0) (s.points 1)) / 2 *
        ((-dist (s.points 1) (s.points 2) + dist (s.points 2) (s.points 0) +
          dist (s.points 0) (s.points 1)) / 2) *
        ((dist (s.points 1) (s.points 2) - dist (s.points 2) (s.points 0) +
          dist (s.points 0) (s.points 1)) / 2) *
        ((dist (s.points 1) (s.points 2) + dist (s.points 2) (s.points 0) -
          dist (s.points 0) (s.points 1)) / 2)) := by
  have hface : (s.faceOpposite 0).volume = dist (s.points 1) (s.points 2) := by
    rw [Affine.Simplex.volume_eq_dist, Affine.Simplex.faceOpposite_point_eq_point_succAbove,
      Affine.Simplex.faceOpposite_point_eq_point_succAbove]
    rfl
  have hA : s.volume = 1 / 2 * dist (s.points 2) (s.points 0) * dist (s.points 0) (s.points 1) *
      Real.sin (∠ (s.points 1) (s.points 0) (s.points 2)) := by
    rw [Affine.Simplex.volume_eq s 0, hface, mul_assoc, height_mul_dist_eq]
    push_cast; ring
  refine ⟨hA, ?_⟩
  have hlaw := law_cos (s.points 1) (s.points 0) (s.points 2)
  rw [dist_comm (s.points 1) (s.points 0)] at hlaw
  set a := dist (s.points 1) (s.points 2)
  set b := dist (s.points 2) (s.points 0)
  set c := dist (s.points 0) (s.points 1)
  set θ := ∠ (s.points 1) (s.points 0) (s.points 2)
  have hsc := Real.sin_sq_add_cos_sq θ
  have hnn : 0 ≤ s.volume := s.volume_pos.le
  rw [← Real.sqrt_sq hnn]
  congr 1
  rw [hA]
  linear_combination (1 / 4 * b ^ 2 * c ^ 2) * hsc +
    (-1 / 16) * (b ^ 2 + c ^ 2 - a ^ 2 + 2 * b * c * Real.cos θ) * hlaw

/-- **DLMF 4.42.7** in the plane `ℝ²`: the area of a triangle, as the Lebesgue measure of the
closed triangle, is `½ bc sin A = (σ(σ − a)(σ − b)(σ − c))^{1/2}`. -/
theorem dlmf_4_42_7_lebesgue (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) :
    MeasureTheory.volume.real s.closedInterior = s.volume ∧
      s.volume = 1 / 2 * dist (s.points 2) (s.points 0) * dist (s.points 0) (s.points 1) *
        Real.sin (∠ (s.points 1) (s.points 0) (s.points 2)) :=
  ⟨(Affine.Simplex.volume_eq_volume_real_closedInterior finrank_euclideanSpace_fin s).symm,
    (dlmf_4_42_7 s).1⟩


/-! ### §4.42(iii) Spherical triangles

The vertices are unit vectors `u, v, w` of a real inner product space (the unit sphere of `ℝ³`,
say). The side opposite a vertex is the great-circle arc between the other two:
`a = angle v w`, `b = angle w u`, `c = angle u v` (`InnerProductGeometry.angle`, in `[0, π]`). The
angle at a vertex `x` between the arcs to `y` and `z` is the angle between their tangent vectors
`y − ⟪x, y⟫x` and `z − ⟪x, z⟫x` at `x` (`sphAngle x y z`): `A = sphAngle u v w`,
`B = sphAngle v w u`, `C = sphAngle w u v`. -/

/-- The angle at `x` of the spherical triangle `x y z` (`x, y, z` unit vectors). -/
noncomputable def sphAngle (x y z : V) : ℝ :=
  InnerProductGeometry.angle (y - ⟪x, y⟫ • x) (z - ⟪x, z⟫ • x)

theorem cos_angle_of_unit {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Real.cos (InnerProductGeometry.angle x y) = ⟪x, y⟫ := by
  rw [InnerProductGeometry.cos_angle, hx, hy]; simp

theorem sin_angle_of_unit {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Real.sin (InnerProductGeometry.angle x y) = √(1 - ⟪x, y⟫ ^ 2) := by
  have h := InnerProductGeometry.sin_angle_mul_norm_mul_norm x y
  rw [hx, hy, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx, hy] at h
  simpa [sq] using h

theorem one_sub_inner_sq_nonneg {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    0 ≤ 1 - ⟪x, y⟫ ^ 2 := by
  have h := abs_real_inner_le_norm x y
  rw [hx, hy, mul_one] at h
  nlinarith [sq_abs ⟪x, y⟫, abs_nonneg ⟪x, y⟫]

/-- The tangent vectors at a vertex: their norms are the sines of the sides and their inner
product is `cos(opposite side) − cos·cos`. -/
theorem tangent_props {x y z : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (_hz : ‖z‖ = 1) :
    ‖y - ⟪x, y⟫ • x‖ = Real.sin (InnerProductGeometry.angle x y) ∧
      ⟪y - ⟪x, y⟫ • x, z - ⟪x, z⟫ • x⟫ = ⟪y, z⟫ - ⟪x, y⟫ * ⟪x, z⟫ := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : ⟪y, y⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  constructor
  · rw [sin_angle_of_unit hx hy, ← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq]
    congr 1
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, hxx, hyy, real_inner_comm x y]
    ring
  · simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, hxx, real_inner_comm x y]
    ring

/-- The two basic relations at a vertex `x`: with `p = ⟪x, y⟫`, `q = ⟪x, z⟫`, `r = ⟪y, z⟫`,
`cos X · sin(xy) sin(xz) = r − pq` and `sin X · sin(xy) sin(xz) = √G`,
`G = 1 − p² − q² − r² + 2pqr`. -/
theorem sphAngle_props {x y z : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    Real.cos (sphAngle x y z) * (Real.sin (InnerProductGeometry.angle x y) *
        Real.sin (InnerProductGeometry.angle x z)) = ⟪y, z⟫ - ⟪x, y⟫ * ⟪x, z⟫ ∧
      Real.sin (sphAngle x y z) * (Real.sin (InnerProductGeometry.angle x y) *
        Real.sin (InnerProductGeometry.angle x z)) =
        √(1 - ⟪x, y⟫ ^ 2 - ⟪x, z⟫ ^ 2 - ⟪y, z⟫ ^ 2 + 2 * ⟪x, y⟫ * ⟪x, z⟫ * ⟪y, z⟫) := by
  obtain ⟨n1, i12⟩ := tangent_props hx hy hz
  obtain ⟨n2, -⟩ := tangent_props hx hz hy
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  constructor
  · rw [← n1, ← n2, sphAngle, InnerProductGeometry.cos_angle_mul_norm_mul_norm, i12]
  · rw [← n1, ← n2, sphAngle, InnerProductGeometry.sin_angle_mul_norm_mul_norm, i12,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, n1, n2, sin_angle_of_unit hx hy,
      sin_angle_of_unit hx hz, Real.sq_sqrt (one_sub_inner_sq_nonneg hx hy),
      Real.sq_sqrt (one_sub_inner_sq_nonneg hx hz)]
    congr 1
    ring


/-- All relations of a spherical triangle `u v w` used below (`p = cos c`, `q = cos b`, `r = cos a`,
`G = 1 − p² − q² − r² + 2pqr`). -/
theorem sph_master {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    let a := InnerProductGeometry.angle v w
    let b := InnerProductGeometry.angle w u
    let c := InnerProductGeometry.angle u v
    let G := 1 - ⟪u, v⟫ ^ 2 - ⟪u, w⟫ ^ 2 - ⟪v, w⟫ ^ 2 + 2 * ⟪u, v⟫ * ⟪u, w⟫ * ⟪v, w⟫
    Real.cos a = ⟪v, w⟫ ∧ Real.cos b = ⟪u, w⟫ ∧ Real.cos c = ⟪u, v⟫ ∧
      Real.sin a ^ 2 = 1 - ⟪v, w⟫ ^ 2 ∧ Real.sin b ^ 2 = 1 - ⟪u, w⟫ ^ 2 ∧
      Real.sin c ^ 2 = 1 - ⟪u, v⟫ ^ 2 ∧
      Real.cos (sphAngle u v w) * (Real.sin c * Real.sin b) = ⟪v, w⟫ - ⟪u, v⟫ * ⟪u, w⟫ ∧
      Real.cos (sphAngle v w u) * (Real.sin a * Real.sin c) = ⟪u, w⟫ - ⟪v, w⟫ * ⟪u, v⟫ ∧
      Real.cos (sphAngle w u v) * (Real.sin b * Real.sin a) = ⟪u, v⟫ - ⟪u, w⟫ * ⟪v, w⟫ ∧
      Real.sin (sphAngle u v w) * (Real.sin c * Real.sin b) = √G ∧
      Real.sin (sphAngle v w u) * (Real.sin a * Real.sin c) = √G ∧
      Real.sin (sphAngle w u v) * (Real.sin b * Real.sin a) = √G ∧ 0 ≤ G := by
  intro a b c G
  have cuv := real_inner_comm u v
  have cuw := real_inner_comm u w
  have cvw := real_inner_comm v w
  have hab : InnerProductGeometry.angle u w = b := InnerProductGeometry.angle_comm _ _
  have hba : InnerProductGeometry.angle v u = c := InnerProductGeometry.angle_comm _ _
  have hca : InnerProductGeometry.angle w v = a := InnerProductGeometry.angle_comm _ _
  obtain ⟨A1, A2⟩ := sphAngle_props hu hv hw
  obtain ⟨B1, B2⟩ := sphAngle_props hv hw hu
  obtain ⟨C1, C2⟩ := sphAngle_props hw hu hv
  rw [hab] at A1 A2
  rw [hba] at B1 B2
  rw [hca] at C1 C2
  have sq : ∀ {x y : V}, ‖x‖ = 1 → ‖y‖ = 1 →
      Real.sin (InnerProductGeometry.angle x y) ^ 2 = 1 - ⟪x, y⟫ ^ 2 := fun hx hy => by
    rw [sin_angle_of_unit hx hy, Real.sq_sqrt (one_sub_inner_sq_nonneg hx hy)]
  have hGA : (1 - ⟪u, v⟫ ^ 2 - ⟪u, w⟫ ^ 2 - ⟪v, w⟫ ^ 2 + 2 * ⟪u, v⟫ * ⟪u, w⟫ * ⟪v, w⟫) = G := rfl
  refine ⟨cos_angle_of_unit hv hw, by rw [cos_angle_of_unit hw hu, cuw], cos_angle_of_unit hu hv,
    sq hv hw, by rw [sq hw hu, cuw], sq hu hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact A1
  · rw [B1, cuw, cuv]
  · rw [C1, cuw, cvw]
  · rw [A2]
  · rw [B2]; congr 1; rw [cuv, cuw]; ring
  · rw [C2]; congr 1; rw [cuw, cvw]; ring
  · -- `G = (sin A sin b sin c)²`
    have h1 := Real.sin_sq_add_cos_sq (sphAngle u v w)
    have h2 : G = (Real.sin (sphAngle u v w) * (Real.sin c * Real.sin b)) ^ 2 := by
      have hb2 := sq hw hu
      have hc2 := sq hu hv
      rw [cuw] at hb2
      simp only [G]
      linear_combination (-(Real.sin c ^ 2 * Real.sin b ^ 2)) * h1 + 0 * A1 +
        (Real.cos (sphAngle u v w) * (Real.sin c * Real.sin b) + (⟪v, w⟫ - ⟪u, v⟫ * ⟪u, w⟫)) * A1 -
        (Real.sin b ^ 2) * hc2 - (1 - ⟪u, v⟫ ^ 2) * hb2
    rw [h2]; positivity


open InnerProductGeometry in
/-- **DLMF 4.42.8** (spherical law of cosines): `cos a = cos b cos c + sin b sin c cos A`. -/
theorem dlmf_4_42_8 {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    Real.cos (angle v w) = Real.cos (angle w u) * Real.cos (angle u v) +
      Real.sin (angle w u) * Real.sin (angle u v) * Real.cos (sphAngle u v w) := by
  obtain ⟨ca, cb, cc, -, -, -, XA, -, -, -, -, -, -⟩ := sph_master hu hv hw
  rw [ca, cb, cc]
  linear_combination -XA

open InnerProductGeometry in
/-- **DLMF 4.42.9** (spherical law of sines): `sin A/sin a = sin B/sin b = sin C/sin c` (sides
not `0` or `π`). -/
theorem dlmf_4_42_9 {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (ha : Real.sin (angle v w) ≠ 0) (hb : Real.sin (angle w u) ≠ 0)
    (hc : Real.sin (angle u v) ≠ 0) :
    Real.sin (sphAngle u v w) / Real.sin (angle v w) =
        Real.sin (sphAngle v w u) / Real.sin (angle w u) ∧
      Real.sin (sphAngle v w u) / Real.sin (angle w u) =
        Real.sin (sphAngle w u v) / Real.sin (angle u v) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, SA, SB, SC, -⟩ := sph_master hu hv hw
  constructor
  · rw [div_eq_div_iff ha hb]
    refine mul_right_cancel₀ hc ?_
    linear_combination SA - SB
  · rw [div_eq_div_iff hb hc]
    refine mul_right_cancel₀ ha ?_
    linear_combination SB - SC

open InnerProductGeometry in
/-- **DLMF 4.42.10**: `sin a cos B = cos b sin c − sin b cos c cos A` (`sin c ≠ 0`). -/
theorem dlmf_4_42_10 {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hc : Real.sin (angle u v) ≠ 0) :
    Real.sin (angle v w) * Real.cos (sphAngle v w u) =
      Real.cos (angle w u) * Real.sin (angle u v) -
        Real.sin (angle w u) * Real.cos (angle u v) * Real.cos (sphAngle u v w) := by
  obtain ⟨-, cb, cc, -, -, sc2, XA, XB, -, -, -, -, -⟩ := sph_master hu hv hw
  rw [cb, cc]
  refine mul_left_cancel₀ hc ?_
  linear_combination XB - ⟪u, w⟫ * sc2 + ⟪u, v⟫ * XA

open InnerProductGeometry in
/-- **DLMF 4.42.11**: `cos a cos C = sin a cot b − sin C cot B` (sides not `0` or `π`,
`sin B ≠ 0`). -/
theorem dlmf_4_42_11 {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (ha : Real.sin (angle v w) ≠ 0) (hb : Real.sin (angle w u) ≠ 0)
    (hc : Real.sin (angle u v) ≠ 0) (hB : Real.sin (sphAngle v w u) ≠ 0) :
    Real.cos (angle v w) * Real.cos (sphAngle w u v) =
      Real.sin (angle v w) * Real.cot (angle w u) -
        Real.sin (sphAngle w u v) * Real.cot (sphAngle v w u) := by
  obtain ⟨ca, cb, -, sa2, -, -, -, XB, XC, -, SB, SC, -⟩ := sph_master hu hv hw
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, ca, cb]
  set sa := Real.sin (angle v w)
  set sb := Real.sin (angle w u)
  set sc := Real.sin (angle u v)
  set sB := Real.sin (sphAngle v w u)
  set sC := Real.sin (sphAngle w u v)
  set cB := Real.cos (sphAngle v w u)
  set cC := Real.cos (sphAngle w u v)
  rw [show sa * (⟪u, w⟫ / sb) - sC * (cB / sB) = (sa * ⟪u, w⟫ * sB - sC * cB * sb) / (sb * sB) by
    field_simp, eq_div_iff (mul_ne_zero hb hB)]
  refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero ha ha) hc) ?_
  linear_combination ⟪v, w⟫ * sB * sc * sa * XC - ⟪u, w⟫ * sB * sc * sa * sa2 +
    sa * sb * sC * XB + (⟪u, w⟫ - ⟪v, w⟫ * ⟪u, v⟫) * SC - (⟪u, w⟫ - ⟪v, w⟫ * ⟪u, v⟫) * SB

open InnerProductGeometry in
/-- **DLMF 4.42.12** (polar law of cosines): `cos A = −cos B cos C + sin B sin C cos a` (sides not
`0` or `π`). -/
theorem dlmf_4_42_12 {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (ha : Real.sin (angle v w) ≠ 0) (hb : Real.sin (angle w u) ≠ 0)
    (hc : Real.sin (angle u v) ≠ 0) :
    Real.cos (sphAngle u v w) = -Real.cos (sphAngle v w u) * Real.cos (sphAngle w u v) +
      Real.sin (sphAngle v w u) * Real.sin (sphAngle w u v) * Real.cos (angle v w) := by
  obtain ⟨ca, -, -, sa2, -, -, XA, XB, XC, -, SB, SC, hG⟩ := sph_master hu hv hw
  rw [ca]
  have hK := Real.mul_self_sqrt hG
  set sa := Real.sin (angle v w)
  set sb := Real.sin (angle w u)
  set sc := Real.sin (angle u v)
  set K := √(1 - ⟪u, v⟫ ^ 2 - ⟪u, w⟫ ^ 2 - ⟪v, w⟫ ^ 2 + 2 * ⟪u, v⟫ * ⟪u, w⟫ * ⟪v, w⟫)
  refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero ha ha) hb) hc) ?_
  linear_combination sa ^ 2 * XA + Real.cos (sphAngle w u v) * sb * sa * XB +
    (⟪u, w⟫ - ⟪v, w⟫ * ⟪u, v⟫) * XC - ⟪v, w⟫ * Real.sin (sphAngle w u v) * sb * sa * SB -
    ⟪v, w⟫ * K * SC - ⟪v, w⟫ * hK + (⟪v, w⟫ - ⟪u, v⟫ * ⟪u, w⟫) * sa2

end Azurite.DLMF
