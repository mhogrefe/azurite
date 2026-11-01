/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.AbsMax
import Azurite.DLMF.Chapter2.Section4CoalescingPrep

/-!
# The disc algebra

`discAlg r`: the functions continuous on the closed disc `|z| ≤ r` and analytic inside, as a
closed subalgebra of `C(closedBall 0 r, ℂ)` with the sup norm, hence a Banach algebra. This is the
space in which the inverse function theorem is applied to obtain the Chester–Friedman–Ursell
change of variable uniformly in the parameter.

* `discExt r F` extends `F : C(closedBall 0 r, ℂ)` by `0` outside the disc;
* `discAlg r = {F | discExt r F is analytic on the open disc}`, closed (`isClosed_discAlg`);
* `discZ r` is the coordinate function `z ↦ z`.
-/

open Set Filter Topology Complex Metric

namespace Azurite.DLMF

variable (r : ℝ)

open scoped Classical in
/-- Extension of a function on the closed disc by zero. -/
noncomputable def discExt (F : C(closedBall (0 : ℂ) r, ℂ)) (z : ℂ) : ℂ :=
  if h : z ∈ closedBall (0 : ℂ) r then F ⟨z, h⟩ else 0

theorem discExt_apply (F : C(closedBall (0 : ℂ) r, ℂ)) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    discExt r F z = F ⟨z, hz⟩ := by
  simp [discExt, hz]

theorem discExt_coe (F : C(closedBall (0 : ℂ) r, ℂ)) (x : closedBall (0 : ℂ) r) :
    discExt r F x = F x := by
  rw [discExt_apply r F x.2]

theorem domRestrict_discExt (F : C(closedBall (0 : ℂ) r, ℂ)) :
    (closedBall (0 : ℂ) r).domRestrict (discExt r F) = F := by
  funext x
  exact discExt_coe r F x

theorem continuousOn_discExt (F : C(closedBall (0 : ℂ) r, ℂ)) :
    ContinuousOn (discExt r F) (closedBall 0 r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert F.continuous using 1
  funext x
  exact discExt_coe r F x

theorem discExt_add (F G : C(closedBall (0 : ℂ) r, ℂ)) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    discExt r (F + G) z = discExt r F z + discExt r G z := by
  simp only [discExt_apply r _ hz, ContinuousMap.add_apply]

theorem discExt_mul (F G : C(closedBall (0 : ℂ) r, ℂ)) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    discExt r (F * G) z = discExt r F z * discExt r G z := by
  simp only [discExt_apply r _ hz, ContinuousMap.mul_apply]

theorem discExt_smul (c : ℂ) (F : C(closedBall (0 : ℂ) r, ℂ)) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) r) : discExt r (c • F) z = c * discExt r F z := by
  simp only [discExt_apply r _ hz, ContinuousMap.smul_apply, smul_eq_mul]

theorem discExt_one {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) : discExt r 1 z = 1 := by
  simp only [discExt_apply r _ hz, ContinuousMap.one_apply]

theorem discExt_algebraMap (c : ℂ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    discExt r (algebraMap ℂ C(closedBall (0 : ℂ) r, ℂ) c) z = c := by
  simp only [discExt_apply r _ hz, Algebra.algebraMap_eq_smul_one, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one]

/-- The disc algebra: continuous on `|z| ≤ r`, analytic on `|z| < r`. -/
def discAlg : Subalgebra ℂ C(closedBall (0 : ℂ) r, ℂ) where
  carrier := {F | DifferentiableOn ℂ (discExt r F) (ball 0 r)}
  mul_mem' {F G} hF hG := (hF.mul hG).congr fun z hz =>
    discExt_mul r F G (ball_subset_closedBall hz)
  one_mem' := (differentiableOn_const 1).congr fun z hz => discExt_one r (ball_subset_closedBall hz)
  add_mem' {F G} hF hG := (hF.add hG).congr fun z hz =>
    discExt_add r F G (ball_subset_closedBall hz)
  zero_mem' := (differentiableOn_const 0).congr fun z hz => by
    simp only [discExt_apply r _ (ball_subset_closedBall hz), ContinuousMap.zero_apply]
  algebraMap_mem' c := (differentiableOn_const c).congr fun z hz =>
    discExt_algebraMap r c (ball_subset_closedBall hz)

theorem mem_discAlg {F : C(closedBall (0 : ℂ) r, ℂ)} :
    F ∈ discAlg r ↔ DifferentiableOn ℂ (discExt r F) (ball 0 r) := Iff.rfl

theorem isClosed_discAlg : IsClosed (discAlg r : Set C(closedBall (0 : ℂ) r, ℂ)) := by
  refine isClosed_of_closure_subset fun F hF => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hF
  have hunif : TendstoUniformly (fun n a => u n a) F atTop :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mp hlim
  show DifferentiableOn ℂ (discExt r F) (ball 0 r)
  refine TendstoLocallyUniformlyOn.differentiableOn (φ := atTop) (F := fun n => discExt r (u n))
    (TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_) (Eventually.of_forall hu) isOpen_ball
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Metric.tendstoUniformly_iff] at hunif
  filter_upwards [hunif ε hε] with n hn z hz
  rw [discExt_apply r _ (ball_subset_closedBall hz), discExt_apply r _ (ball_subset_closedBall hz)]
  exact hn ⟨z, ball_subset_closedBall hz⟩

instance : CompleteSpace (discAlg r) := (isClosed_discAlg r).completeSpace_coe

/-- The coordinate function `z ↦ z` on the closed disc. -/
noncomputable def discZ : discAlg r :=
  ⟨⟨fun x => (x : ℂ), continuous_subtype_val⟩, by
    rw [mem_discAlg]
    exact differentiableOn_id.congr fun z hz => by
      simp only [discExt_apply r _ (ball_subset_closedBall hz), ContinuousMap.coe_mk, id]⟩

theorem discExt_discZ {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) : discExt r (discZ r : _) z = z := by
  simp only [discZ, discExt_apply r _ hz, ContinuousMap.coe_mk]

/-- Elements of the disc algebra: values are bounded by the norm. -/
theorem norm_discExt_le (F : discAlg r) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖discExt r (F : C(closedBall (0 : ℂ) r, ℂ)) z‖ ≤ ‖F‖ := by
  rw [discExt_apply r _ hz]
  exact (ContinuousMap.norm_coe_le_norm (F : C(closedBall (0 : ℂ) r, ℂ)) ⟨z, hz⟩)

theorem differentiableOn_discExt (F : discAlg r) :
    DifferentiableOn ℂ (discExt r (F : C(closedBall (0 : ℂ) r, ℂ))) (ball 0 r) := F.2

end Azurite.DLMF
