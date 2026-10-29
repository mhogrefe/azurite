/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section10Residue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# DLMF §1.10(vi): Multivalued Functions

Formalizations of <https://dlmf.nist.gov/1.10.vi>. A many-valued function is a set-valued
`F : ℂ → Set ℂ`; a *branch* `IsBranch F f D` is an analytic `f` on a domain `D` with
`f(z) ∈ F(z)`.

* `√z` (`sqrtMV`): two-valued (`sqrtMV_eq`, `sqrtMV_two_valued`); branches `±√r e^{iθ/2}` on
  `ℂ \ (−∞, 0]` with `−π < θ < π` (`dlmf_1_10_vi_sqrt_slit`) and on `ℂ \ [0, ∞)` with
  `0 < θ < 2π` (`dlmf_1_10_vi_sqrt_upper`).
* Branch points (`IsBranchPoint`: a branch exists in a disk cut along a ray from `a`, but none
  in any punctured disk): `dlmf_1_10_vi_branchPoint_sqrt` (`0` for `√z`; around a circle
  `exp ∮ f′/f = 1` while `f′/f = 1/(2z)` gives `∮ f′/f = πi`).
* `F(z) = (1 − z)^α (1 + z)^β` (`powPairMV`): the principal branch on the cut plane `D` of
  Figure 1.10.1 (`dlmf_1_10_vi_powPair_branch`, `powPairPrin_eq_cpow`), real logarithms on
  `(−1, 1)` (`dlmf_1_10_vi_powPair_real`), branch points `±1` for `α, β ∉ ℤ`
  (`dlmf_1_10_vi_branchPoints_powPair`; even no *continuous* choice exists in a punctured disk,
  `not_continuous_powPair_punctured_one`).
* Analytic continuation along a closed curve (`ClosedPiecewiseC1`) avoiding `±1`: any continuous
  choice of values is multiplied by `e^{2πi 𝒩(C, 1) α} e^{2πi 𝒩(C, −1) β}`
  (`dlmf_1_10_vi_continuation`), giving DLMF's `e^{2πimα} e^{−2πinβ}` for `m` positive turns
  about `1` and `n` negative turns about `−1` (`dlmf_1_10_vi_continuation_mn`).

Tools: `eq_of_mapsTo_countable` (a continuous function on `[a, b]` with values in a countable
set is constant), `powPair_selection_eq` (continuous choices change like `e^{αℓ₁} e^{βℓ₂}` for
continuous logarithms `ℓ₁`, `ℓ₂`), `ClosedPiecewiseC1.exists_log_lift` and
`ClosedPiecewiseC1.log_lift_sub_eq` (continuous logarithms of `z − p` along a closed curve exist
and gain exactly `2πi 𝒩(C, p)`).
-/

open Filter Topology Set Metric Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Branches -/

/-- `f` is a branch of the multivalued function `F` (a set of values at each point) on the domain
`D`: `f` is analytic on `D` and `f(z)` is one of the values of `F(z)`. -/
def IsBranch (F : ℂ → Set ℂ) (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  IsOpen D ∧ IsPreconnected D ∧ DifferentiableOn ℂ f D ∧ ∀ z ∈ D, f z ∈ F z

/-- The two-valued square root `F(z) = √z`. -/
def sqrtMV (z : ℂ) : Set ℂ := {w | w ^ 2 = z}

/-- The principal square root `z^{1/2}`. -/
noncomputable def sqrtPrin (z : ℂ) : ℂ := z ^ ((2 : ℂ)⁻¹)

theorem sqrtPrin_sq (z : ℂ) : sqrtPrin z ^ 2 = z := by
  have := cpow_nat_inv_pow z (n := 2) two_ne_zero
  simp only [Nat.cast_ofNat] at this
  exact this

/-- DLMF §1.10(vi): `√z` is two-valued for `z ≠ 0`. -/
theorem sqrtMV_eq (z : ℂ) : sqrtMV z = {sqrtPrin z, -sqrtPrin z} := by
  ext w
  simp only [sqrtMV, Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    have : (w - sqrtPrin z) * (w + sqrtPrin z) = 0 := by
      rw [show (w - sqrtPrin z) * (w + sqrtPrin z) = w ^ 2 - sqrtPrin z ^ 2 by ring, h,
        sqrtPrin_sq, sub_self]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
  · rintro (rfl | rfl)
    · exact sqrtPrin_sq z
    · rw [neg_sq, sqrtPrin_sq]

theorem sqrtMV_two_valued {z : ℂ} (hz : z ≠ 0) : sqrtPrin z ≠ -sqrtPrin z := by
  intro h
  have h0 : sqrtPrin z = 0 := by linear_combination h / 2
  have := sqrtPrin_sq z
  rw [h0] at this
  exact hz (by simpa using this.symm)

/-- `(r e^{iθ})^{1/2} = √r e^{iθ/2}` for `r > 0`, `−π < θ < π`. -/
theorem sqrtPrin_polar {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo (-π) π) :
    sqrtPrin (r * exp (θ * I)) = Real.sqrt r * exp (θ / 2 * I) := by
  have hrexp : (r : ℂ) * exp (θ * I) = exp ((Real.log r : ℂ) + θ * I) := by
    rw [exp_add, ← ofReal_exp, Real.exp_log hr]
  have hlog : log ((r : ℂ) * exp (θ * I)) = (Real.log r : ℂ) + θ * I := by
    rw [hrexp, log_exp] <;> simp [hθ.1, hθ.2.le]
  have hne : (r : ℂ) * exp (θ * I) ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (exp_ne_zero _)
  rw [sqrtPrin, cpow_def_of_ne_zero hne, hlog]
  have hsq : (Real.sqrt r : ℂ) = exp ((Real.log r / 2 : ℝ) : ℂ) := by
    rw [← ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
    norm_num [div_eq_mul_inv]
  rw [hsq, ← exp_add]
  congr 1
  push_cast
  ring

theorem isPreconnected_slitPlane : IsPreconnected slitPlane :=
  (starConvex_one_slitPlane.isPathConnected
    (by simp [mem_slitPlane_iff])).isConnected.isPreconnected

/-- DLMF §1.10(vi): on `D = ℂ \ (−∞, 0]` the branches of `√z` are `±√r e^{iθ/2}`, `−π < θ < π`. -/
theorem dlmf_1_10_vi_sqrt_slit :
    IsBranch sqrtMV sqrtPrin slitPlane ∧ IsBranch sqrtMV (fun z => -sqrtPrin z) slitPlane ∧
      ∀ r θ : ℝ, 0 < r → θ ∈ Ioo (-π) π →
        sqrtPrin (r * exp (θ * I)) = Real.sqrt r * exp (θ / 2 * I) := by
  have hd : DifferentiableOn ℂ sqrtPrin slitPlane := fun z hz =>
    (differentiableAt_id.cpow_const hz).differentiableWithinAt
  refine ⟨⟨isOpen_slitPlane, isPreconnected_slitPlane, hd, fun z _ => sqrtPrin_sq z⟩,
    ⟨isOpen_slitPlane, isPreconnected_slitPlane, hd.neg, fun z _ => ?_⟩,
    fun r θ hr hθ => sqrtPrin_polar hr hθ⟩
  show (-sqrtPrin z) ^ 2 = z
  rw [neg_sq, sqrtPrin_sq]

/-- The branch `√r e^{iθ/2}`, `0 < θ < 2π`, on `ℂ \ [0, ∞)`: `i (−z)^{1/2}`. -/
noncomputable def sqrtUpper (z : ℂ) : ℂ := I * sqrtPrin (-z)

/-- DLMF §1.10(vi): on `D = ℂ \ [0, ∞)` the branches of `√z` are `±√r e^{iθ/2}`, `0 < θ < 2π`. -/
theorem dlmf_1_10_vi_sqrt_upper :
    IsBranch sqrtMV sqrtUpper {z | -z ∈ slitPlane} ∧
      IsBranch sqrtMV (fun z => -sqrtUpper z) {z | -z ∈ slitPlane} ∧
      ∀ r θ : ℝ, 0 < r → θ ∈ Ioo 0 (2 * π) →
        sqrtUpper (r * exp (θ * I)) = Real.sqrt r * exp (θ / 2 * I) := by
  have ho : IsOpen {z : ℂ | -z ∈ slitPlane} := isOpen_slitPlane.preimage continuous_neg
  have hc : IsPreconnected {z : ℂ | -z ∈ slitPlane} := by
    have : {z : ℂ | -z ∈ slitPlane} = (fun z => -z) '' slitPlane := by
      ext z
      simp only [Set.mem_ofPred_eq, mem_image]
      exact ⟨fun h => ⟨-z, h, neg_neg z⟩, by rintro ⟨w, hw, rfl⟩; rwa [neg_neg]⟩
    rw [this]
    exact isPreconnected_slitPlane.image _ continuous_neg.continuousOn
  have hd : DifferentiableOn ℂ sqrtUpper {z | -z ∈ slitPlane} := fun z hz =>
    ((differentiableAt_const I).mul
      ((differentiableAt_id.neg).cpow_const hz)).differentiableWithinAt
  have hsq : ∀ z, sqrtUpper z ^ 2 = z := fun z => by
    rw [sqrtUpper, mul_pow, I_sq, sqrtPrin_sq]
    ring
  refine ⟨⟨ho, hc, hd, fun z _ => hsq z⟩, ⟨ho, hc, hd.neg, fun z _ => ?_⟩, fun r θ hr hθ => ?_⟩
  · show (-sqrtUpper z) ^ 2 = z
    rw [neg_sq, hsq]
  · have hneg : -((r : ℂ) * exp (θ * I)) = r * exp (((θ - π : ℝ) : ℂ) * I) := by
      push_cast
      rw [sub_mul, exp_sub, exp_pi_mul_I]
      field_simp
    have hθ' : θ - π ∈ Ioo (-π) π := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    rw [sqrtUpper, hneg, sqrtPrin_polar hr hθ']
    have : exp ((((θ - π : ℝ) : ℂ) / 2) * I) = -I * exp (θ / 2 * I) := by
      push_cast
      rw [show ((θ : ℂ) - π) / 2 * I = θ / 2 * I + -(π / 2 * I) by ring, exp_add, exp_neg,
        exp_pi_div_two_mul_I, inv_I]
      ring
    rw [this]
    ring_nf
    rw [I_sq]
    ring

/-! ### Branch points -/

/-- A cut neighbourhood: the disk `|z − a| < r` with the ray `{a + t e^{iφ} : t ≥ 0}` removed. -/
def cutNbhd (a : ℂ) (r φ : ℝ) : Set ℂ :=
  ball a r \ {z | ∃ t : ℝ, 0 ≤ t ∧ z = a + t * exp (φ * I)}

/-- `a` is a branch point of `F`: `F` has a branch in a cut neighbourhood of `a`, but in no
punctured neighbourhood of `a`. -/
def IsBranchPoint (F : ℂ → Set ℂ) (a : ℂ) : Prop :=
  (∃ r > 0, ∃ φ : ℝ, ∃ f, IsBranch F f (cutNbhd a r φ)) ∧
    ∀ r > 0, ¬ ∃ f, IsBranch F f (ball a r \ {a})

theorem cutNbhd_zero_pi (r : ℝ) : cutNbhd 0 r π = ball 0 r ∩ slitPlane := by
  ext z
  simp only [cutNbhd, Set.mem_sdiff, Set.mem_ofPred_eq, mem_inter_iff, exp_pi_mul_I, zero_add,
    mul_neg, mul_one, mem_slitPlane_iff, not_exists, not_and]
  constructor
  · rintro ⟨hz, hray⟩
    refine ⟨hz, ?_⟩
    by_contra h
    push Not at h
    exact hray (-z.re) (by linarith [h.1]) (Complex.ext (by simp) (by simp [h.2]))
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun t ht hzt => ?_⟩
    rw [hzt] at h
    simp at h
    linarith

/-- The circle `s ↦ ρ e^{is}`. -/
noncomputable def circlePath (ρ : ℝ) (s : ℝ) : ℂ := (ρ : ℂ) * exp (s * I)

theorem contDiff_circlePath (ρ : ℝ) : ContDiff ℝ 1 (circlePath ρ) :=
  contDiff_const.mul (Complex.contDiff_exp.comp (ofRealCLM.contDiff.mul contDiff_const))

theorem norm_circlePath (ρ s : ℝ) : ‖circlePath ρ s‖ = |ρ| := by
  simp [circlePath, norm_exp_ofReal_mul_I]

theorem hasDerivAt_circlePath (ρ s : ℝ) : HasDerivAt (circlePath ρ) (circlePath ρ s * I) s := by
  unfold circlePath
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) * I) I s := by
    simpa using ((hasDerivAt_id s).ofReal_comp).mul_const I
  convert h.cexp.const_mul (ρ : ℂ) using 1
  ring

/-- The circle `ρ e^{is}`, `0 ≤ s ≤ 2π`, as a closed `C¹` curve. -/
noncomputable def circleCurve (ρ : ℝ) : JordanCurve.ClosedPiecewiseC1 (circlePath ρ) 0 (2 * π) where
  n := 1
  t := fun i => if i = 0 then 0 else 2 * π
  g := fun _ => circlePath ρ
  lt := fun i hi => by
    obtain rfl : i = 0 := by omega
    simp [Real.pi_pos]
  first := by simp
  last := by simp
  contDiff := fun _ _ => contDiff_circlePath ρ
  eqOn := fun _ _ _ _ => rfl
  closed := by
    simp only [circlePath, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, exp_two_pi_mul_I, mul_one]

/-- There is no branch of `√z` in any punctured neighbourhood of `0`: along a circle,
`exp(∮ f′/f) = 1`, while `f′/f = 1/(2z)` gives `∮ f′/f = πi`. -/
theorem not_isBranch_sqrt_punctured {r : ℝ} (hr : 0 < r) :
    ¬ ∃ f, IsBranch sqrtMV f (ball 0 r \ {0}) := by
  rintro ⟨f, hVo, -, hfd, hf⟩
  set ρ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  set P := circleCurve ρ
  have hmemV : ∀ s : ℝ, circlePath ρ s ∈ ball 0 r \ {0} := fun s => by
    refine ⟨by rw [mem_ball, dist_zero_right, norm_circlePath, abs_of_pos hρ0]; linarith,
      fun h => ?_⟩
    have := norm_circlePath ρ s
    rw [mem_singleton_iff.mp h, norm_zero, abs_of_pos hρ0] at this
    linarith
  have hcurve : P.curve ⊆ ball 0 r \ {0} := by
    rintro _ ⟨s, -, rfl⟩
    exact hmemV s
  have hsq : ∀ z ∈ ball 0 r \ {0}, f z ^ 2 = z := fun z hz => hf z hz
  have hfne : ∀ z ∈ ball 0 r \ {0}, f z ≠ 0 := fun z hz h => by
    have := hsq z hz
    rw [h] at this
    exact hz.2 (by simp [← this])
  have hexp := P.eq_exp_primitive_mul hVo hcurve hfd (fun z hz => hfne z (hcurve hz)) (2 * π)
    (right_mem_Icc.mpr (by positivity))
  -- the logarithmic derivative is `1/(2z)`
  have hlog : ∀ z ∈ ball 0 r \ {0}, deriv f z / f z = (2 * z)⁻¹ := by
    intro z hz
    have hfz : DifferentiableAt ℂ f z := hfd.differentiableAt (hVo.mem_nhds hz)
    have hev : (fun w => f w ^ 2) =ᶠ[𝓝 z] fun w => w :=
      eventually_of_mem (hVo.mem_nhds hz) hsq
    have h1 : HasDerivAt (fun w => f w ^ 2) (2 * f z * deriv f z) z := by
      convert hfz.hasDerivAt.fun_pow 2 using 1
      simp
    have h2 : 2 * f z * deriv f z = 1 := by
      rw [← h1.deriv, hev.deriv_eq, deriv_id'']
    have hfz0 := hfne z hz
    calc deriv f z / f z = (2 * f z ^ 2)⁻¹ := by
          field_simp
          linear_combination h2
      _ = (2 * z)⁻¹ := by rw [hsq z hz]
  have hint : ∫ s in (0 : ℝ)..2 * π,
      deriv f (circlePath ρ s) / f (circlePath ρ s) * deriv (circlePath ρ) s =
      π * I := by
    have : ∀ s ∈ uIcc (0 : ℝ) (2 * π),
        deriv f (circlePath ρ s) / f (circlePath ρ s) * deriv (circlePath ρ) s = I / 2 := by
      intro s _
      have hcs0 : circlePath ρ s ≠ 0 := fun h => (hmemV s).2 (mem_singleton_iff.mpr h)
      rw [hlog _ (hmemV s), (hasDerivAt_circlePath ρ s).deriv]
      field_simp
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  have hc0 : circlePath ρ (2 * π) = circlePath ρ 0 := P.closed.symm
  rw [hc0, hint] at hexp
  have hf0 : f (circlePath ρ 0) ≠ 0 := hfne _ (hmemV 0)
  have h1 : exp (π * I) = 1 := mul_right_cancel₀ hf0 (hexp.symm.trans (one_mul _).symm)
  rw [exp_pi_mul_I] at h1
  norm_num at h1

/-- DLMF §1.10(vi): `z = 0` is a branch point of `√z`. -/
theorem dlmf_1_10_vi_branchPoint_sqrt : IsBranchPoint sqrtMV 0 := by
  refine ⟨⟨1, one_pos, π, sqrtPrin, ?_⟩, fun r hr => not_isBranch_sqrt_punctured hr⟩
  rw [cutNbhd_zero_pi]
  have hsc : StarConvex ℝ ((1 / 2 : ℝ) : ℂ) (ball (0 : ℂ) 1 ∩ slitPlane) :=
    ((convex_ball (0 : ℂ) 1).starConvex (by simp; norm_num)).inter
      (starConvex_ofReal_slitPlane (by norm_num))
  have hmem : ((1 / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 ∩ slitPlane :=
    ⟨by simp; norm_num, by simp [mem_slitPlane_iff]⟩
  obtain ⟨-, -, hd, hval⟩ := dlmf_1_10_vi_sqrt_slit.1
  exact ⟨isOpen_ball.inter isOpen_slitPlane,
    (hsc.isPathConnected hmem).isConnected.isPreconnected,
    hd.mono inter_subset_right, fun z hz => hval z hz.2⟩

end Azurite.DLMF

namespace Azurite.DLMF

/-! ### Continuous selections with countably many choices -/

/-- A real function continuous on `[a, b]` with countable image is constant there. -/
theorem eq_of_countable_image_real {r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hr : ContinuousOn r (Icc a b)) (hc : (r '' Icc a b).Countable) : r b = r a := by
  have hp : IsPreconnected (r '' Icc a b) := isPreconnected_Icc.image r hr
  have ha : r a ∈ r '' Icc a b := mem_image_of_mem r (left_mem_Icc.mpr hab)
  have hb : r b ∈ r '' Icc a b := mem_image_of_mem r (right_mem_Icc.mpr hab)
  exact le_antisymm (Cardinal.Real.Icc_countable_iff.mp (hc.mono (hp.Icc_subset ha hb)))
    (Cardinal.Real.Icc_countable_iff.mp (hc.mono (hp.Icc_subset hb ha)))

/-- A complex function continuous on `[a, b]` with values in a countable set is constant there. -/
theorem eq_of_mapsTo_countable {q : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hq : ContinuousOn q (Icc a b)) {S : Set ℂ} (hS : S.Countable) (hmaps : MapsTo q (Icc a b) S) :
    q b = q a := by
  have hre := eq_of_countable_image_real (r := fun t => (q t).re) hab
    (continuous_re.comp_continuousOn hq)
    ((hS.image re).mono (by rintro _ ⟨t, ht, rfl⟩; exact ⟨q t, hmaps ht, rfl⟩))
  have him := eq_of_countable_image_real (r := fun t => (q t).im) hab
    (continuous_im.comp_continuousOn hq)
    ((hS.image im).mono (by rintro _ ⟨t, ht, rfl⟩; exact ⟨q t, hmaps ht, rfl⟩))
  exact Complex.ext hre him

/-! ### The function `(1 − z)^α (1 + z)^β` -/

/-- The many-valued function `F(z) = (1 − z)^α (1 + z)^β`: all `e^{α L₁} e^{β L₂}` with `L₁`,
`L₂` logarithms of `1 − z`, `1 + z`. -/
def powPairMV (α β z : ℂ) : Set ℂ :=
  {w | ∃ L₁ L₂ : ℂ, exp L₁ = 1 - z ∧ exp L₂ = 1 + z ∧ w = exp (α * L₁) * exp (β * L₂)}

/-- The branch of `(1 − z)^α (1 + z)^β` with principal values of the logarithms. -/
noncomputable def powPairPrin (α β z : ℂ) : ℂ := exp (α * log (1 - z)) * exp (β * log (1 + z))

theorem powPairPrin_eq_cpow (α β : ℂ) {z : ℂ} (h₁ : z ≠ 1) (h₂ : z ≠ -1) :
    powPairPrin α β z = (1 - z) ^ α * (1 + z) ^ β := by
  have h₁' : 1 - z ≠ 0 := sub_ne_zero.mpr h₁.symm
  have h₂' : 1 + z ≠ 0 := fun h => h₂ (by linear_combination h)
  rw [powPairPrin, cpow_def_of_ne_zero h₁', cpow_def_of_ne_zero h₂', mul_comm (log (1 - z)),
    mul_comm (log (1 + z))]

theorem ne_zero_of_mem_powPairMV {α β z w : ℂ} (hw : w ∈ powPairMV α β z) : w ≠ 0 := by
  obtain ⟨L₁, L₂, -, -, rfl⟩ := hw
  exact mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)

theorem powPairMV_neg (α β z : ℂ) : powPairMV α β (-z) = powPairMV β α z := by
  ext w
  simp only [powPairMV, Set.mem_ofPred_eq, sub_neg_eq_add, ← sub_eq_add_neg]
  exact ⟨fun ⟨L₁, L₂, h₁, h₂, hw⟩ => ⟨L₂, L₁, h₂, h₁, by rw [hw, mul_comm]⟩,
    fun ⟨L₁, L₂, h₁, h₂, hw⟩ => ⟨L₂, L₁, h₂, h₁, by rw [hw, mul_comm]⟩⟩

/-- The cut plane `D`: `ℂ` with `[1, ∞)` and `(−∞, −1]` removed (Figure 1.10.1). -/
def cutPlanePM1 : Set ℂ := {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane}

theorem starConvex_cutPlanePM1 : StarConvex ℝ 0 cutPlanePM1 := by
  intro z hz s t hs ht hst
  have key : ∀ w : ℂ, w ∈ slitPlane → s • (1 : ℂ) + t • w ∈ slitPlane := fun w hw =>
    starConvex_one_slitPlane hw hs ht hst
  have hst' : (s : ℂ) + t = 1 := by exact_mod_cast hst
  refine ⟨?_, ?_⟩
  · convert key _ hz.1 using 1
    simp only [smul_zero, zero_add, Complex.real_smul, mul_one]
    linear_combination -hst'
  · convert key _ hz.2 using 1
    simp only [smul_zero, zero_add, Complex.real_smul, mul_one]
    linear_combination -hst'

/-- DLMF §1.10(vi): assigning `(1 − z)^α` and `(1 + z)^β` their principal values gives a branch
of `(1 − z)^α (1 + z)^β` in the cut plane `D`. -/
theorem dlmf_1_10_vi_powPair_branch (α β : ℂ) :
    IsBranch (powPairMV α β) (powPairPrin α β) cutPlanePM1 := by
  refine ⟨(isOpen_slitPlane.preimage (continuous_const.sub continuous_id)).inter
      (isOpen_slitPlane.preimage (continuous_const.add continuous_id)),
    (starConvex_cutPlanePM1.isPathConnected
      ⟨by simp [mem_slitPlane_iff], by simp [mem_slitPlane_iff]⟩).isConnected.isPreconnected,
    fun z hz => ?_, fun z hz => ⟨_, _, exp_log (slitPlane_ne_zero hz.1),
      exp_log (slitPlane_ne_zero hz.2), rfl⟩⟩
  have h₁ : DifferentiableAt ℂ (fun z : ℂ => log (1 - z)) z :=
    ((differentiableAt_const _).sub differentiableAt_id).clog hz.1
  have h₂ : DifferentiableAt ℂ (fun z : ℂ => log (1 + z)) z :=
    ((differentiableAt_const _).add differentiableAt_id).clog hz.2
  exact (((h₁.const_mul α).cexp).mul ((h₂.const_mul β).cexp)).differentiableWithinAt

/-- DLMF §1.10(vi): for `z₀ ∈ (−1, 1)` the principal logarithms of `1 ∓ z₀` are real. -/
theorem dlmf_1_10_vi_powPair_real {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    log (1 - (x : ℂ)) = (Real.log (1 - x) : ℂ) ∧ log (1 + (x : ℂ)) = (Real.log (1 + x) : ℂ) := by
  constructor
  · rw [ofReal_log (by linarith [hx.2])]
    push_cast
    rfl
  · rw [ofReal_log (by linarith [hx.1])]
    push_cast
    rfl

/-- Along a path, a continuous choice `Φ` of values of `(1 − z)^α (1 + z)^β` changes exactly as
`e^{α ℓ₁} e^{β ℓ₂}` for continuous logarithms `ℓ₁`, `ℓ₂` of `1 − z`, `1 + z`. -/
theorem powPair_selection_eq (α β : ℂ) {c : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) {ℓ₁ ℓ₂ Φ : ℝ → ℂ}
    (hℓ₁ : ContinuousOn ℓ₁ (Icc a b)) (hℓ₂ : ContinuousOn ℓ₂ (Icc a b))
    (he₁ : ∀ t ∈ Icc a b, exp (ℓ₁ t) = 1 - c t) (he₂ : ∀ t ∈ Icc a b, exp (ℓ₂ t) = 1 + c t)
    (hΦ : ContinuousOn Φ (Icc a b)) (hval : ∀ t ∈ Icc a b, Φ t ∈ powPairMV α β (c t)) :
    Φ b * (exp (α * ℓ₁ a) * exp (β * ℓ₂ a)) = Φ a * (exp (α * ℓ₁ b) * exp (β * ℓ₂ b)) := by
  set Ψ : ℝ → ℂ := fun t => exp (α * ℓ₁ t) * exp (β * ℓ₂ t) with hΨ
  have hΨ0 : ∀ t, Ψ t ≠ 0 := fun t => mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)
  have hΨc : ContinuousOn Ψ (Icc a b) :=
    ((continuousOn_const.mul hℓ₁).cexp).mul ((continuousOn_const.mul hℓ₂).cexp)
  set S : Set ℂ := range fun jk : ℤ × ℤ =>
    exp (α * (jk.1 * (2 * π * I))) * exp (β * (jk.2 * (2 * π * I)))
  have hq := eq_of_mapsTo_countable (q := fun t => Φ t / Ψ t) hab
    (hΦ.div hΨc fun t _ => hΨ0 t) (S := S) (countable_range _) (fun t ht => by
      obtain ⟨L₁, L₂, h₁, h₂, hw⟩ := hval t ht
      obtain ⟨j, hj⟩ := exp_eq_exp_iff_exists_int.mp (h₁.trans (he₁ t ht).symm)
      obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp (h₂.trans (he₂ t ht).symm)
      refine ⟨(j, k), ?_⟩
      simp only [hw, hΨ, hj, hk, mul_add, exp_add]
      field_simp)
  rw [div_eq_div_iff (hΨ0 b) (hΨ0 a)] at hq
  exact hq

end Azurite.DLMF

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

open Azurite.DLMF

/-- A continuous logarithm of `z − p` along a closed curve: if `e^{ℓ(t)} = c(t) − p` with `ℓ`
continuous, then `ℓ(b) − ℓ(a) = 2πi 𝒩(C, p)`. -/
theorem log_lift_sub_eq {p : ℂ} (hp : p ∉ P.curve) {ℓ : ℝ → ℂ} (hℓ : ContinuousOn ℓ (Icc a b))
    (he : ∀ t ∈ Icc a b, exp (ℓ t) = c t - p) :
    ℓ b - ℓ a = 2 * π * I * P.windingNumber p := by
  have hab := P.a_le_b
  have hph : ∀ t ∈ Icc a b,
      (fun z => z - p) (c t) = ‖(fun z => z - p) (c t)‖ * exp ((ℓ t).im * I) := by
    intro t ht
    simp only
    rw [← he t ht, norm_exp, ofReal_exp, ← exp_add]
    conv_lhs => rw [← re_add_im (ℓ t)]
  have h := P.contourIntegral_logDeriv_eq_phase (h := fun z => z - p) (V := {p}ᶜ)
    isOpen_compl_singleton (fun z hz hzp => hp (by rwa [mem_singleton_iff.mp hzp] at hz))
    (by fun_prop) (fun z hz => sub_ne_zero.mpr fun e => hp (e ▸ hz))
    (θ := fun t => (ℓ t).im) (continuous_im.comp_continuousOn hℓ) hph
  have hcongr : P.contourIntegral (fun z => deriv (fun z => z - p) z / (z - p)) =
      P.contourIntegral (fun z => (z - p)⁻¹) := by
    congr 1
    funext z
    simp
  rw [hcongr, P.contourIntegral_inv_eq hp] at h
  have hre : (ℓ b).re = (ℓ a).re := Real.exp_injective (by
    rw [← norm_exp, ← norm_exp, he b (right_mem_Icc.mpr hab), he a (left_mem_Icc.mpr hab),
      P.closed])
  rw [h]
  apply Complex.ext <;> simp [hre]

/-- Continuous logarithms of `z − p` exist along a closed curve avoiding `p`, starting from any
logarithm of `c(a) − p`. -/
theorem exists_log_lift {p : ℂ} (hp : p ∉ P.curve) {L₀ : ℂ} (hL₀ : exp L₀ = c a - p) :
    ∃ ℓ : ℝ → ℂ, ContinuousOn ℓ (Icc a b) ∧ ℓ a = L₀ ∧ ∀ t ∈ Icc a b, exp (ℓ t) = c t - p := by
  have hab := P.a_le_b
  have h0 : ∀ z ∈ P.curve, z - p ≠ 0 := fun z hz => sub_ne_zero.mpr fun e => hp (e ▸ hz)
  have key := P.eq_exp_primitive_mul (h := fun z => z - p) (V := {p}ᶜ) isOpen_compl_singleton
    (fun z hz hzp => hp (by rwa [mem_singleton_iff.mp hzp] at hz)) (by fun_prop) h0
  simp only [deriv_sub_const, deriv_id'', one_div] at key
  have hFc : ContinuousOn (fun z : ℂ => (z - p)⁻¹) P.curve :=
    (continuousOn_id.sub continuousOn_const).inv₀ h0
  have hint : IntervalIntegrable (fun s => (c s - p)⁻¹ * deriv c s) MeasureTheory.volume a b :=
    P.intervalIntegrable_full hFc
  refine ⟨fun t => (∫ s in a..t, (c s - p)⁻¹ * deriv c s) + L₀, ?_, by simp, fun t ht => ?_⟩
  · refine ContinuousOn.add ?_ continuousOn_const
    have h1 : ContinuousOn (fun t => ∫ s in a..t, (c s - p)⁻¹ * deriv c s) (uIcc a b) :=
      intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    rwa [uIcc_of_le hab] at h1
  · rw [exp_add, hL₀]
    exact (key t ht).symm

/-- DLMF §1.10(vi): continuing `F(z) = (1 − z)^α (1 + z)^β` along a closed curve avoiding `±1`
multiplies its value by `e^{2πi 𝒩(C, 1) α} e^{2πi 𝒩(C, −1) β}`. -/
theorem dlmf_1_10_vi_continuation (α β : ℂ) (h₁ : (1 : ℂ) ∉ P.curve) (h₂ : (-1 : ℂ) ∉ P.curve)
    {Φ : ℝ → ℂ} (hΦ : ContinuousOn Φ (Icc a b))
    (hval : ∀ t ∈ Icc a b, Φ t ∈ powPairMV α β (c t)) :
    Φ b = Φ a * exp (2 * π * I * P.windingNumber 1 * α) *
      exp (2 * π * I * P.windingNumber (-1) * β) := by
  have hab := P.a_le_b
  have hca : c a ∈ P.curve := mem_image_of_mem c (left_mem_Icc.mpr hab)
  have hne₁ : 1 - c a ≠ 0 := sub_ne_zero.mpr fun e => h₁ (e ▸ hca)
  have hne₂ : 1 + c a ≠ 0 := fun e => h₂ (by
    rw [show (-1 : ℂ) = c a by linear_combination -e]
    exact hca)
  obtain ⟨m₁, hm₁c, -, hm₁⟩ := P.exists_log_lift h₁ (L₀ := log (1 - c a) - π * I)
    (by rw [exp_sub, exp_log hne₁, exp_pi_mul_I]; ring)
  obtain ⟨ℓ₂, hℓ₂c, -, he₂⟩ := P.exists_log_lift h₂ (L₀ := log (1 + c a))
    (by rw [exp_log hne₂]; ring)
  have k₁ := P.log_lift_sub_eq h₁ hm₁c hm₁
  have k₂ := P.log_lift_sub_eq h₂ hℓ₂c he₂
  have hsel := powPair_selection_eq α β hab (ℓ₁ := fun t => m₁ t + π * I) (ℓ₂ := ℓ₂)
    (hm₁c.add continuousOn_const) hℓ₂c
    (fun t ht => by rw [exp_add, hm₁ t ht, exp_pi_mul_I]; ring)
    (fun t ht => by rw [he₂ t ht]; ring) hΦ hval
  have hb₁ : α * (m₁ b + π * I) = α * (m₁ a + π * I) + 2 * π * I * P.windingNumber 1 * α := by
    linear_combination α * k₁
  have hb₂ : β * ℓ₂ b = β * ℓ₂ a + 2 * π * I * P.windingNumber (-1) * β := by
    linear_combination β * k₂
  simp only [hb₁, hb₂, exp_add] at hsel
  have hX : exp (α * (m₁ a + π * I)) * exp (β * ℓ₂ a) ≠ 0 :=
    mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)
  apply mul_right_cancel₀ hX
  linear_combination hsel

/-- DLMF §1.10(vi): if the curve starts at `z₀`, the continuation starts from the principal
value, and the curve circles `1` `m` times positively and `−1` `n` times negatively, the final
value is `e^{α ln(1 − z₀)} e^{β ln(1 + z₀)} e^{2πimα} e^{−2πinβ}`. -/
theorem dlmf_1_10_vi_continuation_mn (α β : ℂ) (h₁ : (1 : ℂ) ∉ P.curve)
    (h₂ : (-1 : ℂ) ∉ P.curve) {Φ : ℝ → ℂ} (hΦ : ContinuousOn Φ (Icc a b))
    (hval : ∀ t ∈ Icc a b, Φ t ∈ powPairMV α β (c t)) (ha : Φ a = powPairPrin α β (c a))
    {m n : ℤ} (hm : P.windingNumber 1 = m) (hn : P.windingNumber (-1) = -n) :
    Φ b = exp (α * log (1 - c a)) * exp (β * log (1 + c a)) * exp (2 * π * I * m * α) *
      exp (-2 * π * I * n * β) := by
  rw [P.dlmf_1_10_vi_continuation α β h₁ h₂ hΦ hval, ha, hm, hn, powPairPrin]
  push_cast
  ring_nf

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

/-! ### Branch points of `(1 − z)^α (1 + z)^β` -/

/-- No continuous choice of `(1 − z)^α (1 + z)^β`, `α ∉ ℤ`, exists in a punctured disk about `1`:
around the circle `1 + ρ e^{is}` it would gain the factor `e^{2πiα} ≠ 1`. -/
theorem not_continuous_powPair_punctured_one {α β : ℂ} (hα : ∀ n : ℤ, α ≠ n) {r : ℝ}
    (hr : 0 < r) :
    ¬ ∃ f, ContinuousOn f (ball 1 r \ {1}) ∧ ∀ z ∈ ball 1 r \ {1}, f z ∈ powPairMV α β z := by
  rintro ⟨f, hfc, hf⟩
  set ρ := min (r / 2) 1 with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) one_pos
  have hρr : ρ < r := (min_le_left _ _).trans_lt (by linarith)
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  set γ : ℝ → ℂ := fun s => 1 + circlePath ρ s with hγ
  have hγc : Continuous γ := continuous_const.add (contDiff_circlePath ρ).continuous
  have hmem : ∀ s, γ s ∈ ball 1 r \ {1} := fun s => by
    refine ⟨?_, fun h => ?_⟩
    · rw [mem_ball, dist_eq_norm, hγ]
      simp only [add_sub_cancel_left, norm_circlePath, abs_of_pos hρ0]
      exact hρr
    · have := norm_circlePath ρ s
      have h0 : circlePath ρ s = 0 := by simpa [hγ] using h
      rw [h0, norm_zero, abs_of_pos hρ0] at this
      linarith
  have hre : ∀ s, 0 < (1 + γ s).re := fun s => by
    have h1 := abs_re_le_norm (circlePath ρ s)
    rw [norm_circlePath, abs_of_pos hρ0] at h1
    simp only [hγ, add_re, one_re]
    linarith [neg_abs_le (circlePath ρ s).re]
  have hslit : ∀ s, 1 + γ s ∈ slitPlane := fun s => mem_slitPlane_iff.mpr (Or.inl (hre s))
  have hsel := powPair_selection_eq α β (c := γ) (a := 0) (b := 2 * π) (by positivity)
    (ℓ₁ := fun s => (Real.log ρ : ℂ) + (s + π) * I) (ℓ₂ := fun s => log (1 + γ s))
    (Φ := fun s => f (γ s)) (by fun_prop)
    ((continuous_const.add hγc).continuousOn.clog fun s _ => hslit s)
    (fun s _ => by
      simp only [hγ, circlePath, add_mul, exp_add, ← ofReal_exp, Real.exp_log hρ0, exp_pi_mul_I]
      ring)
    (fun s _ => exp_log (slitPlane_ne_zero (hslit s)))
    (hfc.comp hγc.continuousOn fun s _ => hmem s) (fun s _ => hf _ (hmem s))
  have hγ2 : γ (2 * π) = γ 0 := by
    simp only [hγ, circlePath, ofReal_zero, zero_mul, Complex.exp_zero]
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, exp_two_pi_mul_I]
  simp only [hγ2] at hsel
  have hf0 : f (γ 0) ≠ 0 := ne_zero_of_mem_powPairMV (hf _ (hmem 0))
  have hX : exp (α * ((Real.log ρ : ℂ) + ((0 : ℝ) + π) * I)) * exp (β * log (1 + γ 0)) ≠ 0 :=
    mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)
  have hexp : exp (α * (2 * π * I)) = 1 := by
    have h2 : α * ((Real.log ρ : ℂ) + (((2 * π : ℝ) : ℂ) + π) * I) =
        α * ((Real.log ρ : ℂ) + ((0 : ℝ) + π) * I) + α * (2 * π * I) := by
      push_cast
      ring
    rw [h2, exp_add] at hsel
    apply mul_left_cancel₀ (mul_ne_zero hf0 hX)
    linear_combination -hsel
  obtain ⟨n, hn⟩ := exp_eq_one_iff.mp hexp
  exact hα n (mul_right_cancel₀ two_pi_I_ne_zero (by rw [hn]))

/-- No continuous choice of `(1 − z)^α (1 + z)^β`, `β ∉ ℤ`, exists in a punctured disk about
`−1`. -/
theorem not_continuous_powPair_punctured_neg_one {α β : ℂ} (hβ : ∀ n : ℤ, β ≠ n) {r : ℝ}
    (hr : 0 < r) :
    ¬ ∃ f, ContinuousOn f (ball (-1) r \ {-1}) ∧
      ∀ z ∈ ball (-1) r \ {-1}, f z ∈ powPairMV α β z := by
  rintro ⟨f, hfc, hf⟩
  have hmaps : MapsTo (fun z : ℂ => -z) (ball 1 r \ {1}) (ball (-1) r \ {-1}) := by
    rintro z ⟨hz, hz1⟩
    refine ⟨?_, fun h => hz1 ?_⟩
    · rw [mem_ball, dist_neg_neg]
      exact hz
    · have : -z = -1 := h
      exact neg_inj.mp this
  refine not_continuous_powPair_punctured_one (β := α) hβ hr
    ⟨fun z => f (-z), hfc.comp continuous_neg.continuousOn hmaps, fun z hz => ?_⟩
  rw [← powPairMV_neg]
  exact hf _ (hmaps hz)

theorem IsBranch.continuousOn {F : ℂ → Set ℂ} {f : ℂ → ℂ} {D : Set ℂ} (h : IsBranch F f D) :
    ContinuousOn f D :=
  h.2.2.1.continuousOn

theorem mem_slitPlane_iff_not_ray (w : ℂ) : w ∈ slitPlane ↔ ¬ ∃ t : ℝ, 0 ≤ t ∧ w = -t := by
  have := Set.ext_iff.mp (cutNbhd_zero_pi (‖w‖ + 1)) w
  simp only [cutNbhd, Set.mem_sdiff, Set.mem_ofPred_eq, mem_inter_iff, exp_pi_mul_I, zero_add,
    mul_neg, mul_one, mem_ball, dist_zero_right, lt_add_one, true_and] at this
  exact this.symm

theorem cutNbhd_one (r : ℝ) : cutNbhd 1 r 0 = {z | 1 - z ∈ ball 0 r ∩ slitPlane} := by
  ext z
  simp only [cutNbhd, Set.mem_sdiff, Set.mem_ofPred_eq, mem_inter_iff, mem_ball,
    dist_zero_right, mem_slitPlane_iff_not_ray, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [dist_eq_norm, norm_sub_rev]
  refine and_congr_right fun _ => not_congr (exists_congr fun t => and_congr_right fun _ => ?_)
  constructor <;> intro h <;> linear_combination -h

theorem cutNbhd_neg_one (r : ℝ) : cutNbhd (-1) r π = {z | 1 + z ∈ ball 0 r ∩ slitPlane} := by
  ext z
  simp only [cutNbhd, Set.mem_sdiff, Set.mem_ofPred_eq, mem_inter_iff, mem_ball,
    dist_zero_right, mem_slitPlane_iff_not_ray, exp_pi_mul_I, mul_neg, mul_one]
  rw [dist_eq_norm, sub_neg_eq_add, add_comm z]
  refine and_congr_right fun _ => not_congr (exists_congr fun t => and_congr_right fun _ => ?_)
  constructor <;> intro h <;> linear_combination h

theorem isPreconnected_ball_inter_slitPlane : IsPreconnected (ball (0 : ℂ) 1 ∩ slitPlane) := by
  have hsc : StarConvex ℝ ((1 / 2 : ℝ) : ℂ) (ball (0 : ℂ) 1 ∩ slitPlane) :=
    ((convex_ball (0 : ℂ) 1).starConvex (by simp; norm_num)).inter
      (starConvex_ofReal_slitPlane (by norm_num))
  have hmem : ((1 / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 ∩ slitPlane :=
    ⟨by simp; norm_num, by simp [mem_slitPlane_iff]⟩
  exact (hsc.isPathConnected hmem).isConnected.isPreconnected

theorem IsBranch.mono {F : ℂ → Set ℂ} {f : ℂ → ℂ} {D D' : Set ℂ} (h : IsBranch F f D)
    (hD' : D' ⊆ D) (ho : IsOpen D') (hc : IsPreconnected D') : IsBranch F f D' :=
  ⟨ho, hc, h.2.2.1.mono hD', fun z hz => h.2.2.2 z (hD' hz)⟩

/-- DLMF §1.10(vi): for non-integer `α`, `β`, `(1 − z)^α (1 + z)^β` has branch points at `±1`. -/
theorem dlmf_1_10_vi_branchPoints_powPair {α β : ℂ} (hα : ∀ n : ℤ, α ≠ n)
    (hβ : ∀ n : ℤ, β ≠ n) :
    IsBranchPoint (powPairMV α β) 1 ∧ IsBranchPoint (powPairMV α β) (-1) := by
  have hU := isPreconnected_ball_inter_slitPlane
  have hUo : IsOpen (ball (0 : ℂ) 1 ∩ slitPlane) := isOpen_ball.inter isOpen_slitPlane
  have hre : ∀ w ∈ ball (0 : ℂ) 1, 0 < 2 - w.re := fun w hw => by
    have := (re_le_norm w).trans_lt (mem_ball_zero_iff.mp hw)
    linarith
  have hbr := dlmf_1_10_vi_powPair_branch α β
  refine ⟨⟨⟨1, one_pos, 0, powPairPrin α β, hbr.mono ?_ ?_ ?_⟩,
      fun r hr ⟨f, hf⟩ =>
        not_continuous_powPair_punctured_one hα hr ⟨f, hf.continuousOn, hf.2.2.2⟩⟩,
    ⟨⟨1, one_pos, π, powPairPrin α β, hbr.mono ?_ ?_ ?_⟩, fun r hr ⟨f, hf⟩ =>
      not_continuous_powPair_punctured_neg_one hβ hr ⟨f, hf.continuousOn, hf.2.2.2⟩⟩⟩
  · rw [cutNbhd_one]
    intro z hz
    refine ⟨hz.2, mem_slitPlane_iff.mpr (Or.inl ?_)⟩
    have := hre _ hz.1
    simp only [sub_re, one_re] at this
    simp only [add_re, one_re]
    linarith
  · rw [cutNbhd_one]
    exact hUo.preimage (continuous_const.sub continuous_id)
  · rw [cutNbhd_one]
    have : {z : ℂ | 1 - z ∈ ball 0 1 ∩ slitPlane} =
        (fun w => 1 - w) '' (ball (0 : ℂ) 1 ∩ slitPlane) := by
      ext z
      exact ⟨fun h => ⟨1 - z, h, by ring⟩, by rintro ⟨w, hw, rfl⟩; simpa using hw⟩
    rw [this]
    exact hU.image _ (continuous_const.sub continuous_id).continuousOn
  · rw [cutNbhd_neg_one]
    intro z hz
    refine ⟨mem_slitPlane_iff.mpr (Or.inl ?_), hz.2⟩
    have := hre _ hz.1
    simp only [add_re, one_re] at this
    simp only [sub_re, one_re]
    linarith
  · rw [cutNbhd_neg_one]
    exact hUo.preimage (continuous_const.add continuous_id)
  · rw [cutNbhd_neg_one]
    have : {z : ℂ | 1 + z ∈ ball 0 1 ∩ slitPlane} =
        (fun w => w - 1) '' (ball (0 : ℂ) 1 ∩ slitPlane) := by
      ext z
      exact ⟨fun h => ⟨1 + z, h, by ring⟩, by rintro ⟨w, hw, rfl⟩; simpa using hw⟩
    rw [this]
    exact hU.image _ (continuous_id.sub continuous_const).continuousOn

end Azurite.DLMF
