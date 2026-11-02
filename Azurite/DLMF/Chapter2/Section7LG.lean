/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section7LGVolterra
import Azurite.DLMF.Chapter1.Section4
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# DLMF §2.7(iii): Liouville–Green (WKBJ) Approximation — the theorem, 2.7.20–2.7.27

In an open interval `I = (a₁, a₂)` (finite or infinite) let `f` be real, positive and `C²`, `g`
continuous (`LGSetup`, with `ξ` any antiderivative of `f^{1/2}`, DLMF's `∫ f^{1/2}(x) dx`).

* 2.7.20 (`IsLGSolution`): `w″ = (f + g) w`, `w` twice continuously differentiable.
* 2.7.24 (`lgControl`): the error-control integrand
  `F′ = f^{−1/4} (f^{−1/4})″ − g f^{−1/2}`; 2.7.25 (`volterraV`, `lgVarUpper`):
  `𝒱_{a₁,x}(F) = ∫_{a₁}^{x} |F′|`, `𝒱_{a₂,x}(F) = ∫_{x}^{a₂} |F′|`; `dlmf_2_7_25` identifies the
  increments with the total variation of any antiderivative `F` (§2.3(i), §1.4(v)).
* 2.7.21–2.7.23 (`LGSetup.dlmf_2_7_21`, `LGSetup.dlmf_2_7_22`): when `𝒱_{a_j,x}(F) < ∞` there
  are solutions `w₁ = f^{−1/4} e^{∫f^{1/2}} (1 + ε₁)`, `w₂ = f^{−1/4} e^{−∫f^{1/2}} (1 + ε₂)` with
  `|ε_j(x)|, ½ f^{−1/2}(x) |ε_j′(x)| ≤ exp(½ 𝒱_{a_j,x}(F)) − 1`.
* 2.7.26–2.7.27 (`LGSetup.dlmf_2_7_26`, `LGSetup.dlmf_2_7_27`):
  `w₁ ∼ f^{−1/4} e^{∫f^{1/2}}` as `x → a₁+`, `w₂ ∼ f^{−1/4} e^{−∫f^{1/2}}` as `x → a₂−`.

`w₁` comes from the Volterra equation of `Section7LGVolterra` (Liouville's substitution
`w = f^{−1/4} e^{ξ} u`); `w₂` from `w₁` for the reflected equation `x ↦ −x`.
-/

open Filter Topology Set MeasureTheory

namespace Azurite.DLMF

/-! ### Definitions -/

/-- `f^{−1/4}`. -/
noncomputable def lgPhi (f : ℝ → ℝ) (x : ℝ) : ℝ := f x ^ (-(1 / 4 : ℝ))

/-- **DLMF 2.7.24**: the integrand of the error-control function,
`F′(x) = f^{−1/4} d²/dx² (f^{−1/4}) − g f^{−1/2}`. -/
noncomputable def lgControl (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  lgPhi f x * deriv (deriv (lgPhi f)) x - g x / Real.sqrt (f x)

/-- **DLMF 2.7.25** for `j = 2`: `𝒱_{a₂,x}(F) = ∫_{x}^{a₂} |F′|`. -/
noncomputable def lgVarUpper (I : Set ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ v in I ∩ Ici x, |lgControl f g v|

/-- **DLMF 2.7.20**: `w` is a twice continuously differentiable solution of `w″ = (f + g) w`
on `I`. -/
def IsLGSolution (I : Set ℝ) (f g w : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 w I ∧ ∀ x ∈ I, deriv (deriv w) x = (f x + g x) * w x

/-- Hypotheses of the Liouville–Green theorem: `I` an open interval, `f > 0` of class `C²`, `g`
continuous, `ξ′ = f^{1/2}`. -/
structure LGSetup (I : Set ℝ) (f g ξ : ℝ → ℝ) : Prop where
  isOpen : IsOpen I
  ordConnected : I.OrdConnected
  nonempty : I.Nonempty
  f_pos : ∀ x ∈ I, 0 < f x
  f_contDiff : ContDiffOn ℝ 2 f I
  g_cont : ContinuousOn g I
  ξ_deriv : ∀ x ∈ I, HasDerivAt ξ (Real.sqrt (f x)) x

/-- A function with `w′`, `w″` on the open set `I` and `w″` continuous is `C²` there. -/
theorem contDiffOn_two_of_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {w w' w'' : ℝ → ℝ}
    (h1 : ∀ x ∈ I, HasDerivAt w (w' x) x) (h2 : ∀ x ∈ I, HasDerivAt w' (w'' x) x)
    (h3 : ContinuousOn w'' I) : ContDiffOn ℝ 2 w I := by
  have hd1 : EqOn (deriv w) w' I := fun x hx => (h1 x hx).deriv
  have hd2 : EqOn (deriv w') w'' I := fun x hx => (h2 x hx).deriv
  have hw' : ContDiffOn ℝ 1 w' I := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hI]
    refine ⟨fun x hx => (h2 x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact h3.congr hd2
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hI]
  exact ⟨fun x hx => (h1 x hx).differentiableAt.differentiableWithinAt, by simp,
    hw'.congr hd1⟩

theorem IsLGSolution.of_hasDerivAt {I : Set ℝ} (hI : IsOpen I) {f g w w' : ℝ → ℝ}
    (hfg : ContinuousOn (fun x => f x + g x) I) (h1 : ∀ x ∈ I, HasDerivAt w (w' x) x)
    (h2 : ∀ x ∈ I, HasDerivAt w' ((f x + g x) * w x) x) : IsLGSolution I f g w := by
  have hwc : ContinuousOn w I := fun x hx => (h1 x hx).continuousAt.continuousWithinAt
  refine ⟨contDiffOn_two_of_hasDerivAt hI h1 h2 (hfg.mul hwc), fun x hx => ?_⟩
  have : deriv w =ᶠ[𝓝 x] w' :=
    Filter.eventually_of_mem (hI.mem_nhds hx) fun y hy => (h1 y hy).deriv
  rw [this.deriv_eq]
  exact (h2 x hx).deriv

/-! ### Reflection `x ↦ −x` -/

theorem setIntegral_comp_neg (s : Set ℝ) (h : ℝ → ℝ) :
    ∫ x in Neg.neg ⁻¹' s, h (-x) = ∫ y in s, h y := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have := A.setIntegral_map (μ := volume) h s
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at this
  exact this.symm

theorem integrableOn_comp_neg_iff (s : Set ℝ) (h : ℝ → ℝ) :
    IntegrableOn (fun x => h (-x)) (Neg.neg ⁻¹' s) ↔ IntegrableOn h s := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have := A.integrableOn_map_iff (μ := volume) (f := h) (s := s)
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at this
  exact this.symm

theorem deriv_deriv_comp_neg (h : ℝ → ℝ) (x : ℝ) :
    deriv (deriv fun y => h (-y)) x = deriv (deriv h) (-x) := by
  have e : deriv (fun y => h (-y)) = fun y => -deriv h (-y) :=
    funext fun y => deriv_comp_neg h y
  rw [e, show (fun y => -deriv h (-y)) = -fun y => deriv h (-y) from rfl, deriv.neg,
    deriv_comp_neg (deriv h) x, neg_neg]

theorem lgControl_reflect (f g : ℝ → ℝ) (x : ℝ) :
    lgControl (fun x => f (-x)) (fun x => g (-x)) x = lgControl f g (-x) := by
  have : lgPhi (fun x => f (-x)) = fun x => lgPhi f (-x) := rfl
  simp only [lgControl]
  rw [this, deriv_deriv_comp_neg]

theorem lgVarUpper_eq (I : Set ℝ) (f g : ℝ → ℝ) (x : ℝ) : lgVarUpper I f g x =
    volterraV (Neg.neg ⁻¹' I) (lgControl (fun x => f (-x)) (fun x => g (-x))) (-x) := by
  rw [volterraV, lgVarUpper]
  have hset : Neg.neg ⁻¹' I ∩ Iic (-x) = Neg.neg ⁻¹' (I ∩ Ici x) := by
    ext v; simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ici]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  simp only [lgControl_reflect]
  rw [hset, setIntegral_comp_neg (I ∩ Ici x) fun v => |lgControl f g v|]

namespace LGSetup

variable {I : Set ℝ} {f g ξ : ℝ → ℝ} (S : LGSetup I f g ξ)
include S

theorem phi_contDiff : ContDiffOn ℝ 2 (lgPhi f) I :=
  S.f_contDiff.rpow_const_of_ne fun x hx => (S.f_pos x hx).ne'

theorem phi_hasDerivAt {x : ℝ} (hx : x ∈ I) : HasDerivAt (lgPhi f) (deriv (lgPhi f) x) x :=
  ((S.phi_contDiff.differentiableOn (by norm_num)).differentiableAt
    (S.isOpen.mem_nhds hx)).hasDerivAt

theorem phi'_contDiff : ContDiffOn ℝ 1 (deriv (lgPhi f)) I :=
  S.phi_contDiff.deriv_of_isOpen S.isOpen (by norm_num)

theorem phi'_hasDerivAt {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (deriv (lgPhi f)) (deriv (deriv (lgPhi f)) x) x :=
  ((S.phi'_contDiff.differentiableOn one_ne_zero).differentiableAt
    (S.isOpen.mem_nhds hx)).hasDerivAt

theorem phi''_cont : ContinuousOn (deriv (deriv (lgPhi f))) I :=
  S.phi'_contDiff.continuousOn_deriv_of_isOpen S.isOpen le_rfl

theorem phi_cont : ContinuousOn (lgPhi f) I := S.phi_contDiff.continuousOn

theorem f_hasDerivAt {x : ℝ} (hx : x ∈ I) : HasDerivAt f (deriv f x) x :=
  ((S.f_contDiff.differentiableOn (by norm_num)).differentiableAt
    (S.isOpen.mem_nhds hx)).hasDerivAt

theorem sqrt_hasDerivAt {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (fun y => Real.sqrt (f y)) (deriv f x / (2 * Real.sqrt (f x))) x :=
  (S.f_hasDerivAt hx).sqrt (S.f_pos x hx).ne'

theorem sqrt_cont : ContinuousOn (fun y => Real.sqrt (f y)) I :=
  fun _ hx => (S.sqrt_hasDerivAt hx).continuousAt.continuousWithinAt

theorem control_cont : ContinuousOn (lgControl f g) I := by
  refine (S.phi_cont.mul S.phi''_cont).sub (S.g_cont.div S.sqrt_cont fun x hx => ?_)
  exact (Real.sqrt_pos.mpr (S.f_pos x hx)).ne'

theorem phi_pos {x : ℝ} (hx : x ∈ I) : 0 < lgPhi f x := Real.rpow_pos_of_pos (S.f_pos x hx) _

/-- `(f^{−1/4})² f^{1/2} = 1`. -/
theorem phi_sq_mul_sqrt {x : ℝ} (hx : x ∈ I) : lgPhi f x ^ 2 * Real.sqrt (f x) = 1 := by
  have hf := S.f_pos x hx
  rw [lgPhi, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hf.le,
    ← Real.rpow_add hf]
  norm_num

/-- Differentiating `φ² f^{1/2} = 1`: `2 φ′ f^{1/2} + φ (f^{1/2})′ = 0`. -/
theorem phi_deriv_rel {x : ℝ} (hx : x ∈ I) :
    2 * deriv (lgPhi f) x * Real.sqrt (f x) +
      lgPhi f x * (deriv f x / (2 * Real.sqrt (f x))) = 0 := by
  have hD := ((S.phi_hasDerivAt hx).pow 2).mul (S.sqrt_hasDerivAt hx)
  have hconst : HasDerivAt (fun y => lgPhi f y ^ 2 * Real.sqrt (f y)) 0 x := by
    refine (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [S.isOpen.mem_nhds hx] with y hy using S.phi_sq_mul_sqrt hy
  have := hD.unique hconst
  have hφ := S.phi_pos hx
  simp only [Pi.pow_apply] at this
  norm_num at this
  have : lgPhi f x * (2 * deriv (lgPhi f) x * Real.sqrt (f x) +
      lgPhi f x * (deriv f x / (2 * Real.sqrt (f x)))) = 0 := by
    linear_combination this
  exact (mul_eq_zero.mp this).resolve_left hφ.ne'

/-! ### 2.7.21, 2.7.23: the solution `w₁` -/

/-- **DLMF 2.7.21, 2.7.23**: if `𝒱_{a₁,x}(F) < ∞`, there is a solution
`w₁(x) = f^{−1/4}(x) e^{ξ(x)} (1 + ε₁(x))` of 2.7.20 with
`|ε₁(x)|, ½ f^{−1/2}(x) |ε₁′(x)| ≤ exp(½ 𝒱_{a₁,x}(F)) − 1`. -/
theorem dlmf_2_7_21 (hV : ∀ x ∈ I, IntegrableOn (lgControl f g) (I ∩ Iic x)) :
    ∃ ε : ℝ → ℝ, IsLGSolution I f g (fun x => lgPhi f x * Real.exp (ξ x) * (1 + ε x)) ∧
      ∀ x ∈ I, HasDerivAt ε (deriv ε x) x ∧
        |ε x| ≤ Real.exp (volterraV I (lgControl f g) x / 2) - 1 ∧
        1 / 2 * f x ^ (-(1 / 2 : ℝ)) * |deriv ε x| ≤
          Real.exp (volterraV I (lgControl f g) x / 2) - 1 := by
  have H : VolterraLG I (lgControl f g) ξ (fun x => Real.sqrt (f x)) :=
    ⟨S.isOpen, S.ordConnected, S.nonempty, S.control_cont, hV, S.ξ_deriv,
      fun _ _ => Real.sqrt_nonneg _⟩
  obtain ⟨u, P, hu, hP, hb⟩ := H.exists_solution
  have hε : ∀ x ∈ I, HasDerivAt (fun y => u y - 1) (-(Real.sqrt (f x)) * P x) x :=
    fun x hx => (hu x hx).sub_const 1
  refine ⟨fun y => u y - 1, ?_, fun x hx => ⟨(hε x hx).deriv ▸ hε x hx, ?_, ?_⟩⟩
  · -- the solution property
    have hw : (fun x => lgPhi f x * Real.exp (ξ x) * (1 + (u x - 1))) =
        fun x => lgPhi f x * Real.exp (ξ x) * u x := by
      funext x; ring
    rw [hw]
    set w' : ℝ → ℝ := fun x => (deriv (lgPhi f) x * Real.exp (ξ x) +
      lgPhi f x * (Real.exp (ξ x) * Real.sqrt (f x))) * u x +
      lgPhi f x * Real.exp (ξ x) * (-(Real.sqrt (f x)) * P x) with hw'
    have hfg : ContinuousOn (fun x => f x + g x) I :=
      S.f_contDiff.continuousOn.add S.g_cont
    refine IsLGSolution.of_hasDerivAt S.isOpen hfg (w' := w') (fun x hx => ?_) (fun x hx => ?_)
    · have hE := (S.ξ_deriv x hx).exp
      exact ((S.phi_hasDerivAt hx).mul hE).mul (hu x hx)
    · have hE := (S.ξ_deriv x hx).exp
      have hs := S.sqrt_hasDerivAt hx
      have hD := ((((S.phi'_hasDerivAt hx).mul hE).add ((S.phi_hasDerivAt hx).mul
        (hE.mul hs))).mul (hu x hx)).add (((S.phi_hasDerivAt hx).mul hE).mul
        (hs.neg.mul (hP x hx)))
      refine hD.congr_deriv ?_
      have hf := S.f_pos x hx
      have hsq : Real.sqrt (f x) ^ 2 = f x := Real.sq_sqrt hf.le
      have hs0 : Real.sqrt (f x) ≠ 0 := (Real.sqrt_pos.mpr hf).ne'
      have hR1 := S.phi_sq_mul_sqrt hx
      have hR2 := S.phi_deriv_rel hx
      have hq : lgControl f g x * Real.sqrt (f x) =
          lgPhi f x * deriv (deriv (lgPhi f)) x * Real.sqrt (f x) - g x := by
        rw [lgControl]
        field_simp
      simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply]
      set E := Real.exp (ξ x)
      linear_combination E * (u x - P x) * hR2 + E * u x * lgPhi f x * hsq -
        E * u x * lgPhi f x * hq - E * u x * deriv (deriv (lgPhi f)) x * hR1
  · exact (hb x hx).1
  · rw [(hε x hx).deriv]
    have hf := S.f_pos x hx
    have hs : 0 < Real.sqrt (f x) := Real.sqrt_pos.mpr hf
    have hpow : f x ^ (-(1 / 2 : ℝ)) = (Real.sqrt (f x))⁻¹ := by
      rw [Real.rpow_neg hf.le, Real.sqrt_eq_rpow]
    rw [hpow, abs_mul, abs_neg, abs_of_pos hs]
    have := (hb x hx).2
    calc 1 / 2 * (Real.sqrt (f x))⁻¹ * (Real.sqrt (f x) * |P x|) = |P x| / 2 := by
          field_simp
      _ ≤ _ := by linarith

/-- **DLMF 2.7.26**: `w₁(x) ∼ f^{−1/4}(x) exp(∫ f^{1/2}(x) dx)` as `x → a₁+`, for any
`ε₁` with the bound 2.7.23. -/
theorem dlmf_2_7_26 (hV : ∀ x ∈ I, IntegrableOn (lgControl f g) (I ∩ Iic x)) {ε : ℝ → ℝ}
    (hε : ∀ x ∈ I, |ε x| ≤ Real.exp (volterraV I (lgControl f g) x / 2) - 1) :
    AsympEqDLMF (ioLowerEnd I) (fun x => lgPhi f x * Real.exp (ξ x) * (1 + ε x))
      (fun x => lgPhi f x * Real.exp (ξ x)) := by
  have H : VolterraLG I (lgControl f g) ξ (fun x => Real.sqrt (f x)) :=
    ⟨S.isOpen, S.ordConnected, S.nonempty, S.control_cont, hV, S.ξ_deriv,
      fun _ _ => Real.sqrt_nonneg _⟩
  have hbound : Tendsto (fun x => Real.exp (volterraV I (lgControl f g) x / 2) - 1)
      (ioLowerEnd I) (𝓝 0) := by
    have h1 : Tendsto (fun x => volterraV I (lgControl f g) x / 2) (ioLowerEnd I) (𝓝 0) := by
      simpa using H.V_tendsto.div_const 2
    have := ((Real.continuous_exp.tendsto 0).comp h1).sub_const 1
    simpa using this
  have hε0 : Tendsto ε (ioLowerEnd I) (𝓝 0) :=
    squeeze_zero_norm' (eventually_mem_ioLowerEnd.mono fun x hx => by
      rw [Real.norm_eq_abs]; exact hε x hx) hbound
  have := hε0.const_add 1
  rw [add_zero] at this
  refine this.congr' (eventually_mem_ioLowerEnd.mono fun x hx => ?_)
  have h1 : lgPhi f x ≠ 0 := (S.phi_pos hx).ne'
  have h2 : Real.exp (ξ x) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-! ### Reflection `x ↦ −x` and the solution `w₂` -/

/-- The reflected setup on `−I` with `f(−x)`, `g(−x)`, `−ξ(−x)`. -/
theorem reflect : LGSetup (Neg.neg ⁻¹' I) (fun x => f (-x)) (fun x => g (-x))
    (fun x => -ξ (-x)) where
  isOpen := S.isOpen.preimage continuous_neg
  ordConnected := ⟨fun x hx y hy z hz => S.ordConnected.out hy hx ⟨by
    simp only [mem_Icc] at hz; linarith, by simp only [mem_Icc] at hz; linarith⟩⟩
  nonempty := by
    obtain ⟨x, hx⟩ := S.nonempty
    exact ⟨-x, by simpa using hx⟩
  f_pos x hx := S.f_pos (-x) hx
  f_contDiff := S.f_contDiff.comp contDiff_neg.contDiffOn fun x hx => hx
  g_cont := S.g_cont.comp continuous_neg.continuousOn fun x hx => hx
  ξ_deriv x hx := by
    have h1 : HasDerivAt (fun y => ξ (-y)) (Real.sqrt (f (-x)) * (-1)) x :=
      (S.ξ_deriv (-x) hx).comp x (hasDerivAt_neg x)
    convert h1.neg using 1
    ring

/-- **DLMF 2.7.22, 2.7.23**: if `𝒱_{a₂,x}(F) < ∞`, there is a solution
`w₂(x) = f^{−1/4}(x) e^{−ξ(x)} (1 + ε₂(x))` of 2.7.20 with
`|ε₂(x)|, ½ f^{−1/2}(x) |ε₂′(x)| ≤ exp(½ 𝒱_{a₂,x}(F)) − 1`. -/
theorem dlmf_2_7_22 (hV : ∀ x ∈ I, IntegrableOn (lgControl f g) (I ∩ Ici x)) :
    ∃ ε : ℝ → ℝ, IsLGSolution I f g (fun x => lgPhi f x * Real.exp (-ξ x) * (1 + ε x)) ∧
      ∀ x ∈ I, HasDerivAt ε (deriv ε x) x ∧
        |ε x| ≤ Real.exp (lgVarUpper I f g x / 2) - 1 ∧
        1 / 2 * f x ^ (-(1 / 2 : ℝ)) * |deriv ε x| ≤
          Real.exp (lgVarUpper I f g x / 2) - 1 := by
  have S' := S.reflect
  have hV' : ∀ x ∈ Neg.neg ⁻¹' I, IntegrableOn (lgControl (fun x => f (-x)) (fun x => g (-x)))
      (Neg.neg ⁻¹' I ∩ Iic x) := by
    intro x hx
    have hset : Neg.neg ⁻¹' I ∩ Iic x = Neg.neg ⁻¹' (I ∩ Ici (-x)) := by
      ext v; simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ici]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    rw [hset, show lgControl (fun x => f (-x)) (fun x => g (-x)) = fun x => lgControl f g (-x)
      from funext (lgControl_reflect f g)]
    exact (integrableOn_comp_neg_iff _ (lgControl f g)).mpr (hV (-x) hx)
  obtain ⟨ε, ⟨hw2, hwode⟩, hε⟩ := S'.dlmf_2_7_21 hV'
  refine ⟨fun x => ε (-x), ⟨?_, fun x hx => ?_⟩, fun x hx => ?_⟩
  · have := hw2.comp contDiff_neg.contDiffOn (fun x hx => by simpa using hx)
    refine this.congr fun x _ => ?_
    simp [lgPhi]
  · have e : (fun x => lgPhi f x * Real.exp (-ξ x) * (1 + ε (-x))) =
        fun y => lgPhi (fun x => f (-x)) (-y) * Real.exp (-ξ (-(-y))) * (1 + ε (-y)) := by
      funext x; simp [lgPhi]
    have key := deriv_deriv_comp_neg
      (fun y => lgPhi (fun x => f (-x)) y * Real.exp (-ξ (-y)) * (1 + ε y)) x
    rw [e, key, hwode (-x) (by simpa using hx)]
    simp [lgPhi]
  · obtain ⟨hd, h1, h2⟩ := hε (-x) (by simpa using hx)
    have hdx : HasDerivAt (fun y => ε (-y)) (-deriv ε (-x)) x := by
      have := hd.comp x (hasDerivAt_neg x)
      convert this using 1 <;> first | rfl | ring
    refine ⟨hdx.deriv ▸ hdx, ?_, ?_⟩
    · rw [lgVarUpper_eq]; exact h1
    · rw [hdx.deriv, abs_neg, lgVarUpper_eq]
      simpa using h2

theorem tendsto_neg_ioUpperEnd :
    Tendsto (fun x : ℝ => -x) (ioUpperEnd I) (ioLowerEnd (Neg.neg ⁻¹' I)) := by
  intro s hs
  rw [Filter.mem_map]
  have hne := S.reflect.nonempty
  have hs' : ∀ᶠ y in ioLowerEnd (Neg.neg ⁻¹' I), y ∈ s := hs
  rw [eventually_ioLowerEnd hne] at hs'
  obtain ⟨a, ha, h⟩ := hs'
  show ∀ᶠ x in ioUpperEnd I, -x ∈ s
  rw [eventually_ioUpperEnd S.nonempty]
  exact ⟨-a, ha, fun x hx hax => h (-x) (by simpa using hx) (by linarith)⟩

/-- **DLMF 2.7.27**: `w₂(x) ∼ f^{−1/4}(x) exp(−∫ f^{1/2}(x) dx)` as `x → a₂−`, for any `ε₂`
with the bound 2.7.23. -/
theorem dlmf_2_7_27 (hV : ∀ x ∈ I, IntegrableOn (lgControl f g) (I ∩ Ici x)) {ε : ℝ → ℝ}
    (hε : ∀ x ∈ I, |ε x| ≤ Real.exp (lgVarUpper I f g x / 2) - 1) :
    AsympEqDLMF (ioUpperEnd I) (fun x => lgPhi f x * Real.exp (-ξ x) * (1 + ε x))
      (fun x => lgPhi f x * Real.exp (-ξ x)) := by
  have S' := S.reflect
  have hV' : ∀ x ∈ Neg.neg ⁻¹' I, IntegrableOn (lgControl (fun x => f (-x)) (fun x => g (-x)))
      (Neg.neg ⁻¹' I ∩ Iic x) := by
    intro x hx
    have hset : Neg.neg ⁻¹' I ∩ Iic x = Neg.neg ⁻¹' (I ∩ Ici (-x)) := by
      ext v; simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ici]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    rw [hset, show lgControl (fun x => f (-x)) (fun x => g (-x)) = fun x => lgControl f g (-x)
      from funext (lgControl_reflect f g)]
    exact (integrableOn_comp_neg_iff _ (lgControl f g)).mpr (hV (-x) hx)
  have H : VolterraLG (Neg.neg ⁻¹' I) (lgControl (fun x => f (-x)) (fun x => g (-x)))
      (fun x => -ξ (-x)) (fun x => Real.sqrt (f (-x))) :=
    ⟨S'.isOpen, S'.ordConnected, S'.nonempty, S'.control_cont, hV', S'.ξ_deriv,
      fun _ _ => Real.sqrt_nonneg _⟩
  have hV0 : Tendsto (lgVarUpper I f g) (ioUpperEnd I) (𝓝 0) := by
    have := H.V_tendsto.comp S.tendsto_neg_ioUpperEnd
    refine this.congr fun x => ?_
    exact (lgVarUpper_eq I f g x).symm
  have hbound : Tendsto (fun x => Real.exp (lgVarUpper I f g x / 2) - 1) (ioUpperEnd I) (𝓝 0) := by
    have h1 : Tendsto (fun x => lgVarUpper I f g x / 2) (ioUpperEnd I) (𝓝 0) := by
      simpa using hV0.div_const 2
    have := ((Real.continuous_exp.tendsto 0).comp h1).sub_const 1
    simpa using this
  have hε0 : Tendsto ε (ioUpperEnd I) (𝓝 0) :=
    squeeze_zero_norm' (eventually_mem_ioUpperEnd.mono fun x hx => by
      rw [Real.norm_eq_abs]; exact hε x hx) hbound
  have := hε0.const_add 1
  rw [add_zero] at this
  refine this.congr' (eventually_mem_ioUpperEnd.mono fun x hx => ?_)
  have h1 : lgPhi f x ≠ 0 := (S.phi_pos hx).ne'
  have h2 : Real.exp (-ξ x) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-! ### 2.7.25: the variational operator -/

/-- **DLMF 2.7.25** and §2.3(i): for an error-control function `F` (2.7.24: `F′ = lgControl`) and
`a ≤ x` in `I`, `𝒱_{a₁,x}(F) − 𝒱_{a₁,a}(F)` is the total variation of `F` on `[a, x]`. -/
theorem dlmf_2_7_25 (hV : ∀ x ∈ I, IntegrableOn (lgControl f g) (I ∩ Iic x)) {F : ℝ → ℝ}
    (hF : ∀ x ∈ I, HasDerivAt F (lgControl f g x) x) {a x : ℝ} (ha : a ∈ I) (hx : x ∈ I)
    (hax : a ≤ x) :
    volterraV I (lgControl f g) x - volterraV I (lgControl f g) a =
      (eVariationOn F (Icc a x)).toReal := by
  have hsub : Icc a x ⊆ I := S.ordConnected.out ha hx
  have hderiv : EqOn (deriv F) (lgControl f g) (Icc a x) := fun y hy => (hF y (hsub hy)).deriv
  rw [← variationIntegral_eq_toReal hax (fun y hy => (hF y (hsub hy)).differentiableAt)
    ((S.control_cont.mono hsub).congr hderiv), variationIntegral,
    intervalIntegral.integral_of_le hax]
  have hsplit : I ∩ Iic x = (I ∩ Iic a) ∪ Ioc a x := by
    ext v
    simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
    constructor
    · rintro ⟨hv, hvx⟩
      by_cases h : v ≤ a
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨not_le.mp h, hvx⟩
    · rintro (⟨hv, h⟩ | ⟨h1, h2⟩)
      · exact ⟨hv, h.trans hax⟩
      · exact ⟨hsub ⟨h1.le, h2⟩, h2⟩
  rw [volterraV, volterraV, hsplit, setIntegral_union
    (disjoint_left.mpr fun v hv hv' => not_lt.mpr hv.2 hv'.1) measurableSet_Ioc
    (hV a ha).abs (IntegrableOn.mono_set (hV x hx).abs fun v hv => ⟨hsub ⟨hv.1.le, hv.2⟩, hv.2⟩)]
  have : ∀ v ∈ Ioc a x, ‖deriv F v‖ = |lgControl f g v| := fun v hv => by
    rw [hderiv ⟨hv.1.le, hv.2⟩, Real.norm_eq_abs]
  rw [setIntegral_congr_fun measurableSet_Ioc this]
  ring

end LGSetup

/-! ### Recessive and dominant solutions; uniqueness -/

/-- **DLMF 2.7.30**: if `w₁ ∼ f^{−1/4} e^{ξ}` and `w₄ ∼ f^{−1/4} e^{−ξ}` along `l` and
`ξ = ∫ f^{1/2} → −∞`, then `w₁/w₄ → 0` (`w₁` recessive, `w₄` dominant). -/
theorem dlmf_2_7_30 {l : Filter ℝ} {w₁ w₄ φ ξ : ℝ → ℝ}
    (h₁ : AsympEqDLMF l w₁ fun x => φ x * Real.exp (ξ x))
    (h₄ : AsympEqDLMF l w₄ fun x => φ x * Real.exp (-ξ x)) (hξ : Tendsto ξ l atBot)
    (hφ : ∀ᶠ x in l, φ x ≠ 0) : Tendsto (fun x => w₁ x / w₄ x) l (𝓝 0) := by
  have he : Tendsto (fun x => Real.exp (2 * ξ x)) l (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hξ.const_mul_atBot two_pos)
  have := (h₁.div h₄ (by norm_num)).mul he
  rw [div_one, one_mul] at this
  refine this.congr' (hφ.mono fun x hx => ?_)
  have hE : Real.exp (ξ x) ≠ 0 := (Real.exp_pos _).ne'
  have hE' : Real.exp (-ξ x) ≠ 0 := (Real.exp_pos _).ne'
  have h2 : Real.exp (2 * ξ x) = Real.exp (ξ x) / Real.exp (-ξ x) := by
    rw [← Real.exp_sub]; ring_nf
  rw [h2]
  simp only [Pi.div_apply]
  by_cases hw : w₄ x = 0
  · simp [hw]
  · field_simp

theorem ioLowerEnd_Ioo_le {a b : ℝ} (hab : a < b) : ioLowerEnd (Ioo a b) ≤ 𝓝 a := by
  intro s hs
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  show ∀ᶠ x in ioLowerEnd (Ioo a b), x ∈ s
  rw [eventually_ioLowerEnd (nonempty_Ioo.mpr hab)]
  refine ⟨min (a + δ / 2) ((a + b) / 2), ⟨lt_min (by linarith) (by linarith),
    (min_le_right _ _).trans_lt (by linarith)⟩, fun x hx hxa => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  have := hxa.trans (min_le_left _ _)
  constructor <;> linarith [hx.1]

/-- DLMF says the solutions with 2.7.26 (and 2.7.27) "are unique"; under the hypotheses stated
there (`𝒱_{a₁,a₂}(F) < ∞`) this fails when `∫ f^{1/2}` is bounded at the endpoint. On `(0, 1)`
with `f = 1`, `g = 0` (so `F′ = 0`), both `eˣ` (the solution `w₁` of 2.7.21, `ε₁ = 0`) and `cosh x`
solve `w″ = w` and are `∼ eˣ` as `x → 0+`. Uniqueness needs `|∫ f^{1/2}| → ∞` at the endpoint, the
extra hypothesis DLMF imposes only afterwards. -/
theorem dlmf_2_7_26_not_unique :
    lgControl (fun _ => 1) (fun _ => 0) = 0 ∧
    IsLGSolution (Ioo 0 1) (fun _ => 1) (fun _ => 0) Real.exp ∧
    IsLGSolution (Ioo 0 1) (fun _ => 1) (fun _ => 0) Real.cosh ∧
    AsympEqDLMF (ioLowerEnd (Ioo 0 1)) Real.exp
      (fun x => lgPhi (fun _ => 1) x * Real.exp x) ∧
    AsympEqDLMF (ioLowerEnd (Ioo 0 1)) Real.cosh
      (fun x => lgPhi (fun _ => 1) x * Real.exp x) ∧
    Real.exp (1 / 2) ≠ Real.cosh (1 / 2) := by
  have hphi : lgPhi (fun _ : ℝ => (1 : ℝ)) = fun _ => 1 := by
    funext x; simp [lgPhi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    simp [lgControl, hphi]
  · refine ⟨Real.contDiff_exp.contDiffOn, fun x _ => ?_⟩
    simp [Real.deriv_exp]
  · refine ⟨Real.contDiff_cosh.contDiffOn, fun x _ => ?_⟩
    simp [Real.deriv_cosh, Real.deriv_sinh]
  · rw [hphi]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun x => ?_)
    simp [(Real.exp_pos x).ne']
  · rw [hphi]
    have hc : Continuous fun x => Real.cosh x / (1 * Real.exp x) :=
      Real.continuous_cosh.div (continuous_const.mul Real.continuous_exp)
        fun x => by simp [(Real.exp_pos x).ne']
    have := (hc.tendsto 0).mono_left (ioLowerEnd_Ioo_le zero_lt_one)
    simpa [AsympEqDLMF] using this
  · intro h
    have : Real.cosh (1 / 2) - Real.exp (1 / 2) = -Real.sinh (1 / 2) := by
      rw [Real.cosh_eq, Real.sinh_eq]; ring
    rw [h, sub_self] at this
    have hs : 0 < Real.sinh (1 / 2) := Real.sinh_pos_iff.mpr (by norm_num)
    linarith

end Azurite.DLMF
