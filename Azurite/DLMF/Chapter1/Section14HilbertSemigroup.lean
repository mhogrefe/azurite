/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14HilbertLebesgue

/-!
# DLMF 1.14.45: semigroup identities for the Poisson kernels

The Poisson kernel `p_b` has Fourier transform `e^{−b|ξ|}` (`integral_pK_mul_cexp`, by Fourier
inversion). This gives `p_c ∗ p_a = p_{a+c}` and `p_c ∗ q_a = q_{a+c}` (`integral_pK_mul_pK`,
`integral_pK_mul_qK`). Hence `P_ε(Q_b g) = Q_{ε+b} g = Q_ε(P_b g)`
(`poissonInt_conjPoissonInt`, `conjPoissonInt_poissonInt`) and the antisymmetry
`∫ (Q_b g)(P_c g′) = −∫ (P_b g)(Q_c g′)` (`integral_conjPoisson_antisymm`).
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace Azurite.DLMF

/-- The Poisson kernel `p_b(s) = b/(π(s² + b²))`. -/
noncomputable def pK (b s : ℝ) : ℝ := b / (π * (s ^ 2 + b ^ 2))

/-- The conjugate Poisson kernel `q_b(s) = s/(π(s² + b²))`. -/
noncomputable def qK (b s : ℝ) : ℝ := s / (π * (s ^ 2 + b ^ 2))

theorem pK_neg (b s : ℝ) : pK b (-s) = pK b s := by simp [pK]

theorem qK_neg (b s : ℝ) : qK b (-s) = -qK b s := by simp [qK, neg_div]

theorem pK_nonneg {b : ℝ} (hb : 0 < b) (s : ℝ) : 0 ≤ pK b s := by
  unfold pK; have := Real.pi_pos; positivity

theorem abs_qK_le {b : ℝ} (hb : 0 < b) (s : ℝ) : |qK b s| ≤ 1 / (π * b) := by
  have hπ := Real.pi_pos
  have := abs_div_sq_add_sq_le (s := s) hb
  rw [qK, abs_div, abs_of_pos (by positivity : 0 < π * (s ^ 2 + b ^ 2))]
  rw [abs_div, abs_of_pos (by positivity : 0 < s ^ 2 + b ^ 2)] at this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hb] at this
  nlinarith

theorem continuous_pK {b : ℝ} (hb : 0 < b) : Continuous (pK b) := by
  unfold pK
  exact continuous_const.div (by fun_prop) fun s => by have := Real.pi_pos; positivity

theorem continuous_qK {b : ℝ} (hb : 0 < b) : Continuous (qK b) := by
  unfold qK
  exact continuous_id.div (by fun_prop) fun s => by have := Real.pi_pos; positivity

theorem pK_eq_expKernel {b : ℝ} (hb : 0 < b) (s : ℝ) :
    ((pK b s : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, expKernel b s ξ := by
  rw [integral_expKernel hb, pK]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd : ((s : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    have : 0 < s ^ 2 + b ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hd' : ((b : ℂ) ^ 2 + (s : ℂ) ^ 2) ≠ 0 := by rwa [add_comm]
  push_cast
  field_simp
  ring

theorem qK_eq_expKernel {b : ℝ} (hb : 0 < b) (s : ℝ) :
    ((qK b s : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, -I * (Real.sign ξ : ℂ) * expKernel b s ξ := by
  rw [integral_sign_expKernel hb, qK]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd : ((s : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    have : 0 < s ^ 2 + b ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hd' : ((b : ℂ) ^ 2 + (s : ℂ) ^ 2) ≠ 0 := by rwa [add_comm]
  push_cast
  field_simp
  ring

theorem integrable_pK {b : ℝ} (hb : 0 < b) : Integrable (pK b) := by
  have := (integrable_poissonKernel hb).div_const π
  refine this.congr (ae_of_all _ fun s => ?_)
  simp only [pK]
  field_simp
  ring

theorem integral_pK {b : ℝ} (hb : 0 < b) : ∫ s, pK b s = 1 := by
  have : (fun s => pK b s) = fun s => b / (b ^ 2 + s ^ 2) / π := funext fun s => by
    simp only [pK]; field_simp; ring
  rw [this, integral_div, integral_poissonKernel hb, div_self Real.pi_ne_zero]

/-- The Fourier transform of the Poisson kernel: `∫ p_b(y) e^{iξy} dy = e^{−b|ξ|}`, by Fourier
inversion applied to `e^{−b|ξ|}`. -/
theorem integral_pK_mul_cexp {b : ℝ} (hb : 0 < b) (ξ : ℝ) :
    ∫ y, (pK b y : ℂ) * cexp (I * ξ * y) = cexp (-((b : ℂ) * |ξ|)) := by
  set E : ℝ → ℂ := fun t => cexp (-((b : ℂ) * |t|)) with hE
  have hEi : Integrable E := by
    refine (integrable_exp_neg_abs hb).ofReal.congr (ae_of_all _ fun t => ?_)
    simp [hE, ofReal_exp]
  have hEc : Continuous E := by simp only [hE]; fun_prop
  have hFE : ∀ x, dlmfFourier E x = ((√(2 * π) : ℝ) : ℂ)⁻¹ * ∫ ξ, expKernel b x ξ := fun x => by
    rw [dlmfFourier]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hE, expKernel]
    rw [← Complex.exp_add]; congr 1; ring
  have hFEi : Integrable (dlmfFourier E) := by
    have heq : dlmfFourier E = fun x =>
        ((√(2 * π) : ℝ) : ℂ)⁻¹ * ((2 * π : ℝ) : ℂ) * ((pK b x : ℝ) : ℂ) := funext fun x => by
      rw [hFE x, pK_eq_expKernel hb x]
      have : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 2 * π).ne'
      field_simp
    rw [heq]
    exact (integrable_pK hb).ofReal.const_mul _
  have hinv := dlmf_inversion hEi hFEi (hEc.continuousAt (x := -ξ))
  set c : ℂ := ((√(2 * π) : ℝ) : ℂ)
  have hcc : c⁻¹ * c⁻¹ = ((2 * π : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  have : E (-ξ) = cexp (-((b : ℂ) * |ξ|)) := by simp [hE, abs_neg]
  rw [← this, hinv, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [hFE x, pK_eq_expKernel hb x, ← mul_assoc, ← mul_assoc, hcc]
  congr 2
  push_cast
  ring

/-- Convolution of `p_c` with a kernel `(1/2π) ∫ φ(ξ) e^{−a|ξ| + iξs} dξ` adds `c` to `a`. -/
theorem integral_pK_mul_expKernel {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {φ : ℝ → ℂ}
    (hφm : Measurable φ) (hφb : ∀ ξ, ‖φ ξ‖ ≤ 1) (u v : ℝ) :
    ∫ x, (pK c (v - x) : ℂ) * ∫ ξ, φ ξ * expKernel a (u - x) ξ =
      ∫ ξ, φ ξ * expKernel (a + c) (u - v) ξ := by
  set H : ℝ → ℝ → ℂ := fun x ξ => (pK c (v - x) : ℂ) * (φ ξ * expKernel a (u - x) ξ) with hH
  have hHi : Integrable (Function.uncurry H) (volume.prod volume) := by
    refine (((integrable_pK hc).comp_sub_left v).mul_prod (integrable_exp_neg_abs ha)).mono'
      ?_ (ae_of_all _ fun q => ?_)
    · exact ((Complex.continuous_ofReal.comp ((continuous_pK hc).comp
        (continuous_const.sub continuous_fst))).aestronglyMeasurable).mul
        ((hφm.aestronglyMeasurable.comp_snd).mul (((continuous_expKernel a).comp
          (by fun_prop : Continuous fun q : ℝ × ℝ => (u - q.1, q.2))).aestronglyMeasurable))
    · change ‖(pK c (v - q.1) : ℂ) * (φ q.2 * expKernel a (u - q.1) q.2)‖ ≤
        pK c (v - q.1) * Real.exp (-(a * |q.2|))
      rw [norm_mul, norm_mul, norm_expKernel, Complex.norm_real,
        Real.norm_of_nonneg (pK_nonneg hc _)]
      exact mul_le_mul_of_nonneg_left (by
        simpa using mul_le_mul_of_nonneg_right (hφb q.2) (Real.exp_pos _).le)
        (pK_nonneg hc _)
  have hswap := integral_integral_swap hHi
  calc ∫ x, (pK c (v - x) : ℂ) * ∫ ξ, φ ξ * expKernel a (u - x) ξ = ∫ x, ∫ ξ, H x ξ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hH]; rw [integral_const_mul]
    _ = ∫ ξ, ∫ x, H x ξ := hswap
    _ = ∫ ξ, φ ξ * expKernel (a + c) (u - v) ξ := by
        refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
        have hfac : ∀ x, H x ξ = φ ξ * cexp (-((a : ℂ) * |ξ|) + I * ξ * u) *
            ((pK c (v - x) : ℂ) * cexp (I * ξ * (v - x)) *
              cexp (I * ξ * (-v))) := fun x => by
          simp only [hH, expKernel]
          rw [show φ ξ * cexp (-((a : ℂ) * |ξ|) + I * ξ * u) *
            ((pK c (v - x) : ℂ) * cexp (I * ξ * (v - x)) * cexp (I * ξ * (-v))) =
            (pK c (v - x) : ℂ) * (φ ξ * (cexp (-((a : ℂ) * |ξ|) + I * ξ * u) *
            cexp (I * ξ * (v - x)) * cexp (I * ξ * (-v)))) by ring,
            ← Complex.exp_add, ← Complex.exp_add]
          congr 3
          push_cast; ring
        simp_rw [hfac]
        rw [integral_const_mul, integral_mul_const]
        have hsub := integral_sub_left_eq_self
          (fun y : ℝ => (pK c y : ℂ) * cexp (I * ξ * y)) (volume : Measure ℝ) v
        rw [show (fun x : ℝ => (pK c (v - x) : ℂ) * cexp (I * ξ * (v - x))) =
          fun x => (pK c (v - x) : ℂ) * cexp (I * ξ * ((v - x : ℝ) : ℂ)) from
          funext fun x => by push_cast; ring_nf]
        rw [hsub, integral_pK_mul_cexp hc, expKernel]
        rw [mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
        congr 2
        push_cast; ring

/-- `∫ p_c(v − x) p_a(u − x) dx = p_{a+c}(u − v)`. -/
theorem integral_pK_mul_pK {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (u v : ℝ) :
    ∫ x, pK c (v - x) * pK a (u - x) = pK (a + c) (u - v) := by
  have h := integral_pK_mul_expKernel ha hc (φ := fun _ => 1) measurable_const
    (fun _ => by simp) u v
  simp only [one_mul] at h
  apply Complex.ofReal_injective
  rw [pK_eq_expKernel (by linarith) (u - v), ← h, ← integral_complex_ofReal,
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [ofReal_mul, pK_eq_expKernel ha]
  push_cast
  ring

/-- `∫ p_c(v − x) q_a(u − x) dx = q_{a+c}(u − v)`. -/
theorem integral_pK_mul_qK {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (u v : ℝ) :
    ∫ x, pK c (v - x) * qK a (u - x) = qK (a + c) (u - v) := by
  have h := integral_pK_mul_expKernel ha hc (φ := fun ξ => -I * (Real.sign ξ : ℂ))
    (measurable_const.mul (Complex.measurable_ofReal.comp measurable_realSign))
    norm_neg_I_mul_sign_le u v
  apply Complex.ofReal_injective
  rw [qK_eq_expKernel (by linarith) (u - v), ← h, ← integral_complex_ofReal,
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [ofReal_mul, qK_eq_expKernel ha]
  push_cast
  ring

/-! ### Semigroup identities for the Poisson integrals -/

theorem poissonInt_eq_pK (b : ℝ) (g : ℝ → ℂ) (x : ℝ) :
    poissonInt b g x = ∫ t, (pK b (t - x) : ℂ) * g t := by
  rw [poissonInt, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [pK]; push_cast; simp only [div_eq_mul_inv, mul_inv]; ring

theorem conjPoissonInt_eq_qK (b : ℝ) (g : ℝ → ℂ) (x : ℝ) :
    conjPoissonInt b g x = ∫ t, (qK b (t - x) : ℂ) * g t := by
  rw [conjPoissonInt, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [qK]; push_cast; simp only [div_eq_mul_inv, mul_inv]; ring

/-- `(s, t) ↦ G(s) p_b(s − t)` is integrable for integrable `G ≥ 0`. -/
theorem integrable_mul_pK_sub {b : ℝ} (hb : 0 < b) {G : ℝ → ℝ} (hG : Integrable G)
    (hG0 : ∀ s, 0 ≤ G s) :
    Integrable (fun q : ℝ × ℝ => G q.1 * pK b (q.1 - q.2)) (volume.prod volume) := by
  have hm : AEStronglyMeasurable (fun q : ℝ × ℝ => G q.1 * pK b (q.1 - q.2))
      (volume.prod volume) :=
    hG.aestronglyMeasurable.comp_fst.mul
      ((continuous_pK hb).comp (by fun_prop : Continuous fun q : ℝ × ℝ => q.1 - q.2)
        ).aestronglyMeasurable
  refine (integrable_prod_iff hm).mpr
    ⟨ae_of_all _ fun s => ((integrable_pK hb).comp_sub_left s).const_mul (G s), ?_⟩
  refine hG.congr (ae_of_all _ fun s => ?_)
  simp only
  have : ∀ t, ‖G s * pK b (s - t)‖ = G s * pK b (s - t) := fun t =>
    Real.norm_of_nonneg (mul_nonneg (hG0 s) (pK_nonneg hb _))
  simp_rw [this]
  rw [integral_const_mul, integral_sub_left_eq_self (pK b) volume s, integral_pK hb, mul_one]

theorem norm_conjPoissonInt_le {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) :
    ‖conjPoissonInt b g x‖ ≤ 1 / (π * b) * ∫ t, ‖g t‖ := by
  rw [conjPoissonInt_eq_qK, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg.norm.const_mul _) (ae_of_all _ fun t => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_qK_le hb _) (norm_nonneg _)

theorem integrable_poissonInt {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (poissonInt b g) := by
  have hprod : Integrable (fun q : ℝ × ℝ => (pK b (q.1 - q.2) : ℂ) * g q.1)
      (volume.prod volume) := by
    refine (integrable_mul_pK_sub hb hg.norm fun _ => norm_nonneg _).mono'
      ((Complex.continuous_ofReal.comp ((continuous_pK hb).comp (by fun_prop :
        Continuous fun q : ℝ × ℝ => q.1 - q.2))).aestronglyMeasurable.mul
        hg.aestronglyMeasurable.comp_fst) (ae_of_all _ fun q => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pK_nonneg hb _), mul_comm]
  have := hprod.integral_prod_right
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [poissonInt_eq_pK]

theorem continuous_conjPoissonInt {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Integrable g) :
    Continuous (conjPoissonInt b g) := by
  have : conjPoissonInt b g = fun x => ∫ t, (qK b (t - x) : ℂ) * g t :=
    funext (conjPoissonInt_eq_qK b g)
  rw [this]
  refine continuous_of_dominated (bound := fun t => 1 / (π * b) * ‖g t‖)
    (fun x => ((Complex.continuous_ofReal.comp ((continuous_qK hb).comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable).mul hg.aestronglyMeasurable)
    (fun x => ae_of_all _ fun t => ?_) (hg.norm.const_mul _)
    (ae_of_all _ fun t => (Complex.continuous_ofReal.comp ((continuous_qK hb).comp
      (continuous_const.sub continuous_id))).mul continuous_const)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_qK_le hb _) (norm_nonneg _)

theorem integral_ofReal_mul_ofReal (f₁ f₂ : ℝ → ℝ) :
    ∫ t, (f₁ t : ℂ) * (f₂ t : ℂ) = ((∫ t, f₁ t * f₂ t : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]; push_cast; rfl

/-- **Semigroup**: `P_ε(Q_b g) = Q_{ε+b} g`. -/
theorem poissonInt_conjPoissonInt {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (x : ℝ) :
    poissonInt ε (conjPoissonInt b g) x = conjPoissonInt (ε + b) g x := by
  set H : ℝ → ℝ → ℂ := fun t s => (pK ε (t - x) : ℂ) * ((qK b (s - t) : ℂ) * g s) with hH
  have hHi : Integrable (Function.uncurry H) (volume.prod volume) := by
    refine ((((integrable_pK hε).comp_sub_right x)).mul_prod (hg.norm.const_mul (1 / (π * b)))
      ).mono' ?_ (ae_of_all _ fun q => ?_)
    · exact ((Complex.continuous_ofReal.comp ((continuous_pK hε).comp
        (continuous_fst.sub continuous_const))).aestronglyMeasurable).mul
        (((Complex.continuous_ofReal.comp ((continuous_qK hb).comp (continuous_snd.sub
          continuous_fst))).aestronglyMeasurable).mul hg.aestronglyMeasurable.comp_snd)
    · change ‖(pK ε (q.1 - x) : ℂ) * ((qK b (q.2 - q.1) : ℂ) * g q.2)‖ ≤
        pK ε (q.1 - x) * (1 / (π * b) * ‖g q.2‖)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (pK_nonneg hε _), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (abs_qK_le hb _)
        (norm_nonneg _)) (pK_nonneg hε _)
  rw [poissonInt_eq_pK, conjPoissonInt_eq_qK]
  calc ∫ t, (pK ε (t - x) : ℂ) * conjPoissonInt b g t = ∫ t, ∫ s, H t s := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only [hH]; rw [conjPoissonInt_eq_qK, integral_const_mul]
    _ = ∫ s, ∫ t, H t s := integral_integral_swap hHi
    _ = ∫ s, (qK (ε + b) (s - x) : ℂ) * g s := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        simp only [hH]
        have : ∀ t, (pK ε (t - x) : ℂ) * ((qK b (s - t) : ℂ) * g s) =
            ((pK ε (x - t) : ℂ) * (qK b (s - t) : ℂ)) * g s := fun t => by
          rw [show t - x = -(x - t) by ring, pK_neg]; ring
        simp_rw [this]
        rw [integral_mul_const, integral_ofReal_mul_ofReal, integral_pK_mul_qK hb hε, add_comm]

/-- **Semigroup**: `Q_ε(P_b g) = Q_{ε+b} g`. -/
theorem conjPoissonInt_poissonInt {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (x : ℝ) :
    conjPoissonInt ε (poissonInt b g) x = conjPoissonInt (ε + b) g x := by
  set H : ℝ → ℝ → ℂ := fun t s => (qK ε (t - x) : ℂ) * ((pK b (s - t) : ℂ) * g s) with hH
  have hHi : Integrable (Function.uncurry H) (volume.prod volume) := by
    have h0 := (integrable_mul_pK_sub hb hg.norm fun _ => norm_nonneg _).swap
    refine (h0.const_mul (1 / (π * ε))).mono' ?_ (ae_of_all _ fun q => ?_)
    · exact ((Complex.continuous_ofReal.comp ((continuous_qK hε).comp
        (continuous_fst.sub continuous_const))).aestronglyMeasurable).mul
        (((Complex.continuous_ofReal.comp ((continuous_pK hb).comp (continuous_snd.sub
          continuous_fst))).aestronglyMeasurable).mul hg.aestronglyMeasurable.comp_snd)
    · change ‖(qK ε (q.1 - x) : ℂ) * ((pK b (q.2 - q.1) : ℂ) * g q.2)‖ ≤
        1 / (π * ε) * (‖g (Prod.swap q).1‖ * pK b ((Prod.swap q).1 - (Prod.swap q).2))
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (pK_nonneg hb _), Real.norm_eq_abs]
      have := abs_qK_le hε (q.1 - x)
      have h1 := pK_nonneg hb (q.2 - q.1)
      have h2 := norm_nonneg (g q.2)
      calc |qK ε (q.1 - x)| * (pK b (q.2 - q.1) * ‖g q.2‖) ≤
          1 / (π * ε) * (pK b (q.2 - q.1) * ‖g q.2‖) := by gcongr
        _ = 1 / (π * ε) * (‖g q.2‖ * pK b (q.2 - q.1)) := by ring
  rw [conjPoissonInt_eq_qK, conjPoissonInt_eq_qK]
  calc ∫ t, (qK ε (t - x) : ℂ) * poissonInt b g t = ∫ t, ∫ s, H t s := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only [hH]; rw [poissonInt_eq_pK, integral_const_mul]
    _ = ∫ s, ∫ t, H t s := integral_integral_swap hHi
    _ = ∫ s, (qK (ε + b) (s - x) : ℂ) * g s := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        simp only [hH]
        have : ∀ t, (qK ε (t - x) : ℂ) * ((pK b (s - t) : ℂ) * g s) =
            -(((pK b (s - t) : ℂ) * (qK ε (x - t) : ℂ)) * g s) := fun t => by
          rw [show t - x = -(x - t) by ring, qK_neg]; push_cast; ring
        simp_rw [this]
        rw [integral_neg, integral_mul_const, integral_ofReal_mul_ofReal,
          integral_pK_mul_qK hε hb, show x - s = -(s - x) by ring, qK_neg]
        push_cast; ring

/-- `∫ (Q_b g)(P_c g′) = ∫ g′ · Q_{c+b} g`. -/
theorem integral_conjPoissonInt_mul_poissonInt {b c : ℝ} (hb : 0 < b) (hc : 0 < c) {g g' : ℝ → ℂ}
    (hg : Integrable g) (hg' : Integrable g') :
    ∫ x, conjPoissonInt b g x * poissonInt c g' x = ∫ s, g' s * conjPoissonInt (c + b) g s := by
  set M := 1 / (π * b) * ∫ t, ‖g t‖
  set H : ℝ → ℝ → ℂ := fun x s => conjPoissonInt b g x * ((pK c (s - x) : ℂ) * g' s) with hH
  have hHi : Integrable (Function.uncurry H) (volume.prod volume) := by
    have h0 := (integrable_mul_pK_sub hc hg'.norm fun _ => norm_nonneg _).swap
    refine (h0.const_mul M).mono' ?_ (ae_of_all _ fun q => ?_)
    · exact ((continuous_conjPoissonInt hb hg).aestronglyMeasurable.comp_fst).mul
        (((Complex.continuous_ofReal.comp ((continuous_pK hc).comp (continuous_snd.sub
          continuous_fst))).aestronglyMeasurable).mul hg'.aestronglyMeasurable.comp_snd)
    · change ‖conjPoissonInt b g q.1 * ((pK c (q.2 - q.1) : ℂ) * g' q.2)‖ ≤
        M * (‖g' (Prod.swap q).1‖ * pK c ((Prod.swap q).1 - (Prod.swap q).2))
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pK_nonneg hc _)]
      have := norm_conjPoissonInt_le hb hg q.1
      have h1 := pK_nonneg hc (q.2 - q.1)
      have h2 := norm_nonneg (g' q.2)
      calc ‖conjPoissonInt b g q.1‖ * (pK c (q.2 - q.1) * ‖g' q.2‖) ≤
          M * (pK c (q.2 - q.1) * ‖g' q.2‖) := by gcongr
        _ = M * (‖g' q.2‖ * pK c (q.2 - q.1)) := by ring
  calc ∫ x, conjPoissonInt b g x * poissonInt c g' x = ∫ x, ∫ s, H x s := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hH]; rw [poissonInt_eq_pK, integral_const_mul]
    _ = ∫ s, ∫ x, H x s := integral_integral_swap hHi
    _ = ∫ s, g' s * conjPoissonInt (c + b) g s := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        simp only [hH]
        rw [← poissonInt_conjPoissonInt hc hb hg, poissonInt_eq_pK, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        rw [show s - x = -(x - s) by ring, pK_neg]
        ring

/-- `∫ (P_b g)(Q_c g′) = −∫ g′ · Q_{c+b} g`. -/
theorem integral_poissonInt_mul_conjPoissonInt {b c : ℝ} (hb : 0 < b) (hc : 0 < c) {g g' : ℝ → ℂ}
    (hg : Integrable g) (hg' : Integrable g') :
    ∫ x, poissonInt b g x * conjPoissonInt c g' x = -∫ s, g' s * conjPoissonInt (c + b) g s := by
  set H : ℝ → ℝ → ℂ := fun x s => poissonInt b g x * ((qK c (s - x) : ℂ) * g' s) with hH
  have hHi : Integrable (Function.uncurry H) (volume.prod volume) := by
    refine ((integrable_poissonInt hb hg).norm.mul_prod (hg'.norm.const_mul (1 / (π * c)))
      ).mono' ?_ (ae_of_all _ fun q => ?_)
    · exact ((integrable_poissonInt hb hg).aestronglyMeasurable.comp_fst).mul
        (((Complex.continuous_ofReal.comp ((continuous_qK hc).comp (continuous_snd.sub
          continuous_fst))).aestronglyMeasurable).mul hg'.aestronglyMeasurable.comp_snd)
    · change ‖poissonInt b g q.1 * ((qK c (q.2 - q.1) : ℂ) * g' q.2)‖ ≤
        ‖poissonInt b g q.1‖ * (1 / (π * c) * ‖g' q.2‖)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (abs_qK_le hc _)
        (norm_nonneg _)) (norm_nonneg _)
  calc ∫ x, poissonInt b g x * conjPoissonInt c g' x = ∫ x, ∫ s, H x s := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hH]; rw [conjPoissonInt_eq_qK, integral_const_mul]
    _ = ∫ s, ∫ x, H x s := integral_integral_swap hHi
    _ = -∫ s, g' s * conjPoissonInt (c + b) g s := by
        rw [← integral_neg]
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        simp only [hH]
        rw [← conjPoissonInt_poissonInt hc hb hg, conjPoissonInt_eq_qK, ← integral_const_mul,
          ← integral_neg]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        rw [show s - x = -(x - s) by ring, qK_neg]
        push_cast; ring

/-- **Antisymmetry**: `∫ (Q_b g)(P_c g′) = −∫ (P_b g)(Q_c g′)`. -/
theorem integral_conjPoisson_antisymm {b c : ℝ} (hb : 0 < b) (hc : 0 < c) {g g' : ℝ → ℂ}
    (hg : Integrable g) (hg' : Integrable g') :
    ∫ x, conjPoissonInt b g x * poissonInt c g' x =
      -∫ x, poissonInt b g x * conjPoissonInt c g' x := by
  rw [integral_conjPoissonInt_mul_poissonInt hb hc hg hg',
    integral_poissonInt_mul_conjPoissonInt hb hc hg hg', neg_neg]

end Azurite.DLMF
