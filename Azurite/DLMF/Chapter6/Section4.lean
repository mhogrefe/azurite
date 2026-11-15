/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section10Multivalued
import Azurite.DLMF.Chapter4.Section3
import Azurite.DLMF.Chapter6.Section3

/-!
# DLMF §6.4: analytic continuation

Formalizations of <https://dlmf.nist.gov/6.4>, equations 6.4.1–6.4.7.

A point `z e^{iθ}` of the Riemann surface of the logarithm is represented by a logarithm `w` of
it (`z = e^w`; rotating by `θ` adds `iθ`).  The general values are entire functions of `w`:
`E1Gen w = Ein(e^w) − w − γ` (6.4.1), `CiGen`, `ChiGen`, `fGen`, `gGen`; on the strip
`|ℑw| < π` they are the principal values at `e^w`, and they are the only entire functions with
this property (`eq_of_eq_on_strip`).

* 6.4.1: `E1Gen`, `E1MV` (the set of values `Ein(z) − Ln z − γ`), `dlmf_6_4_1` (the values,
  the principal value on the strip, uniqueness of the continuation); "branch points at `z = 0`
  and `z = ∞`": `dlmf_6_4_branchPoint_zero` (§1.10(vi)'s `IsBranchPoint`),
  `dlmf_6_4_branchPoint_infty` (`IsBranchPointInfty`), both by reduction to `√z`
  (`not_isBranch_sqrt_punctured`, with `z ↦ 1/z` at `∞`).
* 6.4.2: `dlmf_6_4_2`, `dlmf_6_4_2_principal`; 6.4.3: `dlmf_6_4_3`.
* 6.4.4–6.4.7: `CiGen`, `ChiGen`, `fGen`, `gGen` (`dlmf_6_4_general`), `dlmf_6_4_4`–`dlmf_6_4_7`
  and their `_principal` forms (`Cin`, the integral of 6.2.16 even; `si(−z) = −si(z) − π`).
* Principal values ("real on the positive real axis and two-valued on the negative real axis"):
  `dlmf_6_4_principal_real`, `dlmf_6_4_principal_cut` (with `dlmf_6_2_1_cut`,
  `dlmf_6_2_11_cut`).
-/

open Complex Filter Topology Set Metric
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### The strip and uniqueness of the continuation -/

/-! The strip `−π < ℑw < π` is §4.3's `logStrip`, mapped by `exp` onto the cut plane. -/

theorem isOpen_logStrip : IsOpen logStrip :=
  (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)

theorem zero_mem_logStrip : (0 : ℂ) ∈ logStrip := by simp [logStrip, Real.pi_pos]

theorem log_exp_of_mem_logStrip {w : ℂ} (hw : w ∈ logStrip) : log (exp w) = w :=
  log_exp hw.1 hw.2.le

theorem exp_mem_slitPlane {w : ℂ} (hw : w ∈ logStrip) : exp w ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg]
  refine ⟨fun h => ?_, exp_ne_zero w⟩
  have := congrArg Complex.im (log_exp_of_mem_logStrip hw)
  rw [log_im, h] at this
  have h2 := hw.2
  linarith

theorem log_mem_logStrip {z : ℂ} (hz : z ∈ slitPlane) : log z ∈ logStrip := by
  rw [mem_slitPlane_iff_arg] at hz
  show -π < (log z).im ∧ (log z).im < π
  rw [log_im]
  exact ⟨lt_of_le_of_ne (neg_pi_lt_arg z).le (fun h => by
    have := neg_pi_lt_arg z; rw [← h] at this; exact lt_irrefl _ this), lt_of_le_of_ne
    (arg_le_pi z) hz.1⟩

/-- An entire function is determined by its values on the strip `−π < ℑw < π` (§4.3's `logStrip`) (identity theorem):
the general values below are the unique analytic continuations of the principal values. -/
theorem eq_of_eq_on_strip {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h : ∀ w ∈ logStrip, F w = G w) : F = G := by
  have hFa : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
  have hGa : AnalyticOnNhd ℂ G univ := fun z _ => hG.analyticAt z
  have hev : F =ᶠ[𝓝 0] G := eventually_of_mem (isOpen_logStrip.mem_nhds zero_mem_logStrip) h
  funext w
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_univ (mem_univ 0) hev
    (mem_univ w)

theorem exp_log_add_pi_mul_I {z : ℂ} (hz : z ≠ 0) : exp (log z + π * I) = -z := by
  rw [exp_add, exp_log hz, exp_pi_mul_I]; ring

theorem exp_log_sub_pi_mul_I {z : ℂ} (hz : z ≠ 0) : exp (log z - π * I) = -z := by
  rw [sub_eq_add_neg, exp_add, exp_log hz, exp_neg_pi_mul_I]; ring

theorem exp_add_pi_mul_I (w : ℂ) : exp (w + π * I) = -exp w := by
  rw [exp_add, exp_pi_mul_I]; ring

theorem exp_sub_pi_mul_I (w : ℂ) : exp (w - π * I) = -exp w := by
  rw [sub_eq_add_neg, exp_add, exp_neg_pi_mul_I]; ring

theorem exp_add_two_mul_pi_mul_I (w : ℂ) (m : ℤ) : exp (w + 2 * m * π * I) = exp w := by
  rw [exp_add, show 2 * (m : ℂ) * π * I = m * (2 * π * I) by ring, exp_int_mul_two_pi_mul_I,
    mul_one]

/-! ### 6.4.1–6.4.3: `E₁` -/

/-- The general value `E₁(z)` at the point `z = e^w`: `Ein(z) − w − γ` (6.4.1 with `Ln z = w`). -/
noncomputable def E1Gen (w : ℂ) : ℂ := ein (exp w) - w - γ

/-- The multivalued `E₁(z) = Ein(z) − Ln z − γ` as a set of values. -/
def E1MV (z : ℂ) : Set ℂ := {v | ∃ L, exp L = z ∧ v = ein z - L - γ}

theorem differentiable_E1Gen : Differentiable ℂ E1Gen :=
  ((dlmf_6_2_3_entire.comp differentiable_exp).sub differentiable_id).sub_const _

/-- **DLMF 6.4.1**: the general values of `E₁(z)` are `E1Gen w` over the logarithms `w` of `z`;
on the strip `−π < ℑw < π` (§4.3's `logStrip`) they are the principal value at `e^w`, and `E1Gen` is the only entire
continuation of the principal value. -/
theorem dlmf_6_4_1 :
    (∀ z, E1MV z = E1Gen '' {w | exp w = z}) ∧
      (∀ w ∈ logStrip, E1Gen w = expIntE₁ (exp w)) ∧
      (∀ G : ℂ → ℂ, Differentiable ℂ G → (∀ w ∈ logStrip, G w = expIntE₁ (exp w)) →
        G = E1Gen) := by
  have hprin : ∀ w ∈ logStrip, E1Gen w = expIntE₁ (exp w) := fun w hw => by
    rw [dlmf_6_2_4 (exp_mem_slitPlane hw), log_exp_of_mem_logStrip hw, E1Gen]
  refine ⟨fun z => ?_, hprin, fun G hG h => ?_⟩
  · ext v
    constructor
    · rintro ⟨L, hL, rfl⟩
      exact ⟨L, hL, by rw [E1Gen, hL]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by rw [E1Gen, hw]⟩
  · exact eq_of_eq_on_strip hG differentiable_E1Gen fun w hw => (h w hw).trans (hprin w hw).symm

/-- **DLMF 6.4.2**: `E₁(z e^{2mπi}) = E₁(z) − 2mπi`. -/
theorem dlmf_6_4_2 (w : ℂ) (m : ℤ) : E1Gen (w + 2 * m * π * I) = E1Gen w - 2 * m * π * I := by
  rw [E1Gen, E1Gen, exp_add_two_mul_pi_mul_I]
  ring

/-- **DLMF 6.4.2** at a principal point: `E₁(z e^{2mπi}) = E₁(z) − 2mπi`, `z` off the cut. -/
theorem dlmf_6_4_2_principal {z : ℂ} (hz : z ∈ slitPlane) (m : ℤ) :
    E1Gen (log z + 2 * m * π * I) = expIntE₁ z - 2 * m * π * I := by
  rw [dlmf_6_4_2, (dlmf_6_4_1).2.1 _ (log_mem_logStrip hz), exp_log (slitPlane_ne_zero hz)]

/-- **DLMF 6.4.3**: `E₁(z e^{±πi}) = Ein(−z) − ln z − γ ∓ πi`, `|ph z| ≤ π` (`z ≠ 0`). -/
theorem dlmf_6_4_3 {z : ℂ} (hz : z ≠ 0) :
    E1Gen (log z + π * I) = ein (-z) - log z - γ - π * I ∧
      E1Gen (log z - π * I) = ein (-z) - log z - γ + π * I := by
  constructor
  · rw [E1Gen, exp_log_add_pi_mul_I hz]; ring
  · rw [E1Gen, exp_log_sub_pi_mul_I hz]; ring

/-! ### Branch points of `E₁` at `0` and `∞` -/

/-- A branch of `E₁` gives a branch of `√z` on the same domain: `exp((Ein z − E₁ − γ)/2)`. -/
theorem isBranch_sqrt_of_E1 {f : ℂ → ℂ} {D : Set ℂ} (hf : IsBranch E1MV f D) :
    IsBranch sqrtMV (fun z => exp ((ein z - f z - γ) / 2)) D := by
  obtain ⟨hDo, hDc, hfd, hval⟩ := hf
  refine ⟨hDo, hDc, ?_, fun z hz => ?_⟩
  · exact ((((dlmf_6_2_3_entire.differentiableOn).sub hfd).sub_const _).div_const 2).cexp
  · obtain ⟨L, hL, hv⟩ := hval z hz
    show exp ((ein z - f z - γ) / 2) ^ 2 = z
    rw [← exp_nat_mul, hv]
    push_cast
    rw [show 2 * ((ein z - (ein z - L - γ) - γ) / 2) = L by ring, hL]

/-- The exterior `|z| > R` with the negative real axis removed is the image of a half-strip. -/
theorem exterior_slit_eq_image {R : ℝ} (hR : 0 < R) :
    {z : ℂ | R < ‖z‖} ∩ slitPlane = exp '' ({w | Real.log R < w.re} ∩ logStrip) := by
  ext z
  constructor
  · rintro ⟨hz, hzs⟩
    refine ⟨log z, ⟨?_, log_mem_logStrip hzs⟩, exp_log (slitPlane_ne_zero hzs)⟩
    show Real.log R < (log z).re
    rw [log_re]
    exact Real.log_lt_log hR hz
  · rintro ⟨w, ⟨hw, hws⟩, rfl⟩
    refine ⟨?_, exp_mem_slitPlane hws⟩
    show R < ‖exp w‖
    rw [norm_exp]
    have : Real.exp (Real.log R) < Real.exp w.re := Real.exp_lt_exp.mpr hw
    rwa [Real.exp_log hR] at this

/-- `∞` is a branch point of `F`: there is a branch in `|z| > R` cut along the negative real
axis, and none in any full neighbourhood `|z| > R` of `∞`. -/
def IsBranchPointInfty (F : ℂ → Set ℂ) : Prop :=
  (∃ R > 0, ∃ f, IsBranch F f ({z : ℂ | R < ‖z‖} ∩ slitPlane)) ∧
    ∀ R > 0, ¬ ∃ f, IsBranch F f {z : ℂ | R < ‖z‖}

theorem isBranch_E1_slit {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    (hDs : D ⊆ slitPlane) : IsBranch E1MV expIntE₁ D := by
  refine ⟨hD, hDc, ?_, fun z hz => ⟨log z, exp_log (slitPlane_ne_zero (hDs hz)),
    dlmf_6_2_4 (hDs hz)⟩⟩
  have h : DifferentiableOn ℂ (fun z => ein z - log z - γ) D :=
    ((dlmf_6_2_3_entire.differentiableOn).sub
      (fun z hz => (differentiableAt_log (hDs hz)).differentiableWithinAt)).sub_const _
  exact h.congr fun z hz => dlmf_6_2_4 (hDs hz)

/-- **DLMF §6.4**: `z = 0` is a branch point of `E₁`. -/
theorem dlmf_6_4_branchPoint_zero : IsBranchPoint E1MV 0 := by
  refine ⟨⟨1, one_pos, π, expIntE₁, ?_⟩, fun r hr ⟨f, hf⟩ =>
    not_isBranch_sqrt_punctured hr ⟨_, isBranch_sqrt_of_E1 hf⟩⟩
  rw [cutNbhd_zero_pi]
  have hsc : StarConvex ℝ ((1 / 2 : ℝ) : ℂ) (ball (0 : ℂ) 1 ∩ slitPlane) :=
    ((convex_ball (0 : ℂ) 1).starConvex (by simp; norm_num)).inter
      (starConvex_ofReal_slitPlane (by norm_num))
  have hmem : ((1 / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 ∩ slitPlane :=
    ⟨by simp; norm_num, by simp [mem_slitPlane_iff]⟩
  exact isBranch_E1_slit (isOpen_ball.inter isOpen_slitPlane)
    (hsc.isPathConnected hmem).isConnected.isPreconnected inter_subset_right

/-- **DLMF §6.4**: `z = ∞` is a branch point of `E₁`. -/
theorem dlmf_6_4_branchPoint_infty : IsBranchPointInfty E1MV := by
  refine ⟨⟨1, one_pos, expIntE₁, ?_⟩, fun R hR ⟨f, hf⟩ => ?_⟩
  · have hc : IsPreconnected ({z : ℂ | 1 < ‖z‖} ∩ slitPlane) := by
      rw [exterior_slit_eq_image one_pos]
      refine IsPreconnected.image ?_ _ continuous_exp.continuousOn
      refine (Convex.inter ?_ ?_).isPreconnected
      · exact convex_halfSpace_re_gt _
      · have : logStrip = {w : ℂ | w.im < π} ∩ {w : ℂ | -π < w.im} := by
          ext w; simp [logStrip, and_comm]
        rw [this]
        exact (convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _)
    exact isBranch_E1_slit ((isOpen_lt continuous_const continuous_norm).inter isOpen_slitPlane)
      hc inter_subset_right
  -- a branch near `∞` gives a branch of `√z` near `∞`, hence (by `z ↦ 1/z`) near `0`
  obtain ⟨hEo, hEc, hsd, hsq⟩ := isBranch_sqrt_of_E1 hf
  set s := fun z => exp ((ein z - f z - γ) / 2)
  set E : Set ℂ := {z : ℂ | R < ‖z‖}
  set D : Set ℂ := ball (0 : ℂ) R⁻¹ \ {0}
  have hinv : ∀ z, z ∈ D ↔ z⁻¹ ∈ E := fun z => by
    simp only [D, E, Set.mem_sdiff, mem_ball, dist_zero_right, mem_singleton_iff,
      mem_ofPred_eq, norm_inv]
    constructor
    · rintro ⟨h1, h2⟩
      rw [lt_inv_comm₀ hR (norm_pos_iff.mpr h2)]
      exact h1
    · intro h
      have h0 : z ≠ 0 := fun h0 => by simp [h0] at h; linarith
      exact ⟨by rwa [lt_inv_comm₀ (norm_pos_iff.mpr h0) hR], h0⟩
  have hDeq : D = Inv.inv '' E := by
    ext z
    constructor
    · intro hz
      exact ⟨z⁻¹, (hinv z).mp hz, inv_inv z⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hinv, inv_inv]
      exact hy
  have hs0 : ∀ y ∈ E, s y ≠ 0 := fun y _ => exp_ne_zero _
  have hbr : IsBranch sqrtMV (fun z => (s z⁻¹)⁻¹) D := by
    refine ⟨?_, ?_, ?_, fun z hz => ?_⟩
    · exact isOpen_ball.sdiff isClosed_singleton
    · rw [hDeq]
      exact hEc.image _ (continuousOn_inv₀.mono fun y (hy : R < ‖y‖) =>
        norm_ne_zero_iff.mp (by linarith [norm_nonneg y]))
    · intro z hz
      have hz0 : z ≠ 0 := hz.2
      have hzE := (hinv z).mp hz
      have h1 : DifferentiableAt ℂ s z⁻¹ := hsd.differentiableAt (hEo.mem_nhds hzE)
      exact ((h1.comp z (differentiableAt_inv hz0)).inv (hs0 _ hzE)).differentiableWithinAt
    · have hzE := (hinv z).mp hz
      have h1 : s z⁻¹ ^ 2 = z⁻¹ := hsq _ hzE
      show (s z⁻¹)⁻¹ ^ 2 = z
      rw [inv_pow, h1, inv_inv]
  exact not_isBranch_sqrt_punctured (inv_pos.mpr hR) ⟨_, hbr⟩

/-! ### 6.4.4–6.4.7: `Ci`, `Chi`, `f`, `g` -/

theorem si_eq (z : ℂ) : si z = SiF z - π / 2 := by rw [(dlmf_6_2_10 z).2, Si_eq]

theorem differentiable_si : Differentiable ℂ si := fun z => (hasDerivAt_si z).differentiableAt

/-- `si(−z) = −si(z) − π` (`Si` is odd). -/
theorem si_neg (z : ℂ) : si (-z) = -si z - π := by
  rw [(dlmf_6_2_10 _).2, (dlmf_6_2_10 z).2, dlmf_6_2_9_odd]
  ring

theorem chiInt_neg (z : ℂ) : chiInt (-z) = chiInt z := by
  rw [chiInt_eq, chiInt_eq, chiIntF, chiIntF, neg_neg]
  ring

/-- The general value `Ci(z) = −Cin(z) + Ln z + γ` at `z = e^w`. -/
noncomputable def CiGen (w : ℂ) : ℂ := -Cin (exp w) + w + γ

/-- The general value `Chi(z) = γ + Ln z + ∫_0^z (cosh t − 1)/t dt` at `z = e^w`. -/
noncomputable def ChiGen (w : ℂ) : ℂ := γ + w + chiInt (exp w)

/-- The general value of `f(z) = Ci(z) sin z − si(z) cos z` at `z = e^w`. -/
noncomputable def fGen (w : ℂ) : ℂ :=
  CiGen w * Complex.sin (exp w) - si (exp w) * Complex.cos (exp w)

/-- The general value of `g(z) = −Ci(z) cos z − si(z) sin z` at `z = e^w`. -/
noncomputable def gGen (w : ℂ) : ℂ :=
  -CiGen w * Complex.cos (exp w) - si (exp w) * Complex.sin (exp w)

theorem differentiable_CiGen : Differentiable ℂ CiGen :=
  (((dlmf_6_2_12_entire.comp differentiable_exp).neg).add differentiable_id).add_const _

theorem differentiable_ChiGen : Differentiable ℂ ChiGen :=
  (differentiable_id.const_add _).add (dlmf_6_2_16_entire.comp differentiable_exp)

theorem differentiable_fGen : Differentiable ℂ fGen :=
  (differentiable_CiGen.mul (Complex.differentiable_sin.comp differentiable_exp)).sub
    ((differentiable_si.comp differentiable_exp).mul
      (Complex.differentiable_cos.comp differentiable_exp))

theorem differentiable_gGen : Differentiable ℂ gGen :=
  (differentiable_CiGen.neg.mul (Complex.differentiable_cos.comp differentiable_exp)).sub
    ((differentiable_si.comp differentiable_exp).mul
      (Complex.differentiable_sin.comp differentiable_exp))

theorem CiGen_principal {w : ℂ} (hw : w ∈ logStrip) : CiGen w = Ci (exp w) := by
  rw [(dlmf_6_2_13 (exp_mem_slitPlane hw)).2, log_exp_of_mem_logStrip hw, CiGen]

/-- **DLMF §6.4**: "the general values of the other functions are defined in a similar manner":
`CiGen`, `ChiGen`, `fGen`, `gGen` are entire in `w`, agree with the principal values at `e^w` on
the strip `−π < ℑw < π` (§4.3's `logStrip`), and are the only such entire functions (`eq_of_eq_on_strip`). -/
theorem dlmf_6_4_general :
    (∀ w ∈ logStrip, CiGen w = Ci (exp w)) ∧ (∀ w ∈ logStrip, ChiGen w = Chi (exp w)) ∧
      (∀ w ∈ logStrip, fGen w = auxF (exp w)) ∧ (∀ w ∈ logStrip, gGen w = auxG (exp w)) ∧
      Differentiable ℂ CiGen ∧ Differentiable ℂ ChiGen ∧ Differentiable ℂ fGen ∧
      Differentiable ℂ gGen := by
  refine ⟨fun w hw => CiGen_principal hw, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_,
    differentiable_CiGen, differentiable_ChiGen, differentiable_fGen, differentiable_gGen⟩
  · rw [ChiGen, Chi, log_exp_of_mem_logStrip hw]
  · rw [fGen, auxF, CiGen_principal hw]
  · rw [gGen, auxG, CiGen_principal hw]

/-- **DLMF 6.4.4**: `Ci(z e^{±πi}) = ±πi + Ci(z)`. -/
theorem dlmf_6_4_4 (w : ℂ) :
    CiGen (w + π * I) = π * I + CiGen w ∧ CiGen (w - π * I) = -(π * I) + CiGen w := by
  constructor
  · rw [CiGen, CiGen, exp_add_pi_mul_I, dlmf_6_2_12_even]; ring
  · rw [CiGen, CiGen, exp_sub_pi_mul_I, dlmf_6_2_12_even]; ring

/-- **DLMF 6.4.4** at a principal point `z` off the cut. -/
theorem dlmf_6_4_4_principal {z : ℂ} (hz : z ∈ slitPlane) :
    CiGen (log z + π * I) = π * I + Ci z ∧ CiGen (log z - π * I) = -(π * I) + Ci z := by
  have h := CiGen_principal (log_mem_logStrip hz)
  rw [exp_log (slitPlane_ne_zero hz)] at h
  rw [← h]
  exact dlmf_6_4_4 _

/-- **DLMF 6.4.5**: `Chi(z e^{±πi}) = ±πi + Chi(z)`. -/
theorem dlmf_6_4_5 (w : ℂ) :
    ChiGen (w + π * I) = π * I + ChiGen w ∧ ChiGen (w - π * I) = -(π * I) + ChiGen w := by
  constructor
  · rw [ChiGen, ChiGen, exp_add_pi_mul_I, chiInt_neg]; ring
  · rw [ChiGen, ChiGen, exp_sub_pi_mul_I, chiInt_neg]; ring

/-- **DLMF 6.4.5** at a principal point `z` off the cut. -/
theorem dlmf_6_4_5_principal {z : ℂ} (hz : z ∈ slitPlane) :
    ChiGen (log z + π * I) = π * I + Chi z ∧ ChiGen (log z - π * I) = -(π * I) + Chi z := by
  have h : ChiGen (log z) = Chi z := by rw [ChiGen, Chi, exp_log (slitPlane_ne_zero hz)]
  rw [← h]
  exact dlmf_6_4_5 _

theorem exp_neg_I_mul (ζ : ℂ) : cexp (-I * ζ) = Complex.cos ζ - Complex.sin ζ * I := by
  rw [show -I * ζ = (-ζ) * I by ring, exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

theorem exp_I_mul (ζ : ℂ) : cexp (I * ζ) = Complex.cos ζ + Complex.sin ζ * I := by
  rw [mul_comm, exp_mul_I]

/-- **DLMF 6.4.6**: `f(z e^{±πi}) = π e^{∓iz} − f(z)`. -/
theorem dlmf_6_4_6 (w : ℂ) :
    fGen (w + π * I) = π * cexp (-I * exp w) - fGen w ∧
      fGen (w - π * I) = π * cexp (I * exp w) - fGen w := by
  have h1 := (dlmf_6_4_4 w).1
  have h2 := (dlmf_6_4_4 w).2
  constructor
  · rw [fGen, fGen, h1, exp_add_pi_mul_I, Complex.sin_neg, Complex.cos_neg, si_neg,
      exp_neg_I_mul]
    ring
  · rw [fGen, fGen, h2, exp_sub_pi_mul_I, Complex.sin_neg, Complex.cos_neg, si_neg, exp_I_mul]
    ring

/-- **DLMF 6.4.7**: `g(z e^{±πi}) = ∓πi e^{∓iz} + g(z)`. -/
theorem dlmf_6_4_7 (w : ℂ) :
    gGen (w + π * I) = -(π * I) * cexp (-I * exp w) + gGen w ∧
      gGen (w - π * I) = π * I * cexp (I * exp w) + gGen w := by
  have h1 := (dlmf_6_4_4 w).1
  have h2 := (dlmf_6_4_4 w).2
  constructor
  · rw [gGen, gGen, h1, exp_add_pi_mul_I, Complex.sin_neg, Complex.cos_neg, si_neg,
      exp_neg_I_mul]
    linear_combination (-(π : ℂ) * Complex.sin (exp w)) * I_sq
  · rw [gGen, gGen, h2, exp_sub_pi_mul_I, Complex.sin_neg, Complex.cos_neg, si_neg, exp_I_mul]
    linear_combination (-(π : ℂ) * Complex.sin (exp w)) * I_sq

/-- **DLMF 6.4.6–6.4.7** at a principal point `z` off the cut. -/
theorem dlmf_6_4_6_7_principal {z : ℂ} (hz : z ∈ slitPlane) :
    fGen (log z + π * I) = π * cexp (-I * z) - auxF z ∧
      fGen (log z - π * I) = π * cexp (I * z) - auxF z ∧
      gGen (log z + π * I) = -(π * I) * cexp (-I * z) + auxG z ∧
      gGen (log z - π * I) = π * I * cexp (I * z) + auxG z := by
  have hz0 := slitPlane_ne_zero hz
  have hs := log_mem_logStrip hz
  have hf : fGen (log z) = auxF z := by rw [(dlmf_6_4_general).2.2.1 _ hs, exp_log hz0]
  have hg : gGen (log z) = auxG z := by rw [(dlmf_6_4_general).2.2.2.1 _ hs, exp_log hz0]
  obtain ⟨f1, f2⟩ := dlmf_6_4_6 (log z)
  obtain ⟨g1, g2⟩ := dlmf_6_4_7 (log z)
  rw [exp_log hz0, hf] at f1 f2
  rw [exp_log hz0, hg] at g1 g2
  exact ⟨f1, f2, g1, g2⟩

/-! ### Principal values -/

theorem si_ofReal (x : ℝ) : si x = ((SiR x - π / 2 : ℝ) : ℂ) := by
  rw [(dlmf_6_2_10 _).2, dlmf_6_3_F2_Si_real]
  push_cast
  ring

theorem chiInt_ofReal (x : ℝ) : chiInt x = ((-(BZ.EinR x + BZ.EinR (-x)) / 2 : ℝ) : ℂ) := by
  rw [chiInt_eq, chiIntF, ein_ofReal, ← ofReal_neg, ein_ofReal]
  push_cast
  ring

/-- **DLMF §6.4** (principal values): `E₁`, `Ci`, `Chi`, `f`, `g` are real on the positive real
axis. -/
theorem dlmf_6_4_principal_real {x : ℝ} (hx : 0 < x) :
    (expIntE₁ x).im = 0 ∧ (Ci x).im = 0 ∧ (Chi x).im = 0 ∧ (auxF x).im = 0 ∧
      (auxG x).im = 0 := by
  have hCi := dlmf_6_3_F2_Ci_real hx
  have hsi := si_ofReal x
  refine ⟨by rw [dlmf_6_3_F1_real hx, ofReal_im], by rw [hCi, ofReal_im], ?_, ?_, ?_⟩
  · rw [Chi, chiInt_ofReal, ← ofReal_log hx.le]
    simp
  · rw [auxF, hCi, hsi, ← ofReal_sin, ← ofReal_cos]
    simp
  · rw [auxG, hCi, hsi, ← ofReal_sin, ← ofReal_cos]
    simp

/-- **DLMF §6.4** (principal values): on the negative real axis `Chi`, `f`, `g` have the
boundary values from above and below (two-valued, like `E₁` and `Ci`, `dlmf_6_2_1_cut`,
`dlmf_6_2_11_cut`): `Chi(x ± i0) = γ + ln|x| ± πi + ∫_0^x (cosh t − 1)/t dt`, and `f`, `g` from
`Ci(x ± i0)`.  The jumps are `2πi`, `2πi sin x`, `−2πi cos x`. -/
theorem dlmf_6_4_principal_cut {x : ℝ} (hx : x < 0) :
    Tendsto Chi (𝓝[{z | 0 < z.im}] (x : ℂ)) (𝓝 (γ + (Real.log (-x) + π * I) + chiInt x)) ∧
      Tendsto Chi (𝓝[{z | z.im < 0}] (x : ℂ)) (𝓝 (γ + (Real.log (-x) - π * I) + chiInt x)) ∧
      Tendsto auxF (𝓝[{z | 0 < z.im}] (x : ℂ))
        (𝓝 ((-Cin x + (Real.log (-x) + π * I) + γ) * Complex.sin x - si x * Complex.cos x)) ∧
      Tendsto auxF (𝓝[{z | z.im < 0}] (x : ℂ))
        (𝓝 ((-Cin x + (Real.log (-x) - π * I) + γ) * Complex.sin x - si x * Complex.cos x)) ∧
      Tendsto auxG (𝓝[{z | 0 < z.im}] (x : ℂ))
        (𝓝 (-(-Cin x + (Real.log (-x) + π * I) + γ) * Complex.cos x - si x * Complex.sin x)) ∧
      Tendsto auxG (𝓝[{z | z.im < 0}] (x : ℂ))
        (𝓝 (-(-Cin x + (Real.log (-x) - π * I) + γ) * Complex.cos x - si x * Complex.sin x)) := by
  have hnorm : ‖(x : ℂ)‖ = -x := by rw [norm_real, Real.norm_eq_abs, abs_of_neg hx]
  have hre : (x : ℂ).re < 0 := by simpa using hx
  have him : (x : ℂ).im = 0 := ofReal_im x
  have hchi : Tendsto chiInt (𝓝 (x : ℂ)) (𝓝 (chiInt x)) :=
    (dlmf_6_2_16_entire x).continuousAt.tendsto
  have hlogU := (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).mono_left
      (nhdsWithin_mono _ fun z (hz : 0 < z.im) => le_of_lt hz)
  have hlogL := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him
  rw [hnorm] at hlogU hlogL
  obtain ⟨hCiU, hCiL⟩ := dlmf_6_2_11_cut hx
  have hc : ∀ {h : ℂ → ℂ}, Continuous h → ∀ s : Set ℂ, Tendsto h (𝓝[s] (x : ℂ)) (𝓝 (h x)) :=
    fun hh s => (hh.tendsto _).mono_left nhdsWithin_le_nhds
  have hsin := hc Complex.continuous_sin
  have hcos := hc Complex.continuous_cos
  have hsi := hc differentiable_si.continuous
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (tendsto_const_nhds.add hlogU).add (hchi.mono_left nhdsWithin_le_nhds)
  · exact (tendsto_const_nhds.add hlogL).add (hchi.mono_left nhdsWithin_le_nhds)
  · exact (hCiU.mul (hsin _)).sub ((hsi _).mul (hcos _))
  · exact (hCiL.mul (hsin _)).sub ((hsi _).mul (hcos _))
  · exact (hCiU.neg.mul (hcos _)).sub ((hsi _).mul (hsin _))
  · exact (hCiL.neg.mul (hcos _)).sub ((hsi _).mul (hsin _))

end Azurite.DLMF
