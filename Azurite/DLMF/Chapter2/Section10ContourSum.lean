/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section10Contour
import Azurite.DLMF.Chapter2.Section10Entire
import Azurite.DLMF.Chapter2.Section5LaplaceShift
import Azurite.DLMF.Chapter2.Section5LaplaceExample
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# DLMF §2.10(iii): 2.10.20

`∑_{j<n} xʲ/(j!)³ = (1/2i) ∮_𝒞 x^t cot(πt)/Γ(t + 1)³ dt` (`dlmf_2_10_20`), `x > 0`, with `𝒞` the
contour of Figure 2.10.1 (`cotPath (n − ½)`). `F(t) = x^t/Γ(t + 1)³` is entire (`hypF`,
`differentiable_hypF`); `F(t) cot(πt)` has residue `F(j)/π` at each integer `j`
(`residue_hypF_cot`, writing `sin(πt) = (t − j) S(t)` with `S` the slope function), and the
residue theorem with winding numbers (`contourIntegral_eq_sum_residues_winding`) applies on the
open set `{|t| < R + ¼, ℜt > −¾}`, which contains `K` and no other integer.
-/

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real Nat

namespace Azurite.DLMF

open Azurite.JordanCurve

/-- `F(t) = x^t/Γ(t + 1)³`. -/
noncomputable def hypF (x : ℝ) (t : ℂ) : ℂ := (x : ℂ) ^ t / Gamma (t + 1) ^ 3

theorem hypF_eq {x : ℝ} (hx : 0 < x) (t : ℂ) :
    hypF x t = cexp (Real.log x * t) * (Gamma (t + 1))⁻¹ ^ 3 := by
  rw [hypF, cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← ofReal_log hx.le]
  field_simp

theorem differentiable_hypF {x : ℝ} (hx : 0 < x) : Differentiable ℂ (hypF x) := by
  have hg : Differentiable ℂ fun t : ℂ => (Gamma (t + 1))⁻¹ := fun t =>
    DifferentiableAt.comp (g := fun s : ℂ => (Gamma s)⁻¹) (f := fun u : ℂ => u + 1) t
      (differentiable_one_div_Gamma (t + 1)) ((differentiable_id t).add_const 1)
  have he : Differentiable ℂ fun t : ℂ => cexp (Real.log x * t) := by fun_prop
  have h1 : Differentiable ℂ fun t : ℂ => cexp (Real.log x * t) * (Gamma (t + 1))⁻¹ ^ 3 :=
    he.mul (hg.pow 3)
  intro t
  exact (h1 t).congr_of_eventuallyEq (Eventually.of_forall fun u => hypF_eq hx u)

theorem hypF_nat (x : ℝ) (j : ℕ) : hypF x j = (x : ℂ) ^ j / ((j ! : ℂ) ^ 3) := by
  rw [hypF, cpow_natCast, Gamma_nat_eq_factorial]

/-- The residue of `F(t) cot(πt)` at an integer `j` is `F(j)/π`. -/
theorem residue_mul_cot {F : ℂ → ℂ} (hF : Differentiable ℂ F) (j : ℤ) :
    residue (fun t => F t * Complex.cot (π * t)) j (1 / 2) = F j / π := by
  set f : ℂ → ℂ := fun t => Complex.sin (π * t) with hf
  have hfd : Differentiable ℂ f := (differentiable_const _).mul differentiable_id |>.csin
  have hfj : f j = 0 := by
    simp only [hf]
    rw [Complex.sin_eq_zero_iff]; exact ⟨j, by ring⟩
  have hderiv : HasDerivAt f (Complex.cos (π * j) * π) j := by
    have := ((hasDerivAt_id (j : ℂ)).const_mul (π : ℂ)).csin
    simpa [hf, mul_comm] using this
  have hcos : Complex.cos (π * j) ≠ 0 := by
    rw [show (π : ℂ) * j = ((π * j : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      ofReal_ne_zero, mul_comm, Real.cos_int_mul_pi]
    exact zpow_ne_zero _ (by norm_num)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hS : ∀ t ∈ ball (j : ℂ) (1 / 2), dslope f j t ≠ 0 := by
    intro t ht
    by_cases htj : t = j
    · rw [htj, dslope_same, hderiv.deriv]; exact mul_ne_zero hcos hπ
    · have h1 := sub_smul_dslope f j t
      rw [hfj, sub_zero, smul_eq_mul] at h1
      intro h0
      rw [h0, mul_zero] at h1
      refine sin_pi_mul_ne_zero (fun k hk => ?_) h1.symm
      have hd : ‖(k : ℂ) - j‖ < 1 := by
        rw [← hk]
        have := mem_ball.mp ht
        rw [dist_eq_norm] at this; linarith
      have hkj : k ≠ j := fun h => htj (by rw [hk, h])
      have : (1 : ℝ) ≤ ‖((k - j : ℤ) : ℂ)‖ := by
        rw [Complex.norm_intCast]
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkj)
      push_cast at this; linarith
  have hdsl : DifferentiableOn ℂ (dslope f j) (ball (j : ℂ) (1 / 2)) :=
    (differentiableOn_dslope (ball_mem_nhds _ (by norm_num))).mpr hfd.differentiableOn
  have hA : DifferentiableOn ℂ (fun t => F t * Complex.cos (π * t) / dslope f j t)
      (ball (j : ℂ) (1 / 2)) :=
    ((hF.differentiableOn).mul (((differentiable_const _).mul differentiable_id).ccos
      ).differentiableOn).div hdsl hS
  rw [residue_eq_of_eq_div_add (by norm_num) hA (differentiableOn_const 0) (fun z hz => ?_)]
  · rw [dslope_same, hderiv.deriv]
    field_simp
  · have hz0 : z - j ≠ 0 := norm_pos_iff.mp hz.1
    have h1 := sub_smul_dslope f j z
    rw [hfj, sub_zero, smul_eq_mul] at h1
    rw [add_zero, Complex.cot_eq_cos_div_sin]
    change F z * (Complex.cos (π * z) / f z) = _
    rw [← h1]
    have hS' : dslope f j z ≠ 0 := hS z (by rw [mem_ball, dist_eq_norm]; exact hz.2)
    field_simp

theorem differentiableAt_cot_pi_mul {t : ℂ} (ht : ∀ k : ℤ, t ≠ k) :
    DifferentiableAt ℂ (fun t => Complex.cot (π * t)) t := by
  have h : (fun t => Complex.cot (π * t)) = fun t => Complex.cos (π * t) / Complex.sin (π * t) :=
    funext fun t => Complex.cot_eq_cos_div_sin _
  rw [h]
  exact (((differentiable_const _).mul differentiable_id).ccos t).div
    (((differentiable_const _).mul differentiable_id).csin t) (sin_pi_mul_ne_zero ht)

/-- The open set `{|t| < R + ¼, ℜt > −¾}`: it contains `K` and, for `R = n − ½`, no integer outside
`{0, …, n − 1}`. -/
def cotU (R : ℝ) : Set ℂ := {z | ‖z‖ < R + 1 / 4 ∧ -(3 / 4) < z.re}

theorem isOpen_cotU (R : ℝ) : IsOpen (cotU R) :=
  (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const continuous_re)

theorem cotK_subset_cotU {R : ℝ} (hR : 1 / 2 ≤ R) : cotK R ⊆ cotU R := by
  intro z hz
  have h := abs_le.mp (Complex.abs_re_le_norm z)
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

/-- **DLMF 2.10.20**: `∑_{j<n} xʲ/(j!)³ = (1/2i) ∫_𝒞 x^t cot(πt)/Γ(t + 1)³ dt` for `x > 0`,
`n ≥ 1`, with `𝒞` the contour of Figure 2.10.1 (`cotPath (n − ½)`, counterclockwise). -/
theorem dlmf_2_10_20 {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, (x : ℂ) ^ j / ((j ! : ℂ) ^ 3) =
      1 / (2 * I) * (cotPath ((n : ℝ) - 1 / 2)).contourIntegral
        (fun t => (x : ℂ) ^ t / Gamma (t + 1) ^ 3 * Complex.cot (π * t)) := by
  set R : ℝ := (n : ℝ) - 1 / 2 with hRdef
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 1 / 2 ≤ R := by linarith
  set S : Finset ℂ := (Finset.range n).image (fun j : ℕ => (j : ℂ)) with hS
  have hmemS : ∀ z ∈ S, ∃ j : ℕ, j < n ∧ z = j := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨j, Finset.mem_range.mp hj, rfl⟩
  have hcurveS : ∀ z ∈ (cotPath R).curve, z ∉ S := by
    intro z hz hzS
    obtain ⟨j, hj, rfl⟩ := hmemS z hzS
    have hj' : (j : ℝ) ≤ n - 1 := by
      have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
      linarith
    exact notMem_cotPath_curve hR (Nat.cast_nonneg j) (by linarith) (by exact_mod_cast hz)
  have hfd : DifferentiableOn ℂ (fun t => hypF x t * Complex.cot (π * t)) (cotU R \ ↑S) := by
    intro z ⟨hzU, hzS⟩
    have hnot : ∀ k : ℤ, z ≠ k := by
      rintro k rfl
      apply hzS
      obtain ⟨h1, h2⟩ := hzU
      simp only [Complex.intCast_re] at h2
      have hk0 : (0 : ℤ) ≤ k := by
        have : (-1 : ℤ) < k := by exact_mod_cast (by linarith : (-1 : ℝ) < k)
        omega
      have hkn : k < (n : ℤ) := by
        have h3 : ‖(k : ℂ)‖ = k := by
          rw [Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast hk0)]
        rw [h3] at h1
        have : (k : ℝ) < n := by linarith
        exact_mod_cast this
      refine Finset.mem_image.mpr ⟨k.toNat, Finset.mem_range.mpr (by omega), ?_⟩
      have : ((k.toNat : ℤ) : ℂ) = (k : ℂ) := by rw [Int.toNat_of_nonneg hk0]
      exact_mod_cast this
    exact ((differentiable_hypF hx z).mul (differentiableAt_cot_pi_mul hnot)).differentiableWithinAt
  have hR' : ∀ s ∈ S, 0 < (fun _ : ℂ => (1 / 2 : ℝ)) s ∧
      ball s ((fun _ : ℂ => (1 / 2 : ℝ)) s) ⊆ cotU R ∧
      ∀ t ∈ S, t ≠ s → (fun _ : ℂ => (1 / 2 : ℝ)) s ≤ dist t s := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := hmemS s hs
    have hj' : (j : ℝ) ≤ n - 1 := by
      have : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
      linarith
    refine ⟨by norm_num, fun w hw => ?_, fun t ht htj => ?_⟩
    · rw [mem_ball, dist_eq_norm] at hw
      have h1 := norm_sub_norm_le w (j : ℂ)
      have h2 := abs_le.mp (Complex.abs_re_le_norm (w - j))
      rw [Complex.norm_natCast] at h1
      simp only [Complex.sub_re, Complex.natCast_re] at h2
      exact ⟨by linarith, by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]⟩
    · obtain ⟨k, -, rfl⟩ := hmemS t ht
      have hkj : k ≠ j := fun h => htj (by rw [h])
      rw [dist_eq_norm, show (k : ℂ) - j = (((k : ℝ) - j : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      have : (1 : ℝ) ≤ |(k : ℝ) - j| := by
        rcases Nat.lt_or_gt_of_ne hkj with h | h
        · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      linarith
  have main := (cotPath R).contourIntegral_eq_sum_residues_winding (isOpen_cotU R)
    ((cotPath_windingSupport_subset hR).trans (cotK_subset_cotU hR)) hcurveS hfd
    (fun _ => 1 / 2) hR'
  have hint : (fun t => (x : ℂ) ^ t / Gamma (t + 1) ^ 3 * Complex.cot (π * t)) =
      fun t => hypF x t * Complex.cot (π * t) := rfl
  rw [hint, main, hS, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]
  have hterm : ∀ j ∈ Finset.range n, residue (fun t => hypF x t * Complex.cot (π * t)) (j : ℂ)
      (1 / 2) * ((cotPath R).windingNumber (j : ℂ) : ℂ) = hypF x j / π := by
    intro j hj
    have hj' : (j : ℝ) ≤ n - 1 := by
      have : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hj
      linarith
    have hres := residue_mul_cot (differentiable_hypF hx) (j : ℤ)
    have hW := cotPath_windingNumber_eq_one hR (Nat.cast_nonneg j) (by linarith : (j : ℝ) < R)
    push_cast at hres hW
    rw [hres, hW]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hypF_nat]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-! ### The halves `𝒞₁`, `𝒞₂` and 2.10.22 -/

/-- `∫ u(t) dt` along the `i`-th piece of `𝒞`, parameter `s ∈ [a, b]`. -/
noncomputable def cotPiece (R : ℝ) (u : ℂ → ℂ) (i : ℕ) (a b : ℝ) : ℂ :=
  ∫ s in a..b, u (cotSide R i s) * deriv (cotSide R i) s

/-- `∫_{𝒞₁} u(t) dt`, `𝒞₁` the upper half of `𝒞` (from `R` to `−½` through `ℑt ≥ 0`). -/
noncomputable def cotUpper (R : ℝ) (u : ℂ → ℂ) : ℂ :=
  cotPiece R u 0 (1 / 2) 1 + cotPiece R u 1 1 2 + cotPiece R u 2 2 (5 / 2)

/-- `∫_{𝒞₂} u(t) dt`, `𝒞₂` the lower half of `𝒞` (from `−½` to `R` through `ℑt ≤ 0`). -/
noncomputable def cotLower (R : ℝ) (u : ℂ → ℂ) : ℂ :=
  cotPiece R u 2 (5 / 2) 3 + cotPiece R u 3 3 4 + cotPiece R u 0 0 (1 / 2)

theorem cotSide_mem_curve {R : ℝ} {i : ℕ} (hi : i < 4) {s : ℝ} (hs : s ∈ Icc (i : ℝ) (i + 1)) :
    cotSide R i s ∈ (cotPath R).curve :=
  (cotPath R).mem_curve_of_mem_piece (i := i) hi (by exact_mod_cast hs)

theorem cotPiece_integrable {R : ℝ} {u : ℂ → ℂ} (hu : ContinuousOn u (cotPath R).curve) {i : ℕ}
    (hi : i < 4) {a b : ℝ} (ha : (i : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ i + 1) :
    IntervalIntegrable (fun s => u (cotSide R i s) * deriv (cotSide R i) s) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  refine ContinuousOn.mul ?_ ((contDiff_cotSide R i).continuous_deriv le_rfl).continuousOn
  refine hu.comp (contDiff_cotSide R i).continuous.continuousOn fun s hs => ?_
  exact cotSide_mem_curve hi ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- `∮_𝒞 = ∫_{𝒞₁} + ∫_{𝒞₂}`. -/
theorem cotPath_contourIntegral_eq {R : ℝ} {u : ℂ → ℂ} (hu : ContinuousOn u (cotPath R).curve) :
    (cotPath R).contourIntegral u = cotUpper R u + cotLower R u := by
  show ∑ i ∈ Finset.range 4, ∫ s in ((i : ℕ) : ℝ)..((i + 1 : ℕ) : ℝ),
    u (cotSide R i s) * deriv (cotSide R i) s = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_add]
  rw [show (1 : ℝ) + 1 = 2 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num,
    show (3 : ℝ) + 1 = 4 by norm_num]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (cotPiece_integrable hu (i := 0) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num))
      (cotPiece_integrable hu (i := 0) (by norm_num) (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (by norm_num)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (cotPiece_integrable hu (i := 2) (by norm_num) (by norm_num) (by norm_num : (2 : ℝ) ≤ 5 / 2)
        (by norm_num))
      (cotPiece_integrable hu (i := 2) (by norm_num) (by norm_num) (by norm_num : (5 / 2 : ℝ) ≤ 3)
        (by norm_num))]
  simp only [cotUpper, cotLower, cotPiece]
  norm_num
  ring

/-- Linearity of the half-contour integrals. -/
theorem cotPiece_linear {R : ℝ} {u v : ℂ → ℂ} (hu : ContinuousOn u (cotPath R).curve)
    (hv : ContinuousOn v (cotPath R).curve) (c d : ℂ) {i : ℕ} (hi : i < 4) {a b : ℝ}
    (ha : (i : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ i + 1) :
    cotPiece R (fun t => c * u t + d * v t) i a b =
      c * cotPiece R u i a b + d * cotPiece R v i a b := by
  simp only [cotPiece, add_mul, mul_assoc]
  rw [intervalIntegral.integral_add ((cotPiece_integrable hu hi ha hab hb).const_mul c)
    ((cotPiece_integrable hv hi ha hab hb).const_mul d), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

theorem cotUpper_linear {R : ℝ} {u v : ℂ → ℂ} (hu : ContinuousOn u (cotPath R).curve)
    (hv : ContinuousOn v (cotPath R).curve) (c d : ℂ) :
    cotUpper R (fun t => c * u t + d * v t) = c * cotUpper R u + d * cotUpper R v := by
  simp only [cotUpper]
  rw [cotPiece_linear hu hv c d (i := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cotPiece_linear hu hv c d (i := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cotPiece_linear hu hv c d (i := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  ring

theorem cotLower_linear {R : ℝ} {u v : ℂ → ℂ} (hu : ContinuousOn u (cotPath R).curve)
    (hv : ContinuousOn v (cotPath R).curve) (c d : ℂ) :
    cotLower R (fun t => c * u t + d * v t) = c * cotLower R u + d * cotLower R v := by
  simp only [cotLower]
  rw [cotPiece_linear hu hv c d (i := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cotPiece_linear hu hv c d (i := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cotPiece_linear hu hv c d (i := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  ring

theorem cotPiece_congr {R : ℝ} {u v : ℂ → ℂ} (h : EqOn u v (cotPath R).curve) {i : ℕ}
    (hi : i < 4) {a b : ℝ} (ha : (i : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ i + 1) :
    cotPiece R u i a b = cotPiece R v i a b := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hab] at hs
  rw [h (cotSide_mem_curve hi ⟨by linarith [hs.1], by linarith [hs.2]⟩)]

theorem cotUpper_congr {R : ℝ} {u v : ℂ → ℂ} (h : EqOn u v (cotPath R).curve) :
    cotUpper R u = cotUpper R v := by
  simp only [cotUpper]
  rw [cotPiece_congr h (i := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cotPiece_congr h (i := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cotPiece_congr h (i := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

theorem cotLower_congr {R : ℝ} {u v : ℂ → ℂ} (h : EqOn u v (cotPath R).curve) :
    cotLower R u = cotLower R v := by
  simp only [cotLower]
  rw [cotPiece_congr h (i := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cotPiece_congr h (i := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cotPiece_congr h (i := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

/-- Along a piece, the integral of a function with a primitive `G` is the difference of `G`. -/
theorem cotPiece_of_primitive {R : ℝ} {F G : ℂ → ℂ} (hF : Continuous F)
    (hG : ∀ z, HasDerivAt G (F z) z) {i : ℕ} (hi : i < 4) {a b : ℝ} (ha : (i : ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ i + 1) :
    cotPiece R F i a b = G (cotSide R i b) - G (cotSide R i a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => G (cotSide R i s))
    (fun s _ => ?_) (cotPiece_integrable hF.continuousOn hi ha hab hb)
  have h1 := ((contDiff_cotSide R i).differentiable one_ne_zero s).hasDerivAt
  have h2 := ((hG (cotSide R i s)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s h1
  convert h2 using 1
  · rfl
  · rw [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, mul_comm]

/-- No integer lies on `𝒞` for `R = n − ½`. -/
theorem cotPath_curve_ne_int {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ (cotPath ((n : ℝ) - 1 / 2)).curve) (k : ℤ) : z ≠ k := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : (1 : ℝ) / 2 ≤ (n : ℝ) - 1 / 2 := by linarith
  rintro rfl
  have hK := cotPath_curve_subset hR hz
  have hnk : ‖(k : ℂ)‖ = |(k : ℝ)| := Complex.norm_intCast k
  have hre : ((k : ℂ)).re = k := Complex.intCast_re k
  have hk : (0 : ℝ) ≤ k ∧ (k : ℝ) ≤ (n : ℝ) - 1 / 2 := by
    rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hre] at h2; rw [hnk, abs_of_nonneg h2] at h1; exact ⟨h2, h1⟩
    · rw [hre] at h2; rw [hnk, abs_of_nonpos h2] at h1
      have : (-1 : ℤ) < k := by exact_mod_cast (by linarith : (-1 : ℝ) < k)
      have : k ≤ 0 := by exact_mod_cast h2
      have hk0 : k = 0 := by omega
      subst hk0; norm_num; linarith
  have hlt : (k : ℝ) < (n : ℝ) - 1 / 2 := by
    have : k < (n : ℤ) := by
      have : (k : ℝ) < n := by linarith [hk.2]
      exact_mod_cast this
    have : (k : ℝ) ≤ n - 1 := by
      have : k ≤ (n : ℤ) - 1 := by omega
      exact_mod_cast this
    linarith
  exact notMem_cotPath_curve hR hk.1 hlt (by exact_mod_cast hz)

theorem continuousOn_div_cexp_sub_one {n : ℕ} (hn : 1 ≤ n) {F : ℂ → ℂ} (hF : Continuous F)
    (c : ℂ) (hc' : ∀ (t : ℂ) (m : ℤ), c * t = m * (2 * π * I) → ∃ k : ℤ, t = k) :
    ContinuousOn (fun t => F t / (cexp (c * t) - 1)) (cotPath ((n : ℝ) - 1 / 2)).curve := by
  intro t ht
  have hne : cexp (c * t) - 1 ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp h)
    obtain ⟨k, hk⟩ := hc' t m hm
    exact cotPath_curve_ne_int hn ht k hk
  exact (hF.continuousAt.div ((Complex.continuous_exp.comp (continuous_const.mul
    continuous_id)).continuousAt.sub continuousAt_const) hne).continuousWithinAt

theorem cotSide_zero_half (R : ℝ) : cotSide R 0 (1 / 2) = R := by
  simp only [cotSide]
  rw [show π * (1 / 2 : ℝ) - π / 2 = 0 by ring]
  simp

theorem cotSide_two_five_half (R : ℝ) : cotSide R 2 (5 / 2) = -(1 / 2) := by
  simp only [cotSide, cexp_ofReal_mul_I]
  rw [show π * (5 / 2 : ℝ) - 3 * π / 2 = π by ring, Real.cos_pi, Real.sin_pi]
  push_cast; ring

/-- **DLMF 2.10.22**: `∑_{j<n} xʲ/(j!)³ = ∫_{−1/2}^{n−1/2} x^t/Γ(t+1)³ dt
− ∫_{𝒞₁} x^t/Γ(t+1)³ dt/(e^{−2πit} − 1) + ∫_{𝒞₂} x^t/Γ(t+1)³ dt/(e^{2πit} − 1)`, with `𝒞₁`, `𝒞₂`
the upper and lower halves of `𝒞` (`cotUpper`, `cotLower`). -/
theorem dlmf_2_10_22 {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, (x : ℂ) ^ j / ((j ! : ℂ) ^ 3) =
      (∫ t in (-1 / 2 : ℝ)..((n : ℝ) - 1 / 2), hypF x t) -
        cotUpper ((n : ℝ) - 1 / 2) (fun t => hypF x t / (cexp (-2 * π * I * t) - 1)) +
        cotLower ((n : ℝ) - 1 / 2) (fun t => hypF x t / (cexp (2 * π * I * t) - 1)) := by
  set R : ℝ := (n : ℝ) - 1 / 2 with hRdef
  have hF := (differentiable_hypF hx).continuous
  have hπI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hEm : ContinuousOn (fun t => hypF x t / (cexp (-2 * π * I * t) - 1)) (cotPath R).curve :=
    continuousOn_div_cexp_sub_one hn hF _
      fun t m hm => ⟨-m, by
        apply mul_left_cancel₀ hπI; push_cast; linear_combination -hm⟩
  have hEp : ContinuousOn (fun t => hypF x t / (cexp (2 * π * I * t) - 1)) (cotPath R).curve :=
    continuousOn_div_cexp_sub_one hn hF _
      fun t m hm => ⟨m, by apply mul_left_cancel₀ hπI; linear_combination hm⟩
  have hcot : ContinuousOn (fun t => (x : ℂ) ^ t / Gamma (t + 1) ^ 3 * Complex.cot (π * t))
      (cotPath R).curve := fun t ht =>
    (hF.continuousAt.mul (differentiableAt_cot_pi_mul (cotPath_curve_ne_int hn ht)).continuousAt
      ).continuousWithinAt
  have h20 := dlmf_2_10_20 hx hn
  rw [cotPath_contourIntegral_eq hcot] at h20
  -- `cot(πt) = −i − 2i/(e^{−2πit} − 1) = i + 2i/(e^{2πit} − 1)` on `𝒞`
  have hU : cotUpper R (fun t => (x : ℂ) ^ t / Gamma (t + 1) ^ 3 * Complex.cot (π * t)) =
      cotUpper R (fun t => (-I) * hypF x t + (-2 * I) * (hypF x t / (cexp (-2 * π * I * t) - 1))) :=
    cotUpper_congr fun t ht => by
      have h := (dlmf_2_10_21 (cotPath_curve_ne_int hn ht)).1
      have hc : Complex.cot (π * t) = 2 * I * (-1 / 2 - 1 / (cexp (-2 * π * I * t) - 1)) := by
        rw [← h]; field_simp
      simp only [hypF]
      rw [hc]; ring
  have hL : cotLower R (fun t => (x : ℂ) ^ t / Gamma (t + 1) ^ 3 * Complex.cot (π * t)) =
      cotLower R (fun t => I * hypF x t + (2 * I) * (hypF x t / (cexp (2 * π * I * t) - 1))) :=
    cotLower_congr fun t ht => by
      have h := (dlmf_2_10_21 (cotPath_curve_ne_int hn ht)).2
      have hc : Complex.cot (π * t) = 2 * I * (1 / 2 + 1 / (cexp (2 * π * I * t) - 1)) := by
        rw [← h]; field_simp
      simp only [hypF]
      rw [hc]; ring
  rw [hU, hL, cotUpper_linear hF.continuousOn hEm, cotLower_linear hF.continuousOn hEp] at h20
  -- the primitive
  obtain ⟨G, hG⟩ := (differentiable_hypF hx).isExactOn_univ
  have hG' : ∀ z, HasDerivAt G (hypF x z) z := fun z => hG z (mem_univ z)
  have hUF : cotUpper R (hypF x) = G (-(1 / 2)) - G R := by
    simp only [cotUpper]
    rw [cotPiece_of_primitive hF hG' (i := 0) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num),
      cotPiece_of_primitive hF hG' (i := 1) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num),
      cotPiece_of_primitive hF hG' (i := 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num),
      cotSide_zero_half, cotSide_two_five_half, cotSide_junction₁, ← cotSide_junction₂]
    ring
  have hLF : cotLower R (hypF x) = G R - G (-(1 / 2)) := by
    simp only [cotLower]
    rw [cotPiece_of_primitive hF hG' (i := 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num),
      cotPiece_of_primitive hF hG' (i := 3) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num),
      cotPiece_of_primitive hF hG' (i := 0) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num),
      cotSide_zero_half, cotSide_two_five_half, cotSide_junction₃, cotSide_three_four,
      cotSide_zero_zero]
    ring
  have hreal : ∫ t in (-1 / 2 : ℝ)..R, hypF x t = G R - G (-(1 / 2)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => G t)
      (fun t _ => (hG' t).comp_ofReal) ((hF.comp continuous_ofReal).intervalIntegrable _ _)]
    push_cast; ring_nf
  rw [h20, hUF, hLF, hreal]
  field_simp
  ring

end Azurite.DLMF
