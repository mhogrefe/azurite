/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section10Residue
import Azurite.DLMF.Chapter1.Section10Continuation

/-!
# The residue theorem on rectangles

For the contour shift of DLMF §2.5(i) (2.5.6–2.5.7) we need the residue theorem for the
boundary of a rectangle. The Jordan-curve version of §1.10(iv) (`contourIntegral_eq_sum_residues`)
is first generalized to an arbitrary closed piecewise-`C¹` curve `P` and an open set `U`
containing its winding support (`contourIntegral_eq_sum_residues_winding`): for `f` analytic on
`U` minus finitely many points `S` off the curve,
`∮_P f = 2πi ∑_{s ∈ S} res_s(f) · W_P(s)`.
The rectangle with corners `p`, `q` is then parametrized as such a curve (`rectPath`), its
contour integral is Mathlib's boundary integral (`rectPath_contourIntegral`), its winding number is
`1` inside and `0` outside (`rectPath_windingNumber_eq_one`, `rectPath_windingNumber_eq_zero`,
by explicit logarithmic primitives on the four sides), and the residue theorem follows
(`rectBoundary_eq_sum_residues`).
-/

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

open Azurite.DLMF

/-- **Residue theorem with winding numbers**: `P` a closed piecewise-`C¹` curve, `U` an open set
containing its winding support, `f` analytic on `U` except at finitely many points `S ⊆ U` off
the curve, with punctured discs `ball s (R s) ⊆ U` containing no other singularity. Then
`∮_P f = 2πi ∑_{s ∈ S} res_s(f) · W_P(s)`. -/
theorem contourIntegral_eq_sum_residues_winding {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hKU : P.windingSupport ⊆ U) {S : Finset ℂ}
    (hcurveS : ∀ z ∈ P.curve, z ∉ S) (hfd : DifferentiableOn ℂ f (U \ ↑S)) (R : ℂ → ℝ)
    (hR : ∀ s ∈ S, 0 < R s ∧ ball s (R s) ⊆ U ∧ ∀ t ∈ S, t ≠ s → R s ≤ dist t s) :
    P.contourIntegral f = 2 * π * I * ∑ s ∈ S, residue f s (R s) * P.windingNumber s := by
  classical
  have hSc : IsClosed (↑S : Set ℂ) := S.finite_toSet.isClosed
  -- `f` is analytic on each punctured disk
  have hann : ∀ s ∈ S, annulus s 0 (R s) ⊆ U \ ↑S := by
    intro s hs z hz
    refine ⟨(hR s hs).2.1 (by rw [mem_ball, dist_eq_norm]; exact hz.2), fun hzS => ?_⟩
    by_cases hzs : z = s
    · have h1 : 0 < ‖z - s‖ := hz.1
      rw [hzs, sub_self, norm_zero] at h1
      exact lt_irrefl _ h1
    · have := (hR s hs).2.2 z hzS hzs
      rw [dist_eq_norm] at this
      linarith [hz.2]
  have hfs : ∀ s ∈ S, DifferentiableOn ℂ f (annulus s 0 (R s)) := fun s hs =>
    hfd.mono (hann s hs)
  have hPd : ∀ s ∈ S, DifferentiableOn ℂ (principalPart f s (R s)) {z | z ≠ s} := fun s hs =>
    differentiableOn_principalPart (hR s hs).1 (hfs s hs)
  have hPat : ∀ s ∈ S, ∀ z, z ≠ s → DifferentiableAt ℂ (principalPart f s (R s)) z :=
    fun s hs z hz => (hPd s hs).differentiableAt
      ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hz)
  set Q : ℂ → ℂ := fun z => ∑ s ∈ S, principalPart f s (R s) z with hQ
  set g : ℂ → ℂ := fun z => f z - Q z with hg
  have hQat : ∀ z, z ∉ S → DifferentiableAt ℂ Q z := fun z hz =>
    DifferentiableAt.fun_sum fun s hs => hPat s hs z (fun h => hz (h ▸ hs))
  set G : ℂ → ℂ := fun z => if z ∈ S then limUnder (𝓝[≠] z) g else g z with hG
  have hGg : ∀ z, z ∉ S → G =ᶠ[𝓝 z] g := fun z hz => by
    filter_upwards [hSc.isOpen_compl.mem_nhds hz] with w hw
    simp only [hG, show w ∉ S from hw, ↓reduceIte]
  -- differentiability of `G` on `U`
  have hGd : ∀ z ∈ U, DifferentiableAt ℂ G z := by
    intro z hz
    by_cases hzS : z ∈ S
    · set r := R z / 4 with hrdef
      have hr : 0 < r := by have := (hR z hzS).1; positivity
      have hball : ∀ w ∈ ball z r, w ≠ z → w ∈ annulus z 0 (R z) := fun w hw hwz => by
        rw [mem_ball, dist_eq_norm] at hw
        exact ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hwz), by linarith [(hR z hzS).1, hrdef]⟩
      have hnotS : ∀ w ∈ ball z r, w ≠ z → w ∉ S := fun w hw hwz =>
        ((hann z hzS) (hball w hw hwz)).2
      have hgd : DifferentiableOn ℂ g (ball z r \ {z}) := fun w hw => by
        have hwz : w ≠ z := hw.2
        exact ((hfs z hzS).differentiableAt ((isOpen_annulus z 0 (R z)).mem_nhds
          (hball w hw.1 hwz))).sub (hQat w (hnotS w hw.1 hwz)) |>.differentiableWithinAt
      obtain ⟨B, hB⟩ := norm_sub_principalPart_le (hR z hzS).1 (hfs z hzS)
      have hK : ∀ t ∈ S.erase z, ∃ K, ∀ w ∈ closedBall z r, ‖principalPart f t (R t) w‖ ≤ K := by
        intro t ht
        have htz : t ≠ z := Finset.ne_of_mem_erase ht
        have htS : t ∈ S := Finset.mem_of_mem_erase ht
        refine (isCompact_closedBall z r).exists_bound_of_continuousOn fun w hw => ?_
        refine (hPat t htS w fun h => ?_).continuousAt.continuousWithinAt
        rw [h, mem_closedBall] at hw
        have := (hR z hzS).2.2 t htS htz
        linarith [(hR z hzS).1, hrdef]
      choose! K hK using hK
      have hbdd : BddAbove (norm ∘ g '' (ball z r \ {z})) := by
        refine ⟨B + ∑ t ∈ S.erase z, K t, ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        have hwz : w ≠ z := hw.2
        have hw' : ‖w - z‖ < r := by rw [← dist_eq_norm]; exact hw.1
        simp only [Function.comp_apply, hg, hQ]
        rw [← Finset.add_sum_erase S _ hzS, ← sub_sub]
        refine (norm_sub_le _ _).trans (add_le_add (hB w (norm_pos_iff.mpr
          (sub_ne_zero.mpr hwz)) hw'.le) ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => hK t ht w ?_)
        exact ball_subset_closedBall hw.1
      have hupd := differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds z hr) hgd hbdd
      have hev : G =ᶠ[𝓝 z] Function.update g z (limUnder (𝓝[≠] z) g) := by
        filter_upwards [ball_mem_nhds z hr] with w hw
        by_cases hwz : w = z
        · subst hwz
          simp [hG, hzS]
        · simp only [hG, Function.update_of_ne hwz, hnotS w hw hwz, ↓reduceIte]
      exact (hupd.differentiableAt (ball_mem_nhds z hr)).congr_of_eventuallyEq hev
    · have hfz : DifferentiableAt ℂ f z :=
        hfd.differentiableAt ((hU.sdiff hSc).mem_nhds ⟨hz, hzS⟩)
      exact (hfz.sub (hQat z hzS)).congr_of_eventuallyEq (hGg z hzS)
  have hzero := P.contourIntegral_eq_zero hU (fun z hz => (hGd z hz).differentiableWithinAt) hKU
  have hcurve_eq : P.contourIntegral G = P.contourIntegral g :=
    P.contourIntegral_congr fun z hz => by simp only [hG, hcurveS z hz, ↓reduceIte]
  have hfcurve : ContinuousOn f P.curve := fun z hz =>
    (hfd.differentiableAt ((hU.sdiff hSc).mem_nhds
      ⟨hKU (P.curve_subset_windingSupport hz), hcurveS z hz⟩)).continuousAt.continuousWithinAt
  have hQc : ∀ s ∈ S, ContinuousOn (principalPart f s (R s)) P.curve := fun s hs z hz =>
    (hPat s hs z fun h => hcurveS z hz (h ▸ hs)).continuousAt.continuousWithinAt
  rw [hcurve_eq, P.contourIntegral_sub hfcurve (continuousOn_finsetSum _ hQc),
    P.contourIntegral_finset_sum _ hQc, sub_eq_zero] at hzero
  rw [hzero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [P.contourIntegral_principalPart (hR s hs).1 (hfs s hs) (fun h => hcurveS s h hs)]
  ring

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

open Azurite.JordanCurve

/-! ### The rectangle as a closed piecewise-`C¹` curve -/

/-- The sides of the rectangle with corners `p`, `q`, the `i`-th side parametrized on `[i, i+1]`:
bottom, right, top, left. -/
noncomputable def rectSide (p q : ℂ) : ℕ → ℝ → ℂ
  | 0 => fun s => (((q.re - p.re) * s + p.re : ℝ) : ℂ) + (p.im : ℂ) * I
  | 1 => fun s => (q.re : ℂ) + (((q.im - p.im) * s + (p.im - (q.im - p.im)) : ℝ) : ℂ) * I
  | 2 => fun s => (((p.re - q.re) * s + (q.re - 2 * (p.re - q.re)) : ℝ) : ℂ) + (q.im : ℂ) * I
  | _ => fun s => (p.re : ℂ) + (((p.im - q.im) * s + (q.im - 3 * (p.im - q.im)) : ℝ) : ℂ) * I

/-- The boundary of the rectangle, parametrized on `[0, 4]`. -/
noncomputable def rectCurve (p q : ℂ) (s : ℝ) : ℂ :=
  if s ≤ 1 then rectSide p q 0 s else if s ≤ 2 then rectSide p q 1 s
  else if s ≤ 3 then rectSide p q 2 s else rectSide p q 3 s

theorem rectSide_junction₁ (p q : ℂ) : rectSide p q 0 1 = rectSide p q 1 1 := by
  simp only [rectSide]
  push_cast
  ring

theorem rectSide_junction₂ (p q : ℂ) : rectSide p q 1 2 = rectSide p q 2 2 := by
  simp only [rectSide]
  push_cast
  ring

theorem rectSide_junction₃ (p q : ℂ) : rectSide p q 2 3 = rectSide p q 3 3 := by
  simp only [rectSide]
  push_cast
  ring

theorem rectSide_zero (p q : ℂ) : rectSide p q 0 0 = p := by
  simp only [rectSide]
  push_cast
  rw [mul_zero, zero_add, re_add_im]

theorem rectSide_four (p q : ℂ) : rectSide p q 3 4 = p := by
  simp only [rectSide]
  push_cast
  rw [show ((p.im : ℂ) - q.im) * 4 + (q.im - 3 * (p.im - q.im)) = p.im by ring, re_add_im]

theorem hasDerivAt_rectSide₀ (p q : ℂ) (s : ℝ) :
    HasDerivAt (rectSide p q 0) ((q.re - p.re : ℝ) : ℂ) s := by
  have := ((((hasDerivAt_id' s).const_mul (q.re - p.re)).add_const p.re).ofReal_comp).add_const
    ((p.im : ℂ) * I)
  simpa [rectSide] using this

theorem hasDerivAt_rectSide₁ (p q : ℂ) (s : ℝ) :
    HasDerivAt (rectSide p q 1) (((q.im - p.im : ℝ) : ℂ) * I) s := by
  have := (((((hasDerivAt_id' s).const_mul (q.im - p.im)).add_const
    (p.im - (q.im - p.im))).ofReal_comp).mul_const I).const_add (q.re : ℂ)
  simpa [rectSide] using this

theorem hasDerivAt_rectSide₂ (p q : ℂ) (s : ℝ) :
    HasDerivAt (rectSide p q 2) ((p.re - q.re : ℝ) : ℂ) s := by
  have := ((((hasDerivAt_id' s).const_mul (p.re - q.re)).add_const
    (q.re - 2 * (p.re - q.re))).ofReal_comp).add_const ((q.im : ℂ) * I)
  simpa [rectSide] using this

theorem hasDerivAt_rectSide₃ (p q : ℂ) (s : ℝ) :
    HasDerivAt (rectSide p q 3) (((p.im - q.im : ℝ) : ℂ) * I) s := by
  have := (((((hasDerivAt_id' s).const_mul (p.im - q.im)).add_const
    (q.im - 3 * (p.im - q.im))).ofReal_comp).mul_const I).const_add (p.re : ℂ)
  simpa [rectSide] using this

/-- The rectangle boundary as a closed piecewise-`C¹` curve. -/
noncomputable def rectPath (p q : ℂ) : ClosedPiecewiseC1 (rectCurve p q) 0 4 where
  n := 4
  t i := i
  g := rectSide p q
  lt i _ := by exact_mod_cast Nat.lt_succ_self i
  first := by simp
  last := by simp
  contDiff i _ := by
    have hA : ∀ c d : ℝ, ContDiff ℝ 1 fun s : ℝ => ((c * s + d : ℝ) : ℂ) := fun c d =>
      Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
    rcases i with _ | _ | _ | _ | i
    · exact (hA _ _).add contDiff_const
    · exact contDiff_const.add ((hA _ _).mul contDiff_const)
    · exact (hA _ _).add contDiff_const
    · exact contDiff_const.add ((hA _ _).mul contDiff_const)
    · exact contDiff_const.add ((hA _ _).mul contDiff_const)
  eqOn i hi := by
    intro s hs
    interval_cases i
    · norm_num at hs
      show rectCurve p q s = rectSide p q 0 s
      rw [rectCurve]
      simp only [hs.2, ↓reduceIte]
    · norm_num at hs
      show rectCurve p q s = rectSide p q 1 s
      rw [rectCurve]
      by_cases h1 : s ≤ 1
      · have : s = 1 := le_antisymm h1 hs.1
        rw [this]
        simp only [le_refl, ↓reduceIte, rectSide_junction₁]
      · simp only [h1, hs.2, ↓reduceIte]
    · norm_num at hs
      show rectCurve p q s = rectSide p q 2 s
      rw [rectCurve]
      have h1 : ¬ s ≤ 1 := by linarith [hs.1]
      by_cases h2 : s ≤ 2
      · have : s = 2 := le_antisymm h2 hs.1
        rw [this]
        simp only [show ¬ ((2 : ℝ) ≤ 1) by norm_num, le_refl, ↓reduceIte, rectSide_junction₂]
      · simp only [h1, h2, hs.2, ↓reduceIte]
    · norm_num at hs
      show rectCurve p q s = rectSide p q 3 s
      rw [rectCurve]
      have h1 : ¬ s ≤ 1 := by linarith [hs.1]
      have h2 : ¬ s ≤ 2 := by linarith [hs.1]
      by_cases h3 : s ≤ 3
      · have : s = 3 := le_antisymm h3 hs.1
        rw [this]
        simp only [show ¬ ((3 : ℝ) ≤ 1) by norm_num, show ¬ ((3 : ℝ) ≤ 2) by norm_num, le_refl,
          ↓reduceIte, rectSide_junction₃]
      · simp only [h1, h2, h3, ↓reduceIte]
  closed := by
    simp only [rectCurve, show (0 : ℝ) ≤ 1 by norm_num, show ¬ ((4 : ℝ) ≤ 1) by norm_num,
      show ¬ ((4 : ℝ) ≤ 2) by norm_num, show ¬ ((4 : ℝ) ≤ 3) by norm_num, ↓reduceIte,
      rectSide_zero, rectSide_four]

/-- Points of the boundary lie in the closed rectangle, with one coordinate on an edge. -/
theorem rectCurve_mem {p q : ℂ} (hx : p.re ≤ q.re) (hy : p.im ≤ q.im) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 4) :
    (rectCurve p q s).re ∈ Icc p.re q.re ∧ (rectCurve p q s).im ∈ Icc p.im q.im ∧
      ((rectCurve p q s).re = p.re ∨ (rectCurve p q s).re = q.re ∨
        (rectCurve p q s).im = p.im ∨ (rectCurve p q s).im = q.im) := by
  obtain ⟨hs0, hs4⟩ := hs
  unfold rectCurve
  split_ifs with h1 h2 h3
  · simp only [rectSide, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, add_im, mul_im, zero_add, add_zero]
    refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨le_rfl, hy⟩, Or.inr (Or.inr (Or.inl trivial))⟩
  · simp only [rectSide, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, add_im, mul_im, zero_add, add_zero]
    refine ⟨⟨hx, le_rfl⟩, ⟨by nlinarith, by nlinarith⟩, Or.inr (Or.inl trivial)⟩
  · simp only [rectSide, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, add_im, mul_im, zero_add, add_zero]
    refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨hy, le_rfl⟩, Or.inr (Or.inr (Or.inr trivial))⟩
  · simp only [rectSide, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, add_im, mul_im, zero_add, add_zero]
    refine ⟨⟨le_rfl, hx⟩, ⟨by nlinarith, by nlinarith⟩, Or.inl trivial⟩

theorem rectPath_curve {p q : ℂ} : (rectPath p q).curve = rectCurve p q '' Icc 0 4 := rfl

/-- A point strictly inside the rectangle is not on its boundary. -/
theorem notMem_rectPath_curve_of_mem {p q w : ℂ} (hx : p.re ≤ q.re) (hy : p.im ≤ q.im)
    (hw : p.re < w.re ∧ w.re < q.re ∧ p.im < w.im ∧ w.im < q.im) :
    w ∉ (rectPath p q).curve := by
  rintro ⟨s, hs, rfl⟩
  obtain ⟨-, -, h⟩ := rectCurve_mem hx hy hs
  rcases h with h | h | h | h <;> linarith [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2]

/-- A point outside the closed rectangle is not on its boundary. -/
theorem notMem_rectPath_curve_of_not_mem {p q w : ℂ} (hx : p.re ≤ q.re) (hy : p.im ≤ q.im)
    (hw : w.re < p.re ∨ q.re < w.re ∨ w.im < p.im ∨ q.im < w.im) :
    w ∉ (rectPath p q).curve := by
  rintro ⟨s, hs, rfl⟩
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := rectCurve_mem hx hy hs
  rcases hw with h | h | h | h <;> linarith

/-! ### The contour integral over the rectangle -/

theorem deriv_rectSide₀ (p q : ℂ) : deriv (rectSide p q 0) = fun _ => ((q.re - p.re : ℝ) : ℂ) :=
  funext fun s => (hasDerivAt_rectSide₀ p q s).deriv

theorem deriv_rectSide₁ (p q : ℂ) :
    deriv (rectSide p q 1) = fun _ => ((q.im - p.im : ℝ) : ℂ) * I :=
  funext fun s => (hasDerivAt_rectSide₁ p q s).deriv

theorem deriv_rectSide₂ (p q : ℂ) : deriv (rectSide p q 2) = fun _ => ((p.re - q.re : ℝ) : ℂ) :=
  funext fun s => (hasDerivAt_rectSide₂ p q s).deriv

theorem deriv_rectSide₃ (p q : ℂ) :
    deriv (rectSide p q 3) = fun _ => ((p.im - q.im : ℝ) : ℂ) * I :=
  funext fun s => (hasDerivAt_rectSide₃ p q s).deriv

/-- The contour integral over `rectPath p q` is Mathlib's boundary integral of the rectangle. -/
theorem rectPath_contourIntegral {p q : ℂ} (hx : p.re < q.re) (hy : p.im < q.im) (f : ℂ → ℂ) :
    (rectPath p q).contourIntegral f = rectBoundary f p q := by
  have hcx : q.re - p.re ≠ 0 := sub_ne_zero.mpr hx.ne'
  have hcy : q.im - p.im ≠ 0 := sub_ne_zero.mpr hy.ne'
  have hcx' : p.re - q.re ≠ 0 := sub_ne_zero.mpr hx.ne
  have hcy' : p.im - q.im ≠ 0 := sub_ne_zero.mpr hy.ne
  show ∑ i ∈ Finset.range 4, ∫ s in ((i : ℕ) : ℝ)..((i + 1 : ℕ) : ℝ),
    f (rectSide p q i s) * deriv (rectSide p q i) s = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, deriv_rectSide₀,
    deriv_rectSide₁, deriv_rectSide₂, deriv_rectSide₃, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_add]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  have e0 : ∫ s in (0 : ℝ)..1, f (rectSide p q 0 s) =
      ((q.re - p.re)⁻¹ : ℝ) • ∫ x in p.re..q.re, f (x + p.im * I) := by
    have := intervalIntegral.integral_comp_mul_add (f := fun x : ℝ => f (x + p.im * I)) (a := 0)
      (b := 1) hcx p.re
    rw [show (q.re - p.re) * 0 + p.re = p.re by ring,
      show (q.re - p.re) * 1 + p.re = q.re by ring] at this
    rw [← this]
    rfl
  have e1 : ∫ s in (1 : ℝ)..1 + 1, f (rectSide p q 1 s) =
      ((q.im - p.im)⁻¹ : ℝ) • ∫ y in p.im..q.im, f (q.re + y * I) := by
    have := intervalIntegral.integral_comp_mul_add (f := fun y : ℝ => f (q.re + y * I)) (a := 1)
      (b := 1 + 1) hcy (p.im - (q.im - p.im))
    rw [show (q.im - p.im) * 1 + (p.im - (q.im - p.im)) = p.im by ring,
      show (q.im - p.im) * (1 + 1) + (p.im - (q.im - p.im)) = q.im by ring] at this
    rw [← this]
    rfl
  have e2 : ∫ s in (2 : ℝ)..2 + 1, f (rectSide p q 2 s) =
      ((p.re - q.re)⁻¹ : ℝ) • ∫ x in q.re..p.re, f (x + q.im * I) := by
    have := intervalIntegral.integral_comp_mul_add (f := fun x : ℝ => f (x + q.im * I)) (a := 2)
      (b := 2 + 1) hcx' (q.re - 2 * (p.re - q.re))
    rw [show (p.re - q.re) * 2 + (q.re - 2 * (p.re - q.re)) = q.re by ring,
      show (p.re - q.re) * (2 + 1) + (q.re - 2 * (p.re - q.re)) = p.re by ring] at this
    rw [← this]
    rfl
  have e3 : ∫ s in (3 : ℝ)..3 + 1, f (rectSide p q 3 s) =
      ((p.im - q.im)⁻¹ : ℝ) • ∫ y in q.im..p.im, f (p.re + y * I) := by
    have := intervalIntegral.integral_comp_mul_add (f := fun y : ℝ => f (p.re + y * I)) (a := 3)
      (b := 3 + 1) hcy' (q.im - 3 * (p.im - q.im))
    rw [show (p.im - q.im) * 3 + (q.im - 3 * (p.im - q.im)) = q.im by ring,
      show (p.im - q.im) * (3 + 1) + (q.im - 3 * (p.im - q.im)) = p.im by ring] at this
    rw [← this]
    rfl
  have key : ∀ (c : ℝ), c ≠ 0 → ∀ X : ℂ, ((c⁻¹ : ℝ) • X) * (c : ℂ) = X := fun c hc X => by
    rw [Complex.real_smul, ofReal_inv, mul_comm, ← mul_assoc,
      mul_inv_cancel₀ (ofReal_ne_zero.mpr hc), one_mul]
  have key' : ∀ (c : ℝ), c ≠ 0 → ∀ X : ℂ, ((c⁻¹ : ℝ) • X) * ((c : ℂ) * I) = I * X :=
    fun c hc X => by
    have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
    rw [Complex.real_smul, ofReal_inv]
    field_simp
  rw [e0, e1, e2, e3, key _ hcx, key' _ hcy, key _ hcx', key' _ hcy', rectBoundary,
    intervalIntegral.integral_symm p.re q.re, intervalIntegral.integral_symm p.im q.im]
  simp only [smul_eq_mul]
  ring

/-! ### Winding numbers of the rectangle -/

theorem log_sub_log_neg_of_im_pos {w : ℂ} (h : 0 < w.im) : log w - log (-w) = π * I := by
  apply Complex.ext
  · simp [log_re, norm_neg]
  · simp [log_im, arg_neg_eq_arg_sub_pi_of_im_pos h]

theorem log_sub_log_neg_of_im_neg {w : ℂ} (h : w.im < 0) : log w - log (-w) = -(π * I) := by
  apply Complex.ext
  · simp [log_re, norm_neg]
  · simp [log_im, arg_neg_eq_arg_add_pi_of_im_neg h]

/-- Horizontal edge: `∫_a^b (x + iy − w)⁻¹ dx = log(b + iy − w) − log(a + iy − w)` for
`y ≠ ℑw`. -/
theorem integral_inv_sub_horizontal {w : ℂ} {y : ℝ} (hy : y ≠ w.im) (a b : ℝ) :
    ∫ x in a..b, ((x : ℂ) + y * I - w)⁻¹ =
      log ((b : ℂ) + y * I - w) - log ((a : ℂ) + y * I - w) := by
  have hmem : ∀ x : ℝ, (x : ℂ) + y * I - w ∈ slitPlane := fun x => by
    rw [mem_slitPlane_iff]
    right
    simp [sub_ne_zero.mpr hy]
  have hne : ∀ x : ℝ, (x : ℂ) + y * I - w ≠ 0 := fun x => slitPlane_ne_zero (hmem x)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => log ((x : ℂ) + y * I - w)) (fun x _ => ?_) ?_
  · have h1 : HasDerivAt (fun z : ℂ => log (z + y * I - w)) (1 / ((x : ℂ) + y * I - w)) x :=
      (((hasDerivAt_id' (x : ℂ)).add_const _).sub_const w).clog (hmem x)
    simpa [one_div] using h1.comp_ofReal
  · exact ((by fun_prop : Continuous fun x : ℝ => (x : ℂ) + y * I - w).inv₀ hne).intervalIntegrable
      (μ := volume) _ _

/-- Vertical edge to the right of `w`: `∫_a^b (x + iy − w)⁻¹ dy = −i(log(x + ib − w) −
log(x + ia − w))` for `x > ℜw`. -/
theorem integral_inv_sub_vertical_right {w : ℂ} {x : ℝ} (hx : w.re < x) (a b : ℝ) :
    ∫ y in a..b, ((x : ℂ) + y * I - w)⁻¹ =
      -I * (log ((x : ℂ) + b * I - w) - log ((x : ℂ) + a * I - w)) := by
  have hmem : ∀ y : ℝ, (x : ℂ) + y * I - w ∈ slitPlane := fun y => by
    rw [mem_slitPlane_iff]
    left
    simp [hx]
  have hne : ∀ y : ℝ, (x : ℂ) + y * I - w ≠ 0 := fun y => slitPlane_ne_zero (hmem y)
  have hint : ∫ y in a..b, I * ((x : ℂ) + y * I - w)⁻¹ =
      log ((x : ℂ) + b * I - w) - log ((x : ℂ) + a * I - w) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => log ((x : ℂ) + y * I - w)) (fun y _ => ?_) ?_
    · have h1 : HasDerivAt (fun z : ℂ => log (x + z * I - w)) (1 * I / ((x : ℂ) + y * I - w)) y :=
        ((((hasDerivAt_id' (y : ℂ)).mul_const I).const_add (x : ℂ)).sub_const w).clog (hmem y)
      exact (h1.comp_ofReal).congr_deriv (by rw [one_mul, div_eq_mul_inv])
    · exact (continuous_const.mul
        ((by fun_prop : Continuous fun y : ℝ => (x : ℂ) + y * I - w).inv₀ hne)).intervalIntegrable
        (μ := volume) _ _
  rw [← hint, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun y _ => by
    rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]

/-- Vertical edge to the left of `w`: `∫_a^b (x + iy − w)⁻¹ dy = −i(log(w − x − ib) −
log(w − x − ia))` for `x < ℜw`. -/
theorem integral_inv_sub_vertical_left {w : ℂ} {x : ℝ} (hx : x < w.re) (a b : ℝ) :
    ∫ y in a..b, ((x : ℂ) + y * I - w)⁻¹ =
      -I * (log (w - ((x : ℂ) + b * I)) - log (w - ((x : ℂ) + a * I))) := by
  have hmem : ∀ y : ℝ, w - ((x : ℂ) + y * I) ∈ slitPlane := fun y => by
    rw [mem_slitPlane_iff]
    left
    simp [hx]
  have hne : ∀ y : ℝ, (x : ℂ) + y * I - w ≠ 0 := fun y => by
    intro h
    apply slitPlane_ne_zero (hmem y)
    linear_combination -h
  have hint : ∫ y in a..b, I * ((x : ℂ) + y * I - w)⁻¹ =
      log (w - ((x : ℂ) + b * I)) - log (w - ((x : ℂ) + a * I)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => log (w - ((x : ℂ) + y * I))) (fun y _ => ?_) ?_
    · have h1 : HasDerivAt (fun z : ℂ => log (w - (x + z * I)))
          (-(1 * I) / (w - ((x : ℂ) + y * I))) y :=
        ((((hasDerivAt_id' (y : ℂ)).mul_const I).const_add (x : ℂ)).const_sub w).clog (hmem y)
      refine (h1.comp_ofReal).congr_deriv ?_
      rw [div_eq_mul_inv, one_mul, neg_mul, ← mul_neg, ← inv_neg, neg_sub]
    · exact (continuous_const.mul
        ((by fun_prop : Continuous fun y : ℝ => (x : ℂ) + y * I - w).inv₀ hne)).intervalIntegrable
        (μ := volume) _ _
  rw [← hint, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun y _ => by
    rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]

/-- `∮_{∂R} (z − w)⁻¹ dz = 2πi` for `w` inside the rectangle `R`. -/
theorem rectBoundary_inv_sub {p q w : ℂ}
    (hw : p.re < w.re ∧ w.re < q.re ∧ p.im < w.im ∧ w.im < q.im) :
    rectBoundary (fun z => (z - w)⁻¹) p q = 2 * π * I := by
  rw [rectBoundary, integral_inv_sub_horizontal hw.2.2.1.ne,
    integral_inv_sub_horizontal hw.2.2.2.ne', integral_inv_sub_vertical_right hw.2.1,
    integral_inv_sub_vertical_left hw.1]
  have h1 := log_sub_log_neg_of_im_pos (w := (p.re : ℂ) + q.im * I - w) (by simp [hw.2.2.2])
  have h2 := log_sub_log_neg_of_im_neg (w := (p.re : ℂ) + p.im * I - w) (by simp [hw.2.2.1])
  rw [show -((p.re : ℂ) + q.im * I - w) = w - ((p.re : ℂ) + q.im * I) by ring,
    show -((p.re : ℂ) + p.im * I - w) = w - ((p.re : ℂ) + p.im * I) by ring] at *
  simp only [smul_eq_mul]
  linear_combination h1 - h2 + (log ((q.re : ℂ) + p.im * I - w) - log ((q.re : ℂ) + q.im * I - w) +
    log (w - ((p.re : ℂ) + q.im * I)) - log (w - ((p.re : ℂ) + p.im * I))) * I_sq

/-- The winding number of the rectangle about an interior point is `1`. -/
theorem rectPath_windingNumber_eq_one {p q w : ℂ} (hx : p.re < q.re) (hy : p.im < q.im)
    (hw : p.re < w.re ∧ w.re < q.re ∧ p.im < w.im ∧ w.im < q.im) :
    (rectPath p q).windingNumber w = 1 := by
  have hnot := notMem_rectPath_curve_of_mem hx.le hy.le hw
  have h := (rectPath p q).windingQuot_eq_windingNumber hnot
  rw [ClosedPiecewiseC1.windingQuot, rectPath_contourIntegral hx hy, rectBoundary_inv_sub hw,
    div_self (by simp [Real.pi_ne_zero])] at h
  exact_mod_cast h.symm

/-- The winding number of the rectangle about a point outside the closed rectangle is `0`. -/
theorem rectPath_windingNumber_eq_zero {p q w : ℂ} (hx : p.re < q.re) (hy : p.im < q.im)
    (hw : w.re < p.re ∨ q.re < w.re ∨ w.im < p.im ∨ q.im < w.im) :
    (rectPath p q).windingNumber w = 0 := by
  have hnot := notMem_rectPath_curve_of_not_mem hx.le hy.le hw
  have h := (rectPath p q).windingQuot_eq_windingNumber hnot
  have hcurve : ∀ z ∈ (rectPath p q).curve, z.re ∈ Icc p.re q.re ∧ z.im ∈ Icc p.im q.im := by
    rintro z ⟨s, hs, rfl⟩
    exact ⟨(rectCurve_mem hx.le hy.le hs).1, (rectCurve_mem hx.le hy.le hs).2.1⟩
  have hne : ∀ z ∈ (rectPath p q).curve, z - w ≠ 0 := fun z hz h0 =>
    hnot (by rw [← sub_eq_zero.mp h0]; exact hz)
  have hcont : ContinuousOn (fun z => (z - w)⁻¹) (rectPath p q).curve :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  -- a logarithmic primitive on the curve
  have hzero : (rectPath p q).contourIntegral (fun z => (z - w)⁻¹) = 0 := by
    rcases hw with hw | hw | hw | hw
    · -- `w` to the left: `log (z − w)`
      refine (rectPath p q).contourIntegral_eq_zero_of_hasDerivAt (F := fun z => log (z - w))
        (fun z hz => ?_) hcont
      have hmem : z - w ∈ slitPlane := by
        rw [mem_slitPlane_iff]
        left
        simp only [sub_re]
        linarith [(hcurve z hz).1.1]
      exact (((hasDerivAt_id' z).sub_const w).clog hmem).congr_deriv (one_div _)
    · -- `w` to the right: `log (w − z)`
      refine (rectPath p q).contourIntegral_eq_zero_of_hasDerivAt (F := fun z => log (w - z))
        (fun z hz => ?_) hcont
      have hmem : w - z ∈ slitPlane := by
        rw [mem_slitPlane_iff]
        left
        simp only [sub_re]
        linarith [(hcurve z hz).1.2]
      refine (((hasDerivAt_id' z).const_sub w).clog hmem).congr_deriv ?_
      rw [div_eq_mul_inv, neg_one_mul, ← inv_neg, neg_sub]
    · -- `w` below: `log (z − w)`, `ℑ(z − w) > 0`
      refine (rectPath p q).contourIntegral_eq_zero_of_hasDerivAt (F := fun z => log (z - w))
        (fun z hz => ?_) hcont
      have hmem : z - w ∈ slitPlane := by
        rw [mem_slitPlane_iff]
        right
        simp only [sub_im]
        linarith [(hcurve z hz).2.1]
      exact (((hasDerivAt_id' z).sub_const w).clog hmem).congr_deriv (one_div _)
    · -- `w` above: `log (z − w)`, `ℑ(z − w) < 0`
      refine (rectPath p q).contourIntegral_eq_zero_of_hasDerivAt (F := fun z => log (z - w))
        (fun z hz => ?_) hcont
      have hmem : z - w ∈ slitPlane := by
        rw [mem_slitPlane_iff]
        right
        simp only [sub_im]
        linarith [(hcurve z hz).2.2]
      exact (((hasDerivAt_id' z).sub_const w).clog hmem).congr_deriv (one_div _)
  rw [ClosedPiecewiseC1.windingQuot, hzero, zero_div] at h
  exact_mod_cast h.symm

/-- The winding support of the rectangle path lies in the closed rectangle. -/
theorem rectPath_windingSupport_subset {p q : ℂ} (hx : p.re < q.re) (hy : p.im < q.im) :
    (rectPath p q).windingSupport ⊆ {z | z.re ∈ Icc p.re q.re ∧ z.im ∈ Icc p.im q.im} := by
  intro z hz
  rcases hz with ⟨s, hs, rfl⟩ | ⟨hzc, hW⟩
  · exact ⟨(rectCurve_mem hx.le hy.le hs).1, (rectCurve_mem hx.le hy.le hs).2.1⟩
  · by_contra hout
    apply hW
    apply rectPath_windingNumber_eq_zero hx hy
    by_contra hcon
    push Not at hcon
    exact hout ⟨⟨hcon.1, hcon.2.1⟩, ⟨hcon.2.2.1, hcon.2.2.2⟩⟩

/-- **The residue theorem on a rectangle**: `f` analytic on an open set `U` containing the closed
rectangle with corners `p`, `q`, except at finitely many points `S` strictly inside, with
punctured discs `ball s (R s) ⊆ U` containing no other singularity. Then
`∮_{∂R} f = 2πi ∑_{s ∈ S} res_s(f)`. -/
theorem rectBoundary_eq_sum_residues {p q : ℂ} (hx : p.re < q.re) (hy : p.im < q.im)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hrect : {z : ℂ | z.re ∈ Icc p.re q.re ∧ z.im ∈ Icc p.im q.im} ⊆ U) {S : Finset ℂ}
    (hS : ∀ s ∈ S, p.re < s.re ∧ s.re < q.re ∧ p.im < s.im ∧ s.im < q.im)
    (hfd : DifferentiableOn ℂ f (U \ ↑S)) (R : ℂ → ℝ)
    (hR : ∀ s ∈ S, 0 < R s ∧ ball s (R s) ⊆ U ∧ ∀ t ∈ S, t ≠ s → R s ≤ dist t s) :
    rectBoundary f p q = 2 * π * I * ∑ s ∈ S, residue f s (R s) := by
  have hcurveS : ∀ z ∈ (rectPath p q).curve, z ∉ S := fun z hz hzS =>
    notMem_rectPath_curve_of_mem hx.le hy.le (hS z hzS) hz
  have := (rectPath p q).contourIntegral_eq_sum_residues_winding hU
    ((rectPath_windingSupport_subset hx hy).trans hrect) hcurveS hfd R hR
  rw [rectPath_contourIntegral hx hy] at this
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [rectPath_windingNumber_eq_one hx hy (hS s hs), Int.cast_one, mul_one]

end Azurite.DLMF
