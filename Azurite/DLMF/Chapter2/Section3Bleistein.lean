/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3Watson
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# DLMF §2.3(v): Bleistein's method, the uniform expansion (2.3.32–2.3.33)

After the quadratic change of variable (`Section3BleisteinChange.lean`) the integral is
`e^{−xb} ∫_U exp(−x(½w² − aw)) f(α, w) w^{λ−1} dw` (2.3.29), with `U = (0, κ)`.
`bleisteinWeight lam x a w` is the weight `exp(−x(½w² − aw)) w^{λ−1}`.

* `bleisteinF` is `Fₛ` of 2.3.33; `bleisteinG` is the same integral with `|τ − y|ˢ`.
* `dlmf_2_3_33`: integrating one Taylor term over `(0, ∞)` gives
  `∫₀^∞ exp(−x(½w² − aw)) (w − a)ˢ w^{λ−1} dw = x^{−(λ+s)/2} Fₛ(a√x)`. This is the step
  "replace `κ` by `∞` and integrate term by term" of DLMF.
* `dlmf_2_3_32`: the uniform form of 2.3.32. DLMF derives it only formally. The precise version
  here assumes a Taylor remainder bound for `f(α, ·)` about `w = a(α)`, uniform in the parameter
  `α`, which is the rigorous meaning of "coefficients `φₛ(α)` continuous at `α = 0`". It also
  assumes `κ(α) ≥ a(α) + δ`. The error after `n` terms is then at most
  `K x^{−(λ+n)/2} Gₙ(a√x)`, with `K` independent of `α` and `x`.
* `dlmf_2_3_32_even`: for even `n` the bound is the `n`-th term's own function,
  `K x^{−(λ+n)/2} Fₙ(a√x)` (`bleisteinG_even`).
* `bleisteinF_zero`: `Fₛ(0) = 2^{(λ+s)/2 − 1} Γ((λ+s)/2)`. At `a = 0` the expansion is Watson's
  lemma in the variable `w`.
-/

open Set Filter Topology MeasureTheory

namespace Azurite.DLMF

/-- The weight `exp(−x(½w² − aw)) w^{λ−1}` of DLMF 2.3.29. -/
noncomputable def bleisteinWeight (lam x a w : ℝ) : ℝ :=
  Real.exp (-(x * (w ^ 2 / 2 - a * w))) * w ^ (lam - 1)

/-- DLMF 2.3.33: `Fₛ(y) = ∫₀^∞ exp(−½τ² + yτ)(τ − y)ˢ τ^{λ−1} dτ`. -/
noncomputable def bleisteinF (lam : ℝ) (s : ℕ) (y : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), Real.exp (-(τ ^ 2 / 2) + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)

/-- The majorant of `Fₛ` in the error bound: `Gₛ(y) = ∫₀^∞ exp(−½τ² + yτ)|τ − y|ˢ τ^{λ−1} dτ`. -/
noncomputable def bleisteinG (lam : ℝ) (s : ℕ) (y : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), Real.exp (-(τ ^ 2 / 2) + y * τ) * |τ - y| ^ s * τ ^ (lam - 1)

theorem bleisteinWeight_nonneg {lam x a w : ℝ} (hw : 0 ≤ w) : 0 ≤ bleisteinWeight lam x a w :=
  mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw _)

theorem measurable_bleisteinWeight (lam x a : ℝ) : Measurable (bleisteinWeight lam x a) := by
  unfold bleisteinWeight
  fun_prop

theorem abs_sub_pow_le_two_pow {w : ℝ} (hw : 0 ≤ w) (y : ℝ) (s : ℕ) :
    |w - y| ^ s ≤ 2 ^ s * (w ^ s + |y| ^ s) := by
  have h1 : |w - y| ≤ 2 * max w |y| := by
    calc |w - y| ≤ |w| + |y| := abs_sub _ _
      _ = w + |y| := by rw [abs_of_nonneg hw]
      _ ≤ 2 * max w |y| := by linarith [le_max_left w |y|, le_max_right w |y|]
  calc |w - y| ^ s ≤ (2 * max w |y|) ^ s := pow_le_pow_left₀ (abs_nonneg _) h1 s
    _ = 2 ^ s * max w |y| ^ s := mul_pow _ _ _
    _ ≤ 2 ^ s * (w ^ s + |y| ^ s) := by
      gcongr
      rcases le_total w |y| with h | h
      · rw [max_eq_right h]; linarith [pow_nonneg hw s]
      · rw [max_eq_left h]; linarith [pow_nonneg (abs_nonneg y) s]

theorem exp_bleistein_le {x : ℝ} (hx : 0 ≤ x) (a w : ℝ) :
    Real.exp (-(x * (w ^ 2 / 2 - a * w))) ≤
      Real.exp (x * a ^ 2) * Real.exp (-(x / 4) * w ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hx (sq_nonneg (a - w / 2))]

/-- The majorant integrand `exp(−x(½w² − aw)) |w − a|ˢ w^{λ−1}` is integrable on `(0, ∞)`. -/
theorem integrableOn_bleisteinWeight_abs {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (a : ℝ)
    (s : ℕ) : IntegrableOn (fun w => bleisteinWeight lam x a w * |w - a| ^ s) (Ioi 0) := by
  have hs : (0 : ℝ) ≤ s := s.cast_nonneg
  have h1 := integrableOn_rpow_mul_exp_neg_mul_sq (b := x / 4) (by positivity)
    (s := lam - 1 + s) (by linarith)
  have h2 := integrableOn_rpow_mul_exp_neg_mul_sq (b := x / 4) (by positivity)
    (s := lam - 1) (by linarith)
  refine Integrable.mono' ((h1.add (h2.const_mul (|a| ^ s))).const_mul
    (Real.exp (x * a ^ 2) * 2 ^ s)) ?_ ?_
  · exact ((measurable_bleisteinWeight lam x a).mul (by fun_prop)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
    have hw : (0 : ℝ) < w := hw
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (bleisteinWeight_nonneg hw.le)
      (pow_nonneg (abs_nonneg _) _))]
    have hr : w ^ (lam - 1 + s) = w ^ (lam - 1) * w ^ s := Real.rpow_add_natCast hw.ne' _ _
    unfold bleisteinWeight
    show _ ≤ Real.exp (x * a ^ 2) * 2 ^ s * (w ^ (lam - 1 + s) * Real.exp (-(x / 4) * w ^ 2) +
      |a| ^ s * (w ^ (lam - 1) * Real.exp (-(x / 4) * w ^ 2)))
    rw [hr]
    have e := exp_bleistein_le hx.le a w
    have p := abs_sub_pow_le_two_pow hw.le a s
    have hwr := Real.rpow_nonneg hw.le (lam - 1)
    calc Real.exp (-(x * (w ^ 2 / 2 - a * w))) * w ^ (lam - 1) * |w - a| ^ s
        ≤ (Real.exp (x * a ^ 2) * Real.exp (-(x / 4) * w ^ 2)) * w ^ (lam - 1) *
            (2 ^ s * (w ^ s + |a| ^ s)) := by gcongr
      _ = _ := by ring

theorem integrableOn_bleisteinWeight_pow {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (a : ℝ)
    (s : ℕ) : IntegrableOn (fun w => bleisteinWeight lam x a w * (w - a) ^ s) (Ioi 0) := by
  refine (integrableOn_bleisteinWeight_abs hlam hx a s).mono'
    ((measurable_bleisteinWeight lam x a).mul (by fun_prop)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
  have hw : (0 : ℝ) < w := hw
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (bleisteinWeight_nonneg hw.le)]

/-- Scaling `w = τ/√x` in a weighted integral, for a factor `P` homogeneous of degree `s`. -/
theorem bleistein_subst {P : ℝ → ℝ} {s : ℕ} (hP : ∀ r, 0 < r → ∀ u, P (r * u) = r ^ s * P u)
    (lam a : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ w in Ioi (0 : ℝ), bleisteinWeight lam x a w * P (w - a) =
      x ^ (-(lam + s) / 2) * ∫ τ in Ioi (0 : ℝ),
        Real.exp (-(τ ^ 2 / 2) + a * √x * τ) * P (τ - a * √x) * τ ^ (lam - 1) := by
  have hr0 : 0 < √x := Real.sqrt_pos.mpr hx
  have hrx : √x ^ 2 = x := Real.sq_sqrt hx.le
  set g : ℝ → ℝ := fun τ =>
    Real.exp (-(τ ^ 2 / 2) + a * √x * τ) * P (τ - a * √x) * τ ^ (lam - 1) with hg
  have key := integral_comp_mul_left_Ioi g 0 hr0
  rw [mul_zero] at key
  have hc : √x ^ s * √x ^ (lam - 1) * √x = x ^ ((lam + s) / 2) := by
    rw [mul_comm (√x ^ s), ← Real.rpow_add_natCast hr0.ne', ← Real.rpow_add_one hr0.ne',
      Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hne : √x ^ s * √x ^ (lam - 1) ≠ 0 := by positivity
  have heq : EqOn (fun w => bleisteinWeight lam x a w * P (w - a))
      (fun w => (√x ^ s * √x ^ (lam - 1))⁻¹ * g (√x * w)) (Ioi 0) := by
    intro w hw
    have hw : (0 : ℝ) < w := hw
    simp only [hg, bleisteinWeight]
    have h1 : √x * w - a * √x = √x * (w - a) := by ring
    have h2 : -((√x * w) ^ 2 / 2) + a * √x * (√x * w) = -(x * (w ^ 2 / 2 - a * w)) := by
      conv_rhs => rw [← hrx]
      ring
    rw [h1, hP _ hr0, Real.mul_rpow hr0.le hw.le, h2]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, key, smul_eq_mul,
    ← mul_assoc, ← mul_inv, hc, ← Real.rpow_neg hx.le, neg_div]

/-- DLMF 2.3.33, the term-by-term integral behind 2.3.32:
`∫₀^∞ exp(−x(½w² − aw)) (w − a)ˢ w^{λ−1} dw = x^{−(λ+s)/2} Fₛ(a√x)`. -/
theorem dlmf_2_3_33 (lam a : ℝ) (s : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ w in Ioi (0 : ℝ), bleisteinWeight lam x a w * (w - a) ^ s =
      x ^ (-(lam + s) / 2) * bleisteinF lam s (a * √x) :=
  bleistein_subst (P := fun u => u ^ s) (fun r _ u => mul_pow r u s) lam a hx

theorem integral_bleisteinWeight_abs (lam a : ℝ) (s : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ w in Ioi (0 : ℝ), bleisteinWeight lam x a w * |w - a| ^ s =
      x ^ (-(lam + s) / 2) * bleisteinG lam s (a * √x) :=
  bleistein_subst (P := fun u => |u| ^ s)
    (fun r hr u => by rw [abs_mul, abs_of_pos hr, mul_pow]) lam a hx

theorem bleisteinG_even (lam y : ℝ) (m : ℕ) :
    bleisteinG lam (2 * m) y = bleisteinF lam (2 * m) y := by
  unfold bleisteinG bleisteinF
  congr 1
  ext τ
  rw [(even_two_mul m).pow_abs]

/-- `Fₛ(0) = 2^{(λ+s)/2 − 1} Γ((λ+s)/2)` (the Watson case `a = 0`). -/
theorem bleisteinF_zero {lam : ℝ} (hlam : 0 < lam) (s : ℕ) :
    bleisteinF lam s 0 = 2 ^ ((lam + s) / 2 - 1) * Real.Gamma ((lam + s) / 2) := by
  have hs : (0 : ℝ) ≤ s := s.cast_nonneg
  have heq : EqOn (fun τ : ℝ => Real.exp (-(τ ^ 2 / 2) + 0 * τ) * (τ - 0) ^ s * τ ^ (lam - 1))
      (fun τ => τ ^ (lam - 1 + s) * Real.exp (-(1 / 2) * τ ^ (2 : ℝ))) (Ioi 0) := by
    intro τ hτ
    have hτ : (0 : ℝ) < τ := hτ
    simp only [zero_mul, add_zero, sub_zero, Real.rpow_two]
    rw [Real.rpow_add_natCast hτ.ne']
    ring_nf
  unfold bleisteinF
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith) (by norm_num)]
  have h2 : (1 / 2 : ℝ) ^ (-(lam - 1 + s + 1) / 2) = 2 ^ ((lam + s) / 2) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [h2, show (lam - 1 + s + 1) / 2 = (lam + s) / 2 by ring, Real.rpow_sub (by norm_num),
    Real.rpow_one]
  ring

/-- DLMF 2.3.32, uniform form. Let `U(α) ⊆ (0, ∞)` be the `w`-range `(0, κ(α))` and suppose:
* `f(α, ·)` has, on `U(α)`, the Taylor remainder bound
  `‖f(α, w) − ∑_{s<n} φₛ(α)(w − a)ˢ‖ ≤ C|w − a|ⁿ` (2.3.31 truncated), uniformly in `α`;
* the coefficients `φₛ(α)`, `s < n`, are bounded;
* `w ∉ U(α)` implies `|w − a(α)| ≥ δ` (that is, `κ(α) ≥ a(α) + δ`).

Then, with `K` independent of `α` and of `x > 0`, the error after `n` terms satisfies
`‖∫_U exp(−x(½w² − aw)) f(α, w) w^{λ−1} dw − ∑_{s<n} φₛ(α) x^{−(λ+s)/2} Fₛ(a√x)‖
  ≤ K x^{−(λ+n)/2} Gₙ(a√x)`. -/
theorem dlmf_2_3_32 {A : Type*} {U : A → Set ℝ} {a : A → ℝ} {f : A → ℝ → ℂ}
    {φ : ℕ → A → ℂ} {lam δ B C : ℝ} {n : ℕ} (hlam : 0 < lam) (hδ : 0 < δ)
    (hU : ∀ α, U α ⊆ Ioi 0) (hUm : ∀ α, MeasurableSet (U α))
    (hfar : ∀ α w, 0 < w → w ∉ U α → δ ≤ |w - a α|)
    (hφ : ∀ s < n, ∀ α, ‖φ s α‖ ≤ B)
    (hT : ∀ α, ∀ w ∈ U α,
      ‖f α w - ∑ s ∈ Finset.range n, (w - a α) ^ s • φ s α‖ ≤ C * |w - a α| ^ n)
    (hint : ∀ α x, 0 < x →
      IntegrableOn (fun w => bleisteinWeight lam x (a α) w • f α w) (U α)) :
    ∃ K, ∀ α x, 0 < x →
      ‖(∫ w in U α, bleisteinWeight lam x (a α) w • f α w) -
          ∑ s ∈ Finset.range n, (x ^ (-(lam + s) / 2) * bleisteinF lam s (a α * √x)) • φ s α‖ ≤
        K * (x ^ (-(lam + n) / 2) * bleisteinG lam n (a α * √x)) := by
  set D := ∑ s ∈ Finset.range n, (δ ^ (n - s))⁻¹ with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun s _ => (inv_pos.mpr (pow_pos hδ _)).le
  set K := |C| + |B| * D with hK
  refine ⟨K, fun α x hx => ?_⟩
  set b := a α with hb
  set E := bleisteinWeight lam x b with hE
  set r : ℝ → ℂ := fun w =>
    (U α).indicator (f α) w - ∑ s ∈ Finset.range n, (w - b) ^ s • φ s α with hr
  -- the pointwise remainder bound on `(0, ∞)`
  have hrb : ∀ w, 0 < w → ‖r w‖ ≤ K * |w - b| ^ n := by
    intro w hw
    by_cases hwU : w ∈ U α
    · simp only [hr, indicator_of_mem hwU]
      calc _ ≤ C * |w - b| ^ n := hT α w hwU
        _ ≤ K * |w - b| ^ n := by
          gcongr
          rw [hK]
          nlinarith [le_abs_self C, abs_nonneg B]
    · simp only [hr, indicator_of_notMem hwU, zero_sub, norm_neg]
      have hd := hfar α w hw hwU
      calc ‖∑ s ∈ Finset.range n, (w - b) ^ s • φ s α‖
          ≤ ∑ s ∈ Finset.range n, ‖(w - b) ^ s • φ s α‖ := norm_sum_le _ _
        _ ≤ ∑ s ∈ Finset.range n, |B| * ((δ ^ (n - s))⁻¹ * |w - b| ^ n) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hsn : s < n := Finset.mem_range.mp hs
          rw [norm_smul, Real.norm_eq_abs, abs_pow]
          have h1 : |w - b| ^ s ≤ (δ ^ (n - s))⁻¹ * |w - b| ^ n := by
            rw [le_inv_mul_iff₀ (pow_pos hδ _), ← pow_sub_mul_pow |w - b| hsn.le]
            gcongr
          calc |w - b| ^ s * ‖φ s α‖ ≤ ((δ ^ (n - s))⁻¹ * |w - b| ^ n) * |B| := by
                gcongr
                exact (hφ s hsn α).trans (le_abs_self B)
            _ = _ := by ring
        _ = |B| * D * |w - b| ^ n := by rw [← Finset.mul_sum, ← Finset.sum_mul, hD]; ring
        _ ≤ K * |w - b| ^ n := by
          gcongr
          rw [hK]
          linarith [abs_nonneg C]
  -- integrability
  have hIf : Integrable (fun w => E w • (U α).indicator (f α) w) (volume.restrict (Ioi 0)) := by
    have h := ((hint α x hx).integrable_indicator (hUm α)).restrict (s := Ioi 0)
    refine h.congr (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ U α
    · simp [indicator_of_mem hw, hE, hb]
    · simp [indicator_of_notMem hw]
  have hIs : ∀ s, Integrable (fun w => E w • ((w - b) ^ s • φ s α))
      (volume.restrict (Ioi 0)) := by
    intro s
    refine ((integrableOn_bleisteinWeight_pow hlam hx b s).smul_const (φ s α)).congr
      (Eventually.of_forall fun w => ?_)
    simp only [hE, smul_smul]
  -- the remainder integral
  have main : ∫ w in Ioi (0 : ℝ), E w • r w =
      (∫ w in U α, E w • f α w) -
        ∑ s ∈ Finset.range n, (x ^ (-(lam + s) / 2) * bleisteinF lam s (b * √x)) • φ s α := by
    simp only [hr, smul_sub, Finset.smul_sum]
    rw [integral_sub hIf (integrable_finsetSum _ fun s _ => hIs s),
      integral_finsetSum _ fun s _ => hIs s]
    congr 1
    · have h1 : ∫ w in U α, E w • f α w =
          ∫ w in Ioi (0 : ℝ), (U α).indicator (fun w => E w • f α w) w := by
        rw [setIntegral_indicator (hUm α), inter_eq_right.mpr (hU α)]
      rw [h1]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      by_cases hw : w ∈ U α
      · simp [indicator_of_mem hw]
      · simp [indicator_of_notMem hw]
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp only [smul_smul]
      rw [integral_smul_const, hE, dlmf_2_3_33 lam b s hx]
  rw [← main]
  have hg := (integrableOn_bleisteinWeight_abs hlam hx b n).const_mul K
  calc ‖∫ w in Ioi (0 : ℝ), E w • r w‖
      ≤ ∫ w in Ioi (0 : ℝ), K * (bleisteinWeight lam x b w * |w - b| ^ n) := by
        refine norm_integral_le_of_norm_le hg ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun w hw => ?_))
        have hw : (0 : ℝ) < w := hw
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bleisteinWeight_nonneg hw.le)]
        calc E w * ‖r w‖ ≤ E w * (K * |w - b| ^ n) :=
              mul_le_mul_of_nonneg_left (hrb w hw) (bleisteinWeight_nonneg hw.le)
          _ = _ := by rw [hE]; ring
    _ = K * (x ^ (-(lam + n) / 2) * bleisteinG lam n (b * √x)) := by
        rw [integral_const_mul, integral_bleisteinWeight_abs lam b n hx]

/-- DLMF 2.3.32 for an even number `n = 2m` of terms: the error is bounded by the function of the
next term itself, `K x^{−(λ+n)/2} Fₙ(a√x)`. -/
theorem dlmf_2_3_32_even {A : Type*} {U : A → Set ℝ} {a : A → ℝ} {f : A → ℝ → ℂ}
    {φ : ℕ → A → ℂ} {lam δ B C : ℝ} {m : ℕ} (hlam : 0 < lam) (hδ : 0 < δ)
    (hU : ∀ α, U α ⊆ Ioi 0) (hUm : ∀ α, MeasurableSet (U α))
    (hfar : ∀ α w, 0 < w → w ∉ U α → δ ≤ |w - a α|)
    (hφ : ∀ s < 2 * m, ∀ α, ‖φ s α‖ ≤ B)
    (hT : ∀ α, ∀ w ∈ U α,
      ‖f α w - ∑ s ∈ Finset.range (2 * m), (w - a α) ^ s • φ s α‖ ≤ C * |w - a α| ^ (2 * m))
    (hint : ∀ α x, 0 < x →
      IntegrableOn (fun w => bleisteinWeight lam x (a α) w • f α w) (U α)) :
    ∃ K, ∀ α x, 0 < x →
      ‖(∫ w in U α, bleisteinWeight lam x (a α) w • f α w) -
          ∑ s ∈ Finset.range (2 * m),
            (x ^ (-(lam + s) / 2) * bleisteinF lam s (a α * √x)) • φ s α‖ ≤
        K * (x ^ (-(lam + (2 * m : ℕ)) / 2) * bleisteinF lam (2 * m) (a α * √x)) := by
  obtain ⟨K, hK⟩ := dlmf_2_3_32 hlam hδ hU hUm hfar hφ hT hint
  exact ⟨K, fun α x hx => by simpa only [bleisteinG_even] using hK α x hx⟩

end Azurite.DLMF
