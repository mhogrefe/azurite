/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# DLMF §4.13: the Lambert `W`-function on the real line

Formalizations of the real-variable part of <https://dlmf.nist.gov/4.13>.

* `lambertW0` (`W₀`, the principal branch, `Wp`) on `[−e⁻¹, ∞)` and `lambertWm1`
  (`W_{±1}(x ∓ 0i)`, `Wm`) on `[−e⁻¹, 0)`, the two real inverses of `x eˣ`.
* 4.13.1 and the count of real solutions: one on `[0, ∞)` (nonnegative, increasing), two on
  `(−e⁻¹, 0)` (one increasing, one decreasing), none below `−e⁻¹` (`dlmf_4_13_1_*`).
* 4.13.2 (special values), 4.13.3_1–4.13.3_2, the real Wright `ω` (4.13.1_2) and the tree
  function `T` (4.13.1_3).
* 4.13.4 (derivative), 4.13.4_1–4.13.4_2 (higher derivatives and the polynomials `pₙ`, of degree
  exactly `n`).
* 4.13.12–4.13.14 (antiderivatives) on the real line.
-/

open Set Filter Topology Real Polynomial
open scoped Nat

namespace Azurite.DLMF

/-! ### The function `x eˣ` -/

theorem hasDerivAt_mul_exp (x : ℝ) : HasDerivAt (fun x => x * exp x) ((1 + x) * exp x) x := by
  have h : HasDerivAt (fun x => x * exp x) (1 * exp x + x * exp x) x :=
    (hasDerivAt_id' x).mul (hasDerivAt_exp x)
  exact h.congr_deriv (by ring)

theorem strictMonoOn_mul_exp : StrictMonoOn (fun x => x * exp x) (Ici (-1)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _)
    (continuous_id.mul continuous_exp).continuousOn fun x hx => ?_
  rw [interior_Ici, mem_Ioi] at hx
  rw [(hasDerivAt_mul_exp x).deriv]
  exact mul_pos (by linarith) (exp_pos x)

theorem strictAntiOn_mul_exp : StrictAntiOn (fun x => x * exp x) (Iic (-1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Iic _)
    (continuous_id.mul continuous_exp).continuousOn fun x hx => ?_
  rw [interior_Iic, mem_Iio] at hx
  rw [(hasDerivAt_mul_exp x).deriv]
  exact mul_neg_of_neg_of_pos (by linarith) (exp_pos x)

theorem neg_one_mul_exp : (-1 : ℝ) * exp (-1) = -exp (-1) := by ring

/-- `x eˣ ≥ −e⁻¹`, with equality only at `x = −1`. -/
theorem neg_exp_neg_one_le_mul_exp (x : ℝ) : -exp (-1) ≤ x * exp x := by
  rcases le_total (-1) x with h | h
  · rw [← neg_one_mul_exp]; exact strictMonoOn_mul_exp.monotoneOn (mem_Ici.mpr le_rfl) h h
  · rw [← neg_one_mul_exp]; exact strictAntiOn_mul_exp.antitoneOn h (mem_Iic.mpr le_rfl) h

theorem neg_exp_neg_one_lt_mul_exp {x : ℝ} (hx : x ≠ -1) : -exp (-1) < x * exp x := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [← neg_one_mul_exp]; exact strictAntiOn_mul_exp (mem_Iic.mpr h.le) (mem_Iic.mpr le_rfl) h
  · rw [← neg_one_mul_exp]; exact strictMonoOn_mul_exp (mem_Ici.mpr le_rfl) (mem_Ici.mpr h.le) h

theorem tendsto_mul_exp_atBot : Tendsto (fun x => x * exp x) atBot (𝓝 0) := by
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).neg.comp tendsto_neg_atBot_atTop
  simp only [neg_zero] at h
  refine h.congr fun x => ?_
  simp

/-! ### The real branches -/

theorem exists_lambertW0 {y : ℝ} (hy : -exp (-1) ≤ y) : ∃ x, -1 ≤ x ∧ x * exp x = y := by
  set M := max y 0 + 1
  have hM : y ≤ M * exp M := by
    have h1 : 1 ≤ exp M := one_le_exp (by positivity)
    have h2 : 0 ≤ M := by positivity
    nlinarith [le_max_left y 0]
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc (by linarith [le_max_right y 0] : (-1 : ℝ) ≤ M)
    (by fun_prop : Continuous fun x : ℝ => x * exp x).continuousOn
    ⟨by show (-1 : ℝ) * exp (-1) ≤ y; rw [neg_one_mul_exp]; exact hy, hM⟩
  exact ⟨x, hx.1, hxy⟩

theorem exists_lambertWm1 {y : ℝ} (hy : -exp (-1) ≤ y) (hy0 : y < 0) :
    ∃ x, x ≤ -1 ∧ x * exp x = y := by
  obtain ⟨b, hb⟩ := ((tendsto_mul_exp_atBot.eventually (Ioi_mem_nhds hy0)).and
    (eventually_le_atBot (-1))).exists
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc' hb.2
    (by fun_prop : Continuous fun x : ℝ => x * exp x).continuousOn
    ⟨by show (-1 : ℝ) * exp (-1) ≤ y; rw [neg_one_mul_exp]; exact hy, le_of_lt hb.1⟩
  exact ⟨x, hx.2, hxy⟩

/-- **DLMF §4.13**: the principal branch `W₀(x)` (`x ≥ −e⁻¹`): the solution `≥ −1` of `W e^W = x`.
(Junk value `−1` below `−e⁻¹`.) -/
noncomputable def lambertW0 (y : ℝ) : ℝ :=
  if h : -exp (-1) ≤ y then (exists_lambertW0 h).choose else -1

/-- **DLMF §4.13**: the real branch `W_{±1}(x ∓ 0i)` (`Wm(x)`, `−e⁻¹ ≤ x < 0`): the solution
`≤ −1` of `W e^W = x`. (Junk value `−1` elsewhere.) -/
noncomputable def lambertWm1 (y : ℝ) : ℝ :=
  if h : -exp (-1) ≤ y ∧ y < 0 then (exists_lambertWm1 h.1 h.2).choose else -1

theorem lambertW0_spec {y : ℝ} (hy : -exp (-1) ≤ y) :
    -1 ≤ lambertW0 y ∧ lambertW0 y * exp (lambertW0 y) = y := by
  simp only [lambertW0, hy, ↓reduceDIte]; exact (exists_lambertW0 hy).choose_spec

theorem lambertWm1_spec {y : ℝ} (hy : -exp (-1) ≤ y) (hy0 : y < 0) :
    lambertWm1 y ≤ -1 ∧ lambertWm1 y * exp (lambertWm1 y) = y := by
  simp only [lambertWm1, hy, hy0, and_self, ↓reduceDIte]
  exact (exists_lambertWm1 hy hy0).choose_spec

/-- **DLMF 4.13.3_1**: `W₀(x eˣ) = x` for `−1 ≤ x`. -/
theorem dlmf_4_13_3_1 {x : ℝ} (hx : -1 ≤ x) : lambertW0 (x * exp x) = x := by
  obtain ⟨h1, h2⟩ := lambertW0_spec (neg_exp_neg_one_le_mul_exp x)
  exact strictMonoOn_mul_exp.injOn h1 hx h2

/-- **DLMF 4.13.3_2**: `W_{±1}(x eˣ ∓ 0i) = x` for `x < −1`. -/
theorem dlmf_4_13_3_2 {x : ℝ} (hx : x < -1) : lambertWm1 (x * exp x) = x := by
  have h0 : x * exp x < 0 := mul_neg_of_neg_of_pos (by linarith) (exp_pos x)
  obtain ⟨h1, h2⟩ := lambertWm1_spec (neg_exp_neg_one_le_mul_exp x) h0
  exact strictAntiOn_mul_exp.injOn h1 hx.le h2

/-- **DLMF 4.13.1**: `W e^W = x`, both real branches. -/
theorem dlmf_4_13_1_real {y : ℝ} (hy : -exp (-1) ≤ y) :
    lambertW0 y * exp (lambertW0 y) = y ∧ (y < 0 → lambertWm1 y * exp (lambertWm1 y) = y) :=
  ⟨(lambertW0_spec hy).2, fun h => (lambertWm1_spec hy h).2⟩

/-- **DLMF §4.13**: below `−e⁻¹` there is no real solution. -/
theorem dlmf_4_13_1_none {y : ℝ} (hy : y < -exp (-1)) (x : ℝ) : x * exp x ≠ y := fun h => by
  linarith [neg_exp_neg_one_le_mul_exp x]

/-- **DLMF §4.13**: on `[0, ∞)` there is one real solution, and it is nonnegative. -/
theorem dlmf_4_13_1_nonneg {y : ℝ} (hy : 0 ≤ y) :
    {x : ℝ | x * exp x = y} = {lambertW0 y} ∧ 0 ≤ lambertW0 y := by
  have hy' : -exp (-1) ≤ y := by linarith [exp_pos (-1)]
  obtain ⟨h1, h2⟩ := lambertW0_spec hy'
  have hnn : 0 ≤ lambertW0 y := by
    by_contra h; push Not at h
    have : lambertW0 y * exp (lambertW0 y) < 0 := mul_neg_of_neg_of_pos h (exp_pos _)
    linarith
  refine ⟨Set.ext fun x => ⟨fun hx => ?_, fun hx => by rw [mem_singleton_iff.mp hx]; exact h2⟩,
    hnn⟩
  have hx' : 0 ≤ x := by
    by_contra h; push Not at h
    have : x * exp x < 0 := mul_neg_of_neg_of_pos h (exp_pos _)
    have hx2 : x * exp x = y := hx
    linarith
  exact strictMonoOn_mul_exp.injOn (by linarith : (-1 : ℝ) ≤ x) h1 (hx.trans h2.symm)

/-- **DLMF §4.13**: on `(−e⁻¹, 0)` there are exactly two real solutions, `W₀ > −1 > W₋₁`. -/
theorem dlmf_4_13_1_two {y : ℝ} (hy : -exp (-1) < y) (hy0 : y < 0) :
    {x : ℝ | x * exp x = y} = {lambertW0 y, lambertWm1 y} ∧
      lambertWm1 y < -1 ∧ -1 < lambertW0 y := by
  obtain ⟨a1, a2⟩ := lambertW0_spec hy.le
  obtain ⟨b1, b2⟩ := lambertWm1_spec hy.le hy0
  have ha : lambertW0 y ≠ -1 := fun h => by rw [h, neg_one_mul_exp] at a2; linarith
  have hb : lambertWm1 y ≠ -1 := fun h => by rw [h, neg_one_mul_exp] at b2; linarith
  refine ⟨Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩, lt_of_le_of_ne b1 hb,
    lt_of_le_of_ne a1 (Ne.symm ha)⟩
  · rcases le_total (-1) x with h | h
    · exact Or.inl (strictMonoOn_mul_exp.injOn h a1 (hx.trans a2.symm))
    · exact Or.inr (strictAntiOn_mul_exp.injOn h b1 (hx.trans b2.symm))
  · rcases hx with rfl | hx
    · exact a2
    · rw [mem_singleton_iff.mp hx]; exact b2

/-- **DLMF §4.13**: `W₀` is increasing on `[−e⁻¹, ∞)`. -/
theorem strictMonoOn_lambertW0 : StrictMonoOn lambertW0 (Ici (-exp (-1))) := by
  intro a ha b hb hab
  obtain ⟨a1, a2⟩ := lambertW0_spec ha
  obtain ⟨b1, b2⟩ := lambertW0_spec hb
  by_contra h; push Not at h
  have := strictMonoOn_mul_exp.monotoneOn b1 a1 h
  rw [a2, b2] at this; linarith

/-- **DLMF §4.13**: `W_{±1}(x ∓ 0i)` is decreasing on `[−e⁻¹, 0)`. -/
theorem strictAntiOn_lambertWm1 : StrictAntiOn lambertWm1 (Ico (-exp (-1)) 0) := by
  intro a ha b hb hab
  obtain ⟨a1, a2⟩ := lambertWm1_spec ha.1 ha.2
  obtain ⟨b1, b2⟩ := lambertWm1_spec hb.1 hb.2
  by_contra h; push Not at h
  have := strictAntiOn_mul_exp.antitoneOn a1 b1 h
  rw [a2, b2] at this; linarith

/-! ### 4.13.2: special values -/

theorem lambertW0_neg_exp_neg_one : lambertW0 (-exp (-1)) = -1 := by
  rw [← neg_one_mul_exp]; exact dlmf_4_13_3_1 le_rfl

theorem lambertWm1_neg_exp_neg_one : lambertWm1 (-exp (-1)) = -1 := by
  have h := lambertWm1_spec le_rfl (by linarith [exp_pos (-1)])
  by_contra hne
  have := neg_exp_neg_one_lt_mul_exp hne
  rw [h.2] at this; exact lt_irrefl _ this

theorem lambertW0_zero : lambertW0 0 = 0 := by
  have := dlmf_4_13_3_1 (x := 0) (by norm_num); simpa using this

theorem lambertW0_exp_one : lambertW0 (exp 1) = 1 := by
  have := dlmf_4_13_3_1 (x := 1) (by norm_num); simpa using this

/-- **DLMF 4.13.2** (real form): `W₀(−e⁻¹) = W_{±1}(−e⁻¹ ∓ 0i) = −1`, `W₀(0) = 0`,
`W₀(e) = 1`. -/
theorem dlmf_4_13_2_real :
    lambertW0 (-exp (-1)) = -1 ∧ lambertWm1 (-exp (-1)) = -1 ∧ lambertW0 0 = 0 ∧
      lambertW0 (exp 1) = 1 :=
  ⟨lambertW0_neg_exp_neg_one, lambertWm1_neg_exp_neg_one, lambertW0_zero, lambertW0_exp_one⟩

/-! ### The Wright `ω` and tree `T` functions (real arguments) -/

/-- The Wright `ω`-function on the real line, `ω(x) = W₀(eˣ)`. -/
noncomputable def wrightOmegaReal (x : ℝ) : ℝ := lambertW0 (exp x)

theorem wrightOmegaReal_pos (x : ℝ) : 0 < wrightOmegaReal x := by
  have h := lambertW0_spec (y := exp x) (by linarith [exp_pos x, exp_pos (-1)])
  by_contra hn; push Not at hn
  have : wrightOmegaReal x * exp (wrightOmegaReal x) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hn (exp_pos _).le
  rw [wrightOmegaReal, h.2] at this; linarith [exp_pos x]

/-- **DLMF 4.13.1_2** (real `z`): `ω(x) + ln ω(x) = x`. -/
theorem dlmf_4_13_1_2_real (x : ℝ) : wrightOmegaReal x + Real.log (wrightOmegaReal x) = x := by
  have h := (lambertW0_spec (y := exp x) (by linarith [exp_pos x, exp_pos (-1)])).2
  have hp := wrightOmegaReal_pos x
  have := congrArg Real.log h
  simp only [wrightOmegaReal] at this hp ⊢
  rw [Real.log_mul hp.ne' (exp_pos _).ne', Real.log_exp, Real.log_exp] at this
  linarith

/-- The tree function `T(x) = −W₀(−x)` (`x ≤ e⁻¹`). -/
noncomputable def treeT (x : ℝ) : ℝ := -lambertW0 (-x)

/-- **DLMF 4.13.1_3**: `T e^{−T} = x`. -/
theorem dlmf_4_13_1_3 {x : ℝ} (hx : x ≤ exp (-1)) : treeT x * exp (-treeT x) = x := by
  have := (lambertW0_spec (y := -x) (by linarith)).2
  simp only [treeT, neg_neg]
  linarith

/-! ### 4.13.4: derivatives -/

theorem lambertW0_gt {y : ℝ} (hy : -exp (-1) < y) : -1 < lambertW0 y := by
  obtain ⟨h1, h2⟩ := lambertW0_spec hy.le
  rcases h1.lt_or_eq with h | h
  · exact h
  · rw [← h, neg_one_mul_exp] at h2; linarith

theorem continuousAt_lambertW0 {y : ℝ} (hy : -exp (-1) < y) : ContinuousAt lambertW0 y := by
  refine continuousAt_of_monotoneOn_of_image_mem_nhds
    (strictMonoOn_lambertW0.monotoneOn.mono Ioi_subset_Ici_self) (Ioi_mem_nhds hy) ?_
  have himg : lambertW0 '' Ioi (-exp (-1)) = Ioi (-1) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; exact lambertW0_gt hy
    · intro hx
      exact ⟨x * exp x, neg_exp_neg_one_lt_mul_exp (ne_of_gt hx), dlmf_4_13_3_1 hx.le⟩
  rw [himg]; exact Ioi_mem_nhds (lambertW0_gt hy)

/-- **DLMF 4.13.4** (`W₀`): `dW/dz = e^{−W}/(1 + W)`. -/
theorem dlmf_4_13_4_W0 {y : ℝ} (hy : -exp (-1) < y) :
    HasDerivAt lambertW0 (exp (-lambertW0 y) / (1 + lambertW0 y)) y := by
  have hW := lambertW0_gt hy
  have h := (hasDerivAt_mul_exp (lambertW0 y)).of_local_left_inverse (continuousAt_lambertW0 hy)
    (mul_ne_zero (by linarith) (exp_pos _).ne')
    (eventually_of_mem (Ioi_mem_nhds hy) fun z hz => (lambertW0_spec (le_of_lt hz)).2)
  refine h.congr_deriv ?_
  rw [exp_neg]; field_simp

/-- **DLMF 4.13.4** (second form): `dW/dz = W/(z(1 + W))` for `z ≠ 0`. -/
theorem dlmf_4_13_4_W0' {y : ℝ} (hy : -exp (-1) < y) (hy0 : y ≠ 0) :
    HasDerivAt lambertW0 (lambertW0 y / (y * (1 + lambertW0 y))) y := by
  refine (dlmf_4_13_4_W0 hy).congr_deriv ?_
  have h2 := (lambertW0_spec hy.le).2
  have hW := lambertW0_gt hy
  have h1 : 1 + lambertW0 y ≠ 0 := by linarith
  have hW0 : lambertW0 y ≠ 0 := fun h => hy0 (by rw [← h2, h]; simp)
  generalize lambertW0 y = W at h2 hW h1 hW0 ⊢
  subst h2
  rw [exp_neg]; field_simp

theorem lambertWm1_lt {y : ℝ} (hy : -exp (-1) < y) (hy0 : y < 0) : lambertWm1 y < -1 :=
  (dlmf_4_13_1_two hy hy0).2.1

theorem continuousAt_lambertWm1 {y : ℝ} (hy : -exp (-1) < y) (hy0 : y < 0) :
    ContinuousAt lambertWm1 y := by
  have hanti : AntitoneOn lambertWm1 (Ioo (-exp (-1)) 0) :=
    strictAntiOn_lambertWm1.antitoneOn.mono fun x hx => ⟨hx.1.le, hx.2⟩
  have hneg : ContinuousAt (fun y => -lambertWm1 y) y := by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := Ioo (-exp (-1)) 0)
      (fun a ha b hb hab => neg_le_neg (hanti ha hb hab)) (Ioo_mem_nhds hy hy0) ?_
    have himg : (fun y => -lambertWm1 y) '' Ioo (-exp (-1)) 0 = Ioi 1 := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; simp only [mem_Ioi]; linarith [lambertWm1_lt hy.1 hy.2]
      · intro hx
        have hx' : -x < -1 := by linarith [mem_Ioi.mp hx]
        refine ⟨-x * exp (-x), ⟨neg_exp_neg_one_lt_mul_exp (by linarith),
          mul_neg_of_neg_of_pos (by linarith) (exp_pos _)⟩, ?_⟩
        simp only; rw [dlmf_4_13_3_2 hx']; ring
    rw [himg]; exact Ioi_mem_nhds (by linarith [lambertWm1_lt hy hy0])
  convert hneg.neg using 1; funext z; simp

/-- **DLMF 4.13.4** (`W_{±1}(x ∓ 0i)`): `dW/dz = e^{−W}/(1 + W)` on `(−e⁻¹, 0)`. -/
theorem dlmf_4_13_4_Wm1 {y : ℝ} (hy : -exp (-1) < y) (hy0 : y < 0) :
    HasDerivAt lambertWm1 (exp (-lambertWm1 y) / (1 + lambertWm1 y)) y := by
  have hW := lambertWm1_lt hy hy0
  have h := (hasDerivAt_mul_exp (lambertWm1 y)).of_local_left_inverse
    (continuousAt_lambertWm1 hy hy0) (mul_ne_zero (by linarith) (exp_pos _).ne')
    (eventually_of_mem (Ioo_mem_nhds hy hy0) fun z hz => (lambertWm1_spec hz.1.le hz.2).2)
  refine h.congr_deriv ?_
  have : 1 + lambertWm1 y ≠ 0 := by linarith
  rw [exp_neg]; field_simp

/-! ### 4.13.4_1–4.13.4_2: higher derivatives -/

/-- **DLMF 4.13.4_2**: `p₀ = 1`, `pₙ = (1 + x) p′ₙ₋₁ + (1 − n(x + 3)) pₙ₋₁`. -/
noncomputable def lambertP : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * derivative (lambertP n) + (1 - ((n + 1 : ℕ) : ℝ[X]) * (X + 3)) * lambertP n

/-- `pₙ` has degree exactly `n` (leading coefficient `(−1)ⁿ n!`). -/
theorem lambertP_degree (n : ℕ) :
    (lambertP n).natDegree = n ∧ (lambertP n).leadingCoeff = (-1) ^ n * n ! := by
  induction n with
  | zero => simp [lambertP]
  | succ n ih =>
    obtain ⟨hd, hl⟩ := ih
    have hne : lambertP n ≠ 0 := by
      intro h; rw [h, leadingCoeff_zero] at hl
      exact (mul_ne_zero (pow_ne_zero n (by norm_num)) (by exact_mod_cast n.factorial_ne_zero))
        hl.symm
    have hq : (1 - ((n + 1 : ℕ) : ℝ[X]) * (X + 3)) = C (-((n + 1 : ℕ) : ℝ)) * X +
        C (1 - 3 * ((n + 1 : ℕ) : ℝ)) := by
      simp only [map_neg, map_sub, map_mul, map_natCast, map_one, map_ofNat]; ring
    have hc : (-((n + 1 : ℕ) : ℝ)) ≠ 0 := neg_ne_zero.mpr (by positivity)
    have hqd : (C (-((n + 1 : ℕ) : ℝ)) * X + C (1 - 3 * ((n + 1 : ℕ) : ℝ))).natDegree = 1 :=
      natDegree_linear hc
    have hql : (C (-((n + 1 : ℕ) : ℝ)) * X + C (1 - 3 * ((n + 1 : ℕ) : ℝ))).leadingCoeff =
        -((n + 1 : ℕ) : ℝ) := leadingCoeff_linear hc
    have hqne : (C (-((n + 1 : ℕ) : ℝ)) * X + C (1 - 3 * ((n + 1 : ℕ) : ℝ))) ≠ 0 := by
      intro h; rw [h, leadingCoeff_zero] at hql; exact hc hql.symm
    have h2d : ((1 - ((n + 1 : ℕ) : ℝ[X]) * (X + 3)) * lambertP n).natDegree = n + 1 := by
      rw [hq, natDegree_mul hqne hne, hqd, hd]; ring
    have h2l : ((1 - ((n + 1 : ℕ) : ℝ[X]) * (X + 3)) * lambertP n).leadingCoeff =
        -((n + 1 : ℕ) : ℝ) * ((-1) ^ n * n !) := by
      rw [hq, leadingCoeff_mul, hql, hl]
    have h1d : ((1 + X) * derivative (lambertP n)).natDegree < n + 1 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [derivative_of_natDegree_zero hd, mul_zero, natDegree_zero]; omega
      · calc ((1 + X) * derivative (lambertP n)).natDegree
            ≤ (1 + X : ℝ[X]).natDegree + (derivative (lambertP n)).natDegree := natDegree_mul_le
          _ ≤ 1 + (n - 1) := by
              gcongr
              · rw [add_comm]; exact (natDegree_X_add_C 1).le
              · exact (natDegree_derivative_le _).trans (by rw [hd])
          _ < n + 1 := by omega
    have hdeg : ((1 + X) * derivative (lambertP n)).degree <
        ((1 - ((n + 1 : ℕ) : ℝ[X]) * (X + 3)) * lambertP n).degree := by
      have h2ne : ((1 - ((n + 1 : ℕ) : ℝ[X]) * (X + 3)) * lambertP n) ≠ 0 := by
        rw [hq]; exact mul_ne_zero hqne hne
      rw [degree_eq_natDegree h2ne, h2d]
      exact (degree_le_natDegree).trans_lt (by exact_mod_cast h1d)
    show (((1 + X) * derivative (lambertP n)) +
      (1 - ((n + 1 : ℕ) : ℝ[X]) * (X + 3)) * lambertP n).natDegree = n + 1 ∧
      (((1 + X) * derivative (lambertP n)) +
      (1 - ((n + 1 : ℕ) : ℝ[X]) * (X + 3)) * lambertP n).leadingCoeff =
        (-1 : ℝ) ^ (n + 1) * ((n + 1)! : ℝ)
    rw [natDegree_add_eq_right_of_degree_lt hdeg, leadingCoeff_add_of_degree_lt hdeg, h2d, h2l]
    refine ⟨rfl, ?_⟩
    push_cast [Nat.factorial_succ]; ring

theorem lambertP_succ_eval (n : ℕ) (w : ℝ) : (lambertP (n + 1)).eval w =
    (1 + w) * (derivative (lambertP n)).eval w + (1 - (n + 1) * (w + 3)) * (lambertP n).eval w := by
  simp only [lambertP, eval_add, eval_mul, eval_sub, eval_one, eval_X, eval_natCast, eval_ofNat]
  push_cast; ring

/-- **DLMF 4.13.4_1**: `dⁿW/dzⁿ = e^{−nW} p_{n−1}(W)/(1 + W)^{2n−1}` (`W = W₀`, `z > −e⁻¹`). -/
theorem dlmf_4_13_4_1 (n : ℕ) {y : ℝ} (hy : -exp (-1) < y) :
    iteratedDeriv (n + 1) lambertW0 y = exp (-((n + 1 : ℕ) : ℝ) * lambertW0 y) *
      (lambertP n).eval (lambertW0 y) / (1 + lambertW0 y) ^ (2 * n + 1) := by
  induction n generalizing y with
  | zero =>
    rw [iteratedDeriv_one, (dlmf_4_13_4_W0 hy).deriv]
    simp [lambertP]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv (n + 1) lambertW0 =ᶠ[𝓝 y] fun z =>
        exp (-((n + 1 : ℕ) : ℝ) * lambertW0 z) * (lambertP n).eval (lambertW0 z) /
          (1 + lambertW0 z) ^ (2 * n + 1) :=
      eventually_of_mem (Ioi_mem_nhds hy) fun z hz => ih hz
    rw [heq.deriv_eq]
    have hW := dlmf_4_13_4_W0 hy
    have hw1 : 1 + lambertW0 y ≠ 0 := by have := lambertW0_gt hy; linarith
    have h1 := (hW.const_mul (-((n + 1 : ℕ) : ℝ))).exp
    have h2 := ((lambertP n).hasDerivAt (lambertW0 y)).comp y hW
    have h3 := (hW.const_add 1).pow (2 * n + 1)
    have h : HasDerivAt (fun z => exp (-((n + 1 : ℕ) : ℝ) * lambertW0 z) *
        (lambertP n).eval (lambertW0 z) / (1 + lambertW0 z) ^ (2 * n + 1)) _ y :=
      (h1.mul h2).div h3 (pow_ne_zero _ hw1)
    rw [h.deriv, lambertP_succ_eval]
    simp only [Pi.mul_apply, Function.comp_apply]
    have he : exp (-((n + 1 + 1 : ℕ) : ℝ) * lambertW0 y) =
        exp (-((n + 1 : ℕ) : ℝ) * lambertW0 y) * exp (-lambertW0 y) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [he, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, show 2 * n + 1 - 1 = 2 * n by omega]
    generalize exp (-((n + 1 : ℕ) : ℝ) * lambertW0 y) = E1
    generalize exp (-lambertW0 y) = E2
    generalize lambertW0 y = w at hw1 ⊢
    field_simp
    push_cast
    ring

/-! ### 4.13.12–4.13.14: antiderivatives -/

theorem lambertW0_ne_zero {y : ℝ} (hy : -exp (-1) ≤ y) (hy0 : y ≠ 0) : lambertW0 y ≠ 0 :=
  fun h => hy0 (by rw [← (lambertW0_spec hy).2, h]; simp)

/-- **DLMF 4.13.12**: `∫ W dz = z/W + zW − z`. -/
theorem dlmf_4_13_12 {y : ℝ} (hy : -exp (-1) < y) (hy0 : y ≠ 0) :
    HasDerivAt (fun y => y / lambertW0 y + y * lambertW0 y - y) (lambertW0 y) y := by
  have hW := dlmf_4_13_4_W0' hy hy0
  have hw0 := lambertW0_ne_zero hy.le hy0
  have hw1 : 1 + lambertW0 y ≠ 0 := by have := lambertW0_gt hy; linarith
  have h : HasDerivAt (fun y => y / lambertW0 y + y * lambertW0 y - y) _ y :=
    (((hasDerivAt_id' y).div hW hw0).add ((hasDerivAt_id' y).mul hW)).sub (hasDerivAt_id' y)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **DLMF 4.13.13**: `∫ W/z dz = W²/2 + W`. -/
theorem dlmf_4_13_13 {y : ℝ} (hy : -exp (-1) < y) (hy0 : y ≠ 0) :
    HasDerivAt (fun y => lambertW0 y ^ 2 / 2 + lambertW0 y) (lambertW0 y / y) y := by
  have hW := dlmf_4_13_4_W0' hy hy0
  have hw1 : 1 + lambertW0 y ≠ 0 := by have := lambertW0_gt hy; linarith
  have h : HasDerivAt (fun y => lambertW0 y ^ 2 / 2 + lambertW0 y) _ y :=
    ((hW.pow 2).div_const 2).add hW
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **DLMF 4.13.14**: `2∫ sin W dz = z(1 + 1/W) sin W − z cos W`. -/
theorem dlmf_4_13_14 {y : ℝ} (hy : -exp (-1) < y) (hy0 : y ≠ 0) :
    HasDerivAt (fun y => y * (1 + 1 / lambertW0 y) * sin (lambertW0 y) - y * cos (lambertW0 y))
      (2 * sin (lambertW0 y)) y := by
  have hW := dlmf_4_13_4_W0' hy hy0
  have hw0 := lambertW0_ne_zero hy.le hy0
  have hw1 : 1 + lambertW0 y ≠ 0 := by have := lambertW0_gt hy; linarith
  have h : HasDerivAt (fun y => y * (1 + 1 / lambertW0 y) * sin (lambertW0 y) -
      y * cos (lambertW0 y)) _ y :=
    (((hasDerivAt_id' y).mul ((hasDerivAt_const y (1 : ℝ)).add
      ((hasDerivAt_const y (1 : ℝ)).div hW hw0))).mul hW.sin).sub ((hasDerivAt_id' y).mul hW.cos)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply]
  field_simp
  ring

end Azurite.DLMF
