/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section4
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DLMF §1.4(v): Olver's exercises on the variation

The remaining parts of Olver (1997b) §11 cited by DLMF §1.4(v) (see `Section4.lean` for §11.2–11.5
on the real line and Ex. 11.1, 11.2 (ii)–(iii)).

* Olver §11.5, the variation along a path `𝒫` (a finite chain of arcs `z = γⱼ(τ)`) of a holomorphic
  `f`: `pathVariation` (`𝒱_𝒫(f) = ∑ⱼ ∫ |f′(zⱼ(τ)) zⱼ′(τ)| dτ`).
* Ex. 11.4: `olver_ex_11_4` (`𝒱_𝒫(f) = sup ∑ₛ |f(zₛ₊₁) − f(zₛ)|` over points of `𝒫` arranged in
  order, i.e. the total variation of `f ∘ Γ`; only `zⱼ′` continuous is needed).
* Ex. 11.3: `𝒱_{−1,1}(e^{iz})` along the join of `−1` and `1` (`olver_ex_11_3_i`, `= 2`), around
  the other three sides of the square `−1, 1, 1 + 2i, −1 + 2i` (`olver_ex_11_3_ii`, `= 2`), and
  around the conjugate path (`olver_ex_11_3_iii`, `= 4e² − 2`); `sqArc`, `sqPath`,
  `eVariationOn_sqPath`.
* Ex. 11.2 (i): `olver_ex_11_2_i` (`𝒱_{0,1}{sin²(nπx)} = 2|n|`, subdividing at `x = j/(2|n|)`);
  (iv): `olver_ex_11_2_iv` (`𝒱_{x=0,∞}{∫₀ˣ (t − 1)e^{−t} dt} = 2/e`).
-/

open Set Filter Topology MeasureTheory Finset Complex
open scoped ENNReal Real

namespace Azurite.DLMF

/-! ### Variation along a path (Olver §11.5, Ex. 11.4) -/

/-- **Olver §11.5**: the variation `𝒱_𝒫(f) = ∑ⱼ ∫ |f′(zⱼ(τ)) zⱼ′(τ)| dτ` of `f` along the path `𝒫`
made of the arcs `z = γⱼ(τ)`, `tⱼ ≤ τ ≤ tⱼ₊₁`, `j < m`. -/
noncomputable def pathVariation (f : ℂ → ℂ) (γ γ' : ℕ → ℝ → ℂ) (t : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range m, ∫ τ in t j..t (j + 1), ‖deriv f (γ j τ) * γ' j τ‖

/-- **Olver Ex. 11.4**: if the path `𝒫` (parametrized by `Γ`, agreeing on `[tⱼ, tⱼ₊₁]` with the
continuously differentiable arc `γⱼ`) lies in a domain where `f` is holomorphic, then
`𝒱_𝒫(f) = sup ∑ₛ |f(zₛ₊₁) − f(zₛ)|` over all points `z₀, z₁, …, zₙ` of `𝒫` arranged in order
(the total variation of `f ∘ Γ`). -/
theorem olver_ex_11_4 {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    {Γ : ℝ → ℂ} {t : ℕ → ℝ} (ht : Monotone t) {m : ℕ} {γ γ' : ℕ → ℝ → ℂ}
    (hγ : ∀ j < m, ∀ τ ∈ Icc (t j) (t (j + 1)), HasDerivAt (γ j) (γ' j τ) τ)
    (hγ' : ∀ j < m, ContinuousOn (γ' j) (Icc (t j) (t (j + 1))))
    (hΓ : ∀ j < m, EqOn Γ (γ j) (Icc (t j) (t (j + 1))))
    (hγD : ∀ j < m, MapsTo (γ j) (Icc (t j) (t (j + 1))) D) :
    eVariationOn (f ∘ Γ) (Icc (t 0) (t m)) = ENNReal.ofReal (pathVariation f γ γ' t m) := by
  rw [← eVariationOn.sum' _ ht, pathVariation, ENNReal.ofReal_sum_of_nonneg fun j _ =>
    intervalIntegral.integral_nonneg (ht (Nat.le_succ j)) fun _ _ => norm_nonneg _]
  refine sum_congr rfl fun j hj => ?_
  have hjm := mem_range.mp hj
  rw [eVariationOn.eq_of_eqOn (f' := f ∘ γ j) fun τ hτ => by
    simp only [Function.comp_apply, hΓ j hjm hτ]]
  refine olver_11_02 (ht (Nat.le_succ j)) (fun τ hτ => ?_) ?_
  · exact (hf.differentiableAt (hD.mem_nhds (hγD j hjm hτ))).hasDerivAt.comp τ (hγ j hjm τ hτ)
  · have hc : ContinuousOn (γ j) (Icc (t j) (t (j + 1))) := fun τ hτ =>
      (hγ j hjm τ hτ).continuousAt.continuousWithinAt
    exact ((hf.deriv hD).continuousOn.comp hc (hγD j hjm)).mul (hγ' j hjm)

/-! ### Olver Ex. 11.3: `𝒱_{−1,1}(e^{iz})` along three paths -/

theorem deriv_exp_I_mul (z : ℂ) : deriv (fun z => cexp (I * z)) z = I * cexp (I * z) := by
  have := ((hasDerivAt_id z).const_mul I).cexp
  simp only [id, mul_one] at this
  rw [this.deriv, mul_comm]

theorem norm_deriv_exp_I_mul (z w : ℂ) :
    ‖deriv (fun z => cexp (I * z)) z * w‖ = Real.exp (-z.im) * ‖w‖ := by
  rw [deriv_exp_I_mul, norm_mul, norm_mul, norm_I, one_mul, Complex.norm_exp]
  simp

/-- The three arcs `−1 → −1 + 2si → 1 + 2si → 1` (`s = ±1`) of the square of Ex. 11.3. -/
noncomputable def sqArc (s : ℝ) : ℕ → ℝ → ℂ
  | 0 => fun τ => -1 + ((s * τ : ℝ) : ℂ) * I
  | 1 => fun τ => ((τ - 3 : ℝ) : ℂ) + ((2 * s : ℝ) : ℂ) * I
  | _ => fun τ => 1 + ((s * (6 - τ) : ℝ) : ℂ) * I

/-- Their derivatives. -/
noncomputable def sqArc' (s : ℝ) : ℕ → ℝ → ℂ
  | 0 => fun _ => (s : ℂ) * I
  | 1 => fun _ => 1
  | _ => fun _ => -(s : ℂ) * I

/-- The path around three sides of the square, parametrized on `[0, 6]`. -/
noncomputable def sqPath (s : ℝ) (τ : ℝ) : ℂ :=
  if τ ≤ 2 then sqArc s 0 τ else if τ ≤ 4 then sqArc s 1 τ else sqArc s 2 τ

theorem eVariationOn_sqPath {s : ℝ} (hs : |s| = 1) :
    eVariationOn (fun τ => cexp (I * sqPath s τ)) (Icc 0 6) =
      ENNReal.ofReal (2 * (∫ τ in (0 : ℝ)..2, Real.exp (-(s * τ))) + 2 * Real.exp (-(2 * s))) := by
  have hT : Icc (0 : ℝ) 6 = Icc ((fun j : ℕ => (2 * j : ℝ)) 0) ((fun j : ℕ => (2 * j : ℝ)) 3) := by
    norm_num
  have key := olver_ex_11_4 (f := fun z => cexp (I * z)) (D := univ) isOpen_univ
    (by fun_prop) (Γ := sqPath s) (t := fun j : ℕ => (2 * j : ℝ))
    (fun i j hij => by simp only; gcongr) (m := 3) (γ := sqArc s) (γ' := sqArc' s)
    (fun j hj τ _ => by
      interval_cases j
      · show HasDerivAt (fun τ : ℝ => -1 + ((s * τ : ℝ) : ℂ) * I) ((s : ℂ) * I) τ
        have := (((hasDerivAt_id τ).const_mul s).ofReal_comp.mul_const I).const_add (-1)
        simpa only [id, mul_one] using this
      · show HasDerivAt (fun τ : ℝ => ((τ - 3 : ℝ) : ℂ) + ((2 * s : ℝ) : ℂ) * I) 1 τ
        have := ((((hasDerivAt_id τ).sub_const 3).ofReal_comp).add_const
          (((2 * s : ℝ) : ℂ) * I))
        simpa only [id, Complex.ofReal_one] using this
      · show HasDerivAt (fun τ : ℝ => 1 + ((s * (6 - τ) : ℝ) : ℂ) * I) (-(s : ℂ) * I) τ
        have := ((((hasDerivAt_id τ).const_sub 6).const_mul s).ofReal_comp.mul_const I).const_add 1
        rw [show -(s : ℂ) * I = ((s * -1 : ℝ) : ℂ) * I by push_cast; ring]
        simpa only [id] using this)
    (fun j hj => by interval_cases j <;> exact continuousOn_const)
    (fun j hj τ hτ => by
      obtain ⟨h1, h2⟩ := hτ
      interval_cases j <;> norm_num at h1 h2 <;> simp only [sqPath]
      · simp only [h2, ↓reduceIte]
      · by_cases h : τ ≤ 2
        · simp only [h, ↓reduceIte]
          have : τ = 2 := by linarith
          subst this; simp only [sqArc]; push_cast; ring
        · simp only [h, h2, ↓reduceIte]
      · have h : ¬ τ ≤ 2 := by linarith
        by_cases h' : τ ≤ 4
        · simp only [h, h', ↓reduceIte]
          have : τ = 4 := by linarith
          subst this; simp only [sqArc]; push_cast; ring
        · simp only [h, h', ↓reduceIte])
    (fun j _ => mapsTo_univ _ _)
  rw [hT]
  refine key.trans (congrArg _ ?_)
  have hsI : ‖(s : ℂ) * I‖ = 1 := by rw [norm_mul, norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, hs]
  have hsI' : ‖-(s : ℂ) * I‖ = 1 := by rw [neg_mul, norm_neg, hsI]
  simp only [pathVariation, sum_range_succ, sum_range_zero, zero_add, norm_deriv_exp_I_mul,
    sqArc, sqArc', hsI, hsI', norm_one, mul_one, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  simp only [Complex.add_im, Complex.neg_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
    neg_zero, intervalIntegral.integral_const, smul_eq_mul]
  have h3 : ∫ τ in (4 : ℝ)..6, Real.exp (-(s * (6 - τ))) =
      ∫ τ in (0 : ℝ)..2, Real.exp (-(s * τ)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun τ => Real.exp (-(s * τ)))]; norm_num
  norm_num [h3]
  ring

/-- **Olver Ex. 11.3 (i)**: along the join of `−1` and `1`, `𝒱_{−1,1}(e^{iz}) = 2`. -/
theorem olver_ex_11_3_i :
    eVariationOn (fun τ : ℝ => cexp (I * τ)) (Icc (-1) 1) = 2 := by
  have key := olver_ex_11_4 (f := fun z => cexp (I * z)) (D := univ) isOpen_univ
    (by fun_prop) (Γ := fun τ : ℝ => (τ : ℂ)) (t := fun j : ℕ => (-1 + 2 * j : ℝ))
    (fun i j hij => by simp only; gcongr) (m := 1) (γ := fun _ τ => (τ : ℂ))
    (γ' := fun _ _ => 1) (fun _ _ τ _ => by simpa using (hasDerivAt_id τ).ofReal_comp)
    (fun _ _ => continuousOn_const) (fun _ _ => fun _ _ => rfl) (fun _ _ => mapsTo_univ _ _)
  norm_num at key
  refine key.trans ?_
  rw [pathVariation, sum_range_one]
  have h : ∀ τ : ℝ, ‖deriv (fun z => cexp (I * z)) τ * 1‖ = 1 := fun τ => by
    rw [norm_deriv_exp_I_mul]; simp
  simp only [h, intervalIntegral.integral_const, smul_eq_mul]
  norm_num

theorem integral_exp_neg_two : ∫ τ in (0 : ℝ)..2, Real.exp (-(1 * τ)) = 1 - Real.exp (-2) := by
  simp only [one_mul]
  rw [intervalIntegral.integral_comp_neg (fun τ => Real.exp τ), integral_exp]; norm_num

theorem integral_exp_two : ∫ τ in (0 : ℝ)..2, Real.exp (-(-1 * τ)) = Real.exp 2 - 1 := by
  simp only [neg_mul, one_mul, neg_neg]
  rw [integral_exp]; norm_num

/-- **Olver Ex. 11.3 (ii)**: around the other three sides of the square with vertices `−1`, `1`,
`1 + 2i`, `−1 + 2i`, again `𝒱(e^{iz}) = 2`. -/
theorem olver_ex_11_3_ii :
    eVariationOn (fun τ => cexp (I * sqPath 1 τ)) (Icc 0 6) = 2 := by
  rw [eVariationOn_sqPath (by norm_num), integral_exp_neg_two,
    show 2 * (1 - Real.exp (-2)) + 2 * Real.exp (-(2 * 1)) = (2 : ℝ) by ring_nf]
  norm_num

/-- **Olver Ex. 11.3 (iii)**: around the conjugate path (through `−1 − 2i`, `1 − 2i`),
`𝒱(e^{iz}) = 4e² − 2`. -/
theorem olver_ex_11_3_iii :
    eVariationOn (fun τ => cexp (I * sqPath (-1) τ)) (Icc 0 6) =
      ENNReal.ofReal (4 * Real.exp 2 - 2) := by
  rw [eVariationOn_sqPath (by norm_num), integral_exp_two,
    show -(2 * (-1 : ℝ)) = 2 by norm_num]
  congr 1; ring

/-! ### Olver Ex. 11.2 (i), (iv) -/

theorem hasDerivAt_neg_mul_exp_neg (x : ℝ) :
    HasDerivAt (fun t => -(t * Real.exp (-t))) ((x - 1) * Real.exp (-x)) x := by
  have h := ((hasDerivAt_id x).mul (hasDerivAt_neg x).exp).neg
  convert h using 1
  · rfl
  · simp only [id]; ring

theorem integral_sub_one_mul_exp_neg (x : ℝ) :
    ∫ t in (0 : ℝ)..x, (t - 1) * Real.exp (-t) = -(x * Real.exp (-x)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_neg_mul_exp_neg t)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

/-- **Olver Ex. 11.2 (iv)**: `𝒱_{x=0,∞}{∫₀ˣ (t − 1) e^{−t} dt} = 2/e`. -/
theorem olver_ex_11_2_iv :
    eVariationOn (fun x => ∫ t in (0 : ℝ)..x, (t - 1) * Real.exp (-t)) (Ici 0) =
      ENNReal.ofReal (2 * Real.exp (-1)) := by
  set g : ℝ → ℝ := fun x => -(x * Real.exp (-x)) with hg
  rw [show (fun x => ∫ t in (0 : ℝ)..x, (t - 1) * Real.exp (-t)) = g from
    funext integral_sub_one_mul_exp_neg]
  have hd : ∀ x, HasDerivAt g ((x - 1) * Real.exp (-x)) x := hasDerivAt_neg_mul_exp_neg
  have hc : Continuous g := by rw [hg]; fun_prop
  have anti : AntitoneOn g (Icc 0 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hc.continuousOn
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => by
        rw [interior_Icc] at hx
        rw [(hd x).deriv]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (Real.exp_pos _).le
  have mono : MonotoneOn g (Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) hc.continuousOn
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => by
        rw [interior_Ici] at hx
        rw [(hd x).deriv]
        exact mul_nonneg (by linarith [mem_Ioi.mp hx]) (Real.exp_pos _).le
  have lim : Tendsto (-g) atTop (𝓝 0) := by
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    simp only [pow_one] at this
    convert this using 1
    funext x; simp [hg]
  have v1 := olver_11_01 zero_le_one (Or.inr anti)
  have v2 := eVariationOn_Ici_of_antitoneOn (f := -g) (a := 1)
    (fun x hx y hy hxy => neg_le_neg (mono hx hy hxy)) lim
  rw [eVariationOn_neg] at v2
  rw [← Icc_union_Ici_eq_Ici zero_le_one, eVariationOn.union _ (isGreatest_Icc zero_le_one)
    isLeast_Ici, v1, v2, ← ENNReal.ofReal_add (abs_nonneg _) (by simp [hg]; positivity)]
  congr 1
  simp [hg]
  ring

theorem sin_sq_eq_piece (N : ℕ) (j : ℕ) (x : ℝ) :
    Real.sin (N * π * x) ^ 2 =
      1 / 2 - (-1) ^ j * Real.cos (2 * N * π * x - j * π) / 2 := by
  rw [Real.sin_sq_eq_half_sub, ← Real.cos_add_nat_mul_pi, sub_add_cancel]
  ring_nf

/-- **Olver Ex. 11.2 (i)**: `𝒱_{0,1}{sin²(nπx)} = 2|n|` for every integer `n`. -/
theorem olver_ex_11_2_i (n : ℤ) :
    eVariationOn (fun x : ℝ => Real.sin (n * π * x) ^ 2) (Icc 0 1) =
      ENNReal.ofReal (2 * |(n : ℝ)|) := by
  set N := n.natAbs with hN
  have hNn : (N : ℝ) = |(n : ℝ)| := by simp [hN, Nat.cast_natAbs, Int.cast_abs]
  have hf : (fun x : ℝ => Real.sin (n * π * x) ^ 2) = fun x => Real.sin (N * π * x) ^ 2 := by
    funext x
    rcases Int.natAbs_eq n with h | h
    · rw [h]; simp [hN]
    · rw [h]; simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.sin_neg, neg_sq, hN]
  rw [hf, ← hNn]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, zero_mul, Real.sin_zero, mul_zero, ENNReal.ofReal_zero]
    norm_num
    exact eVariationOn.constant_on (by simp [Set.Subsingleton])
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
  set x : ℕ → ℝ := fun j => j / (2 * N) with hx
  have hxm : Monotone x := fun i j hij => by
    simp only [hx]; gcongr
  have hx0 : x 0 = 0 := by simp [hx]
  have hxN : x (2 * N) = 1 := by simp only [hx]; push_cast; field_simp
  have hpiece : ∀ j, ∀ y ∈ Icc (x j) (x (j + 1)), 2 * N * π * y - j * π ∈ Icc 0 π := by
    intro j y hy
    simp only [hx, Set.mem_Icc] at hy
    rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity)] at hy
    push_cast at hy
    constructor <;> nlinarith [Real.pi_pos]
  have key := olver_11_3_subdivision (f := fun y => Real.sin (N * π * y) ^ 2) hxm (n := 2 * N)
    fun j _ => by
      rcases Nat.even_or_odd j with he | ho
      · left
        intro y hy z hz hyz
        simp only [sin_sq_eq_piece N j, he.neg_one_pow, one_mul]
        have := Real.antitoneOn_cos (hpiece j y hy) (hpiece j z hz) (by
          have := mul_le_mul_of_nonneg_left hyz (by positivity : (0 : ℝ) ≤ 2 * N * π)
          linarith)
        linarith
      · right
        intro y hy z hz hyz
        simp only [sin_sq_eq_piece N j, ho.neg_one_pow, neg_one_mul]
        have := Real.antitoneOn_cos (hpiece j y hy) (hpiece j z hz) (by
          have := mul_le_mul_of_nonneg_left hyz (by positivity : (0 : ℝ) ≤ 2 * N * π)
          linarith)
        linarith
  rw [hx0, hxN] at key
  rw [key]
  congr 1
  have hval : ∀ j : ℕ, Real.sin (N * π * x j) ^ 2 = 1 / 2 - (-1) ^ j / 2 := fun j => by
    rw [sin_sq_eq_piece N j]
    have : 2 * N * π * x j - j * π = 0 := by simp only [hx]; field_simp; ring
    rw [this, Real.cos_zero, mul_one]
  simp only [hval, pow_succ]
  have : ∀ j : ℕ, |1 / 2 - (-1 : ℝ) ^ j * -1 / 2 - (1 / 2 - (-1) ^ j / 2)| = 1 := fun j => by
    rw [show 1 / 2 - (-1 : ℝ) ^ j * -1 / 2 - (1 / 2 - (-1) ^ j / 2) = (-1) ^ j by ring,
      abs_pow, abs_neg, abs_one, one_pow]
  simp only [this, sum_const, card_range, nsmul_eq_mul, mul_one]
  push_cast; ring

end Azurite.DLMF
