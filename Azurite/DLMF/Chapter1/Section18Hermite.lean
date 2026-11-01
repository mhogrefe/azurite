/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18Spectral
import Azurite.DLMF.Chapter1.Section14Mellin

/-!
# DLMF §1.18(v): Hermite's differential equation, `X = (−∞, ∞)`

https://dlmf.nist.gov/1.18.v

* The physicists' Hermite polynomials `physHermite` (DLMF §18.3), defined by `H₀ = 1`,
  `H_{n+1} = 2x Hₙ − Hₙ′`. They satisfy `H′_{n+1} = 2(n+1)Hₙ`, Hermite's equation
  `Hₙ″ = 2xHₙ′ − 2nHₙ`, and `deg Hₙ = n` with leading coefficient `2ⁿ`.
* 1.18.41: `e^{−x²/2} Hₙ(x)` (`gaussFun (physHermite n)`) is an eigenfunction of
  `ℒ = −d²/dx² + x²` with eigenvalue `2n + 1` (`dlmf_1_18_41`).
* 1.18.42: the normalized `φₙ = e^{−x²/2} Hₙ / √(√π 2ⁿ n!)` (`hermitePhi`, `hermiteVec`) form a
  Hilbert basis of `L²(ℝ)` (`exists_hilbertBasis_hermiteVec`).
  * Orthonormality: `∫ Hₘ Hₙ e^{−x²} = √π 2ⁿ n! δ_{m,n}` (`integral_physHermite_mul`), by
    repeated integration by parts on `ℝ` with `Hₙ₊₁ e^{−x²} = −(Hₙ e^{−x²})′`.
  * Completeness (`eq_zero_of_forall_dlmfInner_hermiteVec`): if `f ⊥ φₙ` for all `n`, then
    `f ⊥ e^{−x²/2}P(x)` for every polynomial `P`. Expanding `e^{−2πixw}` in its power series
    (dominated by `e^{c|x|} |f(x)| e^{−x²/2} ∈ L¹`) shows that the Fourier transform of
    `f e^{−x²/2}` vanishes. Fourier inversion a.e. (§1.14) then gives `f = 0`.
* 1.18.43: the expansion `f(x) = ∑ₙ ∫ e^{−(x²+y²)/2} Hₙ(x)Hₙ(y) f(y) dy / (√π 2ⁿ n!)` for every
  `f ∈ L²(ℝ)`, with convergence in the mean (`hermiteKernel`, `dlmf_1_18_43`).
* The implicit boundary conditions `φₙ, φₙ′ → 0` at `±∞` (`dlmf_1_18_v_hermite_boundary`). DLMF's
  remark that this is equivalent to `φₙ ∈ L²` is not formalized.

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory Polynomial
open scoped InnerProductSpace ComplexConjugate Real Nat FourierTransform

namespace Azurite.DLMF

/-! ### Physicists' Hermite polynomials -/

/-- The physicists' Hermite polynomials `Hₙ` (DLMF §18.3): `H₀ = 1`, `H_{n+1} = 2x Hₙ − Hₙ′`. -/
noncomputable def physHermite : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C 2 * X * physHermite n - derivative (physHermite n)

theorem physHermite_zero : physHermite 0 = 1 := rfl

theorem physHermite_succ (n : ℕ) :
    physHermite (n + 1) = C 2 * X * physHermite n - derivative (physHermite n) := rfl

/-- `H′_{n+1} = 2(n + 1) Hₙ`. -/
theorem derivative_physHermite_succ (n : ℕ) :
    derivative (physHermite (n + 1)) = C (2 * (n + 1 : ℝ)) * physHermite n := by
  induction n with
  | zero => simp [physHermite_succ, physHermite_zero]
  | succ n ih =>
    rw [physHermite_succ (n + 1), derivative_sub, derivative_mul, derivative_C_mul_X, ih,
      derivative_C_mul]
    have e := physHermite_succ n
    have h2 : C (2 * ((n + 1 : ℕ) + 1 : ℝ)) = C 2 + C (2 * (n + 1 : ℝ)) := by
      rw [← C_add]; congr 1; push_cast; ring
    rw [h2]
    linear_combination (-C (2 * (n + 1 : ℝ))) * e

/-- Hermite's equation `Hₙ″ = 2x Hₙ′ − 2n Hₙ`. -/
theorem physHermite_ode (n : ℕ) :
    derivative (derivative (physHermite n)) =
      C 2 * X * derivative (physHermite n) - C (2 * n : ℝ) * physHermite n := by
  have h1 := derivative_physHermite_succ n
  rw [physHermite_succ, derivative_sub, derivative_mul, derivative_C_mul_X] at h1
  have h2 : C (2 * (n + 1 : ℝ)) = C 2 + C (2 * n : ℝ) := by rw [← C_add]; congr 1; ring
  rw [h2] at h1
  linear_combination -h1

theorem natDegree_leadingCoeff_physHermite (n : ℕ) :
    (physHermite n).natDegree = n ∧ (physHermite n).leadingCoeff = 2 ^ n := by
  induction n with
  | zero => simp [physHermite_zero]
  | succ n ih =>
    have hne : physHermite n ≠ 0 := by
      intro h
      have := ih.2
      rw [h, leadingCoeff_zero] at this
      exact (pow_ne_zero n two_ne_zero) this.symm
    have hA1 : (C 2 * X * physHermite n).natDegree = n + 1 := by
      rw [mul_assoc, natDegree_C_mul two_ne_zero, natDegree_X_mul hne, ih.1]
    have hA2 : (C 2 * X * physHermite n).leadingCoeff = 2 ^ (n + 1) := by
      rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, ih.2]
      ring
    have hd : (derivative (physHermite n)).natDegree < (C 2 * X * physHermite n).natDegree := by
      rw [hA1]
      exact lt_of_le_of_lt (natDegree_derivative_le _) (by rw [ih.1]; omega)
    rw [physHermite_succ, natDegree_sub_eq_left_of_natDegree_lt hd, hA1,
      leadingCoeff_sub_of_degree_lt (degree_lt_degree hd), hA2]
    exact ⟨rfl, rfl⟩

theorem physHermite_ne_zero (n : ℕ) : physHermite n ≠ 0 := by
  intro h
  have := (natDegree_leadingCoeff_physHermite n).2
  rw [h, leadingCoeff_zero] at this
  exact (pow_ne_zero n two_ne_zero) this.symm

/-! ### Polynomials times the Gaussian `e^{−x²}` -/

theorem integrable_pow_mul_gauss (k : ℕ) :
    Integrable fun x : ℝ => x ^ k * Real.exp (-x ^ 2) := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := k)
    (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  simpa [Real.rpow_natCast] using this

theorem integrable_poly_gauss (p : ℝ[X]) :
    Integrable fun x => p.eval x * Real.exp (-x ^ 2) := by
  simp_rw [eval_eq_sum_range, Finset.sum_mul]
  exact integrable_finsetSum _ fun i _ => by
    simpa [mul_assoc] using (integrable_pow_mul_gauss i).const_mul (p.coeff i)

theorem tendsto_pow_mul_gauss_atTop (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k) ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with x hx using by positivity
  · filter_upwards [eventually_ge_atTop 1] with x hx
    gcongr
    nlinarith

theorem tendsto_pow_mul_gauss_atBot (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := ((tendsto_pow_mul_gauss_atTop k).const_mul ((-1 : ℝ) ^ k)).comp tendsto_neg_atBot_atTop
  rw [mul_zero] at h
  refine h.congr fun x => ?_
  simp only [Function.comp, neg_sq]
  rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]

theorem tendsto_poly_gauss (p : ℝ[X]) {l : Filter ℝ} (hl : l = atTop ∨ l = atBot) :
    Tendsto (fun x => p.eval x * Real.exp (-x ^ 2)) l (𝓝 0) := by
  simp_rw [eval_eq_sum_range, Finset.sum_mul]
  rw [show (0 : ℝ) = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * 0 by simp]
  refine tendsto_finsetSum _ fun i _ => ?_
  simp_rw [mul_assoc]
  refine Tendsto.const_mul _ ?_
  rcases hl with rfl | rfl
  · exact tendsto_pow_mul_gauss_atTop i
  · exact tendsto_pow_mul_gauss_atBot i

theorem hasDerivAt_poly_mul_gauss (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x => P.eval x * Real.exp (-x ^ 2))
      ((derivative P - C 2 * X * P).eval x * Real.exp (-x ^ 2)) x := by
  have h := (P.hasDerivAt x).mul ((hasDerivAt_pow 2 x).neg.exp)
  convert h using 1
  simp only [eval_sub, eval_mul, eval_C, eval_X, Pi.neg_apply]
  ring

/-- Integration by parts: `∫ p Hₙ₊₁ e^{−x²} = ∫ p′ Hₙ e^{−x²}`, as
`Hₙ₊₁ e^{−x²} = −(Hₙ e^{−x²})′`. -/
theorem integral_mul_physHermite_succ (p : ℝ[X]) (n : ℕ) :
    ∫ x, p.eval x * ((physHermite (n + 1)).eval x * Real.exp (-x ^ 2)) =
      ∫ x, (derivative p).eval x * ((physHermite n).eval x * Real.exp (-x ^ 2)) := by
  have hv : ∀ x, HasDerivAt (fun x => (physHermite n).eval x * Real.exp (-x ^ 2))
      (-((physHermite (n + 1)).eval x * Real.exp (-x ^ 2))) x := fun x => by
    convert hasDerivAt_poly_mul_gauss (physHermite n) x using 1
    rw [physHermite_succ]
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    ring
  have h := integral_mul_deriv_eq_deriv_mul (u := p.eval) (u' := (derivative p).eval)
    (v := fun x => (physHermite n).eval x * Real.exp (-x ^ 2))
    (v' := fun x => -((physHermite (n + 1)).eval x * Real.exp (-x ^ 2))) (a' := 0) (b' := 0)
    (fun x _ => p.hasDerivAt x) (fun x _ => hv x)
    ((integrable_poly_gauss (p * physHermite (n + 1))).neg.congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply, eval_mul, Pi.neg_apply]; ring))
    ((integrable_poly_gauss (derivative p * physHermite n)).congr (ae_of_all _ fun x => by
      simp only [Pi.mul_apply, eval_mul]; ring))
    ((tendsto_poly_gauss (p * physHermite n) (Or.inr rfl)).congr fun x => by
      simp only [Pi.mul_apply, eval_mul]; ring)
    ((tendsto_poly_gauss (p * physHermite n) (Or.inl rfl)).congr fun x => by
      simp only [Pi.mul_apply, eval_mul]; ring)
  simp only [sub_zero, zero_sub, mul_neg, integral_neg, neg_inj] at h
  exact h

/-- Orthogonality: `∫ Hₘ(x) Hₙ(x) e^{−x²} dx = √π 2ⁿ n! δ_{m,n}`. -/
theorem integral_physHermite_mul (m n : ℕ) :
    ∫ x, (physHermite m).eval x * ((physHermite n).eval x * Real.exp (-x ^ 2)) =
      if m = n then √π * 2 ^ n * n ! else 0 := by
  induction n generalizing m with
  | zero =>
    rcases m with _ | k
    · simp only [physHermite_zero, eval_one, one_mul, ite_true, pow_zero, Nat.factorial_zero,
        Nat.cast_one, mul_one]
      have := integral_gaussian 1
      simp only [neg_mul, one_mul, div_one] at this
      exact this
    · have h := integral_mul_physHermite_succ 1 k
      simp only [derivative_one, eval_zero, zero_mul, integral_zero, eval_one, one_mul] at h
      simp only [physHermite_zero, eval_one, one_mul, Nat.succ_ne_zero, ite_false]
      exact h
  | succ n ih =>
    rw [integral_mul_physHermite_succ]
    rcases m with _ | k
    · simp [physHermite_zero]
    · rw [derivative_physHermite_succ]
      simp only [eval_mul, eval_C, mul_assoc]
      rw [integral_const_mul, integral_const_mul, ih k]
      by_cases h : k = n
      · subst h
        simp only [ite_true]
        push_cast [Nat.factorial_succ]
        ring
      · simp [h]

/-! ### The eigenfunctions `e^{−x²/2} Hₙ(x)` (1.18.41) -/

/-- `e^{−x²/2} P(x)`. -/
noncomputable def gaussFun (P : ℝ[X]) (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2) * P.eval x

theorem hasDerivAt_gaussFun (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (gaussFun P) (gaussFun (derivative P - X * P) x) x := by
  have h := ((hasDerivAt_pow 2 x).neg.div_const 2).exp.mul (P.hasDerivAt x)
  refine h.congr_deriv ?_
  simp only [gaussFun, eval_sub, eval_mul, eval_X, Pi.neg_apply]
  ring

theorem deriv_gaussFun (P : ℝ[X]) : deriv (gaussFun P) = gaussFun (derivative P - X * P) :=
  funext fun x => (hasDerivAt_gaussFun P x).deriv

/-- DLMF 1.18.41: `e^{−x²/2} Hₙ(x)` is an eigenfunction of `ℒ = −d²/dx² + x²` with eigenvalue
`λₙ = 2n + 1`. -/
theorem dlmf_1_18_41 (n : ℕ) (x : ℝ) :
    -deriv (deriv (gaussFun (physHermite n))) x + x ^ 2 * gaussFun (physHermite n) x =
      (2 * n + 1) * gaussFun (physHermite n) x := by
  rw [deriv_gaussFun, deriv_gaussFun]
  have hode := physHermite_ode n
  have key : -(derivative (derivative (physHermite n) - X * physHermite n) -
      X * (derivative (physHermite n) - X * physHermite n)) + X ^ 2 * physHermite n =
      C (2 * n + 1 : ℝ) * physHermite n := by
    rw [derivative_sub, derivative_mul, derivative_X, hode]
    have : C (2 * n + 1 : ℝ) = C (2 * n : ℝ) + 1 := by rw [← C_1, ← C_add]
    have h2 : (C 2 : ℝ[X]) = 2 := map_ofNat C 2
    rw [this, h2]
    ring
  have := congrArg (fun P => gaussFun P x) key
  simp only [gaussFun, eval_add, eval_neg, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at this ⊢
  linarith [this]

/-! ### `L²(ℝ)` and the normalized eigenfunctions (1.18.42) -/

/-- `L²(ℝ)`. -/
noncomputable abbrev L2R := Lp ℂ 2 (volume : Measure ℝ)

theorem sq_gaussFun (P : ℝ[X]) (x : ℝ) :
    gaussFun P x ^ 2 = (P * P).eval x * Real.exp (-x ^ 2) := by
  simp only [gaussFun, eval_mul]
  rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
  ring_nf

theorem continuous_gaussFun (P : ℝ[X]) : Continuous (gaussFun P) := by
  unfold gaussFun; fun_prop

theorem memLp_gaussFun (P : ℝ[X]) : MemLp (fun x => ((gaussFun P x : ℝ) : ℂ)) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    (Complex.continuous_ofReal.comp (continuous_gaussFun P)).aestronglyMeasurable).mpr ?_
  refine (integrable_poly_gauss (P * P)).congr (ae_of_all _ fun x => ?_)
  show _ = ‖((gaussFun P x : ℝ) : ℂ)‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq_gaussFun]

/-- `e^{−x²/2} P(x)` as an element of `L²(ℝ)`. -/
noncomputable def gaussVec (P : ℝ[X]) : L2R := (memLp_gaussFun P).toLp _

theorem coeFn_gaussVec (P : ℝ[X]) : (gaussVec P : ℝ → ℂ) =ᵐ[volume] fun x => (gaussFun P x : ℂ) :=
  (memLp_gaussFun P).coeFn_toLp

theorem gaussVec_add (P Q : ℝ[X]) : gaussVec (P + Q) = gaussVec P + gaussVec Q := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [coeFn_gaussVec (P + Q), coeFn_gaussVec P, coeFn_gaussVec Q,
    Lp.coeFn_add (gaussVec P) (gaussVec Q)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3]
  simp only [gaussFun, eval_add]
  push_cast; ring

theorem gaussVec_C_mul (c : ℝ) (P : ℝ[X]) : gaussVec (C c * P) = (c : ℂ) • gaussVec P := by
  refine Lp.ext_iff.mpr ?_
  filter_upwards [coeFn_gaussVec (C c * P), coeFn_gaussVec P,
    Lp.coeFn_smul (c : ℂ) (gaussVec P)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul]
  simp only [gaussFun, eval_mul, eval_C]
  push_cast; ring

theorem gaussVec_zero : gaussVec 0 = 0 := by
  have := gaussVec_C_mul 0 0
  simpa using this

/-- The normalizing constant `1/√(√π 2ⁿ n!)` of 1.18.42. -/
noncomputable def hermiteNorm (n : ℕ) : ℝ := 1 / √(√π * 2 ^ n * n !)

theorem hermiteNorm_sq (n : ℕ) : hermiteNorm n ^ 2 * (√π * 2 ^ n * n !) = 1 := by
  have hA : 0 < √π * 2 ^ n * n ! := by positivity
  rw [hermiteNorm, div_pow, one_pow, Real.sq_sqrt hA.le, one_div_mul_cancel hA.ne']

/-- DLMF 1.18.42: `φₙ(x) = e^{−x²/2} Hₙ(x) / √(√π 2ⁿ n!)`. -/
noncomputable def hermitePhi (n : ℕ) (x : ℝ) : ℝ := hermiteNorm n * gaussFun (physHermite n) x

/-- `φₙ` as an element of `L²(ℝ)`. -/
noncomputable def hermiteVec (n : ℕ) : L2R := (hermiteNorm n : ℂ) • gaussVec (physHermite n)

theorem coeFn_hermiteVec (n : ℕ) :
    (hermiteVec n : ℝ → ℂ) =ᵐ[volume] fun x => (hermitePhi n x : ℂ) := by
  filter_upwards [Lp.coeFn_smul (hermiteNorm n : ℂ) (gaussVec (physHermite n)),
    coeFn_gaussVec (physHermite n)] with x h1 h2
  rw [hermiteVec, h1, Pi.smul_apply, h2, smul_eq_mul, hermitePhi]
  push_cast; ring

theorem dlmfInner_L2R (f g : L2R) : dlmfInner f g = ∫ x, f x * conj (g x) :=
  dlmfInner_Lp_eq f g

/-- DLMF 1.18.29 for 1.18.42: the `φₙ` are orthonormal. -/
theorem orthonormal_hermiteVec : Orthonormal ℂ hermiteVec := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [← dlmfInner, dlmfInner_L2R]
  have e : ∫ x, (hermiteVec m : ℝ → ℂ) x * conj ((hermiteVec n : ℝ → ℂ) x) =
      ((hermiteNorm m * hermiteNorm n *
        ∫ x, (physHermite m).eval x * ((physHermite n).eval x * Real.exp (-x ^ 2)) : ℝ) : ℂ) := by
    rw [← integral_const_mul, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_hermiteVec m, coeFn_hermiteVec n] with x hm hn
    rw [hm, hn, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    simp only [hermitePhi, gaussFun]
    have : Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = Real.exp (-x ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (hermiteNorm m * hermiteNorm n * (physHermite m).eval x *
      (physHermite n).eval x) * this
  rw [e, integral_physHermite_mul]
  by_cases h : m = n
  · subst h
    simp only [ite_true]
    have := hermiteNorm_sq m
    rw [show hermiteNorm m * hermiteNorm m * (√π * 2 ^ m * m !) = 1 by nlinarith [this]]
    simp
  · simp [h, Ne.symm h]

/-! ### Completeness -/

theorem dlmfInner_add_right' (f u v : L2R) :
    dlmfInner f (u + v) = dlmfInner f u + dlmfInner f v := by
  simp [dlmfInner, inner_add_left]

/-- If `f ⊥ φₙ` for all `n`, then `f ⊥ e^{−x²/2} P(x)` for every polynomial `P`. -/
theorem dlmfInner_gaussVec_eq_zero {f : L2R} (hf : ∀ n, dlmfInner f (hermiteVec n) = 0)
    (P : ℝ[X]) : dlmfInner f (gaussVec P) = 0 := by
  have hH : ∀ n, dlmfInner f (gaussVec (physHermite n)) = 0 := fun n => by
    have h := hf n
    rw [hermiteVec, dlmfInner_smul_right, Complex.conj_ofReal] at h
    have hc : (hermiteNorm n : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by rw [hermiteNorm]; positivity)
    exact (mul_eq_zero.mp h).resolve_left hc
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ N ih =>
    by_cases hP : P = 0
    · rw [hP, gaussVec_zero]; simp [dlmfInner]
    set c := P.leadingCoeff / 2 ^ N
    have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
    have hc : c ≠ 0 := div_ne_zero hlc (pow_ne_zero _ two_ne_zero)
    set Q := C c * physHermite N
    have hQd : Q.natDegree = N := by
      rw [natDegree_C_mul hc, (natDegree_leadingCoeff_physHermite N).1]
    have hQl : Q.leadingCoeff = P.leadingCoeff := by
      rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hc),
        (natDegree_leadingCoeff_physHermite N).2]
      simp only [c]
      field_simp
    have hQ0 : Q ≠ 0 := by
      intro h0; rw [h0, leadingCoeff_zero] at hQl; exact hlc hQl.symm
    have hsplit : gaussVec P = gaussVec (P - Q) + (c : ℂ) • gaussVec (physHermite N) := by
      rw [← gaussVec_C_mul, ← gaussVec_add, sub_add_cancel]
    rw [hsplit, dlmfInner_add_right', dlmfInner_smul_right, hH, mul_zero, add_zero]
    by_cases hR : P - Q = 0
    · rw [hR, gaussVec_zero]; simp [dlmfInner]
    have hdeg : (P - Q).degree < P.degree :=
      degree_sub_lt_left (by rw [degree_eq_natDegree hP, degree_eq_natDegree hQ0, hQd, h])
        hP hQl.symm
    have hlt : (P - Q).natDegree < N := by
      rw [← h]; exact natDegree_lt_natDegree hR hdeg
    exact ih _ hlt (P - Q) rfl

theorem integrable_exp_quad (b : ℝ) : Integrable fun x : ℝ => Real.exp (-x ^ 2 + b * x) := by
  have h := (integrable_cexp_quadratic' (b := -1) (by simp) (b : ℂ) 0).norm
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [sq]

/-- `e^{−x²/2 + c|x|} ∈ L²(ℝ)`. -/
theorem memLp_exp_abs (c : ℝ) :
    MemLp (fun x : ℝ => ((Real.exp (-x ^ 2 / 2 + c * |x|) : ℝ) : ℂ)) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr ?_
  refine ((integrable_exp_quad (2 * c)).add (integrable_exp_quad (-(2 * c)))).mono'
    (by fun_prop) (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity), Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have := (Real.exp_pos (-x ^ 2 + -(2 * c) * x)).le
    have e : -x ^ 2 / 2 + c * x + (-x ^ 2 / 2 + c * x) = -x ^ 2 + 2 * c * x := by ring
    rw [e]; linarith
  · rw [abs_of_nonpos hx]
    have := (Real.exp_pos (-x ^ 2 + 2 * c * x)).le
    have e : -x ^ 2 / 2 + c * -x + (-x ^ 2 / 2 + c * -x) = -x ^ 2 + -(2 * c) * x := by ring
    rw [e]; linarith

theorem integrable_mul_L2R {u : ℝ → ℂ} (hu : MemLp u 2 volume) (hreal : ∀ x, conj (u x) = u x)
    (f : L2R) : Integrable fun x => u x * f x := by
  have h := L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) f
  refine h.congr ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [RCLike.inner_apply, hx, hreal, mul_comm]

/-- DLMF §1.18(v): the Hermite functions `φₙ` are complete: `f ⊥ φₙ` for all `n` forces `f = 0`.
The moments `∫ f xᵏ e^{−x²/2}` vanish, so expanding `e^{−2πixw}` shows that the Fourier transform
of `f e^{−x²/2}` vanishes. -/
theorem eq_zero_of_forall_dlmfInner_hermiteVec {f : L2R}
    (hf : ∀ n, dlmfInner f (hermiteVec n) = 0) : f = 0 := by
  set g : ℝ → ℂ := fun x => f x * (Real.exp (-x ^ 2 / 2) : ℂ)
  have hreal : ∀ (r : ℝ → ℝ) x, conj ((r x : ℝ) : ℂ) = (r x : ℂ) := fun r x => Complex.conj_ofReal _
  -- moments
  have hmom_int : ∀ k : ℕ, Integrable fun x : ℝ => (x : ℂ) ^ k * g x := fun k => by
    refine (integrable_mul_L2R (memLp_gaussFun (X ^ k)) (hreal _) f).congr
      (ae_of_all _ fun x => ?_)
    simp only [g, gaussFun, eval_pow, eval_X]
    push_cast; ring
  have hmom : ∀ k : ℕ, ∫ x : ℝ, (x : ℂ) ^ k * g x = 0 := fun k => by
    have h := dlmfInner_gaussVec_eq_zero hf (X ^ k)
    rw [dlmfInner_L2R] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_gaussVec (X ^ k)] with x hx
    rw [hx, Complex.conj_ofReal]
    simp only [g, gaussFun, eval_pow, eval_X]
    push_cast; ring
  have hg : Integrable g := by
    have := hmom_int 0
    simpa using this
  -- the Fourier transform of `g` vanishes
  have hF0 : ∀ w : ℝ, 𝓕 g w = 0 := fun w => by
    rw [Real.fourier_real_eq_integral_exp_smul]
    set z : ℂ := ((-2 * π * w : ℝ) : ℂ) * Complex.I
    have hz : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) = Complex.exp (z * v) :=
      fun v => by simp only [z]; push_cast; ring_nf
    simp_rw [hz, smul_eq_mul]
    set F : ℕ → ℝ → ℂ := fun k x => (z * x) ^ k / k ! * g x
    have hF_int : ∀ k, Integrable (F k) := fun k => by
      have := (hmom_int k).const_mul (z ^ k / k !)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [F]; ring
    have hB : Integrable fun x : ℝ => Real.exp (‖z‖ * |x|) * ‖g x‖ := by
      have := (integrable_mul_L2R (memLp_exp_abs ‖z‖) (hreal _) f).norm
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [g, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [Real.exp_add]
      ring
    have hnorm : ∀ k x, ‖F k x‖ = (‖z‖ * |x|) ^ k / k ! * ‖g x‖ := fun k x => by
      simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs]
    have hF_sum : Summable fun k => ∫ x, ‖F k x‖ := by
      refine summable_of_sum_range_le (c := ∫ x, Real.exp (‖z‖ * |x|) * ‖g x‖)
        (fun k => integral_nonneg fun x => norm_nonneg _) fun N => ?_
      rw [← integral_finsetSum _ fun k _ => (hF_int k).norm]
      refine integral_mono (integrable_finsetSum _ fun k _ => (hF_int k).norm) hB fun x => ?_
      simp only [hnorm, ← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hs := NormedSpace.expSeries_div_hasSum_exp (‖z‖ * |x| : ℝ)
      rw [← Real.exp_eq_exp_ℝ] at hs
      exact sum_le_hasSum _ (fun k _ => by positivity) hs
    have hsum := integral_tsum_of_summable_integral_norm hF_int hF_sum
    have hpt : ∀ x, ∑' k, F k x = Complex.exp (z * x) * g x := fun x => by
      have hs := (NormedSpace.expSeries_div_hasSum_exp (z * x : ℂ)).mul_right (g x)
      rw [← Complex.exp_eq_exp_ℂ] at hs
      exact hs.tsum_eq
    have hk : ∀ k, ∫ x, F k x = 0 := fun k => by
      have : (fun x => F k x) = fun x : ℝ => z ^ k / k ! * ((x : ℂ) ^ k * g x) :=
        funext fun x => by simp only [F]; ring
      rw [this, integral_const_mul, hmom k, mul_zero]
    simp only [hpt, hk, tsum_zero] at hsum
    exact hsum.symm
  have hF : 𝓕 g = 0 := funext hF0
  have hae := fourierInv_fourier_ae hg (by rw [hF]; exact integrable_zero _ _ _)
  rw [hF] at hae
  have hz : (f : ℝ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    have h0 : g x = 0 := by
      rw [← hx]
      simp [Real.fourierInv_eq]
    simp only [g, mul_eq_zero, Complex.ofReal_eq_zero, (Real.exp_pos _).ne', or_false] at h0
    exact h0
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hz

/-- DLMF 1.18.42: the normalized Hermite functions form a complete orthonormal set (a Hilbert
basis) of `L²(ℝ)`. -/
theorem exists_hilbertBasis_hermiteVec : ∃ b : HilbertBasis ℕ ℂ L2R, ⇑b = hermiteVec := by
  have hsp : (Submodule.span ℂ (Set.range hermiteVec))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact eq_zero_of_forall_dlmfInner_hermiteVec fun n =>
      Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self n)) hx
  exact ⟨HilbertBasis.mkOfOrthogonalEqBot orthonormal_hermiteVec hsp,
    HilbertBasis.coe_mkOfOrthogonalEqBot orthonormal_hermiteVec hsp⟩

/-! ### The expansion 1.18.43 -/

/-- The partial kernels `∑_{n=0}^{m} e^{−(x²+y²)/2} Hₙ(x) Hₙ(y) / (√π 2ⁿ n!)` of 1.18.43. -/
noncomputable def hermiteKernel (m : ℕ) (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), Real.exp (-(x ^ 2 + y ^ 2) / 2) / (√π * 2 ^ n * n !) *
    ((physHermite n).eval x * (physHermite n).eval y)

theorem hermiteKernel_eq (m : ℕ) (x y : ℝ) :
    hermiteKernel m x y = ∑ n ∈ Finset.range (m + 1), hermitePhi n x * hermitePhi n y := by
  refine Finset.sum_congr rfl fun n _ => ?_
  have h := hermiteNorm_sq n
  have hA : 0 < √π * 2 ^ n * n ! := by positivity
  have hc : 1 / (√π * 2 ^ n * n !) = hermiteNorm n ^ 2 := by
    field_simp; linarith
  simp only [hermitePhi, gaussFun]
  rw [div_eq_mul_one_div, hc, show -(x ^ 2 + y ^ 2) / 2 = -x ^ 2 / 2 + -y ^ 2 / 2 by ring,
    Real.exp_add]
  ring

theorem memLp_hermitePhi (n : ℕ) : MemLp (fun x => (hermitePhi n x : ℂ)) 2 volume := by
  have e : (fun x => (hermitePhi n x : ℂ)) =
      fun x => (hermiteNorm n : ℂ) * (gaussFun (physHermite n) x : ℂ) :=
    funext fun x => by simp [hermitePhi]
  rw [e]
  exact (memLp_gaussFun (physHermite n)).const_mul _

theorem tendsto_integral_sub_partialSum_L2R {c : ℕ → ℂ} {v : ℕ → L2R} {g : L2R}
    (h : HasSum (fun n => c n • v n) g) :
    Tendsto (fun m : ℕ => ∫ x, ‖g x - ∑ n ∈ Finset.range (m + 1), c n * v n x‖ ^ 2)
      atTop (𝓝 0) := by
  set S : ℕ → L2R := fun m => ∑ n ∈ Finset.range (m + 1), c n • v n
  have h1 := (h.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  have h2 := ((tendsto_iff_norm_sub_tendsto_zero.mp h1).pow 2)
  rw [zero_pow two_ne_zero] at h2
  refine h2.congr fun m => ?_
  simp only [Function.comp]
  rw [norm_sub_rev, ← integral_norm_sq_Lp]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub g (S m), coeFn_finsetSum_Lp (Finset.range (m + 1))
    (fun n => c n • v n), ae_all_iff.mpr fun n : ℕ => Lp.coeFn_smul (c n) (v n)] with x hx hs hsm
  rw [hx, Pi.sub_apply, hs]
  simp only [hsm, Pi.smul_apply, smul_eq_mul]

/-- DLMF 1.18.43: for `f ∈ L²(ℝ)`,
`f(x) = ∑ₙ ∫ e^{−(x²+y²)/2} Hₙ(x) Hₙ(y) f(y) / (√π 2ⁿ n!) dy`, with convergence in the mean
(§1.18(ii)) of the partial sums: `∫ |f(x) − ∫ Kₘ(x, y) f(y) dy|² dx → 0`. -/
theorem dlmf_1_18_43 (f : L2R) :
    Tendsto (fun m : ℕ => ∫ x, ‖f x - ∫ y, (hermiteKernel m x y : ℂ) * f y‖ ^ 2) atTop
      (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_hilbertBasis_hermiteVec
  have hS : HasSum (fun n => dlmfInner f (hermiteVec n) • hermiteVec n) f := by
    have := b.hasSum_repr f
    convert this using 1
    funext n
    rw [b.repr_apply_apply, hb]
    rfl
  have hreal : ∀ n x, conj ((hermitePhi n x : ℝ) : ℂ) = (hermitePhi n x : ℂ) := fun n x =>
    Complex.conj_ofReal _
  have hcoef : ∀ n, dlmfInner f (hermiteVec n) = ∫ y, (hermitePhi n y : ℂ) * f y := fun n => by
    rw [dlmfInner_L2R]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_hermiteVec n] with y hy
    rw [hy, hreal, mul_comm]
  have hint : ∀ n, Integrable fun y => (hermitePhi n y : ℂ) * f y := fun n =>
    integrable_mul_L2R (memLp_hermitePhi n) (hreal n) f
  refine (tendsto_integral_sub_partialSum_L2R hS).congr fun m => ?_
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.mpr fun n => coeFn_hermiteVec n] with x hx
  have key : ∑ n ∈ Finset.range (m + 1), dlmfInner f (hermiteVec n) * (hermiteVec n : ℝ → ℂ) x =
      ∫ y, (hermiteKernel m x y : ℂ) * f y := by
    have e : (fun y => (hermiteKernel m x y : ℂ) * f y) = fun y =>
        ∑ n ∈ Finset.range (m + 1), (hermitePhi n x : ℂ) * ((hermitePhi n y : ℂ) * f y) :=
      funext fun y => by
        simp only [hermiteKernel_eq, Complex.ofReal_sum, Finset.sum_mul, Complex.ofReal_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    rw [e, integral_finsetSum _ fun n _ => (hint n).const_mul _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hcoef, hx n, integral_const_mul, mul_comm]
  rw [key]

/-! ### The implicit boundary conditions -/

theorem tendsto_gaussFun (P : ℝ[X]) {l : Filter ℝ} (hl : l = atTop ∨ l = atBot) :
    Tendsto (gaussFun P) l (𝓝 0) := by
  have h := (tendsto_poly_gauss (P * P) hl).sqrt
  rw [Real.sqrt_zero] at h
  refine (tendsto_zero_iff_abs_tendsto_zero _).mpr (h.congr fun x => ?_)
  rw [← sq_gaussFun, Real.sqrt_sq_eq_abs]
  rfl

/-- DLMF §1.18(v): the implicit boundary conditions, `φₙ(x) → 0` and `φₙ′(x) → 0` as
`x → ±∞`. -/
theorem dlmf_1_18_v_hermite_boundary (n : ℕ) {l : Filter ℝ} (hl : l = atTop ∨ l = atBot) :
    Tendsto (gaussFun (physHermite n)) l (𝓝 0) ∧
      Tendsto (deriv (gaussFun (physHermite n))) l (𝓝 0) := by
  refine ⟨tendsto_gaussFun _ hl, ?_⟩
  rw [deriv_gaussFun]
  exact tendsto_gaussFun _ hl

end Azurite.DLMF
