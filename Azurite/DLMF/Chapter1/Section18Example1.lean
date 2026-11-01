/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18Spectral
import Azurite.DLMF.Chapter1.Section8

/-!
# DLMF §1.18(v), Example 1: three simple cases with `q = 0`, `X = [0, π]`

https://dlmf.nist.gov/1.18.v

`−d²/dx²` on `L²[0, π]` (`L2pi`) with three boundary conditions.

* Case 1 (`φ(0) = φ(π) = 0`, 1.18.36): `sinFun n = √(2/π) sin((n+1)x)`, eigenvalue `(n+1)²`.
* Case 2 (`φ′(0) = φ′(π) = 0`, 1.18.37): `cosFun 0 = 1/√π`, `cosFun n = √(2/π) cos(nx)`,
  eigenvalue `n²`.
* Case 3 (periodic, 1.18.38): `expFun n = e^{2inx}/√π`, `n ∈ ℤ`, eigenvalue `4n²`, of
  multiplicity two for `n ≠ 0` (`dlmf_1_18_38_multiplicity`).

Each family satisfies `−φ″ = λφ` and its boundary conditions (`dlmf_1_18_36`,
`dlmf_1_18_37_eigen`, `dlmf_1_18_38`). Each is orthonormal (by trigonometric integrals) and
complete, i.e. a Hilbert basis (`exists_hilbertBasis_sinVec`, `exists_hilbertBasis_cosVec`,
`exists_hilbertBasis_expVec`). Completeness follows from Parseval:
* Case 3: from Mathlib's Parseval for Fourier series of period `π` (`hasSum_sq_fourierCoeffOn`),
  since `⟨f, φ_exp(n)⟩ = √π cₙ` (`dlmfInner_expVec_eq_fourierCoeffOn`).
* Cases 1–2: from §1.8's Parseval 1.8.5 applied to the odd and even extensions of `f` to
  `[−π, π]`.

1.18.39 holds in weak form (`dlmf_1_18_39`), and 1.18.40 is the expansion in `L²[0, π]`
(`dlmf_1_18_40`, with the coefficient formula `dlmf_1_18_40_coeff`). The sine and cosine
expansions of 1.8.1–1.8.2 follow from Cases 1–2 (`hasSum_sinVec`, `hasSum_cosVec`).

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory Real
open scoped InnerProductSpace ComplexConjugate

namespace Azurite.DLMF

/-! ### Trigonometric integrals on `[0, π]` -/

theorem integral_cos_int_mul_zero_pi {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..π, Real.cos (k * x) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk', integral_cos, mul_zero,
    Real.sin_zero, sub_zero, Real.sin_int_mul_pi, smul_zero]

theorem integral_cos_int_mul_zero_pi' (k : ℤ) :
    ∫ x in (0 : ℝ)..π, Real.cos (k * x) = if k = 0 then π else 0 := by
  split_ifs with hk
  · simp [hk]
  · exact integral_cos_int_mul_zero_pi hk

/-- `∫_0^π sin(nx) sin(mx) dx = (π/2) δ_{n,m}` for `n, m ≥ 1`. -/
theorem integral_sin_mul_sin_pi (n m : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.sin ((n + 1 : ℕ) * x) * Real.sin ((m + 1 : ℕ) * x) =
      if n = m then π / 2 else 0 := by
  have e : ∀ x : ℝ, Real.sin ((n + 1 : ℕ) * x) * Real.sin ((m + 1 : ℕ) * x) =
      (Real.cos (((n : ℤ) - m : ℤ) * x) - Real.cos (((n + m + 2 : ℕ) : ℤ) * x)) / 2 := fun x => by
    have h1 := Real.cos_sub ((n + 1 : ℕ) * x) ((m + 1 : ℕ) * x)
    have h2 := Real.cos_add ((n + 1 : ℕ) * x) ((m + 1 : ℕ) * x)
    have a1 : (((n : ℤ) - m : ℤ) : ℝ) * x = (n + 1 : ℕ) * x - (m + 1 : ℕ) * x := by push_cast; ring
    have a2 : (((n + m + 2 : ℕ) : ℤ) : ℝ) * x = (n + 1 : ℕ) * x + (m + 1 : ℕ) * x := by
      push_cast; ring
    rw [a1, a2, h1, h2]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_cos_int_mul_zero_pi (by omega : ((n + m + 2 : ℕ) : ℤ) ≠ 0),
    integral_cos_int_mul_zero_pi']
  split_ifs with h1 h2 h2 <;> first | omega | simp_all

/-- `∫_0^π cos(nx) cos(mx) dx = π` for `n = m = 0`, `π/2` for `n = m ≥ 1`, else `0`. -/
theorem integral_cos_mul_cos_pi (n m : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.cos (n * x) * Real.cos (m * x) =
      if n = m then (if n = 0 then π else π / 2) else 0 := by
  have e : ∀ x : ℝ, Real.cos (n * x) * Real.cos (m * x) =
      (Real.cos (((n : ℤ) - m : ℤ) * x) + Real.cos (((n + m : ℕ) : ℤ) * x)) / 2 := fun x => by
    have h1 := Real.cos_sub (n * x) (m * x)
    have h2 := Real.cos_add (n * x) (m * x)
    have a1 : (((n : ℤ) - m : ℤ) : ℝ) * x = n * x - m * x := by push_cast; ring
    have a2 : (((n + m : ℕ) : ℤ) : ℝ) * x = n * x + m * x := by push_cast; ring
    rw [a1, a2, h1, h2]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_cos_int_mul_zero_pi', integral_cos_int_mul_zero_pi']
  split_ifs <;> first | omega | (simp_all; try ring)

/-- `∫_0^π e^{2inx} conj(e^{2imx}) dx = π δ_{n,m}`. -/
theorem integral_exp_mul_conj_pi (n m : ℤ) :
    ∫ x in (0 : ℝ)..π, Complex.exp (2 * Complex.I * n * x) *
      conj (Complex.exp (2 * Complex.I * m * x)) = if n = m then (π : ℂ) else 0 := by
  have e : ∀ x : ℝ, Complex.exp (2 * Complex.I * n * x) *
      conj (Complex.exp (2 * Complex.I * m * x)) =
        Complex.exp ((2 * Complex.I * ((n - m : ℤ) : ℂ)) * x) := fun x => by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
    push_cast
    ring
  simp_rw [e]
  split_ifs with h
  · simp [h]
  · have hc : 2 * Complex.I * ((n - m : ℤ) : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) ?_
      exact_mod_cast sub_ne_zero.mpr h
    have h1 : Complex.exp (2 * Complex.I * ((n - m : ℤ) : ℂ) * π) = 1 := by
      rw [show 2 * Complex.I * ((n - m : ℤ) : ℂ) * π = ((n - m : ℤ) : ℂ) * (2 * π * Complex.I) by
        ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [integral_exp_mul_complex hc, h1]
    simp

/-! ### `L²[0, π]` -/

/-- `L²[0, π]`. -/
noncomputable abbrev L2pi := Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) π))

theorem setIntegral_Icc_zero_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) : ∫ x in Icc 0 π, F x = ∫ x in (0 : ℝ)..π, F x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le Real.pi_pos.le]

theorem memLp_Icc_of_continuous {φ : ℝ → ℂ} (hφ : Continuous φ) :
    MemLp φ 2 (volume.restrict (Icc 0 π)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 π) hφ.continuousOn
  exact MemLp.of_bound hφ.aestronglyMeasurable C (ae_restrict_of_forall_mem measurableSet_Icc hC)

theorem dlmfInner_toLp (f : L2pi) {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc 0 π))) :
    dlmfInner f (hφ.toLp φ) = ∫ x in (0 : ℝ)..π, f x * conj (φ x) := by
  rw [dlmfInner_Lp_eq, ← setIntegral_Icc_zero_pi]
  refine integral_congr_ae ?_
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx]

theorem norm_sq_L2pi (f : L2pi) : ‖f‖ ^ 2 = ∫ x in (0 : ℝ)..π, ‖f x‖ ^ 2 := by
  rw [← integral_norm_sq_Lp, setIntegral_Icc_zero_pi]

theorem memLp_Ioc_of_L2pi (f : L2pi) : MemLp f 2 (volume.restrict (Ioc 0 π)) :=
  (Lp.memLp f).mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

/-! ### The three families of eigenfunctions -/

/-- DLMF 1.18.36 (Case 1, `φ(0) = φ(π) = 0`): `φ_sin(n, x) = √(2/π) sin(nx)`, `n = 1, 2, …`
(indexed here from `0` as `n + 1`). -/
noncomputable def sinFun (n : ℕ) (x : ℝ) : ℂ := ((√(2 / π) * Real.sin ((n + 1 : ℕ) * x) : ℝ) : ℂ)

/-- The normalizing constants of Case 2: `1/√π` for `n = 0`, `√(2/π)` for `n ≥ 1`. -/
noncomputable def cosNorm (n : ℕ) : ℝ := if n = 0 then 1 / √π else √(2 / π)

/-- DLMF 1.18.37 (Case 2, `φ′(0) = φ′(π) = 0`): `φ_cos(0, x) = 1/√π`,
`φ_cos(n, x) = √(2/π) cos(nx)`. -/
noncomputable def cosFun (n : ℕ) (x : ℝ) : ℂ := ((cosNorm n * Real.cos (n * x) : ℝ) : ℂ)

/-- DLMF 1.18.38 (Case 3, periodic): `φ_exp(n, x) = e^{2inx}/√π`, `n ∈ ℤ`. -/
noncomputable def expFun (n : ℤ) (x : ℝ) : ℂ :=
  ((1 / √π : ℝ) : ℂ) * Complex.exp (2 * Complex.I * n * x)

theorem dlmf_1_18_37 (n : ℕ) (x : ℝ) :
    cosFun 0 x = ((1 / √π : ℝ) : ℂ) ∧
      (n ≠ 0 → cosFun n x = ((√(2 / π) * Real.cos (n * x) : ℝ) : ℂ)) := by
  refine ⟨by simp [cosFun, cosNorm], fun hn => by simp [cosFun, cosNorm, hn]⟩

theorem continuous_sinFun (n : ℕ) : Continuous (sinFun n) := by unfold sinFun; fun_prop
theorem continuous_cosFun (n : ℕ) : Continuous (cosFun n) := by unfold cosFun; fun_prop
theorem continuous_expFun (n : ℤ) : Continuous (expFun n) := by unfold expFun; fun_prop

theorem hasDerivAt_ofReal_mul_sin (c k x : ℝ) :
    HasDerivAt (fun y : ℝ => ((c * Real.sin (k * y) : ℝ) : ℂ))
      ((c * (k * Real.cos (k * x)) : ℝ) : ℂ) x := by
  have h : HasDerivAt (fun y => c * Real.sin (k * y)) (c * (k * Real.cos (k * x))) x := by
    convert ((Real.hasDerivAt_sin (k * x)).comp x ((hasDerivAt_id x).const_mul k)).const_mul c
      using 1
    · rfl
    · ring
  exact h.ofReal_comp

theorem hasDerivAt_ofReal_mul_cos (c k x : ℝ) :
    HasDerivAt (fun y : ℝ => ((c * Real.cos (k * y) : ℝ) : ℂ))
      ((c * (-(k * Real.sin (k * x))) : ℝ) : ℂ) x := by
  have h : HasDerivAt (fun y => c * Real.cos (k * y)) (c * (-(k * Real.sin (k * x)))) x := by
    convert ((Real.hasDerivAt_cos (k * x)).comp x ((hasDerivAt_id x).const_mul k)).const_mul c
      using 1
    · rfl
    · ring
  exact h.ofReal_comp

/-- DLMF 1.18.36: `−φ″ = n²φ` and `φ(0) = φ(π) = 0`. -/
theorem dlmf_1_18_36 (n : ℕ) :
    (∀ x, -deriv (deriv (sinFun n)) x = (((n + 1 : ℕ) : ℝ) ^ 2 : ℝ) * sinFun n x) ∧
      sinFun n 0 = 0 ∧ sinFun n π = 0 := by
  set k : ℝ := ((n + 1 : ℕ) : ℝ)
  have h1 : deriv (sinFun n) = fun x => ((√(2 / π) * k * Real.cos (k * x) : ℝ) : ℂ) := by
    funext x
    rw [show sinFun n = fun y : ℝ => ((√(2 / π) * Real.sin (k * y) : ℝ) : ℂ) from rfl,
      (hasDerivAt_ofReal_mul_sin _ k x).deriv]
    congr 1; ring
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [h1, (hasDerivAt_ofReal_mul_cos (√(2 / π) * k) k x).deriv]
    show _ = ((k ^ 2 : ℝ) : ℂ) * ((√(2 / π) * Real.sin (k * x) : ℝ) : ℂ)
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul]
    congr 1; ring
  · simp [sinFun]
  · simp only [sinFun]
    rw [Real.sin_nat_mul_pi, mul_zero, Complex.ofReal_zero]

/-- DLMF 1.18.37: `−φ″ = n²φ` and `φ′(0) = φ′(π) = 0`. -/
theorem dlmf_1_18_37_eigen (n : ℕ) :
    (∀ x, -deriv (deriv (cosFun n)) x = ((n : ℝ) ^ 2 : ℝ) * cosFun n x) ∧
      deriv (cosFun n) 0 = 0 ∧ deriv (cosFun n) π = 0 := by
  have h1 : deriv (cosFun n) = fun x => ((cosNorm n * (-(n * Real.sin (n * x))) : ℝ) : ℂ) := by
    funext x
    exact (hasDerivAt_ofReal_mul_cos (cosNorm n) n x).deriv
  refine ⟨fun x => ?_, ?_, ?_⟩
  · have h2 : HasDerivAt (fun x => ((cosNorm n * (-(n * Real.sin (n * x))) : ℝ) : ℂ))
        ((-(cosNorm n * n) * (n * Real.cos (n * x)) : ℝ) : ℂ) x := by
      have := hasDerivAt_ofReal_mul_sin (-(cosNorm n * n)) n x
      convert this using 1
      funext y; congr 1; ring
    rw [h1, h2.deriv]
    show _ = (((n : ℝ) ^ 2 : ℝ) : ℂ) * ((cosNorm n * Real.cos (n * x) : ℝ) : ℂ)
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul]
    congr 1; ring
  · rw [h1]; simp
  · rw [h1]; simp [Real.sin_nat_mul_pi]

/-- DLMF 1.18.38: `−φ″ = 4n²φ`, `φ(0) = φ(π)` and `φ′(0) = φ′(π)`. -/
theorem dlmf_1_18_38 (n : ℤ) :
    (∀ x, -deriv (deriv (expFun n)) x = ((4 * n ^ 2 : ℝ) : ℂ) * expFun n x) ∧
      expFun n 0 = expFun n π ∧ deriv (expFun n) 0 = deriv (expFun n) π := by
  set c : ℂ := 2 * Complex.I * n
  have hd : ∀ (a : ℂ) (x : ℝ), HasDerivAt (fun y : ℝ => a * Complex.exp (c * y))
      (a * (c * Complex.exp (c * x))) x := fun a x => by
    have := ((hasDerivAt_id (x : ℂ)).const_mul c).cexp.comp_ofReal (z := x)
    convert this.const_mul a using 1
    · funext y; simp
    · simp only [id, mul_one]; ring
  have he : ∀ y : ℝ, expFun n y = ((1 / √π : ℝ) : ℂ) * Complex.exp (c * y) := fun y => by
    simp only [expFun, c]
  have hf : expFun n = fun y : ℝ => ((1 / √π : ℝ) : ℂ) * Complex.exp (c * y) := funext he
  have h1 : deriv (expFun n) = fun y : ℝ => ((1 / √π : ℝ) : ℂ) * c * Complex.exp (c * y) := by
    funext y; rw [hf, (hd _ y).deriv]; ring
  have hπ : Complex.exp (c * π) = 1 := by
    rw [show c * π = (n : ℂ) * (2 * π * Complex.I) by simp only [c]; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [h1, (hd _ x).deriv, he]
    simp only [c]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · rw [he, he, hπ]; simp
  · rw [h1]; simp [hπ]

/-! ### Orthonormality (1.18.29) -/

noncomputable def sinVec (n : ℕ) : L2pi := (memLp_Icc_of_continuous (continuous_sinFun n)).toLp _
noncomputable def cosVec (n : ℕ) : L2pi := (memLp_Icc_of_continuous (continuous_cosFun n)).toLp _
noncomputable def expVec (n : ℤ) : L2pi := (memLp_Icc_of_continuous (continuous_expFun n)).toLp _

theorem dlmfInner_sinVec (f : L2pi) (n : ℕ) :
    dlmfInner f (sinVec n) = ∫ x in (0 : ℝ)..π, f x * conj (sinFun n x) := dlmfInner_toLp f _

theorem dlmfInner_cosVec (f : L2pi) (n : ℕ) :
    dlmfInner f (cosVec n) = ∫ x in (0 : ℝ)..π, f x * conj (cosFun n x) := dlmfInner_toLp f _

theorem dlmfInner_expVec (f : L2pi) (n : ℤ) :
    dlmfInner f (expVec n) = ∫ x in (0 : ℝ)..π, f x * conj (expFun n x) := dlmfInner_toLp f _

theorem integral_toLp_mul_conj {φ ψ : ℝ → ℂ} (hφ : Continuous φ) :
    ∫ x in (0 : ℝ)..π, (memLp_Icc_of_continuous hφ).toLp φ x * ψ x =
      ∫ x in (0 : ℝ)..π, φ x * ψ x := by
  rw [← setIntegral_Icc_zero_pi, ← setIntegral_Icc_zero_pi]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_Icc_of_continuous hφ).coeFn_toLp] with x hx
  rw [hx]

theorem orthonormal_sinVec : Orthonormal ℂ sinVec := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [← dlmfInner, dlmfInner_sinVec, sinVec, integral_toLp_mul_conj (continuous_sinFun m)]
  have e : ∀ x : ℝ, sinFun m x * conj (sinFun n x) =
      (((2 / π) * (Real.sin ((m + 1 : ℕ) * x) * Real.sin ((n + 1 : ℕ) * x)) : ℝ) : ℂ) := fun x => by
    simp only [sinFun, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    congr 1
    have : √(2 / π) * √(2 / π) = 2 / π := Real.mul_self_sqrt (by positivity)
    rw [mul_mul_mul_comm, this]
  simp_rw [e]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    integral_sin_mul_sin_pi]
  have hπ := Real.pi_pos
  by_cases h : n = m
  · subst h
    simp only [ite_true, show 2 / π * (π / 2) = (1 : ℝ) by field_simp]
    simp
  · simp only [h, Ne.symm h, ite_false]
    simp

theorem orthonormal_cosVec : Orthonormal ℂ cosVec := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [← dlmfInner, dlmfInner_cosVec, cosVec, integral_toLp_mul_conj (continuous_cosFun m)]
  have e : ∀ x : ℝ, cosFun m x * conj (cosFun n x) =
      ((cosNorm m * cosNorm n * (Real.cos (m * x) * Real.cos (n * x)) : ℝ) : ℂ) := fun x => by
    simp only [cosFun, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    congr 1
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    integral_cos_mul_cos_pi]
  have hπ := Real.pi_pos
  have hs : √π * √π = π := Real.mul_self_sqrt hπ.le
  have hs2 : √(2 / π) * √(2 / π) = 2 / π := Real.mul_self_sqrt (by positivity)
  have hsp : 0 < √π := Real.sqrt_pos.mpr hπ
  by_cases h : n = m
  · subst h
    simp only [ite_true]
    by_cases hn : n = 0
    · have : 1 / √π * (1 / √π) * π = 1 := by
        rw [div_mul_div_comm, one_mul, hs, div_mul_cancel₀ _ hπ.ne']
      simp only [hn, cosNorm, ite_true, this, Complex.ofReal_one]
    · have : √(2 / π) * √(2 / π) * (π / 2) = 1 := by rw [hs2]; field_simp
      simp only [hn, cosNorm, ite_false, this, Complex.ofReal_one]
  · simp only [h, Ne.symm h, ite_false]
    simp

theorem orthonormal_expVec : Orthonormal ℂ expVec := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [← dlmfInner, dlmfInner_expVec, expVec, integral_toLp_mul_conj (continuous_expFun m)]
  have e : ∀ x : ℝ, expFun m x * conj (expFun n x) = ((1 / π : ℝ) : ℂ) *
      (Complex.exp (2 * Complex.I * m * x) * conj (Complex.exp (2 * Complex.I * n * x))) :=
    fun x => by
      simp only [expFun, map_mul, Complex.conj_ofReal]
      have : (1 / √π) * (1 / √π) = 1 / π := by
        rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt Real.pi_pos.le]
      rw [show ((1 / π : ℝ) : ℂ) = ((1 / √π : ℝ) : ℂ) * ((1 / √π : ℝ) : ℂ) by
        rw [← Complex.ofReal_mul, this]]
      ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_conj_pi]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases h : n = m
  · subst h
    simp only [ite_true]
    push_cast
    field_simp
  · simp only [h, Ne.symm h, ite_false]
    simp

/-! ### Completeness: Case 3 (periodic) via Fourier series of period `π` -/

theorem conj_expFun (n : ℤ) (x : ℝ) :
    conj (expFun n x) = ((1 / √π : ℝ) : ℂ) * Complex.exp (-(2 * Complex.I * n * x)) := by
  simp only [expFun, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_ofNat,
    Complex.conj_I, map_intCast]
  congr 2
  ring

/-- DLMF 1.18.40: `f̂(λₙ) = (1/√π) ∫_0^π f(y) e^{−2iny} dy = ⟨f, φ_exp(n)⟩`. -/
theorem dlmf_1_18_40_coeff (f : L2pi) (n : ℤ) :
    dlmfInner f (expVec n) =
      ((1 / √π : ℝ) : ℂ) * ∫ y in (0 : ℝ)..π, f y * Complex.exp (-(2 * Complex.I * n * y)) := by
  rw [dlmfInner_expVec, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [conj_expFun]
  ring

/-- The coefficients are those of the Fourier series of period `π` (1.8.3–1.8.4):
`⟨f, φ_exp(n)⟩ = √π cₙ`. -/
theorem dlmfInner_expVec_eq_fourierCoeffOn (f : L2pi) (n : ℤ) :
    dlmfInner f (expVec n) = ((√π : ℝ) : ℂ) * fourierCoeffOn Real.pi_pos f n := by
  rw [dlmf_1_18_40_coeff, fourierCoeffOn_eq_integral, Complex.real_smul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hexp : fourier (-n) (x : AddCircle (π - 0)) = Complex.exp (-(2 * Complex.I * n * x)) := by
    rw [fourier_coe_apply]
    congr 1
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [sub_zero]
    push_cast
    field_simp
  simp only [hexp, smul_eq_mul]
  have hs : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hsp : (√π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsr : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have : ((1 / √π : ℝ) : ℂ) = ((√π : ℝ) : ℂ) * ((1 / (π - 0) : ℝ) : ℂ) := by
    rw [sub_zero, ← Complex.ofReal_mul]
    congr 1
    rw [mul_one_div, div_eq_div_iff hsr.ne' Real.pi_ne_zero, one_mul, hs]
  rw [this]
  ring

/-- Parseval for the periodic eigenfunctions. -/
theorem hasSum_norm_sq_expVec (f : L2pi) :
    HasSum (fun n : ℤ => ‖dlmfInner f (expVec n)‖ ^ 2) (‖f‖ ^ 2) := by
  have h := (hasSum_sq_fourierCoeffOn Real.pi_pos (memLp_Ioc_of_L2pi f)).mul_left π
  rw [norm_sq_L2pi]
  convert h using 1
  · funext n
    rw [dlmfInner_expVec_eq_fourierCoeffOn, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt Real.pi_pos.le]
  · rw [sub_zero, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]

/-- Case 3: the periodic eigenfunctions form a complete orthonormal set (a Hilbert basis). -/
theorem exists_hilbertBasis_expVec : ∃ b : HilbertBasis ℤ ℂ L2pi, ⇑b = expVec :=
  (isCompleteOrthonormal_iff expVec).mp
    ⟨orthonormal_expVec, fun f => (hasSum_norm_sq_expVec f).tsum_eq⟩

/-! ### Completeness: Cases 1, 2 via odd and even extensions to `[−π, π]` -/

/-- The odd extension of `f` from `(0, π]` (with value `0` at `0`). -/
noncomputable def oddExtPi (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then f x else if x < 0 then -f (-x) else 0

theorem oddExtPi_neg (f : ℝ → ℂ) (x : ℝ) : oddExtPi f (-x) = -oddExtPi f x := by
  unfold oddExtPi
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [h, not_lt.mpr h.le, neg_pos.mpr h]
  · simp
  · simp [h, not_lt.mpr h.le, neg_neg_iff_pos.mpr h]

theorem norm_oddExtPi_le (f : ℝ → ℂ) (x : ℝ) : ‖oddExtPi f x‖ ≤ ‖f |x|‖ := by
  unfold oddExtPi
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [not_lt.mpr h.le, h, abs_of_neg h]
  · simp
  · simp [h, abs_of_pos h]

theorem integral_neg_pi_pi_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G H : ℝ → E} (hG : IntervalIntegrable G volume (-π) π) (h1 : ∀ x ∈ Ioc 0 π, G x = H x)
    (h2 : ∀ x ∈ Ioc 0 π, G (-x) = H x) :
    ∫ x in (-π)..π, G x = (2 : ℝ) • ∫ x in (0 : ℝ)..π, H x := by
  have hπ := Real.pi_pos
  have hm : (0 : ℝ) ∈ uIcc (-π) π := by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, hπ.le⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hG.mono_set (uIcc_subset_uIcc_left hm))
    (hG.mono_set (uIcc_subset_uIcc_right hm))]
  have e1 : ∫ x in (-π)..0, G x = ∫ x in (0 : ℝ)..π, G (-x) := by
    rw [intervalIntegral.integral_comp_neg, neg_zero]
  have e2 : ∫ x in (0 : ℝ)..π, G (-x) = ∫ x in (0 : ℝ)..π, H x :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => by
      rw [uIoc_of_le hπ.le] at hx; exact h2 x hx)
  have e3 : ∫ x in (0 : ℝ)..π, G x = ∫ x in (0 : ℝ)..π, H x :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => by
      rw [uIoc_of_le hπ.le] at hx; exact h1 x hx)
  rw [e1, e2, e3, two_smul]

theorem integrableOn_norm_sq_abs (f : L2pi) :
    IntervalIntegrable (fun x => ‖f |x|‖ ^ 2) volume (-π) π := by
  have hπ := Real.pi_pos
  have hi : IntegrableOn (fun x => ‖f x‖ ^ 2) (Ioc 0 π) :=
    (memLp_two_iff_integrable_sq_norm (memLp_Ioc_of_L2pi f).aestronglyMeasurable).mp
      (memLp_Ioc_of_L2pi f)
  have hR : IntervalIntegrable (fun x => ‖f |x|‖ ^ 2) volume 0 π :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le).mpr
      (hi.congr_fun (fun x hx => by simp only [abs_of_pos hx.1]) measurableSet_Ioc)
  have hL : IntervalIntegrable (fun x => ‖f |x|‖ ^ 2) volume (-π) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simp only [neg_neg, neg_zero, abs_neg]
    exact hR.symm
  exact hL.trans hR

theorem memLp_ext_of_bound (f : L2pi) {g : ℝ → ℂ} (hg : StronglyMeasurable g)
    (hb : ∀ x, ‖g x‖ ≤ ‖f |x|‖) : MemLp g 2 (volume.restrict (Ioc (-π) π)) := by
  have hπ := Real.pi_pos
  refine (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr ?_
  have hI : IntegrableOn (fun x => ‖f |x|‖ ^ 2) (Ioc (-π) π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp (integrableOn_norm_sq_abs f)
  refine hI.mono' (hg.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2

theorem stronglyMeasurable_oddExtPi (f : L2pi) : StronglyMeasurable (oddExtPi f) := by
  have hf := Lp.stronglyMeasurable f
  exact StronglyMeasurable.ite measurableSet_Ioi hf
    (StronglyMeasurable.ite measurableSet_Iio (hf.comp_measurable measurable_neg).neg
      stronglyMeasurable_const)

theorem integral_norm_sq_ext (f : L2pi) {g : ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (Ioc (-π) π)))
    (h1 : ∀ x ∈ Ioc 0 π, ‖g x‖ = ‖f x‖) (h2 : ∀ x ∈ Ioc 0 π, ‖g (-x)‖ = ‖f x‖) :
    ∫ x in (-π)..π, ‖g x‖ ^ 2 = 2 * ∫ x in (0 : ℝ)..π, ‖f x‖ ^ 2 := by
  have hi : IntervalIntegrable (fun x => ‖g x‖ ^ 2) volume (-π) π :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).mpr
      ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
  rw [integral_neg_pi_pi_eq hi (fun x hx => by rw [h1 x hx]) (fun x hx => by rw [h2 x hx]),
    smul_eq_mul]

/-- Parseval for the Dirichlet eigenfunctions. -/
theorem hasSum_norm_sq_sinVec (f : L2pi) :
    HasSum (fun n : ℕ => ‖dlmfInner f (sinVec n)‖ ^ 2) (‖f‖ ^ 2) := by
  have hπ := Real.pi_pos
  set g := oddExtPi f
  have hg : MemLp g 2 (volume.restrict (Ioc (-π) π)) :=
    memLp_ext_of_bound f (stronglyMeasurable_oddExtPi f) (norm_oddExtPi_le f)
  have hA : ∀ n, fourierA g n = 0 := dlmf_1_8_i_odd (oddExtPi_neg f)
  have hpos : ∀ x ∈ Ioc 0 π, g x = f x := fun x hx => by simp [g, oddExtPi, hx.1]
  have hneg : ∀ x ∈ Ioc 0 π, g (-x) = -f x := fun x hx => by
    show oddExtPi f (-x) = _
    rw [oddExtPi_neg, show oddExtPi f x = f x from hpos x hx]
  have hB : ∀ n : ℕ, fourierB g (n + 1) = ((2 / π : ℝ) : ℂ) *
      ∫ x in (0 : ℝ)..π, f x * (Real.sin ((n + 1 : ℕ) * x) : ℂ) := fun n => by
    rw [fourierB, integral_neg_pi_pi_eq
      (intervalIntegrable_mul_sin (intervalIntegrable_of_memLp hg) _)
      (fun x hx => by rw [hpos x hx]) (fun x hx => by
        rw [hneg x hx, mul_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul_neg])]
    rw [Complex.real_smul, Complex.real_smul]
    push_cast; ring
  have hinner : ∀ n : ℕ, dlmfInner f (sinVec n) = ((√(2 / π) * (π / 2) : ℝ) : ℂ) *
      fourierB g (n + 1) := fun n => by
    rw [hB, dlmfInner_sinVec, ← mul_assoc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [sinFun, Complex.conj_ofReal]
    have : π / 2 * (2 / π) = (1 : ℝ) := by field_simp
    push_cast
    rw [show (√(2 / π) : ℂ) * (π / 2) * (2 / π) = √(2 / π) * (((π / 2 * (2 / π)) : ℝ) : ℂ) by
      push_cast; ring, this]
    push_cast; ring
  have hP := dlmf_1_8_5 hg
  simp only [hA, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
    zero_div, sub_zero] at hP
  rw [integral_norm_sq_ext f hg (fun x hx => by rw [hpos x hx])
    (fun x hx => by rw [hneg x hx, norm_neg])] at hP
  have h2 := hP.mul_left (π / 2)
  rw [norm_sq_L2pi]
  convert h2 using 1
  · funext n
    rw [hinner, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow,
      mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  · field_simp

/-- Case 1: the Dirichlet eigenfunctions form a complete orthonormal set. -/
theorem exists_hilbertBasis_sinVec : ∃ b : HilbertBasis ℕ ℂ L2pi, ⇑b = sinVec :=
  (isCompleteOrthonormal_iff sinVec).mp
    ⟨orthonormal_sinVec, fun f => (hasSum_norm_sq_sinVec f).tsum_eq⟩

/-- Parseval for the Neumann eigenfunctions. -/
theorem hasSum_norm_sq_cosVec (f : L2pi) :
    HasSum (fun n : ℕ => ‖dlmfInner f (cosVec n)‖ ^ 2) (‖f‖ ^ 2) := by
  have hπ := Real.pi_pos
  set g : ℝ → ℂ := fun x => f |x|
  have hgs : StronglyMeasurable g :=
    (Lp.stronglyMeasurable f).comp_measurable continuous_abs.measurable
  have hg : MemLp g 2 (volume.restrict (Ioc (-π) π)) :=
    memLp_ext_of_bound f hgs fun x => le_rfl
  have hBz : ∀ n, fourierB g n = 0 := dlmf_1_8_i_even fun x => by simp [g]
  have hpos : ∀ x ∈ Ioc 0 π, g x = f x := fun x hx => by simp [g, abs_of_pos hx.1]
  have hneg : ∀ x ∈ Ioc 0 π, g (-x) = f x := fun x hx => by simp [g, abs_of_pos hx.1]
  have hA : ∀ n : ℕ, fourierA g n = ((2 / π : ℝ) : ℂ) *
      ∫ x in (0 : ℝ)..π, f x * (Real.cos (n * x) : ℂ) := fun n => by
    rw [fourierA, integral_neg_pi_pi_eq
      (intervalIntegrable_mul_cos (intervalIntegrable_of_memLp hg) _)
      (fun x hx => by rw [hpos x hx]) (fun x hx => by
        rw [hneg x hx, mul_neg, Real.cos_neg])]
    rw [Complex.real_smul, Complex.real_smul]
    push_cast; ring
  have hinner : ∀ n : ℕ, dlmfInner f (cosVec n) = ((cosNorm n * (π / 2) : ℝ) : ℂ) *
      fourierA g n := fun n => by
    rw [hA, dlmfInner_cosVec, ← mul_assoc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [cosFun, Complex.conj_ofReal]
    have : π / 2 * (2 / π) = (1 : ℝ) := by field_simp
    push_cast
    rw [show (cosNorm n : ℂ) * (π / 2) * (2 / π) = cosNorm n * (((π / 2 * (2 / π)) : ℝ) : ℂ) by
      push_cast; ring, this]
    push_cast; ring
  have hP := dlmf_1_8_5 hg
  simp only [hBz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at hP
  rw [integral_norm_sq_ext f hg (fun x hx => by rw [hpos x hx])
    (fun x hx => by rw [hneg x hx])] at hP
  have h2 := hP.mul_left (π / 2)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton]
  rw [norm_sq_L2pi]
  have hs2 : √(2 / π) ^ 2 = 2 / π := Real.sq_sqrt (by positivity)
  have hs1 : (1 / √π) ^ 2 = 1 / π := by rw [div_pow, Real.sq_sqrt hπ.le, one_pow]
  convert h2 using 1
  · funext n
    rw [hinner, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by
      unfold cosNorm; split_ifs <;> positivity), mul_pow, mul_pow]
    simp only [cosNorm, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, hs2]
    field_simp
  · rw [hinner, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by
      unfold cosNorm; positivity), mul_pow, mul_pow]
    simp only [cosNorm, ite_true, hs1]
    field_simp

/-- Case 2: the Neumann eigenfunctions form a complete orthonormal set. -/
theorem exists_hilbertBasis_cosVec : ∃ b : HilbertBasis ℕ ℂ L2pi, ⇑b = cosVec :=
  (isCompleteOrthonormal_iff cosVec).mp
    ⟨orthonormal_cosVec, fun f => (hasSum_norm_sq_cosVec f).tsum_eq⟩

/-! ### Expansions (1.18.39–1.18.40) -/

theorem hasSum_of_hilbertBasis {ι : Type*} {v : ι → L2pi} (hb : ∃ b : HilbertBasis ι ℂ L2pi, ⇑b = v)
    (f : L2pi) : HasSum (fun n => dlmfInner f (v n) • v n) f := by
  obtain ⟨b, rfl⟩ := hb
  have := b.hasSum_repr f
  convert this using 1
  funext n
  rw [b.repr_apply_apply]
  rfl

/-- DLMF 1.18.38: for `n ≠ 0` the eigenvalue `4n²` has multiplicity two: `φ_exp(n)` and
`φ_exp(−n)` are orthogonal eigenfunctions with the same eigenvalue. -/
theorem dlmf_1_18_38_multiplicity {n : ℤ} (hn : n ≠ 0) :
    dlmfInner (expVec n) (expVec (-n)) = 0 ∧ (4 * n ^ 2 : ℝ) = 4 * ((-n : ℤ) : ℝ) ^ 2 := by
  refine ⟨?_, by push_cast; ring⟩
  have hne : ¬ -n = n := by omega
  rw [dlmfInner, orthonormal_iff_ite.mp orthonormal_expVec]
  simp only [hne, ite_false]

/-- DLMF 1.18.39, `δ(x − y) = (1/π) ∑ₙ e^{2in(x−y)}`, in weak form: for `f, g ∈ L²[0, π]`,
`∑ₙ ⟨f, φ_exp(n)⟩ conj⟨g, φ_exp(n)⟩ = ∫_0^π f conj g`. -/
theorem dlmf_1_18_39 (f g : L2pi) :
    HasSum (fun n : ℤ => dlmfInner f (expVec n) * conj (dlmfInner g (expVec n)))
      (∫ x in (0 : ℝ)..π, f x * conj (g x)) := by
  obtain ⟨b, hb⟩ := exists_hilbertBasis_expVec
  have h := b.hasSum_inner_mul_inner g f
  have e : ∫ x in (0 : ℝ)..π, f x * conj (g x) = ⟪g, f⟫_ℂ := by
    rw [← setIntegral_Icc_zero_pi, ← dlmfInner_Lp_eq, dlmfInner]
  rw [e]
  refine h.congr_fun fun n => ?_
  simp only [dlmfInner, ← hb]
  rw [← inner_conj_symm (b n) g, mul_comm, Complex.conj_conj]

/-- DLMF 1.18.40: the Fourier (eigenfunction) expansion `f = (1/√π) ∑ₙ e^{2inx} f̂(λₙ)`,
convergent in `L²[0, π]`, with `f̂(λₙ) = ⟨f, φ_exp(n)⟩` as in `dlmf_1_18_40_coeff`. -/
theorem dlmf_1_18_40 (f : L2pi) : HasSum (fun n : ℤ => dlmfInner f (expVec n) • expVec n) f :=
  hasSum_of_hilbertBasis exists_hilbertBasis_expVec f

/-- DLMF §1.18(v): the sine expansion (cf. 1.8.1–1.8.2), from Case 1. -/
theorem hasSum_sinVec (f : L2pi) : HasSum (fun n : ℕ => dlmfInner f (sinVec n) • sinVec n) f :=
  hasSum_of_hilbertBasis exists_hilbertBasis_sinVec f

/-- DLMF §1.18(v): the cosine expansion (cf. 1.8.1–1.8.2), from Case 2. -/
theorem hasSum_cosVec (f : L2pi) : HasSum (fun n : ℕ => dlmfInner f (cosVec n) • cosVec n) f :=
  hasSum_of_hilbertBasis exists_hilbertBasis_cosVec f

end Azurite.DLMF
