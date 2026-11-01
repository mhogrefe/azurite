/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3LaplaceMethod
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# DLMF §2.3(iii): power-series tools for Laplace's method

* `HasPowExpansion.polyEval`, `HasPowExpansion.subst`: expansions of `P(u(x))` and `g(u(x))`.
* `hasPowExpansion_of_hasFPowerSeriesAt`: an analytic function has its Taylor series as
  asymptotic expansion; with Mathlib's `Real.one_add_rpow_hasFPowerSeriesAt_zero` this gives
  `hasPowExpansion_one_add_rpow` (binomial series).
* `rpowPS P β`: the power series `P^β` for `P(0) > 0`, via `PowerSeries.binomialSeries`; its laws
  `rpowPS_mul`, `rpowPS_one`, `rpowPS_zero`, `rpowPS_inv`, `rpowPS_pow`, the derivative
  `derivative_rpowPS_mul` (`(P^β)′P = βP^βP′`, from `one_add_X_mul_derivative_binomialSeries`),
  and the asymptotic `HasPowExpansion.rpow`.
* `lagrange_inversion_second`: Lagrange–Bürmann inversion in the form
  `[wⁿ]H(Ψ) = [tⁿ]Hφⁿ(1 − tφ′/φ)`, from the first form of §2.2.
* `HasPowExpansion.change_var`: from `F ∼ A(y)` with `A = B(XÛ)` to `F ∼ B(yU)`.
-/

open Set Filter Topology Asymptotics PowerSeries

namespace Azurite.DLMF

section Compose

variable {α 𝕜 : Type*} [NontriviallyNormedField 𝕜] {l : Filter α} {y : α → 𝕜}

theorem trunc_eq_of_X_pow_dvd_sub {n : ℕ} {A B : 𝕜⟦X⟧} (h : X ^ n ∣ A - B) :
    trunc n A = trunc n B := by
  ext d
  simp only [coeff_trunc]
  split_ifs with hd
  · have := (X_pow_dvd_iff.mp h) d hd
    rwa [map_sub, sub_eq_zero] at this
  · rfl

/-- A polynomial in a function with an expansion. -/
theorem HasPowExpansion.polyEval (hy : Tendsto y l (𝓝 0)) {u : α → 𝕜} {U : 𝕜⟦X⟧}
    (hu : HasPowExpansion l y u U) (P : Polynomial 𝕜) :
    HasPowExpansion l y (fun x => P.eval (u x)) (Polynomial.aeval U P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact (hp.add hq).congr' (Eventually.of_forall fun x => by simp [Polynomial.eval_add])
  | monomial n c =>
    have e : algebraMap 𝕜 𝕜⟦X⟧ c = C c := by ext; simp [coeff_C]
    rw [Polynomial.aeval_monomial, e]
    exact ((hu.pow hy n).const_mul c).congr'
      (Eventually.of_forall fun x => by simp [Polynomial.eval_monomial])

theorem trunc_aeval_trunc {U : 𝕜⟦X⟧} (hU0 : constantCoeff U = 0) (G : 𝕜⟦X⟧) (n : ℕ) :
    trunc n (Polynomial.aeval U (trunc n G)) = trunc n (G.subst U) := by
  have hs : HasSubst U := HasSubst.of_constantCoeff_zero' hU0
  refine (trunc_eq_of_X_pow_dvd_sub ?_).symm
  obtain ⟨H, hH⟩ := X_pow_dvd_sub_trunc n G
  rw [← subst_coe hs, ← coe_substAlgHom hs, ← map_sub, hH, map_mul, map_pow,
    coe_substAlgHom hs, subst_X hs]
  exact (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hU0) n).mul_right _

/-- Composition: if `g(z) ∼ G(z)` as `z → 0` and `u ∼ U` with `U(0) = 0`, then
`g(u) ∼ G(U)`. -/
theorem HasPowExpansion.subst (hy : Tendsto y l (𝓝 0)) {g : 𝕜 → 𝕜} {G : 𝕜⟦X⟧}
    (hg : HasPowExpansion (𝓝 0) id g G) {u : α → 𝕜} {U : 𝕜⟦X⟧}
    (hu : HasPowExpansion l y u U) (hU0 : constantCoeff U = 0) :
    HasPowExpansion l y (fun x => g (u x)) (G.subst U) := fun n => by
  have hut : Tendsto u l (𝓝 0) := by simpa [hU0] using hu.tendsto hy
  have huO : u =O[l] y := by
    have h1 := hu 1
    simpa [trunc_one_left, hU0] using h1
  have hs : HasSubst U := HasSubst.of_constantCoeff_zero' hU0
  have e1 : (fun x => g (u x) - (trunc n G).eval (u x)) =O[l] fun x => y x ^ n :=
    ((hg n).comp_tendsto hut).trans (huO.pow n)
  have h2 := hu.polyEval hy (trunc n G) n
  have htr := trunc_aeval_trunc hU0 G n
  rw [htr] at h2
  exact (e1.add h2).congr_left fun x => by ring

/-- An analytic function has its Taylor series as asymptotic expansion at `0`. -/
theorem hasPowExpansion_of_hasFPowerSeriesAt {g : 𝕜 → 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} (hg : HasFPowerSeriesAt g p 0) :
    HasPowExpansion (𝓝 0) id g (mk fun n => p.coeff n) := fun n => by
  have h := hg.isBigO_sub_partialSum_pow n
  rw [← isBigO_norm_right]
  refine (h.congr_left fun z => ?_).congr_right fun z => by simp [norm_pow]
  simp only [zero_add, FormalMultilinearSeries.partialSum, eval_trunc_eq_sum, coeff_mk, id,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]

end Compose

theorem hasPowExpansion_const {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {y : α → 𝕜}
    (hy : Tendsto y l (𝓝 0)) (k : 𝕜) : HasPowExpansion l y (fun _ => k) (C k) := by
  have h := hasPowExpansion_polynomial hy (Polynomial.C k)
  rw [Polynomial.coe_C] at h
  exact h.congr' (Eventually.of_forall fun _ => Polynomial.eval_C)

/-! ### Fractional powers of power series -/

theorem ring_choose_succ_mul (β : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.choose β (n + 1) = (β - n) * Ring.choose β n := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose β (n + 1)
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose β n
  rw [← Polynomial.aeval_eq_smeval, ← Polynomial.eval_map_algebraMap, descPochhammer_map,
    descPochhammer_succ_eval] at h1
  rw [← Polynomial.aeval_eq_smeval, ← Polynomial.eval_map_algebraMap, descPochhammer_map] at h2
  rw [h2, nsmul_eq_mul, nsmul_eq_mul, Nat.factorial_succ] at h1
  push_cast at h1
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have : (n.factorial : ℝ) * (((n : ℝ) + 1) * Ring.choose β (n + 1)) =
      (n.factorial : ℝ) * ((β - n) * Ring.choose β n) := by linear_combination -h1
  exact mul_left_cancel₀ hf.ne' this

/-- `(1 + X) B′ = β B` for the binomial series `B = (1 + X)^β`. -/
theorem one_add_X_mul_derivative_binomialSeries (β : ℝ) :
    (1 + X) * d⁄dX (PowerSeries.binomialSeries ℝ β) =
      C β * PowerSeries.binomialSeries ℝ β := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_C_mul, coeff_derivative]
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
    have h := ring_choose_succ_mul β (n + 1)
    push_cast at h ⊢
    linarith

theorem coeff_binomialSeries_analytic (β : ℝ) (n : ℕ) :
    (_root_.binomialSeries ℝ β).coeff n = Ring.choose β n := by
  rw [FormalMultilinearSeries.coeff, binomialSeries_apply]
  simp [Pi.one_def, List.ofFn_const]

theorem hasPowExpansion_one_add_rpow (β : ℝ) :
    HasPowExpansion (𝓝 0) id (fun u : ℝ => (1 + u) ^ β) (PowerSeries.binomialSeries ℝ β) := by
  have h := hasPowExpansion_of_hasFPowerSeriesAt (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := β))
  convert h using 1
  ext n
  simp [coeff_binomialSeries_analytic]

/-- `P^β = P(0)^β (1 + (P/P(0) − 1))^β` for a real power series with `P(0) > 0`. -/
noncomputable def rpowPS (P : ℝ⟦X⟧) (β : ℝ) : ℝ⟦X⟧ :=
  C (constantCoeff P ^ β) *
    (PowerSeries.binomialSeries ℝ β).subst (C (constantCoeff P)⁻¹ * P - 1)

section RpowPS

variable {P : ℝ⟦X⟧} (hP : 0 < constantCoeff P)
include hP

theorem constantCoeff_rpowPS_sub_one :
    constantCoeff (C (constantCoeff P)⁻¹ * P - 1) = 0 := by
  simp [inv_mul_cancel₀ hP.ne']

theorem hasSubst_rpowPS : HasSubst (C (constantCoeff P)⁻¹ * P - 1) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_rpowPS_sub_one hP)

theorem constantCoeff_rpowPS (β : ℝ) : constantCoeff (rpowPS P β) = constantCoeff P ^ β := by
  rw [rpowPS, map_mul, constantCoeff_C]
  erw [constantCoeff_subst_of_constantCoeff_zero (constantCoeff_rpowPS_sub_one hP)]
  simp

theorem rpowPS_mul (β γ : ℝ) : rpowPS P β * rpowPS P γ = rpowPS P (β + γ) := by
  simp only [rpowPS]
  rw [PowerSeries.binomialSeries_add, subst_mul (hasSubst_rpowPS hP), Real.rpow_add hP, map_mul]
  ring

theorem rpowPS_one : rpowPS P 1 = P := by
  have hs := hasSubst_rpowPS hP
  have h1 : PowerSeries.binomialSeries ℝ (1 : ℝ) = 1 + X := by
    have := PowerSeries.binomialSeries_nat (R := ℝ) (A := ℝ) 1
    simpa using this
  rw [rpowPS, h1, Real.rpow_one, ← coe_substAlgHom hs, map_add, map_one, coe_substAlgHom hs,
    subst_X hs, add_sub_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hP.ne', map_one,
    one_mul]

theorem rpowPS_zero : rpowPS P 0 = 1 := by
  have hs := hasSubst_rpowPS hP
  have h0 : PowerSeries.binomialSeries ℝ (0 : ℝ) = 1 := by simp
  rw [rpowPS, h0, Real.rpow_zero, map_one, one_mul, ← coe_substAlgHom hs, map_one]

/-- `(P^β)′ P = β P^β P′`. -/
theorem derivative_rpowPS_mul (β : ℝ) :
    d⁄dX (rpowPS P β) * P = C β * rpowPS P β * d⁄dX P := by
  set c := constantCoeff P with hc
  set U := C c⁻¹ * P - 1 with hU
  have hs : HasSubst U := hasSubst_rpowPS hP
  have hPU : P = C c * (1 + U) := by
    rw [hU, add_sub_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hP.ne', map_one, one_mul]
  have hdU : d⁄dX U = C c⁻¹ * d⁄dX P := by
    rw [hU, map_sub, Derivation.leibniz, derivative_C, Derivation.map_one_eq_zero]
    simp
  set B := PowerSeries.binomialSeries ℝ β
  have key := congrArg (subst U) (one_add_X_mul_derivative_binomialSeries β)
  have e1 : ((1 + X) * d⁄dX B).subst U = (1 + U) * (d⁄dX B).subst U := by
    rw [subst_mul hs, ← coe_substAlgHom hs, map_add, map_one, coe_substAlgHom hs, subst_X hs]
  have e2 : (C β * B).subst U = C β * B.subst U := by
    rw [subst_mul hs, subst_C]; rfl
  rw [e1, e2] at key
  have hd : ∀ (k : ℝ) (F : ℝ⟦X⟧), d⁄dX (C k * F) = C k * d⁄dX F := fun k F => by
    rw [Derivation.leibniz, derivative_C]; simp
  have hcc : C c⁻¹ * C c = (1 : ℝ⟦X⟧) := by
    rw [← map_mul, inv_mul_cancel₀ hP.ne', map_one]
  simp only [rpowPS, ← hc, ← hU]
  rw [hd, derivative_subst hs, hdU]
  generalize d⁄dX P = Q
  rw [hPU]
  linear_combination (C (c ^ β) * Q * ((1 + U) * (d⁄dX B).subst U)) * hcc +
    (C (c ^ β) * Q) * key

theorem rpowPS_neg_mul (β : ℝ) : rpowPS P (-β) * rpowPS P β = 1 := by
  rw [rpowPS_mul hP, neg_add_cancel, rpowPS_zero hP]

theorem rpowPS_inv (β : ℝ) : (rpowPS P β)⁻¹ = rpowPS P (-β) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one, rpowPS_neg_mul hP]
  rw [constantCoeff_rpowPS hP]
  exact (Real.rpow_pos_of_pos hP _).ne'

theorem rpowPS_pow (β : ℝ) (n : ℕ) : rpowPS P β ^ n = rpowPS P (n * β) := by
  induction n with
  | zero => simp [rpowPS_zero hP]
  | succ n ih => rw [pow_succ, ih, rpowPS_mul hP]; push_cast; ring_nf

end RpowPS

/-- Fractional powers of a function with an expansion and positive leading term. -/
theorem HasPowExpansion.rpow {α : Type*} {l : Filter α} {y f : α → ℝ}
    (hy : Tendsto y l (𝓝 0)) {P : ℝ⟦X⟧} (hf : HasPowExpansion l y f P)
    (hP : 0 < constantCoeff P) (β : ℝ) :
    HasPowExpansion l y (fun x => f x ^ β) (rpowPS P β) := by
  set c := constantCoeff P with hc
  have hU := (hf.const_mul c⁻¹).sub (hasPowExpansion_const hy 1)
  rw [map_one] at hU
  have hcomp := (HasPowExpansion.subst hy (hasPowExpansion_one_add_rpow β) hU
    (constantCoeff_rpowPS_sub_one hP)).const_mul (c ^ β)
  refine hcomp.congr' ?_
  filter_upwards [(hf.tendsto hy).eventually (lt_mem_nhds hP)] with x hx
  simp only [Pi.sub_apply]
  rw [add_sub_cancel, ← Real.mul_rpow hP.le (by positivity), ← mul_assoc,
    mul_inv_cancel₀ hP.ne', one_mul]

/-! ### Transport to `ℂ` -/

theorem derivative_map_ofReal (A : ℝ⟦X⟧) :
    d⁄dX (map Complex.ofRealHom A) = map Complex.ofRealHom (d⁄dX A) := by
  ext n
  simp [coeff_derivative]

theorem HasPowExpansion.ofReal {α : Type*} {l : Filter α} {y f : α → ℝ} {A : ℝ⟦X⟧}
    (hf : HasPowExpansion l y f A) :
    HasPowExpansion l (fun x => (y x : ℂ)) (fun x => (f x : ℂ)) (map Complex.ofRealHom A) :=
  fun n => by
    have h := hf n
    have e : ∀ x, (f x : ℂ) - (trunc n (map Complex.ofRealHom A)).eval (y x : ℂ) =
        ((f x - (trunc n A).eval (y x) : ℝ) : ℂ) := fun x => by
      rw [trunc_map, Polynomial.eval_map, show ((y x : ℂ)) = Complex.ofRealHom (y x) from rfl,
        Polynomial.eval₂_at_apply]
      push_cast
      rfl
    rw [← isBigO_norm_left, ← isBigO_norm_right] at h ⊢
    refine h.congr (fun x => ?_) (fun x => ?_)
    · beta_reduce
      rw [e x, Complex.norm_real]
    · beta_reduce
      rw [← Complex.ofReal_pow, Complex.norm_real]

/-! ### Lagrange inversion, second form -/

/-- **Lagrange–Bürmann, second form**: if `Ψ = X φ(Ψ)`, then
`[wⁿ] H(Ψ(w)) = [tⁿ] H(t) φ(t)ⁿ (1 − tφ′(t)/φ(t))`, written without division. -/
theorem lagrange_inversion_second {K : Type*} [Field K] [CharZero K] {φ Ψ : K⟦X⟧}
    (hΨ0 : constantCoeff Ψ = 0) (hφ0 : constantCoeff φ ≠ 0) (hΨ : Ψ = X * φ.subst Ψ)
    (H : K⟦X⟧) (n : ℕ) :
    coeff n (H.subst Ψ) = coeff n (H * φ ^ n - X * (H * φ ^ (n - 1) * d⁄dX φ)) := by
  rcases n with _ | n
  · rw [map_sub, coeff_zero_X_mul, sub_zero, pow_zero, mul_one, coeff_zero_eq_constantCoeff]
    erw [constantCoeff_subst_of_constantCoeff_zero hΨ0]
    rfl
  · have h1 := lagrange_inversion hΨ0 hφ0 hΨ H (n := n + 1) (by omega)
    have h2 : coeff n (d⁄dX (H * φ ^ (n + 1))) = coeff (n + 1) (H * φ ^ (n + 1)) * (n + 1) :=
      coeff_derivative _ _
    rw [Derivation.leibniz, Derivation.leibniz_pow] at h2
    simp only [smul_eq_mul, map_add, nsmul_eq_mul, Nat.add_sub_cancel] at h2
    rw [map_sub, coeff_succ_X_mul, Nat.add_sub_cancel]
    simp only [Nat.add_sub_cancel] at h1
    have hn : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hc2 : coeff n (H * ((↑(n + 1) : K⟦X⟧) * (φ ^ n * d⁄dX φ))) =
        ((n : K) + 1) * coeff n (H * φ ^ n * d⁄dX φ) := by
      rw [show H * ((↑(n + 1) : K⟦X⟧) * (φ ^ n * d⁄dX φ)) =
        C ((n : K) + 1) * (H * φ ^ n * d⁄dX φ) by
          push_cast; rw [map_add, map_natCast, map_one]; ring,
        coeff_C_mul]
    rw [hc2, mul_comm (φ ^ (n + 1))] at h2
    push_cast at h1 h2
    apply mul_left_cancel₀ hn
    linear_combination h1 + h2

/-! ### Change of variable in an expansion -/

theorem hasPowExpansion_id {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {y : α → 𝕜}
    (hy : Tendsto y l (𝓝 0)) : HasPowExpansion l y y X := by
  have h := hasPowExpansion_polynomial hy Polynomial.X
  rw [Polynomial.coe_X] at h
  exact h.congr' (Eventually.of_forall fun _ => Polynomial.eval_X)

/-- If `F ∼ A(y)` and `z = y U` with `U ∼ Û`, `Û(0) ≠ 0`, and `A = B(XÛ)`, then `F ∼ B(z)`. -/
theorem HasPowExpansion.change_var {α 𝕜 : Type*} [NontriviallyNormedField 𝕜] {l : Filter α}
    {y : α → 𝕜} (hy : Tendsto y l (𝓝 0)) {F u : α → 𝕜} {A B Û : 𝕜⟦X⟧}
    (hF : HasPowExpansion l y F A) (hu : HasPowExpansion l y u Û) (hU0 : constantCoeff Û ≠ 0)
    (hAB : A = B.subst (X * Û)) : HasPowExpansion l (fun x => y x * u x) F B := fun n => by
  have hz : HasPowExpansion l y (fun x => y x * u x) (X * Û) := (hasPowExpansion_id hy).mul hy hu
  have hz0 : constantCoeff (X * Û) = 0 := by simp
  have h2 := hz.polyEval hy (trunc n B) n
  rw [trunc_aeval_trunc hz0 B n, ← hAB] at h2
  have e : (fun x => F x - (trunc n B).eval (y x * u x)) =O[l] fun x => y x ^ n :=
    ((hF n).sub h2).congr_left fun x => by ring
  have hut := hu.tendsto hy
  have hyz : y =O[l] fun x => y x * u x := by
    have hinv : (fun x => (u x)⁻¹) =O[l] fun _ => (1 : 𝕜) := (hut.inv₀ hU0).isBigO_one 𝕜
    refine ((isBigO_refl (fun x => y x * u x) l).mul hinv).congr' ?_ (by simp)
    filter_upwards [hut.eventually_ne hU0] with x hx
    field_simp
  exact e.trans (hyz.pow n)

end Azurite.DLMF
