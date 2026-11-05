/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# DLMF §3.8(vi): Conditioning of zeros

* 3.8.13 (`dlmf_3_8_13`): if `f(z, α)` has continuous partial derivatives and `z₀` is a simple
  zero of `f(·, α₀)`, there is a unique zero `z(α)` near `z₀` for `α` near `α₀` (implicit
  function theorem), and `dz/dα = −(∂f/∂α)/(∂f/∂z)`.
* 3.8.14 (`dlmf_3_8_14`): for the polynomial 3.8.8 with `α = a_j`, `dz/da_j = −z^j/f′(z)`.
* Wilkinson's polynomial 3.8.15 `p(x) = (x − 1)(x − 2)⋯(x − 20)` (`wilkinson`): its zeros are
  `1, …, 20` (`wilkinson_roots`), `p′(20) = 19!` (`wilkinson_deriv_twenty`), and 3.8.16
  `dx/da₁₉ = −20¹⁹/19! = (−4.30…) × 10⁷` (`dlmf_3_8_16`). **Erratum**: `a₁₉ = −(1 + 2 + ⋯ + 20)
  = −210`, not `210` (`wilkinson_coeff_nineteen`).
* "For moderate or large values of `n` it is not uncommon for the magnitude of the right-hand
  side of (3.8.14) to be very large compared with unity": illustrated by 3.8.16. Gautschi (1984)
  is not formalized.
-/

open Filter Topology Polynomial ContinuousLinearMap

namespace Azurite.DLMF

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **DLMF 3.8.13**: the sensitivity of a simple zero to a parameter. If `f(α, z)` has partial
derivatives `∂f/∂α`, `∂f/∂z` near `(α₀, z₀)`, continuous at `(α₀, z₀)`, with `f(α₀, z₀) = 0` and
`∂f/∂z (α₀, z₀) ≠ 0`, then near `(α₀, z₀)` the zeros of `f` form the graph of a function
`z(α)` with `z(α₀) = z₀` and `dz/dα = −(∂f/∂α)/(∂f/∂z)` at `α₀`. -/
theorem dlmf_3_8_13 {f fα fz : 𝕜 → 𝕜 → 𝕜} {α₀ z₀ : 𝕜}
    (hα : ∀ᶠ v in 𝓝 (α₀, z₀), HasDerivAt (f · v.2) (fα v.1 v.2) v.1)
    (hz : ∀ᶠ v in 𝓝 (α₀, z₀), HasDerivAt (f v.1 ·) (fz v.1 v.2) v.2)
    (cα : ContinuousAt (Function.uncurry fα) (α₀, z₀))
    (cz : ContinuousAt (Function.uncurry fz) (α₀, z₀))
    (h0 : f α₀ z₀ = 0) (hs : fz α₀ z₀ ≠ 0) :
    ∃ ψ : 𝕜 → 𝕜, ψ α₀ = z₀ ∧ (∀ᶠ α in 𝓝 α₀, f α (ψ α) = 0) ∧
      (∀ᶠ v in 𝓝 (α₀, z₀), f v.1 v.2 = 0 ↔ ψ v.1 = v.2) ∧
      HasDerivAt ψ (-(fα α₀ z₀ / fz α₀ z₀)) α₀ := by
  have hspan : ∀ c : 𝕜, toSpanSingleton 𝕜 c = c • ContinuousLinearMap.id 𝕜 𝕜 := fun c => by
    ext; simp
  obtain ⟨F1, hF1⟩ : ∃ F1 : 𝕜 → 𝕜 → 𝕜 →L[𝕜] 𝕜,
      F1 = fun α z => fα α z • ContinuousLinearMap.id 𝕜 𝕜 := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : 𝕜 → 𝕜 → 𝕜 →L[𝕜] 𝕜,
      F2 = fun α z => fz α z • ContinuousLinearMap.id 𝕜 𝕜 := ⟨_, rfl⟩
  have df₁ : ∀ᶠ v in 𝓝 (α₀, z₀), HasFDerivAt (f · v.2) (F1 v.1 v.2) v.1 :=
    hα.mono fun v hv => by
      rw [hF1]
      show HasFDerivAt _ (fα v.1 v.2 • ContinuousLinearMap.id 𝕜 𝕜) _
      rw [← hspan]; exact hasDerivAt_iff_hasFDerivAt.mp hv
  have df₂ : ∀ᶠ v in 𝓝 (α₀, z₀), HasFDerivAt (f v.1 ·) (F2 v.1 v.2) v.2 :=
    hz.mono fun v hv => by
      rw [hF2]
      show HasFDerivAt _ (fz v.1 v.2 • ContinuousLinearMap.id 𝕜 𝕜) _
      rw [← hspan]; exact hasDerivAt_iff_hasFDerivAt.mp hv
  have cf₁ : ContinuousAt (Function.uncurry F1) (α₀, z₀) := by
    rw [hF1]; exact cα.smul continuousAt_const
  have cf₂ : ContinuousAt (Function.uncurry F2) (α₀, z₀) := by
    rw [hF2]; exact cz.smul continuousAt_const
  set M := ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 _ hs)
  have hM : (M : 𝕜 →L[𝕜] 𝕜) = F2 (α₀, z₀).1 (α₀, z₀).2 := by
    rw [hF2]; ext; simp [M]
  have if₂ : (F2 (α₀, z₀).1 (α₀, z₀).2).IsInvertible := ⟨M, hM⟩
  set ψ := implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have hiff := eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have happ := eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have hder := (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).hasFDerivAt
  simp only at hiff happ hder
  rw [h0] at hiff happ
  refine ⟨ψ, (hiff.self_of_nhds).mp h0, happ, hiff, ?_⟩
  rw [hasDerivAt_iff_hasFDerivAt]
  convert hder using 1
  rw [← hM, inverse_equiv, hF1]
  ext
  simp only [toSpanSingleton_apply, smul_eq_mul, one_mul, coe_comp, Function.comp_apply,
    neg_apply, FunLike.coe_smul, coe_id', Pi.smul_apply, id_eq, mul_one]
  rw [neg_inj, eq_comm, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_eq]
  simp [M]
  field_simp

/-- The polynomial `p` with its coefficient `a_j` replaced by `α`: `p(z) + (α − a_j) z^j`. -/
noncomputable def coeffPerturb (p : 𝕜[X]) (j : ℕ) (α z : 𝕜) : 𝕜 :=
  p.eval z + (α - p.coeff j) * z ^ j

theorem coeffPerturb_eq (p : 𝕜[X]) (j : ℕ) (α z : 𝕜) :
    coeffPerturb p j α z = (p + C (α - p.coeff j) * X ^ j).eval z := by
  simp [coeffPerturb]

theorem coeff_coeffPerturb (p : 𝕜[X]) (j : ℕ) (α : 𝕜) :
    (p + C (α - p.coeff j) * X ^ j).coeff j = α := by
  simp only [coeff_add, coeff_C_mul_X_pow, ↓reduceIte]
  ring

/-- **DLMF 3.8.14**: for the polynomial 3.8.8 and `α = a_j`, a simple zero `z₀` moves with the
coefficient as `dz/da_j = −z₀^j/f′(z₀)`. -/
theorem dlmf_3_8_14 (p : 𝕜[X]) (j : ℕ) {z₀ : 𝕜} (h0 : p.eval z₀ = 0)
    (hs : p.derivative.eval z₀ ≠ 0) :
    ∃ ψ : 𝕜 → 𝕜, ψ (p.coeff j) = z₀ ∧
      (∀ᶠ α in 𝓝 (p.coeff j), (p + C (α - p.coeff j) * X ^ j).eval (ψ α) = 0) ∧
      (∀ᶠ v in 𝓝 (p.coeff j, z₀), (p + C (v.1 - p.coeff j) * X ^ j).eval v.2 = 0 ↔
        ψ v.1 = v.2) ∧
      HasDerivAt ψ (-(z₀ ^ j / p.derivative.eval z₀)) (p.coeff j) := by
  have hα : ∀ v : 𝕜 × 𝕜, HasDerivAt (coeffPerturb p j · v.2) (v.2 ^ j) v.1 := fun v => by
    have := ((hasDerivAt_id v.1).sub_const (p.coeff j)).mul_const (v.2 ^ j)
    have := this.const_add (p.eval v.2)
    simpa [coeffPerturb] using this
  have hz : ∀ v : 𝕜 × 𝕜, HasDerivAt (coeffPerturb p j v.1 ·)
      (p.derivative.eval v.2 + (v.1 - p.coeff j) * (j * v.2 ^ (j - 1))) v.2 := fun v => by
    have := (p.hasDerivAt v.2).add ((hasDerivAt_pow j v.2).const_mul (v.1 - p.coeff j))
    exact this
  have cα : ContinuousAt (Function.uncurry fun (_ : 𝕜) (z : 𝕜) => z ^ j) (p.coeff j, z₀) :=
    (continuous_snd.pow j).continuousAt
  have cz : ContinuousAt (Function.uncurry fun (α z : 𝕜) =>
      p.derivative.eval z + (α - p.coeff j) * (j * z ^ (j - 1))) (p.coeff j, z₀) :=
    (((p.derivative.continuous.comp continuous_snd).add ((continuous_fst.sub
      continuous_const).mul (continuous_const.mul (continuous_snd.pow _))))).continuousAt
  obtain ⟨ψ, h1, h2, h3, h4⟩ := dlmf_3_8_13 (f := coeffPerturb p j)
    (fα := fun _ z => z ^ j)
    (fz := fun α z => p.derivative.eval z + (α - p.coeff j) * (j * z ^ (j - 1)))
    (Eventually.of_forall hα) (Eventually.of_forall hz) cα cz
    (by simp [coeffPerturb, h0]) (by simpa using hs)
  refine ⟨ψ, h1, h2.mono fun α h => by rwa [← coeffPerturb_eq],
    h3.mono fun v h => by rwa [← coeffPerturb_eq], ?_⟩
  simpa using h4

/-! ### Wilkinson's polynomial -/

/-- **DLMF 3.8.15**: Wilkinson's polynomial `(x − 1)(x − 2)⋯(x − 20)`. -/
noncomputable def wilkinson : ℝ[X] := ∏ k ∈ Finset.range 20, (X - C ((k : ℝ) + 1))

theorem wilkinson_roots :
    wilkinson.roots = (Finset.range 20).val.map fun k : ℕ => (k : ℝ) + 1 := by
  have : wilkinson = (((Finset.range 20).val.map fun k : ℕ => (k : ℝ) + 1).map
      fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [this, roots_multiset_prod_X_sub_C]

theorem wilkinson_eval_eq_zero_iff (x : ℝ) :
    wilkinson.eval x = 0 ↔ ∃ k ∈ Finset.range 20, x = k + 1 := by
  simp [wilkinson, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- `p′(20) = 19!`. -/
theorem wilkinson_deriv_twenty : wilkinson.derivative.eval 20 = (Nat.factorial 19 : ℝ) := by
  have h : wilkinson = (X - C ((19 : ℕ) + 1 : ℝ)) *
      ∏ k ∈ Finset.range 19, (X - C ((k : ℝ) + 1)) := by
    rw [wilkinson, Finset.prod_range_succ, mul_comm]
  rw [h, derivative_mul]
  simp only [eval_add, eval_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    one_mul, eval_sub, eval_X, eval_C, eval_prod]
  norm_num [Finset.prod_range_succ, Nat.factorial]

/-- `a₁₉ = −(1 + 2 + ⋯ + 20) = −210` (DLMF prints `210`). -/
theorem wilkinson_coeff_nineteen : wilkinson.coeff 19 = -210 := by
  have := prod_X_sub_C_coeff_card_pred (Finset.range 20) (fun k : ℕ => (k : ℝ) + 1)
    (by simp)
  simp only [Finset.card_range] at this
  rw [wilkinson, this]
  norm_num [Finset.sum_range_succ]

/-- **DLMF 3.8.16**: for the zero `x = 20` of Wilkinson's polynomial and `j = 19`,
`dx/da₁₉ = −20¹⁹/19! = (−4.30…) × 10⁷`: the zero moves `4.3 × 10⁷` times as fast as `a₁₉`. -/
theorem dlmf_3_8_16 :
    ∃ ψ : ℝ → ℝ, ψ (-210) = 20 ∧
      (∀ᶠ α in 𝓝 (-210), (wilkinson + C (α + 210) * X ^ 19).eval (ψ α) = 0) ∧
      HasDerivAt ψ (-((20 : ℝ) ^ 19 / Nat.factorial 19)) (-210) ∧
      -4.31e7 < -((20 : ℝ) ^ 19 / Nat.factorial 19) ∧
      -((20 : ℝ) ^ 19 / Nat.factorial 19) < -4.30e7 := by
  have h0 : wilkinson.eval 20 = 0 :=
    (wilkinson_eval_eq_zero_iff 20).mpr ⟨19, by simp, by norm_num⟩
  have hs : wilkinson.derivative.eval 20 ≠ 0 := by
    rw [wilkinson_deriv_twenty]; exact_mod_cast (Nat.factorial_pos 19).ne'
  obtain ⟨ψ, h1, h2, -, h4⟩ := dlmf_3_8_14 wilkinson 19 h0 hs
  rw [wilkinson_coeff_nineteen] at h1 h2 h4
  rw [wilkinson_deriv_twenty] at h4
  refine ⟨ψ, h1, h2.mono fun α h => by simpa using h, h4, ?_, ?_⟩ <;>
    norm_num [Nat.factorial]

end Azurite.DLMF
