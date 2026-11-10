/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Instances.Nat
import Azurite.DLMF.Chapter3.Section12

/-!
# DLMF §5.2: Definitions (gamma and psi functions, Euler's constant, Pochhammer's symbol)

Formalizations of <https://dlmf.nist.gov/5.2>.  `Γ` is Mathlib's `Complex.Gamma`, `ψ` is
Mathlib's `Complex.digamma` (`= logDeriv Gamma`), `γ` is `Real.eulerMascheroniConstant`, and
Pochhammer's symbol `(a)ₙ` is `(ascPochhammer R n).eval a`; the falling factorial
`x(x − 1)⋯(x − n + 1)` is `(descPochhammer R n).eval x`.  The poles `0, −1, −2, …` form
`gammaPoles` (closed, `isClosed_gammaPoles`, with a path-connected complement,
`isPreconnected_compl_gammaPoles`).

## §5.2(i) Gamma and Psi Functions

* 5.2.1, Euler's integral for `ℜz > 0` (`dlmf_5_2_1`).  "When `ℜz ≤ 0`, `Γ(z)` is defined by
  analytic continuation": `Γ` is analytic off the poles (`dlmf_5_2_i_analytic`) and is the only
  analytic function there agreeing with Euler's integral on `ℜz > 0`
  (`dlmf_5_2_i_continuation`).  "It is a meromorphic function" (`dlmf_5_2_i_meromorphic`) "with
  no zeros" (`dlmf_5_2_i_ne_zero`), "and with simple poles of residue `(−1)ⁿ/n!` at `z = −n`"
  (`dlmf_5_2_i_pole`: order `−1`; `dlmf_5_2_i_residue`: `(z + n) Γ(z) → (−1)ⁿ/n!`).
  "`1/Γ(z)` is entire" (`dlmf_5_2_i_inv_entire`), "with simple zeros at `z = −n`"
  (`dlmf_5_2_i_inv_zero_iff`: the zeros are exactly these; `dlmf_5_2_i_inv_simple_zero`: order
  `1`).  (Mathlib's junk value `Γ(−n) = 0` makes `1/Γ` literally `0` there.)
* 5.2.2, `ψ(z) = Γ′(z)/Γ(z)` (`dlmf_5_2_2`; with Mathlib's junk values it holds at every `z`);
  `ψ` is analytic off the poles (`dlmf_5_2_2_analytic`); "`ψ(z)` is meromorphic"
  (`dlmf_5_2_i_digamma_meromorphic`) "with simple poles of residue `−1` at `z = −n`"
  (`dlmf_5_2_i_digamma_pole`, `dlmf_5_2_i_digamma_residue`).

## §5.2(ii) Euler's Constant

* 5.2.3, `γ = lim (1 + 1/2 + ⋯ + 1/n − ln n)` (`dlmf_5_2_3`, Mathlib's
  `Real.tendsto_harmonic_sub_log`) and its 20 decimals `0.57721 56649 01532 86060…`
  (`dlmf_5_2_3_decimals` = `dlmf_3_12_4`, evaluated in the kernel from AzFloat's enclosure).

## §5.2(iii) Pochhammer's Symbol

* 5.2.4 (`dlmf_5_2_4_zero`, `dlmf_5_2_4`), 5.2.5 (`dlmf_5_2_5`, Mathlib's
  `Complex.Gamma_add_nat_div_Gamma_eq`), 5.2.6 (`dlmf_5_2_6`), 5.2.7 (`dlmf_5_2_7`,
  `dlmf_5_2_7_zero`), 5.2.8 (`dlmf_5_2_8`, `dlmf_5_2_8_odd`), over any commutative (semi)ring or
  any field of characteristic zero where DLMF divides.
* 5.2.9, rising and falling factorials in terms of each other (`dlmf_5_2_9`, `dlmf_5_2_9_falling`,
  over any commutative ring), with the Lah numbers `lah n k` defined by their recurrence
  `L(n + 1, k + 1) = (n + k + 1) L(n, k + 1) + L(n, k)` and shown equal to DLMF's
  `L(n, k) = C(n − 1, k − 1) n!/k!` for `n, k ≥ 1` (`lah_eq`); for `k = 0` DLMF's formula needs
  the conventions `C(−1, −1) = 1` (`L(0, 0) = 1`, `lah_zero_zero`) and `C(n − 1, −1) = 0` for
  `n ≥ 1` (`L(n, 0) = 0`, `lah_succ_zero`).
-/

open Complex Filter Topology Finset Polynomial
open scoped Nat

namespace Azurite.DLMF

/-! ### The poles of `Γ` -/

/-- The poles of `Γ` (and of `ψ`): `z = 0, −1, −2, …`. -/
def gammaPoles : Set ℂ := Set.range fun n : ℕ => -(n : ℂ)

theorem not_mem_gammaPoles {z : ℂ} : z ∉ gammaPoles ↔ ∀ m : ℕ, z ≠ -m := by
  simp [gammaPoles, eq_comm]

theorem neg_natCast_mem_gammaPoles (n : ℕ) : -(n : ℂ) ∈ gammaPoles := ⟨n, rfl⟩

theorem not_mem_gammaPoles_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ∉ gammaPoles := by
  rintro ⟨n, rfl⟩
  simp only [neg_re, natCast_re] at hz
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem isClosed_gammaPoles : IsClosed gammaPoles := by
  have h : IsClosedEmbedding (⇑(Homeomorph.neg ℂ) ∘ ((↑) : ℝ → ℂ) ∘ ((↑) : ℕ → ℝ)) :=
    (Homeomorph.neg ℂ).isClosedEmbedding.comp
      (Complex.isometry_ofReal.isClosedEmbedding.comp Nat.isClosedEmbedding_coe_real)
  have e : (⇑(Homeomorph.neg ℂ) ∘ ((↑) : ℝ → ℂ) ∘ ((↑) : ℕ → ℝ)) = fun n : ℕ => -(n : ℂ) := by
    funext n; simp
  rw [e] at h
  exact h.isClosed_range

theorem isPreconnected_compl_gammaPoles : IsPreconnected gammaPolesᶜ :=
  ((Set.countable_range _).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected

/-- Near `−n`, the only pole is `−n` itself. -/
theorem not_mem_gammaPoles_of_dist {n : ℕ} {z : ℂ} (hz : dist z (-(n : ℂ)) < 1)
    (hne : z ≠ -(n : ℂ)) : z ∉ gammaPoles := by
  rintro ⟨m, rfl⟩
  apply hne
  rw [dist_eq_norm, show -(m : ℂ) - -(n : ℂ) = (((n : ℝ) - m : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs] at hz
  have h := abs_lt.mp hz
  have h1 : ((n : ℤ) - m : ℤ) < 1 := by exact_mod_cast h.2
  have h2 : (-1 : ℤ) < (n : ℤ) - m := by exact_mod_cast h.1
  have : m = n := by omega
  rw [this]

theorem eventually_not_mem_gammaPoles (n : ℕ) :
    ∀ᶠ z in 𝓝[≠] (-(n : ℂ)), z ∉ gammaPoles := by
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (-(n : ℂ)) one_pos),
    self_mem_nhdsWithin] with z hz hne
  exact not_mem_gammaPoles_of_dist hz hne

/-! ### §5.2(i): Euler's integral and analytic continuation -/

/-- **DLMF 5.2.1** (Euler's integral): `Γ(z) = ∫₀^∞ e^{−t} t^{z−1} dt`, `ℜz > 0`
(Mathlib's `Complex.Gamma_eq_integral`). -/
theorem dlmf_5_2_1 {z : ℂ} (hz : 0 < z.re) :
    Gamma z = ∫ t in Set.Ioi (0 : ℝ), cexp (-(t : ℂ)) * (t : ℂ) ^ (z - 1) := by
  rw [Gamma_eq_integral hz, GammaIntegral]
  simp only [ofReal_exp, ofReal_neg]

/-- `Γ` is analytic off the poles. -/
theorem dlmf_5_2_i_analytic : AnalyticOnNhd ℂ Gamma gammaPolesᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun z hz => (differentiableAt_Gamma z (not_mem_gammaPoles.mp hz)).differentiableWithinAt)
    isClosed_gammaPoles.isOpen_compl

/-- **DLMF §5.2(i)**: "When `ℜz ≤ 0`, `Γ(z)` is defined by analytic continuation" — any function
analytic off the poles that agrees with Euler's integral 5.2.1 on `ℜz > 0` is `Γ`. -/
theorem dlmf_5_2_i_continuation {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f gammaPolesᶜ)
    (h : ∀ z : ℂ, 0 < z.re → f z = ∫ t in Set.Ioi (0 : ℝ), cexp (-(t : ℂ)) * (t : ℂ) ^ (z - 1)) :
    Set.EqOn f Gamma gammaPolesᶜ := by
  refine hf.eqOn_of_preconnected_of_eventuallyEq dlmf_5_2_i_analytic
    isPreconnected_compl_gammaPoles (z₀ := 1) (not_mem_gammaPoles_of_re_pos (by simp)) ?_
  have hU : {z : ℂ | 0 < z.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
  filter_upwards [hU] with z hz
  rw [h z hz, dlmf_5_2_1 hz]

/-- **DLMF §5.2(i)**: `Γ` "is a meromorphic function". -/
theorem dlmf_5_2_i_meromorphic : Meromorphic Gamma := Meromorphic.Gamma

/-- **DLMF §5.2(i)**: `Γ` has "no zeros". -/
theorem dlmf_5_2_i_ne_zero {z : ℂ} (hz : z ∉ gammaPoles) : Gamma z ≠ 0 :=
  Gamma_ne_zero (not_mem_gammaPoles.mp hz)

/-- `Γ(z) = Γ(z + n + 1) / ((z)ₙ (z + n))` off the poles. -/
theorem Gamma_eq_div_pochhammer {z : ℂ} (hz : z ∉ gammaPoles) (n : ℕ) :
    Gamma z = Gamma (z + n + 1) / ((ascPochhammer ℂ n).eval z * (z + n)) := by
  have hz' := not_mem_gammaPoles.mp hz
  have h := Gamma_add_nat_div_Gamma_eq (n := n + 1) z hz'
  rw [ascPochhammer_succ_eval] at h
  have hs : ∀ m : ℕ, z + ((n : ℂ) + 1) ≠ -m := fun m hm =>
    hz' (m + n + 1) (by push_cast; linear_combination hm)
  push_cast at h
  rw [show z + n + 1 = z + ((n : ℂ) + 1) by ring, ← h, div_div_eq_mul_div,
    mul_div_cancel_left₀ _ (Gamma_ne_zero hs)]

/-- `(−n)ₙ = (−1)ⁿ n!`. -/
theorem ascPochhammer_eval_neg_self (n : ℕ) :
    (ascPochhammer ℂ n).eval (-(n : ℂ)) = (-1) ^ n * n ! := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_self]

theorem ascPochhammer_eval_neg_self_ne_zero (n : ℕ) :
    (ascPochhammer ℂ n).eval (-(n : ℂ)) ≠ 0 := by
  rw [ascPochhammer_eval_neg_self]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero n)

theorem analyticAt_Gamma_shift (n : ℕ) :
    AnalyticAt ℂ (fun z : ℂ => Gamma (z + n + 1)) (-(n : ℂ)) := by
  have h1 : AnalyticAt ℂ Gamma (-(n : ℂ) + n + 1) :=
    dlmf_5_2_i_analytic _ (not_mem_gammaPoles_of_re_pos (by simp))
  exact h1.comp (f := fun z : ℂ => z + n + 1) (by fun_prop)

theorem analyticAt_ascPochhammer_eval (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (ascPochhammer ℂ n).eval w) z :=
  (Polynomial.differentiable _).analyticAt z

theorem inv_neg_one_pow (n : ℕ) : (((-1 : ℂ) ^ n))⁻¹ = (-1) ^ n := by
  rw [← inv_pow, inv_neg, inv_one]

/-- The regular factor at the pole `−n`: `g(z) = Γ(z + n + 1)/(z)ₙ`, `Γ(z) = (z + n)⁻¹ g(z)`. -/
noncomputable def gammaPoleFactor (n : ℕ) (z : ℂ) : ℂ :=
  Gamma (z + n + 1) / (ascPochhammer ℂ n).eval z

theorem gammaPoleFactor_analyticAt (n : ℕ) : AnalyticAt ℂ (gammaPoleFactor n) (-(n : ℂ)) :=
  (analyticAt_Gamma_shift n).div (analyticAt_ascPochhammer_eval n _)
    (ascPochhammer_eval_neg_self_ne_zero n)

theorem gammaPoleFactor_neg (n : ℕ) : gammaPoleFactor n (-(n : ℂ)) = (-1) ^ n / n ! := by
  rw [gammaPoleFactor, ascPochhammer_eval_neg_self, show -(n : ℂ) + n + 1 = 1 by ring, Gamma_one,
    one_div, mul_inv, inv_neg_one_pow, div_eq_mul_inv]

theorem Gamma_eq_gammaPoleFactor (n : ℕ) :
    ∀ᶠ z in 𝓝[≠] (-(n : ℂ)), Gamma z = (z - -(n : ℂ)) ^ (-1 : ℤ) • gammaPoleFactor n z := by
  filter_upwards [eventually_not_mem_gammaPoles n] with z hz
  rw [Gamma_eq_div_pochhammer hz n, zpow_neg_one, smul_eq_mul, sub_neg_eq_add, gammaPoleFactor,
    div_eq_mul_inv, mul_inv, div_eq_mul_inv]
  ring

/-- **DLMF §5.2(i)**: `Γ` has a simple pole at `z = −n`. -/
theorem dlmf_5_2_i_pole (n : ℕ) : meromorphicOrderAt Gamma (-(n : ℂ)) = -1 := by
  rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) by norm_cast,
    meromorphicOrderAt_eq_int_iff (Meromorphic.Gamma _)]
  refine ⟨gammaPoleFactor n, gammaPoleFactor_analyticAt n, ?_, Gamma_eq_gammaPoleFactor n⟩
  rw [gammaPoleFactor_neg]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero n)

/-- **DLMF §5.2(i)**: the residue of `Γ` at `z = −n` is `(−1)ⁿ/n!`. -/
theorem dlmf_5_2_i_residue (n : ℕ) :
    Tendsto (fun z => (z + n) * Gamma z) (𝓝[≠] (-(n : ℂ))) (𝓝 ((-1) ^ n / n !)) := by
  have hc := (gammaPoleFactor_analyticAt n).continuousAt.tendsto
  rw [gammaPoleFactor_neg] at hc
  refine (tendsto_nhdsWithin_of_tendsto_nhds hc).congr' ?_
  filter_upwards [Gamma_eq_gammaPoleFactor n, self_mem_nhdsWithin] with z hz hne
  have hz0 : z + n ≠ 0 := fun h => hne (Set.mem_singleton_iff.mpr (by linear_combination h))
  rw [hz, zpow_neg_one, smul_eq_mul, sub_neg_eq_add, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]

/-- **DLMF §5.2(i)**: "`1/Γ(z)` is entire" (Mathlib's `Complex.differentiable_one_div_Gamma`). -/
theorem dlmf_5_2_i_inv_entire : Differentiable ℂ fun z : ℂ => (Gamma z)⁻¹ :=
  differentiable_one_div_Gamma

/-- **DLMF §5.2(i)**: the zeros of `1/Γ` are exactly `z = −n`. -/
theorem dlmf_5_2_i_inv_zero_iff (z : ℂ) : (Gamma z)⁻¹ = 0 ↔ z ∈ gammaPoles := by
  constructor
  · intro h
    by_contra hz
    exact dlmf_5_2_i_ne_zero hz (inv_eq_zero.mp h)
  · rintro ⟨n, rfl⟩
    rw [Gamma_neg_nat_eq_zero, inv_zero]

/-- **DLMF §5.2(i)**: the zeros of `1/Γ` at `z = −n` are simple. -/
theorem dlmf_5_2_i_inv_simple_zero (n : ℕ) :
    analyticOrderAt (fun z : ℂ => (Gamma z)⁻¹) (-(n : ℂ)) = 1 := by
  have hA : AnalyticAt ℂ (fun z : ℂ => (Gamma z)⁻¹) (-(n : ℂ)) :=
    dlmf_5_2_i_inv_entire.analyticAt _
  have h1 : Gamma (-(n : ℂ) + n + 1) ≠ 0 := by
    rw [show -(n : ℂ) + n + 1 = 1 by ring, Gamma_one]; exact one_ne_zero
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, hA.analyticOrderAt_eq_natCast]
  refine ⟨fun z => (ascPochhammer ℂ n).eval z / Gamma (z + n + 1),
    (analyticAt_ascPochhammer_eval n _).div (analyticAt_Gamma_shift n) h1,
    div_ne_zero (ascPochhammer_eval_neg_self_ne_zero n) h1, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (-(n : ℂ)) one_pos] with z hz
  by_cases hne : z = -(n : ℂ)
  · rw [hne, Gamma_neg_nat_eq_zero, inv_zero, sub_self, zero_pow one_ne_zero, zero_smul]
  · rw [Gamma_eq_div_pochhammer (not_mem_gammaPoles_of_dist hz hne) n, pow_one, smul_eq_mul,
      sub_neg_eq_add, inv_div]
    ring

/-! ### §5.2(i): the psi function -/

/-- **DLMF 5.2.2**: `ψ(z) = Γ′(z)/Γ(z)` (Mathlib's `Complex.digamma = logDeriv Gamma`; DLMF
states it for `z ≠ 0, −1, −2, …`, and with Mathlib's junk values it holds everywhere). -/
theorem dlmf_5_2_2 (z : ℂ) : digamma z = deriv Gamma z / Gamma z := by
  rw [digamma_def, logDeriv_apply]

/-- `ψ` is analytic off the poles. -/
theorem dlmf_5_2_2_analytic : AnalyticOnNhd ℂ digamma gammaPolesᶜ := by
  intro z hz
  have h := (dlmf_5_2_i_analytic.deriv z hz).div (dlmf_5_2_i_analytic z hz)
    (dlmf_5_2_i_ne_zero hz)
  have e : deriv Gamma / Gamma = digamma := funext fun w => by rw [Pi.div_apply, dlmf_5_2_2]
  rwa [e] at h

/-- **DLMF §5.2(i)**: "`ψ(z)` is meromorphic" (Mathlib's `Complex.meromorphic_digamma`). -/
theorem dlmf_5_2_i_digamma_meromorphic : Meromorphic digamma := meromorphic_digamma

/-- The regular factor of `ψ` at the pole `−n`:
`h(z) = (z + n) ψ(z + n + 1) − (z + n) ∑_{k < n} 1/(z + k) − 1`, `ψ(z) = (z + n)⁻¹ h(z)`. -/
noncomputable def digammaPoleFactor (n : ℕ) (z : ℂ) : ℂ :=
  (z + n) * digamma (z + n + 1) - (z + n) * ∑ k ∈ range n, (z + k)⁻¹ - 1

theorem digammaPoleFactor_analyticAt (n : ℕ) :
    AnalyticAt ℂ (digammaPoleFactor n) (-(n : ℂ)) := by
  have h1 : AnalyticAt ℂ digamma (-(n : ℂ) + n + 1) :=
    dlmf_5_2_2_analytic _ (not_mem_gammaPoles_of_re_pos (by simp))
  have hψ : AnalyticAt ℂ (fun z : ℂ => digamma (z + n + 1)) (-(n : ℂ)) :=
    h1.comp (f := fun z : ℂ => z + n + 1) (by fun_prop)
  have hS : AnalyticAt ℂ (fun z : ℂ => ∑ k ∈ range n, (z + k)⁻¹) (-(n : ℂ)) := by
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ) (f := fun (k : ℕ) (z : ℂ) => (z + (k : ℂ))⁻¹) _
      fun k hk => ?_
    refine AnalyticAt.inv (f := fun z : ℂ => z + (k : ℂ)) (by fun_prop) ?_
    have hk' : k < n := Finset.mem_range.mp hk
    intro h
    have : ((k : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; linear_combination h
    have : (k : ℝ) = n := by exact_mod_cast this
    have : k = n := by exact_mod_cast this
    omega
  have hlin : AnalyticAt ℂ (fun z : ℂ => z + (n : ℂ)) (-(n : ℂ)) := by fun_prop
  unfold digammaPoleFactor
  exact ((hlin.mul hψ).sub (hlin.mul hS)).sub analyticAt_const

theorem digammaPoleFactor_neg (n : ℕ) : digammaPoleFactor n (-(n : ℂ)) = -1 := by
  simp [digammaPoleFactor]

theorem digamma_eq_digammaPoleFactor (n : ℕ) :
    ∀ᶠ z in 𝓝[≠] (-(n : ℂ)), digamma z = (z - -(n : ℂ)) ^ (-1 : ℤ) • digammaPoleFactor n z := by
  filter_upwards [eventually_not_mem_gammaPoles n, self_mem_nhdsWithin] with z hz hne
  have hz0 : z + n ≠ 0 := fun h => hne (Set.mem_singleton_iff.mpr (by linear_combination h))
  have hrec := digamma_apply_add_nat (not_mem_gammaPoles.mp hz) (n + 1)
  rw [Finset.sum_range_succ] at hrec
  push_cast at hrec
  rw [zpow_neg_one, smul_eq_mul, sub_neg_eq_add, digammaPoleFactor,
    show z + n + 1 = z + ((n : ℂ) + 1) by ring, hrec]
  field_simp
  ring

/-- **DLMF §5.2(i)**: `ψ` has a simple pole at `z = −n`. -/
theorem dlmf_5_2_i_digamma_pole (n : ℕ) : meromorphicOrderAt digamma (-(n : ℂ)) = -1 := by
  rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) by norm_cast,
    meromorphicOrderAt_eq_int_iff (meromorphic_digamma _)]
  refine ⟨digammaPoleFactor n, digammaPoleFactor_analyticAt n, ?_,
    digamma_eq_digammaPoleFactor n⟩
  rw [digammaPoleFactor_neg]
  norm_num

/-- **DLMF §5.2(i)**: the residue of `ψ` at `z = −n` is `−1`. -/
theorem dlmf_5_2_i_digamma_residue (n : ℕ) :
    Tendsto (fun z => (z + n) * digamma z) (𝓝[≠] (-(n : ℂ))) (𝓝 (-1)) := by
  have hc := (digammaPoleFactor_analyticAt n).continuousAt.tendsto
  rw [digammaPoleFactor_neg] at hc
  refine (tendsto_nhdsWithin_of_tendsto_nhds hc).congr' ?_
  filter_upwards [digamma_eq_digammaPoleFactor n, self_mem_nhdsWithin] with z hz hne
  have hz0 : z + n ≠ 0 := fun h => hne (Set.mem_singleton_iff.mpr (by linear_combination h))
  rw [hz, zpow_neg_one, smul_eq_mul, sub_neg_eq_add, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]

/-! ### §5.2(ii): Euler's constant -/

/-- **DLMF 5.2.3**: `γ = lim_{n→∞} (1 + 1/2 + ⋯ + 1/n − ln n)` (Mathlib's
`Real.tendsto_harmonic_sub_log`). -/
theorem dlmf_5_2_3 :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log

/-- **DLMF 5.2.3**: `γ = 0.57721 56649 01532 86060 …` (= `dlmf_3_12_4`, AzFloat's enclosure of
`γ` evaluated in the kernel). -/
theorem dlmf_5_2_3_decimals :
    0.57721566490153286060 < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < 0.57721566490153286061 :=
  dlmf_3_12_4

/-! ### §5.2(iii): Pochhammer's symbol -/

/-- **DLMF 5.2.4**: `(a)₀ = 1`. -/
theorem dlmf_5_2_4_zero {R : Type*} [Semiring R] (a : R) : (ascPochhammer R 0).eval a = 1 := by
  simp

/-- **DLMF 5.2.4**: `(a)ₙ = a(a + 1)(a + 2)⋯(a + n − 1)`. -/
theorem dlmf_5_2_4 {R : Type*} [CommSemiring R] (a : R) (n : ℕ) :
    (ascPochhammer R n).eval a = ∏ k ∈ range n, (a + k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]

/-- **DLMF 5.2.5**: `(a)ₙ = Γ(a + n)/Γ(a)`, `a ≠ 0, −1, −2, …` (Mathlib's
`Complex.Gamma_add_nat_div_Gamma_eq`). -/
theorem dlmf_5_2_5 {a : ℂ} (ha : a ∉ gammaPoles) (n : ℕ) :
    (ascPochhammer ℂ n).eval a = Gamma (a + n) / Gamma a :=
  (Gamma_add_nat_div_Gamma_eq a (not_mem_gammaPoles.mp ha)).symm

/-- **DLMF 5.2.6**: `(−a)ₙ = (−1)ⁿ (a − n + 1)ₙ`. -/
theorem dlmf_5_2_6 {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    (ascPochhammer R n).eval (-a) = (-1) ^ n * (ascPochhammer R n).eval (a - n + 1) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer]

/-- **DLMF 5.2.7**: `(−m)ₙ = (−1)ⁿ m!/(m − n)!` for `0 ≤ n ≤ m`. -/
theorem dlmf_5_2_7 {m n : ℕ} (h : n ≤ m) :
    (ascPochhammer ℂ n).eval (-(m : ℂ)) = (-1) ^ n * ((m ! : ℂ) / (m - n)!) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
  congr 1
  rw [eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero _)]
  exact_mod_cast (mul_comm _ _).trans (Nat.factorial_mul_descFactorial h)

/-- **DLMF 5.2.7**: `(−m)ₙ = 0` for `n > m`. -/
theorem dlmf_5_2_7_zero {m n : ℕ} (h : m < n) : (ascPochhammer ℂ n).eval (-(m : ℂ)) = 0 :=
  ascPochhammer_eval_neg_coe_nat_of_lt h

/-- **DLMF 5.2.8**: `(a)₂ₙ = 2^{2n} (a/2)ₙ ((a + 1)/2)ₙ`. -/
theorem dlmf_5_2_8 {K : Type*} [Field K] [CharZero K] (a : K) (n : ℕ) :
    (ascPochhammer K (2 * n)).eval a
      = 2 ^ (2 * n) * (ascPochhammer K n).eval (a / 2)
        * (ascPochhammer K n).eval ((a + 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    simp only [ascPochhammer_succ_eval, ih]
    push_cast
    field_simp
    ring

/-- **DLMF 5.2.8**: `(a)₂ₙ₊₁ = 2^{2n+1} (a/2)ₙ₊₁ ((a + 1)/2)ₙ`. -/
theorem dlmf_5_2_8_odd {K : Type*} [Field K] [CharZero K] (a : K) (n : ℕ) :
    (ascPochhammer K (2 * n + 1)).eval a
      = 2 ^ (2 * n + 1) * (ascPochhammer K (n + 1)).eval (a / 2)
        * (ascPochhammer K n).eval ((a + 1) / 2) := by
  rw [ascPochhammer_succ_eval, dlmf_5_2_8, ascPochhammer_succ_eval]
  push_cast
  field_simp
  ring

/-! ### Lah numbers and 5.2.9 -/

/-- The **Lah numbers**, by their recurrence: `L(0, 0) = 1`, `L(0, k + 1) = L(n + 1, 0) = 0`,
`L(n + 1, k + 1) = (n + k + 1) L(n, k + 1) + L(n, k)`.  DLMF's closed form is `lah_eq`. -/
def lah : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (n + k + 1) * lah n (k + 1) + lah n k

@[simp] theorem lah_zero_zero : lah 0 0 = 1 := rfl

@[simp] theorem lah_zero_succ (k : ℕ) : lah 0 (k + 1) = 0 := rfl

@[simp] theorem lah_succ_zero (n : ℕ) : lah (n + 1) 0 = 0 := rfl

theorem lah_succ_succ (n k : ℕ) : lah (n + 1) (k + 1) = (n + k + 1) * lah n (k + 1) + lah n k :=
  rfl

theorem lah_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → lah n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [lah_succ_succ, lah_eq_zero_of_lt (by omega : n < k + 1), lah_eq_zero_of_lt (by omega)]
    simp

/-- `L(m + 1, j + 1) (j + 1)! = C(m, j) (m + 1)!`. -/
theorem lah_mul_factorial : ∀ m j : ℕ, lah (m + 1) (j + 1) * (j + 1)! = m.choose j * (m + 1)!
  | 0, 0 => rfl
  | 0, j + 1 => by simp [lah_succ_succ]
  | m + 1, 0 => by
    have ih := lah_mul_factorial m 0
    rw [lah_succ_succ, lah_succ_zero, add_zero]
    simp only [Nat.choose_zero_right, one_mul, zero_add, Nat.factorial_one, mul_one] at ih ⊢
    rw [ih, Nat.factorial_succ (m + 1)]
  | m + 1, i + 1 => by
    have ih1 := lah_mul_factorial m (i + 1)
    have ih0 := lah_mul_factorial m i
    rw [lah_succ_succ, Nat.choose_succ_succ, Nat.factorial_succ (m + 1),
      Nat.factorial_succ (i + 1)]
    have e : ((m + 1 + (i + 1) + 1) * lah (m + 1) (i + 1 + 1) + lah (m + 1) (i + 1))
        * ((i + 1 + 1) * (i + 1)!)
        = (m + i + 3) * (lah (m + 1) (i + 1 + 1) * (i + 1 + 1)!)
          + (i + 2) * (lah (m + 1) (i + 1) * (i + 1)!) := by
      rw [Nat.factorial_succ (i + 1)]; ring
    rw [e, ih1, ih0]
    by_cases him : i ≤ m
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le him
      have h := Nat.choose_succ_right_eq (i + d) i
      rw [show i + d - i = d by omega] at h
      nlinarith [h]
    · rw [Nat.choose_eq_zero_of_lt (by omega : m < i),
        Nat.choose_eq_zero_of_lt (by omega : m < i + 1)]
      ring

/-- **DLMF §5.2(iii)**: the Lah number `L(n, k) = C(n − 1, k − 1) n!/k!`, `n, k ≥ 1`. -/
theorem lah_eq {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (lah n k : ℚ) = ((n - 1).choose (k - 1) : ℚ) * n ! / k ! := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero _), Nat.add_sub_cancel,
    Nat.add_sub_cancel]
  exact_mod_cast lah_mul_factorial m j

/-- `x(x − 1)⋯(x − k + 1) (x + n) = x(x − 1)⋯(x − k) + (n + k) x(x − 1)⋯(x − k + 1)`. -/
theorem descPochhammer_eval_mul_add {R : Type*} [CommRing R] (x : R) (n k : ℕ) :
    (descPochhammer R k).eval x * (x + n)
      = (descPochhammer R (k + 1)).eval x + ((n + k : ℕ) : R) * (descPochhammer R k).eval x := by
  rw [descPochhammer_succ_eval]
  push_cast
  ring

/-- **DLMF 5.2.9**: `(x)ₙ = ∑_{k=0}^{n} L(n, k) x(x − 1)⋯(x − k + 1)`. -/
theorem dlmf_5_2_9 {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (ascPochhammer R n).eval x
      = ∑ k ∈ range (n + 1), (lah n k : R) * (descPochhammer R k).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, sum_mul, sum_range_succ' _ (n + 1)]
    simp only [lah_succ_zero, Nat.cast_zero, zero_mul, add_zero, lah_succ_succ]
    have hL : ∀ k ∈ range (n + 1), (lah n k : R) * (descPochhammer R k).eval x * (x + n)
        = (lah n k : R) * (descPochhammer R (k + 1)).eval x
          + ((n + k : ℕ) : R) * (lah n k : R) * (descPochhammer R k).eval x := by
      intro k _
      rw [mul_assoc, descPochhammer_eval_mul_add]
      ring
    rw [sum_congr rfl hL, sum_add_distrib]
    have hR : ∀ k ∈ range (n + 1),
        (((n + k + 1) * lah n (k + 1) + lah n k : ℕ) : R) * (descPochhammer R (k + 1)).eval x
          = ((n + (k + 1) : ℕ) : R) * (lah n (k + 1) : R) * (descPochhammer R (k + 1)).eval x
            + (lah n k : R) * (descPochhammer R (k + 1)).eval x := by
      intro k _
      push_cast
      ring
    rw [sum_congr rfl hR, sum_add_distrib, add_comm]
    congr 1
    rw [sum_range_succ' (fun k => ((n + k : ℕ) : R) * (lah n k : R) * (descPochhammer R k).eval x),
      sum_range_succ (fun k => ((n + (k + 1) : ℕ) : R) * (lah n (k + 1) : R)
        * (descPochhammer R (k + 1)).eval x), lah_eq_zero_of_lt (Nat.lt_succ_self n)]
    have h0 : ((n + 0 : ℕ) : R) * (lah n 0 : R) = 0 := by
      cases n with
      | zero => simp
      | succ n => simp
    rw [h0]
    simp

/-- `x(x − 1)⋯` at `−x`: `desc_k(−x) = (−1)ᵏ (x)ₖ`. -/
theorem descPochhammer_eval_neg {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    (descPochhammer R k).eval (-x) = (-1) ^ k * (ascPochhammer R k).eval x := by
  have h := ascPochhammer_eval_neg_eq_descPochhammer R (-x) k
  rw [neg_neg] at h
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **DLMF 5.2.9**: `x(x − 1)⋯(x − n + 1) = ∑_{k=0}^{n} (−1)^{n−k} L(n, k) (x)ₖ`. -/
theorem dlmf_5_2_9_falling {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (descPochhammer R n).eval x
      = ∑ k ∈ range (n + 1), (-1) ^ (n - k) * (lah n k : R) * (ascPochhammer R k).eval x := by
  have h := dlmf_5_2_9 (-x) n
  rw [ascPochhammer_eval_neg_eq_descPochhammer] at h
  have h' : (descPochhammer R n).eval x = (-1) ^ n * ((-1) ^ n * (descPochhammer R n).eval x) := by
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h', h, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [descPochhammer_eval_neg]
  have e : (-1 : R) ^ n * (-1) ^ k = (-1) ^ (n - k) := by
    rw [← pow_add, show n + k = (n - k) + 2 * k by omega, pow_add, pow_mul, neg_one_sq, one_pow,
      mul_one]
  rw [← e]
  ring

end Azurite.DLMF
