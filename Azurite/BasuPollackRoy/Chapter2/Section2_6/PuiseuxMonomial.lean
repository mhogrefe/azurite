/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.Lemma_2_93

/-! # BPR §2.6 — the Puiseux monomial `ε^ξ`

For a rational exponent `ξ ∈ ℚ`, the monomial `ε^ξ` is the Puiseux series `single ξ 1`. It lies
in `K⟨⟨ε⟩⟩` (its single exponent `ξ` has bounded denominator `ξ.den`), is a unit with inverse
`ε^{−ξ}`, has order `ξ` and initial coefficient `1`. These monomials are the rescaling factors
used throughout the Newton-polygon analysis (e.g. the substitution `X = ε^ξ(x + Y)` and the
normalization `ε^{−β}` of Lemma 2.95).
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- The single term `single ξ 1` is a Puiseux series: its exponent `ξ` has bounded denominator
`ξ.den`, so it is a Laurent series in `ε^{1/ξ.den}`. -/
theorem single_mem_puiseux (ξ : ℚ) : (HahnSeries.single ξ (1 : R)) ∈ PuiseuxSeries R := by
  rw [mem_puiseuxSeries_iff]
  refine ⟨ξ.den.toPNat ξ.den_pos, ?_⟩
  show HahnSeries.single ξ (1 : R)
    ∈ (puiseuxEmb R (ξ.den.toPNat ξ.den_pos)).fieldRange
  rw [RingHom.mem_fieldRange]
  refine ⟨HahnSeries.single ξ.num 1, ?_⟩
  rw [puiseuxEmb_single,
    show puiseuxExpHom (ξ.den.toPNat ξ.den_pos) ξ.num = ξ from by
      simp only [puiseuxExpHom_apply]
      show (ξ.num : ℚ) / ((ξ.den : ℕ) : ℚ) = ξ
      exact_mod_cast Rat.num_div_den ξ]

/-- **The Puiseux monomial `ε^ξ`** for a rational exponent `ξ`. -/
noncomputable def puiseuxMonomial (ξ : ℚ) : PuiseuxSeries R :=
  ⟨HahnSeries.single ξ 1, single_mem_puiseux ξ⟩

@[simp] theorem coe_puiseuxMonomial (ξ : ℚ) :
    ((puiseuxMonomial ξ : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single ξ 1 := rfl

/-- `ε^ξ · ε^{ξ'} = ε^{ξ + ξ'}`. -/
theorem puiseuxMonomial_mul (ξ ξ' : ℚ) :
    (puiseuxMonomial ξ : PuiseuxSeries R) * puiseuxMonomial ξ' = puiseuxMonomial (ξ + ξ') := by
  apply Subtype.ext
  rw [Subfield.coe_mul, coe_puiseuxMonomial, coe_puiseuxMonomial, coe_puiseuxMonomial,
    HahnSeries.single_mul_single, mul_one]

/-- `ε^0 = 1`. -/
@[simp] theorem puiseuxMonomial_zero : (puiseuxMonomial 0 : PuiseuxSeries R) = 1 := by
  apply Subtype.ext
  rw [coe_puiseuxMonomial, OneMemClass.coe_one, HahnSeries.single_zero_one]

/-- `ε^ξ ≠ 0`. -/
theorem puiseuxMonomial_ne_zero (ξ : ℚ) : (puiseuxMonomial ξ : PuiseuxSeries R) ≠ 0 := by
  intro h
  have hz : (HahnSeries.single ξ (1 : R)) = 0 := by rw [← coe_puiseuxMonomial, h]; simp
  exact HahnSeries.single_ne_zero one_ne_zero hz

/-- `ε^ξ · ε^{−ξ} = 1`: the monomial `ε^ξ` is a unit with inverse `ε^{−ξ}`. -/
theorem puiseuxMonomial_mul_neg (ξ : ℚ) :
    (puiseuxMonomial ξ : PuiseuxSeries R) * puiseuxMonomial (-ξ) = 1 := by
  rw [puiseuxMonomial_mul, add_neg_cancel, puiseuxMonomial_zero]

theorem puiseuxMonomial_inv (ξ : ℚ) :
    (puiseuxMonomial ξ : PuiseuxSeries R)⁻¹ = puiseuxMonomial (-ξ) :=
  inv_eq_of_mul_eq_one_right (puiseuxMonomial_mul_neg ξ)

/-- The order of `ε^ξ` is `ξ`. -/
@[simp] theorem puiseuxOrder_puiseuxMonomial (ξ : ℚ) :
    puiseuxOrder R (puiseuxMonomial ξ) = (ξ : WithTop ℚ) := by
  rw [puiseuxOrder, coe_puiseuxMonomial, HahnSeries.orderTop_single one_ne_zero]

/-- The initial coefficient of `ε^ξ` is `1`. -/
@[simp] theorem puiseuxInitCoeff_puiseuxMonomial (ξ : ℚ) :
    puiseuxInitCoeff R (puiseuxMonomial ξ) = 1 := by
  rw [puiseuxInitCoeff, coe_puiseuxMonomial, HahnSeries.leadingCoeff_of_single]

end Azurite.BPR
