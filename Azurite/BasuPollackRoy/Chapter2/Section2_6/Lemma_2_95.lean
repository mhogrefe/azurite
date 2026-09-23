/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.ConstPuiseux
import Azurite.BasuPollackRoy.Chapter2.Section2_6.CharacteristicPolynomial

/-! # BPR §2.6 Lemma 2.95 — the substitution `R(P, E, x, Y) = ε^{−β} P(ε^ξ(x + Y))`

Let `E = [A, B]` be an edge of the Newton polygon of `P`, with slope `−ξ` and common value
`β = A.2 + A.1 ξ` of `o(ā_h) + h ξ` along `E`, and let `x ∈ R` be a nonzero root of the
characteristic polynomial `Q = Q(P, E, X)` of multiplicity `r`. The recentered polynomial

`R(P, E, x, Y) = ε^{−β} P(ε^ξ(x + Y)) = b̄₀ + b̄₁ Y + ⋯ + b̄_p Y^p`

has `o(b̄_i) ≥ 0` for all `i`, `o(b̄_i) > 0` for `i < r`, and `o(b̄_r) = 0` (part a). Consequently,
for any `x̄ = ε^ξ(x + y)` with `o(y) > 0`, one has `o(P(x̄)) > β` (part b).

The heart is the decomposition `b̄_i = In(a_i) + (positive-order remainder)`, where the
order-`0` part is the `i`-th coefficient of the shifted characteristic polynomial `Q(x + Y)`:
the on-edge columns contribute their initial coefficient `In(ā_h)` (the leading terms surviving
at order `0`), while every other contribution has strictly positive order
(`key_decomp`).
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- `(ε^ξ)^n = ε^{n ξ}`. -/
theorem puiseuxMonomial_pow (ξ : ℚ) (n : ℕ) :
    (puiseuxMonomial ξ : PuiseuxSeries R) ^ n = puiseuxMonomial ((n : ℚ) * ξ) := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, puiseuxMonomial_mul]; congr 1; push_cast; ring

/-- **The substitution polynomial `R(P, E, x, Y) = ε^{−β} P(ε^ξ(x + Y))`** of Lemma 2.95. -/
noncomputable def substPoly (P : Polynomial (PuiseuxSeries R)) (x : R) (ξ β : ℚ) :
    Polynomial (PuiseuxSeries R) :=
  C (puiseuxMonomial (-β)) * P.comp (C (puiseuxMonomial ξ) * (X + C (constPuiseux x)))

/-- `R(P, E, x, Y) = ∑_h ā_h ε^{h ξ − β} (Y + x)^h` as a sum over `h ≤ deg P`. -/
theorem substPoly_eq_sum (P : Polynomial (PuiseuxSeries R)) (x : R) (ξ β : ℚ) :
    substPoly P x ξ β = ∑ h ∈ Finset.range (P.natDegree + 1),
      C (P.coeff h * puiseuxMonomial ((h : ℚ) * ξ - β)) * (X + C (constPuiseux x)) ^ h := by
  rw [substPoly, show P.comp (C (puiseuxMonomial ξ) * (X + C (constPuiseux x)))
      = P.eval₂ C (C (puiseuxMonomial ξ) * (X + C (constPuiseux x))) from rfl,
    eval₂_eq_sum_range' C (Nat.lt_succ_self _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  have hs : puiseuxMonomial (-β) * P.coeff h * puiseuxMonomial ((h : ℚ) * ξ)
      = P.coeff h * puiseuxMonomial ((h : ℚ) * ξ - β) := by
    rw [mul_comm (puiseuxMonomial (-β)) (P.coeff h), mul_assoc, puiseuxMonomial_mul,
      show (-β + (h : ℚ) * ξ) = (h : ℚ) * ξ - β from by ring]
  rw [mul_pow, ← C_pow, puiseuxMonomial_pow, ← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, hs]

/-- The `i`-th coefficient of `R(P, E, x, Y)`, expanded over columns `h`:
`b̄_i = ∑_h (ā_h ε^{h ξ − β}) · [(Y + x)^h]_i`, the inner constant `[(Y + x)^h]_i ∈ R`. -/
theorem substPoly_coeff (P : Polynomial (PuiseuxSeries R)) (x : R) (ξ β : ℚ) (i : ℕ) :
    (substPoly P x ξ β).coeff i
      = ∑ h ∈ Finset.range (P.natDegree + 1),
          P.coeff h * puiseuxMonomial ((h : ℚ) * ξ - β)
            * constPuiseux (((X + C x) ^ h).coeff i) := by
  rw [substPoly_eq_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [coeff_C_mul]
  congr 1
  rw [show (X + C (constPuiseux x) : Polynomial (PuiseuxSeries R))
      = (X + C x).map constPuiseux from by rw [Polynomial.map_add, map_X, map_C],
    ← Polynomial.map_pow, coeff_map]

@[simp] theorem puiseuxOrder_one : puiseuxOrder R (1 : PuiseuxSeries R) = 0 := by
  rw [show (1 : PuiseuxSeries R) = constPuiseux 1 from (map_one _).symm,
    puiseuxOrder_constPuiseux_of_ne one_ne_zero]

/-- The characteristic polynomial of any edge of `P` has degree at most `deg P`: an on-edge column
`h` has finite order `o(ā_h)`, so `ā_h ≠ 0` and `h ≤ deg P`. -/
theorem charPoly_natDegree_le_natDegree (P : Polynomial (PuiseuxSeries R)) (A B : ℕ × ℚ) :
    (charPoly P A B).natDegree ≤ P.natDegree := by
  classical
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hnotmem : k ∉ (Finset.Icc A.1 B.1).filter (colOnLine P A B) := by
    intro hmem
    have hcol : puiseuxOrder R (P.coeff k) = ↑(lineValue A B k) := (Finset.mem_filter.mp hmem).2
    have hne : P.coeff k ≠ 0 := fun h0 => by
      rw [h0, puiseuxOrder_zero] at hcol; exact WithTop.top_ne_coe hcol
    exact absurd (le_natDegree_of_ne_zero hne) (by omega)
  rw [charPoly_coeff, ite_eq_right hnotmem]

/-- **The per-column positivity (the heart of part a).** For every column `h`, the difference
between the rescaled coefficient `ā_h ε^{h ξ − β}` and the constant `In(a_h)` of the
characteristic polynomial has strictly positive order: for on-edge `h` the leading terms cancel
(both have order `0`, initial coefficient `In(ā_h)`), and for off-edge `h` the rescaled
coefficient already has strictly positive order. -/
theorem key_term_pos {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {ξ β : ℚ}
    (hξ : newtonSlope A B = -ξ) (hβ : β = A.2 + (A.1 : ℚ) * ξ)
    (hsupport : ∀ h, (lineValue A B h : WithTop ℚ) ≤ puiseuxOrder R (P.coeff h))
    (honseg : ∀ h, colOnLine P A B h → A.1 ≤ h ∧ h ≤ B.1) (h : ℕ) :
    0 < puiseuxOrder R (P.coeff h * puiseuxMonomial ((h : ℚ) * ξ - β)
      - constPuiseux ((charPoly P A B).coeff h)) := by
  classical
  by_cases hcol : colOnLine P A B h
  · have hcol' : puiseuxOrder R (P.coeff h) = ↑(lineValue A B h) := hcol
    have hmem : h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (honseg h hcol), hcol⟩
    rw [charPoly_coeff, ite_eq_left hmem]
    have hord : puiseuxOrder R (P.coeff h * puiseuxMonomial ((h : ℚ) * ξ - β)) = 0 := by
      rw [puiseuxOrder_mul, puiseuxOrder_puiseuxMonomial, hcol', ← WithTop.coe_add,
        show lineValue A B h + ((h : ℚ) * ξ - β) = 0 from by
          have := lineValue_add_mul A B h hξ; rw [hβ]; linarith, WithTop.coe_zero]
    have hIn : puiseuxInitCoeff R (P.coeff h)
        = puiseuxInitCoeff R (P.coeff h * puiseuxMonomial ((h : ℚ) * ξ - β)) := by
      rw [puiseuxInitCoeff_mul, puiseuxInitCoeff_puiseuxMonomial, mul_one]
    rw [hIn]
    exact puiseuxOrder_sub_constPuiseux_leadingCoeff_pos hord
  · rw [charPoly_coeff, ite_eq_right (fun hmem => hcol (Finset.mem_filter.mp hmem).2), map_zero, sub_zero,
      puiseuxOrder_mul, puiseuxOrder_puiseuxMonomial]
    have hlt : (lineValue A B h : WithTop ℚ) < puiseuxOrder R (P.coeff h) :=
      lt_of_le_of_ne (hsupport h) (fun he => hcol he.symm)
    have hzero : ((lineValue A B h : ℚ) : WithTop ℚ) + (((h : ℚ) * ξ - β : ℚ) : WithTop ℚ) = 0 := by
      rw [← WithTop.coe_add, show lineValue A B h + ((h : ℚ) * ξ - β) = 0 from by
        have := lineValue_add_mul A B h hξ; rw [hβ]; linarith, WithTop.coe_zero]
    have hne_top : (((h : ℚ) * ξ - β : ℚ) : WithTop ℚ) ≠ ⊤ := WithTop.coe_ne_top
    rw [← hzero]
    exact WithTop.add_lt_add_right hne_top hlt

/-- **The decomposition `b̄_i = In(a_i) + (positive order)` (the structural core of part a).**
The `i`-th coefficient of `R(P, E, x, Y)` differs from the `i`-th coefficient of the shifted
characteristic polynomial `Q(x + Y)` (a constant in `R`) by a series of strictly positive order. -/
theorem key_decomp {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {ξ β : ℚ}
    (hξ : newtonSlope A B = -ξ) (hβ : β = A.2 + (A.1 : ℚ) * ξ)
    (hsupport : ∀ h, (lineValue A B h : WithTop ℚ) ≤ puiseuxOrder R (P.coeff h))
    (honseg : ∀ h, colOnLine P A B h → A.1 ≤ h ∧ h ≤ B.1) (x : R) (i : ℕ) :
    0 < puiseuxOrder R ((substPoly P x ξ β).coeff i
      - constPuiseux (((charPoly P A B).comp (X + C x)).coeff i)) := by
  classical
  have hcomp : ((charPoly P A B).comp (X + C x)).coeff i
      = ∑ h ∈ Finset.range (P.natDegree + 1),
          (charPoly P A B).coeff h * ((X + C x) ^ h).coeff i := by
    rw [show (charPoly P A B).comp (X + C x) = (charPoly P A B).eval₂ C (X + C x) from rfl,
      eval₂_eq_sum_range' C (Nat.lt_succ_of_le (charPoly_natDegree_le_natDegree P A B)),
      finsetSum_coeff]
    exact Finset.sum_congr rfl fun h _ => by rw [coeff_C_mul]
  rw [substPoly_coeff, hcomp, map_sum]
  simp only [map_mul]
  rw [← Finset.sum_sub_distrib]
  apply puiseuxOrder_sum_pos
  intro h _
  rw [← sub_mul, puiseuxOrder_mul]
  refine lt_of_lt_of_le ?_ (le_add_of_nonneg_right (puiseuxOrder_constPuiseux_nonneg _))
  exact key_term_pos hξ hβ hsupport honseg h

/-- **BPR Lemma 2.95(a).** With `R(P, E, x, Y) = b̄₀ + b̄₁ Y + ⋯`, the coefficients satisfy
`o(b̄_i) ≥ 0` for all `i`, `o(b̄_i) > 0` for `i < r`, and `o(b̄_r) = 0`, where `r` is the
multiplicity of `x` as a root of the characteristic polynomial. -/
theorem lemma_2_95a {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {x : R} {ξ β : ℚ}
    (hξ : newtonSlope A B = -ξ) (hβ : β = A.2 + (A.1 : ℚ) * ξ)
    (hsupport : ∀ h, (lineValue A B h : WithTop ℚ) ≤ puiseuxOrder R (P.coeff h))
    (honseg : ∀ h, colOnLine P A B h → A.1 ≤ h ∧ h ≤ B.1)
    (hQ : charPoly P A B ≠ 0) :
    (∀ i, 0 ≤ puiseuxOrder R ((substPoly P x ξ β).coeff i)) ∧
    (∀ i < (charPoly P A B).rootMultiplicity x,
        0 < puiseuxOrder R ((substPoly P x ξ β).coeff i)) ∧
    puiseuxOrder R ((substPoly P x ξ β).coeff ((charPoly P A B).rootMultiplicity x)) = 0 := by
  set r := (charPoly P A B).rootMultiplicity x with hrdef
  have hmonic : ((X - C x : Polynomial R) ^ r).Monic := (monic_X_sub_C x).pow r
  have hdvd : (X - C x) ^ r ∣ charPoly P A B := pow_rootMultiplicity_dvd (charPoly P A B) x
  have hQfact : charPoly P A B = (X - C x) ^ r * (charPoly P A B /ₘ (X - C x) ^ r) := by
    conv_lhs => rw [← modByMonic_add_div (charPoly P A B) ((X - C x) ^ r),
      (modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd, zero_add]
  have hQcomp : (charPoly P A B).comp (X + C x)
      = X ^ r * (charPoly P A B /ₘ (X - C x) ^ r).comp (X + C x) := by
    conv_lhs => rw [hQfact]
    rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right]
  have hM1 : ∀ i, i < r → ((charPoly P A B).comp (X + C x)).coeff i = 0 := fun i hi => by
    rw [hQcomp, mul_comm, coeff_mul_X_pow', ite_eq_right (by omega)]
  have hM2 : ((charPoly P A B).comp (X + C x)).coeff r ≠ 0 := by
    rw [hQcomp, mul_comm, coeff_mul_X_pow', ite_eq_left (le_refl r), Nat.sub_self,
      coeff_zero_eq_eval_zero, eval_comp]
    simp only [eval_add, eval_X, eval_C, zero_add]
    exact eval_divByMonic_pow_rootMultiplicity_ne_zero x hQ
  have hkey : ∀ i, 0 < puiseuxOrder R ((substPoly P x ξ β).coeff i
      - constPuiseux (((charPoly P A B).comp (X + C x)).coeff i)) :=
    fun i => key_decomp hξ hβ hsupport honseg x i
  refine ⟨fun i => ?_, fun i hi => ?_, ?_⟩
  · have hb : (substPoly P x ξ β).coeff i
        = constPuiseux (((charPoly P A B).comp (X + C x)).coeff i)
          + ((substPoly P x ξ β).coeff i
            - constPuiseux (((charPoly P A B).comp (X + C x)).coeff i)) := by ring
    rw [hb]
    exact le_trans (le_min (puiseuxOrder_constPuiseux_nonneg _) (le_of_lt (hkey i)))
      (min_le_puiseuxOrder_add _ _)
  · have hb : (substPoly P x ξ β).coeff i
        = (substPoly P x ξ β).coeff i
          - constPuiseux (((charPoly P A B).comp (X + C x)).coeff i) := by
      rw [hM1 i hi, map_zero, sub_zero]
    rw [hb]; exact hkey i
  · have hne : puiseuxOrder R (constPuiseux (((charPoly P A B).comp (X + C x)).coeff r))
        ≠ puiseuxOrder R ((substPoly P x ξ β).coeff r
            - constPuiseux (((charPoly P A B).comp (X + C x)).coeff r)) := by
      rw [puiseuxOrder_constPuiseux_of_ne hM2]; exact ne_of_lt (hkey r)
    have hb : (substPoly P x ξ β).coeff r
        = constPuiseux (((charPoly P A B).comp (X + C x)).coeff r)
          + ((substPoly P x ξ β).coeff r
            - constPuiseux (((charPoly P A B).comp (X + C x)).coeff r)) := by ring
    rw [hb, puiseuxOrder_add_of_ne _ _ hne, puiseuxOrder_constPuiseux_of_ne hM2,
      min_eq_left (le_of_lt (hkey r))]

/-- **BPR Lemma 2.95(b).** For any `x̄ = ε^ξ(x + y)` with `o(y) > 0`, one has `o(P(x̄)) > β`. -/
theorem lemma_2_95b {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {x : R} {ξ β : ℚ}
    (hξ : newtonSlope A B = -ξ) (hβ : β = A.2 + (A.1 : ℚ) * ξ)
    (hsupport : ∀ h, (lineValue A B h : WithTop ℚ) ≤ puiseuxOrder R (P.coeff h))
    (honseg : ∀ h, colOnLine P A B h → A.1 ≤ h ∧ h ≤ B.1)
    (hQ : charPoly P A B ≠ 0) (hxroot : (charPoly P A B).IsRoot x)
    (y : PuiseuxSeries R) (hy : 0 < puiseuxOrder R y) :
    (β : WithTop ℚ) < puiseuxOrder R (P.eval (puiseuxMonomial ξ * (constPuiseux x + y))) := by
  obtain ⟨ha1, ha2, _⟩ := lemma_2_95a (x := x) hξ hβ hsupport honseg hQ
  have hr1 : 0 < (charPoly P A B).rootMultiplicity x := (rootMultiplicity_pos hQ).mpr hxroot
  have hb0 : 0 < puiseuxOrder R ((substPoly P x ξ β).coeff 0) := ha2 0 hr1
  have hpow : ∀ j, 0 < puiseuxOrder R (y ^ (j + 1)) := by
    intro j
    induction j with
    | zero => rw [zero_add, pow_one]; exact hy
    | succ k ih =>
        rw [pow_succ, puiseuxOrder_mul]
        exact lt_of_lt_of_le ih (le_add_of_nonneg_right (le_of_lt hy))
  have hpos : 0 < puiseuxOrder R ((substPoly P x ξ β).eval y) := by
    rw [eval_eq_sum_range]
    apply puiseuxOrder_sum_pos
    intro i _
    rw [puiseuxOrder_mul]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, puiseuxOrder_one, add_zero]; exact hb0
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact lt_of_lt_of_le (hpow j) (le_add_of_nonneg_left (ha1 _))
  have hsub : (substPoly P x ξ β).eval y
      = puiseuxMonomial (-β) * P.eval (puiseuxMonomial ξ * (constPuiseux x + y)) := by
    rw [substPoly, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_add, eval_X, eval_C,
      add_comm y (constPuiseux x)]
  have hP : P.eval (puiseuxMonomial ξ * (constPuiseux x + y))
      = puiseuxMonomial β * (substPoly P x ξ β).eval y := by
    rw [hsub, ← mul_assoc, puiseuxMonomial_mul, add_neg_cancel, puiseuxMonomial_zero, one_mul]
  rw [hP, puiseuxOrder_mul, puiseuxOrder_puiseuxMonomial]
  exact lt_of_eq_of_lt (add_zero (β : WithTop ℚ)).symm (WithTop.add_lt_add_left (by simp) hpos)

end Azurite.BPR
