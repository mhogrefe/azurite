/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.AlgebraicPuiseux
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Infinitesimal
import Azurite.BasuPollackRoy.Chapter2.Section2_6.ConstPuiseux
import Azurite.BasuPollackRoy.Chapter2.Section2_6.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # BPR §2.6 Proposition 2.99 — the valuation ring `K⟨ε⟩_b`

* **Part 1.** The elements of `K⟨ε⟩` (algebraic Puiseux series) with non-negative order constitute a
  valuation ring `K⟨ε⟩_b` (`puiseuxBounded`). The order `o` is an additive valuation, so the
  non-negative-order elements form a subring; and for nonzero `x`, `o(x) + o(x⁻¹) = 0`, so one of
  `o(x)`, `o(x⁻¹)` is non-negative — the valuation-ring condition.

* **Part 2.** For `R` real closed, the elements of `R⟨ε⟩_b` are exactly the elements of `R⟨ε⟩`
  *bounded over `R`* (absolute value less than a positive element of `R`): this is the analytic core
  `bounded_iff_puiseuxOrder_nonneg`, comparing `|x|` with `ι(a)` through their leading terms. A
  negative-order series dominates every `ι(a)` (unbounded); a positive-order one is infinitesimal;
  and an order-`0` series differs from its constant leading term by an infinitesimal.

Part 3 (the complex modulus version, for `C = R[i]`) is in `Proposition_2_99_Complex`. -/

namespace Azurite.BPR

open Polynomial

/-! ## Order arithmetic helpers (any field of coefficients) -/

variable {K : Type*} [Field K]

theorem puiseuxOrder_one : puiseuxOrder K (1 : PuiseuxSeries K) = 0 := by
  show HahnSeries.orderTop ((1 : PuiseuxSeries K) : HahnSeries ℚ K) = 0
  rw [OneMemClass.coe_one]; exact HahnSeries.orderTop_one

theorem puiseuxOrder_neg (a : PuiseuxSeries K) : puiseuxOrder K (-a) = puiseuxOrder K a := by
  show HahnSeries.orderTop ((-a : PuiseuxSeries K) : HahnSeries ℚ K) = HahnSeries.orderTop _
  rw [NegMemClass.coe_neg, HahnSeries.orderTop_neg]

theorem puiseuxOrder_ne_top {x : PuiseuxSeries K} (hx : x ≠ 0) : puiseuxOrder K x ≠ ⊤ := by
  rw [puiseuxOrder, Ne, HahnSeries.orderTop_eq_top]; simpa using hx

theorem puiseuxInitCoeff_neg (a : PuiseuxSeries K) :
    puiseuxInitCoeff K (-a) = -puiseuxInitCoeff K a := by
  simp only [puiseuxInitCoeff, NegMemClass.coe_neg, HahnSeries.leadingCoeff_neg]

theorem algebraMap_eq_constPuiseux (c : K) :
    algebraMap K (PuiseuxSeries K) c = constPuiseux c := by
  apply Subtype.ext; rw [algebraMap_puiseux_coe, coe_constPuiseux, HahnSeries.C_apply]

theorem puiseuxOrder_algebraMap_of_ne {a : K} (ha : a ≠ 0) :
    puiseuxOrder K (algebraMap K (PuiseuxSeries K) a) = 0 := by
  rw [algebraMap_eq_constPuiseux, puiseuxOrder_constPuiseux_of_ne ha]

theorem puiseuxInitCoeff_algebraMap (a : K) :
    puiseuxInitCoeff K (algebraMap K (PuiseuxSeries K) a) = a := by
  rw [algebraMap_eq_constPuiseux, puiseuxInitCoeff_constPuiseux]

theorem puiseuxInitCoeff_add_eq_left (a b : PuiseuxSeries K)
    (h : puiseuxOrder K a < puiseuxOrder K b) :
    puiseuxInitCoeff K (a + b) = puiseuxInitCoeff K a := by
  show HahnSeries.leadingCoeff ((a + b : PuiseuxSeries K) : HahnSeries ℚ K) = _
  rw [Subfield.coe_add]; exact HahnSeries.leadingCoeff_add_eq_left h

theorem puiseuxInitCoeff_add_eq_right (a b : PuiseuxSeries K)
    (h : puiseuxOrder K b < puiseuxOrder K a) :
    puiseuxInitCoeff K (a + b) = puiseuxInitCoeff K b := by
  show HahnSeries.leadingCoeff ((a + b : PuiseuxSeries K) : HahnSeries ℚ K) = _
  rw [Subfield.coe_add]; exact HahnSeries.leadingCoeff_add_eq_right h

/-! ## Part 1 — the valuation ring `K⟨ε⟩_b` -/

/-- **Proposition 2.99 (part 1).** `K⟨ε⟩_b`: the elements of `K⟨ε⟩ = algebraicPuiseux K` with
non-negative order form a valuation subring of `K⟨ε⟩`. -/
noncomputable def puiseuxBounded (K : Type*) [Field K] : ValuationSubring (algebraicPuiseux K) where
  carrier := {y | 0 ≤ puiseuxOrder K (y : PuiseuxSeries K)}
  one_mem' := by
    show 0 ≤ puiseuxOrder K ((1 : algebraicPuiseux K) : PuiseuxSeries K)
    rw [OneMemClass.coe_one, puiseuxOrder_one]
  mul_mem' := by
    intro a b ha hb
    show 0 ≤ puiseuxOrder K ((a * b : algebraicPuiseux K) : PuiseuxSeries K)
    rw [Subfield.coe_mul, puiseuxOrder_mul]; exact add_nonneg ha hb
  zero_mem' := by
    show 0 ≤ puiseuxOrder K ((0 : algebraicPuiseux K) : PuiseuxSeries K)
    rw [ZeroMemClass.coe_zero, puiseuxOrder_zero]; exact le_top
  add_mem' := by
    intro a b ha hb
    show 0 ≤ puiseuxOrder K ((a + b : algebraicPuiseux K) : PuiseuxSeries K)
    rw [Subfield.coe_add]; exact le_trans (le_min ha hb) (min_le_puiseuxOrder_add _ _)
  neg_mem' := by
    intro a ha
    show 0 ≤ puiseuxOrder K ((-a : algebraicPuiseux K) : PuiseuxSeries K)
    rw [NegMemClass.coe_neg, puiseuxOrder_neg]; exact ha
  mem_or_inv_mem' := by
    intro y
    simp only [Set.mem_ofPred_eq]
    rcases eq_or_ne y 0 with rfl | hy
    · left
      rw [ZeroMemClass.coe_zero, puiseuxOrder_zero]; exact le_top
    · have hcoe : (y : PuiseuxSeries K) ≠ 0 := by simpa using hy
      have hcoeinv : ((y⁻¹ : algebraicPuiseux K) : PuiseuxSeries K) ≠ 0 := by
        simpa using inv_ne_zero hy
      have hsum : puiseuxOrder K (y : PuiseuxSeries K)
          + puiseuxOrder K ((y⁻¹ : algebraicPuiseux K) : PuiseuxSeries K) = 0 := by
        rw [← puiseuxOrder_mul, ← Subfield.coe_mul, mul_inv_cancel₀ hy, OneMemClass.coe_one,
          puiseuxOrder_one]
      lift puiseuxOrder K (y : PuiseuxSeries K) to ℚ using puiseuxOrder_ne_top hcoe with p
      lift puiseuxOrder K ((y⁻¹ : algebraicPuiseux K) : PuiseuxSeries K) to ℚ using
        puiseuxOrder_ne_top hcoeinv with q
      rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hsum
      rw [WithTop.coe_nonneg, WithTop.coe_nonneg]
      by_cases hp : 0 ≤ p
      · exact Or.inl hp
      · right; linarith

/-- Membership in `K⟨ε⟩_b` is exactly non-negative order. -/
@[simp] theorem mem_puiseuxBounded {y : algebraicPuiseux K} :
    y ∈ puiseuxBounded K ↔ 0 ≤ puiseuxOrder K (y : PuiseuxSeries K) := Iff.rfl

/-! ## Part 2 — `R⟨ε⟩_b` is the ring of elements bounded over `R` -/

section Ordered

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
theorem puiseuxOrder_abs (x : PuiseuxSeries R) : puiseuxOrder R |x| = puiseuxOrder R x := by
  rcases abs_choice x with h | h <;> rw [h]; exact puiseuxOrder_neg x

theorem puiseux_lt_iff_initCoeff (u v : PuiseuxSeries R) :
    u < v ↔ 0 < puiseuxInitCoeff R (v - u) := by rw [← sub_pos, puiseux_pos_iff]

/-- **Proposition 2.99 (core of part 2).** A Puiseux series over `R` has non-negative order iff it is
*bounded over `R`*: its absolute value is less than `ι(a)` for some positive `a ∈ R`. -/
theorem bounded_iff_puiseuxOrder_nonneg (x : PuiseuxSeries R) :
    (∃ a : R, 0 < a ∧ |x| < algebraMap R (PuiseuxSeries R) a) ↔ 0 ≤ puiseuxOrder R x := by
  constructor
  · rintro ⟨a, ha, hlt⟩
    by_contra hneg
    rw [not_le] at hneg
    have hx : x ≠ 0 := by rintro rfl; rw [puiseuxOrder_zero] at hneg; exact absurd hneg (by simp)
    have habs : 0 < |x| := abs_pos.mpr hx
    rw [puiseux_lt_iff_initCoeff] at hlt
    have heq : algebraMap R (PuiseuxSeries R) a - |x| = algebraMap R (PuiseuxSeries R) a + (-|x|) := by
      ring
    rw [heq, puiseuxInitCoeff_add_eq_right _ _ (by
        rw [puiseuxOrder_neg, puiseuxOrder_abs, puiseuxOrder_algebraMap_of_ne ha.ne']; exact hneg),
      puiseuxInitCoeff_neg] at hlt
    have : 0 < puiseuxInitCoeff R |x| := (puiseux_pos_iff _).mp habs
    linarith
  · intro h0
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨1, one_pos, by rw [abs_zero, map_one]; exact zero_lt_one⟩
    · by_cases ho : puiseuxOrder R x = 0
      · set c := puiseuxInitCoeff R x with hc
        have hsub : 0 < puiseuxOrder R (x - algebraMap R (PuiseuxSeries R) c) := by
          rw [algebraMap_eq_constPuiseux]; exact puiseuxOrder_sub_constPuiseux_leadingCoeff_pos ho
        have hac1 : (0 : R) < |c| + 1 - c := by have := le_abs_self c; linarith
        have hac2 : (0 : R) < |c| + 1 + c := by have := neg_abs_le c; linarith
        refine ⟨|c| + 1, by have := abs_nonneg c; linarith, ?_⟩
        rw [abs_lt]
        refine ⟨?_, ?_⟩
        · rw [puiseux_lt_iff_initCoeff]
          have heq : x - -algebraMap R (PuiseuxSeries R) (|c| + 1)
              = (x - algebraMap R (PuiseuxSeries R) c)
                + algebraMap R (PuiseuxSeries R) ((|c| + 1) + c) := by
            simp only [map_add]; ring
          rw [heq, puiseuxInitCoeff_add_eq_right _ _ (by
              rw [puiseuxOrder_algebraMap_of_ne hac2.ne']; exact hsub),
            puiseuxInitCoeff_algebraMap]
          exact hac2
        · rw [puiseux_lt_iff_initCoeff]
          have heq : algebraMap R (PuiseuxSeries R) (|c| + 1) - x
              = algebraMap R (PuiseuxSeries R) ((|c| + 1) - c)
                + -(x - algebraMap R (PuiseuxSeries R) c) := by
            simp only [map_sub]; ring
          rw [heq, puiseuxInitCoeff_add_eq_left _ _ (by
              rw [puiseuxOrder_algebraMap_of_ne hac1.ne', puiseuxOrder_neg]; exact hsub),
            puiseuxInitCoeff_algebraMap]
          exact hac1
      · have hopos : 0 < puiseuxOrder R x := lt_of_le_of_ne h0 (Ne.symm ho)
        refine ⟨1, one_pos, ?_⟩
        rw [abs_lt]
        refine ⟨?_, ?_⟩
        · rw [puiseux_lt_iff_initCoeff]
          have heq : x - -algebraMap R (PuiseuxSeries R) 1 = x + algebraMap R (PuiseuxSeries R) 1 := by
            ring
          rw [heq, puiseuxInitCoeff_add_eq_right _ _ (by
              rw [puiseuxOrder_algebraMap_of_ne one_ne_zero]; exact hopos),
            puiseuxInitCoeff_algebraMap]
          exact one_pos
        · rw [puiseux_lt_iff_initCoeff]
          have heq : algebraMap R (PuiseuxSeries R) 1 - x = algebraMap R (PuiseuxSeries R) 1 + -x := by
            ring
          rw [heq, puiseuxInitCoeff_add_eq_left _ _ (by
              rw [puiseuxOrder_algebraMap_of_ne one_ne_zero, puiseuxOrder_neg]; exact hopos),
            puiseuxInitCoeff_algebraMap]
          exact one_pos

/-- **Proposition 2.99 (part 2).** For `R` real closed, an algebraic Puiseux series lies in
`R⟨ε⟩_b` exactly when it is bounded over `R`. -/
theorem mem_puiseuxBounded_iff_bounded (y : algebraicPuiseux R) :
    y ∈ puiseuxBounded R ↔
      ∃ a : R, 0 < a ∧ |(y : PuiseuxSeries R)| < algebraMap R (PuiseuxSeries R) a := by
  rw [mem_puiseuxBounded]; exact (bounded_iff_puiseuxOrder_nonneg _).symm

end Ordered

end Azurite.BPR
