/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Product
import Azurite.AzFloat.Equiv.Mul
import Azurite.AzFloat.Equiv.Sum
import Azurite.AzNat.Equiv.SumProduct
import Azurite.AzInt.Equiv.SumProduct

/-!
## Correctness of `AzFloat.productPrecRound`

`productPrecRound_eq`: the product is the correct rounding of `Spec.product`, the fold of the
two-operand specification `Spec.mul` over the values.  `Spec.product_eq` puts the specification
in case form (a `NaN` factor; a zero with an infinity; an infinity, with the sign of the
product; a zero; the real product), and `realProd_eq` identifies the real product of a list of
finite nonzero floats with the signed product of the cores on the summed scale that
`roundScaled` rounds.
-/

namespace Azurite.AzFloat

/-! ### The specification -/

namespace Spec

/-- The specification of a product: the fold of `mul` over the values, `NaN` propagating. -/
noncomputable def product (xs : List AzFloat) : Option EReal :=
  xs.foldr (fun x acc => x.toVal.bind fun a => acc.bind fun b => mul a b) (some 1)

theorem mul_inf_inf (s t : Bool) :
    mul (if s then ⊤ else ⊥) (if t then ⊤ else ⊥) = some (if (s == t) then ⊤ else ⊥) := by
  unfold mul
  cases s <;> cases t <;> simp

theorem mul_zero_inf (t : Bool) : mul 0 (if t then ⊤ else ⊥) = none := by
  unfold mul; cases t <;> simp

theorem mul_inf_zero (s : Bool) : mul (if s then ⊤ else ⊥) 0 = none := by
  unfold mul; cases s <;> simp

theorem mul_zero_coe (r : ℝ) : mul 0 (r : EReal) = some 0 := by unfold mul; simp

theorem mul_zero_zero : mul 0 0 = some 0 := by unfold mul; simp

theorem mul_coe_zero (r : ℝ) : mul (r : EReal) 0 = some 0 := by unfold mul; simp

end Spec

/-! ### The classification predicates on constructors -/

@[simp] theorem isNaN_nan : isNaN nan = true := rfl
@[simp] theorem isNaN_infinity (s : Bool) : isNaN (infinity s) = false := rfl
@[simp] theorem isNaN_zero : isNaN zero = false := rfl
@[simp] theorem isNaN_finite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (h : FiniteValid p m) :
    isNaN (finite s e p m h) = false := rfl
@[simp] theorem isInfinite_nan : isInfinite nan = false := rfl
@[simp] theorem isInfinite_infinity (s : Bool) : isInfinite (infinity s) = true := rfl
@[simp] theorem isInfinite_zero : isInfinite zero = false := rfl
@[simp] theorem isInfinite_finite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat)
    (h : FiniteValid p m) : isInfinite (finite s e p m h) = false := rfl
@[simp] theorem isZero_nan : isZero nan = false := rfl
@[simp] theorem isZero_infinity (s : Bool) : isZero (infinity s) = false := rfl
@[simp] theorem isZero_zero : isZero zero = true := rfl
@[simp] theorem isZero_finite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (h : FiniteValid p m) :
    isZero (finite s e p m h) = false := rfl
@[simp] theorem isNegative_infinity (s : Bool) : isNegative (infinity s) = !s := rfl
@[simp] theorem isNegative_zero : isNegative zero = false := rfl
@[simp] theorem isNegative_finite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat)
    (h : FiniteValid p m) : isNegative (finite s e p m h) = !s := rfl

/-- A float that is not `NaN`, infinite or zero is finite and nonzero. -/
theorem isNormal_of_flags {y : AzFloat} (h1 : y.isNaN = false) (h2 : y.isInfinite = false)
    (h3 : y.isZero = false) : y.isNormal = true := by
  cases y <;> simp_all [isNormal]

/-- Every member of a list without `NaN`, infinities or zeros is finite and nonzero. -/
theorem isNormal_of_any_flags {xs : List AzFloat} (h1 : ¬ xs.any isNaN = true)
    (h2 : ¬ xs.any isInfinite = true) (h3 : ¬ xs.any isZero = true) :
    ∀ y ∈ xs, y.isNormal = true := by
  intro y hy
  simp only [List.any_eq_true, not_exists, not_and] at h1 h2 h3
  exact isNormal_of_flags (Bool.eq_false_iff.mpr (h1 y hy)) (Bool.eq_false_iff.mpr (h2 y hy))
    (Bool.eq_false_iff.mpr (h3 y hy))

/-- The real product of the finite values of a list. -/
noncomputable def realProd (xs : List AzFloat) : ℝ := (xs.map fval).prod

@[simp] theorem realProd_nil : realProd [] = 1 := rfl

theorem realProd_cons (x : AzFloat) (xs : List AzFloat) :
    realProd (x :: xs) = fval x * realProd xs := by
  simp [realProd]

theorem productSign_nil : productSign [] = true := rfl

theorem productSign_cons (x : AzFloat) (xs : List AzFloat) :
    productSign (x :: xs) = ((!x.isNegative) == productSign xs) := by
  unfold productSign
  rw [List.countP_cons]
  cases x.isNegative <;> cases h : decide (List.countP isNegative xs % 2 = 0) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h <;> simp <;> omega

theorem finiteVal_ne_zero_of_valid (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) : finiteVal s e m ≠ 0 := by
  rw [finiteVal_eq_core s e hv]
  exact finiteVal_ne_zero' s e _ (coreSignificand_ne_zero hv)

theorem decide_pos_finiteVal_of_valid (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) : decide (0 < finiteVal s e m) = s := by
  rw [finiteVal_eq_core s e hv, decide_pos_finiteVal s e _ (coreSignificand_ne_zero hv)]

theorem decide_pos_fval {x : AzFloat} (hx : x.isNormal = true) :
    decide (0 < fval x) = !x.isNegative := by
  cases x with
  | finite s e q m hv =>
    show decide (0 < finiteVal s e m) = !(!s)
    rw [Bool.not_not, decide_pos_finiteVal_of_valid s e hv]
  | _ => simp [isNormal] at hx

theorem fval_ne_zero {x : AzFloat} (hx : x.isNormal = true) : fval x ≠ 0 := by
  cases x with
  | finite s e q m hv => exact finiteVal_ne_zero_of_valid s e hv
  | _ => simp [isNormal] at hx

/-- The real product of a list of finite nonzero floats is nonzero, and positive exactly when
`productSign` says so. -/
theorem realProd_spec (xs : List AzFloat) (h : ∀ x ∈ xs, x.isNormal = true) :
    realProd xs ≠ 0 ∧ decide (0 < realProd xs) = productSign xs := by
  induction xs with
  | nil => simp [productSign_nil]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    obtain ⟨hne, hsign⟩ := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    rw [realProd_cons, productSign_cons, ← hsign, ← decide_pos_fval hx]
    refine ⟨mul_ne_zero (fval_ne_zero hx) hne, ?_⟩
    rcases lt_or_gt_of_ne (fval_ne_zero hx) with h1 | h1 <;>
      rcases lt_or_gt_of_ne hne with h2 | h2
    · rw [decide_eq_true (mul_pos_of_neg_of_neg h1 h2), decide_eq_false (not_lt.mpr h1.le),
        decide_eq_false (not_lt.mpr h2.le)]; rfl
    · rw [decide_eq_false (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg h1.le h2.le)),
        decide_eq_false (not_lt.mpr h1.le), decide_eq_true h2]; rfl
    · rw [decide_eq_false (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos h1.le h2.le)),
        decide_eq_true h1, decide_eq_false (not_lt.mpr h2.le)]; rfl
    · rw [decide_eq_true (mul_pos h1 h2), decide_eq_true h1, decide_eq_true h2]; rfl

/-- The specification, by cases: a `NaN` factor, or a zero with an infinity, gives `NaN`; an
infinity gives the infinity with the sign of the product; a zero gives zero; otherwise the real
product. -/
theorem Spec.product_eq (xs : List AzFloat) :
    Spec.product xs =
      if xs.any isNaN = true then none
      else if xs.any isZero = true ∧ xs.any isInfinite = true then none
      else if xs.any isInfinite = true then some (if productSign xs then ⊤ else ⊥)
      else if xs.any isZero = true then some 0
      else some ((realProd xs : ℝ) : EReal) := by
  induction xs with
  | nil => simp [Spec.product]
  | cons x xs ih =>
    rw [Spec.product, List.foldr_cons, ← Spec.product, ih]
    simp only [List.any_cons, realProd_cons, productSign_cons]
    by_cases hN : xs.any isNaN = true
    · cases x <;> simp [hN]
    have hN' : xs.any isNaN = false := Bool.eq_false_iff.mpr hN
    by_cases hI : xs.any isInfinite = true
    · by_cases hZ : xs.any isZero = true
      · cases x <;> simp [hN', hI, hZ]
      · have hZ' : xs.any isZero = false := Bool.eq_false_iff.mpr hZ
        cases x with
        | nan => simp
        | infinity s => simp [hN', hI, hZ', Spec.mul_inf_inf]
        | zero => simp [hN', hI, hZ', Spec.mul_zero_inf]
        | finite s e q m hv =>
          simp only [isNaN_finite, isInfinite_finite, isZero_finite, isNegative_finite, hN', hI,
            hZ', Bool.false_eq_true, false_and, Bool.not_not, toVal_finite, Option.bind_some,
            ↓reduceIte]
          rw [Spec.mul_coe_inf _ (finiteVal_ne_zero_of_valid s e hv) _,
            decide_pos_finiteVal_of_valid s e hv]
          simp
    · have hI' : xs.any isInfinite = false := Bool.eq_false_iff.mpr hI
      by_cases hZ : xs.any isZero = true
      · cases x with
        | nan => simp
        | infinity s => simp [hN', hI', hZ, Spec.mul_inf_zero]
        | zero => simp [hN', hI', hZ, Spec.mul_zero_zero]
        | finite s e q m hv => simp [hN', hI', hZ, Spec.mul_coe_zero]
      · have hZ' : xs.any isZero = false := Bool.eq_false_iff.mpr hZ
        obtain ⟨hne, hsign⟩ := realProd_spec xs (isNormal_of_any_flags hN hI hZ)
        cases x with
        | nan => simp
        | infinity s =>
          simp only [isNaN_infinity, isInfinite_infinity, isZero_infinity, isNegative_infinity,
            hN', hI', hZ', Bool.false_eq_true, and_false, Bool.not_not, toVal_infinity,
            Option.bind_some, ↓reduceIte]
          rw [Spec.mul_inf_coe s _ hne, hsign]
          simp
        | zero => simp [hN', hI', hZ', Spec.mul_zero_coe]
        | finite s e q m hv =>
          simp only [isNaN_finite, isInfinite_finite, isZero_finite, hN', hI', hZ',
            Bool.false_eq_true, and_false, toVal_finite, Option.bind_some, ↓reduceIte,
            Spec.mul_coe_coe]
          rfl

/-! ### The signed product of the cores -/

/-- The real product of a list of finite nonzero floats is the signed product of the cores on
the summed scale. -/
theorem realProd_eq (xs : List AzFloat) (h : ∀ x ∈ xs, x.isNormal = true) :
    (if productSign xs then (1 : ℝ) else -1)
        * (((AzNat.product ((xs.filterMap coreParts).map fun t => t.2.1)).toNat : ℕ) : ℝ)
        * (2 : ℝ) ^ (AzInt.sum ((xs.filterMap coreParts).map fun t => t.2.2)).toInt
      = realProd xs := by
  induction xs with
  | nil => simp [productSign_nil, AzNat.toNat_product, AzInt.toInt_sum]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases x with
    | finite s e q m hv =>
      rw [realProd_cons, ← ih, productSign_cons, List.filterMap_cons_some
        (show coreParts (finite s e q m hv)
          = some (s, coreSignificand q m, e - (AzNat.ofNat q).toAzInt) from rfl),
        List.map_cons, List.map_cons, AzNat.toNat_product, List.map_cons, List.prod_cons,
        ← AzNat.toNat_product, AzInt.toInt_sum, List.map_cons, List.sum_cons, ← AzInt.toInt_sum]
      show _ = finiteVal s e m * _
      rw [finiteVal_eq_core s e hv, finiteVal_sign s e, finiteVal_true_eq, size_coreSignificand hv,
        AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_add₀ (by norm_num)]
      simp only [isNegative, Bool.not_not]
      push_cast
      rw [← signed_mul]
      ring
    | _ => simp [isNormal] at hx

/-! ### The main theorem -/

/-- **`productPrecRound` is the correct rounding of the product**: `NaN` for a `NaN` factor or
a zero with an infinity, the signed infinity for an infinity, zero for a zero, and otherwise
the rounding of the exact real product, with the tag comparing the result to it. -/
theorem productPrecRound_eq (xs : List AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    productPrecRound xs p mode = roundVal p mode (Spec.product xs) := by
  rw [Spec.product_eq]
  unfold productPrecRound
  dsimp only
  by_cases hN : xs.any isNaN = true
  · simp only [hN, ↓reduceIte]
    rfl
  have hN' : xs.any isNaN = false := Bool.eq_false_iff.mpr hN
  by_cases hI : xs.any isInfinite = true <;> by_cases hZ : xs.any isZero = true
  · simp only [hN', hI, hZ, Bool.false_eq_true, Bool.and_self, and_self, ↓reduceIte]
    rfl
  · have hZ' : xs.any isZero = false := Bool.eq_false_iff.mpr hZ
    simp only [hN', hI, hZ', Bool.false_eq_true, Bool.false_and, false_and, ↓reduceIte]
    exact (roundVal_of_toVal p mode (infinity _) _ (Or.inr rfl) rfl).symm
  · have hI' : xs.any isInfinite = false := Bool.eq_false_iff.mpr hI
    simp only [hN', hI', hZ, Bool.false_eq_true, Bool.and_false, and_false, ↓reduceIte]
    exact (roundVal_of_toVal p mode zero 0 (Or.inr rfl) rfl).symm
  · have hI' : xs.any isInfinite = false := Bool.eq_false_iff.mpr hI
    have hZ' : xs.any isZero = false := Bool.eq_false_iff.mpr hZ
    simp only [hN', hI', hZ', Bool.false_eq_true, Bool.and_self, and_self, ↓reduceIte]
    rw [roundScaled_eq_roundVal, realProd_eq xs (isNormal_of_any_flags hN hI hZ)]

end Azurite.AzFloat
