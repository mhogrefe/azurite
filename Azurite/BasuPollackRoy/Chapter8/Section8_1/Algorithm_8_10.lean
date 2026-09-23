/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_1.Notation_8_7
import Azurite.BasuPollackRoy.Chapter8.Section8_1.Algorithm_8_8
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# BPR §8.1 Algorithm 8.10: Special translation

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

Given `P = aₚ Xᵖ + ⋯ + a₀ ∈ A[X]` and `b, c ∈ A`, compute the
polynomial `Q = cᵖ · P((X − b) / c)` without leaving `A`:

  - Initialize `result := aₚ`, `d := 1`.
  - For `i` from `1` to `p`:
    - `d := c · d`
    - `result := result · (c·X − b) + (d · aₚ₋ᵢ)`
  - Output `result = cᵖ · P((X − b) / c)`.

The intermediate polynomial sequence is captured by
`Polynomial.specialTrans`, defined (outside `Azurite.BPR`, extending
Mathlib's `Polynomial`) via the recurrence above. Over a field with
`c ≠ 0`, this satisfies `specialTrans P b c i = C(cⁱ) · Hor_i(P, X − b/c)`
where `Hor_i` is the Horner polynomial from Notation 8.7. The bitsize
bound on the coefficients of `specialTrans` over `ℤ` is recorded as
`Polynomial.bitsize_specialTrans_coeff_le`.
-/

section SpecialTranslation

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **BPR Algorithm 8.10 (Special Translation).** Given `P ∈ R[X]`
    with `p = natDegree P`, and elements `b, c ∈ R`, the `i`-th
    intermediate polynomial is:
    - `specialTrans P b c 0 = C(aₚ)`
    - `specialTrans P b c (i+1) = (C c * X - C b) * specialTrans P b c i
                                    + C(c^{i+1} * aₚ₋ᵢ₋₁)`

    The output `specialTrans P b c p = cᵖ P((X − b)/c)`. -/
noncomputable def Polynomial.specialTrans (P : R[X]) (b c : R) : ℕ → R[X]
  | 0 => C (P.coeff P.natDegree)
  | i + 1 => (C c * X - C b) * P.specialTrans b c i +
      C (c ^ (i + 1) * P.coeff (P.natDegree - (i + 1)))

/-- The base case: `specialTrans P b c 0 = C(leadingCoeff P)`. -/
theorem Polynomial.specialTrans_zero (P : R[X]) (b c : R) :
    P.specialTrans b c 0 = C P.leadingCoeff := by
  unfold Polynomial.specialTrans; rw [leadingCoeff]

/-- The recurrence for `specialTrans`. -/
theorem Polynomial.specialTrans_succ (P : R[X]) (b c : R) (i : ℕ) :
    P.specialTrans b c (i + 1) =
      (C c * X - C b) * P.specialTrans b c i +
      C (c ^ (i + 1) * P.coeff (P.natDegree - (i + 1))) :=
  rfl
/-- **Closed-form characterization.**
    `specialTrans P b c i = ∑ j ∈ range (i+1), C(aₚ₋ⱼ · cʲ) · (cX − b)^{i−j}`. -/
theorem Polynomial.specialTrans_eq_sum (P : R[X]) (b c : R) (i : ℕ) :
    P.specialTrans b c i = ∑ j ∈ range (i + 1),
      C (P.coeff (P.natDegree - j) * c ^ j) * (C c * X - C b) ^ (i - j) := by
  induction i with
  | zero => simp [Polynomial.specialTrans]
  | succ n ih =>
    rw [Polynomial.specialTrans, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show n + 1 - (n + 1) = 0 from Nat.sub_self _, pow_zero, mul_one,
        show c ^ (n + 1) * P.coeff (P.natDegree - (n + 1)) =
          P.coeff (P.natDegree - (n + 1)) * c ^ (n + 1) from by ring]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mul_comm (C c * X - C b), mul_assoc, ← pow_succ,
        show n - j + 1 = n + 1 - j from by omega]

private theorem cx_sub_b_eq {K : Type*} [Field K] (b c : K) (hc : c ≠ 0) :
    X - C (b * c⁻¹) = C c⁻¹ * (C c * X - C b) := by
  have h1 : C c⁻¹ * (C c * X) = X := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  have h2 : C c⁻¹ * C b = C (b * c⁻¹) := by
    rw [← map_mul, mul_comm]
  rw [mul_sub, h1, h2]

/-- **BPR Algorithm 8.10 (field characterization).**
    Over a field with `c ≠ 0`:

    `specialTrans P b c i = C(cⁱ) · Horᵢ(P, X − b·c⁻¹)`,

    i.e. `SpecialTransᵢ = cⁱ (aₚ(X − b/c)ⁱ + ⋯ + aₚ₋ᵢ)`. -/
theorem Polynomial.specialTrans_eq_horner_comp {K : Type*} [Field K]
    (P : K[X]) (b c : K) (hc : c ≠ 0) (i : ℕ) :
    P.specialTrans b c i =
      C (c ^ i) * (P.horner i).comp (X - C (b * c⁻¹)) := by
  rw [Polynomial.horner_eq_sum, Polynomial.specialTrans_eq_sum]
  show _ = C (c ^ i) * eval₂ C (X - C (b * c⁻¹)) _
  rw [eval₂_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj; rw [Finset.mem_range] at hj
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  rw [cx_sub_b_eq b c hc, mul_pow]
  simp only [← C_pow, ← mul_assoc, ← map_mul]
  congr 1; congr 1
  rw [show c⁻¹ ^ (i - j) = (c ^ (i - j))⁻¹ from inv_pow c (i - j)]
  rw [show c ^ i * P.coeff (P.natDegree - j) * (c ^ (i - j))⁻¹ =
    P.coeff (P.natDegree - j) * (c ^ i * (c ^ (i - j))⁻¹) from by ring]
  rw [← pow_sub₀ c hc (by omega : i - j ≤ i),
      show i - (i - j) = j from by omega]

end SpecialTranslation

/-! ### Bitsize bound on SpecialTrans coefficients -/

section SpecialTransBitsize

open Polynomial Finset Azurite.BPR

/-- The bitsize of a coefficient of `(cX − b)^n` is at most `n(1 + τ')`
    when `n ≥ 1` and `bitsize(b), bitsize(c) ≤ τ'`. -/
private theorem bitsize_coeff_cX_sub_b_pow (b c : ℤ) (n m τ' : ℕ)
    (hn : 0 < n)
    (hb : Int.size b ≤ τ') (hc : Int.size c ≤ τ') :
    Int.size (((C c * X - C b) ^ n).coeff m) ≤ n * (1 + τ') := by
  -- By the binomial theorem, coeff m ((cX-b)^n) = choose(n,m) · c^m · (-b)^{n-m}.
  -- bitsize(choose(n,m)) ≤ n and bitsize(c^m · (-b)^{n-m}) ≤ n·τ', giving n·(1+τ').
  by_cases hm : n < m
  · -- m > n: coefficient is 0
    have hdeg : natDegree ((C c * X - C b) ^ n) ≤ n := by
      calc natDegree ((C c * X - C b) ^ n)
          ≤ n * natDegree (C c * X - C b) := Polynomial.natDegree_pow_le
        _ ≤ n * 1 := Nat.mul_le_mul_left _ (by
            rw [sub_eq_add_neg, ← map_neg]; exact Polynomial.natDegree_linear_le)
        _ = n := Nat.mul_one _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [Int.size]
  · push Not at hm
    -- m ≤ n: expand via binomial theorem, only the j = m term survives
    rw [sub_eq_add_neg, ← map_neg, Commute.add_pow (Commute.all _ _)]
    simp only [finsetSum_coeff, coeff_mul_natCast, mul_pow, ← C_pow, coeff_mul_C, coeff_C_mul,
               coeff_X_pow]

    rw [Finset.sum_eq_single_of_mem m (mem_range.mpr (by omega))]
    · -- j = m term
      simp only [ite_true, mul_one]
      unfold Int.size at *
      -- bitsize(c^m · (-b)^{n-m} · choose(n,m)) ≤ n·τ' + n = n·(1+τ')
      have hprod : (c ^ m * (-b) ^ (n - m)).natAbs.size ≤ n * τ' := by
        have hbm : (-b).natAbs.size ≤ τ' := by rwa [Int.natAbs_neg]
        set L := List.replicate m c ++ List.replicate (n - m) (-b)
        have hLne : L ≠ [] := by
          apply List.ne_nil_of_length_pos
          simp only [L, List.length_append, List.length_replicate]; omega
        have hLlen : L.length = n := by
          simp only [L, List.length_append, List.length_replicate]; omega
        have hprod_eq : L.prod = c ^ m * (-b) ^ (n - m) := by
          simp only [L, List.prod_append, List.prod_replicate]
        rw [← hprod_eq, ← Int.size, ← hLlen]
        exact Int.size_list_prod_le L τ' hLne (by
          intro x hx
          simp only [L, List.mem_append, List.mem_replicate] at hx
          rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact hc
          · exact hbm)
      have hchoose : (↑(n.choose m) : ℤ).natAbs.size ≤ n := by
        simp only [Int.natAbs_natCast, Nat.size_le]
        exact_mod_cast Nat.choose_lt_two_pow n m hn
      calc (c ^ m * (-b) ^ (n - m) * ↑(n.choose m)).natAbs.size
          ≤ (c ^ m * (-b) ^ (n - m)).natAbs.size + (↑(n.choose m) : ℤ).natAbs.size :=
            Int.size_mul_le _ _ _ _ (le_refl _) (le_refl _)
        _ ≤ n * τ' + n := Nat.add_le_add hprod hchoose
        _ = n * (1 + τ') := by ring
    · intro j _ hjm
      simp only [ite_eq_right (Ne.symm hjm), mul_zero, zero_mul]

/-- The bitsize of the coefficient of `X^m` in the `k`-th summand
    `C(aₚ₋ₖ · cᵏ) · (cX − b)^{i−k}` is at most `τ + i(1 + τ')`. -/
private theorem bitsize_specialTrans_summand (P : ℤ[X]) (b c : ℤ)
    (i k m τ τ' : ℕ) (hk : k ≤ i)
    (hτ : ∀ j, Int.size (P.coeff j) ≤ τ)
    (hb : Int.size b ≤ τ') (hc : Int.size c ≤ τ') :
    Int.size ((C (P.coeff (P.natDegree - k) * c ^ k) *
      (C c * X - C b) ^ (i - k)).coeff m) ≤ τ + i * (1 + τ') := by
  -- coeff m (C(a_{p-k} * c^k) * (cX-b)^{i-k}) = a_{p-k} * c^k * coeff m ((cX-b)^{i-k})
  simp only [coeff_C_mul]
  unfold Int.size at *
  -- Helper: (c^j).natAbs.size ≤ j * τ'
  -- Helper: (a * c^j).natAbs.size ≤ a.natAbs.size + j * τ'
  have hmul_c_pow : ∀ (a : ℤ) (j : ℕ),
      (a * c ^ j).natAbs.size ≤ a.natAbs.size + j * τ' := by
    intro a j; rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · calc (a * c ^ j).natAbs.size
          ≤ a.natAbs.size + (c ^ j).natAbs.size :=
            Int.size_mul_le _ _ _ _ (le_refl _) (le_refl _)
        _ ≤ a.natAbs.size + j * τ' := by
            apply Nat.add_le_add_left
            rw [Int.natAbs_pow, Nat.size_le, show j * τ' = τ' * j from by ring, pow_mul]
            exact Nat.pow_lt_pow_left (Nat.size_le.mp hc) (Nat.pos_iff_ne_zero.mp hj)
  by_cases hik : i - k = 0
  · -- i = k: (cX-b)^0 = 1
    have hki : k = i := by omega
    simp only [hik, pow_zero, coeff_one]
    split
    · -- m = 0
      simp only [mul_one]
      calc (P.coeff (P.natDegree - k) * c ^ k).natAbs.size
          ≤ (P.coeff (P.natDegree - k)).natAbs.size + k * τ' :=
            hmul_c_pow _ k
        _ ≤ τ + k * τ' := Nat.add_le_add (hτ _) (le_refl _)
        _ ≤ τ + i * (1 + τ') := by nlinarith
    · -- m ≠ 0
      simp
  · -- i - k > 0: use bitsize_coeff_cX_sub_b_pow
    have hik_pos : 0 < i - k := by omega
    calc (P.coeff (P.natDegree - k) * c ^ k * ((C c * X - C b) ^ (i - k)).coeff m).natAbs.size
        ≤ (P.coeff (P.natDegree - k) * c ^ k).natAbs.size +
          (((C c * X - C b) ^ (i - k)).coeff m).natAbs.size :=
          Int.size_mul_le _ _ _ _ (le_refl _) (le_refl _)
      _ ≤ (τ + k * τ') + ((i - k) * (1 + τ')) := by
          apply Nat.add_le_add
          · calc (P.coeff (P.natDegree - k) * c ^ k).natAbs.size
                ≤ (P.coeff (P.natDegree - k)).natAbs.size + k * τ' :=
                  hmul_c_pow _ k
              _ ≤ τ + k * τ' := Nat.add_le_add (hτ _) (le_refl _)
          · exact bitsize_coeff_cX_sub_b_pow b c (i - k) m τ' hik_pos hb hc
      _ ≤ τ + i * (1 + τ') := by
          -- k*τ' + (i-k)*(1+τ') ≤ i*(1+τ')
          suffices h : k * τ' + (i - k) * (1 + τ') ≤ i * (1 + τ') by omega
          calc k * τ' + (i - k) * (1 + τ')
              = k * τ' + (i - k) + (i - k) * τ' := by ring
            _ = (i - k) + (k + (i - k)) * τ' := by ring
            _ = (i - k) + i * τ' := by rw [Nat.add_sub_cancel' hk]
            _ ≤ i + i * τ' := by omega
            _ = i * (1 + τ') := by ring

/-- **BPR §8.1 (bitsize of SpecialTrans coefficients).**
    Let `P ∈ ℤ[X]` with `p = natDegree P` and coefficient bitsizes bounded by `τ`.
    Let `b, c ∈ ℤ` with bitsizes bounded by `τ'`. Then for `i ≤ p`:

      `bitsize(coeff m (specialTrans P b c i)) ≤ τ + i(1 + τ') + bitsize(p + 1)`. -/
theorem Polynomial.bitsize_specialTrans_coeff_le (P : ℤ[X]) (b c : ℤ) (i τ τ' : ℕ)
    (hi : i ≤ P.natDegree)
    (hτ : ∀ k, Int.size (P.coeff k) ≤ τ)
    (hb : Int.size b ≤ τ') (hc : Int.size c ≤ τ') :
    ∀ m, Int.size ((P.specialTrans b c i).coeff m) ≤
      τ + i * (1 + τ') + Nat.size (P.natDegree + 1) := by
  intro m
  rw [Polynomial.specialTrans_eq_sum, finsetSum_coeff]
  unfold Int.size at *
  -- Each summand has coeff of bitsize ≤ τ + i*(1+τ')
  have hB : ∀ j ∈ range (i + 1),
      ((C (P.coeff (P.natDegree - j) * c ^ j) *
        (C c * X - C b) ^ (i - j)).coeff m).natAbs.size ≤ τ + i * (1 + τ') := by
    intro j hj
    have hji : j ≤ i := by simp [Finset.mem_range] at hj; omega
    exact bitsize_specialTrans_summand P b c i j m τ τ' hji hτ hb hc
  calc (∑ j ∈ range (i + 1), ((C (P.coeff (P.natDegree - j) * c ^ j) *
          (C c * X - C b) ^ (i - j)).coeff m)).natAbs.size
      ≤ (τ + i * (1 + τ')) + Nat.size (range (i + 1)).card :=
        Int.size_finset_sum_le hB
    _ = τ + i * (1 + τ') + Nat.size (i + 1) := by simp [Finset.card_range]
    _ ≤ τ + i * (1 + τ') + Nat.size (P.natDegree + 1) := by
        apply Nat.add_le_add_left
        exact Nat.size_le_size (by omega)

end SpecialTransBitsize
