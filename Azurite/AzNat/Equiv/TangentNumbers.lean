/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.TangentNumbers
import Azurite.AzNat.Equiv.MulNat
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Factorial
import Azurite.BrentZimmermann.Chapter4.TangentAlgorithm

/-!
# Equivalence: the tangent numbers

`TangentRepr T m a`: the array `T` of length `m` holds the row `a` of the model of Algorithm 4.3
(`BZ.tangentPass`, `BZ.tangentOuter`), `a j` at index `j − 1`.  The loops preserve it
(`tangentPassArr_repr`, `tangentOuterArr_repr`), so `tangentNumbers m` is
`BZ.tangentNumbersModel m`, hence the tangent numbers (`toNat_tangentNumbers`).
-/

namespace Azurite.AzNat

open BZ

/-- The array `T` of length `m` holds `a 1, …, a m`. -/
def TangentRepr (T : Array AzNat) (m : ℕ) (a : ℕ → ℕ) : Prop :=
  T.size = m ∧ ∀ j, 1 ≤ j → j ≤ m → (T.getD (j - 1) 0).toNat = a j

theorem tangentPassArr_repr {k m : ℕ} (hk : 2 ≤ k) {T : Array AzNat} {a : ℕ → ℕ}
    (h : TangentRepr T m a) :
    ∀ s, k + s ≤ m + 1 → TangentRepr (tangentPassArr k T s) m (tangentPass k a s)
  | 0, _ => h
  | s + 1, hs => by
    obtain ⟨hsz, hval⟩ := tangentPassArr_repr hk h s (by omega)
    rw [tangentPassArr, tangentPass]
    refine ⟨by rw [Array.size_setIfInBounds]; exact hsz, fun j h1 hj => ?_⟩
    unfold tangentStep
    by_cases hjk : j = k + s
    · subst hjk
      rw [Function.update_self, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt
        (by omega), Option.getD_some, toNat_add, toNat_mulNat, toNat_mulNat,
        show k + s - 2 = (k + s - 1) - 1 by omega, hval (k + s - 1) (by omega) (by omega),
        hval (k + s) (by omega) (by omega), Nat.add_sub_cancel_left]
      ring
    · rw [Function.update_of_ne hjk, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_ne (by omega), ← Array.getD_eq_getD_getElem?]
      exact hval j h1 hj

theorem tangentOuterArr_repr {m : ℕ} {T : Array AzNat} {a : ℕ → ℕ} (h : TangentRepr T m a) :
    ∀ r, r + 1 ≤ m → TangentRepr (tangentOuterArr m T r) m (tangentOuter m a r)
  | 0, _ => h
  | r + 1, hr => by
    rw [tangentOuterArr, tangentOuter]
    exact tangentPassArr_repr (by omega) (tangentOuterArr_repr h r (by omega)) _ (by omega)

theorem size_tangentNumbers (m : ℕ) : (tangentNumbers m).size = m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · have h0 : TangentRepr (Array.ofFn (n := m) fun i => factorial i.val) m tangentInit := by
      refine ⟨Array.size_ofFn, fun j h1 hj => ?_⟩
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
      simp [show j - 1 < m by omega, toNat_factorial, tangentInit]
    exact (tangentOuterArr_repr h0 (m - 1) (by omega)).1

/-- **The array holds the tangent numbers**: `T_j` at index `j − 1`. -/
theorem toNat_tangentNumbers {m j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ m) :
    ((((tangentNumbers m).getD (j - 1) 0).toNat : ℕ) : ℤ) = tangentNumber j := by
  have hm : 1 ≤ m := h1.trans hj
  have h0 : TangentRepr (Array.ofFn (n := m) fun i => factorial i.val) m tangentInit := by
    refine ⟨Array.size_ofFn, fun j h1 hj => ?_⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp [show j - 1 < m by omega, toNat_factorial, tangentInit]
  have := (tangentOuterArr_repr h0 (m - 1) (by omega)).2 j h1 hj
  rw [← tangentNumbersModel_eq hm h1 hj]
  exact_mod_cast this

end Azurite.AzNat
