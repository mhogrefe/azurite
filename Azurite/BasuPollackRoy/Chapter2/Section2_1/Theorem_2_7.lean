/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_8
import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealField
import Azurite.BasuPollackRoy.Chapter2.Section2_1.SumOfSquares
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.TFAE

/-! # BPR Section 2.1 — Theorem 2.7: Equivalent characterizations of real fields

> Let `F` be a field. The following are equivalent:
> - **(a)** `F` is a real field (`IsRealField F`).
> - **(b)** `F` has a proper cone (`∃ C : Subsemiring F, IsProperCone C`).
> - **(c)** `F` can be ordered (`∃ T : RingCone F, HasMemOrNegMem T`).
>     A `RingCone` with totality is exactly the data of a linear field
>     ordering (positive cone = elements of T; `IsCone` holds automatically
>     since `HasMemOrNegMem` implies every square is in T).
> - **(d)** For every finite family `x : Fin n → F`, `∑ i, x i ^ 2 = 0 →
>     ∀ i, x i = 0`.

**Proof outline.**
- a) ⇒ b): `ΣF^{(2)}` is a proper cone when F is real.
- b) ⇒ c): Proposition 2.8 (Zorn's lemma) extends any proper cone to a
  total one.
- c) ⇒ d): If `∑ xᵢ² = 0` and xₖ ≠ 0, then `∑_{i≠k} xᵢ²` and its negative
  `xₖ²` are both in T, forcing `∑_{i≠k} xᵢ² = 0` (antisymmetry), then
  xₖ² = 0.
- d) ⇒ a): If −1 ∈ ΣF^{(2)}, then −1 = ∑ aᵢ², so 1² + ∑ aᵢ² = 0, giving
  1 = 0.
-/

namespace Azurite.BPR

variable {F : Type*} [Field F]

/-- Extract a Fin-indexed vector from an `IsSumSq` witness. -/
lemma isSumSq_exists_vector {s : F} (h : IsSumSq s) :
    ∃ (n : ℕ) (x : Fin n → F), s = ∑ i, x i * x i := by
  induction h with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | sq_add a _ ih =>
    obtain ⟨n, x, rfl⟩ := ih
    exact ⟨n + 1, Fin.cons a x, by simp [Fin.sum_univ_succ]⟩

/-- **Theorem 2.7 a) ⇒ b).** A real field has a proper cone, namely `ΣF^{(2)}`. -/
theorem theorem_2_7_a_of_b (ha : IsRealField F) : ∃ C : Subsemiring F, IsProperCone C :=
  ⟨sumOfSquares F, isCone_sumOfSquares F, (isRealField_iff_neg_one_notMem F).mp ha⟩

/-- **Theorem 2.7 b) ⇒ c).** A proper cone extends to a `RingCone` with totality
    (Proposition 2.8). -/
theorem theorem_2_7_b_of_c (hb : ∃ C : Subsemiring F, IsProperCone C) :
    ∃ T : RingCone F, HasMemOrNegMem T := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨T, _, hT⟩ := prop_2_8 hC
  exact ⟨T, hT⟩

/-- **Theorem 2.7 c) ⇒ d).** If F has a total RingCone, then every
    finite sum of squares that equals 0 forces all summands to be 0. -/
theorem theorem_2_7_c_of_d (hc : ∃ T : RingCone F, HasMemOrNegMem T) :
    ∀ (n : ℕ) (x : Fin n → F), (∑ i, x i ^ 2 = 0) → ∀ k, x k = 0 := by
  obtain ⟨T, hT⟩ := hc
  intro n x hsum k
  -- S := ∑_{i ≠ k} xᵢ²
  set S := ∑ i ∈ Finset.univ.erase k, x i ^ 2 with hS_def
  -- S + xk² = 0 (from hsum via Finset.sum_erase_add)
  have hSk : S + x k ^ 2 = 0 := by
    have hera : ∑ i ∈ Finset.univ.erase k, x i ^ 2 + x k ^ 2 = ∑ i : Fin n, x i ^ 2 :=
      Finset.sum_erase_add Finset.univ _ (Finset.mem_univ k)
    linear_combination hera.trans hsum
  -- Each xᵢ² is in T: by HasMemOrNegMem, xᵢ ∈ T or -xᵢ ∈ T; in either case xᵢ² = xᵢ·xᵢ ∈ T
  have hmem : ∀ i : Fin n, x i ^ 2 ∈ T.toSubsemiring := fun i => by
    rw [sq]
    rcases hT.mem_or_neg_mem (x i) with h | h
    · exact T.toSubsemiring.mul_mem h h
    · have := T.toSubsemiring.mul_mem h h
      rwa [neg_mul_neg] at this
  -- S ∈ T (sum of elements in a subsemiring)
  have hS_mem : S ∈ T.toSubsemiring :=
    T.toSubsemiring.sum_mem fun i _ => hmem i
  -- -S = xk² ∈ T
  have hneg_eq : -S = x k ^ 2 := by linear_combination -hSk
  have hneg_mem : -S ∈ T.toSubsemiring := hneg_eq ▸ hmem k
  -- By RingCone antisymmetry: S = 0
  have hS0 : S = 0 := T.eq_zero_of_mem_of_neg_mem' hS_mem hneg_mem
  -- xk² = 0 hence xk = 0
  have hk2 : x k ^ 2 = 0 := by rw [hS0, zero_add] at hSk; exact hSk
  exact pow_eq_zero_iff (by norm_num) |>.mp hk2

/-- **Theorem 2.7 d) ⇒ a).** If sums of squares vanish only trivially,
    then −1 is not a sum of squares. -/
theorem theorem_2_7_d_of_a
    (hd : ∀ (n : ℕ) (x : Fin n → F), (∑ i, x i ^ 2 = 0) → ∀ k, x k = 0) :
    IsRealField F := by
  rw [isRealField_iff]
  intro h
  obtain ⟨n, x, hx⟩ := isSumSq_exists_vector h
  -- Let y = Fin.cons 1 x : Fin (n+1) → F (prepend 1)
  let y : Fin (n + 1) → F := Fin.cons 1 x
  have hkey : ∑ i : Fin (n + 1), y i ^ 2 = 0 := by
    simp only [y, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sq]
    -- goal: 1 * 1 + ∑ i, x i * x i = 0
    -- hx : -1 = ∑ i, x i * x i, so ∑ x i * x i = -1
    have : ∑ i : Fin n, x i * x i = -1 := hx.symm
    rw [this]; ring
  have h1 := hd (n + 1) y hkey ⟨0, Nat.zero_lt_succ n⟩
  simp [y, Fin.cons_zero] at h1

/-- **Theorem 2.7 (BPR p.37).** The four characterizations of real fields are equivalent.

The `List.TFAE` structure lets us extract any pairwise implication via `theorem_2_7.out`. -/
theorem theorem_2_7 {F : Type*} [Field F] : List.TFAE
    [ IsRealField F,
      ∃ C : Subsemiring F, IsProperCone C,
      ∃ T : RingCone F, HasMemOrNegMem T,
      ∀ (n : ℕ) (x : Fin n → F), (∑ i, x i ^ 2 = 0) → ∀ k, x k = 0] := by
  tfae_have 1 → 2 := theorem_2_7_a_of_b
  tfae_have 2 → 3 := theorem_2_7_b_of_c
  tfae_have 3 → 4 := theorem_2_7_c_of_d
  tfae_have 4 → 1 := theorem_2_7_d_of_a
  tfae_finish

end Azurite.BPR
