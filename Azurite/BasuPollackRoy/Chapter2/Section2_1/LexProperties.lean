/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_14
import Mathlib.Data.Finsupp.Basic

/-! # BPR Section 2.1 — Properties of the lexicographic ordering on monomials

BPR notes three key properties of the lex ordering on monomials `Fin k →₀ ℕ`:

1. The smallest monomial is `1` (the zero exponent).
2. The ordering is compatible with multiplication (addition of exponents).
3. The set of monomials `≤ₗₑₓ` a given monomial can be infinite.

The third property is what motivates the graded refinement (Definition 2.15):
plain lex has infinite down-sets for `k ≥ 2`, while grlex's down-sets are
always finite (`grlex_le_set_finite` in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.GrlexProperties`).
-/

namespace Azurite.BPR

/-- The zero multi-index (monomial `1`) is the lex-smallest: for any nonzero `α`,
    `0 <ₗₑₓ α`. -/
theorem lex_bot {k : ℕ} {α : Fin k →₀ ℕ} (hα : α ≠ 0) :
    LexOrder k ℕ 0 α := by
  simp only [LexOrder, Pi.Lex, Pi.zero_apply]
  rw [Finsupp.ne_iff] at hα
  obtain ⟨i, hi⟩ := hα
  have hi' : 0 < α i := by simp [Finsupp.coe_zero] at hi; omega
  classical
  let S := Finset.univ.filter (fun j : Fin k => 0 < α j)
  have hS : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩⟩
  refine ⟨S.min' hS, fun m hm => ?_, ?_⟩
  · by_contra h; push Not at h
    have : 0 < α m := Nat.pos_of_ne_zero (by omega)
    exact absurd (Finset.min'_le S m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩))
      (not_le.mpr hm)
  · exact (Finset.mem_filter.mp (Finset.min'_mem S hS)).2

/-- The lex ordering on monomials is compatible with multiplication:
    if `α <ₗₑₓ β` then `α + γ <ₗₑₓ β + γ`. -/
theorem lex_add_right {k : ℕ} {α β γ : Fin k →₀ ℕ}
    (h : LexOrder k ℕ α β) :
    LexOrder k ℕ (α + γ) (β + γ) := by
  simp only [LexOrder, Pi.Lex] at *
  obtain ⟨i, hi_eq, hi_lt⟩ := h
  refine ⟨i, fun m hm => ?_, ?_⟩
  · simp [Pi.add_apply, hi_eq m hm]
  · simp [Pi.add_apply]; omega

/-- The set of monomials lex-≤ a given monomial can be infinite.
    Concretely, for `k ≥ 2` and `α = X₁`, the set
    `{β | LexOrder k ℕ β α ∨ β = α}` is infinite. -/
theorem lex_le_set_infinite {k : ℕ} (hk : 2 ≤ k) :
    Set.Infinite {β : Fin k →₀ ℕ | LexOrder k ℕ β (Finsupp.single ⟨0, by omega⟩ 1) ∨
      β = Finsupp.single ⟨0, by omega⟩ 1} := by
  -- For any n, Finsupp.single ⟨1, _⟩ n is in the set (since its 0-th component is 0 < 1)
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => Finsupp.single ⟨1, by omega⟩ n)
  · intro a b hab
    simp [Finsupp.single_eq_single_iff] at hab
    omega
  · intro n
    left
    simp only [LexOrder, Pi.Lex]
    exact ⟨⟨0, by omega⟩, fun j hj => absurd hj (not_lt.mpr (Fin.mk_le_mk.mpr (Nat.zero_le _))),
      by simp [Fin.ext_iff]⟩

end Azurite.BPR
