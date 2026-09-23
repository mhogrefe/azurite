/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_15

/-! # BPR Section 2.1 — Properties of the graded lexicographic ordering

These three supplementary results back up Definition 2.15:

* `grlex_bot`         — the zero multi-index is the grlex-smallest;
* `grlex_add_right`   — grlex is compatible with addition of multi-indices;
* `grlex_le_set_finite` — for any `α`, the grlex-≤ down-set of `α` is finite.

The last property is the key contrast with the plain lex order
(`lex_le_set_infinite`): grading by total degree compactifies the down-sets.
-/

namespace Azurite.BPR

open Finsupp.DegLex in
/-- The zero multi-index (monomial `1`) is the grlex-smallest: for any nonzero `α`,
    `0 <_grlex α`. -/
theorem grlex_bot {k : ℕ} {α : Fin k →₀ ℕ} (hα : α ≠ 0) :
    GrlexOrder k 0 α := by
  exact bot_lt_iff_ne_bot.mpr (show toDegLex α ≠ ⊥ from fun h => hα (toDegLex_inj.mp h))

open Finsupp.DegLex in
/-- The grlex ordering on monomials is compatible with multiplication:
    if `α <_grlex β` then `α + γ <_grlex β + γ`. -/
theorem grlex_add_right {k : ℕ} {α β γ : Fin k →₀ ℕ}
    (h : GrlexOrder k α β) :
    GrlexOrder k (α + γ) (β + γ) := by
  simp only [GrlexOrder, lt_iff, ofDegLex_toDegLex] at *
  rcases h with hdeg | ⟨hdeq, hlex⟩
  · left; simp [map_add]; omega
  · right
    exact ⟨by simp [map_add, hdeq], by simpa [toLex_add] using add_lt_add_right hlex (toLex γ)⟩

open Finsupp.DegLex in
/-- The set of monomials grlex-≤ a given monomial is always finite.
    This is because grlex-≤ implies bounded total degree, and there
    are finitely many monomials of bounded total degree in `k` variables. -/
theorem grlex_le_set_finite {k : ℕ} (α : Fin k →₀ ℕ) :
    Set.Finite {β : Fin k →₀ ℕ | GrlexOrder k β α ∨ β = α} := by
  apply Set.Finite.subset (Finsupp.finite_of_degree_le α.degree)
  intro β hβ
  rcases hβ with hlt | heq
  · exact monotone_degree (le_of_lt hlt)
  · simp [heq]

end Azurite.BPR
