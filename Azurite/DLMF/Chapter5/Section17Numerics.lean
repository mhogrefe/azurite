/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.GlaisherKinkelin
import Azurite.AzFloat.Equiv.Interval

/-!
# DLMF §5.17: the decimals of Glaisher's constant

**DLMF 5.17.6**: `A = 1.28242 71291 00622 63687 …`.

`dlmf_5_17_6_numerics`: `1.28242712910062263687 < A < 1.28242712910062263688`, from the
enclosure of the Glaisher–Kinkelin constant of `AzFloat/GlaisherKinkelin.lean` at Ziv level
`72`, evaluated in the kernel (`glaisherKinkelinEnds_data`), and its specification
`glaisherKinkelinCore_spec`.
-/

namespace Azurite.DLMF

open Azurite.AzFloat

/-- The two ends of the enclosure of `A` at Ziv level `w`, as exact fractions. -/
def glaisherKinkelinEnds (w : ℕ) : Option (Bool × ℕ × ℕ) × Option (Bool × ℕ × ℕ) :=
  match glaisherKinkelinCore w with
  | some r => (valData r.2.1, valData r.2.2)
  | none => (none, none)

set_option maxRecDepth 100000 in
/-- The enclosure of `A` at Ziv level `72`. -/
theorem glaisherKinkelinEnds_data :
    glaisherKinkelinEnds 72 =
      (some (true, 193794908518000760334137, 151115727451828646838272),
        some (true, 387589817036001520668923, 302231454903657293676544)) := by
  decide +kernel

/-- **DLMF 5.17.6** (decimals): `A = 1.28242 71291 00622 63687 …`. -/
theorem dlmf_5_17_6_numerics :
    1.28242712910062263687 < glaisherA ∧ glaisherA < 1.28242712910062263688 := by
  have hdata := glaisherKinkelinEnds_data
  unfold glaisherKinkelinEnds at hdata
  cases hr : glaisherKinkelinCore 72 with
  | none =>
    rw [hr] at hdata
    exact absurd (Prod.mk.inj hdata).1 (by simp)
  | some r =>
    obtain ⟨neg, b⟩ := r
    rw [hr] at hdata
    obtain ⟨d1, d2⟩ := Prod.mk.inj hdata
    obtain ⟨l, u, hl, hu, hl0, h1, h2⟩ := glaisherKinkelinCore_spec (by norm_num) hr
    rw [toVal_of_valData d1, Option.some.injEq, EReal.coe_eq_coe_iff] at hl
    rw [toVal_of_valData d2, Option.some.injEq, EReal.coe_eq_coe_iff] at hu
    have hA0 : 0 < glaisherA := Real.exp_pos _
    have hneg : neg = false := by
      cases neg
      · rfl
      · simp only [↓reduceIte] at h1
        linarith
    subst hneg
    rw [← hl] at h1
    rw [← hu] at h2
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, signedVal] at h1 h2
    push_cast at h1 h2
    exact ⟨lt_of_lt_of_le (by norm_num) h1, lt_of_le_of_lt h2 (by norm_num)⟩

end Azurite.DLMF
