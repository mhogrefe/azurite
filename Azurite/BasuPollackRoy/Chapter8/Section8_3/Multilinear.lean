/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# BPR §8.3.2.1: multilinear, alternating, and antisymmetric mappings

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.3.2.1.

Let `K` be a field and `0 < m ≤ n`. For a mapping `Φ` from `(𝓕_n)^m` to
`𝓕_{n-m+1}` — where `𝓕_n = Polynomial.degreeLT K n` is the space of polynomials
of degree `< n` — BPR defines three properties:

* **multilinear**: `Φ` is `K`-linear in each argument;
* **alternating**: `Φ` vanishes whenever two arguments are equal;
* **antisymmetric**: swapping two arguments negates the value.

These are formalized as predicates `IsMultilinear`, `IsAlternating`,
`IsAntisymmetric` on `Φ`. The "`…, X_i, …`" slot notation is `Function.update`,
and the swap of two slots is precomposition with `Equiv.swap`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-- **BPR §8.3.2.1.** `Φ : (𝓕_n)^m → 𝓕_{n-m+1}` is **multilinear** if, for every
    argument slot `i` and scalars `a, b ∈ K`,
    `Φ(…, a•A + b•B, …) = a•Φ(…, A, …) + b•Φ(…, B, …)`. -/
def IsMultilinear (Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)) : Prop :=
  ∀ (v : Fin m → degreeLT K n) (i : Fin m) (a b : K) (A B : degreeLT K n),
    Φ (Function.update v i (a • A + b • B))
      = a • Φ (Function.update v i A) + b • Φ (Function.update v i B)

/-- **BPR §8.3.2.1.** `Φ : (𝓕_n)^m → 𝓕_{n-m+1}` is **alternating** if it vanishes
    whenever two of its arguments are equal: `Φ(…, A, …, A, …) = 0`. -/
def IsAlternating (Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)) : Prop :=
  ∀ (v : Fin m → degreeLT K n) (i j : Fin m), i ≠ j → v i = v j → Φ v = 0

/-- **BPR §8.3.2.1.** `Φ : (𝓕_n)^m → 𝓕_{n-m+1}` is **antisymmetric** if swapping
    two of its arguments negates the value:
    `Φ(…, A, …, B, …) = -Φ(…, B, …, A, …)`. -/
def IsAntisymmetric (Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)) : Prop :=
  ∀ (v : Fin m → degreeLT K n) (i j : Fin m), i ≠ j → Φ (v ∘ ⇑(Equiv.swap i j)) = - Φ v

/-- **BPR Lemma 8.26.** A multilinear and alternating mapping is antisymmetric.

    Proof: fixing all but two slots `i ≠ j`, the form `g X Y := Φ(…, X, …, Y, …)`
    is bilinear (multilinearity) and vanishes on the diagonal `g X X = 0`
    (alternating). Hence `0 = g(A+B, A+B) = g A B + g B A`, i.e. swapping the two
    slots negates the value (`A = v i`, `B = v j`). -/
theorem isAntisymmetric_of_isMultilinear_of_isAlternating
    {Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)}
    (hM : IsMultilinear Φ) (hA : IsAlternating Φ) : IsAntisymmetric Φ := by
  intro v i j hij
  -- The bilinear form on slots `i, j`.
  let g : degreeLT K n → degreeLT K n → degreeLT K (n - m + 1) :=
    fun X Y => Φ (Function.update (Function.update v i X) j Y)
  -- Diagonal vanishes (two equal arguments).
  have gdiag : ∀ X, g X X = 0 := by
    intro X
    show Φ (Function.update (Function.update v i X) j X) = 0
    refine hA _ i j hij ?_
    rw [Function.update_self, Function.update_of_ne hij, Function.update_self]
  -- Additivity in the second slot (multilinearity with scalars `1`).
  have gaddY : ∀ X Y₁ Y₂, g X (Y₁ + Y₂) = g X Y₁ + g X Y₂ := by
    intro X Y₁ Y₂
    show Φ (Function.update (Function.update v i X) j (Y₁ + Y₂))
      = Φ (Function.update (Function.update v i X) j Y₁)
        + Φ (Function.update (Function.update v i X) j Y₂)
    rw [show Y₁ + Y₂ = (1 : K) • Y₁ + (1 : K) • Y₂ by simp,
      hM (Function.update v i X) j 1 1 Y₁ Y₂, one_smul, one_smul]
  -- Additivity in the first slot (commute the two updates, then multilinearity).
  have gaddX : ∀ X₁ X₂ Y, g (X₁ + X₂) Y = g X₁ Y + g X₂ Y := by
    intro X₁ X₂ Y
    show Φ (Function.update (Function.update v i (X₁ + X₂)) j Y)
      = Φ (Function.update (Function.update v i X₁) j Y)
        + Φ (Function.update (Function.update v i X₂) j Y)
    rw [show X₁ + X₂ = (1 : K) • X₁ + (1 : K) • X₂ by simp,
      Function.update_comm hij ((1 : K) • X₁ + (1 : K) • X₂) Y v,
      hM (Function.update v j Y) i 1 1 X₁ X₂, one_smul, one_smul,
      ← Function.update_comm hij X₁ Y v, ← Function.update_comm hij X₂ Y v]
  -- The two cross terms sum to zero: `0 = g(A+B, A+B) = g A B + g B A`.
  have key : g (v i) (v j) + g (v j) (v i) = 0 := by
    have h0 := gdiag (v i + v j)
    rw [gaddX, gaddY, gaddY, gdiag, gdiag] at h0
    simpa using h0
  -- Identify `Φ v` and `Φ (v ∘ swap)` with the cross terms.
  have hΦv : Φ v = g (v i) (v j) := by
    show Φ v = Φ (Function.update (Function.update v i (v i)) j (v j))
    rw [Function.update_eq_self, Function.update_eq_self]
  have hswap : Φ (v ∘ ⇑(Equiv.swap i j)) = g (v j) (v i) := by
    show Φ (v ∘ ⇑(Equiv.swap i j))
      = Φ (Function.update (Function.update v i (v j)) j (v i))
    congr 1
    funext k
    simp only [Function.comp_apply]
    rcases eq_or_ne k i with rfl | hki
    · rw [Equiv.swap_apply_left, Function.update_of_ne hij, Function.update_self]
    · rcases eq_or_ne k j with rfl | hkj
      · rw [Equiv.swap_apply_right, Function.update_self]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, Function.update_of_ne hkj,
          Function.update_of_ne hki]
  rw [hswap, hΦv]
  exact eq_neg_of_add_eq_zero_right key

end Azurite.BPR.Chapter8
