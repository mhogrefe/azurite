/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_28

/-!
# BPR Definition 2.29: Thom Encoding

**Definition 2.29 (BPR).** A sign condition `σ` on `Der(P)` is a *Thom encoding*
of `x ∈ R` if `σ(P) = 0` and `Reali(σ) = {x}`.

By Proposition 2.28 part 1 (root injectivity), if `P ≠ 0` and `σ(P) = 0`, then
any `x ∈ derReali P n σ` satisfies `derReali P n σ = {x}`, i.e.\ `σ` is
automatically a Thom encoding of `x`.
-/

namespace Azurite.BPR.Proposition2_28

open Polynomial Azurite.BPR Azurite.BPR.Proposition2_27

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Definition 2.29 (Thom encoding).** A sign condition `σ` on `Der(P)` is
    a *Thom encoding* of `x ∈ R` if `σ(P) = 0` and the derivative realization
    set `{y | ∀ i ≤ n, sign(P⁽ⁱ⁾(y)) = σ(i)}` equals `{x}`. -/
def IsThomEncoding (P : R[X]) (n : ℕ) (σ : ℕ → SignType) (x : R) : Prop :=
  σ 0 = 0 ∧ derReali P n σ = {x}

/-- A root realization gives a Thom encoding: if `P ≠ 0`, `σ(P) = 0`, and
    `x ∈ derReali P n σ`, then `σ` is a Thom encoding of `x`. -/
theorem isThomEncoding_of_mem (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (hP : P ≠ 0) (n : ℕ) (σ : ℕ → SignType) (hn : P.natDegree ≤ n)
    (hσ0 : σ 0 = 0) (x : R) (hx : x ∈ derReali P n σ) :
    IsThomEncoding P n σ x :=
  ⟨hσ0, Set.eq_singleton_iff_unique_mem.mpr
    ⟨hx, fun _ hy => proposition_2_28_part1 hIVP P hP n σ hn hσ0 _ x hy hx⟩⟩

theorem isThomEncoding_of_mem_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) (hP : P ≠ 0) (n : ℕ) (σ : ℕ → SignType) (hn : P.natDegree ≤ n)
    (hσ0 : σ 0 = 0) (x : R)
    (hx : letI : LinearOrder R := IsRealClosed.toLinearOrder; x ∈ derReali P n σ) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    IsThomEncoding P n σ x := by
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  have : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  exact isThomEncoding_of_mem Theorem2_11.theorem_2_11_b_c P hP n σ hn hσ0 x hx

end Azurite.BPR.Proposition2_28
