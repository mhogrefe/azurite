/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.SignConditionTransfer
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_28

/-! # Thom encodings transfer along order-preserving embeddings

The Thom encoding of a root (BPR §2.1, `derReali`/`IsThomEncoding`) is a sign
condition on the iterated derivatives `P', P'', …`. This file bridges that
description to the §2.4 sign-condition counting framework (`realizationOver` on a
finite family) and concludes:

* `derReali_eq_realizationOver` — the Thom realization set is exactly the
  realization of the derivative family `thomFamily`;
* `derReali_nonempty_transfer` — a Thom sign condition is realized by a root in
  `R` iff it is realized in `R'`, for two order-preserving extensions of the
  ordered field `F`.

Together with root injectivity (`proposition_2_28_part1`) and the order criterion
(`proposition_2_28_part2`), this gives a canonical, order-preserving bijection
between the roots of `P ∈ F[X]` in `R` and in `R'` — the engine of the
Artin–Schreier embedding extension and the uniqueness of the real closure.
-/

open scoped Polynomial

namespace Azurite.BPR

open _root_.Polynomial Azurite.BPR.Proposition2_27

/-- The Thom derivative family `(P', P'', …, P⁽ⁿ⁾)`, indexed by `Fin n`. -/
noncomputable def thomFamily {R : Type*} [Field R] (P : R[X]) (n : ℕ) : Fin n → R[X] :=
  fun i => (⇑derivative)^[(i : ℕ) + 1] P

/-- A Thom sign condition (indexed by `ℕ`) restricted to the derivative-family
indices `Fin n` (dropping the `σ 0` entry, which records `P(x) = 0`). -/
def thomSC (n : ℕ) (σ : ℕ → SignType) : SignCondition (Fin n) := fun i => σ ((i : ℕ) + 1)

/-- `thomFamily` commutes with `map φ`. -/
lemma thomFamily_map {R R' : Type*} [Field R] [Field R'] (φ : R →+* R') (P : R[X]) (n : ℕ) :
    (fun i => (thomFamily P n i).map φ) = thomFamily (P.map φ) n := by
  funext i
  simp only [thomFamily]
  exact (iterate_derivative_map P φ ((i : ℕ) + 1)).symm

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
/-- **Bridge.** The Thom realization set `derReali P n σ` (for `σ 0 = 0`) equals
the §2.4 realization of the derivative family: the `σ 0 = 0` entry becomes the
root condition `P(x) = 0`, and the remaining entries become the sign condition
`thomSC n σ` on `thomFamily P n`. -/
lemma derReali_eq_realizationOver (P : R[X]) (n : ℕ) (σ : ℕ → SignType) (hσ0 : σ 0 = 0) :
    derReali P n σ = SignCondition.realizationOver (thomSC n σ) P (thomFamily P n) := by
  ext x
  rw [SignCondition.mem_realizationOver]
  simp only [derReali, Set.mem_ofPred_eq, thomFamily, thomSC]
  constructor
  · intro h
    refine ⟨?_, fun i => h ((i : ℕ) + 1) (by omega)⟩
    have h0 := h 0 (Nat.zero_le n)
    rw [Function.iterate_zero_apply, hσ0] at h0
    exact sign_eq_zero_iff.mp h0
  · rintro ⟨hroot, h⟩ i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [Function.iterate_zero_apply, hσ0, hroot, sign_zero]
    · have hi' : (i - 1) < n := by omega
      have := h ⟨i - 1, hi'⟩
      simpa [Nat.sub_add_cancel hipos] using this

/-- **Thom encoding realization transfers.** A Thom sign condition `σ` (with
`σ 0 = 0`) on `P ∈ F[X]` is realized by a root in `R` iff it is realized in `R'`,
for two order-preserving embeddings of `F` into fields with the intermediate
value property. So a root of `P` in `R` and the root of `P` in `R'` carrying the
same Thom encoding exist together. -/
theorem derReali_nonempty_transfer
    {F R R' : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field R'] [LinearOrder R'] [IsStrictOrderedRing R']
    (hR : HasIntermediateValueProperty R) (hR' : HasIntermediateValueProperty R')
    (ι : F →+* R) (hι : StrictMono ι) (τ : F →+* R') (hτ : StrictMono τ)
    (n : ℕ) (P : F[X]) (hP : P ≠ 0) (σ : ℕ → SignType) (hσ0 : σ 0 = 0) :
    (derReali (P.map ι) n σ).Nonempty ↔ (derReali (P.map τ) n σ).Nonempty := by
  rw [derReali_eq_realizationOver _ n σ hσ0, derReali_eq_realizationOver _ n σ hσ0,
    ← thomFamily_map ι P n, ← thomFamily_map τ P n]
  exact realizationOver_nonempty_transfer hR hR' ι hι τ hτ n P hP (thomFamily P n) (thomSC n σ)

end Azurite.BPR
