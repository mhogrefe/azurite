/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.ZMod.Basic

/-! # BPR Section 1.4 — Characteristic of a field

BPR's unnumbered definition (preceding the Lefschetz principle):

> The **characteristic of a field `K`** is a prime number `p` if `K`
> contains `ℤ/pℤ`, and `0` if `K` contains `ℚ`.

We record both halves as predicates `HasCharP K p` and `HasCharZero K` —
expressed structurally as the existence of an injective ring homomorphism
from `ZMod p` or `ℚ` — and prove their equivalence with Mathlib's `CharP`
and `CharZero` typeclasses.
-/

namespace Azurite.BPR

variable (K : Type*) [Field K]

/-- **BPR's characteristic `p` condition.** A field `K` "contains `ℤ/pℤ`":
there exists an injective ring homomorphism `ZMod p → K`. -/
def HasCharP (p : ℕ) : Prop :=
  ∃ f : ZMod p →+* K, Function.Injective f

/-- **BPR's characteristic `0` condition.** A field `K` "contains `ℚ`":
there exists an injective ring homomorphism `ℚ → K`. -/
def HasCharZero : Prop :=
  ∃ f : ℚ →+* K, Function.Injective f

/-- BPR's characteristic-`p` condition is Mathlib's `CharP K p` (for prime `p`). -/
theorem hasCharP_iff_charP (p : ℕ) [Fact p.Prime] :
    HasCharP K p ↔ CharP K p := by
  constructor
  · rintro ⟨f, hinj⟩
    refine ⟨fun n => ?_⟩
    have h_cast : (n : K) = f ((n : ZMod p)) := (map_natCast f n).symm
    rw [h_cast, show (0 : K) = f 0 from f.map_zero.symm, hinj.eq_iff,
        CharP.cast_eq_zero_iff (ZMod p) p n]
  · intro _
    exact ⟨ZMod.castHom (dvd_refl p) K, ZMod.castHom_injective K⟩

/-- BPR's characteristic-`0` condition is Mathlib's `CharZero K`. -/
theorem hasCharZero_iff_charZero :
    HasCharZero K ↔ CharZero K := by
  constructor
  · rintro ⟨f, hinj⟩
    refine ⟨fun n m hnm => ?_⟩
    have h_n : (n : K) = f ((n : ℚ)) := (map_natCast f n).symm
    have h_m : (m : K) = f ((m : ℚ)) := (map_natCast f m).symm
    have h_eq : f ((n : ℚ)) = f ((m : ℚ)) := by rw [← h_n, ← h_m, hnm]
    exact_mod_cast hinj h_eq
  · intro _
    exact ⟨Rat.castHom K, Rat.cast_injective⟩

end Azurite.BPR
