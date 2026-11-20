/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PsiZero

/-!
## A search with a certificate, and the tight enclosures of the zeros of `ψ`

`searchCertified c w₀ h` returns the first answer among `c (w₀)`, `c (2 w₀)`, `c (4 w₀)`, …;
the certificate `h` says that there is one, so the search needs no fuel.

`psiZeroTightAt n V w` is the enclosure of the `n`-th zero of `ψ` at Ziv level `w` when it is
narrower than `2^(−V)`.  The search over the levels (`psiZeroEnclAt`,
`AzFloat/GammaExtremum.lean`) is certified by `psiZeroTightAt_exists`
(`Equiv/GammaExtremumCertificate.lean`): the enclosures converge.
-/

namespace Azurite.AzFloat

/-- The first answer among `c (w₀ 2^f)`, `f = 0, 1, 2, …`, given that there is one. -/
def searchCertified {α : Type} (c : Nat → Option α) (w₀ : Nat)
    (h : ∃ f : Nat, (c (w₀ * 2 ^ f)).isSome = true) : α :=
  go h 0 (fun _ hg => absurd hg (Nat.not_lt_zero _))
where
  go (h : ∃ f : Nat, (c (w₀ * 2 ^ f)).isSome = true) (f : Nat)
      (hf : ∀ g < f, (c (w₀ * 2 ^ g)).isSome = false) : α :=
    match hr : c (w₀ * 2 ^ f) with
    | some r => r
    | none => go h (f + 1) (fun g hg => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg' | rfl
        · exact hf g hg'
        · rw [hr]; rfl)
  termination_by Nat.find h - f
  decreasing_by
    have hlt : f < Nat.find h := by
      by_contra hcon
      push Not at hcon
      have hspec := Nat.find_spec h
      rcases Nat.lt_or_eq_of_le hcon with hlt' | heq
      · rw [hf _ hlt'] at hspec; exact Bool.false_ne_true hspec
      · rw [heq, hr] at hspec; exact Bool.false_ne_true hspec
    omega

/-- The enclosure of the `n`-th zero of `ψ` at Ziv level `w`, when it is narrower than
`2^(−V)`. -/
def psiZeroTightAt (n V w : Nat) : Option Encl :=
  (psiZeroEncl n w).filter (psiZeroNarrow · (2 * V))

end Azurite.AzFloat
