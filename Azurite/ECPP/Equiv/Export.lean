/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Export
import Azurite.ECPP.Equiv.Check
import Azurite.AzNat.Equiv.IsPrimeAprcl

/-!
# Soundness of the checker of certificates for exchange

**`checkExport_prime`**: `checkExport n cert = true → Nat.Prime n.toNat`.  The conversion
`toStepCert` is only a function into the proven `check` (whatever point it computes, `check`
tests it), and the empty certificate is decided by `AzNat.isPrimeAprcl`.

**`strictBound_nat`**: the bound `(⌊√q⌋ − 1)⁴ > n` of other verifiers implies the two
conditions on `q` of `checkStep`; `strictBound_eq_true_iff` ties the computed test to it.
-/

namespace Azurite.ECPP

/-- **An accepted certificate for exchange proves primality.** -/
theorem checkExport_prime {n : AzNat} {cert : List ExportStep}
    (h : checkExport n cert = true) : Nat.Prime n.toNat := by
  unfold checkExport at h
  split at h
  · rw [Bool.and_eq_true] at h
    exact (AzNat.isPrimeAprcl_eq_true_iff n).1 h.2
  · rw [Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    split at h
    · exact check_prime h
    · exact absurd h (by simp)

/-- **The bound of other verifiers implies the checker's**: if `(⌊√q⌋ − 1)⁴ > n` then, with
`s = ⌊√n⌋`, `s + 1 < q` and `4s < (q − s − 1)²`. -/
theorem strictBound_nat {n q : ℕ} (h : n < (Nat.sqrt q - 1) ^ 4) :
    Nat.sqrt n + 1 < q ∧ 4 * Nat.sqrt n < (q - Nat.sqrt n - 1) ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ u, u = Nat.sqrt q - 1 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt n := ⟨_, rfl⟩
  rw [← hu] at h
  rw [← hs]
  have hsn : s * s ≤ n := hs ▸ Nat.sqrt_le n
  have hrq : Nat.sqrt q * Nat.sqrt q ≤ q := Nat.sqrt_le q
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0] at h
      simp at h
    · exact h0
  have hr : Nat.sqrt q = u + 1 := by omega
  rw [hr] at hrq
  -- `s < u²`
  have hsu : s < u * u := by
    by_contra hc
    push Not at hc
    have : (u * u) * (u * u) ≤ s * s := Nat.mul_le_mul hc hc
    have h4 : u ^ 4 = (u * u) * (u * u) := by ring
    omega
  obtain ⟨w, hw⟩ : ∃ w, w = u * u := ⟨_, rfl⟩
  rw [← hw] at hsu
  have hq : w + 2 * u + 1 ≤ q := by
    have : (u + 1) * (u + 1) = w + 2 * u + 1 := by rw [hw]; ring
    omega
  refine ⟨by omega, ?_⟩
  have hd : 2 * u + 1 ≤ q - s - 1 := by omega
  have h2 : (2 * u + 1) ^ 2 ≤ (q - s - 1) ^ 2 := Nat.pow_le_pow_left hd 2
  have h3 : (2 * u + 1) ^ 2 = 4 * w + 4 * u + 1 := by rw [hw]; ring
  omega

/-- `strictBound` computes its bound. -/
theorem strictBound_eq_true_iff (n q : AzNat) :
    strictBound n q = true ↔ n.toNat < (Nat.sqrt q.toNat - 1) ^ 4 := by
  unfold strictBound
  simp only [decide_eq_true_eq]
  rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_mul, AzNat.toNat_mul, AzNat.toNat_sub,
    AzNat.toNat_sqrt, AzNat.toNat_ofNat]
  have : (Nat.sqrt q.toNat - 1) ^ 4 =
      (Nat.sqrt q.toNat - 1) * (Nat.sqrt q.toNat - 1) *
        ((Nat.sqrt q.toNat - 1) * (Nat.sqrt q.toNat - 1)) := by ring
  rw [this]

end Azurite.ECPP
