/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaExtremumBracket
import Azurite.AzFloat.Equiv.PsiZero

/-!
# The certificate of the tight enclosures of the zeros of `ψ`

`psiZeroTightAt_exists`: for every `V`, some level `w₀ 2^f` gives an enclosure of the `n`-th
zero narrower than `2^(−V)` — because the enclosures converge (`psiZeroEncl_conv`, which
rests on the verified bisection behind the fast enclosure).  `searchCertified_eq`: the
certified search returns one of the answers.
-/

namespace Azurite.AzFloat

open Filter Topology

/-- The certified search returns the answer at one of its levels. -/
theorem searchCertified_go_eq {α : Type} (c : ℕ → Option α) (w₀ : ℕ)
    (h : ∃ f : ℕ, (c (w₀ * 2 ^ f)).isSome = true) :
    ∀ (m f : ℕ) (hf : ∀ g < f, (c (w₀ * 2 ^ g)).isSome = false), Nat.find h - f = m →
      ∃ f' : ℕ, c (w₀ * 2 ^ f') = some (searchCertified.go c w₀ h f hf)
  | m, f, hf, hm => by
    rw [searchCertified.go.eq_def]
    split
    · rename_i r hr
      exact ⟨f, hr⟩
    · rename_i hr
      have hlt : f < Nat.find h := by
        by_contra hcon
        push Not at hcon
        have hspec := Nat.find_spec h
        rcases Nat.lt_or_eq_of_le hcon with hlt' | heq
        · rw [hf _ hlt'] at hspec; exact Bool.false_ne_true hspec
        · rw [heq, hr] at hspec; exact Bool.false_ne_true hspec
      cases m with
      | zero => omega
      | succ m => exact searchCertified_go_eq c w₀ h m (f + 1) _ (by omega)

theorem searchCertified_eq {α : Type} (c : ℕ → Option α) (w₀ : ℕ)
    (h : ∃ f : ℕ, (c (w₀ * 2 ^ f)).isSome = true) :
    ∃ f : ℕ, c (w₀ * 2 ^ f) = some (searchCertified c w₀ h) :=
  searchCertified_go_eq c w₀ h _ 0 _ rfl

/-- An enclosure of width at most `2^(−V−1)` passes the test for `2^(−V)`. -/
theorem psiZeroNarrow_of_width {b : Encl} {x : ℝ} {V : ℕ}
    (hb : AEncl b x ((1 / 2 : ℝ) ^ (V + 1))) : psiZeroNarrow b (2 * V) = true := by
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := hb
  obtain ⟨r, hr, -, hr2⟩ := subCeiling_abs hu hl 64
  have h0 : 0 ≤ u - l := by linarith
  rw [abs_of_nonneg h0] at hr2
  have hp : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
  have hV : (1 / 2 : ℝ) ^ (V + 1) = (1 / 2 : ℝ) ^ V / 2 := by
    rw [pow_succ]
    ring
  unfold psiZeroNarrow
  rw [le_eq_true_iff hr (toVal_powerOf2 _), AzInt.toInt_ofInt, two_zpow_neg_nat,
    Nat.mul_div_cancel_left V two_pos]
  nlinarith

/-- **Some level gives an enclosure of the zero narrower than `2^(−V)`.** -/
theorem psiZeroTightAt_exists (n V w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (psiZeroTightAt n V (w₀ * 2 ^ f)).isSome = true := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (psiZeroEncl_conv n (ε := (1 / 2 : ℝ) ^ (V + 1)) (by positivity))
  have hle : N ≤ w₀ * 2 ^ N :=
    (Nat.lt_two_pow_self).le.trans (Nat.le_mul_of_pos_left _ hw₀)
  obtain ⟨b, hb, hA⟩ := hN _ hle
  refine ⟨N, ?_⟩
  unfold psiZeroTightAt
  rw [hb, Option.filter_some, psiZeroNarrow_of_width hA]
  rfl

end Azurite.AzFloat
