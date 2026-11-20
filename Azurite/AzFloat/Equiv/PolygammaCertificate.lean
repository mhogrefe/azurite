/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PolygammaWidth
import Azurite.AzFloat.Equiv.RoundToInteger
import Azurite.AzFloat.Equiv.BetaCertificate
import Azurite.Transcendental.PolygammaValues

/-!
# The Ziv certificate of the polygamma functions at arguments with irrational values

`polygammaSpecial n x`: `n` odd and `x` a positive integer or a half-integer.  There
`ψ⁽ⁿ⁾(x)` is irrational (`irrational_polygamma_of_special`) and Ziv's loop terminates
(`polygammaApprox_cert`).
-/

namespace Azurite.AzFloat

/-- What `polygammaSpecial` says. -/
theorem polygammaSpecial_spec {n : ℕ} {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hc : polygammaSpecial n x = true) :
    n % 2 = 1 ∧ (0 < xv ∨ ¬ isInteger x = true) ∧
      ∃ N : ℤ, xv = (N : ℝ) / 2 ∧ (N % 2 = 1 ∨ 0 < N) := by
  unfold polygammaSpecial at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨hn, -⟩, h2⟩, hsign⟩ := hc
  have hx2 := toVal_shiftLeft_of_toVal hx (AzInt.ofInt 1)
  rw [AzInt.toInt_ofInt] at hx2
  obtain ⟨N, hN⟩ := (isInteger_iff_of_toVal hx2).mp h2
  have hxv : xv = (N : ℝ) / 2 := by
    have : (2 : ℝ) ^ (1 : ℤ) = 2 := by norm_num
    rw [this] at hN
    linarith
  have hsign' : 0 < xv ∨ ¬ isInteger x = true := by
    rcases hsign with h | h
    · exact Or.inl ((lt_eq_true_iff toVal_zero' hx).mp h)
    · exact Or.inr (by simp [h])
  refine ⟨hn, hsign', N, hxv, ?_⟩
  rcases hsign' with h | h
  · right
    have : (0 : ℝ) < N := by rw [hxv] at h; linarith
    exact_mod_cast this
  · left
    by_contra hodd
    apply h
    obtain ⟨k, hk⟩ : ∃ k : ℤ, N = 2 * k := ⟨N / 2, by omega⟩
    refine (isInteger_iff_of_toVal hx).mpr ⟨k, ?_⟩
    rw [hxv, hk]
    push_cast
    ring

theorem exists_toVal_of_polygammaSpecial {n : ℕ} {x : AzFloat}
    (hc : polygammaSpecial n x = true) : ∃ xv : ℝ, x.toVal = some (xv : EReal) := by
  unfold polygammaSpecial at hc
  simp only [Bool.and_eq_true] at hc
  exact exists_toVal_of_isFinite hc.1.1.2

/-- **`ψ⁽ⁿ⁾(x)` is irrational at the arguments recognized by `polygammaSpecial`.** -/
theorem irrational_polygamma_of_special {n : ℕ} {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hc : polygammaSpecial n x = true) :
    Irrational (polygammaR n xv) := by
  obtain ⟨hn, -, N, hxv, hN⟩ := polygammaSpecial_spec hx hc
  rw [hxv]
  exact irrational_polygammaR_div_two (Nat.odd_iff.mpr hn) hN

/-- **The Ziv certificate of `ψ⁽ⁿ⁾(x)` at the arguments recognized by `polygammaSpecial`**:
some level `w₀ 2^f` is accepted. -/
theorem polygammaApprox_cert {n : ℕ} {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hc : polygammaSpecial n (finite s e q m hv) = true) (p : ℕ)
    [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (lnAbsGammaApproxOf (polygammaEnclFor n (finite s e q m hv) s p (w₀ * 2 ^ f))
        (w₀ * 2 ^ f)).1
      (lnAbsGammaApproxOf (polygammaEnclFor n (finite s e q m hv) s p (w₀ * 2 ^ f))
        (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hx := toVal_finite s e q m hv
  obtain ⟨hn, hsign, -⟩ := polygammaSpecial_spec hx hc
  have hirr := irrational_polygamma_of_special hx hc
  have hconv := polygammaApprox_bracketConv (n := n) (by omega) hx (pos := s)
    (fun hs => by subst hs; exact finiteVal_true_pos e hv)
    (fun hs => by
      subst hs
      have hneg := finiteVal_false_neg e hv
      refine ⟨hneg, fun k hk => ?_⟩
      rcases hsign with h | h
      · linarith
      · exact h ((isInteger_finite false e hv).mpr ⟨k, hk⟩)) p
  exact hconv.exists_isSome hirr.ne_zero p (not_mem_floatSet_of_irrational p hirr) mode w₀ hw₀

end Azurite.AzFloat
