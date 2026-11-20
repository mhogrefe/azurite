/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaRatBracket
import Azurite.AzFloat.Equiv.BetaCertificate
import Azurite.AzFloat.Equiv.GammaRatBracket
import Azurite.AzFloat.Equiv.PowRat
import Azurite.AzFloat.Equiv.RatPowRat
import Azurite.AzRat.Equiv.Add

/-!
# The Beta function of two rationals: convergence and the Ziv certificate

* `argConv_rat`: a rational argument converges (`ArgConv`), so the bracket of `B(a, b)`
  converges (`betaRatApprox_bracketConv`).
* `irrational_beta_of_ratSpecial`, `betaRatApprox_cert`: at the arguments recognized by
  `betaRatSpecial`, off the zeros of `B`, the value is irrational and Ziv's loop terminates.
-/

namespace Azurite.AzFloat

open Filter Topology

/-- The roundings of a rational enclose it. -/
theorem lnGammaRatEncl_isEncl (q : AzRat) (w : ℕ) :
    IsEncl (lnGammaRatEncl q w) ((AzRat.toRat q : ℚ) : ℝ) := by
  have : NeZero (w + 32) := ⟨by omega⟩
  obtain ⟨l, hl, hl1, -⟩ := ofAzRatRound_floor_abs q (w + 32)
  obtain ⟨h, hh, hh1, -⟩ := ofAzRatRound_ceiling_abs q (w + 32)
  exact ⟨l, h, hl, hh, hl1, hh1⟩

/-- `gammaRatFrac` answers with the sign of `q − k` and a positive enclosure of `|q − k|`. -/
theorem gammaRatFrac_spec (q : AzRat) {W : ℕ} {σ : Bool} {k : AzInt} {A : Encl}
    (h : gammaRatFrac q W = some (σ, k, A)) :
    IsEnclPos A ((if σ then -1 else 1) * (((AzRat.toRat q : ℚ) : ℝ) - k.toInt)) := by
  unfold gammaRatFrac at h
  dsimp only at h
  generalize (q.round .Nearest).1 = k' at h
  have hdv : ((AzRat.toRat (q - k'.toAzRat) : ℚ) : ℝ)
      = ((AzRat.toRat q : ℚ) : ℝ) - k'.toInt := by
    rw [AzRat.toRat_sub, AzRat.toRat_toAzRat_int]
    push_cast
    rfl
  split_ifs at h with h0 hs
  · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have := lnGammaRatEncl_spec _ ((toRat_sign_iff _ h0).mp hs) W
    rw [hdv] at this
    simpa [hs] using this
  · have hs' : (q - k'.toAzRat).sign = false := by simpa using hs
    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hneg := toRat_neg_of_sign_false _ h0 hs'
    have hv : ((AzRat.toRat (-(q - k'.toAzRat)) : ℚ) : ℝ)
        = -(((AzRat.toRat q : ℚ) : ℝ) - k'.toInt) := by
      rw [AzRat.toRat_neg, Rat.cast_neg, hdv]
    have := lnGammaRatEncl_spec (-(q - k'.toAzRat)) (by rw [hv]; rw [hdv] at hneg; linarith) W
    rw [hv] at this
    simpa [hs'] using this

/-- A rational is a non-positive integer exactly when its denominator is `1` and it is `0` or
negative. -/
theorem nonpos_int_iff (s : AzRat) :
    (s.den = 1 ∧ (s.num = 0 ∨ s.sign = false)) ↔
      ((AzRat.toRat s : ℚ) : ℝ) ≤ 0 ∧ ∃ k : ℤ, ((AzRat.toRat s : ℚ) : ℝ) = k := by
  constructor
  · rintro ⟨hd, h⟩
    refine ⟨?_, _, coe_toRat_eq_mkNorm_of_den_one s hd⟩
    rcases h with h0 | hs
    · rw [coe_toRat_eq_zero_of_num_eq_zero s h0]
    · by_cases h0 : s.num = 0
      · rw [coe_toRat_eq_zero_of_num_eq_zero s h0]
      · exact (toRat_neg_of_sign_false s h0 hs).le
  · rintro ⟨hle, hk⟩
    have hd : s.den = 1 := by
      by_contra hd
      exact not_exists_int_of_den_ne_one s hd hk
    refine ⟨hd, ?_⟩
    by_cases h0 : s.num = 0
    · exact Or.inl h0
    · right
      by_contra hs
      have := (toRat_sign_iff s h0).mp (by simpa using hs)
      linarith

/-- A rational argument converges where `Γ` is finite and nonzero. -/
theorem argConv_rat (q : AzRat)
    (h : 0 < ((AzRat.toRat q : ℚ) : ℝ) ∨
      (((AzRat.toRat q : ℚ) : ℝ) < 0 ∧ ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k)) :
    ArgConv (lnGammaRatEncl q) (gammaRatFrac q) ((AzRat.toRat q : ℚ) : ℝ) := by
  refine ⟨⟨4 * |((AzRat.toRat q : ℚ) : ℝ)|, fun V _ => ?_⟩, ?_⟩
  · have : NeZero (V + 32) := ⟨by omega⟩
    obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs q (V + 32)
    obtain ⟨u, hu, hu1, hu2⟩ := ofAzRatRound_ceiling_abs q (V + 32)
    refine ⟨l, u, hl, hu, hl1, hu1, ?_⟩
    have hpow : (1 / 2 : ℝ) ^ (V + 32) ≤ (1 / 2 : ℝ) ^ V :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ _)
    have := mul_le_mul_of_nonneg_left hpow (abs_nonneg ((AzRat.toRat q : ℚ) : ℝ))
    linarith
  · rcases h with h | ⟨h, hint⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      have e : (fun ws => (gammaRatFrac q (ws + 16)).bind
          fun t => gammaSinOfFrac t.1 t.2.1 t.2.2 (ws + 16) ws)
          = fun w => gammaRatSinEncl q (w + 16) w := by
        funext w
        unfold gammaRatFrac gammaRatSinEncl
        dsimp only
        split_ifs <;> rfl
      rw [e]
      exact gammaRatSinEncl_conv q hint

/-- **The core of `B(a, b)` converges** for rationals where none of `a`, `b`, `a + b` is `0`
or a negative integer. -/
theorem betaRatCore_coreConv (a b : AzRat)
    (hA : 0 < ((AzRat.toRat a : ℚ) : ℝ) ∨
      (((AzRat.toRat a : ℚ) : ℝ) < 0 ∧ ∀ k : ℤ, ((AzRat.toRat a : ℚ) : ℝ) ≠ k))
    (hB : 0 < ((AzRat.toRat b : ℚ) : ℝ) ∨
      (((AzRat.toRat b : ℚ) : ℝ) < 0 ∧ ∀ k : ℤ, ((AzRat.toRat b : ℚ) : ℝ) ≠ k))
    (hS : 0 < ((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) ∨
      (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) < 0 ∧
        ∀ k : ℤ, ((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) ≠ k)) :
    CoreConv (betaEnclOf (lnGammaRatEncl a) (lnGammaRatEncl b) (lnGammaRatEncl (a + b))
        (gammaRatExp a) (gammaRatExp b) (gammaRatExp (a + b)) (gammaRatFrac a) (gammaRatFrac b)
        (gammaRatFrac (a + b)))
      (Real.Gamma ((AzRat.toRat a : ℚ) : ℝ) * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
        / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ))) := by
  have hsum : ((AzRat.toRat (a + b) : ℚ) : ℝ)
      = ((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) := by
    rw [AzRat.toRat_add]; push_cast; rfl
  rw [← hsum] at hS ⊢
  exact betaEnclOf_coreConv (argConv_rat a hA) (argConv_rat b hB) (argConv_rat (a + b) hS)
    (fun W σ k E _ hF => gammaRatFrac_spec a hF) (fun W σ k E _ hF => gammaRatFrac_spec b hF)
    (fun W σ k E _ hF => gammaRatFrac_spec (a + b) hF)

/-- **The bracket of `B(a, b)` converges** for rationals. -/
theorem betaRatApprox_bracketConv (a b : AzRat)
    (hA : 0 < ((AzRat.toRat a : ℚ) : ℝ) ∨
      (((AzRat.toRat a : ℚ) : ℝ) < 0 ∧ ∀ k : ℤ, ((AzRat.toRat a : ℚ) : ℝ) ≠ k))
    (hB : 0 < ((AzRat.toRat b : ℚ) : ℝ) ∨
      (((AzRat.toRat b : ℚ) : ℝ) < 0 ∧ ∀ k : ℤ, ((AzRat.toRat b : ℚ) : ℝ) ≠ k))
    (hS : 0 < ((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) ∨
      (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) < 0 ∧
        ∀ k : ℤ, ((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) ≠ k)) :
    BracketConv (betaRatApprox a b (a + b))
      (Real.Gamma ((AzRat.toRat a : ℚ) : ℝ) * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
        / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ))) :=
  gammaApproxOf_bracketConv (betaRatCore_coreConv a b hA hB hS)

theorem den_toRat_ne_one {q : AzRat} (h : q.den ≠ 1) : (AzRat.toRat q).den ≠ 1 := by
  have hden : (AzRat.toRat q).den = q.den.toNat := rfl
  rw [hden]
  intro h1
  exact h (AzNat.toNat_injective (by rw [h1, AzNat.toNat_one]))

/-- What `betaRatSpecial` says. -/
theorem betaRatSpecial_spec {a b s : AzRat} (hc : betaRatSpecial a b s = true) :
    a.den ≠ 1 ∧ b.den ≠ 1 ∧
      (s.den = 1 ∨ ((AzRat.toRat a).den ∣ 4 ∧ (AzRat.toRat b).den ∣ 4)
        ∨ ((AzRat.toRat a).den ∣ 6 ∧ (AzRat.toRat b).den ∣ 6)) := by
  have hden : ∀ q : AzRat, (AzRat.toRat q).den = q.den.toNat := fun _ => rfl
  have h4 : ∀ q : AzRat, q.den = AzNat.ofNat 2 ∨ q.den = AzNat.ofNat 4 →
      (AzRat.toRat q).den ∣ 4 := by
    intro q h
    rw [hden]
    rcases h with h | h
    · rw [h, AzNat.toNat_ofNat]
      norm_num
    · rw [h, AzNat.toNat_ofNat]
  have h6 : ∀ q : AzRat,
      (q.den = AzNat.ofNat 2 ∨ q.den = AzNat.ofNat 3) ∨ q.den = AzNat.ofNat 6 →
      (AzRat.toRat q).den ∣ 6 := by
    intro q h
    rw [hden]
    rcases h with (h | h) | h <;> rw [h, AzNat.toNat_ofNat] <;> norm_num
  unfold betaRatSpecial at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hda, hdb⟩, hcase⟩ := hc
  refine ⟨hda, hdb, ?_⟩
  rcases hcase with (h | ⟨ha, hb⟩) | ⟨ha, hb⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h4 a ha, h4 b hb⟩)
  · exact Or.inr (Or.inr ⟨h6 a ha, h6 b hb⟩)

/-- **`B(a, b)` is irrational at the rationals recognized by `betaRatSpecial`**, off its
zeros. -/
theorem irrational_beta_of_ratSpecial {a b : AzRat} (hc : betaRatSpecial a b (a + b) = true)
    (hs : ¬ ((a + b).den = 1 ∧ ((a + b).num = 0 ∨ (a + b).sign = false))) :
    Irrational (Real.Gamma ((AzRat.toRat a : ℚ) : ℝ) * Real.Gamma ((AzRat.toRat b : ℚ) : ℝ)
      / Real.Gamma (((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ))) := by
  obtain ⟨hda, hdb, hcase⟩ := betaRatSpecial_spec hc
  have hsumq : AzRat.toRat (a + b) = AzRat.toRat a + AzRat.toRat b := AzRat.toRat_add a b
  have hsden : (AzRat.toRat a + AzRat.toRat b).den = (a + b).den.toNat := by
    rw [← hsumq]
    rfl
  rw [nonpos_int_iff] at hs
  by_cases h1 : (a + b).den = 1
  · refine Azurite.Chudnovsky.irrational_beta_of_den (den_toRat_ne_one hda)
      (den_toRat_ne_one hdb) (Or.inl ⟨by rw [hsden, h1, AzNat.toNat_one], ?_⟩)
    by_contra hle
    push Not at hle
    refine hs ⟨?_, _, coe_toRat_eq_mkNorm_of_den_one (a + b) h1⟩
    rw [hsumq]
    exact_mod_cast hle
  · have hne : (AzRat.toRat a + AzRat.toRat b).den ≠ 1 := by
      rw [← hsumq]
      exact den_toRat_ne_one h1
    rcases hcase with h | h | h
    · exact absurd h h1
    · exact Azurite.Chudnovsky.irrational_beta_of_den (den_toRat_ne_one hda)
        (den_toRat_ne_one hdb) (Or.inr ⟨hne, Or.inl h⟩)
    · exact Azurite.Chudnovsky.irrational_beta_of_den (den_toRat_ne_one hda)
        (den_toRat_ne_one hdb) (Or.inr ⟨hne, Or.inr h⟩)

/-- A rational with a denominator other than `1` is positive, or negative and not an
integer. -/
theorem rat_arg_cases {q : AzRat} (hd : q.den ≠ 1) :
    0 < ((AzRat.toRat q : ℚ) : ℝ) ∨
      (((AzRat.toRat q : ℚ) : ℝ) < 0 ∧ ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k) := by
  have hni := not_exists_int_of_den_ne_one q hd
  exact beta_arg_cases (fun h0 => hni ⟨0, by simpa using h0⟩) (fun h => hni h.2)

/-- **The Ziv certificate of `B(a, b)` at the rationals recognized by `betaRatSpecial`**, off
the zeros of `B`: some level `w₀ 2^f` is accepted. -/
theorem betaRatApprox_cert {a b : AzRat} (hc : betaRatSpecial a b (a + b) = true)
    (hs : ¬ ((a + b).den = 1 ∧ ((a + b).num = 0 ∨ (a + b).sign = false))) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (betaRatApprox a b (a + b) (w₀ * 2 ^ f)).1
      (betaRatApprox a b (a + b) (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  obtain ⟨hda, hdb, -⟩ := betaRatSpecial_spec hc
  have hirr := irrational_beta_of_ratSpecial hc hs
  have hsum : ((AzRat.toRat (a + b) : ℚ) : ℝ)
      = ((AzRat.toRat a : ℚ) : ℝ) + ((AzRat.toRat b : ℚ) : ℝ) := by
    rw [AzRat.toRat_add]; push_cast; rfl
  have hS := beta_sum_cases (fun h => hs ((nonpos_int_iff (a + b)).mpr (by rw [hsum]; exact h)))
  exact gammaApproxOf_isSome_exists
    (betaRatCore_coreConv a b (rat_arg_cases hda) (rat_arg_cases hdb) hS) hirr p mode w₀ hw₀

end Azurite.AzFloat
