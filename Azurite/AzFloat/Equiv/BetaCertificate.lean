/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.BetaWidth
import Azurite.AzFloat.Equiv.GammaCertificate
import Azurite.AzFloat.Equiv.RoundToInteger
import Azurite.AzFloat.Equiv.Ln2Bracket
import Azurite.Chudnovsky.BetaValues

/-!
# The Ziv certificate of the Beta function at arguments with irrational values

* `sumIsNonposInt_iff`, `sumIsPosInt_iff`: the exact decisions whether `a + b` is a
  non-positive, or a positive, integer.
* `irrational_beta_of_special`: `B(a, b)` is irrational at the arguments recognized by
  `betaSpecial` that are not zeros of `B`.
* `betaApprox_cert`: there Ziv's loop terminates — the certificate of the loop without fuel.
-/

namespace Azurite.AzFloat

/-- A float that is not an integer is a finite one, below `2` to its precision. -/
theorem abs_lt_of_not_isInteger {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hni : ¬ isInteger x = true) : |xv| < (2 : ℝ) ^ (x.precision?.getD 1) := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero => exact absurd rfl hni
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    rw [← hx]
    have hqe : e.toInt < q := by
      by_contra hcon
      push Not at hcon
      apply hni
      simp only [isInteger, Bool.or_eq_true, decide_eq_true_eq, AzInt.le_iff_toInt_le,
        toInt_toAzInt, AzNat.toNat_ofNat]
      exact Or.inl hcon
    have hb := (abs_finiteVal_bounds s e hv).2
    show |finiteVal s e m| < (2 : ℝ) ^ q
    refine lt_of_lt_of_le hb ?_
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ (by norm_num) hqe.le

/-- **`sumIsNonposInt` decides whether `a + b` is a non-positive integer.** -/
theorem sumIsNonposInt_iff {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) :
    sumIsNonposInt a b = true ↔ av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k := by
  unfold sumIsNonposInt
  have hnb : (-b).toVal = some ((-bv : ℝ) : EReal) := by
    rw [toVal_neg, hb, Option.map_some, EReal.coe_neg]
  by_cases hia : isInteger a = true
  · rw [ite_eq_left hia, Bool.and_eq_true, isInteger_iff_of_toVal hb, le_eq_true_iff ha hnb]
    obtain ⟨na, hna⟩ := (isInteger_iff_of_toVal ha).mp hia
    constructor
    · rintro ⟨⟨nb, hnb'⟩, hle⟩
      exact ⟨by linarith, na + nb, by rw [hna, hnb']; push_cast; ring⟩
    · rintro ⟨hle, k, hk⟩
      exact ⟨⟨k - na, by push_cast; linarith⟩, by linarith⟩
  · rw [ite_eq_right hia]
    by_cases hib : isInteger b = true
    · rw [ite_eq_left hib]
      obtain ⟨nb, hnb'⟩ := (isInteger_iff_of_toVal hb).mp hib
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨-, k, hk⟩
        exact absurd ((isInteger_iff_of_toVal ha).mpr ⟨k - nb, by push_cast; linarith⟩) hia
    · rw [ite_eq_right hib]
      dsimp only
      set P := a.precision?.getD 1 + b.precision?.getD 1 + 2 with hP
      have : NeZero P := ⟨by omega⟩
      have hr : addPrecRound a b P .Nearest
          = roundVal P .Nearest (some ((av + bv : ℝ) : EReal)) := by
        rw [addPrecRound_eq_liftVal₂, liftVal₂, ha, hb, Option.bind_some, Option.bind_some,
          Spec.add_coe_coe]
      rw [hr]
      obtain ⟨h1, h2⟩ := roundVal_coe P .Nearest (av + bv)
      constructor
      · intro h
        split_ifs at h with heq
        rw [Bool.and_eq_true] at h
        rw [h2, compare_eq_iff_eq] at heq
        rw [heq] at h1
        exact ⟨(le_eq_true_iff h1 toVal_zero').mp h.2, (isInteger_iff_of_toVal h1).mp h.1⟩
      · rintro ⟨hle, k, hk⟩
        have hba := abs_lt_of_not_isInteger ha hia
        have hbb := abs_lt_of_not_isInteger hb hib
        have hkabs : |k| ≤ 2 ^ P := by
          have h3 : |(k : ℝ)| < (2 : ℝ) ^ P := by
            rw [← hk]
            have hpa : (2 : ℝ) ^ (a.precision?.getD 1) ≤ 2 ^ (P - 1) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            have hpb : (2 : ℝ) ^ (b.precision?.getD 1) ≤ 2 ^ (P - 1) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            have hPP : (2 : ℝ) ^ P = 2 * 2 ^ (P - 1) := by
              rw [← pow_succ', show P - 1 + 1 = P by omega]
            calc |av + bv| ≤ |av| + |bv| := abs_add_le _ _
              _ < 2 ^ P := by linarith
          have h4 : ((|k| : ℤ) : ℝ) < ((2 ^ P : ℤ) : ℝ) := by push_cast; exact h3
          exact (Int.cast_lt.mp h4).le
        have hmem := mem_floatSet_mul_zpow P k 0 hkabs
        rw [zpow_zero, mul_one, ← hk] at hmem
        obtain ⟨m1, m2⟩ := roundVal_of_mem P .Nearest (av + bv) hmem
        rw [ite_eq_left m2, Bool.and_eq_true]
        exact ⟨(isInteger_iff_of_toVal m1).mpr ⟨k, hk⟩, (le_eq_true_iff m1 toVal_zero').mpr hle⟩

/-- **`sumIsPosInt` decides whether `a + b` is a positive integer**, for `a`, `b` that are
not integers. -/
theorem sumIsPosInt_iff {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (hia : ¬ isInteger a = true)
    (hib : ¬ isInteger b = true) :
    sumIsPosInt a b = true ↔ 0 < av + bv ∧ ∃ k : ℤ, av + bv = k := by
  unfold sumIsPosInt
  dsimp only
  set P := a.precision?.getD 1 + b.precision?.getD 1 + 2 with hP
  have : NeZero P := ⟨by omega⟩
  have hr : addPrecRound a b P .Nearest
      = roundVal P .Nearest (some ((av + bv : ℝ) : EReal)) := by
    rw [addPrecRound_eq_liftVal₂, liftVal₂, ha, hb, Option.bind_some, Option.bind_some,
      Spec.add_coe_coe]
  rw [hr]
  obtain ⟨h1, h2⟩ := roundVal_coe P .Nearest (av + bv)
  constructor
  · intro h
    split_ifs at h with heq
    rw [Bool.and_eq_true] at h
    rw [h2, compare_eq_iff_eq] at heq
    rw [heq] at h1
    exact ⟨(lt_eq_true_iff toVal_zero' h1).mp h.2, (isInteger_iff_of_toVal h1).mp h.1⟩
  · rintro ⟨hpos, k, hk⟩
    have hba := abs_lt_of_not_isInteger ha hia
    have hbb := abs_lt_of_not_isInteger hb hib
    have hkabs : |k| ≤ 2 ^ P := by
      have h3 : |(k : ℝ)| < (2 : ℝ) ^ P := by
        rw [← hk]
        have hpa : (2 : ℝ) ^ (a.precision?.getD 1) ≤ 2 ^ (P - 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hpb : (2 : ℝ) ^ (b.precision?.getD 1) ≤ 2 ^ (P - 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hPP : (2 : ℝ) ^ P = 2 * 2 ^ (P - 1) := by
          rw [← pow_succ', show P - 1 + 1 = P by omega]
        calc |av + bv| ≤ |av| + |bv| := abs_add_le _ _
          _ < 2 ^ P := by linarith
      have h4 : ((|k| : ℤ) : ℝ) < ((2 ^ P : ℤ) : ℝ) := by push_cast; exact h3
      exact (Int.cast_lt.mp h4).le
    have hmem := mem_floatSet_mul_zpow P k 0 hkabs
    rw [zpow_zero, mul_one, ← hk] at hmem
    obtain ⟨m1, m2⟩ := roundVal_of_mem P .Nearest (av + bv) hmem
    rw [ite_eq_left m2, Bool.and_eq_true]
    exact ⟨(isInteger_iff_of_toVal m1).mpr ⟨k, hk⟩, (lt_eq_true_iff toVal_zero' m1).mpr hpos⟩

theorem exists_toVal_of_isFinite {x : AzFloat} (h : x.isFinite = true) :
    ∃ xv : ℝ, x.toVal = some (xv : EReal) := by
  cases x with
  | nan => exact absurd h (by decide)
  | infinity s => exact absurd h (by simp [isFinite])
  | zero => exact ⟨0, toVal_zero'⟩
  | finite s e q m hv => exact ⟨_, toVal_finite s e q m hv⟩

/-- What `betaSpecial` says. -/
theorem betaSpecial_spec {a b : AzFloat} (hc : betaSpecial a b = true) :
    ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧ b.toVal = some (bv : EReal) ∧
      ¬ isInteger a = true ∧ ¬ isInteger b = true ∧
      (sumIsPosInt a b = true ∨ (gammaSpecial a = true ∧ gammaSpecial b = true)) := by
  unfold betaSpecial at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨hfa, hfb⟩, hia⟩, hib⟩, hcase⟩ := hc
  obtain ⟨av, ha⟩ := exists_toVal_of_isFinite hfa
  obtain ⟨bv, hb⟩ := exists_toVal_of_isFinite hfb
  exact ⟨av, bv, ha, hb, by simp [hia], by simp [hib], hcase⟩

/-- A float that is not an integer is a rational with a denominator other than `1`. -/
theorem exists_rat_den_ne_one {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hni : ¬ isInteger x = true) : ∃ q : ℚ, xv = q ∧ q.den ≠ 1 := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  refine ⟨q, hq, fun h1 => hni ((isInteger_iff_of_toVal hx).mpr ⟨q.num, ?_⟩)⟩
  rw [hq]
  have := Rat.coe_int_num_of_den_eq_one h1
  exact_mod_cast this.symm

/-- **`B(a, b)` is irrational at the arguments recognized by `betaSpecial`**, off its
zeros. -/
theorem irrational_beta_of_special {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal)) (hb : b.toVal = some (bv : EReal))
    (hc : betaSpecial a b = true) (hs : ¬ sumIsNonposInt a b = true) :
    Irrational (Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)) := by
  obtain ⟨av', bv', ha', hb', hia, hib, hcase⟩ := betaSpecial_spec hc
  rw [ha, Option.some.injEq, EReal.coe_eq_coe_iff] at ha'
  rw [hb, Option.some.injEq, EReal.coe_eq_coe_iff] at hb'
  subst ha' hb'
  obtain ⟨qa, hqa, hda⟩ := exists_rat_den_ne_one ha hia
  obtain ⟨qb, hqb, hdb⟩ := exists_rat_den_ne_one hb hib
  rw [sumIsNonposInt_iff ha hb] at hs
  rw [hqa, hqb] at hs ⊢
  have hsumint : (qa + qb).den = 1 → 0 < qa + qb := by
    intro h1
    by_contra hle
    push Not at hle
    refine hs ⟨by exact_mod_cast hle, (qa + qb).num, ?_⟩
    have := Rat.coe_int_num_of_den_eq_one h1
    have h2 : ((qa + qb : ℚ) : ℝ) = (((qa + qb).num : ℤ) : ℝ) := by exact_mod_cast this.symm
    rw [← h2]
    push_cast
    rfl
  rcases hcase with hpos | ⟨hga, hgb⟩
  · obtain ⟨hp, k, hk⟩ := (sumIsPosInt_iff ha hb hia hib).mp hpos
    rw [hqa, hqb] at hp hk
    have hq : qa + qb = (k : ℚ) := by exact_mod_cast hk
    refine Azurite.Chudnovsky.irrational_beta_of_den hda hdb (Or.inl ⟨?_, by exact_mod_cast hp⟩)
    rw [hq]
    exact Rat.den_intCast k
  · obtain ⟨ra, hra, hrda⟩ := gammaSpecial_spec ha hga
    obtain ⟨rb, hrb, hrdb⟩ := gammaSpecial_spec hb hgb
    have ea : ra = qa := by exact_mod_cast hra.trans hqa
    have eb : rb = qb := by exact_mod_cast hrb.trans hqb
    subst ea eb
    have d4a : ra.den ∣ 4 := by
      rcases hrda with h | h
      · rw [h]; norm_num
      · rw [h]
    have d4b : rb.den ∣ 4 := by
      rcases hrdb with h | h
      · rw [h]; norm_num
      · rw [h]
    by_cases h1 : (ra + rb).den = 1
    · exact Azurite.Chudnovsky.irrational_beta_of_den hda hdb (Or.inl ⟨h1, hsumint h1⟩)
    · exact Azurite.Chudnovsky.irrational_beta_of_den hda hdb
        (Or.inr ⟨h1, Or.inl ⟨d4a, d4b⟩⟩)

/-- The conditions of `betaApprox_bracketConv` off the special values. -/
theorem beta_arg_cases {av : ℝ} (h0 : av ≠ 0) (hnp : ¬ (av < 0 ∧ ∃ k : ℤ, av = k)) :
    0 < av ∨ (av < 0 ∧ ∀ k : ℤ, av ≠ k) := by
  rcases lt_trichotomy av 0 with h | h | h
  · exact Or.inr ⟨h, fun k hk => hnp ⟨h, k, hk⟩⟩
  · exact absurd h h0
  · exact Or.inl h

theorem beta_sum_cases {sv : ℝ} (hs : ¬ (sv ≤ 0 ∧ ∃ k : ℤ, sv = k)) :
    0 < sv ∨ (sv < 0 ∧ ∀ k : ℤ, sv ≠ k) := by
  rcases lt_or_ge 0 sv with h | h
  · exact Or.inl h
  · refine Or.inr ⟨lt_of_le_of_ne h fun h0 => hs ⟨h, 0, by simpa using h0⟩,
      fun k hk => hs ⟨h, k, hk⟩⟩

/-- **The Ziv certificate of `B(a, b)` at the arguments recognized by `betaSpecial`**, off the
zeros of `B`: some level `w₀ 2^f` is accepted. -/
theorem betaApprox_cert {a b : AzFloat} (hc : betaSpecial a b = true)
    (hs : ¬ sumIsNonposInt a b = true) (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (betaApprox a b (w₀ * 2 ^ f)).1
      (betaApprox a b (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  obtain ⟨av, bv, ha, hb, hia, hib, -⟩ := betaSpecial_spec hc
  have hirr := irrational_beta_of_special ha hb hc hs
  have hA : 0 < av ∨ (av < 0 ∧ ∀ k : ℤ, av ≠ k) :=
    beta_arg_cases (fun h0 => hia ((isInteger_iff_of_toVal ha).mpr ⟨0, by simpa using h0⟩))
      (fun h => hia ((isInteger_iff_of_toVal ha).mpr h.2))
  have hB : 0 < bv ∨ (bv < 0 ∧ ∀ k : ℤ, bv ≠ k) :=
    beta_arg_cases (fun h0 => hib ((isInteger_iff_of_toVal hb).mpr ⟨0, by simpa using h0⟩))
      (fun h => hib ((isInteger_iff_of_toVal hb).mpr h.2))
  have hS := beta_sum_cases (fun h => hs ((sumIsNonposInt_iff ha hb).mpr h))
  exact gammaApproxOf_isSome_exists (betaCore_coreConv ha hb hA hB hS) hirr p mode w₀ hw₀

end Azurite.AzFloat
