/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AddSubRat
import Azurite.AzFloat.Equiv.Mul
import Azurite.AzFloat.MulRat
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.TrailingZeros
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Multiplication of an `AzFloat` by an `AzRat` is a lift

`mulRatPrecRound_eq_liftVal`: `mulRatPrecRound x q p mode = liftVal (fun a => Spec.mul a q) x
p mode`, where `q` stands for the value of the rational.  The exact path is checked by
`mulRatExact_eq` (the product is `± (m / oddDen q) · num · 2^(e − |m| − t)` when the odd part
of the denominator divides the significand).  For the loop, `mulRatApprox_spec` gives the two
ends as the rounding procedures of `x · lo` and `x · (lo + ε)` in increasing order, and the
termination theorem `mulRatApprox_possible` applies when the odd part does not divide the
significand: then the product is not dyadic (`oddDen_dvd_of_mem_floatSet`), hence not a
boundary, and it is at distance at least `1/(den · 2^a)` from the adjacent boundaries
(`dist_prod_boundary`), while the bracket has width `|x| · ε ≤ 2^(e + |num| + 1 − w)`.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### Values and the odd part of the denominator -/

/-- The sign of a nonzero rational is the sign of its value. -/
theorem sign_eq_decide_pos (q : AzRat) (hq : q.num ≠ 0) :
    q.sign = decide (0 < (AzRat.toRat q : ℝ)) := by
  have hnum : (0 : ℝ) < q.num.toNat := by exact_mod_cast AzRat.num_toNat_pos q hq
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  rw [coe_toRat_eq]
  cases hs : q.sign
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
    rw [eq_comm, decide_eq_false_iff_not, not_lt]
    exact (div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden).le
  · simp only [↓reduceIte, Int.cast_natCast]
    rw [eq_comm, decide_eq_true_iff]
    exact div_pos hnum hden

/-- The denominator is its odd part times a power of two. -/
theorem den_eq_oddDen_mul (q : AzRat) :
    q.den.toNat = (oddDen q).toNat * 2 ^ denTrailingZeros q := by
  have hden := q.den_nz
  unfold oddDen denTrailingZeros
  rw [AzNat.trailingZeros_eq_padicValNat q.den hden, Option.getD_some]
  rw [show q.den >>> padicValNat 2 q.den.toNat
    = AzNat.shiftRight q.den (padicValNat 2 q.den.toNat) from rfl, AzNat.toNat_shiftRight]
  have := Nat.ordProj_mul_ordCompl_eq_self q.den.toNat 2
  rw [Nat.factorization_def _ Nat.prime_two] at this
  rw [mul_comm]
  exact this.symm

/-- The odd part of the denominator is odd. -/
theorem coprime_two_oddDen (q : AzRat) : Nat.Coprime 2 (oddDen q).toNat := by
  have hden : q.den.toNat ≠ 0 := (AzRat.den_toNat_pos q).ne'
  have h := Nat.coprime_ordCompl Nat.prime_two hden
  rw [Nat.factorization_def _ Nat.prime_two] at h
  have hod : (oddDen q).toNat = q.den.toNat / 2 ^ padicValNat 2 q.den.toNat := by
    unfold oddDen denTrailingZeros
    rw [AzNat.trailingZeros_eq_padicValNat q.den q.den_nz, Option.getD_some]
    rw [show q.den >>> padicValNat 2 q.den.toNat
      = AzNat.shiftRight q.den (padicValNat 2 q.den.toNat) from rfl, AzNat.toNat_shiftRight]
  rw [hod]
  exact h

theorem oddDen_pos (q : AzRat) : 0 < (oddDen q).toNat := by
  have := AzRat.den_toNat_pos q
  rw [den_eq_oddDen_mul q] at this
  exact Nat.pos_of_mul_pos_right this

/-- The odd part of the denominator is coprime to the numerator. -/
theorem coprime_num_oddDen (q : AzRat) : Nat.Coprime q.num.toNat (oddDen q).toNat :=
  Nat.Coprime.coprime_dvd_right (Dvd.intro _ (den_eq_oddDen_mul q).symm)
    ((AzNat.coprime_iff _ _).mp q.reduced)

/-! ### The exact product -/

/-- The product of a finite float and a rational whose denominator's odd part divides the
significand, built exactly. -/
theorem mulRatExact_eq (s : Bool) (e : AzInt) (p' : ℕ) (m : AzNat) (hv : FiniteValid p' m)
    (q : AzRat) (hq : q.num ≠ 0) (hdvd : (m.divMod (oddDen q)).2 = 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    mulRatExact s e m (m.divMod (oddDen q)).1 q p mode
      = roundVal p mode (some ((finiteVal s e m * AzRat.toRat q : ℝ) : EReal)) := by
  have hm0 : m.toNat ≠ 0 := by
    intro h
    exact ne_zero_of_size_pos (by rw [hv.size_eq]; exact lt_of_lt_of_le hv.pos (le_alignedBits p'))
      (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hod0 : (oddDen q).toNat ≠ 0 := (oddDen_pos q).ne'
  have hqr := (AzNat.divMod_toNat m (oddDen q)).1
  have hr0 : (m.divMod (oddDen q)).2.toNat = 0 := by rw [hdvd]; rfl
  rw [hr0, add_zero] at hqr
  have hdvd' : (oddDen q).toNat ∣ m.toNat := Dvd.intro_left _ hqr
  have hquot : (m.divMod (oddDen q)).1.toNat = m.toNat / (oddDen q).toNat := by
    rw [← hqr, Nat.mul_div_cancel _ (oddDen_pos q)]
  have hnum0 : q.num.toNat ≠ 0 := (AzRat.num_toNat_pos q hq).ne'
  set c := (m.divMod (oddDen q)).1 * q.num with hcdef
  have hc : c.toNat = m.toNat / (oddDen q).toNat * q.num.toNat := by
    rw [hcdef, AzNat.toNat_mul, hquot]
  have hc0 : c ≠ 0 := by
    intro h
    have := congrArg AzNat.toNat h
    rw [hc, AzNat.toNat_zero] at this
    rcases Nat.mul_eq_zero.mp this with h1 | h1
    · exact absurd (Nat.eq_zero_of_dvd_of_div_eq_zero hdvd' h1) hm0
    · exact hnum0 h1
  set t := denTrailingZeros q with ht
  have hexp : (e - (AzNat.ofNat (m.size + t)).toAzInt + (AzNat.ofNat c.size).toAzInt).toInt
      - c.size = e.toInt - m.size - t := by
    rw [AzInt.toInt_add, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat]
    push_cast
    ring
  have hcR : (c.toNat : ℝ) = (m.toNat : ℝ) / (oddDen q).toNat * q.num.toNat := by
    rw [hc, Nat.cast_mul, Nat.cast_div hdvd' (by exact_mod_cast hod0)]
  have hdenR : (q.den.toNat : ℝ) = (oddDen q).toNat * 2 ^ t := by
    exact_mod_cast den_eq_oddDen_mul q
  have hpow : (2 : ℝ) ^ (e.toInt - m.size - t) = 2 ^ (e.toInt - m.size) * (2 ^ t)⁻¹ := by
    rw [show e.toInt - (m.size : ℤ) - t = (e.toInt - m.size) + (-(t : ℤ)) by ring,
      zpow_add₀ (by norm_num), zpow_neg, zpow_natCast]
  have hval : finiteVal (s == q.sign)
      (e - (AzNat.ofNat (m.size + t)).toAzInt + (AzNat.ofNat c.size).toAzInt) c
      = finiteVal s e m * AzRat.toRat q := by
    unfold finiteVal
    rw [hexp, hcR, hpow, coe_toRat_eq, hdenR]
    cases s <;> cases q.sign <;> simp <;> ring
  unfold mulRatExact
  rw [setPrecRound_eq_liftE]
  unfold liftE liftVal
  rw [← ht, ← hcdef, toVal_mkFinite _ _ _ _ hc0, Option.bind_some, hval]
  rfl

/-! ### Dyadic products -/

/-- The distance from `x · q` to `b = M · 2^k`, once `a` dominates the exponents of both `x`
and `b`: at least `1/(den · 2^a)`. -/
theorem dist_prod_boundary (s : Bool) (e : AzInt) (m : AzNat) (q : AzRat) (b : ℝ) (M k : ℤ)
    (hb : b = M * 2 ^ k) (a : ℕ) (ha : (m.size : ℤ) - e.toInt ≤ a) (hk : -k ≤ a)
    (hne : finiteVal s e m * AzRat.toRat q ≠ b) :
    1 / (q.den.toNat * 2 ^ a) ≤ |finiteVal s e m * AzRat.toRat q - b| := by
  generalize hc : (if s then (m.toNat : ℤ) else -(m.toNat : ℤ)) = c
  generalize hσ : (if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) = σ
  obtain ⟨N, hN⟩ :=
    exists_int_mul_sub_dyadic (c * σ) (M * q.den.toNat) (e.toInt - m.size) k a (by omega) hk
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  have hD : (0 : ℝ) < q.den.toNat * 2 ^ a := by positivity
  have h1 : finiteVal s e m = (c : ℝ) * 2 ^ (e.toInt - m.size) := by
    rw [finiteVal_eq_int_mul, hc]
  have h2 : (AzRat.toRat q : ℝ) * q.den.toNat = σ := by
    rw [coe_toRat_eq, hσ]
    exact div_mul_cancel₀ _ hden.ne'
  apply one_div_le_abs_of_mul_eq_int _ _ hD N _ (sub_ne_zero.mpr hne)
  rw [← hN, h1, hb]
  push_cast
  linear_combination ((c : ℝ) * 2 ^ (e.toInt - m.size) * 2 ^ a) * h2

/-- A dyadic product forces the odd part of the denominator to divide the significand. -/
theorem oddDen_dvd_of_mem_floatSet (s : Bool) (e : AzInt) (p' : ℕ) (m : AzNat)
    (hv : FiniteValid p' m) (q : AzRat) (hq : q.num ≠ 0) (p : ℕ) [NeZero p]
    (hB : ((finiteVal s e m * AzRat.toRat q : ℝ) : EReal) ∈ floatSet (p + 1)) :
    (oddDen q).toNat ∣ m.toNat := by
  have hx0 := finiteVal_ne_zero s e hv
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => hq ((AzRat.toRat_eq_zero_iff q).mp h)
  have hv0 : finiteVal s e m * AzRat.toRat q ≠ 0 := mul_ne_zero hx0 hq0
  obtain ⟨M, k, hMk, _⟩ := boundary_repr p _ hB hv0
  generalize hc : (if s then (m.toNat : ℤ) else -(m.toNat : ℤ)) = c
  generalize hσ : (if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) = σ
  have hcabs : c.natAbs = m.toNat := by rw [← hc]; cases s <;> simp
  have hσabs : σ.natAbs = q.num.toNat := by rw [← hσ]; cases q.sign <;> simp
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  set t := denTrailingZeros q with ht
  have hdenR : (q.den.toNat : ℝ) = (oddDen q).toNat * 2 ^ t := by
    exact_mod_cast den_eq_oddDen_mul q
  -- `c σ 2^(e − |m|) = M od 2^(k + t)`
  have hreal : ((c * σ : ℤ) : ℝ) * 2 ^ (e.toInt - m.size)
      = ((M * (oddDen q).toNat : ℤ) : ℝ) * 2 ^ (k + t) := by
    have h1 : finiteVal s e m = (c : ℝ) * 2 ^ (e.toInt - m.size) := by
      rw [finiteVal_eq_int_mul, hc]
    have h2 : (AzRat.toRat q : ℝ) * q.den.toNat = σ := by
      rw [coe_toRat_eq, hσ]
      exact div_mul_cancel₀ _ hden.ne'
    have h3 : finiteVal s e m * AzRat.toRat q * q.den.toNat = M * 2 ^ k * q.den.toNat := by
      rw [hMk]
    rw [mul_assoc, h2, h1, hdenR] at h3
    push_cast
    rw [zpow_add₀ (by norm_num), zpow_natCast]
    linear_combination h3
  set a : ℕ := (max ((m.size : ℤ) - e.toInt) (-(k + t))).toNat with hadef
  have hint := int_eq_of_mul_zpow_eq (c * σ) (M * (oddDen q).toNat) (e.toInt - m.size) (k + t) a
    (by have := Int.self_le_toNat (max ((m.size : ℤ) - e.toInt) (-(k + t))); omega)
    (by have := Int.self_le_toNat (max ((m.size : ℤ) - e.toInt) (-(k + t))); omega) hreal
  have hnat := congrArg Int.natAbs hint
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_mul,
    Int.natAbs_pow, hcabs, hσabs, Int.natAbs_natCast] at hnat
  have h2 : Int.natAbs 2 = 2 := rfl
  rw [h2] at hnat
  have hdvd : (oddDen q).toNat ∣ m.toNat * q.num.toNat * 2 ^ (e.toInt - m.size + a).toNat :=
    ⟨M.natAbs * 2 ^ (k + t + a).toNat, by rw [hnat]; ring⟩
  have hcop2 : Nat.Coprime (oddDen q).toNat (2 ^ (e.toInt - m.size + a).toNat) :=
    Nat.Coprime.pow_right _ (coprime_two_oddDen q).symm
  have hdvd2 : (oddDen q).toNat ∣ m.toNat * q.num.toNat := hcop2.dvd_of_dvd_mul_right hdvd
  exact (coprime_num_oddDen q).symm.dvd_of_dvd_mul_right hdvd2

/-! ### The approximation -/

/-- The bracket of `x · q` at working precision `w`: the two ends round `x · lo` and
`x · (lo + ε)` in increasing order, where `lo ≤ q ≤ lo + ε` with `ε = 0` exactly when the
truncation of `q` was exact. -/
theorem mulRatApprox_spec (s : Bool) (e : AzInt) (p' : ℕ) (m : AzNat) (hv : FiniteValid p' m)
    (q : AzRat) (w : ℕ) [NeZero w] :
    ∃ lov e₁ : ℝ,
      ((lov : ℝ) : EReal) = (roundFloor (precisionSet 2 w) (AzRat.toRat q : ℝ)).val ∧
      lov ≤ AzRat.toRat q ∧ AzRat.toRat q ≤ lov + e₁ ∧ (lov = AzRat.toRat q → e₁ = 0) ∧
      0 ≤ e₁ ∧
      (e₁ ≠ 0 → ∃ k : ℤ, e₁ = (2 : ℝ) ^ (k - w) ∧ (2 : ℝ) ^ (k - 1) ≤ |lov| ∧
        |lov| < (2 : ℝ) ^ k) ∧
      ((lov + e₁ : ℝ) : EReal) ∈ floatSet w ∧
      Rounds (mulRatApprox (finite s e p' m hv) q w).1
        (if s then finiteVal s e m * lov else finiteVal s e m * (lov + e₁)) ∧
      Rounds (mulRatApprox (finite s e p' m hv) q w).2
        (if s then finiteVal s e m * (lov + e₁) else finiteVal s e m * lov) := by
  unfold mulRatApprox
  simp only
  rw [ofAzRatRound_eq_roundVal]
  obtain ⟨lov, e₁, hlo, he₁, hlo1, hlo2, hlo3, hlo4, hlo5, hmem⟩ :=
    truncError_spec w (AzRat.toRat q : ℝ)
  have hlofl : ((lov : ℝ) : EReal) = (roundFloor (precisionSet 2 w) (AzRat.toRat q : ℝ)).val := by
    rw [fst_roundVal] at hlo
    change (ofEReal w .Floor (AzRat.toRat q : ℝ)).toVal = _ at hlo
    have h := (ofEReal_spec w .Floor (AzRat.toRat q : ℝ)).2
    rw [val_round_floatSet] at h
    rw [h, Option.some.injEq] at hlo
    exact hlo.symm
  have hhi : (addPrecRound (roundVal w .Floor (some ((AzRat.toRat q : ℝ) : EReal))).1
      (truncError (roundVal w .Floor (some ((AzRat.toRat q : ℝ) : EReal)))) w .Ceiling).1.toVal
      = some ((lov + e₁ : ℝ) : EReal) := by
    rw [addPrecRound_eq_liftVal₂]
    unfold liftVal₂
    rw [hlo, he₁, Option.bind_some, Option.bind_some, Spec.add_coe_coe, fst_roundVal]
    change (ofEReal w .Ceiling ((lov + e₁ : ℝ) : EReal)).toVal = _
    rw [(ofEReal_spec w .Ceiling (lov + e₁)).2, val_round_of_mem _ .Ceiling hmem]
  have hmulLo : Rounds (fun p mode => mulPrecRound (finite s e p' m hv)
      (roundVal w .Floor (some ((AzRat.toRat q : ℝ) : EReal))).1 p mode)
      (finiteVal s e m * lov) := by
    intro p'' _ mo
    beta_reduce
    rw [mulPrecRound_eq_liftVal₂]
    unfold liftVal₂
    rw [toVal_finite, hlo, Option.bind_some, Option.bind_some, Spec.mul_coe_coe]
  have hmulHi : Rounds (fun p mode => mulPrecRound (finite s e p' m hv)
      (addPrecRound (roundVal w .Floor (some ((AzRat.toRat q : ℝ) : EReal))).1
        (truncError (roundVal w .Floor (some ((AzRat.toRat q : ℝ) : EReal)))) w .Ceiling).1
      p mode) (finiteVal s e m * (lov + e₁)) := by
    intro p'' _ mo
    beta_reduce
    rw [mulPrecRound_eq_liftVal₂ (finite s e p' m hv)]
    unfold liftVal₂
    rw [toVal_finite, hhi, Option.bind_some, Option.bind_some, Spec.mul_coe_coe]
  cases s
  · exact ⟨lov, e₁, hlofl, hlo1, hlo2, hlo3, hlo4, hlo5, hmem, hmulHi, hmulLo⟩
  · exact ⟨lov, e₁, hlofl, hlo1, hlo2, hlo3, hlo4, hlo5, hmem, hmulLo, hmulHi⟩

/-! ### Termination -/

/-- From the working precision `p + |num| + 2|den| + |m| + 2|e| + 2` on, rounding is possible
for a product that is not dyadic. -/
theorem mulRatApprox_possible (s : Bool) (e : AzInt) (p' : ℕ) (m : AzNat) (hv : FiniteValid p' m)
    (q : AzRat) (hq : q.num ≠ 0) (hnd : ¬ (oddDen q).toNat ∣ m.toNat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (w : ℕ)
    (hw : p + q.num.size + 2 * q.den.size + m.size + 2 * e.abs.toNat + 2 ≤ w) :
    (roundingPossible (mulRatApprox (finite s e p' m hv) q w).1
      (mulRatApprox (finite s e p' m hv) q w).2 p mode).isSome = true := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lov, e₁, hlofl, hlo1, hlo2, hlo3, hlo4, hlo5, _, hl, hh⟩ :=
    mulRatApprox_spec s e p' m hv q w
  set xv := finiteVal s e m with hxv
  set v := xv * AzRat.toRat q with hvdef
  have hvB : ((v : ℝ) : EReal) ∉ floatSet (p + 1) :=
    fun h => hnd (oddDen_dvd_of_mem_floatSet s e p' m hv q hq p h)
  have hx0 := finiteVal_ne_zero s e hv
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => hq ((AzRat.toRat_eq_zero_iff q).mp h)
  have hv0 : v ≠ 0 := mul_ne_zero hx0 hq0
  have hden_pos := AzRat.den_toNat_pos q
  have hden_lt : q.den.toNat < 2 ^ q.den.size := by
    have := Nat.lt_size_self q.den.toNat
    rwa [AzNat.size_toNat] at this
  have habs_e : (e.abs.toNat : ℤ) = |e.toInt| := (AzInt.abs_toInt e).symm
  set a₀ : ℕ := m.size + e.abs.toNat with ha₀def
  have ha₀ : (m.size : ℤ) - e.toInt ≤ a₀ := by
    have := neg_abs_le e.toInt
    push_cast [ha₀def]
    omega
  have hv_lower : 1 / (q.den.toNat * 2 ^ a₀) ≤ |v| := by
    have := dist_prod_boundary s e m q 0 0 0 (by simp) a₀ ha₀ (by simp) hv0
    rwa [sub_zero] at this
  have hLlow := neg_le_log_of_one_div_le v hv0 _ hden_pos _ hden_lt a₀ hv_lower
  set a : ℕ := p + a₀ + q.den.size with hadef
  have hdist : ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → b ≠ v →
      (b = 0 ∨ Int.log 2 |v| ≤ Int.log 2 |b|) → 1 / (q.den.toNat * 2 ^ a) ≤ |v - b| := by
    intro b hb hne hlog
    obtain ⟨M, k, hMk, hk⟩ : ∃ M k : ℤ, b = M * 2 ^ k ∧ -k ≤ a := by
      rcases eq_or_ne b 0 with hb0 | hb0
      · exact ⟨0, 0, by simp [hb0], by simp⟩
      · obtain ⟨M, k, hMk, hk⟩ := boundary_repr p b hb hb0
        refine ⟨M, k, hMk, ?_⟩
        rcases hlog with h | h
        · exact absurd h hb0
        · push_cast [hadef]
          omega
    exact dist_prod_boundary s e m q b M k hMk a (by push_cast [hadef]; omega) hk
      (fun h => hne h.symm)
  -- the bracket is narrow: `|x| · ε ≤ 2^(e + |num| + 1 − w)`
  have he₁ := truncErr_le q w lov e₁ hlofl hlo1 hlo5
  have hxabs := (abs_finiteVal_bounds s e hv).2
  have hwidth : |xv| * e₁ < 1 / (q.den.toNat * 2 ^ a) := by
    have h1 : |xv| * e₁ ≤ 2 ^ e.toInt * 2 ^ ((q.num.size : ℤ) + 1 - w) :=
      mul_le_mul hxabs.le he₁ hlo4 (by positivity)
    have h2 : (2 : ℝ) ^ e.toInt * 2 ^ ((q.num.size : ℤ) + 1 - w) ≤ 2 ^ (-(q.den.size : ℤ) - a) := by
      rw [← zpow_add₀ (by norm_num)]
      apply zpow_le_zpow_right₀ (by norm_num)
      have := le_abs_self e.toInt
      push_cast [hadef, ha₀def]
      omega
    have h3 := two_zpow_lt_one_div _ hden_pos _ hden_lt a
    linarith
  cases s with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
    have hxneg : xv < 0 := by
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact h
      · exact absurd ((finiteVal_pos_iff false e m (by
          intro hm; rw [hm] at hv; exact absurd hv.size_eq (by simp; exact
            (lt_of_lt_of_le hv.pos (le_alignedBits p')).ne))).mp h) (by simp)
    apply roundingPossible_isSome_of_no_boundary p mode hl hh (by nlinarith)
    apply no_boundary_of_dist p v _ _ _ hv0 hvB (by nlinarith) (by nlinarith) hdist
    rw [abs_of_neg hxneg] at hwidth
    linarith
  | true =>
    simp only [↓reduceIte] at hl hh
    have hxpos : 0 < xv := (finiteVal_pos_iff true e m (by
      intro hm; rw [hm] at hv; exact absurd hv.size_eq (by simp; exact
        (lt_of_lt_of_le hv.pos (le_alignedBits p')).ne))).mpr rfl
    apply roundingPossible_isSome_of_no_boundary p mode hl hh (by nlinarith)
    apply no_boundary_of_dist p v _ _ _ hv0 hvB (by nlinarith) (by nlinarith) hdist
    rw [abs_of_pos hxpos] at hwidth
    linarith

/-! ### The lift -/

/-- The fuel reaches the working precision of `mulRatApprox_possible`. -/
theorem mulRatBound_le (s : Bool) (e : AzInt) (p' : ℕ) (m : AzNat) (hv : FiniteValid p' m)
    (q : AzRat) (p : ℕ) :
    p + q.num.size + 2 * q.den.size + m.size + 2 * e.abs.toNat + 2
      ≤ zivStart q p * 2 ^ mulRatFuel (finite s e p' m hv) q p := by
  set A := p + q.num.size + 2 * q.den.size + m.size + 2 with hA
  have hA' : A < 2 ^ zivFuel A := by
    have := le_mul_two_pow_zivFuel A 1 one_pos
    have h2 : A ≠ 2 ^ zivFuel A := by
      unfold zivFuel
      have h3 : (AzNat.ofNat A).size = A.size := by rw [← AzNat.size_toNat, AzNat.toNat_ofNat]
      rw [h3]
      exact (Nat.lt_size_self A).ne
    omega
  have he : e.abs.toNat < 2 ^ e.abs.size := by
    have := Nat.lt_size_self e.abs.toNat
    rwa [AzNat.size_toNat] at this
  have hstart : 1 ≤ zivStart q p := by
    simp only [zivStart, zivGuardBits]; split_ifs <;> omega
  have hW : p + q.num.size + 2 * q.den.size + m.size + 2 * e.abs.toNat + 2
      = A + 2 * e.abs.toNat := by omega
  rw [hW]
  show A + 2 * e.abs.toNat ≤ zivStart q p * 2 ^ (zivFuel A + e.abs.size + 2)
  have h1 : 2 ^ zivFuel A ≤ 2 ^ (zivFuel A + e.abs.size + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (e.abs.size + 1) ≤ 2 ^ (zivFuel A + e.abs.size + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (zivFuel A + e.abs.size + 2) = 2 * 2 ^ (zivFuel A + e.abs.size + 1) := by
    rw [pow_succ]; ring
  have h4 : 2 ^ (e.abs.size + 1) = 2 * 2 ^ e.abs.size := by rw [pow_succ]; ring
  calc A + 2 * e.abs.toNat ≤ 2 ^ zivFuel A + 2 ^ (e.abs.size + 1) := by omega
    _ ≤ 2 ^ (zivFuel A + e.abs.size + 2) := by omega
    _ ≤ zivStart q p * 2 ^ (zivFuel A + e.abs.size + 2) := Nat.le_mul_of_pos_left _ hstart

/-- Multiplication by a rational is the lift of `EReal` multiplication with its value. -/
theorem mulRatPrecRound_eq_liftVal (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    mulRatPrecRound x q p mode
      = liftVal (fun a => Spec.mul a ((AzRat.toRat q : ℝ) : EReal)) x p mode := by
  cases x with
  | nan => rfl
  | infinity s =>
    unfold liftVal
    rw [toVal_infinity, Option.bind_some]
    by_cases hq : q.num = 0
    · have hq0 : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr hq
      cases s <;> simp [mulRatPrecRound, hq, hq0, Spec.mul]
    · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => hq ((AzRat.toRat_eq_zero_iff q).mp h)
      rw [Spec.mul_inf_coe s _ hq0, roundVal_inf]
      simp [mulRatPrecRound, hq, sign_eq_decide_pos q hq]
  | zero =>
    show (zero, Ordering.eq) = _
    unfold liftVal
    rw [toVal_zero, Option.bind_some]
    have : Spec.mul (0 : EReal) ((AzRat.toRat q : ℝ) : EReal) = some 0 := by
      rw [show (0 : EReal) = ((0 : ℝ) : EReal) by simp, Spec.mul_coe_coe, zero_mul]
    rw [this, roundVal_zero]
  | finite s e p' m hv =>
    unfold liftVal
    rw [toVal_finite, Option.bind_some, Spec.mul_coe_coe]
    by_cases hq : q.num = 0
    · have hq0 : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr hq
      simp only [mulRatPrecRound, hq, ↓reduceIte]
      rw [hq0, mul_zero, EReal.coe_zero, roundVal_zero]
    by_cases hdvd : (m.divMod (oddDen q)).2 = 0
    · simp only [mulRatPrecRound, hq, hdvd, ↓reduceIte]
      exact mulRatExact_eq s e p' m hv q hq hdvd p mode
    · simp only [mulRatPrecRound, hq, hdvd, ↓reduceIte]
      have hnd : ¬ (oddDen q).toNat ∣ m.toNat := by
        intro h
        apply hdvd
        obtain ⟨hqr, hlt⟩ := AzNat.divMod_toNat m (oddDen q)
        have hr : (oddDen q).toNat ∣ (m.divMod (oddDen q)).2.toNat := by
          have : (m.divMod (oddDen q)).2.toNat
              = m.toNat - (m.divMod (oddDen q)).1.toNat * (oddDen q).toNat := by omega
          rw [this]
          exact Nat.dvd_sub h (Dvd.intro_left _ rfl)
        have hr0 : (m.divMod (oddDen q)).2.toNat = 0 :=
          Nat.eq_zero_of_dvd_of_lt hr (hlt (oddDen_pos q).ne')
        exact AzNat.toNat_injective (hr0.trans AzNat.toNat_zero.symm)
      apply zivLoop_eq p mode _ (finiteVal s e m * AzRat.toRat q) ?_
        (p + q.num.size + 2 * q.den.size + m.size + 2 * e.abs.toNat + 2) ?_ _ _ ?_
        (mulRatBound_le s e p' m hv q p)
      · intro w hw
        have : NeZero w := ⟨hw.ne'⟩
        obtain ⟨lov, e₁, hlofl, hlo1, hlo2, hlo3, hlo4, _, hmem, hl, hh⟩ :=
          mulRatApprox_spec s e p' m hv q w
        have hx0 := finiteVal_ne_zero s e hv
        have hm0 : m ≠ 0 := by
          intro hm; rw [hm] at hv; exact absurd hv.size_eq (by simp; exact
            (lt_of_lt_of_le hv.pos (le_alignedBits p')).ne)
        cases s with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
          have hxneg : finiteVal false e m < 0 := by
            rcases lt_or_gt_of_ne hx0 with h | h
            · exact h
            · exact absurd ((finiteVal_pos_iff false e m hm0).mp h) (by simp)
          refine ⟨_, _, hl, hh, by nlinarith, by nlinarith, ?_⟩
          intro h
          have h1 : lov + e₁ = AzRat.toRat q := by
            have := mul_left_cancel₀ hx0 h
            exact this
          -- `q` is then representable, so the truncation was exact
          have hqmem : ((AzRat.toRat q : ℝ) : EReal) ∈ precisionSet 2 w := by
            rw [← h1]
            have h2 := hmem
            rw [floatSet_eq] at h2
            rcases h2 with h2 | h2
            · exact h2
            · exfalso; rcases h2 with h2 | h2 <;> simp at h2
          have hlo_exact : lov = AzRat.toRat q := by
            have := val_roundFloor_of_mem (precisionSet 2 w) hqmem
            rw [← hlofl] at this
            exact EReal.coe_eq_coe_iff.mp this
          rw [hlo_exact]
        | true =>
          simp only [↓reduceIte] at hl hh
          have hxpos : 0 < finiteVal true e m := (finiteVal_pos_iff true e m hm0).mpr rfl
          refine ⟨_, _, hl, hh, by nlinarith, by nlinarith, ?_⟩
          intro h
          have h1 : lov = AzRat.toRat q := mul_left_cancel₀ hx0 h
          rw [hlo3 h1, add_zero, h1]
      · intro w hw
        exact mulRatApprox_possible s e p' m hv q hq hnd p mode w hw
      · simp only [zivStart, zivGuardBits]
        split_ifs <;> omega

end Azurite.AzFloat
