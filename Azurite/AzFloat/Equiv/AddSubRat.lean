/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddSubRat
import Azurite.AzFloat.Equiv.Ziv
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzNat.Equiv.Size
import Azurite.AzRat.Equiv.LogBase
import Azurite.AzRat.Equiv.Unary

/-!
# Addition of an `AzFloat` and an `AzRat` is a lift

`addRatPrecRound_eq_liftVal`: `addRatPrecRound x q p mode = liftVal (fun a => Spec.add a q) x
p mode`, where `q` stands for the value of the rational; `subRatPrecRound_eq_liftVal` and
`ratSubPrecRound_eq_liftVal` for the two subtractions.  Two facts feed `zivLoop_eq`:

* `addRatApprox_spec`: the two ends of the bracket at working precision `w` are the rounding
  procedures of `x + lo` and `x + lo + ε`, where `lo ≤ q ≤ lo + ε` and `ε = 0` exactly when the
  truncation of `q` was exact (`truncError_spec`);
* `addRatApprox_possible`: from the working precision `p + |num| + 2|den| + |m| + |e| + 2` on,
  rounding is possible.  If the exact sum `v` is a boundary, `q` is dyadic
  (`toRat_mem_precisionSet_of_dyadic`) and the bracket is a point.  Otherwise the boundaries
  adjacent to `v` are at distance at least `1/(den · 2^a)` from it (`dist_sum_boundary`:
  `v − b` is a rational with that denominator), while the bracket has width `ε ≤ 2^(|num|+1−w)`,
  so it contains no boundary and the two `(p + 1)`-bit truncations agree.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### Values -/

/-- The value of a rational as a quotient of integers. -/
theorem coe_toRat_eq (q : AzRat) :
    (AzRat.toRat q : ℝ)
      = (((if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) : ℤ) : ℝ) /
        (q.den.toNat : ℝ) := by
  rw [Rat.cast_def]
  rfl

/-- `|q| < 2^|num|`. -/
theorem abs_toRat_lt (q : AzRat) : |(AzRat.toRat q : ℝ)| < (2 : ℝ) ^ (q.num.size : ℤ) := by
  rw [AzRat.abs_toRat_eq]
  have hden : (1 : ℝ) ≤ q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  have hnum : (q.num.toNat : ℝ) < 2 ^ q.num.size := by
    have := Nat.lt_size_self q.num.toNat
    rw [AzNat.size_toNat] at this
    exact_mod_cast this
  rw [zpow_natCast]
  calc (q.num.toNat : ℝ) / q.den.toNat ≤ q.num.toNat := div_le_self (by positivity) hden
    _ < _ := hnum

/-- A float's value as an integer times a power of two. -/
theorem finiteVal_eq_int_mul (s : Bool) (e : AzInt) (m : AzNat) :
    finiteVal s e m
      = (((if s then (m.toNat : ℤ) else -(m.toNat : ℤ)) : ℤ) : ℝ) * 2 ^ (e.toInt - m.size) := by
  unfold finiteVal
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]; ring
  · simp only [↓reduceIte, Int.cast_natCast]; ring

/-- The magnitude of an `AzInt`'s value. -/
theorem _root_.Azurite.AzInt.abs_toInt (z : AzInt) : |z.toInt| = (z.abs.toNat : ℤ) := by
  unfold AzInt.toInt
  split_ifs <;> simp

/-! ### Distances to boundaries and dyadic rationals -/

/-- The distance from `x + q` to `b = M · 2^k`, once `a` dominates the exponents of both `x`
and `b`: at least `1/(den · 2^a)`, as `x + q − b` is a nonzero rational with that
denominator. -/
theorem dist_sum_boundary (s : Bool) (e : AzInt) (m : AzNat) (q : AzRat) (b : ℝ) (M k : ℤ)
    (hb : b = M * 2 ^ k) (a : ℕ) (ha : (m.size : ℤ) - e.toInt ≤ a) (hk : -k ≤ a)
    (hne : finiteVal s e m + AzRat.toRat q ≠ b) :
    1 / (q.den.toNat * 2 ^ a) ≤ |finiteVal s e m + AzRat.toRat q - b| := by
  generalize hc : (if s then (m.toNat : ℤ) else -(m.toNat : ℤ)) = c
  generalize hσ : (if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) = σ
  obtain ⟨N, hN⟩ := exists_int_mul_sub_dyadic c M (e.toInt - m.size) k a (by omega) hk
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  have hD : (0 : ℝ) < q.den.toNat * 2 ^ a := by positivity
  have h1 : (finiteVal s e m - b) * 2 ^ a = N := by
    rw [finiteVal_eq_int_mul, hc, hb]
    exact hN
  have h2 : (AzRat.toRat q : ℝ) * q.den.toNat = σ := by
    rw [coe_toRat_eq, hσ]
    exact div_mul_cancel₀ _ hden.ne'
  apply one_div_le_abs_of_mul_eq_int _ _ hD (σ * 2 ^ a + N * q.den.toNat) _ (sub_ne_zero.mpr hne)
  push_cast
  linear_combination (q.den.toNat : ℝ) * h1 + (2 : ℝ) ^ a * h2

/-- A rational whose value is dyadic is representable at every precision of at least its
numerator's bit length. -/
theorem toRat_mem_precisionSet_of_dyadic (q : AzRat) (N : ℤ) (a : ℕ)
    (h : (AzRat.toRat q : ℝ) * 2 ^ a = N) (w : ℕ) [NeZero w] (hw : q.num.size ≤ w) :
    ((AzRat.toRat q : ℝ) : EReal) ∈ precisionSet 2 w := by
  by_cases h0 : q.num = 0
  · left
    rw [(AzRat.toRat_eq_zero_iff q).mpr h0]
    simp
  have hden := AzRat.den_toNat_pos q
  have hnum := AzRat.num_toNat_pos q h0
  have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
  generalize hσ : (if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) = σ
  have hσabs : σ.natAbs = q.num.toNat := by
    rw [← hσ]; cases q.sign <;> simp
  have hσ0 : σ ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero] at hσabs
    omega
  -- the integer equation `σ · 2^a = N · den`
  have hint : σ * 2 ^ a = N * q.den.toNat := by
    have h' := h
    rw [coe_toRat_eq, hσ] at h'
    have hd : (q.den.toNat : ℝ) ≠ 0 := by positivity
    have : (σ : ℝ) * 2 ^ a = N * q.den.toNat := by
      rw [div_mul_eq_mul_div, div_eq_iff hd] at h'
      exact h'
    exact_mod_cast this
  have hdvd : q.den.toNat ∣ 2 ^ a * q.num.toNat := by
    have := congrArg Int.natAbs hint
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, hσabs, Int.natAbs_natCast] at this
    have h2 : Int.natAbs 2 = 2 := rfl
    rw [h2] at this
    exact ⟨N.natAbs, by rw [mul_comm (2 ^ a), this, mul_comm]⟩
  have hdvd2 : q.den.toNat ∣ 2 ^ a := hcop.symm.dvd_of_dvd_mul_right hdvd
  obtain ⟨t, _, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  right
  refine ⟨σ, -(t : ℤ), hσ0, ?_, ?_⟩
  · have h1 : (q.num.toNat : ℤ) < 2 ^ q.num.size := by
      have := Nat.lt_size_self q.num.toNat
      rw [AzNat.size_toNat] at this
      exact_mod_cast this
    have h2 : (2 : ℤ) ^ q.num.size ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) hw
    rw [Int.abs_eq_natAbs, hσabs]
    exact lt_of_lt_of_le h1 h2
  · rw [EReal.coe_eq_coe_iff, coe_toRat_eq, hσ, ht]
    push_cast
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

/-! ### The approximation -/

/-- The bracket of `x + q` at working precision `w`: `lo` truncates `q` with its one-ulp error
`ε` (`0` if exact), and the two ends round `x + lo` and `x + lo + ε`. -/
theorem addRatApprox_spec (s : Bool) (e : AzInt) (p' : ℕ) (m : AzNat) (hv : FiniteValid p' m)
    (q : AzRat) (w : ℕ) [NeZero w] :
    ∃ lov e₁ : ℝ,
      ((lov : ℝ) : EReal) = (roundFloor (precisionSet 2 w) (AzRat.toRat q : ℝ)).val ∧
      lov ≤ AzRat.toRat q ∧ AzRat.toRat q ≤ lov + e₁ ∧ (lov = AzRat.toRat q → e₁ = 0) ∧
      0 ≤ e₁ ∧
      (e₁ ≠ 0 → ∃ k : ℤ, e₁ = (2 : ℝ) ^ (k - w) ∧ (2 : ℝ) ^ (k - 1) ≤ |lov| ∧
        |lov| < (2 : ℝ) ^ k) ∧
      Rounds (addRatApprox (finite s e p' m hv) q w).1 (finiteVal s e m + lov) ∧
      Rounds (addRatApprox (finite s e p' m hv) q w).2 (finiteVal s e m + lov + e₁) := by
  unfold addRatApprox
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
  -- the next float up
  have hhi : (addPrecRound (roundVal w .Floor (some ((AzRat.toRat q : ℝ) : EReal))).1
      (truncError (roundVal w .Floor (some ((AzRat.toRat q : ℝ) : EReal)))) w .Ceiling).1.toVal
      = some ((lov + e₁ : ℝ) : EReal) := by
    rw [addPrecRound_eq_liftVal₂]
    unfold liftVal₂
    rw [hlo, he₁, Option.bind_some, Option.bind_some, Spec.add_coe_coe, fst_roundVal]
    change (ofEReal w .Ceiling ((lov + e₁ : ℝ) : EReal)).toVal = _
    rw [(ofEReal_spec w .Ceiling (lov + e₁)).2, val_round_of_mem _ .Ceiling hmem]
  refine ⟨lov, e₁, hlofl, hlo1, hlo2, hlo3, hlo4, hlo5, ?_, ?_⟩
  · intro p'' _ mo
    beta_reduce
    rw [addPrecRound_eq_liftVal₂ (finite s e p' m hv)]
    unfold liftVal₂
    rw [toVal_finite, hlo, Option.bind_some, Option.bind_some, Spec.add_coe_coe]
  · intro p'' _ mo
    beta_reduce
    rw [addPrecRound_eq_liftVal₂ (finite s e p' m hv)]
    unfold liftVal₂
    rw [toVal_finite, hhi, Option.bind_some, Option.bind_some, Spec.add_coe_coe, add_assoc]

/-! ### Termination -/

/-- From the working precision `p + |num| + 2|den| + |m| + |e| + 2` on, rounding is
possible. -/
theorem addRatApprox_possible (s : Bool) (e : AzInt) (p' : ℕ) (m : AzNat) (hv : FiniteValid p' m)
    (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) (w : ℕ)
    (hw : p + q.num.size + 2 * q.den.size + m.size + e.abs.toNat + 2 ≤ w) :
    (roundingPossible (addRatApprox (finite s e p' m hv) q w).1
      (addRatApprox (finite s e p' m hv) q w).2 p mode).isSome = true := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lov, e₁, hlofl, hlo1, hlo2, hlo3, hlo4, hlo5, hl, hh⟩ :=
    addRatApprox_spec s e p' m hv q w
  set xv := finiteVal s e m with hxv
  set v := xv + AzRat.toRat q with hvdef
  unfold roundingPossible
  rw [hl (p + 1) .Floor, hh (p + 1) .Floor]
  -- it suffices that the two floors agree
  suffices hsuff : (roundFloor (floatSet (p + 1)) (xv + lov)).val
      = (roundFloor (floatSet (p + 1)) (xv + lov + e₁)).val by
    have heq : (roundVal (p + 1) .Floor (some ((xv + lov : ℝ) : EReal))).1
        = (roundVal (p + 1) .Floor (some ((xv + lov + e₁ : ℝ) : EReal))).1 := by
      rw [fst_roundVal, fst_roundVal]
      change ofEReal (p + 1) .Floor ((xv + lov : ℝ) : EReal)
        = ofEReal (p + 1) .Floor ((xv + lov + e₁ : ℝ) : EReal)
      exact toVal_injective (p + 1) (ofEReal_spec (p + 1) .Floor _).1
        (ofEReal_spec (p + 1) .Floor _).1
        (by rw [(ofEReal_spec (p + 1) .Floor _).2, (ofEReal_spec (p + 1) .Floor _).2]; exact
          congrArg some hsuff)
    rw [heq]
    simp
  have hden_pos : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  have hden_lt : (q.den.toNat : ℝ) < 2 ^ q.den.size := by
    have := Nat.lt_size_self q.den.toNat
    rw [AzNat.size_toNat] at this
    exact_mod_cast this
  have habs_e : (e.abs.toNat : ℤ) = |e.toInt| := (AzInt.abs_toInt e).symm
  set a₀ : ℕ := m.size + e.abs.toNat with ha₀def
  have ha₀ : (m.size : ℤ) - e.toInt ≤ a₀ := by
    have := neg_abs_le e.toInt
    push_cast [ha₀def]
    omega
  by_cases hvB : ((v : ℝ) : EReal) ∈ floatSet (p + 1)
  · -- the exact sum is a boundary: `q` is dyadic, the truncation is exact, the bracket a point
    obtain ⟨M, k, hMk⟩ : ∃ M k : ℤ, v = M * 2 ^ k := by
      rcases eq_or_ne v 0 with hv0 | hv0
      · exact ⟨0, 0, by simp [hv0]⟩
      · obtain ⟨M, k, hMk, _⟩ := boundary_repr p v hvB hv0
        exact ⟨M, k, hMk⟩
    set a : ℕ := (max ((m.size : ℤ) - e.toInt) (-k)).toNat with hadef
    obtain ⟨N, hN⟩ := exists_int_mul_sub_dyadic M (if s then (m.toNat : ℤ) else -(m.toNat : ℤ))
      k (e.toInt - m.size) a
      (by have := Int.self_le_toNat (max ((m.size : ℤ) - e.toInt) (-k)); omega)
      (by have := Int.self_le_toNat (max ((m.size : ℤ) - e.toInt) (-k)); omega)
    have hq : (AzRat.toRat q : ℝ) * 2 ^ a = N := by
      rw [← hN, ← finiteVal_eq_int_mul, ← hMk]
      ring
    have hqmem := toRat_mem_precisionSet_of_dyadic q N a hq w (by omega)
    have hlo_exact : lov = AzRat.toRat q := by
      have := val_roundFloor_of_mem (precisionSet 2 w) hqmem
      rw [← hlofl] at this
      exact EReal.coe_eq_coe_iff.mp this
    rw [hlo3 hlo_exact, add_zero]
  · -- the exact sum is not a boundary: it is at a positive distance from the adjacent ones
    have hv0 : v ≠ 0 := fun h => hvB (by rw [h]; exact ⟨zero, Or.inr rfl, by simp⟩)
    set L := Int.log 2 |v| with hL
    have hv_lower : 1 / (q.den.toNat * 2 ^ a₀) ≤ |v| := by
      have := dist_sum_boundary s e m q 0 0 0 (by simp) a₀ ha₀ (by simp) (by simpa using hv0)
      simpa using this
    have hLlow : -(q.den.size : ℤ) - a₀ ≤ L := by
      apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hv0)).mp
      push_cast
      calc (2 : ℝ) ^ (-(q.den.size : ℤ) - a₀) = 1 / (2 ^ q.den.size * 2 ^ a₀) := by
            rw [zpow_sub₀ (by norm_num), zpow_neg, zpow_natCast, zpow_natCast]
            field_simp
        _ ≤ 1 / (q.den.toNat * 2 ^ a₀) := by
            apply one_div_le_one_div_of_le (by positivity)
            exact mul_le_mul_of_nonneg_right hden_lt.le (by positivity)
        _ ≤ |v| := hv_lower
    set a : ℕ := p + a₀ + q.den.size with hadef
    have hdist : ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → b ≠ v →
        (b = 0 ∨ L ≤ Int.log 2 |b|) → 1 / (q.den.toNat * 2 ^ a) ≤ |v - b| := by
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
      exact dist_sum_boundary s e m q b M k hMk a (by push_cast [hadef]; omega) hk
        (fun h => hne h.symm)
    have hpow_lt : (2 : ℝ) ^ (-(q.den.size : ℤ) - a) < 1 / (q.den.toNat * 2 ^ a) := by
      calc (2 : ℝ) ^ (-(q.den.size : ℤ) - a) = 1 / (2 ^ q.den.size * 2 ^ a) := by
            rw [zpow_sub₀ (by norm_num), zpow_neg, zpow_natCast, zpow_natCast]
            field_simp
        _ < 1 / (q.den.toNat * 2 ^ a) := by
            apply one_div_lt_one_div_of_lt (by positivity)
            exact mul_lt_mul_of_pos_right hden_lt (by positivity)
    -- the adjacent boundaries
    obtain ⟨bmv, hbm⟩ : ∃ r : ℝ, ((r : ℝ) : EReal) = (roundFloor (floatSet (p + 1)) v).val := by
      rw [val_roundFloor_floatSet]; exact precisionSet_exists_real _
    obtain ⟨bpv, hbp⟩ : ∃ r : ℝ, ((r : ℝ) : EReal) = (roundCeiling (floatSet (p + 1)) v).val := by
      rw [val_roundCeiling_floatSet]; exact precisionSet_exists_real _
    have hbm_mem : ((bmv : ℝ) : EReal) ∈ floatSet (p + 1) := hbm ▸ (roundFloor _ _).property
    have hbp_mem : ((bpv : ℝ) : EReal) ∈ floatSet (p + 1) := hbp ▸ (roundCeiling _ _).property
    have hbm_le : bmv ≤ v := by
      have := (isGreatest_roundFloor (floatSet (p + 1)) v).1.2
      rw [← hbm] at this; exact EReal.coe_le_coe_iff.mp this
    have hbp_ge : v ≤ bpv := by
      have := (isLeast_roundCeiling (floatSet (p + 1)) v).1.2
      rw [← hbp] at this; exact EReal.coe_le_coe_iff.mp this
    have hbm_ne : bmv ≠ v := fun h => hvB (h ▸ hbm_mem)
    have hbp_ne : bpv ≠ v := fun h => hvB (h ▸ hbp_mem)
    have h2L : (2 : ℝ) ^ L ≤ |v| := Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hv0)
    have h2Lpos : (0 : ℝ) < 2 ^ L := zpow_pos (by norm_num) _
    have hmemL : ∀ c : ℤ, |c| ≤ 1 → (((c : ℝ) * 2 ^ L : ℝ) : EReal) ∈ floatSet (p + 1) :=
      fun c hc => mem_floatSet_mul_zpow (p + 1) c L
        (le_trans hc (one_le_pow₀ (by norm_num)))
    have hLbm : bmv = 0 ∨ L ≤ Int.log 2 |bmv| := by
      right
      rcases lt_or_gt_of_ne hv0 with hneg | hpos
      · have hbneg : bmv < 0 := lt_of_le_of_lt hbm_le hneg
        apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hbneg.ne)).mp
        push_cast
        rw [abs_of_neg hbneg]
        rw [abs_of_neg hneg] at h2L
        linarith
      · have hmem := hmemL 1 (by simp)
        simp only [Int.cast_one, one_mul] at hmem
        rw [abs_of_pos hpos] at h2L
        have := (isGreatest_roundFloor (floatSet (p + 1)) v).2
          ⟨hmem, EReal.coe_le_coe_iff.mpr h2L⟩
        rw [← hbm] at this
        have hle := EReal.coe_le_coe_iff.mp this
        apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num)
          (abs_pos.mpr (lt_of_lt_of_le h2Lpos hle).ne')).mp
        push_cast
        rw [abs_of_pos (lt_of_lt_of_le h2Lpos hle)]
        exact hle
    have hLbp : bpv = 0 ∨ L ≤ Int.log 2 |bpv| := by
      right
      rcases lt_or_gt_of_ne hv0 with hneg | hpos
      · have hmem := hmemL (-1) (by simp)
        simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at hmem
        rw [abs_of_neg hneg] at h2L
        have := (isLeast_roundCeiling (floatSet (p + 1)) v).2
          ⟨hmem, EReal.coe_le_coe_iff.mpr (by linarith : v ≤ -(2 : ℝ) ^ L)⟩
        rw [← hbp] at this
        have hle := EReal.coe_le_coe_iff.mp this
        have hbneg : bpv < 0 := lt_of_le_of_lt hle (by linarith)
        apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hbneg.ne)).mp
        push_cast
        rw [abs_of_neg hbneg]
        linarith
      · rw [abs_of_pos hpos] at h2L
        have hbpos : 0 < bpv := lt_of_lt_of_le hpos hbp_ge
        apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hbpos.ne')).mp
        push_cast
        rw [abs_of_pos hbpos]
        linarith
    have hDm : (2 : ℝ) ^ (-(q.den.size : ℤ) - a) < v - bmv := by
      have h := hdist bmv hbm_mem hbm_ne hLbm
      rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_ne hbm_le hbm_ne))] at h
      exact lt_of_lt_of_le hpow_lt h
    have hDp : (2 : ℝ) ^ (-(q.den.size : ℤ) - a) < bpv - v := by
      have h := hdist bpv hbp_mem hbp_ne hLbp
      rw [abs_of_neg (sub_neg.mpr (lt_of_le_of_ne hbp_ge hbp_ne.symm))] at h
      linarith [lt_of_lt_of_le hpow_lt h]
    -- the bracket is narrow: `ε ≤ 2^(|num| + 1 − w)`
    have hq_lo : AzRat.toRat q - lov ≤ (2 : ℝ) ^ ((q.num.size : ℤ) - w) := by
      rcases eq_or_ne (AzRat.toRat q : ℝ) 0 with hq0 | hq0
      · have hmem : ((AzRat.toRat q : ℝ) : EReal) ∈ precisionSet 2 w := Or.inl (by rw [hq0]; simp)
        have h := val_roundFloor_of_mem (precisionSet 2 w) hmem
        rw [← hlofl] at h
        rw [EReal.coe_eq_coe_iff.mp h]
        simp only [sub_self]
        positivity
      · have h := sub_roundFloor_lt_precScale w (AzRat.toRat q : ℝ) hq0 lov hlofl
        have hsc : precScale 2 w (AzRat.toRat q : ℝ) ≤ 2 ^ ((q.num.size : ℤ) - w) := by
          unfold precScale
          push_cast
          apply zpow_le_zpow_right₀ (by norm_num)
          have := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (abs_pos.mpr hq0)).mp
            (by push_cast; exact abs_toRat_lt q)
          omega
        linarith
    have hlov_abs : |lov| < (2 : ℝ) ^ ((q.num.size : ℤ) + 1) := by
      have h1 := abs_toRat_lt q
      have h2 : (2 : ℝ) ^ ((q.num.size : ℤ) - w) ≤ 2 ^ (q.num.size : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h3 : |lov| ≤ |(AzRat.toRat q : ℝ)| + (AzRat.toRat q - lov) :=
        abs_le.mpr ⟨by linarith [neg_abs_le (AzRat.toRat q : ℝ)],
          by linarith [le_abs_self (AzRat.toRat q : ℝ)]⟩
      rw [zpow_add_one₀ (by norm_num)]
      linarith
    have he₁ : e₁ ≤ (2 : ℝ) ^ ((q.num.size : ℤ) + 1 - w) := by
      rcases eq_or_ne e₁ 0 with h0 | h0
      · rw [h0]; positivity
      · obtain ⟨k, hk, hk1, hk2⟩ := hlo5 h0
        have : k - 1 < (q.num.size : ℤ) + 1 :=
          (zpow_lt_zpow_iff_right₀ (by norm_num)).mp (lt_of_le_of_lt hk1 hlov_abs)
        rw [hk]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hgap : (2 : ℝ) ^ ((q.num.size : ℤ) + 1 - w) ≤ 2 ^ (-(q.den.size : ℤ) - a) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      push_cast [hadef, ha₀def]
      omega
    -- no boundary lies in `(x + lo, x + lo + ε]`
    have hnob : ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) →
        ¬ (xv + lov < b ∧ b ≤ xv + lov + e₁) := by
      intro b hb ⟨hb1, hb2⟩
      rcases le_or_gt b v with hbv | hbv
      · have hbv_le_bm : b ≤ bmv := by
          have := (isGreatest_roundFloor (floatSet (p + 1)) v).2
            ⟨hb, EReal.coe_le_coe_iff.mpr hbv⟩
          rw [← hbm] at this
          exact EReal.coe_le_coe_iff.mp this
        linarith
      · have hbp_le : bpv ≤ b := by
          have := (isLeast_roundCeiling (floatSet (p + 1)) v).2
            ⟨hb, EReal.coe_le_coe_iff.mpr hbv.le⟩
          rw [← hbp] at this
          exact EReal.coe_le_coe_iff.mp this
        linarith
    -- hence the two floors agree
    obtain ⟨fh, hfh⟩ : ∃ r : ℝ,
        ((r : ℝ) : EReal) = (roundFloor (floatSet (p + 1)) (xv + lov + e₁)).val := by
      rw [val_roundFloor_floatSet]; exact precisionSet_exists_real _
    have hfh_mem : ((fh : ℝ) : EReal) ∈ floatSet (p + 1) := hfh ▸ (roundFloor _ _).property
    have hfh_le : fh ≤ xv + lov + e₁ := by
      have := (isGreatest_roundFloor (floatSet (p + 1)) (xv + lov + e₁)).1.2
      rw [← hfh] at this; exact EReal.coe_le_coe_iff.mp this
    have hfh_le' : fh ≤ xv + lov := by
      by_contra hcon
      push Not at hcon
      exact hnob fh hfh_mem ⟨hcon, hfh_le⟩
    apply le_antisymm
    · exact (isGreatest_roundFloor (floatSet (p + 1)) (xv + lov + e₁)).2
        ⟨(roundFloor _ _).property,
          le_trans (isGreatest_roundFloor (floatSet (p + 1)) (xv + lov)).1.2
            (EReal.coe_le_coe_iff.mpr (by linarith))⟩
    · rw [← hfh]
      exact (isGreatest_roundFloor (floatSet (p + 1)) (xv + lov)).2
        ⟨hfh_mem, EReal.coe_le_coe_iff.mpr hfh_le'⟩

/-! ### The lifts -/

/-- The fuel reaches the working precision of `addRatApprox_possible`. -/
theorem addRatBound_le (s : Bool) (e : AzInt) (p' : ℕ) (m : AzNat) (hv : FiniteValid p' m)
    (q : AzRat) (p : ℕ) :
    p + q.num.size + 2 * q.den.size + m.size + e.abs.toNat + 2
      ≤ zivStart q p * 2 ^ addRatFuel (finite s e p' m hv) q p := by
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
  have hW : p + q.num.size + 2 * q.den.size + m.size + e.abs.toNat + 2 = A + e.abs.toNat := by
    omega
  rw [hW]
  show A + e.abs.toNat ≤ zivStart q p * 2 ^ (zivFuel A + e.abs.size + 1)
  have h1 : 2 ^ zivFuel A ≤ 2 ^ (zivFuel A + e.abs.size) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ e.abs.size ≤ 2 ^ (zivFuel A + e.abs.size) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (zivFuel A + e.abs.size + 1) = 2 * 2 ^ (zivFuel A + e.abs.size) := by
    rw [pow_succ]; ring
  calc A + e.abs.toNat ≤ 2 ^ zivFuel A + 2 ^ e.abs.size := by omega
    _ ≤ 2 ^ (zivFuel A + e.abs.size + 1) := by omega
    _ ≤ zivStart q p * 2 ^ (zivFuel A + e.abs.size + 1) := Nat.le_mul_of_pos_left _ hstart

/-- Addition of a rational is the lift of `EReal` addition with its value. -/
theorem addRatPrecRound_eq_liftVal (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    addRatPrecRound x q p mode
      = liftVal (fun a => Spec.add a ((AzRat.toRat q : ℝ) : EReal)) x p mode := by
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;> simp [addRatPrecRound, liftVal, Spec.add]
  | zero =>
    show ofAzRatRound q p mode = _
    unfold liftVal
    rw [toVal_zero, Option.bind_some, Spec.add_zero_left, ofAzRatRound_eq_roundVal]
  | finite s e p' m hv =>
    show zivLoop _ p mode _ _ = _
    unfold liftVal
    rw [toVal_finite, Option.bind_some, Spec.add_coe_coe]
    apply zivLoop_eq p mode _ (finiteVal s e m + AzRat.toRat q) ?_
      (p + q.num.size + 2 * q.den.size + m.size + e.abs.toNat + 2) ?_ _ _ ?_
      (addRatBound_le s e p' m hv q p)
    · intro w hw
      have : NeZero w := ⟨hw.ne'⟩
      obtain ⟨lov, e₁, _, hlo1, hlo2, hlo3, _, _, hl, hh⟩ := addRatApprox_spec s e p' m hv q w
      refine ⟨_, _, hl, hh, by linarith, by linarith, ?_⟩
      intro h
      have h1 : lov = AzRat.toRat q := by linarith
      rw [hlo3 h1, add_zero, h1]
    · intro w hw
      exact addRatApprox_possible s e p' m hv q p mode w hw
    · simp only [zivStart, zivGuardBits]
      split_ifs <;> omega

/-- The value of a negated rational. -/
theorem coe_toRat_neg (q : AzRat) :
    ((AzRat.toRat (-q) : ℝ) : EReal) = -((AzRat.toRat q : ℝ) : EReal) := by
  rw [AzRat.toRat_neg]
  push_cast
  rfl

/-- Subtraction of a rational is the lift of `EReal` subtraction with its value. -/
theorem subRatPrecRound_eq_liftVal (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    subRatPrecRound x q p mode
      = liftVal (fun a => Spec.sub a ((AzRat.toRat q : ℝ) : EReal)) x p mode := by
  unfold subRatPrecRound
  rw [addRatPrecRound_eq_liftVal, coe_toRat_neg]
  rfl

/-- Subtraction from a rational is the lift of `EReal` subtraction from its value. -/
theorem ratSubPrecRound_eq_liftVal (q : AzRat) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ratSubPrecRound q x p mode
      = liftVal (fun a => Spec.sub ((AzRat.toRat q : ℝ) : EReal) a) x p mode := by
  unfold ratSubPrecRound
  rw [addRatPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_neg]
  cases x.toVal with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Option.bind_some]
    unfold Spec.sub Spec.add
    congr 1
    rw [add_comm]
    by_cases h1 : a = ⊤
    · subst h1; simp
    · by_cases h2 : a = ⊥
      · subst h2; simp
      · simp [h1, h2, EReal.neg_eq_top_iff, EReal.neg_eq_bot_iff]

end Azurite.AzFloat
