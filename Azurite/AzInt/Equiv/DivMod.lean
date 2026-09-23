/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.DivMod
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Equiv.Conversion
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Sub

namespace Azurite.AzInt

/-! ### Helpers. -/

/-- Unified `toInt` formula for `mkNorm`. -/
private lemma toInt_mkNorm (s : Bool) (a : AzNat) :
    (mkNorm s a).toInt = if s then (a.toNat : Int) else -(a.toNat : Int) := by
  by_cases h : a = 0
  · subst h
    have hm : mkNorm s (0 : AzNat) = 0 := by
      unfold mkNorm; simp only [↓reduceDIte]; rfl
    rw [hm, toInt_zero, AzNat.toNat_zero]
    cases s <;> simp
  · cases s
    · rw [toInt_mkNorm_false a h]; simp
    · rw [toInt_mkNorm_true a]; simp

/-- Unified `toInt` formula for `mkNonzero`. -/
private lemma toInt_mkNonzero (s : Bool) (a : AzNat) (h : a ≠ 0) :
    (mkNonzero s a h).toInt = if s then (a.toNat : Int) else -(a.toNat : Int) := by
  cases s
  · rw [toInt_mkNonzero_false a h]; simp
  · rw [toInt_mkNonzero_true a h]; simp

/-- If `z.sign = false`, then `z.abs ≠ 0`. -/
private lemma abs_ne_zero_of_sign_false {z : AzInt} (h : z.sign = false) : z.abs ≠ 0 := by
  intro h0
  rw [z.zero_sign h0] at h
  exact (Bool.false_ne_true h.symm).elim

/-- `z.toInt.natAbs = z.abs.toNat`. -/
private lemma natAbs_toInt (z : AzInt) : z.toInt.natAbs = z.abs.toNat := by
  show (if z.sign then ((z.abs.toNat : Int)) else -((z.abs.toNat : Int))).natAbs = z.abs.toNat
  cases z.sign <;> simp

/-- `|z.toInt| = (z.abs.toNat : Int)`. -/
private lemma abs_toInt (z : AzInt) : |z.toInt| = (z.abs.toNat : Int) := by
  rw [Int.abs_eq_natAbs, natAbs_toInt]

/-- `b.toInt = 0 ↔ b.abs.toNat = 0`. -/
private lemma toInt_eq_zero_iff_abs_toNat_eq_zero (z : AzInt) :
    z.toInt = 0 ↔ z.abs.toNat = 0 := by
  show (if z.sign then ((z.abs.toNat : Int)) else -((z.abs.toNat : Int))) = 0 ↔ _
  cases z.sign <;> simp

/-- Generalized Euclidean uniqueness handling `b = 0` too. -/
private lemma ediv_emod_unique_general {a b q r : Int}
    (h_id : q * b + r = a)
    (h_nonzero : b ≠ 0 → 0 ≤ r ∧ r < |b|)
    (h_b_zero : b = 0 → q = 0 ∧ r = a) :
    a / b = q ∧ a % b = r := by
  by_cases hb : b = 0
  · rw [hb, Int.ediv_zero, Int.emod_zero]
    obtain ⟨hq, hr⟩ := h_b_zero hb
    exact ⟨hq.symm, hr.symm⟩
  · obtain ⟨h_lo, h_hi⟩ := h_nonzero hb
    rcases lt_trichotomy b 0 with hneg | hzero | hpos
    · have h_npos : 0 < -b := by linarith
      have h_abs_eq : |b| = -b := abs_of_neg hneg
      have h_hi' : r < -b := by rw [← h_abs_eq]; exact h_hi
      have h_sum : r + (-b) * (-q) = a := by linarith
      obtain ⟨h_div, h_mod⟩ := (Int.ediv_emod_unique h_npos).mpr ⟨h_sum, h_lo, h_hi'⟩
      refine ⟨?_, ?_⟩
      · have h1 : a / -b = -q := h_div
        rw [Int.ediv_neg] at h1
        linarith
      · rw [show b = -(-b) from (neg_neg b).symm, Int.emod_neg, h_mod]
    · exact absurd hzero hb
    · have h_abs_eq : |b| = b := abs_of_pos hpos
      have h_hi' : r < b := by rw [← h_abs_eq]; exact h_hi
      have h_sum : r + b * q = a := by linarith
      exact (Int.ediv_emod_unique hpos).mpr ⟨h_sum, h_lo, h_hi'⟩

/-- Generalized floor uniqueness: `r` has the sign of `b` (or is zero) and `|r| < |b|`. -/
private lemma fdiv_fmod_unique_general {a b q r : Int}
    (h_id : q * b + r = a)
    (h_pos : 0 < b → 0 ≤ r ∧ r < b)
    (h_neg : b < 0 → b < r ∧ r ≤ 0)
    (h_b_zero : b = 0 → q = 0 ∧ r = a) :
    a.fdiv b = q ∧ a.fmod b = r := by
  by_cases hb : b = 0
  · rw [hb, Int.fdiv_zero, Int.fmod_zero]
    obtain ⟨hq, hr⟩ := h_b_zero hb
    exact ⟨hq.symm, hr.symm⟩
  · rcases lt_or_gt_of_ne hb with hneg | hpos
    · -- b < 0
      obtain ⟨hr_lo, hr_hi⟩ := h_neg hneg
      by_cases h_dvd : b ∣ a
      · -- b ∣ a ⇒ r = 0
        have h_dvd_r : b ∣ r := by
          have h_eq : r = a - q * b := by linarith
          rw [h_eq]; exact h_dvd.sub ⟨q, by ring⟩
        have h_r_zero : r = 0 := by
          have h_negb_dvd : -b ∣ r := Int.neg_dvd.mpr h_dvd_r
          have h_abs : |r| < -b := by rw [abs_of_nonpos hr_hi]; linarith
          exact Int.eq_zero_of_abs_lt_dvd h_negb_dvd h_abs
        subst h_r_zero
        have h_npos : (0 : Int) < -b := by linarith
        have h_sum : (0 : Int) + (-b) * (-q) = a := by linarith
        obtain ⟨he_d, he_m⟩ := (Int.ediv_emod_unique h_npos).mpr
          ⟨h_sum, le_refl 0, h_npos⟩
        have ha_div : a / b = q := by
          have h1 : a / -b = -q := he_d
          rw [Int.ediv_neg] at h1
          linarith
        have ha_mod : a % b = 0 := (Int.emod_neg a b).symm.trans he_m
        refine ⟨?_, ?_⟩
        · rw [Int.fdiv_eq_ediv]; simp [h_dvd, ha_div]
        · rw [Int.fmod_eq_emod]; simp [h_dvd, ha_mod]
      · -- ¬ b ∣ a ⇒ r ≠ 0
        have hr_ne : r ≠ 0 := by
          intro h; subst h
          exact h_dvd ⟨q, by linarith [mul_comm q b]⟩
        have hr_neg : r < 0 := lt_of_le_of_ne hr_hi hr_ne
        have h_npos : (0 : Int) < -b := by linarith
        have h_re_lo : (0 : Int) ≤ r - b := by linarith
        have h_re_hi : r - b < -b := by linarith
        have h_sum : (r - b) + (-b) * (-(q+1)) = a := by ring_nf; linarith
        obtain ⟨he_d, he_m⟩ := (Int.ediv_emod_unique h_npos).mpr
          ⟨h_sum, h_re_lo, h_re_hi⟩
        have ha_div : a / b = q + 1 := by
          have h1 : a / -b = -(q+1) := he_d
          rw [Int.ediv_neg] at h1
          linarith
        have ha_mod : a % b = r - b := (Int.emod_neg a b).symm.trans he_m
        have h_cond : ¬ (0 ≤ b ∨ b ∣ a) := by
          rintro (h | h)
          · linarith
          · exact h_dvd h
        refine ⟨?_, ?_⟩
        · rw [Int.fdiv_eq_ediv]; simp [h_cond]; linarith
        · rw [Int.fmod_eq_emod]; simp [h_cond]; linarith
    · -- b > 0
      obtain ⟨hr_lo, hr_hi⟩ := h_pos hpos
      have h_sum : r + b * q = a := by linarith
      obtain ⟨hd, hm⟩ := (Int.ediv_emod_unique hpos).mpr ⟨h_sum, hr_lo, hr_hi⟩
      have h_fd : a.fdiv b = a / b := by
        rw [Int.fdiv_eq_ediv]; simp [le_of_lt hpos]
      have h_fm : a.fmod b = a % b := by
        rw [Int.fmod_eq_emod]; simp [le_of_lt hpos]
      exact ⟨h_fd.trans hd, h_fm.trans hm⟩

/-! ### Main correctness theorem for `edivMod`. -/

set_option maxHeartbeats 1600000 in
/-- `AzInt.edivMod` matches Lean's Euclidean `Int / ` and `Int %`. -/
theorem toInt_edivMod (a b : AzInt) :
    (a.edivMod b).1.toInt = a.toInt / b.toInt ∧
    (a.edivMod b).2.toInt = a.toInt % b.toInt := by
  -- Bridge to Nat-level facts about divMod.
  have h_qq_n : (a.abs.divMod b.abs).1.toNat = a.abs.toNat / b.abs.toNat := by
    rw [← AzNat.div_eq_divMod_fst]
    show (a.abs / b.abs).toNat = _; exact AzNat.toNat_div _ _
  have h_qr_n : (a.abs.divMod b.abs).2.toNat = a.abs.toNat % b.abs.toNat := by
    rw [← AzNat.mod_eq_divMod_snd]
    show (a.abs % b.abs).toNat = _; exact AzNat.toNat_mod _ _
  have h_id_nat : (a.abs.divMod b.abs).1.toNat * b.abs.toNat + (a.abs.divMod b.abs).2.toNat
      = a.abs.toNat := (AzNat.divMod_toNat a.abs b.abs).1
  have h_bnd : b.abs.toNat ≠ 0 →
      (a.abs.divMod b.abs).2.toNat < b.abs.toNat :=
    (AzNat.divMod_toNat a.abs b.abs).2
  have h_id_int : ((a.abs.divMod b.abs).1.toNat : Int) * (b.abs.toNat : Int)
      + ((a.abs.divMod b.abs).2.toNat : Int) = (a.abs.toNat : Int) := by
    exact_mod_cast h_id_nat
  -- Sign decomposition.
  have h_a_int : a.toInt = if a.sign then (a.abs.toNat : Int) else -(a.abs.toNat : Int) := rfl
  have h_b_int : b.toInt = if b.sign then (b.abs.toNat : Int) else -(b.abs.toNat : Int) := rfl
  have h_abs_b : |b.toInt| = (b.abs.toNat : Int) := abs_toInt b
  have h_b_zero_iff : b.toInt = 0 ↔ b.abs.toNat = 0 := toInt_eq_zero_iff_abs_toNat_eq_zero b
  -- Suffice to find q, r satisfying uniqueness conditions.
  suffices h : ∃ q r : Int,
      (a.edivMod b).1.toInt = q ∧ (a.edivMod b).2.toInt = r ∧
      q * b.toInt + r = a.toInt ∧
      (b.toInt ≠ 0 → 0 ≤ r ∧ r < |b.toInt|) ∧
      (b.toInt = 0 → q = 0 ∧ r = a.toInt) by
    obtain ⟨q, r, h1, h2, h_id, h_nonzero, h_zero⟩ := h
    obtain ⟨hd, hm⟩ := ediv_emod_unique_general h_id h_nonzero h_zero
    exact ⟨h1.trans hd.symm, h2.trans hm.symm⟩
  unfold edivMod
  by_cases hsa : a.sign = true
  · -- a.sign = true
    have h_a_pos : a.toInt = ((a.abs.toNat : Int)) := by rw [h_a_int, hsa]; simp
    simp only [hsa, ↓reduceIte]
    by_cases hsb : b.sign = true
    · -- AT: a.sign = true, b.sign = true
      have h_b_pos : b.toInt = ((b.abs.toNat : Int)) := by rw [h_b_int, hsb]; simp
      have h_beq : (true == b.sign) = true := by rw [hsb]; rfl
      refine ⟨((a.abs.divMod b.abs).1.toNat : Int),
              ((a.abs.divMod b.abs).2.toNat : Int), ?_, ?_, ?_, ?_, ?_⟩
      · rw [toInt_mkNorm, h_beq]; simp
      · rw [AzNat.toInt_toAzInt]
      · rw [h_a_pos, h_b_pos]; exact_mod_cast h_id_nat
      · intro h_b_ne
        have hbn : b.abs.toNat ≠ 0 := fun h => h_b_ne (h_b_zero_iff.mpr h)
        rw [h_abs_b]
        refine ⟨by exact_mod_cast Nat.zero_le _, by exact_mod_cast h_bnd hbn⟩
      · intro hbz
        have hbn : b.abs.toNat = 0 := h_b_zero_iff.mp hbz
        have h_qq0 : (a.abs.divMod b.abs).1.toNat = 0 := by rw [h_qq_n, hbn]; simp
        have h_qr_eq : (a.abs.divMod b.abs).2.toNat = a.abs.toNat := by rw [h_qr_n, hbn]; simp
        exact ⟨by exact_mod_cast h_qq0, by rw [h_qr_eq, h_a_pos]⟩
    · -- AF: a.sign = true, b.sign = false
      have hsb_f : b.sign = false := Bool.eq_false_iff.mpr hsb
      have h_b_neg : b.toInt = -((b.abs.toNat : Int)) := by rw [h_b_int, hsb_f]; simp
      have hbn : b.abs.toNat ≠ 0 := by
        intro h0
        have hb_ne : b.abs ≠ 0 := abs_ne_zero_of_sign_false hsb_f
        exact hb_ne (AzNat.toNat_injective (h0.trans AzNat.toNat_zero.symm))
      have h_beq : (true == b.sign) = false := by rw [hsb_f]; rfl
      have h_b_ne : b.toInt ≠ 0 := by rw [h_b_neg]; intro h; omega
      refine ⟨-((a.abs.divMod b.abs).1.toNat : Int),
              ((a.abs.divMod b.abs).2.toNat : Int), ?_, ?_, ?_, ?_, ?_⟩
      · rw [toInt_mkNorm, h_beq]; simp
      · rw [AzNat.toInt_toAzInt]
      · rw [h_a_pos, h_b_neg]
        have h_neg : -((a.abs.divMod b.abs).1.toNat : Int) * -((b.abs.toNat : Int))
            = ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int)) := by ring
        linarith [h_id_int]
      · intro _
        rw [h_abs_b]
        refine ⟨by exact_mod_cast Nat.zero_le _, by exact_mod_cast h_bnd hbn⟩
      · intro hbz; exact absurd hbz h_b_ne
  · -- a.sign = false
    have hsa_f : a.sign = false := Bool.eq_false_iff.mpr hsa
    have ha_ne : a.abs ≠ 0 := abs_ne_zero_of_sign_false hsa_f
    have han : a.abs.toNat ≠ 0 := fun h =>
      ha_ne (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have h_a_neg : a.toInt = -((a.abs.toNat : Int)) := by rw [h_a_int, hsa_f]; simp
    simp only [hsa, Bool.false_eq_true, ↓reduceIte]
    by_cases hr0 : (a.abs.divMod b.abs).2 = 0
    · -- B1: r' = 0
      simp only [hr0, ↓reduceDIte]
      have h_qr0 : (a.abs.divMod b.abs).2.toNat = 0 := by rw [hr0]; rfl
      have h_id0 : (a.abs.divMod b.abs).1.toNat * b.abs.toNat = a.abs.toNat := by
        have := h_id_nat; rw [h_qr0] at this; omega
      have hbn : b.abs.toNat ≠ 0 := by
        intro h; rw [h, Nat.mul_zero] at h_id0; exact han h_id0.symm
      have h_mkNorm_F0 : (mkNorm false (0 : AzNat)).toInt = 0 := by
        rw [toInt_mkNorm, AzNat.toNat_zero]; simp
      by_cases hsb : b.sign = true
      · -- B1T: a.sign=F, b.sign=T
        have h_b_pos : b.toInt = ((b.abs.toNat : Int)) := by rw [h_b_int, hsb]; simp
        have h_beq : (false == b.sign) = false := by rw [hsb]; rfl
        have h_b_ne : b.toInt ≠ 0 := by rw [h_b_pos]; intro h; omega
        refine ⟨-((a.abs.divMod b.abs).1.toNat : Int), 0, ?_, ?_, ?_, ?_, ?_⟩
        · rw [toInt_mkNorm, h_beq]; simp
        · exact h_mkNorm_F0
        · rw [h_a_neg, h_b_pos]
          have hcast : ((a.abs.divMod b.abs).1.toNat * b.abs.toNat : Nat)
              = ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int)) := by push_cast; ring
          have : -((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))
              = -(((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))) := by ring
          rw [this]
          have h_id0_int : ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))
              = (a.abs.toNat : Int) := by exact_mod_cast h_id0
          rw [h_id0_int]; ring
        · intro _
          rw [h_abs_b]
          refine ⟨le_refl 0, ?_⟩
          exact_mod_cast Nat.pos_of_ne_zero hbn
        · intro hbz; exact absurd hbz h_b_ne
      · -- B1F: a.sign=F, b.sign=F
        have hsb_f : b.sign = false := Bool.eq_false_iff.mpr hsb
        have h_b_neg : b.toInt = -((b.abs.toNat : Int)) := by rw [h_b_int, hsb_f]; simp
        have h_beq : (false == b.sign) = true := by rw [hsb_f]; rfl
        have h_b_ne : b.toInt ≠ 0 := by rw [h_b_neg]; intro h; omega
        refine ⟨((a.abs.divMod b.abs).1.toNat : Int), 0, ?_, ?_, ?_, ?_, ?_⟩
        · rw [toInt_mkNorm, h_beq]; simp
        · exact h_mkNorm_F0
        · rw [h_a_neg, h_b_neg]
          have h_id0_int : ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))
              = (a.abs.toNat : Int) := by exact_mod_cast h_id0
          have : ((a.abs.divMod b.abs).1.toNat : Int) * (-((b.abs.toNat : Int)))
              = -(((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))) := by ring
          rw [this, h_id0_int]; ring
        · intro _
          rw [h_abs_b]
          refine ⟨le_refl 0, ?_⟩
          exact_mod_cast Nat.pos_of_ne_zero hbn
        · intro hbz; exact absurd hbz h_b_ne
    · -- r' ≠ 0
      simp only [hr0, ↓reduceDIte]
      by_cases hBzero : b.abs = 0
      · -- B2: a.sign=F, r'≠0, b.abs = 0
        rw [dite_eq_left hBzero]
        have hqb0 : b.abs.toNat = 0 := by rw [hBzero]; rfl
        have hb_sign : b.sign = true := b.zero_sign hBzero
        have h_btoint_zero : b.toInt = 0 := h_b_zero_iff.mpr hqb0
        have h_qq0 : (a.abs.divMod b.abs).1.toNat = 0 := by rw [h_qq_n, hqb0]; simp
        have h_qr_eq : (a.abs.divMod b.abs).2.toNat = a.abs.toNat := by rw [h_qr_n, hqb0]; simp
        have h_beq : (false == b.sign) = false := by rw [hb_sign]; rfl
        refine ⟨0, -((a.abs.toNat : Int)), ?_, ?_, ?_, ?_, ?_⟩
        · rw [toInt_mkNorm, h_beq]; simp [h_qq0]
        · rw [toInt_mkNonzero]; simp [h_qr_eq]
        · rw [h_btoint_zero, h_a_neg]; ring
        · intro hb_ne; exact absurd h_btoint_zero hb_ne
        · intro _
          refine ⟨rfl, ?_⟩
          rw [h_a_neg]
      · -- B3: a.sign=F, r'≠0, b.abs ≠ 0
        rw [dite_eq_right hBzero]
        have hbn : b.abs.toNat ≠ 0 := by
          intro h; apply hBzero; apply AzNat.toNat_injective
          rw [h, AzNat.toNat_zero]
        have hrlt : (a.abs.divMod b.abs).2.toNat < b.abs.toNat := h_bnd hbn
        have hqr_pos : (a.abs.divMod b.abs).2.toNat ≠ 0 := by
          intro h
          apply hr0
          apply AzNat.toNat_injective
          rw [h, AzNat.toNat_zero]
        have hle : (a.abs.divMod b.abs).2.toNat ≤ b.abs.toNat := le_of_lt hrlt
        by_cases hsb : b.sign = true
        · -- B3T: a.sign=F, b.sign=T
          have h_b_pos : b.toInt = ((b.abs.toNat : Int)) := by rw [h_b_int, hsb]; simp
          have h_b_ne : b.toInt ≠ 0 := by rw [h_b_pos]; intro h; omega
          have h_notb : (!b.sign) = false := by rw [hsb]; rfl
          refine ⟨-(((a.abs.divMod b.abs).1.toNat : Int) + 1),
                  ((b.abs.toNat : Int) - ((a.abs.divMod b.abs).2.toNat : Int)),
                  ?_, ?_, ?_, ?_, ?_⟩
          · rw [toInt_mkNonzero, h_notb]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [AzNat.toNat_addUInt64]
            push_cast; ring
          · rw [toInt_mkNonzero_true, AzNat.toNat_sub, Nat.cast_sub hle]
          · rw [h_a_neg, h_b_pos]
            have h_id0_int : ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))
                + ((a.abs.divMod b.abs).2.toNat : Int) = (a.abs.toNat : Int) := h_id_int
            linarith
          · intro _
            rw [h_abs_b]
            have hqr_pos_int : (0 : Int) < ((a.abs.divMod b.abs).2.toNat : Int) :=
              Int.natCast_pos.mpr (Nat.pos_of_ne_zero hqr_pos)
            have hrlt_int : ((a.abs.divMod b.abs).2.toNat : Int) < (b.abs.toNat : Int) := by
              exact_mod_cast hrlt
            exact ⟨by linarith, by linarith⟩
          · intro hbz; exact absurd hbz h_b_ne
        · -- B3F: a.sign=F, b.sign=F
          have hsb_f : b.sign = false := Bool.eq_false_iff.mpr hsb
          have h_b_neg : b.toInt = -((b.abs.toNat : Int)) := by rw [h_b_int, hsb_f]; simp
          have h_b_ne : b.toInt ≠ 0 := by rw [h_b_neg]; intro h; omega
          have h_notb : (!b.sign) = true := by rw [hsb_f]; rfl
          refine ⟨((a.abs.divMod b.abs).1.toNat : Int) + 1,
                  ((b.abs.toNat : Int) - ((a.abs.divMod b.abs).2.toNat : Int)),
                  ?_, ?_, ?_, ?_, ?_⟩
          · rw [toInt_mkNonzero, h_notb]
            simp only [↓reduceIte]
            rw [AzNat.toNat_addUInt64]
            push_cast; ring
          · rw [toInt_mkNonzero_true, AzNat.toNat_sub, Nat.cast_sub hle]
          · rw [h_a_neg, h_b_neg]
            have h_id0_int : ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))
                + ((a.abs.divMod b.abs).2.toNat : Int) = (a.abs.toNat : Int) := h_id_int
            linarith
          · intro _
            rw [h_abs_b]
            have hqr_pos_int : (0 : Int) < ((a.abs.divMod b.abs).2.toNat : Int) :=
              Int.natCast_pos.mpr (Nat.pos_of_ne_zero hqr_pos)
            have hrlt_int : ((a.abs.divMod b.abs).2.toNat : Int) < (b.abs.toNat : Int) := by
              exact_mod_cast hrlt
            exact ⟨by linarith, by linarith⟩
          · intro hbz; exact absurd hbz h_b_ne

/-- The specialised `AzInt.ediv` agrees with the first projection of
    `edivMod`.  Mirrors `AzNat.div_eq_divMod_fst`: `ediv` shares
    `edivMod`'s outer dispatch but skips the remainder-side AzInt
    construction in each branch. -/
theorem ediv_eq_edivMod_fst (a b : AzInt) : a.ediv b = (a.edivMod b).1 := by
  unfold AzInt.ediv AzInt.edivMod
  simp only [apply_ite Prod.fst, apply_dite Prod.fst]

/-- The specialised `AzInt.emod` agrees with the second projection of
    `edivMod`.  Mirrors `AzNat.mod_eq_divMod_snd`: `emod` shares
    `edivMod`'s outer dispatch but skips the quotient-side AzInt
    construction in each branch. -/
theorem emod_eq_edivMod_snd (a b : AzInt) : a.emod b = (a.edivMod b).2 := by
  unfold AzInt.emod AzInt.edivMod
  simp only [apply_ite Prod.snd, apply_dite Prod.snd]

/-- Correctness of `AzInt.ediv`. -/
theorem toInt_ediv (a b : AzInt) : (a.ediv b).toInt = a.toInt / b.toInt := by
  rw [ediv_eq_edivMod_fst]; exact (toInt_edivMod a b).1

/-- Correctness of `AzInt.emod`. -/
theorem toInt_emod (a b : AzInt) : (a.emod b).toInt = a.toInt % b.toInt := by
  rw [emod_eq_edivMod_snd]; exact (toInt_edivMod a b).2

/-- `AzInt.divMod = AzInt.edivMod`, so it inherits the same correctness. -/
theorem toInt_divMod (a b : AzInt) :
    (a.divMod b).1.toInt = a.toInt / b.toInt ∧
    (a.divMod b).2.toInt = a.toInt % b.toInt :=
  toInt_edivMod a b

/-- Correctness of `AzInt.div`. -/
theorem toInt_div (a b : AzInt) : (a.div b).toInt = a.toInt / b.toInt := toInt_ediv a b

/-- Correctness of `AzInt.mod`. -/
theorem toInt_mod (a b : AzInt) : (a.mod b).toInt = a.toInt % b.toInt := toInt_emod a b

/-- `(/)` on `AzInt` is `Int.ediv`. -/
@[simp] theorem toInt_hDiv (a b : AzInt) : (a / b).toInt = a.toInt / b.toInt := toInt_div a b

/-- `(%)` on `AzInt` is `Int.emod`. -/
@[simp] theorem toInt_hMod (a b : AzInt) : (a % b).toInt = a.toInt % b.toInt := toInt_mod a b

/-- `ofInt`-version of `toInt_ediv`. -/
theorem ofInt_ediv (i j : Int) : ofInt (i / j) = (ofInt i).ediv (ofInt j) := by
  have h : (ofInt (i / j)).toInt = ((ofInt i).ediv (ofInt j)).toInt := by
    rw [toInt_ofInt, toInt_ediv, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- `ofInt`-version of `toInt_emod`. -/
theorem ofInt_emod (i j : Int) : ofInt (i % j) = (ofInt i).emod (ofInt j) := by
  have h : (ofInt (i % j)).toInt = ((ofInt i).emod (ofInt j)).toInt := by
    rw [toInt_ofInt, toInt_emod, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- `ofInt`-version of `toInt_div`. -/
theorem ofInt_div (i j : Int) : ofInt (i / j) = (ofInt i).div (ofInt j) := ofInt_ediv i j

/-- `ofInt`-version of `toInt_mod`. -/
theorem ofInt_mod (i j : Int) : ofInt (i % j) = (ofInt i).mod (ofInt j) := ofInt_emod i j

/-! ### Main correctness theorem for `fdivMod`. -/

set_option maxHeartbeats 1600000 in
/-- `AzInt.fdivMod` matches Lean's floor `Int.fdiv`/`Int.fmod`. -/
theorem toInt_fdivMod (a b : AzInt) :
    (a.fdivMod b).1.toInt = a.toInt.fdiv b.toInt ∧
    (a.fdivMod b).2.toInt = a.toInt.fmod b.toInt := by
  have h_qq_n : (a.abs.divMod b.abs).1.toNat = a.abs.toNat / b.abs.toNat := by
    rw [← AzNat.div_eq_divMod_fst]
    show (a.abs / b.abs).toNat = _; exact AzNat.toNat_div _ _
  have h_qr_n : (a.abs.divMod b.abs).2.toNat = a.abs.toNat % b.abs.toNat := by
    rw [← AzNat.mod_eq_divMod_snd]
    show (a.abs % b.abs).toNat = _; exact AzNat.toNat_mod _ _
  have h_id_nat : (a.abs.divMod b.abs).1.toNat * b.abs.toNat + (a.abs.divMod b.abs).2.toNat
      = a.abs.toNat := (AzNat.divMod_toNat a.abs b.abs).1
  have h_bnd : b.abs.toNat ≠ 0 →
      (a.abs.divMod b.abs).2.toNat < b.abs.toNat :=
    (AzNat.divMod_toNat a.abs b.abs).2
  have h_id_int : ((a.abs.divMod b.abs).1.toNat : Int) * (b.abs.toNat : Int)
      + ((a.abs.divMod b.abs).2.toNat : Int) = (a.abs.toNat : Int) := by
    exact_mod_cast h_id_nat
  have h_a_int : a.toInt = if a.sign then (a.abs.toNat : Int) else -(a.abs.toNat : Int) := rfl
  have h_b_int : b.toInt = if b.sign then (b.abs.toNat : Int) else -(b.abs.toNat : Int) := rfl
  have h_b_zero_iff : b.toInt = 0 ↔ b.abs.toNat = 0 := toInt_eq_zero_iff_abs_toNat_eq_zero b
  suffices h : ∃ q r : Int,
      (a.fdivMod b).1.toInt = q ∧ (a.fdivMod b).2.toInt = r ∧
      q * b.toInt + r = a.toInt ∧
      (0 < b.toInt → 0 ≤ r ∧ r < b.toInt) ∧
      (b.toInt < 0 → b.toInt < r ∧ r ≤ 0) ∧
      (b.toInt = 0 → q = 0 ∧ r = a.toInt) by
    obtain ⟨q, r, h1, h2, h_id, h_pos, h_neg, h_zero⟩ := h
    obtain ⟨hd, hm⟩ := fdiv_fmod_unique_general h_id h_pos h_neg h_zero
    exact ⟨h1.trans hd.symm, h2.trans hm.symm⟩
  unfold fdivMod
  by_cases hsa : a.sign = true
  · have h_a_pos : a.toInt = ((a.abs.toNat : Int)) := by rw [h_a_int, hsa]; simp
    by_cases hsb : b.sign = true
    · -- TT
      have h_b_pos : b.toInt = ((b.abs.toNat : Int)) := by rw [h_b_int, hsb]; simp
      have h_seq : (a.sign == b.sign) = true := by rw [hsa, hsb]; rfl
      simp only [h_seq, ↓reduceIte]
      refine ⟨((a.abs.divMod b.abs).1.toNat : Int),
              ((a.abs.divMod b.abs).2.toNat : Int), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [AzNat.toInt_toAzInt]
      · rw [toInt_mkNorm, hsa]; simp
      · rw [h_a_pos, h_b_pos]; exact_mod_cast h_id_nat
      · intro h_b_pos_int
        have hbn : b.abs.toNat ≠ 0 := by
          rw [h_b_pos] at h_b_pos_int; intro h; rw [h] at h_b_pos_int; simp at h_b_pos_int
        rw [h_b_pos]
        refine ⟨by exact_mod_cast Nat.zero_le _, by exact_mod_cast h_bnd hbn⟩
      · intro h_b_neg_int
        rw [h_b_pos] at h_b_neg_int
        have : (b.abs.toNat : Int) ≥ 0 := by exact_mod_cast Nat.zero_le _
        linarith
      · intro hbz
        rw [h_b_pos] at hbz
        have hbn : b.abs.toNat = 0 := by exact_mod_cast hbz
        have h_qq0 : (a.abs.divMod b.abs).1.toNat = 0 := by rw [h_qq_n, hbn]; simp
        have h_qr_eq : (a.abs.divMod b.abs).2.toNat = a.abs.toNat := by rw [h_qr_n, hbn]; simp
        refine ⟨by exact_mod_cast h_qq0, ?_⟩
        rw [h_a_pos]; exact_mod_cast h_qr_eq
    · -- TF
      have hsb_f : b.sign = false := Bool.eq_false_iff.mpr hsb
      have h_b_neg : b.toInt = -((b.abs.toNat : Int)) := by rw [h_b_int, hsb_f]; simp
      have hbn : b.abs.toNat ≠ 0 := by
        intro h0
        have hb_ne : b.abs ≠ 0 := abs_ne_zero_of_sign_false hsb_f
        exact hb_ne (AzNat.toNat_injective (h0.trans AzNat.toNat_zero.symm))
      have h_b_neg_pos : b.toInt < 0 := by
        rw [h_b_neg]; have : (0 : Int) < (b.abs.toNat : Int) := by
          exact_mod_cast Nat.pos_of_ne_zero hbn
        linarith
      have h_b_ne : b.toInt ≠ 0 := ne_of_lt h_b_neg_pos
      have h_seq : (a.sign == b.sign) = false := by rw [hsa, hsb_f]; rfl
      simp only [h_seq, Bool.false_eq_true, ↓reduceIte]
      by_cases hr0 : (a.abs.divMod b.abs).2 = 0
      · -- TF, r' = 0
        simp only [hr0, ↓reduceDIte]
        have h_qr0 : (a.abs.divMod b.abs).2.toNat = 0 := by rw [hr0]; rfl
        have h_id0 : (a.abs.divMod b.abs).1.toNat * b.abs.toNat = a.abs.toNat := by
          have := h_id_nat; rw [h_qr0] at this; omega
        refine ⟨-((a.abs.divMod b.abs).1.toNat : Int), 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [toInt_mkNorm]; simp
        · rw [toInt_mkNorm, hsa]; simp
        · rw [h_a_pos, h_b_neg]
          have h_id0_int : ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))
              = (a.abs.toNat : Int) := by exact_mod_cast h_id0
          linarith
        · intro h_p; linarith
        · intro _; exact ⟨h_b_neg_pos, le_refl 0⟩
        · intro hbz; exact absurd hbz h_b_ne
      · -- TF, r' ≠ 0
        simp only [hr0, ↓reduceDIte]
        have hBzero : ¬ b.abs = 0 := by
          intro h; apply hbn; rw [h]; rfl
        rw [dite_eq_right hBzero]
        have hrlt : (a.abs.divMod b.abs).2.toNat < b.abs.toNat := h_bnd hbn
        have hqr_pos : (a.abs.divMod b.abs).2.toNat ≠ 0 := by
          intro h; apply hr0; apply AzNat.toNat_injective
          rw [h, AzNat.toNat_zero]
        have hle : (a.abs.divMod b.abs).2.toNat ≤ b.abs.toNat := le_of_lt hrlt
        refine ⟨-(((a.abs.divMod b.abs).1.toNat : Int) + 1),
                (((a.abs.divMod b.abs).2.toNat : Int) - (b.abs.toNat : Int)),
                ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [toInt_mkNonzero, Bool.false_eq_true, ↓reduceIte]
          rw [AzNat.toNat_addUInt64]
          push_cast; ring
        · simp only [toInt_mkNonzero, hsb_f, Bool.false_eq_true, ↓reduceIte]
          rw [AzNat.toNat_sub, Nat.cast_sub hle]
          ring
        · rw [h_a_pos, h_b_neg]
          have h_id0_int : ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))
              + ((a.abs.divMod b.abs).2.toNat : Int) = (a.abs.toNat : Int) := h_id_int
          linarith
        · intro h_p; linarith
        · intro _
          have hqr_pos_int : (0 : Int) < ((a.abs.divMod b.abs).2.toNat : Int) :=
            Int.natCast_pos.mpr (Nat.pos_of_ne_zero hqr_pos)
          have hrlt_int : ((a.abs.divMod b.abs).2.toNat : Int) < (b.abs.toNat : Int) := by
            exact_mod_cast hrlt
          refine ⟨?_, ?_⟩
          · rw [h_b_neg]; linarith
          · linarith
        · intro hbz; exact absurd hbz h_b_ne
  · -- a.sign = false
    have hsa_f : a.sign = false := Bool.eq_false_iff.mpr hsa
    have ha_ne : a.abs ≠ 0 := abs_ne_zero_of_sign_false hsa_f
    have han : a.abs.toNat ≠ 0 := fun h =>
      ha_ne (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have h_a_neg : a.toInt = -((a.abs.toNat : Int)) := by rw [h_a_int, hsa_f]; simp
    by_cases hsb : b.sign = true
    · -- FT
      have h_b_pos : b.toInt = ((b.abs.toNat : Int)) := by rw [h_b_int, hsb]; simp
      have h_seq : (a.sign == b.sign) = false := by rw [hsa_f, hsb]; rfl
      simp only [h_seq, Bool.false_eq_true, ↓reduceIte]
      by_cases hr0 : (a.abs.divMod b.abs).2 = 0
      · -- FT, r' = 0
        simp only [hr0, ↓reduceDIte]
        have h_qr0 : (a.abs.divMod b.abs).2.toNat = 0 := by rw [hr0]; rfl
        have h_id0 : (a.abs.divMod b.abs).1.toNat * b.abs.toNat = a.abs.toNat := by
          have := h_id_nat; rw [h_qr0] at this; omega
        have hbn : b.abs.toNat ≠ 0 := by
          intro h; rw [h, Nat.mul_zero] at h_id0; exact han h_id0.symm
        have h_b_pos_pos : 0 < b.toInt := by
          rw [h_b_pos]; exact_mod_cast Nat.pos_of_ne_zero hbn
        have h_b_ne : b.toInt ≠ 0 := ne_of_gt h_b_pos_pos
        refine ⟨-((a.abs.divMod b.abs).1.toNat : Int), 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [toInt_mkNorm]; simp
        · rw [toInt_mkNorm, hsa_f]; simp
        · rw [h_a_neg, h_b_pos]
          have h_id0_int : ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))
              = (a.abs.toNat : Int) := by exact_mod_cast h_id0
          linarith
        · intro _; exact ⟨le_refl 0, h_b_pos_pos⟩
        · intro h_n; linarith
        · intro hbz; exact absurd hbz h_b_ne
      · -- FT, r' ≠ 0
        simp only [hr0, ↓reduceDIte]
        by_cases hBzero : b.abs = 0
        · rw [dite_eq_left hBzero]
          have hqb0 : b.abs.toNat = 0 := by rw [hBzero]; rfl
          have h_btoint_zero : b.toInt = 0 := h_b_zero_iff.mpr hqb0
          have h_qq0 : (a.abs.divMod b.abs).1.toNat = 0 := by rw [h_qq_n, hqb0]; simp
          have h_qr_eq : (a.abs.divMod b.abs).2.toNat = a.abs.toNat := by rw [h_qr_n, hqb0]; simp
          refine ⟨0, -((a.abs.toNat : Int)), ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [toInt_mkNorm]; simp [h_qq0]
          · rw [toInt_mkNonzero, hsa_f]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [h_qr_eq]
          · rw [h_btoint_zero, h_a_neg]; ring
          · intro h_p; rw [h_btoint_zero] at h_p; exact absurd h_p (lt_irrefl _)
          · intro h_n; rw [h_btoint_zero] at h_n; exact absurd h_n (lt_irrefl _)
          · intro _; refine ⟨rfl, ?_⟩; rw [h_a_neg]
        · rw [dite_eq_right hBzero]
          have hbn : b.abs.toNat ≠ 0 := by
            intro h; apply hBzero; apply AzNat.toNat_injective
            rw [h, AzNat.toNat_zero]
          have hrlt : (a.abs.divMod b.abs).2.toNat < b.abs.toNat := h_bnd hbn
          have hqr_pos : (a.abs.divMod b.abs).2.toNat ≠ 0 := by
            intro h; apply hr0; apply AzNat.toNat_injective
            rw [h, AzNat.toNat_zero]
          have hle : (a.abs.divMod b.abs).2.toNat ≤ b.abs.toNat := le_of_lt hrlt
          have h_b_pos_pos : 0 < b.toInt := by
            rw [h_b_pos]; exact_mod_cast Nat.pos_of_ne_zero hbn
          have h_b_ne : b.toInt ≠ 0 := ne_of_gt h_b_pos_pos
          refine ⟨-(((a.abs.divMod b.abs).1.toNat : Int) + 1),
                  ((b.abs.toNat : Int) - ((a.abs.divMod b.abs).2.toNat : Int)),
                  ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [toInt_mkNonzero, Bool.false_eq_true, ↓reduceIte]
            rw [AzNat.toNat_addUInt64]
            push_cast; ring
          · simp only [toInt_mkNonzero, hsb, ↓reduceIte]
            rw [AzNat.toNat_sub, Nat.cast_sub hle]
          · rw [h_a_neg, h_b_pos]
            have h_id0_int : ((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))
                + ((a.abs.divMod b.abs).2.toNat : Int) = (a.abs.toNat : Int) := h_id_int
            linarith
          · intro _
            have hqr_pos_int : (0 : Int) < ((a.abs.divMod b.abs).2.toNat : Int) :=
              Int.natCast_pos.mpr (Nat.pos_of_ne_zero hqr_pos)
            have hrlt_int : ((a.abs.divMod b.abs).2.toNat : Int) < (b.abs.toNat : Int) := by
              exact_mod_cast hrlt
            refine ⟨by linarith, ?_⟩
            rw [h_b_pos]; linarith
          · intro h_n; linarith
          · intro hbz; exact absurd hbz h_b_ne
    · -- FF
      have hsb_f : b.sign = false := Bool.eq_false_iff.mpr hsb
      have h_b_neg : b.toInt = -((b.abs.toNat : Int)) := by rw [h_b_int, hsb_f]; simp
      have hbn : b.abs.toNat ≠ 0 := by
        intro h0
        have hb_ne : b.abs ≠ 0 := abs_ne_zero_of_sign_false hsb_f
        exact hb_ne (AzNat.toNat_injective (h0.trans AzNat.toNat_zero.symm))
      have h_b_neg_pos : b.toInt < 0 := by
        rw [h_b_neg]; have : (0 : Int) < (b.abs.toNat : Int) := by
          exact_mod_cast Nat.pos_of_ne_zero hbn
        linarith
      have h_seq : (a.sign == b.sign) = true := by rw [hsa_f, hsb_f]; rfl
      simp only [h_seq, ↓reduceIte]
      refine ⟨((a.abs.divMod b.abs).1.toNat : Int),
              -((a.abs.divMod b.abs).2.toNat : Int), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [AzNat.toInt_toAzInt]
      · rw [toInt_mkNorm, hsa_f]; simp
      · rw [h_a_neg, h_b_neg]
        have : ((a.abs.divMod b.abs).1.toNat : Int) * (-((b.abs.toNat : Int)))
            = -(((a.abs.divMod b.abs).1.toNat : Int) * ((b.abs.toNat : Int))) := by ring
        rw [this]
        linarith [h_id_int]
      · intro h_p; linarith
      · intro _
        refine ⟨?_, ?_⟩
        · rw [h_b_neg]
          have hrlt : (a.abs.divMod b.abs).2.toNat < b.abs.toNat := h_bnd hbn
          have hrlt_int : ((a.abs.divMod b.abs).2.toNat : Int) < (b.abs.toNat : Int) := by
            exact_mod_cast hrlt
          linarith
        · have : (0 : Int) ≤ ((a.abs.divMod b.abs).2.toNat : Int) := by
            exact_mod_cast Nat.zero_le _
          linarith
      · intro hbz; rw [h_b_neg] at hbz
        have : (b.abs.toNat : Int) = 0 := by linarith
        exact absurd (by exact_mod_cast this : b.abs.toNat = 0) hbn

/-- Correctness of `AzInt.fdiv`. -/
theorem toInt_fdiv (a b : AzInt) : (a.fdiv b).toInt = a.toInt.fdiv b.toInt :=
  (toInt_fdivMod a b).1

/-- Correctness of `AzInt.fmod`. -/
theorem toInt_fmod (a b : AzInt) : (a.fmod b).toInt = a.toInt.fmod b.toInt :=
  (toInt_fdivMod a b).2

/-- `ofInt`-version of `toInt_fdiv`. -/
theorem ofInt_fdiv (i j : Int) : ofInt (i.fdiv j) = (ofInt i).fdiv (ofInt j) := by
  have h : (ofInt (i.fdiv j)).toInt = ((ofInt i).fdiv (ofInt j)).toInt := by
    rw [toInt_ofInt, toInt_fdiv, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- `ofInt`-version of `toInt_fmod`. -/
theorem ofInt_fmod (i j : Int) : ofInt (i.fmod j) = (ofInt i).fmod (ofInt j) := by
  have h : (ofInt (i.fmod j)).toInt = ((ofInt i).fmod (ofInt j)).toInt := by
    rw [toInt_ofInt, toInt_fmod, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
