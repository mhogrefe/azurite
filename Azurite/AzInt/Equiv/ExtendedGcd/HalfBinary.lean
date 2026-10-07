/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Equiv.ExtendedGcd.Binary
import Azurite.AzInt.ExtendedGcd.HalfBinary
import Azurite.AzNat.Equiv.Gcd.HalfBinary
import Azurite.AzZModPow2.Equiv.Conversion
import Azurite.AzZModPow2.Equiv.Inv
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
## Correctness of the extended half-binary GCD

Every intermediate result is a `ScaledBezout` row `r` for the operands it was computed for:
`r.s x + r.t y = 2^{r.e} r.g` (`ScaledBezout.Spec`) with `r.g` the odd part of `gcd(x, y)`
(`ScaledBezout.GcdSpec`).  The base case inherits both from the quadratic algorithm
(`egcdBinary_bezout`, `egcdBinary_gcd`); each pull-back preserves `Spec` by a ring identity from
the matrix relation `2^sh (x', y')ᵀ = R (x, y)ᵀ` (`pullBack_spec`, `pullBackWord_spec`,
`pullBackStep_spec`) and `GcdSpec` by the odd-part lemmas of the plain driver (`OddEquiv`).
`fixUp_spec` strips the power of two: the correction `k ≡ −t x⁻¹ (mod 2^e)` makes both
coefficients divisible by `2^e` (the second because `x` is odd), and the two exact shifts give a
Bézout row for `g` itself.  The entry point then undoes the preparation exactly as
`toNat_gcdHalfBinaryWith` does.
-/

namespace Azurite.AzInt

open Azurite.AzNat (OddEquiv oddPartNat)

/-! ### The row invariants -/

/-- `r` is a scaled Bézout row for `(x, y)`: `s x + t y = 2^e g`. -/
def ScaledBezout.Spec (r : ScaledBezout) (x y : ℤ) : Prop :=
  r.s.toInt * x + r.t.toInt * y = 2 ^ r.e * (r.g.toNat : ℤ)

/-- The gcd component of `r` is the odd part of `gcd(x, y)`. -/
def ScaledBezout.GcdSpec (r : ScaledBezout) (x y : ℤ) : Prop :=
  r.g.toNat = oddPartNat (Int.gcd x y)

@[simp] theorem pullBack_g (R : AzNat.Mat2) (sh : ℕ) (r : ScaledBezout) :
    (pullBack R sh r).g = r.g := rfl

@[simp] theorem pullBackWord_g (M : AzNat.WordMat) (sh : ℕ) (r : ScaledBezout) :
    (pullBackWord M sh r).g = r.g := rfl

@[simp] theorem pullBackStep_g (j : ℕ) (q : AzInt) (r : ScaledBezout) :
    (pullBackStep j q r).g = r.g := rfl

/-! ### The base case -/

theorem toInt_signed_mul (b : Bool) (z : AzInt) (c : AzInt) (hz : z.sign = b) :
    (if b then c else -c).toInt * z.toInt = c.toInt * (z.abs.toNat : ℤ) := by
  rw [AzNat.toInt_eq_ite z, hz]
  cases b
  · simp only [toInt_neg, Bool.false_eq_true, ↓reduceIte]; ring
  · simp only [↓reduceIte]

theorem egcdBase_spec (x y : AzInt) :
    (egcdBase x y).Spec x.toInt y.toInt ∧ (egcdBase x y).GcdSpec x.toInt y.toInt := by
  have hbez := egcdBinary_bezout x.abs y.abs
  have hgcd := egcdBinary_gcd x.abs y.abs
  have hsx := toInt_signed_mul x.sign x (egcdBinary x.abs y.abs).2.1 rfl
  have hsy := toInt_signed_mul y.sign y (egcdBinary x.abs y.abs).2.2 rfl
  have hg : Int.gcd x.toInt y.toInt = (egcdBinary x.abs y.abs).1.toNat := by
    rw [hgcd]
    show Nat.gcd x.toInt.natAbs y.toInt.natAbs = _
    rw [← AzInt.toNat_natAbs, ← AzInt.toNat_natAbs]; rfl
  unfold egcdBase ScaledBezout.Spec ScaledBezout.GcdSpec
  dsimp only
  split
  · rename_i hz
    have h0 : (egcdBinary x.abs y.abs).1 = 0 := by
      by_contra hne
      rw [AzNat.trailingZeros_eq_padicValNat _ hne] at hz
      cases hz
    rw [h0, AzNat.toNat_zero] at hbez hg
    refine ⟨?_, ?_⟩
    · dsimp only
      rw [hsx, hsy, hbez, AzNat.toNat_zero]; simp
    · dsimp only
      rw [hg, AzNat.toNat_zero]; simp [oddPartNat]
  · rename_i e he
    have hne : (egcdBinary x.abs y.abs).1 ≠ 0 := fun h0 => by
      rw [h0, AzNat.trailingZeros_zero] at he; cases he
    rw [AzNat.trailingZeros_eq_padicValNat _ hne] at he
    obtain rfl := Option.some.inj he
    refine ⟨?_, ?_⟩
    · dsimp only
      rw [hsx, hsy, hbez, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
      have := Nat.mul_div_cancel'
        (pow_padicValNat_dvd (p := 2) (n := (egcdBinary x.abs y.abs).1.toNat))
      exact_mod_cast this.symm
    · dsimp only
      rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow, hg]; rfl

/-! ### Pulling a row back through a round -/

theorem pullBack_spec (R : AzNat.Mat2) (sh : ℕ) (r : ScaledBezout) (x y x' y' : ℤ)
    (h : r.Spec x' y') (hx : R.a.toInt * x + R.b.toInt * y = 2 ^ sh * x')
    (hy : R.c.toInt * x + R.d.toInt * y = 2 ^ sh * y') : (pullBack R sh r).Spec x y := by
  unfold ScaledBezout.Spec at *
  simp only [pullBack, toInt_add, toInt_mul, pow_add]
  linear_combination r.s.toInt * hx + r.t.toInt * hy + 2 ^ sh * h

theorem toInt_combineWord (m₁ m₂ : Int64) (s t : AzInt) :
    ((AzNat.fusedCombine? m₁ m₂ s t 0).getD (m₁.toAzInt * s + m₂.toAzInt * t)).toInt
      = m₁.toInt * s.toInt + m₂.toInt * t.toInt := by
  cases h : AzNat.fusedCombine? m₁ m₂ s t 0 with
  | none => simp [toInt_add, toInt_mul, Int64.toInt_toAzInt]
  | some c =>
    have := AzNat.toInt_fusedCombine? m₁ m₂ s t 0 c h
    simpa using this

theorem pullBackWord_spec (M : AzNat.WordMat) (sh : ℕ) (r : ScaledBezout) (x y x' y' : ℤ)
    (h : r.Spec x' y') (hx : M.m₁₁.toInt * x + M.m₁₂.toInt * y = 2 ^ sh * x')
    (hy : M.m₂₁.toInt * x + M.m₂₂.toInt * y = 2 ^ sh * y') : (pullBackWord M sh r).Spec x y := by
  unfold ScaledBezout.Spec at *
  simp only [pullBackWord, toInt_combineWord, pow_add]
  linear_combination r.s.toInt * hx + r.t.toInt * hy + 2 ^ sh * h

theorem pullBackStep_spec (j : ℕ) (q : AzInt) (r : ScaledBezout) (x' y' y'' r' : ℤ)
    (h : r.Spec y'' r') (hy : 2 ^ j * y' = 2 ^ (2 * j) * y'')
    (hr : 2 ^ j * x' + q.toInt * y' = 2 ^ (2 * j) * r') : (pullBackStep j q r).Spec x' y' := by
  unfold ScaledBezout.Spec at *
  simp only [pullBackStep, toInt_add, toInt_mul, toInt_hShiftLeft, pow_add]
  linear_combination r.t.toInt * hr + r.s.toInt * hy + 2 ^ (2 * j) * h

/-! ### The driver -/

theorem egcdDriver_spec (threshold quadThreshold fuel : ℕ) : ∀ x y : AzInt,
    (egcdDriver threshold quadThreshold fuel x y).Spec x.toInt y.toInt ∧
      (egcdDriver threshold quadThreshold fuel x y).GcdSpec x.toInt y.toInt := by
  induction fuel with
  | zero => intro x y; exact egcdBase_spec x y
  | succ fuel ih =>
    intro x y
    rw [egcdDriver]
    dsimp only
    by_cases hn : max x.size y.size ≤ threshold
    · rw [ite_eq_left hn]; exact egcdBase_spec x y
    rw [ite_eq_right hn]
    by_cases hq : max x.size y.size ≤ quadThreshold
    · rw [ite_eq_left hq]
      split_ifs with hj
      · exact egcdBase_spec x y
      split
      · rename_i x' y' hx' hy'
        have hdet := AzNat.natAbs_detInts_halfBinaryGcdWord
          (x.lowWord2 (2 * AzNat.halfBinaryWordThreshold + 1))
          (y.lowWord2 (2 * AzNat.halfBinaryWordThreshold + 1)) AzNat.halfBinaryWordThreshold
        have hc := AzNat.toInt_fusedCombine? _ _ _ _ _ _ hx'
        have hd := AzNat.toInt_fusedCombine? _ _ _ _ _ _ hy'
        obtain ⟨h1, h2⟩ := ih x' y'
        refine ⟨pullBackWord_spec _ _ _ _ _ _ _ h1 (by rw [← hc]; ring) (by rw [← hd]; ring), ?_⟩
        unfold ScaledBezout.GcdSpec at h2 ⊢
        rw [pullBackWord_g, h2]
        exact (AzNat.oddPartNat_eq_of_oddEquiv (AzNat.oddEquiv_gcd_of_mat _ _ _ _ _ _ _ _ _ hdet
          (by rw [← hc]; ring) (by rw [← hd]; ring))).symm
      · exact egcdBase_spec x y
    · rw [ite_eq_right hq]
      split
      · rename_i x' y' hx' hy'
        have hdet := AzNat.natAbs_detInt_halfBinaryGcd (max x.size y.size / 2 + 1)
          (x.lowBits (2 * (max x.size y.size / 2) + 1))
          (y.lowBits (2 * (max x.size y.size / 2) + 1))
          (max x.size y.size / 2)
        have hc := AzNat.toInt_exactShiftRight _ _ _ hx'
        have hd := AzNat.toInt_exactShiftRight _ _ _ hy'
        rw [AzNat.toInt_apply_fst] at hc
        rw [AzNat.toInt_apply_snd] at hd
        have hmat : OddEquiv (Int.gcd x.toInt y.toInt) (Int.gcd x'.toInt y'.toInt) :=
          AzNat.oddEquiv_gcd_of_mat _ _ _ _ _ _ _ _ _ hdet (by rw [← hc]; ring)
            (by rw [← hd]; ring)
        have pull : ∀ (R : AzNat.Mat2) (sh : ℕ) (r : ScaledBezout),
            R.a.toInt * x.toInt + R.b.toInt * y.toInt = 2 ^ sh * x'.toInt →
            R.c.toInt * x.toInt + R.d.toInt * y.toInt = 2 ^ sh * y'.toInt →
            r.Spec x'.toInt y'.toInt → r.GcdSpec x'.toInt y'.toInt →
            (pullBack R sh r).Spec x.toInt y.toInt ∧ (pullBack R sh r).GcdSpec x.toInt y.toInt := by
          intro R sh r hR₁ hR₂ h1 h2
          refine ⟨pullBack_spec _ _ _ _ _ _ _ h1 hR₁ hR₂, ?_⟩
          unfold ScaledBezout.GcdSpec at h2 ⊢
          rw [pullBack_g, h2, AzNat.oddPartNat_eq_of_oddEquiv hmat]
        split
        · exact pull _ _ _ (by rw [← hc]; ring) (by rw [← hd]; ring) (egcdBase_spec x' y').1
            (egcdBase_spec x' y').2
        · rename_i j₀ hj₀
          have hb'' := AzNat.toInt_mkNorm_shift_of_trailingZeros y' j₀ hj₀
          have hstep : OddEquiv (Int.gcd x'.toInt y'.toInt)
              (Int.gcd (AzInt.mkNorm y'.sign (y'.abs >>> j₀)).toInt
                (AzNat.binaryDivide x' (AzInt.mkNorm y'.sign (y'.abs >>> j₀)) j₀).2.toInt) := by
            rw [AzNat.toInt_snd_binaryDivide, ← hb'']
            exact AzNat.oddEquiv_gcd_binaryStep _ _ _ _
          split
          · rename_i r' hr'
            have hr := AzNat.toInt_exactShiftRight _ _ _ hr'
            have h3 := AzNat.toInt_snd_binaryDivide x' (AzInt.mkNorm y'.sign (y'.abs >>> j₀)) j₀
            obtain ⟨h1, h2⟩ := ih _ r'
            apply pull _ _ _ (by rw [← hc]; ring) (by rw [← hd]; ring)
            · apply pullBackStep_spec _ _ _ _ _ _ _ h1
              · rw [← hb'']; ring
              · rw [← hb'']
                linear_combination -(2 ^ j₀ : ℤ) * h3 - 2 ^ j₀ * hr
            · unfold ScaledBezout.GcdSpec at h2 ⊢
              rw [pullBackStep_g, h2, AzNat.oddPartNat_eq_of_oddEquiv hstep, ← hr]
              exact (AzNat.oddPartNat_eq_of_oddEquiv (AzNat.oddEquiv_gcd_div_pow _ _ _)).symm
          · exact pull _ _ _ (by rw [← hc]; ring) (by rw [← hd]; ring) (egcdBase_spec x' y').1
              (egcdBase_spec x' y').2
      · exact egcdBase_spec x y

/-! ### Stripping the power of two -/

theorem fixUp_spec (x y : AzNat) (hx : Odd x.toNat) (r : ScaledBezout)
    (h : r.Spec x.toNat y.toNat) :
    (fixUp x y r).1.toInt * x.toNat + (fixUp x y r).2.toInt * y.toNat = (r.g.toNat : ℤ) := by
  unfold ScaledBezout.Spec at h
  unfold fixUp
  dsimp only
  split_ifs with hodd
  · set kz := AzZModPow2.ofAzInt r.e (-r.t) * (AzZModPow2.ofAzNat r.e x).invOdd hodd with hkz
    set K : ℤ := (kz.val.toNat : ℤ) with hK
    -- the inverse really inverts, and `k ≡ −t x⁻¹`
    have hinv : (x.toNat : ZMod (2 ^ r.e)) *
        AzZModPow2.toZMod ((AzZModPow2.ofAzNat r.e x).invOdd hodd) = 1 := by
      have := congrArg AzZModPow2.toZMod (AzZModPow2.mul_invOdd (AzZModPow2.ofAzNat r.e x) hodd)
      rwa [AzZModPow2.toZMod_mul, AzZModPow2.toZMod_ofAzNat, AzZModPow2.toZMod_one] at this
    have hKz : (K : ZMod (2 ^ r.e)) = -(r.t.toInt : ZMod (2 ^ r.e)) *
        AzZModPow2.toZMod ((AzZModPow2.ofAzNat r.e x).invOdd hodd) := by
      rw [hK, Int.cast_natCast]
      show AzZModPow2.toZMod kz = _
      rw [hkz, AzZModPow2.toZMod_mul, AzZModPow2.toZMod_ofAzInt, toInt_neg, Int.cast_neg]
    -- `2^e ∣ t + k x`
    have hT : (2 : ℤ) ^ r.e ∣ r.t.toInt + K * x.toNat := by
      have hz : ((r.t.toInt + K * x.toNat : ℤ) : ZMod (2 ^ r.e)) = 0 := by
        push_cast
        rw [hKz]
        linear_combination (-(r.t.toInt : ZMod (2 ^ r.e))) * hinv
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      exact_mod_cast this
    -- `2^e ∣ s − k y`, because `(s − k y) x = 2^e g − (t + k x) y` and `x` is odd
    have hS : (2 : ℤ) ^ r.e ∣ r.s.toInt - K * y.toNat := by
      have hcop : IsCoprime ((2 : ℤ) ^ r.e) (x.toNat : ℤ) := by
        apply IsCoprime.pow_left
        have := Nat.isCoprime_iff_coprime.mpr (Odd.coprime_two_left hx)
        exact_mod_cast this
      apply hcop.dvd_of_dvd_mul_left
      have : (x.toNat : ℤ) * (r.s.toInt - K * y.toNat)
          = 2 ^ r.e * r.g.toNat - (r.t.toInt + K * x.toNat) * y.toNat := by
        linear_combination h
      rw [this]
      exact Dvd.dvd.sub (Dvd.intro _ rfl) (Dvd.dvd.mul_right hT _)
    simp only [toInt_hShiftRight, Int.shiftRight_eq_div_pow, toInt_sub, toInt_add, toInt_mul,
      AzNat.toInt_toAzInt, Nat.cast_pow, Nat.cast_ofNat]
    rw [← hK]
    apply mul_left_cancel₀ (pow_ne_zero r.e (two_ne_zero' ℤ))
    rw [mul_add, ← mul_assoc, ← mul_assoc, Int.mul_ediv_cancel' hS, Int.mul_ediv_cancel' hT]
    linear_combination h
  · have he : r.e = 0 := by
      by_contra hne
      apply hodd
      rw [AzZModPow2.isOdd_iff]
      show Odd (x.modPow2 r.e).toNat
      rw [AzNat.toNat_modPow2, Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 hne),
        ← Nat.odd_iff]
      exact hx
    rw [he, pow_zero, one_mul] at h
    exact h

/-! ### The entry points -/

theorem egcdOddWith_spec (threshold quadThreshold : ℕ) (x y : AzNat) (hx : Odd x.toNat) :
    (egcdOddWith threshold quadThreshold x y).2.1.toInt * x.toNat
        + (egcdOddWith threshold quadThreshold x y).2.2.toInt * y.toNat
      = ((egcdOddWith threshold quadThreshold x y).1.toNat : ℤ) ∧
    (egcdOddWith threshold quadThreshold x y).1.toNat = Nat.gcd x.toNat y.toNat := by
  have hodd : ∀ n, Odd (Nat.gcd x.toNat n) := fun n => hx.of_dvd_nat (Nat.gcd_dvd_left _ _)
  unfold egcdOddWith
  dsimp only
  split_ifs with hy
  · obtain ⟨h1, h2⟩ := egcdDriver_spec threshold quadThreshold (max x.size (x + y).size + 1)
      x.toAzInt (x + y).toAzInt
    simp only [ScaledBezout.Spec, ScaledBezout.GcdSpec] at h1 h2
    rw [AzNat.toInt_toAzInt, AzNat.toInt_toAzInt] at h1 h2
    have hf := fixUp_spec x (x + y) hx _ h1
    rw [Int.gcd_natCast_natCast, AzNat.toNat_add, AzNat.oddPartNat_of_odd (hodd _),
      Nat.gcd_self_add_right] at h2
    refine ⟨?_, h2⟩
    rw [AzNat.toNat_add] at hf
    push_cast at hf
    rw [toInt_add]
    linear_combination hf
  · obtain ⟨h1, h2⟩ := egcdDriver_spec threshold quadThreshold (max x.size y.size + 1)
      x.toAzInt y.toAzInt
    simp only [ScaledBezout.Spec, ScaledBezout.GcdSpec] at h1 h2
    rw [AzNat.toInt_toAzInt, AzNat.toInt_toAzInt] at h1 h2
    have hf := fixUp_spec x y hx _ h1
    rw [Int.gcd_natCast_natCast, AzNat.oddPartNat_of_odd (hodd _)] at h2
    exact ⟨hf, h2⟩

theorem egcdHalfBinaryWith_spec (threshold quadThreshold : ℕ) (a b : AzNat) :
    (egcdHalfBinaryWith threshold quadThreshold a b).2.1.toInt * a.toNat
        + (egcdHalfBinaryWith threshold quadThreshold a b).2.2.toInt * b.toNat
      = ((egcdHalfBinaryWith threshold quadThreshold a b).1.toNat : ℤ) ∧
    (egcdHalfBinaryWith threshold quadThreshold a b).1.toNat = Nat.gcd a.toNat b.toNat := by
  unfold egcdHalfBinaryWith
  by_cases ha : a = 0
  · subst ha; rw [AzNat.trailingZeros_zero]; simp [toInt_zero, toInt_one, AzNat.toNat_zero]
  by_cases hb : b = 0
  · subst hb
    rw [AzNat.trailingZeros_eq_padicValNat a ha, AzNat.trailingZeros_zero]
    simp [toInt_zero, toInt_one, AzNat.toNat_zero]
  have ha' : a.toNat ≠ 0 := fun h => ha (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
  have hb' : b.toNat ≠ 0 := fun h => hb (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
  rw [AzNat.trailingZeros_eq_padicValNat a ha, AzNat.trailingZeros_eq_padicValNat b hb]
  dsimp only
  have hshift : ∀ (n : AzNat) (t : ℕ), (n >>> t).toNat = n.toNat / 2 ^ t := fun n t => by
    rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
  have hfin : ∀ (x y : ℕ) (t : ℕ), 2 ^ t ∣ x → 2 ^ t ∣ y →
      Nat.gcd (x / 2 ^ t) (y / 2 ^ t) * 2 ^ t = Nat.gcd x y := fun x y t hx hy => by
    rw [Nat.gcd_div hx hy, Nat.div_mul_cancel (Nat.dvd_gcd hx hy)]
  have hcast : ∀ (n : AzNat) (t : ℕ), 2 ^ t ∣ n.toNat →
      (((n >>> t).toNat : ℕ) : ℤ) * 2 ^ t = (n.toNat : ℤ) := fun n t hdvd => by
    rw [hshift]; exact_mod_cast Nat.div_mul_cancel hdvd
  split_ifs with hle
  · rw [Nat.min_eq_left hle]
    have hdb : 2 ^ padicValNat 2 a.toNat ∣ b.toNat := (padicValNat_dvd_iff_le hb').mpr hle
    obtain ⟨h1, h2⟩ := egcdOddWith_spec threshold quadThreshold (a >>> padicValNat 2 a.toNat)
      (b >>> padicValNat 2 a.toNat) (by rw [hshift]; exact AzNat.odd_oddPartNat ha')
    refine ⟨?_, ?_⟩
    · rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, ← hcast a _ pow_padicValNat_dvd,
        ← hcast b _ hdb]
      push_cast
      linear_combination (2 ^ padicValNat 2 a.toNat : ℤ) * h1
    · rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, h2, hshift, hshift]
      exact hfin _ _ _ pow_padicValNat_dvd hdb
  · have hlt := le_of_lt (not_le.mp hle)
    rw [Nat.min_eq_right hlt]
    have hda : 2 ^ padicValNat 2 b.toNat ∣ a.toNat := (padicValNat_dvd_iff_le ha').mpr hlt
    obtain ⟨h1, h2⟩ := egcdOddWith_spec threshold quadThreshold (b >>> padicValNat 2 b.toNat)
      (a >>> padicValNat 2 b.toNat) (by rw [hshift]; exact AzNat.odd_oddPartNat hb')
    refine ⟨?_, ?_⟩
    · rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, ← hcast a _ hda,
        ← hcast b _ pow_padicValNat_dvd]
      push_cast
      linear_combination (2 ^ padicValNat 2 b.toNat : ℤ) * h1
    · rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, h2, hshift, hshift, Nat.gcd_comm]
      exact hfin _ _ _ hda pow_padicValNat_dvd

/-- **Bézout identity for `egcdHalfBinary`.** -/
theorem egcdHalfBinary_bezout (a b : AzNat) :
    (egcdHalfBinary a b).2.1.toInt * (a.toNat : ℤ) + (egcdHalfBinary a b).2.2.toInt * (b.toNat : ℤ)
      = ((egcdHalfBinary a b).1.toNat : ℤ) :=
  (egcdHalfBinaryWith_spec _ _ a b).1

/-- **gcd-value equality for `egcdHalfBinary`.** -/
theorem egcdHalfBinary_gcd (a b : AzNat) :
    (egcdHalfBinary a b).1.toNat = Nat.gcd a.toNat b.toNat :=
  (egcdHalfBinaryWith_spec _ _ a b).2

end Azurite.AzInt
