/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.ExtendedGcd
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.TrailingZeros
import Azurite.AzNat.Equiv.Basic
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Sub
import Azurite.AzInt.Equiv.Mul
import Azurite.AzInt.Equiv.ShiftRight
import Azurite.AzInt.Equiv.Parity
import Azurite.AzInt.Equiv.Basic
import Mathlib.Data.ZMod.Basic

/-!
## Bézout identity for the extended binary GCD (`egcd`)

This file proves the **Bézout identity** for `Azurite.AzInt.egcd`: if
`egcd a b = (g, s, t)` then `s · a + t · b = g` over `ℤ`.  (The gcd-value
equality `g = gcd a b` is a separate result, not proved here.)

The proof is by invariant preservation: each loop body preserves the relations
`A·x + B·y = u` and `C·x + D·y = v` over `ℤ`, so no fuel-sufficiency reasoning is
needed — the `fuel = 0` base cases simply return their inputs.
-/

namespace Azurite.AzInt

open Azurite (AzNat)

/-! ### Exact-halving lemmas -/

/-- For an even `AzNat`, `2 · (u >>> 1) = u` over `ℤ`. -/
private lemma two_mul_shiftRight_one_toNat (u : AzNat) (h : u.isEven = true) :
    2 * ((u >>> 1).toNat : ℤ) = (u.toNat : ℤ) := by
  have hsr : (u >>> 1).toNat = u.toNat / 2 ^ 1 := AzNat.toNat_shiftRight u 1
  have heven : Even u.toNat := (AzNat.isEven_iff u).mp h
  obtain ⟨m, hm⟩ := heven
  rw [hsr]
  simp only [pow_one]
  have : u.toNat / 2 = m := by omega
  rw [this]
  omega

/-- For an even `AzInt`, `2 · (z >>> 1) = z` over `ℤ`. -/
private lemma two_mul_hShiftRight_one_toInt (z : AzInt) (h : Even z.toInt) :
    2 * (z >>> 1).toInt = z.toInt := by
  rw [AzInt.toInt_hShiftRight z 1, Int.shiftRight_eq_div_pow, pow_one]
  obtain ⟨m, hm⟩ := h
  omega

/-! ### Parity lemma -/

/-- The key parity fact: under the branch hypotheses, both numerators of the
"not both even" halving step are even. -/
private lemma egcd_parity (A B X Y : ℤ) (hu : Even (A * X + B * Y))
    (hxy : ¬(Even X ∧ Even Y)) (hbranch : ¬(Even A ∧ Even B)) :
    Even (A + Y) ∧ Even (B - X) := by
  -- Translate all parities to `ZMod 2` and decide.
  have key : ∀ n : ℤ, Even n ↔ ((n : ZMod 2) = 0) := by
    intro n
    rw [even_iff_two_dvd, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [key, Int.cast_add, Int.cast_sub, Int.cast_mul] at hu hxy hbranch ⊢
  revert hu hxy hbranch
  generalize (A : ZMod 2) = a
  generalize (B : ZMod 2) = b
  generalize (X : ZMod 2) = x
  generalize (Y : ZMod 2) = y
  revert a b x y
  decide

/-! ### `egcdMakeOdd` preserves the Bézout invariant -/

private lemma egcdMakeOdd_bezout (x y : AzNat)
    (hxy : ¬(Even (x.toNat : ℤ) ∧ Even (y.toNat : ℤ)))
    (fuel : Nat) (u : AzNat) (A B : AzInt)
    (hinv : A.toInt * (x.toNat : ℤ) + B.toInt * (y.toNat : ℤ) = (u.toNat : ℤ)) :
    (egcdMakeOdd x y fuel u A B).2.1.toInt * (x.toNat : ℤ)
      + (egcdMakeOdd x y fuel u A B).2.2.toInt * (y.toNat : ℤ)
      = ((egcdMakeOdd x y fuel u A B).1.toNat : ℤ) := by
  induction fuel generalizing u A B with
  | zero => simpa [egcdMakeOdd] using hinv
  | succ fuel ih =>
    rw [egcdMakeOdd]
    by_cases hcond : u.isEven && !(u.limbs.size == 0)
    · rw [ite_eq_left hcond]
      have hue : u.isEven = true := by
        simp only [Bool.and_eq_true] at hcond; exact hcond.1
      have h2u : 2 * ((u >>> 1).toNat : ℤ) = (u.toNat : ℤ) :=
        two_mul_shiftRight_one_toNat u hue
      by_cases hAB : A.isEven && B.isEven
      · -- both even branch
        simp only [hAB, ite_true]
        have hABp := (Bool.and_eq_true _ _).mp hAB
        have hAe : Even A.toInt := (AzInt.isEven_iff A).mp hABp.1
        have hBe : Even B.toInt := (AzInt.isEven_iff B).mp hABp.2
        have h2A : 2 * (A >>> 1).toInt = A.toInt := two_mul_hShiftRight_one_toInt A hAe
        have h2B : 2 * (B >>> 1).toInt = B.toInt := two_mul_hShiftRight_one_toInt B hBe
        have hnew : (A >>> 1).toInt * (x.toNat : ℤ) + (B >>> 1).toInt * (y.toNat : ℤ)
            = ((u >>> 1).toNat : ℤ) := by
          have : 2 * ((A >>> 1).toInt * (x.toNat : ℤ) + (B >>> 1).toInt * (y.toNat : ℤ))
              = 2 * ((u >>> 1).toNat : ℤ) := by
            rw [h2u, ← hinv]; nlinarith [h2A, h2B]
          omega
        exact ih (u >>> 1) (A >>> 1) (B >>> 1) hnew
      · -- not both even branch
        simp only [hAB]
        have hbranch : ¬(Even A.toInt ∧ Even B.toInt) := by
          rw [← AzInt.isEven_iff A, ← AzInt.isEven_iff B]
          rw [← Bool.and_eq_true]
          simp only [hAB, Bool.false_eq_true, not_false_iff]
        have hue2 : Even u.toNat := (AzNat.isEven_iff u).mp hue
        have huinv : Even (A.toInt * (x.toNat : ℤ) + B.toInt * (y.toNat : ℤ)) := by
          rw [hinv]; exact_mod_cast hue2
        obtain ⟨hAY, hBX⟩ := egcd_parity A.toInt B.toInt (x.toNat : ℤ) (y.toNat : ℤ)
          huinv hxy hbranch
        -- A' = (A + mkNorm true y) >>> 1, B' = (B - mkNorm true x) >>> 1
        have hAYi : Even (A + AzInt.mkNorm true y).toInt := by
          rw [AzInt.toInt_add, AzInt.toInt_mkNorm_true]; exact hAY
        have hBXi : Even (B - AzInt.mkNorm true x).toInt := by
          rw [AzInt.toInt_sub, AzInt.toInt_mkNorm_true]; exact hBX
        have h2A : 2 * ((A + AzInt.mkNorm true y) >>> 1).toInt
            = A.toInt + (y.toNat : ℤ) := by
          rw [two_mul_hShiftRight_one_toInt _ hAYi, AzInt.toInt_add,
            AzInt.toInt_mkNorm_true]
        have h2B : 2 * ((B - AzInt.mkNorm true x) >>> 1).toInt
            = B.toInt - (x.toNat : ℤ) := by
          rw [two_mul_hShiftRight_one_toInt _ hBXi, AzInt.toInt_sub,
            AzInt.toInt_mkNorm_true]
        set A' := (A + AzInt.mkNorm true y) >>> 1 with hA'
        set B' := (B - AzInt.mkNorm true x) >>> 1 with hB'
        have hnew : A'.toInt * (x.toNat : ℤ) + B'.toInt * (y.toNat : ℤ)
            = ((u >>> 1).toNat : ℤ) := by
          have key : 2 * (A'.toInt * (x.toNat : ℤ) + B'.toInt * (y.toNat : ℤ))
              = 2 * ((u >>> 1).toNat : ℤ) := by
            rw [h2u, ← hinv]; nlinarith [h2A, h2B]
          omega
        exact ih (u >>> 1) A' B' hnew
    · rw [ite_eq_right hcond]
      simpa using hinv

/-! ### `egcdLoop` preserves the Bézout invariant -/

private lemma egcdLoop_bezout (x y : AzNat)
    (hxy : ¬(Even (x.toNat : ℤ) ∧ Even (y.toNat : ℤ)))
    (innerFuel fuel : Nat) (u v : AzNat) (A B C D : AzInt)
    (hU : A.toInt * (x.toNat : ℤ) + B.toInt * (y.toNat : ℤ) = (u.toNat : ℤ))
    (hV : C.toInt * (x.toNat : ℤ) + D.toInt * (y.toNat : ℤ) = (v.toNat : ℤ)) :
    (egcdLoop x y innerFuel fuel u v A B C D).2.1.toInt * (x.toNat : ℤ)
      + (egcdLoop x y innerFuel fuel u v A B C D).2.2.toInt * (y.toNat : ℤ)
      = ((egcdLoop x y innerFuel fuel u v A B C D).1.toNat : ℤ) := by
  induction fuel generalizing u v A B C D with
  | zero => simpa [egcdLoop] using hV
  | succ fuel ih =>
    rw [egcdLoop]
    -- makeOdd on the U-side
    set su := egcdMakeOdd x y innerFuel u A B with hsu
    obtain ⟨u', A', B'⟩ := su
    have hUpost : A'.toInt * (x.toNat : ℤ) + B'.toInt * (y.toNat : ℤ) = (u'.toNat : ℤ) := by
      have := egcdMakeOdd_bezout x y hxy innerFuel u A B hU
      rw [← hsu] at this
      exact this
    -- makeOdd on the V-side
    set sv := egcdMakeOdd x y innerFuel v C D with hsv
    obtain ⟨v', C', D'⟩ := sv
    have hVpost : C'.toInt * (x.toNat : ℤ) + D'.toInt * (y.toNat : ℤ) = (v'.toNat : ℤ) := by
      have := egcdMakeOdd_bezout x y hxy innerFuel v C D hV
      rw [← hsv] at this
      exact this
    simp only
    by_cases hcmp : AzNat.compare u' v' = Ordering.lt
    · rw [ite_eq_left hcmp]
      -- u' < v', so subtraction (v' - u') is exact
      have hlt : u'.toNat < v'.toNat := by
        rw [AzNat.compare_eq_compare_toNat] at hcmp
        rw [Nat.compare_eq_lt] at hcmp; exact hcmp
      have hsub : ((v' - u').toNat : ℤ) = (v'.toNat : ℤ) - (u'.toNat : ℤ) := by
        rw [AzNat.toNat_sub]; omega
      have hVnew : (C' - A').toInt * (x.toNat : ℤ) + (D' - B').toInt * (y.toNat : ℤ)
          = ((v' - u').toNat : ℤ) := by
        rw [hsub, AzInt.toInt_sub, AzInt.toInt_sub, ← hVpost, ← hUpost]; ring
      exact ih u' (v' - u') A' B' (C' - A') (D' - B') hUpost hVnew
    · rw [ite_eq_right hcmp]
      have hge : v'.toNat ≤ u'.toNat := by
        rw [AzNat.compare_eq_compare_toNat] at hcmp
        rcases Nat.lt_trichotomy u'.toNat v'.toNat with h | h | h
        · exact absurd (Nat.compare_eq_lt.mpr h) hcmp
        · omega
        · omega
      by_cases hsize : (u' - v').limbs.size == 0
      · rw [ite_eq_left hsize]; simpa using hVpost
      · rw [ite_eq_right hsize]
        have hsub : ((u' - v').toNat : ℤ) = (u'.toNat : ℤ) - (v'.toNat : ℤ) := by
          rw [AzNat.toNat_sub]; omega
        have hUnew : (A' - C').toInt * (x.toNat : ℤ) + (B' - D').toInt * (y.toNat : ℤ)
            = ((u' - v').toNat : ℤ) := by
          rw [hsub, AzInt.toInt_sub, AzInt.toInt_sub, ← hUpost, ← hVpost]; ring
        exact ih (u' - v') v' (A' - C') (B' - D') C' D' hUnew hVpost

/-! ### Top-level Bézout identity -/

/-- **Bézout identity for `egcd`.**  With `(g, s, t) = egcd a b`,
`s · a + t · b = g` over `ℤ`. -/
theorem egcd_bezout (a b : AzNat) :
    (egcd a b).2.1.toInt * (a.toNat : ℤ) + (egcd a b).2.2.toInt * (b.toNat : ℤ)
      = ((egcd a b).1.toNat : ℤ) := by
  rw [egcd]
  by_cases ha0 : a.limbs.size = 0
  · simp only [ha0, ite_eq_left]
    rw [(AzNat.toNat_eq_zero_iff a).mpr ha0]
    simp [AzInt.toInt_zero, AzInt.toInt_one]
  · simp only [ha0, ite_false]
    by_cases hb0 : b.limbs.size = 0
    · simp only [hb0, ite_eq_left]
      rw [(AzNat.toNat_eq_zero_iff b).mpr hb0]
      simp [AzInt.toInt_zero, AzInt.toInt_one]
    · simp only [hb0]
      -- Both nonzero. Set up the reduced inputs.
      have ha_ne : a.toNat ≠ 0 := fun h => ha0 ((AzNat.toNat_eq_zero_iff a).mp h)
      have hb_ne : b.toNat ≠ 0 := fun h => hb0 ((AzNat.toNat_eq_zero_iff b).mp h)
      have ha_ne' : a ≠ 0 := fun h => ha_ne (by rw [h]; rfl)
      have hb_ne' : b ≠ 0 := fun h => hb_ne (by rw [h]; rfl)
      set va := padicValNat 2 a.toNat with hva
      set vb := padicValNat 2 b.toNat with hvb
      have htza : a.trailingZeros = some va :=
        AzNat.trailingZeros_eq_padicValNat a ha_ne'
      have htzb : b.trailingZeros = some vb :=
        AzNat.trailingZeros_eq_padicValNat b hb_ne'
      set k := min ((a.trailingZeros).getD 0) ((b.trailingZeros).getD 0) with hk
      have hkeq : k = min va vb := by rw [hk, htza, htzb]; rfl
      have hka : k ≤ va := by rw [hkeq]; exact Nat.min_le_left _ _
      have hkb : k ≤ vb := by rw [hkeq]; exact Nat.min_le_right _ _
      -- divisibility
      have hdvd_a : 2 ^ k ∣ a.toNat :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 hka) pow_padicValNat_dvd
      have hdvd_b : 2 ^ k ∣ b.toNat :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 hkb) pow_padicValNat_dvd
      set x := a >>> k with hxdef
      set y := b >>> k with hydef
      have hxval : x.toNat = a.toNat / 2 ^ k := AzNat.toNat_shiftRight a k
      have hyval : y.toNat = b.toNat / 2 ^ k := AzNat.toNat_shiftRight b k
      -- a = x * 2^k, b = y * 2^k
      have hax : a.toNat = x.toNat * 2 ^ k := by
        rw [hxval]; exact (Nat.div_mul_cancel hdvd_a).symm
      have hby : b.toNat = y.toNat * 2 ^ k := by
        rw [hyval]; exact (Nat.div_mul_cancel hdvd_b).symm
      -- not both even
      have hxy : ¬(Even (x.toNat : ℤ) ∧ Even (y.toNat : ℤ)) := by
        rintro ⟨hxe, hye⟩
        have hxe' : Even x.toNat := by exact_mod_cast hxe
        have hye' : Even y.toNat := by exact_mod_cast hye
        -- one of va, vb equals k; that odd part has padicValNat = 0, hence odd
        have hx_ne : x.toNat ≠ 0 := by
          rw [hxval]; intro h
          have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha_ne) hdvd_a)
            (Nat.two_pow_pos _); omega
        have hy_ne : y.toNat ≠ 0 := by
          rw [hyval]; intro h
          have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hb_ne) hdvd_b)
            (Nat.two_pow_pos _); omega
        rcases Nat.le_total va vb with hle | hle
        · -- k = va; x is the odd part of a
          have hkva : k = va := by rw [hkeq]; omega
          have hpx : padicValNat 2 x.toNat = 0 := by
            rw [hxval, hkva]
            have h_factor : a.toNat = 2 ^ va * (a.toNat / 2 ^ va) :=
              (Nat.mul_div_cancel' (hkva ▸ hdvd_a)).symm
            have hxne' : a.toNat / 2 ^ va ≠ 0 := by
              have := hx_ne; rw [hxval, hkva] at this; exact this
            have hkey : padicValNat 2 a.toNat
                = va + padicValNat 2 (a.toNat / 2 ^ va) := by
              conv_lhs => rw [h_factor]
              rw [padicValNat.mul (by positivity) hxne', padicValNat.prime_pow]
            omega
          have : ¬ (2 ∣ x.toNat) := by
            intro hdvd
            have := one_le_padicValNat_of_dvd hx_ne hdvd
            omega
          exact this hxe'.two_dvd
        · -- k = vb; y is the odd part of b
          have hkvb : k = vb := by rw [hkeq]; omega
          have hpy : padicValNat 2 y.toNat = 0 := by
            rw [hyval, hkvb]
            have h_factor : b.toNat = 2 ^ vb * (b.toNat / 2 ^ vb) :=
              (Nat.mul_div_cancel' (hkvb ▸ hdvd_b)).symm
            have hyne' : b.toNat / 2 ^ vb ≠ 0 := by
              have := hy_ne; rw [hyval, hkvb] at this; exact this
            have hkey : padicValNat 2 b.toNat
                = vb + padicValNat 2 (b.toNat / 2 ^ vb) := by
              conv_lhs => rw [h_factor]
              rw [padicValNat.mul (by positivity) hyne', padicValNat.prime_pow]
            omega
          have : ¬ (2 ∣ y.toNat) := by
            intro hdvd
            have := one_le_padicValNat_of_dvd hy_ne hdvd
            omega
          exact this hye'.two_dvd
      -- apply the loop invariant
      set fuel := 128 * (a.limbs.size + b.limbs.size) + 64 with hfuel
      have hU0 : (1 : AzInt).toInt * (x.toNat : ℤ) + (0 : AzInt).toInt * (y.toNat : ℤ)
          = (x.toNat : ℤ) := by simp [AzInt.toInt_zero, AzInt.toInt_one]
      have hV0 : (0 : AzInt).toInt * (x.toNat : ℤ) + (1 : AzInt).toInt * (y.toNat : ℤ)
          = (y.toNat : ℤ) := by simp [AzInt.toInt_zero, AzInt.toInt_one]
      set r := egcdLoop x y fuel fuel x y 1 0 0 1 with hr
      have hloop := egcdLoop_bezout x y hxy fuel fuel x y 1 0 0 1 hU0 hV0
      rw [← hr] at hloop
      -- final coefficients are r.2.1, r.2.2; gcd is r.1 <<< k
      have hshl : ((r.1 <<< k).toNat : ℤ) = (r.1.toNat : ℤ) * 2 ^ k := by
        rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]; push_cast; ring
      show r.2.1.toInt * (a.toNat : ℤ) + r.2.2.toInt * (b.toNat : ℤ)
        = ((r.1 <<< k).toNat : ℤ)
      rw [hshl]
      have hax' : (a.toNat : ℤ) = (x.toNat : ℤ) * 2 ^ k := by rw [hax]; push_cast; ring
      have hby' : (b.toNat : ℤ) = (y.toNat : ℤ) * 2 ^ k := by rw [hby]; push_cast; ring
      rw [hax', hby']
      -- hloop : r.2.1.toInt * x + r.2.2.toInt * y = r.1
      linear_combination (2 ^ k : ℤ) * hloop

/-! ## gcd-value equality for `egcd`

We now prove `(egcd a b).1.toNat = Nat.gcd a.toNat b.toNat`.  The architecture
mirrors `gcdOddLimbs_correct` in `Azurite/AzNat/Equiv/Gcd.lean`, but threads the
value-sum bound through *odd parts*.
-/

/-- The odd part of `n`: `n` divided by its largest power-of-two divisor. -/
private def oddpart (n : Nat) : Nat := n / 2 ^ padicValNat 2 n

private lemma odd_oddpart (n : Nat) (hn : n ≠ 0) : Odd (oddpart n) := by
  unfold oddpart
  obtain ⟨k, m, hm_odd, h_eq⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm_pos : m ≠ 0 := Odd.pos hm_odd |>.ne'
  have hk_eq : k = padicValNat 2 n := by
    rw [h_eq, padicValNat.mul (by positivity) hm_pos, padicValNat.prime_pow]
    have : padicValNat 2 m = 0 := by
      rw [padicValNat.eq_zero_of_not_dvd]
      intro h; have := hm_odd; rw [Nat.odd_iff] at this; omega
    omega
  rw [← hk_eq, h_eq, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm_odd

private lemma oddpart_pos (n : Nat) (hn : 0 < n) : 0 < oddpart n :=
  Odd.pos (odd_oddpart n hn.ne')

private lemma oddpart_eq_self_of_odd (n : Nat) (hn : Odd n) : oddpart n = n := by
  unfold oddpart
  have hpv : padicValNat 2 n = 0 := by
    rw [padicValNat.eq_zero_of_not_dvd]
    intro h; rw [Nat.odd_iff] at hn; omega
  rw [hpv]; simp

private lemma oddpart_mul_pow (n : Nat) :
    2 ^ padicValNat 2 n * oddpart n = n := by
  unfold oddpart
  exact Nat.mul_div_cancel' pow_padicValNat_dvd

private lemma oddpart_le_or_self (n : Nat) (hpos : 0 < n) : oddpart n ≤ n := by
  have hmul : 2 ^ padicValNat 2 n * oddpart n = n := oddpart_mul_pow n
  have hge : 1 ≤ 2 ^ padicValNat 2 n := Nat.one_le_two_pow
  have hopos : 0 < oddpart n := oddpart_pos n hpos
  nlinarith [hmul, hge, hopos]

private lemma oddpart_le_half_of_even (n : Nat) (hpos : 0 < n) (hev : Even n) :
    2 * oddpart n ≤ n := by
  have h1 : 1 ≤ padicValNat 2 n :=
    one_le_padicValNat_of_dvd hpos.ne' hev.two_dvd
  have hmul : 2 ^ padicValNat 2 n * oddpart n = n := oddpart_mul_pow n
  have hfac : 2 ^ padicValNat 2 n = 2 * 2 ^ (padicValNat 2 n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hge : 1 ≤ 2 ^ (padicValNat 2 n - 1) := Nat.one_le_two_pow
  nlinarith [hmul, hfac, hge, oddpart_pos n hpos]

private lemma oddpart_two_mul (m : Nat) (hm : 0 < m) :
    oddpart (2 * m) = oddpart m := by
  unfold oddpart
  have hpv : padicValNat 2 (2 * m) = 1 + padicValNat 2 m := by
    rw [padicValNat.mul (by norm_num) hm.ne', padicValNat.self (by norm_num)]
  rw [hpv, pow_add, pow_one, Nat.mul_div_mul_left _ _ (by norm_num)]

private lemma oddpart_div_two_of_even (n : Nat) (hpos : 0 < n) (hev : Even n) :
    oddpart (n / 2) = oddpart n := by
  obtain ⟨m, hm⟩ := hev
  have hm' : n = 2 * m := by omega
  have hmpos : 0 < m := by omega
  rw [hm', Nat.mul_div_cancel_left _ (by norm_num), oddpart_two_mul m hmpos]

/-- `Nat.gcd (oddpart n) m = Nat.gcd n m` when `n` even forces `m` odd. -/
private lemma gcd_oddpart_left (n m : Nat) (_hpos : 0 < n)
    (hcond : Even n → Odd m) : Nat.gcd (oddpart n) m = Nat.gcd n m := by
  by_cases hodd : Odd n
  · rw [oddpart_eq_self_of_odd n hodd]
  · have hev : Even n := Nat.not_odd_iff_even.mp hodd
    have hmodd : Odd m := hcond hev
    set v := padicValNat 2 n with hv
    have hdvd : 2 ^ v ∣ n := pow_padicValNat_dvd
    have hcop : Nat.Coprime (2 ^ v) m :=
      Nat.Coprime.pow_left v (Odd.coprime_two_left hmodd)
    have hfac : n = 2 ^ v * oddpart n := by
      unfold oddpart; rw [← hv]; exact (Nat.mul_div_cancel' hdvd).symm
    conv_rhs => rw [hfac]
    exact (hcop.gcd_mul_left_cancel _).symm

/-! ### Lemma A — `egcdMakeOdd` reaches the odd part -/

private lemma egcdMakeOdd_value (x y : AzNat) (fuel : Nat) (u : AzNat) (A B : AzInt)
    (hu : u.toNat ≠ 0) (hfuel : padicValNat 2 u.toNat ≤ fuel) :
    (egcdMakeOdd x y fuel u A B).1.toNat = oddpart u.toNat := by
  induction fuel generalizing u A B with
  | zero =>
    -- padicValNat 2 u.toNat = 0, so u is odd
    simp only [Nat.le_zero] at hfuel
    have hodd : Odd u.toNat := by
      rw [Nat.odd_iff]
      by_contra h
      have hev : Even u.toNat := by rw [Nat.even_iff]; omega
      have := one_le_padicValNat_of_dvd hu hev.two_dvd
      omega
    simp only [egcdMakeOdd]
    rw [oddpart_eq_self_of_odd _ hodd]
  | succ fuel ih =>
    simp only [egcdMakeOdd]
    by_cases hcond : u.isEven && !(u.limbs.size == 0)
    · rw [ite_eq_left hcond]
      have hue : u.isEven = true := by
        simp only [Bool.and_eq_true] at hcond; exact hcond.1
      have hev : Even u.toNat := (AzNat.isEven_iff u).mp hue
      have hpos : 0 < u.toNat := Nat.pos_of_ne_zero hu
      -- u' = u >>> 1 ; (u').toNat = u.toNat / 2
      have hu'val : (u >>> 1).toNat = u.toNat / 2 := by
        rw [AzNat.hShiftRight_eq, AzNat.toNat_shiftRight u 1, pow_one]
      have hu'ne : (u >>> 1).toNat ≠ 0 := by
        rw [hu'val]
        obtain ⟨m, hm⟩ := hev
        have : u.toNat / 2 = m := by omega
        rw [this]; omega
      have hpv' : padicValNat 2 (u >>> 1).toNat ≤ fuel := by
        rw [hu'val]
        have hkey : padicValNat 2 u.toNat = 1 + padicValNat 2 (u.toNat / 2) := by
          obtain ⟨m, hm⟩ := hev
          have hm' : u.toNat = 2 * m := by omega
          have hmpos : 0 < m := by omega
          rw [hm', Nat.mul_div_cancel_left _ (by norm_num)]
          rw [padicValNat.mul (by norm_num) hmpos.ne', padicValNat.self (by norm_num)]
        omega
      have hoddeq : oddpart (u >>> 1).toNat = oddpart u.toNat := by
        rw [hu'val, oddpart_div_two_of_even u.toNat hpos hev]
      -- The recursive call's first component depends only on u', not on AB.
      rw [ih (u >>> 1) _ _ hu'ne hpv', hoddeq]
    · rw [ite_eq_right hcond]
      -- u odd or size 0; size 0 contradicts hu
      have hsz_ne : ¬ (u.limbs.size = 0) := by
        intro h; exact hu ((AzNat.toNat_eq_zero_iff u).mpr h)
      have hodd : Odd u.toNat := by
        have hue : u.isEven = false := by
          by_contra hc
          have hue' : u.isEven = true := by
            cases hh : u.isEven with
            | false => exact absurd hh hc
            | true => rfl
          apply hcond
          simp only [Bool.and_eq_true, hue', Bool.not_eq_true', beq_eq_false_iff_ne,
            true_and, ne_eq]
          exact hsz_ne
        rw [Nat.odd_iff]
        by_contra hc
        have : Even u.toNat := by rw [Nat.even_iff]; omega
        rw [← AzNat.isEven_iff, hue] at this
        exact absurd this (by simp)
      rw [oddpart_eq_self_of_odd _ hodd]

/-! ### Lemma B — `egcdLoop` computes the gcd -/

private lemma egcdLoop_gcd (x y : AzNat) (G : Nat) (hG_odd : Odd G)
    (innerFuel fuel : Nat) (u v : AzNat) (A B C D : AzInt)
    (hu : 0 < u.toNat) (hv : 0 < v.toNat)
    (hgcd : Nat.gcd u.toNat v.toNat = G)
    (hbound : oddpart u.toNat + oddpart v.toNat ≤ 2 ^ fuel)
    (hinner : ∀ (w : AzNat), w.toNat ≤ u.toNat + v.toNat →
        padicValNat 2 w.toNat ≤ innerFuel) :
    (egcdLoop x y innerFuel fuel u v A B C D).1.toNat = G := by
  induction fuel generalizing u v A B C D with
  | zero =>
    exfalso
    have h1 : 0 < oddpart u.toNat := oddpart_pos _ hu
    have h2 : 0 < oddpart v.toNat := oddpart_pos _ hv
    simp only [pow_zero] at hbound; omega
  | succ fuel ih =>
    rw [egcdLoop]
    -- makeOdd on the U-side
    set su := egcdMakeOdd x y innerFuel u A B with hsu
    obtain ⟨u₁, A₁, B₁⟩ := su
    have hu₁ : u₁.toNat = oddpart u.toNat := by
      have := egcdMakeOdd_value x y innerFuel u A B hu.ne' (hinner u (by omega))
      rw [← hsu] at this; exact this
    -- makeOdd on the V-side
    set sv := egcdMakeOdd x y innerFuel v C D with hsv
    obtain ⟨v₁, C₁, D₁⟩ := sv
    have hv₁ : v₁.toNat = oddpart v.toNat := by
      have := egcdMakeOdd_value x y innerFuel v C D hv.ne' (hinner v (by omega))
      rw [← hsv] at this; exact this
    simp only
    -- Both odd parts are odd and positive
    have hu₁pos : 0 < u₁.toNat := by rw [hu₁]; exact oddpart_pos _ hu
    have hv₁pos : 0 < v₁.toNat := by rw [hv₁]; exact oddpart_pos _ hv
    have hu₁odd : Odd u₁.toNat := by rw [hu₁]; exact odd_oddpart _ hu.ne'
    have hv₁odd : Odd v₁.toNat := by rw [hv₁]; exact odd_oddpart _ hv.ne'
    -- gcd of odd parts is still G
    have hgcd₁ : Nat.gcd u₁.toNat v₁.toNat = G := by
      rw [hu₁, hv₁]
      -- gcd (oddpart u) (oddpart v) = gcd u (oddpart v) = gcd u v
      have step1 : Nat.gcd (oddpart u.toNat) (oddpart v.toNat)
          = Nat.gcd u.toNat (oddpart v.toNat) :=
        gcd_oddpart_left u.toNat (oddpart v.toNat) hu
          (fun _ => odd_oddpart _ hv.ne')
      have hcondV : Even v.toNat → Odd u.toNat := by
        intro hve
        rw [Nat.odd_iff]
        by_contra hc
        have hue : Even u.toNat := by rw [Nat.even_iff]; omega
        have : 2 ∣ Nat.gcd u.toNat v.toNat :=
          Nat.dvd_gcd hue.two_dvd hve.two_dvd
        rw [hgcd] at this
        rw [Nat.odd_iff] at hG_odd; omega
      have step2 : Nat.gcd (oddpart v.toNat) u.toNat = Nat.gcd v.toNat u.toNat :=
        gcd_oddpart_left v.toNat u.toNat hv hcondV
      rw [step1, Nat.gcd_comm u.toNat (oddpart v.toNat), step2,
          Nat.gcd_comm v.toNat u.toNat, hgcd]
    -- bound on oddparts is preserved; sum u₁ + v₁ ≤ u + v
    have hsum_le : u₁.toNat + v₁.toNat ≤ u.toNat + v.toNat := by
      rw [hu₁, hv₁]
      have ha := oddpart_le_or_self u.toNat hu
      have hb := oddpart_le_or_self v.toNat hv
      omega
    by_cases hcmp : AzNat.compare u₁ v₁ = Ordering.lt
    · rw [ite_eq_left hcmp]
      have hlt : u₁.toNat < v₁.toNat := by
        rw [AzNat.compare_eq_compare_toNat, Nat.compare_eq_lt] at hcmp; exact hcmp
      have hsub : (v₁ - u₁).toNat = v₁.toNat - u₁.toNat := by
        rw [AzNat.toNat_sub]
      have hsub_pos : 0 < (v₁ - u₁).toNat := by rw [hsub]; omega
      -- new gcd
      have hgcdnew : Nat.gcd u₁.toNat (v₁ - u₁).toNat = G := by
        rw [hsub, Nat.gcd_sub_self_right (le_of_lt hlt), hgcd₁]
      -- v₁ - u₁ is even (odd - odd) and positive
      have hdiffeven : Even (v₁.toNat - u₁.toNat) := by
        rw [Nat.even_iff]
        rw [Nat.odd_iff] at hu₁odd hv₁odd; omega
      have hdiffeven' : Even (v₁ - u₁).toNat := by rw [hsub]; exact hdiffeven
      -- new bound
      have hboundnew : oddpart u₁.toNat + oddpart (v₁ - u₁).toNat ≤ 2 ^ fuel := by
        have hou : oddpart u₁.toNat = u₁.toNat := oddpart_eq_self_of_odd _ hu₁odd
        have hhalf : 2 * oddpart (v₁ - u₁).toNat ≤ (v₁ - u₁).toNat :=
          oddpart_le_half_of_even _ hsub_pos hdiffeven'
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ]; ring
        have hb : oddpart u.toNat + oddpart v.toNat ≤ 2 ^ (fuel + 1) := hbound
        rw [← hu₁, ← hv₁] at hb
        rw [hou]
        -- hhalf : 2 * oddpart(v₁-u₁) ≤ (v₁-u₁).toNat = v₁ - u₁
        omega
      -- inner bound preserved
      have hinnernew : ∀ (w : AzNat), w.toNat ≤ u₁.toNat + (v₁ - u₁).toNat →
          padicValNat 2 w.toNat ≤ innerFuel := by
        intro w hw
        apply hinner w
        rw [hsub] at hw; omega
      exact ih u₁ (v₁ - u₁) A₁ B₁ (C₁ - A₁) (D₁ - B₁) hu₁pos hsub_pos hgcdnew
        hboundnew hinnernew
    · rw [ite_eq_right hcmp]
      have hge : v₁.toNat ≤ u₁.toNat := by
        rw [AzNat.compare_eq_compare_toNat] at hcmp
        rcases Nat.lt_trichotomy u₁.toNat v₁.toNat with h | h | h
        · exact absurd (Nat.compare_eq_lt.mpr h) hcmp
        · omega
        · omega
      have hsub : (u₁ - v₁).toNat = u₁.toNat - v₁.toNat := by rw [AzNat.toNat_sub]
      by_cases hsize : (u₁ - v₁).limbs.size == 0
      · rw [ite_eq_left hsize]
        -- u₁ = v₁, so G = gcd v₁ v₁ = v₁
        have hzero : (u₁ - v₁).toNat = 0 := by
          rw [AzNat.toNat_eq_zero_iff]; exact beq_iff_eq.mp hsize
        rw [hsub] at hzero
        have heq : u₁.toNat = v₁.toNat := by omega
        rw [← hgcd₁, heq, Nat.gcd_self]
      · rw [ite_eq_right hsize]
        have hsub_pos : 0 < (u₁ - v₁).toNat := by
          rw [Nat.pos_iff_ne_zero]
          intro h
          apply hsize
          rw [beq_iff_eq, ← AzNat.toNat_eq_zero_iff]; exact h
        have hgt : v₁.toNat < u₁.toNat := by rw [hsub] at hsub_pos; omega
        have hgcdnew : Nat.gcd (u₁ - v₁).toNat v₁.toNat = G := by
          rw [hsub, Nat.gcd_sub_self_left hge, hgcd₁]
        have hdiffeven : Even (u₁.toNat - v₁.toNat) := by
          rw [Nat.even_iff]; rw [Nat.odd_iff] at hu₁odd hv₁odd; omega
        have hdiffeven' : Even (u₁ - v₁).toNat := by rw [hsub]; exact hdiffeven
        have hboundnew : oddpart (u₁ - v₁).toNat + oddpart v₁.toNat ≤ 2 ^ fuel := by
          have hov : oddpart v₁.toNat = v₁.toNat := oddpart_eq_self_of_odd _ hv₁odd
          have hhalf : 2 * oddpart (u₁ - v₁).toNat ≤ (u₁ - v₁).toNat :=
            oddpart_le_half_of_even _ hsub_pos hdiffeven'
          have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ]; ring
          have hb : oddpart u.toNat + oddpart v.toNat ≤ 2 ^ (fuel + 1) := hbound
          rw [← hu₁, ← hv₁] at hb
          rw [hov]
          omega
        have hinnernew : ∀ (w : AzNat), w.toNat ≤ (u₁ - v₁).toNat + v₁.toNat →
            padicValNat 2 w.toNat ≤ innerFuel := by
          intro w hw
          apply hinner w
          rw [hsub] at hw; omega
        exact ih (u₁ - v₁) v₁ (A₁ - C₁) (B₁ - D₁) C₁ D₁ hsub_pos hv₁pos hgcdnew
          hboundnew hinnernew

/-! ### Lemma C — top-level gcd-value equality -/

/-- **gcd-value equality for `egcd`.**  With `(g, s, t) = egcd a b`,
`g = gcd a b`. -/
theorem egcd_gcd (a b : AzNat) :
    (egcd a b).1.toNat = Nat.gcd a.toNat b.toNat := by
  rw [egcd]
  by_cases ha0 : a.limbs.size = 0
  · simp only [ha0, ite_eq_left]
    rw [(AzNat.toNat_eq_zero_iff a).mpr ha0, Nat.gcd_zero_left]
  · simp only [ha0, ite_false]
    by_cases hb0 : b.limbs.size = 0
    · simp only [hb0, ite_eq_left]
      rw [(AzNat.toNat_eq_zero_iff b).mpr hb0, Nat.gcd_zero_right]
    · simp only [hb0]
      have ha_ne : a.toNat ≠ 0 := fun h => ha0 ((AzNat.toNat_eq_zero_iff a).mp h)
      have hb_ne : b.toNat ≠ 0 := fun h => hb0 ((AzNat.toNat_eq_zero_iff b).mp h)
      have ha_ne' : a ≠ 0 := fun h => ha_ne (by rw [h]; rfl)
      have hb_ne' : b ≠ 0 := fun h => hb_ne (by rw [h]; rfl)
      have ha_pos : 0 < a.toNat := Nat.pos_of_ne_zero ha_ne
      have hb_pos : 0 < b.toNat := Nat.pos_of_ne_zero hb_ne
      set va := padicValNat 2 a.toNat with hva
      set vb := padicValNat 2 b.toNat with hvb
      have htza : a.trailingZeros = some va :=
        AzNat.trailingZeros_eq_padicValNat a ha_ne'
      have htzb : b.trailingZeros = some vb :=
        AzNat.trailingZeros_eq_padicValNat b hb_ne'
      set k := min ((a.trailingZeros).getD 0) ((b.trailingZeros).getD 0) with hk
      have hkeq : k = min va vb := by rw [hk, htza, htzb]; rfl
      have hka : k ≤ va := by rw [hkeq]; exact Nat.min_le_left _ _
      have hkb : k ≤ vb := by rw [hkeq]; exact Nat.min_le_right _ _
      have hdvd_a : 2 ^ k ∣ a.toNat :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 hka) pow_padicValNat_dvd
      have hdvd_b : 2 ^ k ∣ b.toNat :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 hkb) pow_padicValNat_dvd
      set x := a >>> k with hxdef
      set y := b >>> k with hydef
      have hxval : x.toNat = a.toNat / 2 ^ k := by
        rw [hxdef, AzNat.hShiftRight_eq, AzNat.toNat_shiftRight a k]
      have hyval : y.toNat = b.toNat / 2 ^ k := by
        rw [hydef, AzNat.hShiftRight_eq, AzNat.toNat_shiftRight b k]
      have hax : a.toNat = 2 ^ k * x.toNat := by
        rw [hxval]; exact (Nat.mul_div_cancel' hdvd_a).symm
      have hby : b.toNat = 2 ^ k * y.toNat := by
        rw [hyval]; exact (Nat.mul_div_cancel' hdvd_b).symm
      have hx_pos : 0 < x.toNat := by
        rw [hxval]; exact Nat.div_pos (Nat.le_of_dvd ha_pos hdvd_a) (Nat.two_pow_pos _)
      have hy_pos : 0 < y.toNat := by
        rw [hyval]; exact Nat.div_pos (Nat.le_of_dvd hb_pos hdvd_b) (Nat.two_pow_pos _)
      -- x.toNat = oddpart a.toNat when k = va; similarly for y
      have hxodd_of : k = va → x.toNat = oddpart a.toNat := by
        intro h; rw [hxval, h, hva]; rfl
      have hyodd_of : k = vb → y.toNat = oddpart b.toNat := by
        intro h; rw [hyval, h, hvb]; rfl
      -- G = gcd x y is odd
      set G := Nat.gcd x.toNat y.toNat with hG
      have hG_odd : Odd G := by
        rcases Nat.le_total va vb with hle | hle
        · have hkva : k = va := by rw [hkeq]; omega
          have hxoddval : Odd x.toNat := by
            rw [hxodd_of hkva]; exact odd_oddpart _ ha_ne
          rw [hG]
          exact hxoddval.of_dvd_nat (Nat.gcd_dvd_left x.toNat y.toNat)
        · have hkvb : k = vb := by rw [hkeq]; omega
          have hyoddval : Odd y.toNat := by
            rw [hyodd_of hkvb]; exact odd_oddpart _ hb_ne
          rw [hG]
          exact hyoddval.of_dvd_nat (Nat.gcd_dvd_right x.toNat y.toNat)
      set fuel := 128 * (a.limbs.size + b.limbs.size) + 64 with hfuel
      -- bounds
      have hxlt : x.toNat < 2 ^ (64 * a.limbs.size) := by
        rw [hxval]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (AzNat.toNat_lt_pow a)
      have hylt : y.toNat < 2 ^ (64 * b.limbs.size) := by
        rw [hyval]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (AzNat.toNat_lt_pow b)
      have hbound : oddpart x.toNat + oddpart y.toNat ≤ 2 ^ fuel := by
        have hox : oddpart x.toNat ≤ x.toNat := oddpart_le_or_self _ hx_pos
        have hoy : oddpart y.toNat ≤ y.toNat := oddpart_le_or_self _ hy_pos
        have hsumlt : x.toNat + y.toNat <
            2 ^ (64 * a.limbs.size) + 2 ^ (64 * b.limbs.size) := by omega
        have hbig : 2 ^ (64 * a.limbs.size) + 2 ^ (64 * b.limbs.size) ≤ 2 ^ fuel := by
          have h1 : 64 * a.limbs.size ≤ fuel - 1 := by
            rw [hfuel]; omega
          have h2 : 64 * b.limbs.size ≤ fuel - 1 := by
            rw [hfuel]; omega
          have hf1 : 1 ≤ fuel := by rw [hfuel]; omega
          calc 2 ^ (64 * a.limbs.size) + 2 ^ (64 * b.limbs.size)
              ≤ 2 ^ (fuel - 1) + 2 ^ (fuel - 1) :=
                Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) h1)
                  (Nat.pow_le_pow_right (by norm_num) h2)
            _ = 2 ^ fuel := by
                rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hf1]
        omega
      have hinner : ∀ (w : AzNat), w.toNat ≤ x.toNat + y.toNat →
          padicValNat 2 w.toNat ≤ fuel := by
        intro w hw
        by_cases hw0 : w.toNat = 0
        · rw [hw0]; simp
        · have hwpos : 0 < w.toNat := Nat.pos_of_ne_zero hw0
          have hle : 2 ^ padicValNat 2 w.toNat ≤ w.toNat :=
            Nat.le_of_dvd hwpos pow_padicValNat_dvd
          have hsumlt : x.toNat + y.toNat < 2 ^ fuel := by
            have hox : oddpart x.toNat ≤ x.toNat := oddpart_le_or_self _ hx_pos
            -- reuse hbig-style bound: x + y < 2^(...) ≤ 2^fuel; strict
            have hbig : 2 ^ (64 * a.limbs.size) + 2 ^ (64 * b.limbs.size) ≤ 2 ^ fuel := by
              have h1 : 64 * a.limbs.size ≤ fuel - 1 := by rw [hfuel]; omega
              have h2 : 64 * b.limbs.size ≤ fuel - 1 := by rw [hfuel]; omega
              have hf1 : 1 ≤ fuel := by rw [hfuel]; omega
              calc 2 ^ (64 * a.limbs.size) + 2 ^ (64 * b.limbs.size)
                  ≤ 2 ^ (fuel - 1) + 2 ^ (fuel - 1) :=
                    Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) h1)
                      (Nat.pow_le_pow_right (by norm_num) h2)
                _ = 2 ^ fuel := by rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hf1]
            omega
          have hwlt : w.toNat < 2 ^ fuel := lt_of_le_of_lt hw hsumlt
          have : 2 ^ padicValNat 2 w.toNat < 2 ^ fuel :=
            lt_of_le_of_lt hle hwlt
          have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
          omega
      -- apply Lemma B
      set r := egcdLoop x y fuel fuel x y 1 0 0 1 with hr
      have hloop := egcdLoop_gcd x y G hG_odd fuel fuel x y 1 0 0 1
        hx_pos hy_pos hG.symm hbound hinner
      rw [← hr] at hloop
      -- (r.1 <<< k).toNat = r.1.toNat * 2^k = G * 2^k
      show (r.1 <<< k).toNat = Nat.gcd a.toNat b.toNat
      rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, hloop]
      rw [hax, hby, Nat.gcd_mul_left, ← hG]
      ring

end Azurite.AzInt
