/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Conversion
import Azurite.AzInt.Equiv.Mul
import Azurite.AzInt.Equiv.MulSmall
import Azurite.AzInt.Equiv.ShiftLeft
import Azurite.AzInt.Equiv.Sub
import Azurite.AzInt.Equiv.TrailingZeros
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Gcd.Binary
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.TrailingZeros
import Azurite.AzNat.Gcd.HalfBinary
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
## Correctness of the half-binary GCD

The proof rests on the **determinant invariant** alone: every matrix returned by
`halfBinaryGcd` has determinant `±2^{2j}` (`natAbs_detInt_halfBinaryGcd`), and applying such a
matrix with exact division by `2^{2j}`, performing a binary division with *any* quotient, or
dividing out an exact power of two all preserve the **odd part of the GCD**
(`OddEquiv`).  Since the driver starts from an odd first operand, that odd part is the GCD itself.
-/

namespace Azurite.AzNat

open Azurite.AzInt

/-! ### Determinants -/

/-- The determinant of a `Mat2`, as an integer. -/
def Mat2.detInt (R : Mat2) : ℤ := R.a.toInt * R.d.toInt - R.b.toInt * R.c.toInt

/-- The determinant of a base-case matrix `(m₁₁, m₁₂, m₂₁, m₂₂)`. -/
def detInts (M : Int × Int × Int × Int) : ℤ := M.1 * M.2.2.2 - M.2.1 * M.2.2.1

theorem Mat2.detInt_one : Mat2.one.detInt = 1 := by
  simp [Mat2.detInt, Mat2.one]

theorem Mat2.detInt_mul (S T : Mat2) : (S.mul T).detInt = S.detInt * T.detInt := by
  simp only [Mat2.detInt, Mat2.mul, toInt_add, toInt_mul]; ring

theorem Mat2.detInt_stepMul (j : ℕ) (q : AzInt) (R : Mat2) :
    (Mat2.stepMul j q R).detInt = -((2 : ℤ) ^ j) ^ 2 * R.detInt := by
  simp only [Mat2.detInt, Mat2.stepMul, toInt_add, toInt_mul, toInt_hShiftLeft]; ring

theorem Mat2.natAbs_detInt_mul_stepMul (S R : Mat2) (j₁ j₀ j₂ : ℕ) (q : AzInt)
    (hS : S.detInt.natAbs = 2 ^ (2 * j₂)) (hR : R.detInt.natAbs = 2 ^ (2 * j₁)) :
    (S.mul (Mat2.stepMul j₀ q R)).detInt.natAbs = 2 ^ (2 * (j₁ + j₀ + j₂)) := by
  have h2 : (2 : ℤ).natAbs = 2 := rfl
  rw [Mat2.detInt_mul, Mat2.detInt_stepMul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_neg,
    Int.natAbs_pow, Int.natAbs_pow, h2, hS, hR]
  ring

/-! ### Conversions -/

theorem toInt_ofBoundedInt? (x : ℤ) (z : AzInt) (h : AzInt.ofBoundedInt? x = some z) :
    z.toInt = x := by
  unfold AzInt.ofBoundedInt? at h
  split_ifs at h with hlt hx
  · have hu : x.natAbs.toUInt64.toNat = x.natAbs := UInt64.toNat_ofNat_of_lt hlt
    obtain rfl := Option.some.inj h
    rw [UInt64.toInt_toAzInt, hu, Int.natAbs_of_nonneg hx]
  · have hu : x.natAbs.toUInt64.toNat = x.natAbs := UInt64.toNat_ofNat_of_lt hlt
    obtain rfl := Option.some.inj h
    rw [toInt_neg, UInt64.toInt_toAzInt, hu,
      Int.ofNat_natAbs_of_nonpos (le_of_lt (not_le.mp hx)), neg_neg]

theorem detInt_ofInts? (M : Int × Int × Int × Int) (R : Mat2) (h : Mat2.ofInts? M = some R) :
    R.detInt = detInts M := by
  unfold Mat2.ofInts? at h
  split at h
  · rename_i a b c d ha hb hc hd
    obtain rfl := Option.some.inj h
    simp only [Mat2.detInt, detInts, toInt_ofBoundedInt? _ _ ha, toInt_ofBoundedInt? _ _ hb,
      toInt_ofBoundedInt? _ _ hc, toInt_ofBoundedInt? _ _ hd]
  · exact absurd h (by simp)

/-- `toInt` of `mkNorm`, uniformly in the sign. -/
theorem toInt_mkNorm (s : Bool) (n : AzNat) :
    (AzInt.mkNorm s n).toInt = if s then (n.toNat : ℤ) else -(n.toNat : ℤ) := by
  by_cases hn : n = 0
  · subst hn; rw [toInt_mkNorm_zero]; simp [AzNat.toNat_zero]
  · cases s
    · exact toInt_mkNorm_false n hn
    · exact toInt_mkNorm_true n

theorem toInt_eq_ite (z : AzInt) : z.toInt = if z.sign then (z.abs.toNat : ℤ) else -(z.abs.toNat : ℤ) :=
  rfl

/-- The 2-adic valuation of an integer is that of its magnitude. -/
theorem padicValInt_toInt (z : AzInt) : padicValInt 2 z.toInt = padicValNat 2 z.abs.toNat := by
  unfold padicValInt
  rw [← AzInt.toNat_natAbs]; rfl

/-! ### Exact shifts and odd parts -/

theorem abs_toNat_ne_zero (z : AzInt) (hz : z ≠ 0) : z.abs.toNat ≠ 0 := by
  intro h0
  apply hz
  have habs : z.abs = 0 := AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])
  have := z.zero_sign habs
  rcases z with ⟨sign, abs, zs⟩
  simp only at habs this
  subst habs; subst this
  rfl

theorem toInt_exactShiftRight (z : AzInt) (m : ℕ) (w : AzInt) (h : z.exactShiftRight m = some w) :
    w.toInt * 2 ^ m = z.toInt := by
  unfold AzInt.exactShiftRight at h
  by_cases hz : z = 0
  · subst hz
    rw [AzInt.trailingZeros_zero] at h
    obtain rfl := Option.some.inj h
    simp
  · rw [AzInt.trailingZeros_eq_padicValInt z hz] at h
    simp only at h
    split_ifs at h with hle
    obtain rfl := Option.some.inj h
    rw [padicValInt_toInt] at hle
    have habs := abs_toNat_ne_zero z hz
    have hdvd : 2 ^ m ∣ z.abs.toNat := (padicValNat_dvd_iff_le habs).mpr hle
    rw [toInt_mkNorm, toInt_eq_ite, toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_div_cancel_left c (Nat.two_pow_pos m)]
    push_cast
    split_ifs <;> ring

/-- `oddPart` computes `n / 2^ν(n)`. -/
theorem toNat_oddPart (n : AzNat) : (oddPart n).toNat = n.toNat / 2 ^ padicValNat 2 n.toNat := by
  unfold oddPart
  by_cases hn : n = 0
  · subst hn; rw [trailingZeros_zero]; simp
  · rw [trailingZeros_eq_padicValNat n hn, toNat_hShiftRight, Nat.shiftRight_eq_div_pow]

/-! ### Odd parts of GCDs -/

/-- `m` and `n` have the same odd divisors. -/
def OddEquiv (m n : ℕ) : Prop := ∀ g : ℕ, Odd g → (g ∣ m ↔ g ∣ n)

theorem OddEquiv.refl (m : ℕ) : OddEquiv m m := fun _ _ => Iff.rfl
theorem OddEquiv.symm {m n : ℕ} (h : OddEquiv m n) : OddEquiv n m := fun g hg => (h g hg).symm
theorem OddEquiv.trans {m n p : ℕ} (h₁ : OddEquiv m n) (h₂ : OddEquiv n p) : OddEquiv m p :=
  fun g hg => (h₁ g hg).trans (h₂ g hg)

/-- Odd numbers are coprime to powers of two. -/
theorem odd_coprime_two_pow {g : ℕ} (hg : Odd g) (k : ℕ) : Nat.Coprime g (2 ^ k) :=
  Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hg)

theorem odd_dvd_two_pow_mul_iff {g : ℕ} (hg : Odd g) (k n : ℕ) : g ∣ 2 ^ k * n ↔ g ∣ n :=
  ⟨fun h => (odd_coprime_two_pow hg k).dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩

theorem odd_dvd_two_pow_mul_int_iff {g : ℕ} (hg : Odd g) (k : ℕ) (n : ℤ) :
    (g : ℤ) ∣ 2 ^ k * n ↔ (g : ℤ) ∣ n := by
  rw [Int.natCast_dvd, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow]
  exact odd_dvd_two_pow_mul_iff hg k n.natAbs

theorem nat_dvd_int_gcd_iff (g : ℕ) (a b : ℤ) : g ∣ Int.gcd a b ↔ (g : ℤ) ∣ a ∧ (g : ℤ) ∣ b := by
  constructor
  · intro h
    have h' : (g : ℤ) ∣ (Int.gcd a b : ℤ) := Int.natCast_dvd_natCast.mpr h
    exact ⟨h'.trans (Int.gcd_dvd_left a b), h'.trans (Int.gcd_dvd_right a b)⟩
  · intro ⟨ha, hb⟩
    exact Int.dvd_gcd ha hb

theorem oddEquiv_zero_iff {m n : ℕ} (h : OddEquiv m n) : m = 0 ↔ n = 0 := by
  have key : ∀ m n : ℕ, OddEquiv m n → m = 0 → n = 0 := by
    intro m n h hm
    subst hm
    by_contra hn
    have h1 : (2 * n + 1) ∣ n := (h (2 * n + 1) ⟨n, rfl⟩).mp (dvd_zero _)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1
    omega
  exact ⟨key m n h, key n m h.symm⟩

/-- The odd part of `n`. -/
def oddPartNat (n : ℕ) : ℕ := n / 2 ^ padicValNat 2 n

theorem two_pow_padicValNat_mul_oddPartNat (n : ℕ) : 2 ^ padicValNat 2 n * oddPartNat n = n :=
  Nat.mul_div_cancel' pow_padicValNat_dvd

theorem odd_oddPartNat {n : ℕ} (hn : n ≠ 0) : Odd (oddPartNat n) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  have h : 2 ^ (padicValNat 2 n + 1) ∣ n := by
    rw [pow_succ]
    calc 2 ^ padicValNat 2 n * 2 ∣ 2 ^ padicValNat 2 n * oddPartNat n := Nat.mul_dvd_mul_left _ h2
      _ = n := two_pow_padicValNat_mul_oddPartNat n
  rw [padicValNat_dvd_iff_le hn] at h
  omega

theorem odd_dvd_iff_dvd_oddPartNat {g : ℕ} (hg : Odd g) (n : ℕ) : g ∣ n ↔ g ∣ oddPartNat n := by
  conv_lhs => rw [← two_pow_padicValNat_mul_oddPartNat n]
  exact odd_dvd_two_pow_mul_iff hg _ _

theorem oddPartNat_eq_of_oddEquiv {m n : ℕ} (h : OddEquiv m n) : oddPartNat m = oddPartNat n := by
  by_cases hm : m = 0
  · have hn : n = 0 := (oddEquiv_zero_iff h).mp hm
    subst hm; subst hn; rfl
  · have hn : n ≠ 0 := fun hn => hm ((oddEquiv_zero_iff h).mpr hn)
    apply Nat.dvd_antisymm
    · rw [← odd_dvd_iff_dvd_oddPartNat (odd_oddPartNat hm), ← h _ (odd_oddPartNat hm),
        odd_dvd_iff_dvd_oddPartNat (odd_oddPartNat hm)]
    · rw [← odd_dvd_iff_dvd_oddPartNat (odd_oddPartNat hn), h _ (odd_oddPartNat hn),
        odd_dvd_iff_dvd_oddPartNat (odd_oddPartNat hn)]

theorem oddPartNat_of_odd {n : ℕ} (hn : Odd n) : oddPartNat n = n := by
  unfold oddPartNat
  rw [padicValNat.eq_zero_of_not_dvd (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hn)]
  simp

/-- A matrix of determinant `±2^{2j}`, applied with exact division by `2^{2j}`, preserves the odd
part of the GCD. -/
theorem oddEquiv_gcd_of_mat (r₁₁ r₁₂ r₂₁ r₂₂ a b c d : ℤ) (j : ℕ)
    (hdet : (r₁₁ * r₂₂ - r₁₂ * r₂₁).natAbs = 2 ^ (2 * j))
    (hc : r₁₁ * a + r₁₂ * b = 2 ^ (2 * j) * c) (hd : r₂₁ * a + r₂₂ * b = 2 ^ (2 * j) * d) :
    OddEquiv (Int.gcd a b) (Int.gcd c d) := by
  intro g hg
  rw [nat_dvd_int_gcd_iff, nat_dvd_int_gcd_iff]
  constructor
  · intro ⟨ha, hb⟩
    constructor
    · rw [← odd_dvd_two_pow_mul_int_iff hg (2 * j) c, ← hc]
      exact Dvd.dvd.add (Dvd.dvd.mul_left ha _) (Dvd.dvd.mul_left hb _)
    · rw [← odd_dvd_two_pow_mul_int_iff hg (2 * j) d, ← hd]
      exact Dvd.dvd.add (Dvd.dvd.mul_left ha _) (Dvd.dvd.mul_left hb _)
  · intro ⟨hc', hd'⟩
    have ha : (r₁₁ * r₂₂ - r₁₂ * r₂₁) * a = 2 ^ (2 * j) * (r₂₂ * c - r₁₂ * d) := by
      linear_combination r₂₂ * hc - r₁₂ * hd
    have hb : (r₁₁ * r₂₂ - r₁₂ * r₂₁) * b = 2 ^ (2 * j) * (r₁₁ * d - r₂₁ * c) := by
      linear_combination r₁₁ * hd - r₂₁ * hc
    have hpos : (2 : ℤ) ^ (2 * j) ≠ 0 := by positivity
    have hga : (g : ℤ) ∣ r₂₂ * c - r₁₂ * d :=
      Dvd.dvd.sub (Dvd.dvd.mul_left hc' _) (Dvd.dvd.mul_left hd' _)
    have hgb : (g : ℤ) ∣ r₁₁ * d - r₂₁ * c :=
      Dvd.dvd.sub (Dvd.dvd.mul_left hd' _) (Dvd.dvd.mul_left hc' _)
    rcases Int.natAbs_eq_iff.mp hdet with h | h
    · push_cast at h
      rw [h] at ha hb
      exact ⟨by rw [mul_left_cancel₀ hpos ha]; exact hga,
        by rw [mul_left_cancel₀ hpos hb]; exact hgb⟩
    · push_cast at h
      rw [h, neg_mul, neg_eq_iff_eq_neg, ← mul_neg] at ha hb
      exact ⟨by rw [mul_left_cancel₀ hpos ha]; exact hga.neg_right,
        by rw [mul_left_cancel₀ hpos hb]; exact hgb.neg_right⟩

/-- A binary-division step `(a, 2^j b'') ↦ (b'', a + q b'')` preserves the odd part of the GCD,
whatever the quotient `q`. -/
theorem oddEquiv_gcd_binaryStep (a b'' q : ℤ) (j : ℕ) :
    OddEquiv (Int.gcd a (b'' * 2 ^ j)) (Int.gcd b'' (a + q * b'')) := by
  intro g hg
  rw [nat_dvd_int_gcd_iff, nat_dvd_int_gcd_iff, mul_comm b'', odd_dvd_two_pow_mul_int_iff hg]
  constructor
  · intro ⟨ha, hb⟩
    exact ⟨hb, Dvd.dvd.add ha (Dvd.dvd.mul_left hb _)⟩
  · intro ⟨hb, hr⟩
    refine ⟨?_, hb⟩
    have := Dvd.dvd.sub hr (Dvd.dvd.mul_left hb q)
    simpa using this

/-- Dividing one operand by an exact power of two preserves the odd part of the GCD. -/
theorem oddEquiv_gcd_div_pow (x y : ℤ) (j : ℕ) : OddEquiv (Int.gcd x (y * 2 ^ j)) (Int.gcd x y) := by
  intro g hg
  rw [nat_dvd_int_gcd_iff, nat_dvd_int_gcd_iff, mul_comm y, odd_dvd_two_pow_mul_int_iff hg]

/-! ### Determinant invariant -/

theorem natAbs_detInts_go (k : ℕ) :
    ∀ (fuel : ℕ) (A B : UInt64) (j : ℕ) (M : Int × Int × Int × Int),
      (detInts M).natAbs = 2 ^ (2 * j) →
      (detInts (halfBinaryGcdWord.go k fuel A B j M).2).natAbs =
        2 ^ (2 * (halfBinaryGcdWord.go k fuel A B j M).1) := by
  intro fuel
  induction fuel with
  | zero => intro A B j M h; exact h
  | succ fuel ih =>
    intro A B j M h
    rw [halfBinaryGcdWord.go]
    dsimp only
    split_ifs with hB hk
    · exact h
    · exact h
    all_goals
      apply ih
      have hstep : ∀ (p q m₁₁ m₁₂ m₂₁ m₂₂ : ℤ),
          detInts (p * m₂₁, p * m₂₂, p * m₁₁ + q * m₂₁, p * m₁₂ + q * m₂₂) =
            -p ^ 2 * detInts (m₁₁, m₁₂, m₂₁, m₂₂) := by
        intro p q m₁₁ m₁₂ m₂₁ m₂₂; simp only [detInts]; ring
      have h2 : (2 : ℤ).natAbs = 2 := rfl
      rw [hstep, Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_pow, Int.natAbs_pow, h2, h]
      ring

theorem natAbs_detInts_halfBinaryGcdWord (A B : UInt64) (k : ℕ) :
    (detInts (halfBinaryGcdWord A B k).2).natAbs = 2 ^ (2 * (halfBinaryGcdWord A B k).1) :=
  natAbs_detInts_go k (k + 1) A B 0 (1, 0, 0, 1) (by simp [detInts])

/-- Every matrix returned by `halfBinaryGcd` has determinant `±2^{2j}`. -/
theorem natAbs_detInt_halfBinaryGcd (fuel : ℕ) :
    ∀ (a b : AzInt) (k : ℕ),
      (halfBinaryGcd fuel a b k).2.detInt.natAbs = 2 ^ (2 * (halfBinaryGcd fuel a b k).1) := by
  induction fuel with
  | zero => intro a b k; simp [halfBinaryGcd, Mat2.detInt_one]
  | succ fuel ih =>
    intro a b k
    rw [halfBinaryGcd]
    split_ifs with hk
    · dsimp only
      split
      · rename_i M hM
        rw [detInt_ofInts? _ _ hM]
        exact natAbs_detInts_halfBinaryGcdWord _ _ _
      · simp [Mat2.detInt_one]
    · dsimp only
      split
      · exact ih _ _ _
      · split_ifs
        · exact ih _ _ _
        · exact Mat2.natAbs_detInt_mul_stepMul _ _ _ _ _ _ (ih _ _ _) (ih _ _ _)

/-! ### The driver -/

theorem toInt_apply_fst (R : Mat2) (x y : AzInt) :
    (R.apply x y).1.toInt = R.a.toInt * x.toInt + R.b.toInt * y.toInt := by
  simp [Mat2.apply, toInt_add, toInt_mul]

theorem toInt_apply_snd (R : Mat2) (x y : AzInt) :
    (R.apply x y).2.toInt = R.c.toInt * x.toInt + R.d.toInt * y.toInt := by
  simp [Mat2.apply, toInt_add, toInt_mul]

theorem toInt_snd_binaryDivide (a b' : AzInt) (j : ℕ) :
    (binaryDivide a b' j).2.toInt = a.toInt + (binaryDivide a b' j).1.toInt * b'.toInt := by
  unfold binaryDivide
  dsimp only
  split_ifs
  · simp only [toInt_add, toInt_mul]
  · simp only [toInt_add, toInt_mul]
  · simp

/-- `oddPart (gcdBinary |x| |y|)` is the odd part of `gcd x y`. -/
theorem toNat_oddPart_gcdBinary (x y : AzInt) :
    (oddPart (gcdBinary x.abs y.abs)).toNat = oddPartNat (Int.gcd x.toInt y.toInt) := by
  rw [toNat_oddPart, toNat_gcdBinary]
  show _ = oddPartNat (Nat.gcd x.toInt.natAbs y.toInt.natAbs)
  rw [← AzInt.toNat_natAbs, ← AzInt.toNat_natAbs]; rfl

theorem toInt_mkNorm_shift_of_trailingZeros (b : AzInt) (j : ℕ) (h : b.trailingZeros = some j) :
    (AzInt.mkNorm b.sign (b.abs >>> j)).toInt * 2 ^ j = b.toInt := by
  have hb : b ≠ 0 := fun h0 => by
    rw [h0, AzInt.trailingZeros_zero] at h; cases h
  apply toInt_exactShiftRight b j
  unfold AzInt.exactShiftRight
  rw [h]
  simp

theorem toNat_halfBinaryGcdDriver (threshold fuel : ℕ) :
    ∀ a b : AzInt,
      (halfBinaryGcdDriver threshold fuel a b).toNat = oddPartNat (Int.gcd a.toInt b.toInt) := by
  induction fuel with
  | zero => intro a b; exact toNat_oddPart_gcdBinary a b
  | succ fuel ih =>
    intro a b
    rw [halfBinaryGcdDriver]
    split_ifs with hn
    · exact toNat_oddPart_gcdBinary a b
    · dsimp only
      split
      · rename_i a' b' ha' hb'
        -- the matrix step
        have hdet := natAbs_detInt_halfBinaryGcd (max a.size b.size / 2 + 1)
          (a.lowBits (2 * (max a.size b.size / 2) + 1)) (b.lowBits (2 * (max a.size b.size / 2) + 1))
          (max a.size b.size / 2)
        have hc := toInt_exactShiftRight _ _ _ ha'
        have hd := toInt_exactShiftRight _ _ _ hb'
        rw [toInt_apply_fst] at hc
        rw [toInt_apply_snd] at hd
        have hmat : OddEquiv (Int.gcd a.toInt b.toInt) (Int.gcd a'.toInt b'.toInt) :=
          oddEquiv_gcd_of_mat _ _ _ _ _ _ _ _ _ hdet (by rw [← hc]; ring) (by rw [← hd]; ring)
        rw [← oddPartNat_eq_of_oddEquiv hmat.symm]
        split
        · rename_i hz
          have hb0 : b' = 0 := by
            by_contra hne
            rw [AzInt.trailingZeros_eq_padicValInt b' hne] at hz
            cases hz
          subst hb0
          rw [toNat_oddPart, toInt_zero, Int.gcd_zero_right]
          have : a'.abs.toNat = a'.toInt.natAbs := AzInt.toNat_natAbs a'
          rw [this]; rfl
        · rename_i j₀ hj₀
          have hb'' := toInt_mkNorm_shift_of_trailingZeros b' j₀ hj₀
          have hstep : OddEquiv (Int.gcd a'.toInt b'.toInt)
              (Int.gcd (AzInt.mkNorm b'.sign (b'.abs >>> j₀)).toInt
                (binaryDivide a' (AzInt.mkNorm b'.sign (b'.abs >>> j₀)) j₀).2.toInt) := by
            rw [toInt_snd_binaryDivide, ← hb'']
            exact oddEquiv_gcd_binaryStep _ _ _ _
          rw [oddPartNat_eq_of_oddEquiv hstep]
          split
          · rename_i r' hr'
            rw [ih]
            have hr := toInt_exactShiftRight _ _ _ hr'
            rw [← hr]
            exact (oddPartNat_eq_of_oddEquiv (oddEquiv_gcd_div_pow _ _ _)).symm
          · exact toNat_oddPart_gcdBinary _ _
      · exact toNat_oddPart_gcdBinary a b

/-! ### The `AzNat` entry point -/

/-- `gcdHalfBinaryWith` computes `Nat.gcd` at every threshold. -/
theorem toNat_gcdHalfBinaryWith (threshold : ℕ) (a b : AzNat) :
    (gcdHalfBinaryWith threshold a b).toNat = Nat.gcd a.toNat b.toNat := by
  unfold gcdHalfBinaryWith
  by_cases ha : a = 0
  · subst ha; rw [trailingZeros_zero]; simp
  by_cases hb : b = 0
  · subst hb; rw [trailingZeros_eq_padicValNat a ha, trailingZeros_zero]; simp
  have ha' : a.toNat ≠ 0 := fun h => ha (toNat_injective (by rw [h, toNat_zero]))
  have hb' : b.toNat ≠ 0 := fun h => hb (toNat_injective (by rw [h, toNat_zero]))
  rw [trailingZeros_eq_padicValNat a ha, trailingZeros_eq_padicValNat b hb]
  dsimp only
  have key : ∀ (x y : AzNat) (t : ℕ), Odd x.toNat →
      ((halfBinaryGcdDriver threshold (max x.size (if y.isOdd then x + y else y).size + 1) x.toAzInt
        (if y.isOdd then x + y else y).toAzInt) <<< t).toNat = Nat.gcd x.toNat y.toNat * 2 ^ t := by
    intro x y t hx
    rw [toNat_hShiftLeft, Nat.shiftLeft_eq, toNat_halfBinaryGcdDriver, AzNat.toInt_toAzInt,
      AzNat.toInt_toAzInt, Int.gcd_natCast_natCast]
    congr 1
    have hodd : ∀ n, Odd (Nat.gcd x.toNat n) := fun n => hx.of_dvd_nat (Nat.gcd_dvd_left _ _)
    split_ifs with hy
    · rw [oddPartNat_of_odd (hodd _), toNat_add, Nat.gcd_self_add_right]
    · exact oddPartNat_of_odd (hodd _)
  have hshift : ∀ (n : AzNat) (t : ℕ), (n >>> t).toNat = n.toNat / 2 ^ t := fun n t => by
    rw [toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
  have hfin : ∀ (x y : ℕ) (t : ℕ), 2 ^ t ∣ x → 2 ^ t ∣ y →
      Nat.gcd (x / 2 ^ t) (y / 2 ^ t) * 2 ^ t = Nat.gcd x y := fun x y t hx hy => by
    rw [Nat.gcd_div hx hy, Nat.div_mul_cancel (Nat.dvd_gcd hx hy)]
  by_cases hle : padicValNat 2 a.toNat ≤ padicValNat 2 b.toNat
  · rw [ite_eq_left hle, ite_eq_left hle, Nat.min_eq_left hle]
    rw [key _ _ _ (by rw [hshift]; exact odd_oddPartNat ha'), hshift, hshift]
    exact hfin _ _ _ pow_padicValNat_dvd ((padicValNat_dvd_iff_le hb').mpr hle)
  · have hlt := le_of_lt (not_le.mp hle)
    rw [ite_eq_right hle, ite_eq_right hle, Nat.min_eq_right hlt]
    rw [key _ _ _ (by rw [hshift]; exact odd_oddPartNat hb'), hshift, hshift, Nat.gcd_comm]
    exact hfin _ _ _ ((padicValNat_dvd_iff_le ha').mpr hlt) pow_padicValNat_dvd

/-- `gcdHalfBinary` computes `Nat.gcd`. -/
theorem toNat_gcdHalfBinary (a b : AzNat) : (gcdHalfBinary a b).toNat = Nat.gcd a.toNat b.toNat :=
  toNat_gcdHalfBinaryWith _ a b

end Azurite.AzNat
