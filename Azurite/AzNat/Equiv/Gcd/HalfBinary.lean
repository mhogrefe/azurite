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
import Azurite.AzNat.Equiv.Pow2
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.Sub
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

/-- The determinant of a base-case matrix, as an integer. -/
def detInts (M : WordMat) : ℤ := M.m₁₁.toInt * M.m₂₂.toInt - M.m₁₂.toInt * M.m₂₁.toInt



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

theorem detInt_ofWord (M : WordMat) : (Mat2.ofWord M).detInt = detInts M := by
  simp only [Mat2.detInt, Mat2.ofWord, detInts, Int64.toInt_toAzInt]

/-- `toInt` of `mkNorm`, uniformly in the sign. -/
theorem toInt_mkNorm (s : Bool) (n : AzNat) :
    (AzInt.mkNorm s n).toInt = if s then (n.toNat : ℤ) else -(n.toNat : ℤ) := by
  by_cases hn : n = 0
  · subst hn; rw [toInt_mkNorm_zero]; simp [AzNat.toNat_zero]
  · cases s
    · exact toInt_mkNorm_false n hn
    · exact toInt_mkNorm_true n

theorem toInt_eq_ite (z : AzInt) :
    z.toInt = if z.sign then (z.abs.toNat : ℤ) else -(z.abs.toNat : ℤ) :=
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
theorem oddEquiv_gcd_div_pow (x y : ℤ) (j : ℕ) :
    OddEquiv (Int.gcd x (y * 2 ^ j)) (Int.gcd x y) := by
  intro g hg
  rw [nat_dvd_int_gcd_iff, nat_dvd_int_gcd_iff, mul_comm y, odd_dvd_two_pow_mul_int_iff hg]

/-! ### Determinant invariant -/

/-- `Int64` arithmetic is exact on results of magnitude at most `2^62`. -/
theorem bmod_two_pow_64_of_abs_le {x : ℤ} (h : |x| ≤ 2 ^ 62) : x.bmod (2 ^ 64) = x := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp h
  apply Int.bmod_eq_of_le <;> norm_num <;> linarith

/-- Reinterpreting a word below `2^63` as an `Int64` keeps its value. -/
theorem toInt_toInt64_of_lt (u : UInt64) (h : u.toNat < 2 ^ 63) : u.toInt64.toInt = u.toNat := by
  rw [← Int64.toInt_toBitVec, UInt64.toBitVec_toInt64]
  exact BitVec.toInt_eq_toNat_of_lt (by show 2 * u.toNat < 2 ^ 64; omega)

theorem toNat_one_shiftLeft (j : ℕ) (hj : j < 64) :
    ((1 : UInt64) <<< j.toUInt64).toNat = 2 ^ j := by
  have hsz : 64 < UInt64.size := by decide
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_one, UInt64.toNat_ofNat_of_lt' (by omega),
    Nat.mod_eq_of_lt hj, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj)]

theorem toNat_two_mul_half (j : ℕ) (hj : j ≤ 62) :
    (2 * ((1 : UInt64) <<< j.toUInt64)).toNat = 2 * 2 ^ j := by
  rw [UInt64.toNat_mul, toNat_one_shiftLeft j (by omega)]
  have h2 : (2 : UInt64).toNat = 2 := rfl
  rw [h2]
  apply Nat.mod_eq_of_lt
  have : 2 ^ j ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hj
  have : (2 : ℕ) * 2 ^ 62 < 2 ^ 64 := by norm_num
  omega

theorem toNat_mask (j : ℕ) (hj : j ≤ 62) :
    (2 * ((1 : UInt64) <<< j.toUInt64) - 1).toNat = 2 * 2 ^ j - 1 := by
  have hle : (1 : UInt64) ≤ 2 * ((1 : UInt64) <<< j.toUInt64) := by
    rw [UInt64.le_iff_toNat_le, toNat_two_mul_half j hj, UInt64.toNat_one]
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  rw [UInt64.toNat_sub_of_le _ _ hle, toNat_two_mul_half j hj, UInt64.toNat_one]

/-- The base case's entry check, read in `ℤ`: `-bound ≤ m ≤ bound` with
`bound = 2^{61 − j₀}` (as an `Int64`) means `|m| ≤ 2^{61 − j₀}`. -/
theorem abs_toInt_le_of_check (m : Int64) (j₀ : ℕ) (hj : j₀ ≤ 61)
    (h₁ : -((1 : UInt64) <<< (61 - j₀).toUInt64).toInt64 ≤ m)
    (h₂ : m ≤ ((1 : UInt64) <<< (61 - j₀).toUInt64).toInt64) :
    |m.toInt| ≤ 2 ^ (61 - j₀) := by
  have hsh := toNat_one_shiftLeft (61 - j₀) (by omega)
  have hlt : 2 ^ (61 - j₀) < 2 ^ 63 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hb : (((1 : UInt64) <<< (61 - j₀).toUInt64).toInt64).toInt = 2 ^ (61 - j₀) := by
    rw [toInt_toInt64_of_lt _ (by rw [hsh]; exact hlt), hsh]; push_cast; rfl
  have hle : (2 : ℤ) ^ (61 - j₀) ≤ 2 ^ 62 := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [Int64.le_iff_toInt_le, Int64.toInt_neg, hb,
    bmod_two_pow_64_of_abs_le (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact hle)] at h₁
  rw [Int64.le_iff_toInt_le, hb] at h₂
  exact abs_le.mpr ⟨h₁, h₂⟩

/-- One base-case step on the matrix, in exact integer arithmetic: when every entry of `M` is at
most `2^{61 − j₀}` in magnitude and `|q| ≤ 2^{j₀}`, the wrapping `Int64` computation of
`[0, p; p, q] * M` with `p = 2^{j₀}` gives the exact integer matrix. -/
theorem wordStep_exact (M : WordMat) (j₀ : ℕ) (q : Int64) (hj₀ : 1 ≤ j₀) (hj : j₀ ≤ 61)
    (hB : |M.m₁₁.toInt| ≤ 2 ^ (61 - j₀) ∧ |M.m₁₂.toInt| ≤ 2 ^ (61 - j₀) ∧
      |M.m₂₁.toInt| ≤ 2 ^ (61 - j₀) ∧ |M.m₂₂.toInt| ≤ 2 ^ (61 - j₀))
    (hq : |q.toInt| ≤ 2 ^ j₀) :
    (((1 : UInt64) <<< j₀.toUInt64).toInt64 * M.m₂₁).toInt = 2 ^ j₀ * M.m₂₁.toInt ∧
      (((1 : UInt64) <<< j₀.toUInt64).toInt64 * M.m₂₂).toInt = 2 ^ j₀ * M.m₂₂.toInt ∧
      (((1 : UInt64) <<< j₀.toUInt64).toInt64 * M.m₁₁ + q * M.m₂₁).toInt =
        2 ^ j₀ * M.m₁₁.toInt + q.toInt * M.m₂₁.toInt ∧
      (((1 : UInt64) <<< j₀.toUInt64).toInt64 * M.m₁₂ + q * M.m₂₂).toInt =
        2 ^ j₀ * M.m₁₂.toInt + q.toInt * M.m₂₂.toInt := by
  obtain ⟨h11, h12, h21, h22⟩ := hB
  set p : Int64 := ((1 : UInt64) <<< j₀.toUInt64).toInt64 with hpdef
  have hhalf := toNat_one_shiftLeft j₀ (by omega)
  have hp : p.toInt = 2 ^ j₀ := by
    have h63 : 2 ^ j₀ < 2 ^ 63 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [hpdef, toInt_toInt64_of_lt _ (by rw [hhalf]; exact h63), hhalf]
    push_cast; rfl
  have hpabs : |p.toInt| = 2 ^ j₀ := by rw [hp]; exact abs_of_nonneg (by positivity)
  have hE1 : (2 : ℤ) ^ j₀ * 2 ^ (61 - j₀) = 2 ^ 61 := by
    rw [← pow_add]; congr 1; omega
  have h61 : (2 : ℤ) ^ 61 + 2 ^ 61 = 2 ^ 62 := by norm_num
  have h6162 : (2 : ℤ) ^ 61 ≤ 2 ^ 62 := by norm_num
  have mulb : ∀ x : Int64, |x.toInt| ≤ 2 ^ (61 - j₀) → |p.toInt * x.toInt| ≤ 2 ^ 61 :=
    fun x hx => by
      rw [abs_mul, hpabs, ← hE1]; exact mul_le_mul_of_nonneg_left hx (by positivity)
  have mulq : ∀ x : Int64, |x.toInt| ≤ 2 ^ (61 - j₀) → |q.toInt * x.toInt| ≤ 2 ^ 61 :=
    fun x hx => by
      rw [abs_mul, ← hE1]; exact mul_le_mul hq hx (abs_nonneg _) (by positivity)
  have prod : ∀ x : Int64, |x.toInt| ≤ 2 ^ (61 - j₀) → (p * x).toInt = 2 ^ j₀ * x.toInt :=
    fun x hx => by
      rw [Int64.toInt_mul, bmod_two_pow_64_of_abs_le ((mulb x hx).trans h6162), hp]
  have prodq : ∀ x : Int64, |x.toInt| ≤ 2 ^ (61 - j₀) → (q * x).toInt = q.toInt * x.toInt :=
    fun x hx => by
      rw [Int64.toInt_mul, bmod_two_pow_64_of_abs_le ((mulq x hx).trans h6162)]
  have sum : ∀ x y : Int64, |x.toInt| ≤ 2 ^ (61 - j₀) → |y.toInt| ≤ 2 ^ (61 - j₀) →
      (p * x + q * y).toInt = 2 ^ j₀ * x.toInt + q.toInt * y.toInt := fun x y hx hy => by
    rw [Int64.toInt_add, prod x hx, prodq y hy, ← hp, bmod_two_pow_64_of_abs_le]
    exact ((abs_add_le _ _).trans (add_le_add (mulb x hx) (mulq y hy))).trans (le_of_eq h61)
  exact ⟨prod _ h21, prod _ h22, sum _ _ h11 h21, sum _ _ h12 h22⟩

/-- The quotient of a base-case step satisfies `|q| ≤ 2^{j₀}`. -/
theorem wordStep_quotient_bound (t : UInt64) (j₀ : ℕ) (hj₀ : j₀ ≤ 61)
    (ht : t.toNat ≤ 2 * 2 ^ j₀ - 1) :
    |(if t < (1 : UInt64) <<< j₀.toUInt64 then t.toInt64
        else t.toInt64 - (2 * ((1 : UInt64) <<< j₀.toUInt64)).toInt64).toInt| ≤ 2 ^ j₀ := by
  have h61 : 2 ^ j₀ ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) hj₀
  have hpow : 2 * 2 ^ j₀ ≤ 2 ^ 62 := by
    have : (2 : ℕ) ^ 61 * 2 ≤ 2 ^ 62 := by norm_num
    omega
  have hhalf := toNat_one_shiftLeft j₀ (by omega)
  have htwo := toNat_two_mul_half j₀ (by omega)
  have ht' : t.toInt64.toInt = (t.toNat : ℤ) := toInt_toInt64_of_lt t (by omega)
  have h2 : ((2 * ((1 : UInt64) <<< j₀.toUInt64)).toInt64).toInt = ((2 * 2 ^ j₀ : ℕ) : ℤ) := by
    rw [toInt_toInt64_of_lt _ (by rw [htwo]; omega), htwo]
  have htle : (t.toNat : ℤ) ≤ ((2 * 2 ^ j₀ : ℕ) : ℤ) := by
    exact_mod_cast (Nat.le_trans ht (Nat.sub_le _ _))
  have hpos : (0 : ℤ) ≤ 2 ^ j₀ := by positivity
  split_ifs with hlt
  · rw [UInt64.lt_iff_toNat_lt, hhalf] at hlt
    rw [ht', abs_of_nonneg (by positivity)]
    exact_mod_cast hlt.le
  · rw [UInt64.lt_iff_toNat_lt, hhalf] at hlt
    have hge : ((2 ^ j₀ : ℕ) : ℤ) ≤ t.toNat := by exact_mod_cast not_lt.mp hlt
    have hb : |(t.toNat : ℤ) - ((2 * 2 ^ j₀ : ℕ) : ℤ)| ≤ 2 ^ 62 := by
      have h62 : ((2 * 2 ^ j₀ : ℕ) : ℤ) ≤ 2 ^ 62 := by exact_mod_cast hpow
      have h0 : (0 : ℤ) ≤ t.toNat := Int.natCast_nonneg _
      rw [abs_le]; constructor <;> linarith [show (0 : ℤ) ≤ 2 ^ 62 by positivity]
    rw [Int64.toInt_sub, ht', h2, bmod_two_pow_64_of_abs_le hb, abs_le]
    push_cast at hge htle ⊢
    constructor <;> linarith

theorem det_step (P Q a b c d : ℤ) :
    P * c * (P * b + Q * d) - P * d * (P * a + Q * c) = -P ^ 2 * (a * d - b * c) := by ring

theorem natAbs_detInts_go (k : ℕ) :
    ∀ (fuel : ℕ) (A B : Word2) (j : ℕ) (M : WordMat),
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
    by_cases hstop : B.trailingZeros = 0 ∨ 61 < B.trailingZeros ∨ k < j + B.trailingZeros
    · rw [ite_eq_left hstop]; exact h
    rw [ite_eq_right hstop]
    push Not at hstop
    obtain ⟨hj₀, hj61, _⟩ := hstop
    split
    · rename_i hchk
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hchk
      have hj₀' : 1 ≤ B.trailingZeros := Nat.pos_of_ne_zero hj₀
      have hB : |M.m₁₁.toInt| ≤ 2 ^ (61 - B.trailingZeros) ∧
          |M.m₁₂.toInt| ≤ 2 ^ (61 - B.trailingZeros) ∧
          |M.m₂₁.toInt| ≤ 2 ^ (61 - B.trailingZeros) ∧
          |M.m₂₂.toInt| ≤ 2 ^ (61 - B.trailingZeros) :=
        ⟨abs_toInt_le_of_check _ _ hj61 c1 c2, abs_toInt_le_of_check _ _ hj61 c3 c4,
          abs_toInt_le_of_check _ _ hj61 c5 c6, abs_toInt_le_of_check _ _ hj61 c7 c8⟩
      have ht : ((0 - A.lo) * invOddUInt64 (B.shiftRight B.trailingZeros).lo (B.trailingZeros + 1)
          &&& (2 * ((1 : UInt64) <<< B.trailingZeros.toUInt64) - 1)).toNat ≤
            2 * 2 ^ B.trailingZeros - 1 := by
        rw [UInt64.toNat_and, toNat_mask _ (by omega)]
        exact Nat.and_le_right
      have hq := wordStep_quotient_bound _ B.trailingZeros hj61 ht
      obtain ⟨e11, e12, e21, e22⟩ := wordStep_exact M B.trailingZeros _ hj₀' hj61 hB hq
      refine ih _ _ _ _ ?_
      have h' : (M.m₁₁.toInt * M.m₂₂.toInt - M.m₁₂.toInt * M.m₂₁.toInt).natAbs = 2 ^ (2 * j) := h
      rw [detInts, e11, e12, e21, e22, det_step, Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_pow,
        Int.natAbs_pow, h']
      have h2 : (2 : ℤ).natAbs = 2 := rfl
      rw [h2]; ring
    · exact h

theorem natAbs_detInts_halfBinaryGcdWord (A B : Word2) (k : ℕ) :
    (detInts (halfBinaryGcdWord A B k).2).natAbs = 2 ^ (2 * (halfBinaryGcdWord A B k).1) :=
  natAbs_detInts_go k (k + 1) A B 0 ⟨1, 0, 0, 1⟩ (by simp [detInts])

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
      rw [detInt_ofWord]
      exact natAbs_detInts_halfBinaryGcdWord _ _ _
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

/-! ### The fused linear combination -/

/-- The value of the limbs `f i, f (i+1), …, f (i+n-1)` (least significant first). -/
def seqVal (f : ℕ → UInt64) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i, n + 1 => (f i).toNat + 2 ^ 64 * seqVal f (i + 1) n

theorem seqVal_getD (l : List UInt64) : ∀ (i n : ℕ), l.length ≤ i + n →
    seqVal (fun k => l.getD k 0) i n = toNatLimbsList (l.drop i) := by
  intro i n
  induction n generalizing i with
  | zero =>
    intro h
    rw [List.drop_of_length_le (by omega)]
    rfl
  | succ n ih =>
    intro h
    rw [seqVal, ih (i + 1) (by omega)]
    by_cases hi : i < l.length
    · rw [List.drop_eq_getElem_cons hi, toNatLimbsList_cons, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi]
      simp only [Option.getD_some]
      ring
    · have hle : l.length ≤ i := not_lt.mp hi
      rw [List.drop_of_length_le hle, List.drop_of_length_le (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
      simp [toNatLimbsList]

theorem getD_toList (x : Array UInt64) (k : ℕ) : x.toList.getD k 0 = x.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, Array.getElem?_toList]

/-- `seqVal` over an array's limbs is the array's value once the window covers it. -/
theorem seqVal_array (x : Array UInt64) (n : ℕ) (h : x.size ≤ n) :
    seqVal (fun k => x.getD k 0) 0 n = toNatLimbsList x.toList := by
  have := seqVal_getD x.toList 0 n (by simpa using h)
  rw [List.drop_zero] at this
  rw [← this]
  congr 1
  funext k
  exact (getD_toList x k).symm

/-- The accumulator of `linCombLimbs.go` is only ever appended to. -/
theorem linCombLimbs.go_acc (x y : Array UInt64) (u v : UInt64) (sub : Bool) :
    ∀ (fuel i : ℕ) (acc : Array UInt64) (c₁ c₂ : UInt64) (bo : Bool),
      (linCombLimbs.go x y u v sub fuel i acc c₁ c₂ bo).1.toList =
          acc.toList ++ (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).1.toList ∧
        (linCombLimbs.go x y u v sub fuel i acc c₁ c₂ bo).2 =
          (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).2 := by
  intro fuel
  induction fuel with
  | zero => intro i acc c₁ c₂ bo; simp [linCombLimbs.go]
  | succ fuel ih =>
    intro i acc c₁ c₂ bo
    simp only [linCombLimbs.go]
    obtain ⟨h1, h2⟩ := ih (i + 1) (acc.push _) _ _ _
    obtain ⟨h1', h2'⟩ := ih (i + 1) (#[].push _) _ _ _
    rw [h1, h1', h2, h2', Array.toList_push, Array.toList_push]
    simp

/-- The subtraction pass, all carries included:
`D + (y·v + c₂ + borrow_in) + c₁_out · 2^{64 fuel} = x·u + c₁ + borrow_out · 2^{64 fuel} +
c₂_out · 2^{64 fuel}`. -/
theorem linCombLimbs.go_spec_sub (x y : Array UInt64) (u v : UInt64) :
    ∀ (fuel i : ℕ) (c₁ c₂ : UInt64) (bo : Bool),
      toNatLimbsList (linCombLimbs.go x y u v true fuel i #[] c₁ c₂ bo).1.toList +
          (seqVal (fun k => y.getD k 0) i fuel * v.toNat + c₂.toNat + (if bo then 1 else 0)) +
          (linCombLimbs.go x y u v true fuel i #[] c₁ c₂ bo).2.2.1.toNat * 2 ^ (64 * fuel) =
        seqVal (fun k => x.getD k 0) i fuel * u.toNat + c₁.toNat +
          (if (linCombLimbs.go x y u v true fuel i #[] c₁ c₂ bo).2.1 then 2 ^ (64 * fuel) else 0) +
          (linCombLimbs.go x y u v true fuel i #[] c₁ c₂ bo).2.2.2.toNat * 2 ^ (64 * fuel) := by
  intro fuel
  induction fuel with
  | zero => intro i c₁ c₂ bo; simp only [linCombLimbs.go, seqVal]; simp [toNatLimbsList]; omega
  | succ fuel ih =>
    intro i c₁ c₂ bo
    simp only [linCombLimbs.go, ↓reduceIte]
    set p := UInt64.mulWithCarry (x.getD i 0) u c₁ with hp
    set q := UInt64.mulWithCarry (y.getD i 0) v c₂ with hq
    set d := UInt64.subWithBorrow p.2 q.2 bo with hd
    obtain ⟨h1, h2⟩ := linCombLimbs.go_acc x y u v true fuel (i + 1) (#[].push d.1) p.1 q.1 d.2
    simp only [h1, h2, Array.toList_push, List.nil_append, List.singleton_append,
      toNatLimbsList_cons, seqVal]
    have E1 := UInt64.mulWithCarry_eq (x.getD i 0) u c₁
    have E2 := UInt64.mulWithCarry_eq (y.getD i 0) v c₂
    have E3 := UInt64.subWithBorrow_eq p.2 q.2 bo
    rw [← hp] at E1
    rw [← hq] at E2
    rw [← hd] at E3
    have IH := ih (i + 1) p.1 q.1 d.2
    have hpow : (2 : ℕ) ^ (64 * (fuel + 1)) = 2 ^ (64 * fuel) * 2 ^ 64 := by ring
    rw [hpow, ← ite_zero_mul]
    zify at E1 E2 E3 IH ⊢
    push_cast at E1 E2 E3 IH ⊢
    linear_combination (2 : ℤ) ^ 64 * IH + E3 - E2 + E1

/-- The addition pass, all carries included:
`S + carry_out · 2^{64 fuel} + (c₁_out + c₂_out) · 2^{64 fuel} = x·u + c₁ + y·v + c₂ + carry_in`. -/
theorem linCombLimbs.go_spec_add (x y : Array UInt64) (u v : UInt64) :
    ∀ (fuel i : ℕ) (c₁ c₂ : UInt64) (bo : Bool),
      toNatLimbsList (linCombLimbs.go x y u v false fuel i #[] c₁ c₂ bo).1.toList +
          (if (linCombLimbs.go x y u v false fuel i #[] c₁ c₂ bo).2.1 then 2 ^ (64 * fuel) else 0) +
          (linCombLimbs.go x y u v false fuel i #[] c₁ c₂ bo).2.2.1.toNat * 2 ^ (64 * fuel) +
          (linCombLimbs.go x y u v false fuel i #[] c₁ c₂ bo).2.2.2.toNat * 2 ^ (64 * fuel) =
        seqVal (fun k => x.getD k 0) i fuel * u.toNat + c₁.toNat +
          (seqVal (fun k => y.getD k 0) i fuel * v.toNat + c₂.toNat + (if bo then 1 else 0)) := by
  intro fuel
  induction fuel with
  | zero => intro i c₁ c₂ bo; simp only [linCombLimbs.go, seqVal]; simp [toNatLimbsList]; omega
  | succ fuel ih =>
    intro i c₁ c₂ bo
    simp only [linCombLimbs.go, Bool.false_eq_true, ↓reduceIte]
    set p := UInt64.mulWithCarry (x.getD i 0) u c₁ with hp
    set q := UInt64.mulWithCarry (y.getD i 0) v c₂ with hq
    set d := UInt64.addWithCarry p.2 q.2 bo with hd
    obtain ⟨h1, h2⟩ := linCombLimbs.go_acc x y u v false fuel (i + 1) (#[].push d.1) p.1 q.1 d.2
    simp only [h1, h2, Array.toList_push, List.nil_append, List.singleton_append,
      toNatLimbsList_cons, seqVal]
    have E1 := UInt64.mulWithCarry_eq (x.getD i 0) u c₁
    have E2 := UInt64.mulWithCarry_eq (y.getD i 0) v c₂
    have E3 := UInt64.addWithCarry_eq p.2 q.2 bo
    rw [← hp] at E1
    rw [← hq] at E2
    rw [← hd] at E3
    have IH := ih (i + 1) p.1 q.1 d.2
    have hpow : (2 : ℕ) ^ (64 * (fuel + 1)) = 2 ^ (64 * fuel) * 2 ^ 64 := by ring
    rw [hpow, ← ite_zero_mul]
    zify at E1 E2 E3 IH ⊢
    push_cast at E1 E2 E3 IH ⊢
    linear_combination (2 : ℤ) ^ 64 * IH - E3 + E1 + E2

theorem linCombLimbs.go_length (x y : Array UInt64) (u v : UInt64) (sub : Bool) :
    ∀ (fuel i : ℕ) (c₁ c₂ : UInt64) (bo : Bool),
      (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).1.size = fuel := by
  intro fuel
  induction fuel with
  | zero => intro i c₁ c₂ bo; simp [linCombLimbs.go]
  | succ fuel ih =>
    intro i c₁ c₂ bo
    simp only [linCombLimbs.go]
    rw [← Array.length_toList, (linCombLimbs.go_acc x y u v sub fuel (i + 1) _ _ _ _).1,
      List.length_append, Array.length_toList, Array.length_toList, ih]
    simp; omega

/-- A product step on a zero limb leaves no carry. -/
theorem mulWithCarry_zero_fst (u c : UInt64) : (UInt64.mulWithCarry 0 u c).1 = 0 := by
  have h := UInt64.mulWithCarry_eq 0 u c
  have hc := UInt64.toNat_lt_size c
  rw [UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add] at h
  apply UInt64.eq_of_toNat_eq
  rw [UInt64.toNat_zero]
  have hlt : (UInt64.mulWithCarry 0 u c).1.toNat * 2 ^ 64 < 2 ^ 64 := by
    have hsz : UInt64.size = 2 ^ 64 := rfl
    omega
  rcases Nat.eq_zero_or_pos (UInt64.mulWithCarry 0 u c).1.toNat with h0 | hpos
  · exact h0
  · exfalso
    have := Nat.mul_le_mul_right (2 ^ 64) hpos
    rw [Nat.one_mul] at this
    omega

/-- Once the pass has read past both arrays, the final product carries are zero. -/
theorem linCombLimbs.go_carries (x y : Array UInt64) (u v : UInt64) (sub : Bool) :
    ∀ (fuel i : ℕ) (acc : Array UInt64) (c₁ c₂ : UInt64) (bo : Bool), 1 ≤ fuel →
      x.size ≤ i + fuel - 1 → y.size ≤ i + fuel - 1 →
      (linCombLimbs.go x y u v sub fuel i acc c₁ c₂ bo).2.2.1 = 0 ∧
        (linCombLimbs.go x y u v sub fuel i acc c₁ c₂ bo).2.2.2 = 0 := by
  intro fuel
  induction fuel with
  | zero => intro i acc c₁ c₂ bo h; omega
  | succ fuel ih =>
    intro i acc c₁ c₂ bo _ hx hy
    cases fuel with
    | zero =>
      simp only [linCombLimbs.go]
      have hx0 : x.getD i 0 = 0 := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
      have hy0 : y.getD i 0 = 0 := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
      rw [hx0, hy0]
      exact ⟨mulWithCarry_zero_fst _ _, mulWithCarry_zero_fst _ _⟩
    | succ fuel =>
      simp only [linCombLimbs.go]
      exact ih (i + 1) _ _ _ _ (by omega) (by omega) (by omega)

/-- `linCombLimbs` with `sub = true`: `D + y·v = x·u + borrow · 2^{64 n}`. -/
theorem linCombLimbs_sub (x y : AzNat) (u v : UInt64) :
    toNatLimbsList (linCombLimbs x.limbs y.limbs u v true).1.toList + y.toNat * v.toNat =
      x.toNat * u.toNat + (if (linCombLimbs x.limbs y.limbs u v true).2 then
        2 ^ (64 * (max x.limbs.size y.limbs.size + 2)) else 0) := by
  unfold linCombLimbs
  dsimp only
  have hE : (Array.mkEmpty (max x.limbs.size y.limbs.size + 2) : Array UInt64) = #[] := rfl
  simp only [hE]
  have := linCombLimbs.go_spec_sub x.limbs y.limbs u v (max x.limbs.size y.limbs.size + 2) 0 0 0
    false
  obtain ⟨hc1, hc2⟩ := linCombLimbs.go_carries x.limbs y.limbs u v true
    (max x.limbs.size y.limbs.size + 2) 0 #[] 0 0 false (by omega) (by omega) (by omega)
  rw [seqVal_array _ _ (by omega), seqVal_array _ _ (by omega), hc1, hc2] at this
  simp only [UInt64.toNat_zero, add_zero, Bool.false_eq_true, ite_false, zero_mul] at this
  exact this

/-- `linCombLimbs` with `sub = false`: `S + carry · 2^{64 n} = x·u + y·v`. -/
theorem linCombLimbs_add (x y : AzNat) (u v : UInt64) :
    toNatLimbsList (linCombLimbs x.limbs y.limbs u v false).1.toList +
        (if (linCombLimbs x.limbs y.limbs u v false).2 then
          2 ^ (64 * (max x.limbs.size y.limbs.size + 2)) else 0) =
      x.toNat * u.toNat + y.toNat * v.toNat := by
  unfold linCombLimbs
  dsimp only
  have hE : (Array.mkEmpty (max x.limbs.size y.limbs.size + 2) : Array UInt64) = #[] := rfl
  simp only [hE]
  have := linCombLimbs.go_spec_add x.limbs y.limbs u v (max x.limbs.size y.limbs.size + 2) 0 0 0
    false
  obtain ⟨hc1, hc2⟩ := linCombLimbs.go_carries x.limbs y.limbs u v false
    (max x.limbs.size y.limbs.size + 2) 0 #[] 0 0 false (by omega) (by omega) (by omega)
  rw [seqVal_array _ _ (by omega), seqVal_array _ _ (by omega), hc1, hc2] at this
  simp only [UInt64.toNat_zero, add_zero, Bool.false_eq_true, ite_false, zero_mul] at this
  exact this

theorem linCombLimbs_size (x y : Array UInt64) (u v : UInt64) (sub : Bool) :
    (linCombLimbs x y u v sub).1.size = max x.size y.size + 2 := by
  unfold linCombLimbs
  dsimp only
  have hE : (Array.mkEmpty (max x.size y.size + 2) : Array UInt64) = #[] := rfl
  simp only [hE, linCombLimbs.go_length]

/-- The magnitude word of an `Int64`. -/
theorem toNat_natAbs_toUInt64 (m : Int64) : m.toInt.natAbs.toUInt64.toNat = m.toInt.natAbs := by
  apply UInt64.toNat_ofNat_of_lt'
  have h1 := Int64.toInt_lt m
  have h2 := Int64.le_toInt m
  have : (m.toInt.natAbs : ℤ) ≤ 2 ^ 63 := by
    rw [Int.natCast_natAbs]; exact abs_le.mpr ⟨h2, le_of_lt h1⟩
  have : m.toInt.natAbs ≤ 2 ^ 63 := by exact_mod_cast this
  have : (2 : ℕ) ^ 63 < UInt64.size := by decide
  omega

/-- `int64Abs` is the magnitude. -/
theorem toNat_int64Abs (m : Int64) : (int64Abs m).toNat = m.toInt.natAbs := by
  unfold int64Abs
  have hbv : m.toInt = m.toBitVec.toInt := (Int64.toInt_toBitVec m).symm
  have hu : m.toUInt64.toNat = m.toBitVec.toNat := by
    show m.toUInt64.toBitVec.toNat = _
    rw [Int64.toBitVec_toUInt64]
  have hlt := m.toBitVec.isLt
  rw [BitVec.toInt_eq_toNat_cond] at hbv
  split_ifs with h0
  · rw [Int64.le_iff_toInt_le, Int64.toInt_zero] at h0
    rw [hu]
    split_ifs at hbv with hc
    · rw [hbv, Int.natAbs_natCast]
    · exfalso; rw [hbv] at h0; omega
  · rw [Int64.le_iff_toInt_le, Int64.toInt_zero, not_le] at h0
    rw [UInt64.toNat_sub, UInt64.toNat_zero, hu, Nat.add_zero]
    split_ifs at hbv with hc
    · exfalso; rw [hbv] at h0; omega
    · rw [hbv]
      have hle : m.toBitVec.toNat ≤ 2 ^ 64 := le_of_lt hlt
      have hcast : ((m.toBitVec.toNat : ℕ) : ℤ) - ((2 ^ 64 : ℕ) : ℤ) =
          -(((2 ^ 64 - m.toBitVec.toNat : ℕ)) : ℤ) := by
        rw [Nat.cast_sub hle]; ring
      rw [hcast, Int.natAbs_neg, Int.natAbs_natCast, Nat.mod_eq_of_lt (by omega)]

/-- A signed term as a signed magnitude. -/
theorem term_eq_signed (m : Int64) (z : AzInt) :
    m.toInt * z.toInt = if (decide (0 ≤ m) == z.sign) then
      ((m.toInt.natAbs * z.abs.toNat : ℕ) : ℤ) else -((m.toInt.natAbs * z.abs.toNat : ℕ) : ℤ) := by
  have hm : (0 ≤ m) ↔ 0 ≤ m.toInt := by rw [Int64.le_iff_toInt_le, Int64.toInt_zero]
  rw [toInt_eq_ite]
  push_cast
  by_cases h : 0 ≤ m
  · have h' : 0 ≤ m.toInt := hm.mp h
    rw [abs_of_nonneg h']
    cases z.sign <;> simp [h]
  · have h' : m.toInt < 0 := not_le.mp (fun hh => h (hm.mpr hh))
    rw [abs_of_neg h']
    cases z.sign <;> simp [h]

/-! #### The folded shift -/

/-- The value of one shifted limb: `prev >>> r` plus the low `r` bits of `d` moved to the top. -/
theorem toNat_shiftLimbPair (r : ℕ) (hr : r < 64) (prev d : UInt64) :
    (shiftLimbPair r.toUInt64 (64 - r).toUInt64 (shiftMask0 r) prev d).toNat =
      prev.toNat / 2 ^ r + d.toNat % 2 ^ r * 2 ^ (64 - r) := by
  unfold shiftLimbPair shiftMask0
  have hsz : (64 : ℕ) < UInt64.size := by decide
  have hr' : r.toUInt64.toNat = r := UInt64.toNat_ofNat_of_lt' (by omega)
  have hprev : (prev >>> r.toUInt64).toNat = prev.toNat / 2 ^ r := by
    rw [UInt64.toNat_shiftRight, hr', Nat.mod_eq_of_lt hr, Nat.shiftRight_eq_div_pow]
  by_cases h0 : r = 0
  · subst h0
    simp [Nat.mod_one]
  · rw [ite_eq_right h0]
    have hsh : ((64 - r).toUInt64).toNat = 64 - r := UInt64.toNat_ofNat_of_lt' (by omega)
    have hsplit : (2 : ℕ) ^ 64 = 2 ^ r * 2 ^ (64 - r) := by rw [← pow_add]; congr 1; omega
    have hlt : d.toNat % 2 ^ r * 2 ^ (64 - r) < 2 ^ 64 := by
      rw [hsplit]
      exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos r)) (Nat.two_pow_pos _)
    have hd : ((d <<< (64 - r).toUInt64) &&& 0xFFFFFFFFFFFFFFFF).toNat =
        d.toNat % 2 ^ r * 2 ^ (64 - r) := by
      have hm : (0xFFFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 64 - 1 := rfl
      rw [UInt64.toNat_and, UInt64.toNat_shiftLeft, hsh, Nat.mod_eq_of_lt (by omega : 64 - r < 64),
        Nat.shiftLeft_eq, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ ⟨1, by ring⟩,
        hsplit, Nat.mul_mod_mul_right]
    rw [UInt64.toNat_add, hprev, hd]
    apply Nat.mod_eq_of_lt
    have h1 : prev.toNat / 2 ^ r < 2 ^ (64 - r) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos r), ← pow_add, show 64 - r + r = 64 by omega]
      exact UInt64.toNat_lt_size prev
    have h2 : d.toNat % 2 ^ r < 2 ^ r := Nat.mod_lt _ (Nat.two_pow_pos r)
    have h3 : d.toNat % 2 ^ r * 2 ^ (64 - r) ≤ (2 ^ r - 1) * 2 ^ (64 - r) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (2 ^ r - 1) * 2 ^ (64 - r) + 2 ^ (64 - r) = 2 ^ 64 := by
      rw [Nat.sub_one_mul, ← pow_add, show r + (64 - r) = 64 by omega]
      exact Nat.sub_add_cancel (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega

/-- Pure emission of the fused shifted pass on the raw limbs produced from index `i`. -/
def emitShift (w r : ℕ) : ℕ → List UInt64 → UInt64 → Bool → List UInt64 × UInt64 × Bool
  | _, [], prev, ok => ([], prev, ok)
  | i, d :: ds, prev, ok =>
    if i < w then emitShift w r (i + 1) ds prev (ok && d == 0)
    else if i = w then emitShift w r (i + 1) ds d (ok && (d &&& ((1 <<< r.toUInt64) - 1)) == 0)
    else (shiftLimbPair r.toUInt64 (64 - r).toUInt64 (shiftMask0 r) prev d ::
        (emitShift w r (i + 1) ds d ok).1,
      (emitShift w r (i + 1) ds d ok).2)

/-- The emission phase is the raw loop followed by `emitShift` (for any `ok`, which it does not
touch). -/
theorem linCombShift.goHigh_eq (x y : Array UInt64) (u v : UInt64) (sub : Bool) (w r : ℕ) :
    ∀ (fuel i : ℕ) (acc : Array UInt64) (prev : UInt64) (c₁ c₂ : UInt64) (bo ok : Bool), w < i →
      (linCombShift.goHigh x y u v sub r.toUInt64 (64 - r).toUInt64 (shiftMask0 r) fuel i acc prev
          c₁ c₂ bo).1.toList =
          acc.toList ++ (emitShift w r i (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).1.toList
            prev ok).1 ∧
        (linCombShift.goHigh x y u v sub r.toUInt64 (64 - r).toUInt64 (shiftMask0 r) fuel i acc prev
          c₁ c₂ bo).2.1 =
          (emitShift w r i (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).1.toList prev ok).2.1 ∧
        (emitShift w r i (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).1.toList prev ok).2.2 =
          ok ∧
        (linCombShift.goHigh x y u v sub r.toUInt64 (64 - r).toUInt64 (shiftMask0 r) fuel i acc prev
          c₁ c₂ bo).2.2 =
          (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).2.1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc prev c₁ c₂ bo ok _
    simp [linCombShift.goHigh, linCombLimbs.go, emitShift]
  | succ fuel ih =>
    intro i acc prev c₁ c₂ bo ok hi
    simp only [linCombShift.goHigh, linCombLimbs.go]
    set p := UInt64.mulWithCarry (x.getD i 0) u c₁ with hp
    set q := UInt64.mulWithCarry (y.getD i 0) v c₂ with hq
    set d := (if sub then UInt64.subWithBorrow p.2 q.2 bo else UInt64.addWithCarry p.2 q.2 bo)
      with hd
    obtain ⟨h1, h2⟩ := linCombLimbs.go_acc x y u v sub fuel (i + 1) (#[].push d.1) p.1 q.1 d.2
    have hlt : ¬ i < w := by omega
    have heq : ¬ i = w := by omega
    simp only [h1, h2, Array.toList_push, List.nil_append, List.singleton_append, emitShift, hlt,
      heq, ↓reduceIte]
    obtain ⟨e1, e2, e3, e4⟩ :=
      ih (i + 1) (acc.push (shiftLimbPair r.toUInt64 (64 - r).toUInt64 (shiftMask0 r) prev d.1))
        d.1 p.1 q.1 d.2 ok (by omega)
    refine ⟨?_, e2, e3, e4⟩
    rw [e1, Array.toList_push]
    simp

/-- The low phase is the raw loop followed by `emitShift` (for any `prev`, which it ignores). -/
theorem linCombShift.goLow_eq (x y : Array UInt64) (u v : UInt64) (sub : Bool) (w r : ℕ) :
    ∀ (fuel i : ℕ) (ok : Bool) (c₁ c₂ : UInt64) (bo : Bool) (prev : UInt64),
      i ≤ w → w < i + fuel →
      (linCombShift.goLow x y u v sub w r fuel i ok c₁ c₂ bo).1.toList =
          (emitShift w r i (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).1.toList prev ok).1 ∧
        (linCombShift.goLow x y u v sub w r fuel i ok c₁ c₂ bo).2.1 =
          (emitShift w r i (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).1.toList prev ok).2.1 ∧
        (linCombShift.goLow x y u v sub w r fuel i ok c₁ c₂ bo).2.2.1 =
          (emitShift w r i (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).1.toList prev ok).2.2 ∧
        (linCombShift.goLow x y u v sub w r fuel i ok c₁ c₂ bo).2.2.2 =
          (linCombLimbs.go x y u v sub fuel i #[] c₁ c₂ bo).2.1 := by
  intro fuel
  induction fuel with
  | zero => intro i ok c₁ c₂ bo prev hi hw; omega
  | succ fuel ih =>
    intro i ok c₁ c₂ bo prev hi hw
    simp only [linCombShift.goLow, linCombLimbs.go]
    set p := UInt64.mulWithCarry (x.getD i 0) u c₁ with hp
    set q := UInt64.mulWithCarry (y.getD i 0) v c₂ with hq
    set d := (if sub then UInt64.subWithBorrow p.2 q.2 bo else UInt64.addWithCarry p.2 q.2 bo)
      with hd
    obtain ⟨h1, h2⟩ := linCombLimbs.go_acc x y u v sub fuel (i + 1) (#[].push d.1) p.1 q.1 d.2
    simp only [h1, h2, Array.toList_push, List.nil_append, List.singleton_append, emitShift]
    by_cases hlt : i < w
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      exact ih (i + 1) (ok && d.1 == 0) p.1 q.1 d.2 prev (by omega) (by omega)
    · have heq : i = w := by omega
      rw [ite_eq_right hlt, ite_eq_right hlt, ite_eq_left heq]
      have hE : (Array.mkEmpty fuel : Array UInt64) = #[] := rfl
      obtain ⟨g1, g2, g3, g4⟩ := linCombShift.goHigh_eq x y u v sub w r fuel (i + 1)
        (Array.mkEmpty fuel) d.1 p.1 q.1 d.2 (ok && (d.1 &&& ((1 <<< r.toUInt64) - 1)) == 0)
        (by omega)
      rw [hE] at g1
      simp only [List.nil_append] at g1
      exact ⟨g1, g2, g3.symm, g4⟩

theorem toNat_shiftRight_small (a : UInt64) (r : ℕ) (hr : r < 64) :
    (a >>> r.toUInt64).toNat = a.toNat / 2 ^ r := by
  have hsz : (64 : ℕ) < UInt64.size := by decide
  rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat_of_lt' (by omega), Nat.mod_eq_of_lt hr,
    Nat.shiftRight_eq_div_pow]

/-- The emission phase (`i > w`): the emitted limbs followed by the last raw limb shifted are
`(prev + 2^64 · ds) / 2^r`; the exactness flag is untouched. -/
theorem emitShift_val_high (w r : ℕ) (hr : r < 64) :
    ∀ (ds : List UInt64) (i : ℕ) (prev : UInt64) (ok : Bool), w < i →
      toNatLimbsList ((emitShift w r i ds prev ok).1 ++
          [(emitShift w r i ds prev ok).2.1 >>> r.toUInt64]) =
          (prev.toNat + 2 ^ 64 * toNatLimbsList ds) / 2 ^ r ∧
        (emitShift w r i ds prev ok).2.2 = ok ∧
        (emitShift w r i ds prev ok).1.length = ds.length := by
  intro ds
  induction ds with
  | nil =>
    intro i prev ok _
    simp only [emitShift, List.nil_append, toNatLimbsList_cons, List.length_nil, and_true]
    rw [toNat_shiftRight_small _ _ hr]
    simp [toNatLimbsList]
  | cons d ds ih =>
    intro i prev ok hi
    have h1 : ¬ i < w := by omega
    have h2 : ¬ i = w := by omega
    simp only [emitShift, h1, h2, ↓reduceIte]
    obtain ⟨ihv, ihok, ihlen⟩ := ih (i + 1) d ok (by omega)
    refine ⟨?_, ihok, by simp [ihlen]⟩
    rw [List.cons_append, toNatLimbsList_cons, ihv, toNat_shiftLimbPair r hr, toNatLimbsList_cons]
    set L := toNatLimbsList ds with hL
    set P : ℕ := 2 ^ (64 - r) with hP
    have hPr : P * 2 ^ r = 2 ^ 64 := by rw [hP, ← pow_add]; congr 1; omega
    have hL1 : (d.toNat + 2 ^ 64 * L) / 2 ^ r = d.toNat / 2 ^ r + P * L := by
      have : 2 ^ 64 * L = P * L * 2 ^ r := by rw [← hPr]; ring
      rw [this, Nat.add_mul_div_right _ _ (Nat.two_pow_pos r)]
    have hR : (prev.toNat + 2 ^ 64 * (L * 2 ^ 64 + d.toNat)) / 2 ^ r =
        prev.toNat / 2 ^ r + (P * d.toNat + 2 ^ 64 * (P * L)) := by
      have : 2 ^ 64 * (L * 2 ^ 64 + d.toNat) = (P * d.toNat + 2 ^ 64 * (P * L)) * 2 ^ r := by
        rw [← hPr]; ring
      rw [this, Nat.add_mul_div_right _ _ (Nat.two_pow_pos r)]
    rw [hL1, hR]
    have hdm := Nat.div_add_mod d.toNat (2 ^ r)
    zify at hPr hdm ⊢
    push_cast at hPr hdm ⊢
    linear_combination (-((d.toNat : ℤ) / 2 ^ r)) * hPr + (P : ℤ) * hdm

/-- Divisibility by `2^64 · M` of `L · 2^64 + d` with `d < 2^64`. -/
theorem two_pow_dvd_limb_iff (L d M : ℕ) (hd : d < 2 ^ 64) :
    2 ^ 64 * M ∣ L * 2 ^ 64 + d ↔ d = 0 ∧ M ∣ L := by
  constructor
  · intro h
    have h64 : 2 ^ 64 ∣ L * 2 ^ 64 + d := Dvd.dvd.trans (Dvd.intro M rfl) h
    have hd0 : d = 0 := by
      have : 2 ^ 64 ∣ d := (Nat.dvd_add_right (Dvd.intro_left L rfl)).mp h64
      exact Nat.eq_zero_of_dvd_of_lt this hd
    subst hd0
    rw [Nat.add_zero, mul_comm L] at h
    exact ⟨rfl, Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos 64) h⟩
  · rintro ⟨rfl, ⟨k, hk⟩⟩
    exact ⟨k, by rw [hk]; ring⟩

/-- The low phase (`i ≤ w`): the final value is `D / 2^{64 (w − i)} / 2^r`, the flag records
exactness, and the output has `D.length − (w − i) − 1` emitted limbs. -/
theorem emitShift_val_low (w r : ℕ) (hr : r < 64) :
    ∀ (D : List UInt64) (i : ℕ) (prev : UInt64) (ok : Bool), i ≤ w → w < i + D.length →
      toNatLimbsList ((emitShift w r i D prev ok).1 ++
          [(emitShift w r i D prev ok).2.1 >>> r.toUInt64]) =
          toNatLimbsList D / 2 ^ (64 * (w - i)) / 2 ^ r ∧
        ((emitShift w r i D prev ok).2.2 = true ↔
          ok = true ∧ 2 ^ (64 * (w - i) + r) ∣ toNatLimbsList D) ∧
        (emitShift w r i D prev ok).1.length + (w - i) + 1 = D.length := by
  intro D
  induction D with
  | nil => intro i prev ok _ h; simp at h; omega
  | cons d ds ih =>
    intro i prev ok hi hlen
    by_cases hlt : i < w
    · simp only [emitShift, hlt, ↓reduceIte]
      obtain ⟨ihv, ihok, ihlen⟩ :=
        ih (i + 1) prev (ok && d == 0) (by omega) (by simp at hlen ⊢; omega)
      have hw : w - i = (w - (i + 1)) + 1 := by omega
      have hpow : (2 : ℕ) ^ (64 * (w - i)) = 2 ^ 64 * 2 ^ (64 * (w - (i + 1))) := by
        rw [hw, ← pow_add]; congr 1; ring
      have hd := UInt64.toNat_lt_size d
      have hsz : UInt64.size = 2 ^ 64 := rfl
      rw [hsz] at hd
      refine ⟨?_, ?_, by simp at ihlen ⊢; omega⟩
      · rw [ihv, toNatLimbsList_cons, hpow, ← Nat.div_div_eq_div_mul,
          show toNatLimbsList ds * 2 ^ 64 + d.toNat = d.toNat + toNatLimbsList ds * 2 ^ 64 from
            Nat.add_comm _ _,
          Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt hd, Nat.zero_add]
      · rw [ihok, toNatLimbsList_cons, Bool.and_eq_true, beq_iff_eq, hw,
          show (2 : ℕ) ^ (64 * (w - (i + 1) + 1) + r) = 2 ^ 64 * 2 ^ (64 * (w - (i + 1)) + r) by
            rw [← pow_add]; congr 1; ring,
          two_pow_dvd_limb_iff _ _ _ hd]
        constructor
        · rintro ⟨⟨hok, hd0⟩, hdvd⟩
          exact ⟨hok, by rw [hd0]; rfl, hdvd⟩
        · rintro ⟨hok, hd0, hdvd⟩
          exact ⟨⟨hok, UInt64.eq_of_toNat_eq (by rw [hd0]; rfl)⟩, hdvd⟩
    · have heq : i = w := by omega
      subst heq
      simp only [emitShift, lt_irrefl, ↓reduceIte, Nat.sub_self, Nat.mul_zero, pow_zero,
        Nat.div_one, Nat.zero_add]
      obtain ⟨hv, hok, hlen'⟩ := emitShift_val_high i r hr ds (i + 1) d
        (ok && (d &&& ((1 <<< r.toUInt64) - 1)) == 0) (by omega)
      refine ⟨?_, ?_, by rw [hlen']; simp⟩
      · rw [hv, toNatLimbsList_cons]; congr 1; ring
      · rw [hok, Bool.and_eq_true, beq_iff_eq, toNatLimbsList_cons]
        have hmask : ((1 : UInt64) <<< r.toUInt64 - 1).toNat = 2 ^ r - 1 := by
          have hle : (1 : UInt64) ≤ 1 <<< r.toUInt64 := by
            rw [UInt64.le_iff_toNat_le, toNat_one_shiftLeft r hr, UInt64.toNat_one]
            exact Nat.one_le_two_pow
          rw [UInt64.toNat_sub_of_le _ _ hle, toNat_one_shiftLeft r hr, UInt64.toNat_one]
        have hand : (d &&& ((1 : UInt64) <<< r.toUInt64 - 1)) = 0 ↔ 2 ^ r ∣ d.toNat := by
          rw [← UInt64.toNat_inj, UInt64.toNat_and, hmask, UInt64.toNat_zero,
            Nat.and_two_pow_sub_one_eq_mod, Nat.dvd_iff_mod_eq_zero]
        have hdvd64 : 2 ^ r ∣ toNatLimbsList ds * 2 ^ 64 :=
          Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by omega)) _
        rw [hand, Nat.dvd_add_right hdvd64]

/-- The whole emission from index `0`: value `D / 2^{64 w + r}`, exactness flag, and
`D.length − w` output limbs. -/
theorem emitShift_val (w r : ℕ) (hr : r < 64) (D : List UInt64) (hD : w < D.length) :
    toNatLimbsList ((emitShift w r 0 D 0 true).1 ++
        [(emitShift w r 0 D 0 true).2.1 >>> r.toUInt64]) =
        toNatLimbsList D / 2 ^ (64 * w + r) ∧
      ((emitShift w r 0 D 0 true).2.2 = true ↔ 2 ^ (64 * w + r) ∣ toNatLimbsList D) ∧
      (emitShift w r 0 D 0 true).1.length + w + 1 = D.length := by
  obtain ⟨hv, hok, hlen⟩ := emitShift_val_low w r hr D 0 0 true (Nat.zero_le _) (by omega)
  simp only [Nat.sub_zero] at hv hok hlen
  refine ⟨?_, ?_, hlen⟩
  · rw [hv, Nat.div_div_eq_div_mul, ← pow_add]
  · rw [hok]; simp

/-! #### Negation -/

theorem negLimbs.go_acc (a : Array UInt64) :
    ∀ (fuel i : ℕ) (acc : Array UInt64) (bo : Bool),
      (negLimbs.go a fuel i acc bo).1.toList =
          acc.toList ++ (negLimbs.go a fuel i #[] bo).1.toList ∧
        (negLimbs.go a fuel i acc bo).2 = (negLimbs.go a fuel i #[] bo).2 := by
  intro fuel
  induction fuel with
  | zero => intro i acc bo; simp [negLimbs.go]
  | succ fuel ih =>
    intro i acc bo
    simp only [negLimbs.go]
    obtain ⟨h1, h2⟩ := ih (i + 1) (acc.push _) _
    obtain ⟨h1', h2'⟩ := ih (i + 1) (#[].push _) _
    rw [h1, h1', h2, h2', Array.toList_push, Array.toList_push]
    simp

/-- The negation pass: `out + a + borrow_in = borrow_out · 2^{64 fuel}`. -/
theorem negLimbs.go_spec (a : Array UInt64) :
    ∀ (fuel i : ℕ) (bo : Bool),
      toNatLimbsList (negLimbs.go a fuel i #[] bo).1.toList + seqVal (fun k => a.getD k 0) i fuel +
          (if bo then 1 else 0) =
        (if (negLimbs.go a fuel i #[] bo).2 then 2 ^ (64 * fuel) else 0) := by
  intro fuel
  induction fuel with
  | zero => intro i bo; simp [negLimbs.go, seqVal, toNatLimbsList]
  | succ fuel ih =>
    intro i bo
    rw [negLimbs.go]
    obtain ⟨h1, h2⟩ := negLimbs.go_acc a fuel (i + 1)
      (#[].push (UInt64.subWithBorrow 0 (a.getD i 0) bo).1)
      (UInt64.subWithBorrow 0 (a.getD i 0) bo).2
    simp only [h1, h2, Array.toList_push, List.nil_append, List.singleton_append,
      toNatLimbsList_cons, seqVal]
    have E := UInt64.subWithBorrow_eq 0 (a.getD i 0) bo
    rw [UInt64.toNat_zero] at E
    have IH := ih (i + 1) (UInt64.subWithBorrow 0 (a.getD i 0) bo).2
    have hpow : (2 : ℕ) ^ (64 * (fuel + 1)) = 2 ^ (64 * fuel) * 2 ^ 64 := by ring
    rw [hpow, ← ite_zero_mul]
    zify at E IH ⊢
    push_cast at E IH ⊢
    linear_combination (2 : ℤ) ^ 64 * IH + E

theorem negLimbs.go_length (a : Array UInt64) :
    ∀ (fuel i : ℕ) (bo : Bool), (negLimbs.go a fuel i #[] bo).1.size = fuel := by
  intro fuel
  induction fuel with
  | zero => intro i bo; simp [negLimbs.go]
  | succ fuel ih =>
    intro i bo
    simp only [negLimbs.go]
    rw [← Array.length_toList, (negLimbs.go_acc a fuel (i + 1) _ _).1, List.length_append,
      Array.length_toList, Array.length_toList, ih]
    simp; omega

/-- `negLimbs a` is `2^{64 · size} − a` when `a ≠ 0`. -/
theorem toNatLimbsList_negLimbs (a : Array UInt64) (ha : 0 < toNatLimbsList a.toList) :
    toNatLimbsList (negLimbs a).toList + toNatLimbsList a.toList = 2 ^ (64 * a.size) := by
  unfold negLimbs
  have hE : (Array.mkEmpty a.size : Array UInt64) = #[] := rfl
  simp only [hE]
  have := negLimbs.go_spec a a.size 0 false
  rw [seqVal_array a a.size le_rfl] at this
  simp only [Bool.false_eq_true, ite_false, add_zero] at this
  split_ifs at this with hb
  · exact this
  · omega

theorem negLimbs_size (a : Array UInt64) : (negLimbs a).size = a.size := by
  unfold negLimbs
  have hE : (Array.mkEmpty a.size : Array UInt64) = #[] := rfl
  simp only [hE, negLimbs.go_length]

/-- A product of a word and an `AzNat` is below `2^{64 (size + 1)}`. -/
theorem natAbs_mul_toNat_lt (m : Int64) (z : AzNat) (n : ℕ) (hn : z.limbs.size + 1 ≤ n) :
    m.toInt.natAbs * z.toNat < 2 ^ (64 * n) := by
  have h1 : z.toNat < 2 ^ (64 * z.limbs.size) := toNat_lt_pow z
  have h2 : m.toInt.natAbs < 2 ^ 64 := by
    have h3 := UInt64.toNat_lt_size (int64Abs m)
    rw [toNat_int64Abs] at h3
    exact h3
  calc m.toInt.natAbs * z.toNat < 2 ^ 64 * 2 ^ (64 * z.limbs.size) := Nat.mul_lt_mul'' h2 h1
    _ = 2 ^ (64 * (z.limbs.size + 1)) := by rw [← pow_add]; congr 1; ring
    _ ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `linCombShift` is `linCombLimbs` divided by `2^sh`, with exactness flag, borrow and length. -/
theorem linCombShift_spec (x y : AzNat) (u v : UInt64) (sub : Bool) (sh : ℕ)
    (hsh : sh < 64 * (max x.limbs.size y.limbs.size + 2)) :
    toNatLimbsList (linCombShift x.limbs y.limbs u v sub sh).1.toList =
        toNatLimbsList (linCombLimbs x.limbs y.limbs u v sub).1.toList / 2 ^ sh ∧
      ((linCombShift x.limbs y.limbs u v sub sh).2.1 = true ↔
        2 ^ sh ∣ toNatLimbsList (linCombLimbs x.limbs y.limbs u v sub).1.toList) ∧
      (linCombShift x.limbs y.limbs u v sub sh).2.2 = (linCombLimbs x.limbs y.limbs u v sub).2 ∧
      (linCombShift x.limbs y.limbs u v sub sh).1.size =
        max x.limbs.size y.limbs.size + 2 - sh / 64 := by
  set n := max x.limbs.size y.limbs.size + 2 with hn
  have hE : (Array.mkEmpty n : Array UInt64) = #[] := rfl
  have hr64 : sh % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hwr : 64 * (sh / 64) + sh % 64 = sh := Nat.div_add_mod sh 64
  have hwn : sh / 64 < n := by omega
  have hDlen : (linCombLimbs.go x.limbs y.limbs u v sub n 0 #[] 0 0 false).1.toList.length = n := by
    rw [Array.length_toList, linCombLimbs.go_length]
  obtain ⟨g1, g2, g3, g4⟩ := linCombShift.goLow_eq x.limbs y.limbs u v sub (sh / 64) (sh % 64) n 0
    true 0 0 false 0 (Nat.zero_le _) (by omega)
  obtain ⟨ev, eok, elen⟩ := emitShift_val (sh / 64) (sh % 64) hr64
    (linCombLimbs.go x.limbs y.limbs u v sub n 0 #[] 0 0 false).1.toList (by omega)
  have hres1 : (linCombShift x.limbs y.limbs u v sub sh).1.toList =
      (emitShift (sh / 64) (sh % 64) 0
        (linCombLimbs.go x.limbs y.limbs u v sub n 0 #[] 0 0 false).1.toList 0 true).1 ++
      [(emitShift (sh / 64) (sh % 64) 0
        (linCombLimbs.go x.limbs y.limbs u v sub n 0 #[] 0 0 false).1.toList 0 true).2.1 >>>
          (sh % 64).toUInt64] := by
    unfold linCombShift
    dsimp only
    rw [Array.toList_push, g1, g2]
  have hraw : (linCombLimbs x.limbs y.limbs u v sub).1.toList =
      (linCombLimbs.go x.limbs y.limbs u v sub n 0 #[] 0 0 false).1.toList := by
    unfold linCombLimbs; dsimp only; rw [hE]
  have hraw2 : (linCombLimbs x.limbs y.limbs u v sub).2 =
      (linCombLimbs.go x.limbs y.limbs u v sub n 0 #[] 0 0 false).2.1 := by
    unfold linCombLimbs; dsimp only; rw [hE]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hres1, ev, hwr, hraw]
  · have : (linCombShift x.limbs y.limbs u v sub sh).2.1 =
        (emitShift (sh / 64) (sh % 64) 0
          (linCombLimbs.go x.limbs y.limbs u v sub n 0 #[] 0 0 false).1.toList 0 true).2.2 := by
      unfold linCombShift; dsimp only; exact g3
    rw [this, eok, hwr, hraw]
  · unfold linCombShift; dsimp only; rw [hraw2]; exact g4
  · rw [← Array.length_toList, hres1, List.length_append, List.length_singleton]
    omega

/-- `fusedCombine?` computes `(m₁ x + m₂ y) / 2^sh` exactly. -/
theorem toInt_fusedCombine? (m₁ m₂ : Int64) (x y : AzInt) (sh : ℕ) (c : AzInt)
    (h : fusedCombine? m₁ m₂ x y sh = some c) :
    c.toInt * 2 ^ sh = m₁.toInt * x.toInt + m₂.toInt * y.toInt := by
  rw [term_eq_signed m₁ x, term_eq_signed m₂ y]
  unfold fusedCombine? at h
  dsimp only at h
  set u := int64Abs m₁ with hu
  set v := int64Abs m₂ with hv
  set t₁ := (decide (0 ≤ m₁) == x.sign) with ht₁
  set t₂ := (decide (0 ≤ m₂) == y.sign) with ht₂
  set n := max x.abs.limbs.size y.abs.limbs.size + 2 with hn
  clear_value u v t₁ t₂
  have hun : u.toNat = m₁.toInt.natAbs := by rw [hu]; exact toNat_int64Abs m₁
  have hvn : v.toNat = m₂.toInt.natAbs := by rw [hv]; exact toNat_int64Abs m₂
  set A : ℕ := m₁.toInt.natAbs * x.abs.toNat with hA
  set B : ℕ := m₂.toInt.natAbs * y.abs.toNat with hB
  clear_value A B
  have hA' : x.abs.toNat * u.toNat = A := by rw [hun, hA, mul_comm]
  have hB' : y.abs.toNat * v.toNat = B := by rw [hvn, hB, mul_comm]
  have hAlt : A < 2 ^ (64 * (n - 1)) := hA ▸ natAbs_mul_toNat_lt m₁ x.abs (n - 1) (by omega)
  have hBlt : B < 2 ^ (64 * (n - 1)) := hB ▸ natAbs_mul_toNat_lt m₂ y.abs (n - 1) (by omega)
  have hpown : (2 : ℕ) ^ (64 * n) = 2 ^ (64 * (n - 1)) * 2 ^ 64 := by
    have : 64 * n = 64 * (n - 1) + 64 := by omega
    rw [this, pow_add]
  have hpowle : (2 : ℕ) ^ (64 * (n - 1)) ≤ 2 ^ (64 * n) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hABlt : A + B < 2 ^ (64 * n) := by
    have : (2 : ℕ) ^ (64 * (n - 1)) * 2 ≤ 2 ^ (64 * (n - 1)) * 2 ^ 64 :=
      Nat.mul_le_mul_left _ (by norm_num)
    omega
  by_cases hsh : 64 * n ≤ sh
  · rw [ite_eq_left hsh] at h; cases h
  rw [ite_eq_right hsh] at h
  have hsh' : sh < 64 * (max x.abs.limbs.size y.abs.limbs.size + 2) := by omega
  by_cases hts : t₁ = t₂
  · -- same signs: the sum
    subst hts
    have hsubF : (t₁ != t₁) = false := by simp
    rw [hsubF, beq_self_eq_true] at h
    simp only [↓reduceIte] at h
    obtain ⟨hT, hok, hbo, _⟩ := linCombShift_spec x.abs y.abs u v false sh hsh'
    have hadd := linCombLimbs_add x.abs y.abs u v
    rw [hA', hB', ← hn] at hadd
    set res := linCombShift x.abs.limbs y.abs.limbs u v false sh with hres
    clear_value res
    set D := toNatLimbsList (linCombLimbs x.abs.limbs y.abs.limbs u v false).1.toList with hD
    clear_value D
    have hDAB : D = A + B := by
      by_cases hb : (linCombLimbs x.abs.limbs y.abs.limbs u v false).2
      · rw [ite_eq_left hb] at hadd; omega
      · rw [ite_eq_right hb] at hadd; omega
    by_cases hex : res.2.1 = true
    swap
    · have : (!res.2.1) = true := by simpa using hex
      rw [ite_eq_left this] at h; cases h
    have hexF : (!res.2.1) = false := by simp [hex]
    rw [hexF] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain rfl := Option.some.inj h
    have hdvd : 2 ^ sh ∣ D := hok.mp hex
    have hdivZ : ((D / 2 ^ sh : ℕ) : ℤ) * 2 ^ sh = (D : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hDZ : (D : ℤ) = (A : ℤ) + B := by exact_mod_cast hDAB
    rw [toInt_mkNorm, toNat_ofLimbs, hT]
    cases t₁
    · simp only [Bool.false_eq_true, ↓reduceIte]
      linear_combination -hdivZ - hDZ
    · simp only [↓reduceIte]
      linear_combination hdivZ + hDZ
  · -- opposite signs: the difference in two's complement
    have hsubT : (t₁ != t₂) = true := by simpa using hts
    have hbeq : (t₁ == t₂) = false := by simpa using hts
    rw [hsubT] at h
    obtain ⟨hT, hok, hbo, hlen⟩ := linCombShift_spec x.abs y.abs u v true sh hsh'
    have hsubs := linCombLimbs_sub x.abs y.abs u v
    rw [hA', hB', ← hn] at hsubs
    set res := linCombShift x.abs.limbs y.abs.limbs u v true sh with hres
    clear_value res
    set D := toNatLimbsList (linCombLimbs x.abs.limbs y.abs.limbs u v true).1.toList with hD
    have hDlt : D < 2 ^ (64 * n) := by
      have := toNatLimbsList_lt_pow (linCombLimbs x.abs.limbs y.abs.limbs u v true).1.toList
      rwa [Array.length_toList, linCombLimbs_size] at this
    set bo := (linCombLimbs x.abs.limbs y.abs.limbs u v true).2 with hbodef
    clear_value D bo
    have ht₂' : t₂ = !t₁ := Bool.eq_not.mpr (fun h' => hts h'.symm)
    rw [ht₂']
    by_cases hex : res.2.1 = true
    swap
    · have : (!res.2.1) = true := by simpa using hex
      rw [ite_eq_left this] at h; cases h
    have hexF : (!res.2.1) = false := by simp [hex]
    rw [hexF, hbeq] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hdvd : 2 ^ sh ∣ D := hok.mp hex
    have hdivZ : ((D / 2 ^ sh : ℕ) : ℤ) * 2 ^ sh = (D : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    rw [hbo] at h
    by_cases hb : bo = true
    · -- borrow: negative result
      rw [ite_eq_left hb] at h hsubs
      obtain rfl := Option.some.inj h
      have hDZ : (D : ℤ) + B = A + 2 ^ (64 * n) := by exact_mod_cast hsubs
      -- `T = D / 2^sh` is positive and below `2^(64 n − sh)`
      have hDpos : 0 < D := by omega
      have hDge : 2 ^ sh ≤ D := Nat.le_of_dvd hDpos hdvd
      have hTpos : 0 < D / 2 ^ sh := Nat.div_pos hDge (Nat.two_pow_pos sh)
      have hL : 64 * n - sh + sh = 64 * n := Nat.sub_add_cancel (le_of_lt (not_le.mp hsh))
      have hpowL : (2 : ℕ) ^ (64 * n - sh) * 2 ^ sh = 2 ^ (64 * n) := by rw [← pow_add, hL]
      have hTlt : D / 2 ^ sh < 2 ^ (64 * n - sh) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos sh), hpowL]; exact hDlt
      -- the negation
      have hsize : 64 * res.1.size = 64 * n - sh + sh % 64 := by rw [hlen]; omega
      have hneg := toNatLimbsList_negLimbs res.1 (by rw [hT]; exact hTpos)
      rw [hT] at hneg
      have hpowS : (2 : ℕ) ^ (64 * res.1.size) = 2 ^ (64 * n - sh) * 2 ^ (sh % 64) := by
        rw [hsize, pow_add]
      rw [toInt_mkNorm, toNat_modPow2, toNat_ofLimbs]
      have hN : toNatLimbsList (negLimbs res.1).toList % 2 ^ (64 * n - sh) =
          2 ^ (64 * n - sh) - D / 2 ^ sh := by
        have hval : toNatLimbsList (negLimbs res.1).toList =
            2 ^ (64 * n - sh) * (2 ^ (sh % 64) - 1) + (2 ^ (64 * n - sh) - D / 2 ^ sh) := by
          have h1 : 1 ≤ 2 ^ (sh % 64) := Nat.one_le_two_pow
          have hle : 2 ^ (64 * n - sh) ≤ 2 ^ (64 * res.1.size) := by
            rw [hpowS]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
          rw [Nat.mul_sub, Nat.mul_one, ← hpowS]
          omega
        rw [hval, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [hN]
      have hcast : (((2 ^ (64 * n - sh) - D / 2 ^ sh : ℕ)) : ℤ) =
          (2 : ℤ) ^ (64 * n - sh) - ((D / 2 ^ sh : ℕ) : ℤ) := by
        rw [Nat.cast_sub (le_of_lt hTlt)]; push_cast; ring
      have hpowZ : ((2 : ℤ) ^ (64 * n - sh)) * 2 ^ sh = 2 ^ (64 * n) := by exact_mod_cast hpowL
      rw [hcast]
      cases t₁
      · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        linear_combination hpowZ - hdivZ - hDZ
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        linear_combination -hpowZ + hdivZ + hDZ
    · -- no borrow: nonnegative result
      have hbF : bo = false := by simpa using hb
      rw [hbF] at h hsubs
      simp only [Bool.false_eq_true, ↓reduceIte] at h hsubs
      obtain rfl := Option.some.inj h
      have hDZ : (D : ℤ) + B = (A : ℤ) + 0 := by exact_mod_cast hsubs
      rw [toInt_mkNorm, toNat_ofLimbs, hT]
      cases t₁
      · simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte]
        linear_combination -hdivZ - hDZ
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        linear_combination hdivZ + hDZ

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

theorem toNat_halfBinaryGcdDriver (threshold quadThreshold fuel : ℕ) :
    ∀ a b : AzInt,
      (halfBinaryGcdDriver threshold quadThreshold fuel a b).toNat =
        oddPartNat (Int.gcd a.toInt b.toInt) := by
  induction fuel with
  | zero => intro a b; exact toNat_oddPart_gcdBinary a b
  | succ fuel ih =>
    intro a b
    rw [halfBinaryGcdDriver]
    dsimp only
    by_cases hn : max a.size b.size ≤ threshold
    · rw [ite_eq_left hn]; exact toNat_oddPart_gcdBinary a b
    rw [ite_eq_right hn]
    by_cases hq : max a.size b.size ≤ quadThreshold
    · rw [ite_eq_left hq]
      split_ifs with hj
      · exact toNat_oddPart_gcdBinary a b
      split
      · rename_i a' b' ha' hb'
        rw [ih]
        have hdet := natAbs_detInts_halfBinaryGcdWord
          (a.lowWord2 (2 * halfBinaryWordThreshold + 1))
          (b.lowWord2 (2 * halfBinaryWordThreshold + 1)) halfBinaryWordThreshold
        have hc := toInt_fusedCombine? _ _ _ _ _ _ ha'
        have hd := toInt_fusedCombine? _ _ _ _ _ _ hb'
        exact (oddPartNat_eq_of_oddEquiv (oddEquiv_gcd_of_mat _ _ _ _ _ _ _ _ _ hdet
          (by rw [← hc]; ring) (by rw [← hd]; ring))).symm
      · exact toNat_oddPart_gcdBinary a b
    · rw [ite_eq_right hq]
      split
      · rename_i a' b' ha' hb'
        -- the matrix step
        have hdet := natAbs_detInt_halfBinaryGcd (max a.size b.size / 2 + 1)
          (a.lowBits (2 * (max a.size b.size / 2) + 1))
          (b.lowBits (2 * (max a.size b.size / 2) + 1))
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

/-- `gcdHalfBinaryWith` computes `Nat.gcd` at every pair of thresholds. -/
theorem toNat_gcdHalfBinaryWith (threshold quadThreshold : ℕ) (a b : AzNat) :
    (gcdHalfBinaryWith threshold quadThreshold a b).toNat = Nat.gcd a.toNat b.toNat := by
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
      ((halfBinaryGcdDriver threshold quadThreshold
        (max x.size (if y.isOdd then x + y else y).size + 1) x.toAzInt
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
  toNat_gcdHalfBinaryWith _ _ a b

end Azurite.AzNat
