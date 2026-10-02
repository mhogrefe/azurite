/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.HexString
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzInt.Equiv.Compare
import Azurite.AzInt.Equiv.DivMod
import Azurite.AzInt.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.LimbDigits
import Azurite.AzRat.Equiv.FromSci

/-!
# The hexadecimal debug format round-trips

`ofHexChars_toHexChars : ofHexChars (toHexChars x u) = some x` for every float and either digit
case, hence `ofHexString_toHexString`.  The writer puts the exact value's hexadecimal digits
`N` (with `N · 16^(E − D + 1)` the value) into one of three layouts; the reader recovers `N`,
the digits after the point and the exponent, and rebuilds the float from its padding-free
significand, whose exponent comes out equal to the original.
-/

namespace Azurite.AzFloat

open AzNat (charToDigit digitToChar)

/-! ### Digit strings -/

theorem mem_hexDigits (N : AzNat) (u : Bool) (c : Char) (hc : c ∈ hexDigits N u) :
    ∃ d, charToDigit c = some d ∧ d.toNat < 16 := by
  unfold hexDigits at hc
  rw [Array.toList_map, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have hlt := AzRat.digits_rev_lt_base 16 (by decide) N d (Array.mem_toList_iff.mp hd)
  rw [show (16 : UInt64).toNat = 16 from rfl] at hlt
  exact ⟨d, AzRat.charToDigit_digitToChar' d (by omega) u, hlt⟩

theorem mem_decDigits (N : AzNat) (c : Char) (hc : c ∈ decDigits N) :
    ∃ d, charToDigit c = some d ∧ d.toNat < 10 := by
  unfold decDigits at hc
  rw [Array.toList_map, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have hlt := AzRat.digits_rev_lt_base 10 (by decide) N d (Array.mem_toList_iff.mp hd)
  rw [show (10 : UInt64).toNat = 10 from rfl] at hlt
  exact ⟨d, AzRat.charToDigit_digitToChar' d (by omega) false, hlt⟩

/-- The digit values of `hexDigits N u`, most significant first, are the base-`16` digits of
`N` reversed. -/
theorem map_digitVal_hexDigits (N : AzNat) (u : Bool) :
    (hexDigits N u).map AzRat.digitVal = (Nat.digits 16 N.toNat).reverse := by
  unfold hexDigits
  rw [Array.toList_map, List.map_map, Array.toList_reverse, List.map_reverse]
  have h := AzNat.limbDigits_eq 16 (by decide) N
  rw [show (16 : UInt64).toNat = 16 from rfl] at h
  congr 1
  rw [← h]
  apply List.map_congr_left
  intro d hd
  have hlt := AzRat.digits_rev_lt_base 16 (by decide) N d (by simpa using hd)
  rw [show (16 : UInt64).toNat = 16 from rfl] at hlt
  exact AzRat.digitVal_digitToChar d (by omega) u

theorem map_digitVal_decDigits (N : AzNat) :
    (decDigits N).map AzRat.digitVal = (Nat.digits 10 N.toNat).reverse := by
  unfold decDigits
  rw [Array.toList_map, List.map_map, Array.toList_reverse, List.map_reverse]
  have h := AzNat.limbDigits_eq 10 (by decide) N
  rw [show (10 : UInt64).toNat = 10 from rfl] at h
  congr 1
  rw [← h]
  apply List.map_congr_left
  intro d hd
  have hlt := AzRat.digits_rev_lt_base 10 (by decide) N d (by simpa using hd)
  rw [show (10 : UInt64).toNat = 10 from rfl] at hlt
  exact AzRat.digitVal_digitToChar d (by omega) false

theorem length_hexDigits (N : AzNat) (u : Bool) :
    (hexDigits N u).length = (Nat.digits 16 N.toNat).length := by
  have := congrArg List.length (map_digitVal_hexDigits N u)
  rwa [List.length_map, List.length_reverse] at this

/-- A zero digit character. -/
theorem zero_char_spec : AzRat.digitVal '0' = 0 ∧ ∃ d, charToDigit '0' = some d ∧ d.toNat < 16 :=
  ⟨AzRat.digitVal_zero, 0, by decide, by decide⟩

/-- Parsing the hexadecimal digits of `N`, with zero digits before and after them. -/
theorem parseMagnitude_hexDigits (N : AzNat) (hN : N ≠ 0) (u : Bool) (pre zs : List Char)
    (hpre : ∀ c ∈ pre, AzRat.digitVal c = 0 ∧ ∃ d, charToDigit c = some d ∧ d.toNat < 16)
    (hzs : ∀ c ∈ zs, AzRat.digitVal c = 0 ∧ ∃ d, charToDigit c = some d ∧ d.toNat < 16) :
    ∃ N', AzRat.parseMagnitude 16 (pre ++ hexDigits N u ++ zs) = some N' ∧
      N'.toNat = N.toNat * 16 ^ zs.length := by
  have hzero : ∀ l : List Char,
      (∀ c ∈ l, AzRat.digitVal c = 0 ∧ ∃ d, charToDigit c = some d ∧ d.toNat < 16) →
      l.map AzRat.digitVal = List.replicate l.length 0 := fun l hl => by
    rw [List.eq_replicate_iff]
    exact ⟨by rw [List.length_map], fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      exact (hl c hc).1⟩
  obtain ⟨N', hN', hval⟩ := AzRat.parseMagnitude_eq 16 (by decide) (pre ++ hexDigits N u ++ zs)
    (by
      intro h
      have := congrArg List.length h
      rw [List.length_append, List.length_append, length_hexDigits, List.length_nil] at this
      have hpos : 0 < (Nat.digits 16 N.toNat).length :=
        List.length_pos_of_ne_nil (Nat.digits_ne_nil_iff_ne_zero.mpr (toNat_ne_zero_of_ne_zero hN))
      omega)
    (fun c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨-, d, hd, hlt⟩ := hpre c hc
          exact ⟨d, hd, hlt⟩
        · obtain ⟨d, hd, hlt⟩ := mem_hexDigits N u c hc
          exact ⟨d, hd, hlt⟩
      · obtain ⟨-, d, hd, hlt⟩ := hzs c hc
        exact ⟨d, hd, hlt⟩)
  refine ⟨N', hN', ?_⟩
  rw [hval, show (16 : UInt64).toNat = 16 from rfl, List.map_append, List.map_append,
    map_digitVal_hexDigits, hzero pre hpre, hzero zs hzs, List.reverse_append, List.reverse_append,
    List.reverse_reverse, List.reverse_replicate, List.reverse_replicate, Nat.ofDigits_append,
    Nat.ofDigits_replicate_zero, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits,
    List.length_replicate]
  ring

theorem parseMagnitude_decDigits (N : AzNat) (hN : N ≠ 0) :
    AzRat.parseMagnitude 10 (decDigits N) = some N := by
  obtain ⟨N', hN', hval⟩ := AzRat.parseMagnitude_eq 10 (by decide) (decDigits N)
    (by
      intro h
      have := congrArg List.length (map_digitVal_decDigits N)
      rw [h, List.length_map, List.length_nil, List.length_reverse] at this
      exact Nat.digits_ne_nil_iff_ne_zero.mpr (toNat_ne_zero_of_ne_zero hN)
        (List.length_eq_zero_iff.mp this.symm))
    (fun c hc => by
      obtain ⟨d, hd, hlt⟩ := mem_decDigits N c hc
      exact ⟨d, hd, hlt⟩)
  rw [hN']
  congr 1
  apply AzNat.toNat_injective
  rw [hval, show (10 : UInt64).toNat = 10 from rfl, map_digitVal_decDigits, List.reverse_reverse,
    Nat.ofDigits_digits]

/-! ### Reading the pieces -/

theorem charToDigit_hash : charToDigit '#' = none := by decide

theorem beq_hash_eq_false_of_charToDigit {c : Char} {d : UInt64} (h : charToDigit c = some d) :
    (c == '#') = false := by
  by_contra hc
  have : c = '#' := by simpa using hc
  subst this
  rw [charToDigit_hash] at h
  cases h

theorem splitHexExponent_no_sign (cs : List Char) (h : ∀ c ∈ cs, AzRat.isSignChar c = false) :
    splitHexExponent cs = some (cs, 0) := by
  unfold splitHexExponent
  rw [AzRat.splitLast_eq_none _ _ h]

theorem splitHexExponent_append (pre : List Char) (sgn : Char) (hs : AzRat.isSignChar sgn = true)
    (n : AzNat) (hn : n ≠ 0) :
    splitHexExponent (pre ++ 'E' :: sgn :: decDigits n)
      = some (pre, AzInt.mkNorm (sgn == '+') n) := by
  unfold splitHexExponent
  rw [show pre ++ 'E' :: sgn :: decDigits n = (pre ++ ['E']) ++ sgn :: decDigits n by simp,
    AzRat.splitLast_append _ _ _ _ hs (fun c hc => by
      obtain ⟨d, hd, -⟩ := mem_decDigits n c hc
      exact AzRat.isSignChar_eq_false_of_charToDigit c d hd)]
  simp only [List.getLast?_concat, show AzRat.isExpChar 'E' = true from by decide, ↓reduceIte,
    parseMagnitude_decDigits n hn, Option.map_some, List.dropLast_concat]

/-- `AzInt` helpers. -/
theorem AzInt.sign_eq_true_iff (z : AzInt) : z.sign = true ↔ 0 ≤ z.toInt := by
  unfold AzInt.toInt
  cases hz : z.sign
  · simp only [Bool.false_eq_true, ↓reduceIte, false_iff, not_le, Left.neg_neg_iff, Nat.cast_pos]
    have : z.abs ≠ 0 := fun h => by have := z.zero_sign h; rw [hz] at this; cases this
    exact Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero this)
  · simp

theorem AzInt.mkNorm_sign_abs (z : AzInt) (h : z.abs ≠ 0) : AzInt.mkNorm z.sign z.abs = z := by
  unfold AzInt.mkNorm
  rw [dite_eq_right h]

theorem AzInt.abs_toNat_eq (z : AzInt) : (z.abs.toNat : ℤ) = |z.toInt| := by
  unfold AzInt.toInt; cases z.sign <;> simp

/-- The reader on a string of the writer's shape. -/
theorem ofHexChars_shape (neg : Bool) (pre post expPart : List Char) (E : AzInt) (p : ℕ)
    (hp : 0 < p)
    (hpre : ∀ c ∈ pre, ∃ d, charToDigit c = some d ∧ d.toNat < 16)
    (hpost : ∀ c ∈ post, ∃ d, charToDigit c = some d ∧ d.toNat < 16)
    (hexp : (expPart = [] ∧ E = 0) ∨
      ∃ sgn n, AzRat.isSignChar sgn = true ∧ n ≠ 0 ∧ expPart = 'E' :: sgn :: decDigits n ∧
        E = AzInt.mkNorm (sgn == '+') n)
    (N : AzNat) (hN : AzRat.parseMagnitude 16 (pre ++ post) = some N) (hN0 : N ≠ 0)
    (hdiv : N.isMultipleOfPow2 (N.size - p) = true) :
    ofHexChars ((if neg then ['-'] else []) ++
        '0' :: 'x' :: (pre ++ '.' :: post ++ expPart ++ '#' :: Nat.toDigits 10 p))
      = some (mkFinite (!neg)
          ((AzNat.ofNat N.size).toAzInt + (E - (AzNat.ofNat post.length).toAzInt).shiftLeft 2)
          p (N.shiftRight (N.size - p))) := by
  have hpre' : ∀ c ∈ pre, (c == '.') = false := fun c hc => by
    obtain ⟨d, hd, -⟩ := hpre c hc; exact AzRat.beq_point_eq_false_of_charToDigit c d hd
  have hmant_nosign : ∀ c ∈ pre ++ '.' :: post, AzRat.isSignChar c = false := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨d, hd, -⟩ := hpre c hc; exact AzRat.isSignChar_eq_false_of_charToDigit c d hd
    · rcases List.mem_cons.mp hc with rfl | hc
      · decide
      · obtain ⟨d, hd, -⟩ := hpost c hc; exact AzRat.isSignChar_eq_false_of_charToDigit c d hd
  have hmant_nohash : ∀ c ∈ pre ++ '.' :: post ++ expPart, (c == '#') = false := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨d, hd, -⟩ := hpre c hc; exact beq_hash_eq_false_of_charToDigit hd
      · rcases List.mem_cons.mp hc with rfl | hc
        · decide
        · obtain ⟨d, hd, -⟩ := hpost c hc; exact beq_hash_eq_false_of_charToDigit hd
    · rcases hexp with ⟨rfl, -⟩ | ⟨sgn, n, hs, -, rfl, -⟩
      · simp at hc
      · rcases List.mem_cons.mp hc with rfl | hc
        · decide
        · rcases List.mem_cons.mp hc with rfl | hc
          · have : c = '+' ∨ c = '-' := by simpa [AzRat.isSignChar] using hs
            rcases this with rfl | rfl <;> decide
          · obtain ⟨d, hd, -⟩ := mem_decDigits n c hc; exact beq_hash_eq_false_of_charToDigit hd
  have hsplitE : splitHexExponent (pre ++ '.' :: post ++ expPart)
      = some (pre ++ '.' :: post, E) := by
    rcases hexp with ⟨rfl, rfl⟩ | ⟨sgn, n, hs, hn, rfl, rfl⟩
    · rw [List.append_nil]; exact splitHexExponent_no_sign _ hmant_nosign
    · exact splitHexExponent_append _ sgn hs n hn
  have hbody : pre ++ '.' :: post ++ expPart ++ '#' :: Nat.toDigits 10 p ≠ "0.0".toList := by
    intro h
    have : '#' ∈ pre ++ '.' :: post ++ expPart ++ '#' :: Nat.toDigits 10 p := by simp
    rw [h] at this
    simp at this
  have h1 := AzRat.splitFirst_append (· == '#') (pre ++ '.' :: post ++ expPart) '#'
    (Nat.toDigits 10 p) hmant_nohash (by decide)
  have h2 := AzRat.parseDecimalDigits_toDigits p
  have h3 := AzRat.splitFirst_append (· == '.') pre '.' post hpre' (by decide)
  have hpN : ¬ (p = 0 ∨ N = 0) := by push Not; exact ⟨hp.ne', hN0⟩
  have hne : ('0' : Char) ≠ '-' := by decide
  unfold ofHexChars
  rw [ite_eq_right (by cases neg <;> simp), ite_eq_right (by cases neg <;> simp),
    ite_eq_right (by cases neg <;> simp)]
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.singleton_append,
    List.head?_cons, Option.some.injEq, hne, List.tail_cons, Bool.not_false, Bool.not_true] <;>
  · rw [ite_eq_right hbody]
    simp only [Bind.bind, Option.bind, h1, h2, hsplitE, h3, hN, hpN, ↓reduceIte, hdiv]


/-! ### The round trip -/

theorem toInt_ediv4 (z : AzInt) : (z.ediv (AzInt.ofInt 4)).toInt = z.toInt / 4 := by
  rw [AzInt.toInt_ediv, AzInt.toInt_ofInt]

theorem toInt_emod4 (z : AzInt) : (z.emod (AzInt.ofInt 4)).toInt = z.toInt % 4 := by
  rw [AzInt.toInt_emod, AzInt.toInt_ofInt]

theorem toInt_sub_one (z : AzInt) : (z - 1).toInt = z.toInt - 1 := by
  rw [AzInt.toInt_sub]; rfl

theorem toInt_toAzInt_ofNat (k : ℕ) : (AzNat.ofNat k).toAzInt.toInt = k := by
  rw [toInt_toAzInt, AzNat.toNat_ofNat]

/-- The exponent the reader rebuilds, as an integer. -/
theorem toInt_rebuilt_exponent (sz k : ℕ) (E : AzInt) :
    ((AzNat.ofNat sz).toAzInt + (E - (AzNat.ofNat k).toAzInt).shiftLeft 2).toInt
      = (sz : ℤ) + (E.toInt - k) * 4 := by
  rw [AzInt.toInt_add, toInt_toAzInt_ofNat, AzInt.toInt_shiftLeft, AzInt.toInt_sub,
    toInt_toAzInt_ofNat]
  norm_num

/-- Reading back the hexadecimal rendering of every float gives the float. -/
theorem ofHexChars_toHexChars (x : AzFloat) (u : Bool) : ofHexChars (toHexChars x u) = some x := by
  cases x with
  | nan => rfl
  | infinity s => cases s <;> rfl
  | zero => rfl
  | finite s e p m hv =>
    have hp := hv.pos
    -- the core significand and its bounds
    set n := coreSignificand p m with hn_def
    have hn0 : n ≠ 0 := coreSignificand_ne_zero hv
    have hn_size : n.size = p := size_coreSignificand hv
    have hn_lo : 2 ^ (p - 1) ≤ n.toNat := by
      rw [← Nat.lt_size, AzNat.size_toNat, hn_size]; omega
    have hn_hi : n.toNat < 2 ^ p := by rw [← Nat.size_le, AzNat.size_toNat, hn_size]
    have hn_toNat : n.toNat ≠ 0 := toNat_ne_zero_of_ne_zero hn0
    -- the hexadecimal exponent and the bits in the leading digit
    set E := (e - 1).ediv (AzInt.ofInt 4) with hE_def
    set r := (e - 1).emod (AzInt.ofInt 4) with hr_def
    have hE : E.toInt = (e.toInt - 1) / 4 := by rw [hE_def, toInt_ediv4, toInt_sub_one]
    have hr : r.toInt = (e.toInt - 1) % 4 := by rw [hr_def, toInt_emod4, toInt_sub_one]
    have hr0 : 0 ≤ r.toInt := by rw [hr]; exact Int.emod_nonneg _ (by norm_num)
    have hr4 : r.toInt < 4 := by rw [hr]; exact Int.emod_lt_of_pos _ (by norm_num)
    set m' := r.abs.toNat + 1 with hm'_def
    have hm' : (m' : ℤ) = r.toInt + 1 := by
      rw [hm'_def]; push_cast; rw [AzInt.abs_toNat_eq, abs_of_nonneg hr0]
    have he : e.toInt = 4 * E.toInt + m' := by omega
    have hm'1 : 1 ≤ m' := by omega
    have hm'4 : m' ≤ 4 := by omega
    -- the digit count and the shifted significand
    set D := hexDigitCount p m' with hD_def
    have hD : D = (p - m' + 3) / 4 + 1 := rfl
    have hsh : p ≤ 4 * (D - 1) + m' := by rw [hD]; omega
    have hD4 : 4 * (D - 1) + m' ≤ p + 3 := by rw [hD]; omega
    set sh := 4 * (D - 1) + m' - p with hsh_def
    set N := n.shiftLeft sh with hN_def
    have hNtoNat : N.toNat = n.toNat * 2 ^ sh := AzNat.toNat_shiftLeft _ _
    have hN_toNat : N.toNat ≠ 0 := by rw [hNtoNat]; positivity
    have hN0 : N ≠ 0 := fun h => hN_toNat (by rw [h, AzNat.toNat_zero])
    have hNsize : N.size = p + sh := by
      rw [← AzNat.size_toNat, hNtoNat, ← Nat.shiftLeft_eq, Nat.size_shiftLeft hn_toNat,
        AzNat.size_toNat, hn_size]
    have hDlen : (Nat.digits 16 N.toNat).length = D := by
      rw [Nat.length_digits 16 _ (by norm_num) hN_toNat]
      have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
      have hlog : Nat.log 16 N.toNat = D - 1 := by
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · rw [h16, ← pow_mul, hNtoNat]
          calc 2 ^ (4 * (D - 1)) ≤ 2 ^ (p - 1 + sh) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 ^ (p - 1) * 2 ^ sh := pow_add _ _ _
            _ ≤ n.toNat * 2 ^ sh := Nat.mul_le_mul_right _ hn_lo
        · rw [h16, ← pow_mul, hNtoNat]
          calc n.toNat * 2 ^ sh < 2 ^ p * 2 ^ sh :=
                Nat.mul_lt_mul_of_pos_right hn_hi (Nat.two_pow_pos _)
            _ = 2 ^ (p + sh) := (pow_add _ _ _).symm
            _ ≤ 2 ^ (4 * (D - 1 + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    set ds := hexDigits N u with hds_def
    have hds_len : ds.length = D := by rw [hds_def, length_hexDigits, hDlen]
    have hds_dig : ∀ c ∈ ds, ∃ d, charToDigit c = some d ∧ d.toNat < 16 := mem_hexDigits N u
    have hds_ne : ds ≠ [] := by
      intro h; rw [h, List.length_nil] at hds_len; omega
    have hnil : ∀ c ∈ ([] : List Char),
        AzRat.digitVal c = 0 ∧ ∃ d, charToDigit c = some d ∧ d.toNat < 16 :=
      fun _ h => (List.not_mem_nil h).elim
    -- closing: a parsed significand `n · 2^(sh + 4j)` at the right exponent gives `x` back
    have hclose : ∀ (N' : AzNat) (j : ℕ) (ex : AzInt), N'.toNat = N.toNat * 16 ^ j →
        ex.toInt = e.toInt →
        N'.isMultipleOfPow2 (N'.size - p) = true ∧
          mkFinite s ex p (N'.shiftRight (N'.size - p)) = finite s e p m hv := by
      intro N' j ex hN' hex
      have h16 : (16 : ℕ) ^ j = 2 ^ (4 * j) := by rw [pow_mul]; norm_num
      have hN'toNat : N'.toNat = n.toNat * 2 ^ (sh + 4 * j) := by
        rw [hN', hNtoNat, h16, pow_add]; ring
      have hN'size : N'.size = p + (sh + 4 * j) := by
        rw [← AzNat.size_toNat, hN'toNat, ← Nat.shiftLeft_eq, Nat.size_shiftLeft hn_toNat,
          AzNat.size_toNat, hn_size]
      have hsub : N'.size - p = sh + 4 * j := by omega
      have hcore : N'.shiftRight (N'.size - p) = n := by
        apply AzNat.toNat_injective
        rw [AzNat.toNat_shiftRight, hsub, hN'toNat, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      have hex' : ex = e := by rw [← AzInt.ofInt_toInt ex, ← AzInt.ofInt_toInt e, hex]
      refine ⟨?_, ?_⟩
      · rw [AzNat.isMultipleOfPow2_eq, decide_eq_true_eq, hsub, hN'toNat]
        exact Dvd.intro_left _ rfl
      · rw [hcore, hex']
        apply toVal_injective p (Or.inl (precision?_mkFinite _ _ _ _ hn0 hn_size.le)) (Or.inl rfl)
        rw [toVal_mkFinite _ _ _ _ hn0, toVal_finite, finiteVal_eq_core s e hv]
    -- the rendering
    have hsign : (if s then ([] : List Char) else ['-']) = (if !s then ['-'] else []) := by
      cases s <;> rfl
    have hcond : (E ≤ AzInt.ofInt (-6) ∨ (AzNat.ofNat ds.length).toAzInt ≤ E)
        ↔ (E.toInt ≤ -6 ∨ (D : ℤ) ≤ E.toInt) := by
      rw [AzInt.le_iff_toInt_le, AzInt.le_iff_toInt_le, AzInt.toInt_ofInt, toInt_toAzInt_ofNat,
        hds_len]
    show ofHexChars ((if s then [] else ['-']) ++ '0' :: 'x' :: hexLayout ds E ++
      '#' :: Nat.toDigits 10 p) = some (finite s e p m hv)
    rw [hsign, List.append_assoc, List.cons_append, List.cons_append]
    unfold hexLayout
    by_cases hc1 : E.toInt ≤ -6 ∨ (D : ℤ) ≤ E.toInt
    · -- scientific form
      rw [ite_eq_left (hcond.mpr hc1)]
      obtain ⟨d, rest, hds⟩ := List.exists_cons_of_ne_nil hds_ne
      have hE0 : E.toInt ≠ 0 := by omega
      have hEabs : E.abs ≠ 0 := by
        intro h
        have := AzInt.abs_toNat_eq E
        rw [h, AzNat.toNat_zero] at this
        exact hE0 (abs_eq_zero.mp (by exact_mod_cast this.symm))
      have hmk : AzInt.mkNorm ((if E.sign then '+' else '-') == '+') E.abs = E := by
        have hsgn : ((if E.sign then '+' else '-') == '+') = E.sign := by cases E.sign <;> rfl
        rw [hsgn]
        exact AzInt.mkNorm_sign_abs E hEabs
      have hexp : ∃ sgn nn, AzRat.isSignChar sgn = true ∧ nn ≠ 0 ∧
          'E' :: (if E.sign then '+' else '-') :: decDigits E.abs = 'E' :: sgn :: decDigits nn ∧
          E = AzInt.mkNorm (sgn == '+') nn :=
        ⟨_, E.abs, by cases E.sign <;> decide, hEabs, rfl, hmk.symm⟩
      rw [hds]
      have hd : ∀ c ∈ [d], ∃ k, charToDigit c = some k ∧ k.toNat < 16 := fun c hc => by
        rw [List.mem_singleton] at hc; rw [hc]; exact hds_dig d (hds ▸ List.mem_cons_self)
      cases rest with
      | nil =>
        -- `d.0E±k`: one digit, `D = 1`
        have hD1 : D = 1 := by rw [← hds_len, hds]; rfl
        simp only [List.isEmpty_nil, ↓reduceIte]
        obtain ⟨N', hN', hN'val⟩ := parseMagnitude_hexDigits N hN0 u [] ['0'] hnil
          (fun c hc => by rw [List.mem_singleton] at hc; rw [hc]; exact zero_char_spec)
        norm_num at hN'val
        rw [List.nil_append, ← hds_def, hds, List.singleton_append] at hN'
        have hN'0 : N' ≠ 0 := fun h => by
          rw [h, AzNat.toNat_zero] at hN'val; exact hN_toNat (by omega)
        obtain ⟨hdiv, hfin⟩ := hclose N' 1 ((AzNat.ofNat N'.size).toAzInt +
          (E - (AzNat.ofNat (['0'] : List Char).length).toAzInt).shiftLeft 2)
          (by rw [hN'val]; norm_num) (by
          rw [toInt_rebuilt_exponent, ← AzNat.size_toNat, hN'val, hNtoNat]
          rw [show n.toNat * 2 ^ sh * 16 = n.toNat * 2 ^ (sh + 4) by rw [pow_add]; ring,
            ← Nat.shiftLeft_eq, Nat.size_shiftLeft hn_toNat, AzNat.size_toNat, hn_size]
          simp only [List.length_singleton]
          push_cast
          omega)
        have := ofHexChars_shape (!s) [d] ['0'] _ E p hp hd
          (fun c hc => by rw [List.mem_singleton] at hc; rw [hc]; exact zero_char_spec.2)
          (Or.inr hexp) N' hN' hN'0 hdiv
        rw [Bool.not_not] at this
        rw [show (d :: '.' :: ['0'] ++ 'E' :: (if E.sign then '+' else '-') :: decDigits E.abs ++
          '#' :: Nat.toDigits 10 p) = ([d] ++ '.' :: ['0'] ++
            'E' :: (if E.sign then '+' else '-') :: decDigits E.abs ++ '#' :: Nat.toDigits 10 p)
          from rfl]
        rw [this, hfin]
      | cons c rest =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨N', hN', hN'val⟩ := parseMagnitude_hexDigits N hN0 u [] [] hnil hnil
        norm_num at hN'val
        rw [List.nil_append, List.append_nil, ← hds_def, hds] at hN'
        have hN'0 : N' ≠ 0 := fun h => by
          rw [h, AzNat.toNat_zero] at hN'val; exact hN_toNat (by omega)
        have hrest : ∀ x ∈ c :: rest, ∃ k, charToDigit x = some k ∧ k.toNat < 16 := fun x hx =>
          hds_dig x (hds ▸ List.mem_cons_of_mem _ hx)
        have hlen : (c :: rest).length = D - 1 := by
          have := hds_len; rw [hds, List.length_cons] at this; omega
        obtain ⟨hdiv, hfin⟩ := hclose N' 0 ((AzNat.ofNat N'.size).toAzInt +
          (E - (AzNat.ofNat (c :: rest).length).toAzInt).shiftLeft 2)
          (by rw [hN'val]; norm_num) (by
          rw [toInt_rebuilt_exponent, ← AzNat.size_toNat, hN'val, hNtoNat,
            ← Nat.shiftLeft_eq, Nat.size_shiftLeft hn_toNat, AzNat.size_toNat, hn_size, hlen]
          push_cast
          omega)
        have := ofHexChars_shape (!s) [d] (c :: rest) _ E p hp hd hrest (Or.inr hexp) N'
          (by rw [List.singleton_append]; exact hN') hN'0 hdiv
        rw [Bool.not_not] at this
        rw [show (d :: '.' :: (c :: rest) ++ 'E' :: (if E.sign then '+' else '-') :: decDigits E.abs
          ++ '#' :: Nat.toDigits 10 p) = ([d] ++ '.' :: (c :: rest) ++
            'E' :: (if E.sign then '+' else '-') :: decDigits E.abs ++ '#' :: Nat.toDigits 10 p)
          from rfl]
        rw [this, hfin]
    · rw [ite_eq_right (fun h => hc1 (hcond.mp h))]
      push Not at hc1
      obtain ⟨hc1a, hc1b⟩ := hc1
      by_cases hsgn : E.sign = true
      · -- plain, `E ≥ 0`
        rw [ite_eq_left hsgn]
        have hEnn : 0 ≤ E.toInt := (AzInt.sign_eq_true_iff E).mp hsgn
        have hbefore : (E.abs.toNat : ℤ) + 1 = E.toInt + 1 := by
          rw [AzInt.abs_toNat_eq, abs_of_nonneg hEnn]
        set before := E.abs.toNat + 1 with hb_def
        have hbD : before ≤ D := by omega
        dsimp only
        by_cases hlt : before < ds.length
        · rw [ite_eq_left hlt]
          obtain ⟨N', hN', hN'val⟩ := parseMagnitude_hexDigits N hN0 u [] [] hnil hnil
          norm_num at hN'val
          rw [List.nil_append, List.append_nil, ← hds_def, ← List.take_append_drop before ds] at hN'
          have hN'0 : N' ≠ 0 := fun h => by
            rw [h, AzNat.toNat_zero] at hN'val; exact hN_toNat (by omega)
          have hklen : (ds.drop before).length = D - before := by rw [List.length_drop, hds_len]
          obtain ⟨hdiv, hfin⟩ := hclose N' 0 ((AzNat.ofNat N'.size).toAzInt +
            (0 - (AzNat.ofNat (ds.drop before).length).toAzInt).shiftLeft 2)
            (by rw [hN'val]; norm_num) (by
            rw [toInt_rebuilt_exponent, ← AzNat.size_toNat, hN'val, hNtoNat,
              ← Nat.shiftLeft_eq, Nat.size_shiftLeft hn_toNat, AzNat.size_toNat, hn_size, hklen,
              show (0 : AzInt).toInt = 0 from rfl]
            push_cast
            rw [Nat.cast_sub hbD]
            omega)
          have := ofHexChars_shape (!s) (ds.take before) (ds.drop before) [] 0 p hp
            (fun c hc => hds_dig c (List.mem_of_mem_take hc))
            (fun c hc => hds_dig c (List.mem_of_mem_drop hc)) (Or.inl ⟨rfl, rfl⟩) N' hN' hN'0 hdiv
          rw [Bool.not_not, List.append_nil] at this
          rw [this, hfin]
        · rw [ite_eq_right hlt]
          have hbeq : before = D := by omega
          have htake : ds.take before = ds := List.take_of_length_le (by omega)
          rw [htake]
          obtain ⟨N', hN', hN'val⟩ := parseMagnitude_hexDigits N hN0 u [] ['0'] hnil
            (fun c hc => by rw [List.mem_singleton] at hc; rw [hc]; exact zero_char_spec)
          norm_num at hN'val
          rw [List.nil_append, ← hds_def] at hN'
          have hN'0 : N' ≠ 0 := fun h => by
            rw [h, AzNat.toNat_zero] at hN'val; exact hN_toNat (by omega)
          obtain ⟨hdiv, hfin⟩ := hclose N' 1 ((AzNat.ofNat N'.size).toAzInt +
            (0 - (AzNat.ofNat (['0'] : List Char).length).toAzInt).shiftLeft 2)
            (by rw [hN'val]; norm_num) (by
            rw [toInt_rebuilt_exponent, ← AzNat.size_toNat, hN'val, hNtoNat]
            rw [show n.toNat * 2 ^ sh * 16 = n.toNat * 2 ^ (sh + 4) by rw [pow_add]; ring,
              ← Nat.shiftLeft_eq, Nat.size_shiftLeft hn_toNat, AzNat.size_toNat, hn_size,
              show (0 : AzInt).toInt = 0 from rfl]
            simp only [List.length_singleton]
            push_cast
            omega)
          have := ofHexChars_shape (!s) ds ['0'] [] 0 p hp hds_dig
            (fun c hc => by rw [List.mem_singleton] at hc; rw [hc]; exact zero_char_spec.2)
            (Or.inl ⟨rfl, rfl⟩) N' hN' hN'0 hdiv
          rw [Bool.not_not, List.append_nil] at this
          rw [this, hfin]
      · -- plain, `E < 0`
        rw [ite_eq_right hsgn]
        have hEneg : E.toInt < 0 := by
          have := (AzInt.sign_eq_true_iff E).not.mp hsgn; omega
        set z := E.abs.toNat - 1 with hz_def
        have hz : (z : ℤ) = -E.toInt - 1 := by
          have h1 : (E.abs.toNat : ℤ) = -E.toInt := by
            rw [AzInt.abs_toNat_eq, abs_of_neg hEneg]
          have h2 : 1 ≤ E.abs.toNat := by omega
          rw [hz_def]; rw [Nat.cast_sub h2]; push_cast; omega
        obtain ⟨N', hN', hN'val⟩ :=
          parseMagnitude_hexDigits N hN0 u ('0' :: List.replicate z '0') []
          (fun c hc => by
            rcases List.mem_cons.mp hc with rfl | hc
            · exact zero_char_spec
            · rw [List.mem_replicate] at hc; rw [hc.2]; exact zero_char_spec)
          hnil
        norm_num at hN'val
        rw [List.append_nil, ← hds_def] at hN'
        have hN'0 : N' ≠ 0 := fun h => by
          rw [h, AzNat.toNat_zero] at hN'val; exact hN_toNat (by omega)
        have hklen : (List.replicate z '0' ++ ds).length = z + D := by
          rw [List.length_append, List.length_replicate, hds_len]
        obtain ⟨hdiv, hfin⟩ := hclose N' 0 ((AzNat.ofNat N'.size).toAzInt +
          (0 - (AzNat.ofNat (List.replicate z '0' ++ ds).length).toAzInt).shiftLeft 2)
          (by rw [hN'val]; norm_num) (by
          rw [toInt_rebuilt_exponent, ← AzNat.size_toNat, hN'val, hNtoNat,
            ← Nat.shiftLeft_eq, Nat.size_shiftLeft hn_toNat, AzNat.size_toNat, hn_size, hklen,
            show (0 : AzInt).toInt = 0 from rfl]
          push_cast
          omega)
        have := ofHexChars_shape (!s) ['0'] (List.replicate z '0' ++ ds) [] 0 p hp
          (fun c hc => by rw [List.mem_singleton] at hc; rw [hc]; exact zero_char_spec.2)
          (fun c hc => by
            rcases List.mem_append.mp hc with hc | hc
            · rw [List.mem_replicate] at hc; rw [hc.2]; exact zero_char_spec.2
            · exact hds_dig c hc)
          (Or.inl ⟨rfl, rfl⟩) N' (by rw [List.singleton_append, ← List.cons_append]; exact hN')
          hN'0 hdiv
        rw [Bool.not_not, List.append_nil, List.singleton_append] at this
        rw [this, hfin]

theorem ofHexString_toHexString (x : AzFloat) (u : Bool) :
    ofHexString (toHexString x u) = some x := by
  unfold ofHexString toHexString
  rw [String.toList_ofList]
  exact ofHexChars_toHexChars x u

end Azurite.AzFloat
