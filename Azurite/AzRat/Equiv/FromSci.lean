/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.FromSci
import Azurite.AzRat.Equiv.ToSci
import Azurite.AzRat.Equiv.Construct
import Azurite.AzNat.Equiv.ParseBase
import Azurite.AzNat.Equiv.OfLimbDigits
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.Conversion
import Mathlib.Data.List.TakeWhile

/-!
# Round trips between `toSci` and `fromSci`

`fromSci_toString`: parsing the rendering of a well-formed `SciNumber` (any `SciFormat` with a
negative exponent threshold) recovers its value.  Hence `fromSci` undoes `toSci` up to the
rounding `toSci` performed (`fromSci_toSci`), exactly when `toSciExact` holds
(`fromSci_toSci_of_exact`).  The exponents must fit in a signed 64-bit integer, which the parser
requires (as Malachite does).
-/

namespace Azurite.AzRat

open AzNat (charToDigit digitToChar)

/-! ### Splitting lists -/

theorem splitLast_eq_none (p : Char → Bool) (L : List Char) (hL : ∀ x ∈ L, p x = false) :
    splitLast p L = none := by
  induction L with
  | nil => rfl
  | cons c rest ih =>
    simp only [splitLast, ih fun x hx => hL x (List.mem_cons_of_mem _ hx),
      hL c List.mem_cons_self, Bool.false_eq_true, ↓reduceIte]

theorem splitLast_append (p : Char → Bool) (L : List Char) (c : Char) (M : List Char)
    (hc : p c = true) (hM : ∀ x ∈ M, p x = false) :
    splitLast p (L ++ c :: M) = some (L, c, M) := by
  induction L with
  | nil => simp only [List.nil_append, splitLast, splitLast_eq_none p M hM, hc, ↓reduceIte]
  | cons d rest ih => simp only [List.cons_append, splitLast, ih]

theorem splitFirst_eq_none (p : Char → Bool) (L : List Char) (hL : ∀ x ∈ L, p x = false) :
    splitFirst p L = none := by
  induction L with
  | nil => rfl
  | cons c rest ih =>
    simp only [splitFirst, hL c List.mem_cons_self, Bool.false_eq_true, ↓reduceIte,
      ih fun x hx => hL x (List.mem_cons_of_mem _ hx), Option.map_none]

theorem splitFirst_append (p : Char → Bool) (L : List Char) (c : Char) (M : List Char)
    (hL : ∀ x ∈ L, p x = false) (hc : p c = true) :
    splitFirst p (L ++ c :: M) = some (L, M) := by
  induction L with
  | nil => simp only [List.nil_append, splitFirst, hc, ↓reduceIte]
  | cons d rest ih =>
    simp only [List.cons_append, splitFirst, hL d List.mem_cons_self, Bool.false_eq_true,
      ↓reduceIte, ih fun x hx => hL x (List.mem_cons_of_mem _ hx), Option.map_some]

/-! ### Characters -/

/-- The sign prefix of a rendering. -/
def signChars (neg : Bool) : List Char := if neg then ['-'] else []

/-- Both letter cases parse back. -/
theorem charToDigit_digitToChar' (d : UInt64) (hd : d.toNat < 36) (u : Bool) :
    charToDigit (digitToChar d u) = some d := by
  cases u
  · exact AzNat.charToDigit_digitToChar d hd
  · have h_eq : d = UInt64.ofNat d.toNat := by
      apply UInt64.toNat.inj
      show d.toNat = d.toNat % 2 ^ 64
      omega
    conv_rhs => rw [h_eq]
    rw [h_eq]
    generalize h_d_nat : d.toNat = k at hd
    interval_cases k <;> decide

theorem isExpChar_eq_false_of_charToDigit (c : Char) (d : UInt64) (h : charToDigit c = some d)
    (hd : d.toNat < 14) : isExpChar c = false := by
  by_contra hc
  have hc' : c = 'e' ∨ c = 'E' := or_iff_not_imp_left.mpr (by simpa [isExpChar] using hc)
  rcases hc' with rfl | rfl
  · rw [show charToDigit 'e' = some 14 from by decide] at h
    cases h; exact absurd hd (by decide)
  · rw [show charToDigit 'E' = some 14 from by decide] at h
    cases h; exact absurd hd (by decide)

theorem isSignChar_eq_false_of_charToDigit (c : Char) (d : UInt64)
    (h : charToDigit c = some d) : isSignChar c = false := by
  by_contra hc
  have hc' : c = '+' ∨ c = '-' := or_iff_not_imp_left.mpr (by simpa [isSignChar] using hc)
  rcases hc' with rfl | rfl
  · rw [show charToDigit '+' = none from by decide] at h; cases h
  · rw [show charToDigit '-' = none from by decide] at h; cases h

theorem beq_point_eq_false_of_charToDigit (c : Char) (d : UInt64)
    (h : charToDigit c = some d) : (c == '.') = false := by
  by_contra hc
  have hc' : c = '.' := by simpa using hc
  subst hc'
  rw [show charToDigit '.' = none from by decide] at h; cases h

theorem isExpChar_eq_false_of_isDigit (c : Char) (h : c.isDigit = true) :
    isExpChar c = false := by
  by_contra hc
  have hc' : c = 'e' ∨ c = 'E' := or_iff_not_imp_left.mpr (by simpa [isExpChar] using hc)
  rcases hc' with rfl | rfl <;> exact absurd h (by decide)

theorem isSignChar_eq_false_of_isDigit (c : Char) (h : c.isDigit = true) :
    isSignChar c = false := by
  by_contra hc
  have hc' : c = '+' ∨ c = '-' := or_iff_not_imp_left.mpr (by simpa [isSignChar] using hc)
  rcases hc' with rfl | rfl <;> exact absurd h (by decide)

theorem beq_point_eq_false_of_isDigit (c : Char) (h : c.isDigit = true) :
    (c == '.') = false := by
  by_contra hc
  have hc' : c = '.' := by simpa using hc
  subst hc'; exact absurd h (by decide)

theorem isExpChar_ite (b : Bool) : isExpChar (if b then 'e' else 'E') = true := by
  cases b <;> decide

/-! ### The decimal exponent -/

theorem foldl_decimalStep_toDigits (n : ℕ) :
    ∀ init : ℕ, (Nat.toDigits 10 n).foldl decimalStep (some init)
      = some (init * 10 ^ (Nat.toDigits 10 n).length + n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro init
    rw [Nat.toDigits_eq_ite (by norm_num)]
    split
    · rename_i hn
      have hdig : (Nat.digitChar n).isDigit = true := by
        rw [Nat.isDigit_digitChar]; simpa using hn
      have hval : (Nat.digitChar n).toNat - '0'.toNat = n := by
        interval_cases n <;> rfl
      simp only [List.foldl_cons, List.foldl_nil, decimalStep, hdig, ↓reduceIte, hval,
        List.length_singleton, pow_one]
      ring_nf
    · rename_i hn
      rw [List.foldl_append, ih (n / 10) (by omega) init]
      have hdig : (Nat.digitChar (n % 10)).isDigit = true := by
        rw [Nat.isDigit_digitChar]; simpa using Nat.mod_lt n (by norm_num)
      have hval : (Nat.digitChar (n % 10)).toNat - '0'.toNat = n % 10 := by
        have := Nat.mod_lt n (show 0 < 10 by norm_num)
        generalize n % 10 = m at this ⊢
        interval_cases m <;> rfl
      simp only [List.foldl_cons, List.foldl_nil, decimalStep, hdig, ↓reduceIte, hval,
        List.length_append, List.length_singleton, pow_succ]
      congr 1
      have := Nat.div_add_mod n 10
      ring_nf
      omega

theorem parseDecimalDigits_toDigits (n : ℕ) :
    parseDecimalDigits (Nat.toDigits 10 n) = some n := by
  unfold parseDecimalDigits
  rw [ite_eq_right (by simp [Nat.toDigits_ne_nil]), foldl_decimalStep_toDigits n 0]
  simp

theorem isDigit_of_mem_toDigits10 {n : ℕ} {c : Char} (hc : c ∈ Nat.toDigits 10 n) :
    c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by norm_num) (by norm_num) hc

theorem fitsInt64_of_natAbs_lt (e : ℤ) (he : e.natAbs < 2 ^ 63) : fitsInt64 e = true := by
  unfold fitsInt64
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem fitsInt64_iff (e : ℤ) : fitsInt64 e = true ↔ -2 ^ 63 ≤ e ∧ e < 2 ^ 63 := by
  unfold fitsInt64
  simp only [Bool.and_eq_true, decide_eq_true_eq]

theorem parseExponent_toDigits (n : ℕ) (hn : n < 2 ^ 63) :
    parseExponent (Nat.toDigits 10 n) = some (n : ℤ) := by
  obtain ⟨c, rest, h⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := n) (b := 10))
  have hc : c.isDigit = true := isDigit_of_mem_toDigits10 (h ▸ List.mem_cons_self)
  have hplus : (c == '+') = false := by
    have := isSignChar_eq_false_of_isDigit c hc
    simp [isSignChar] at this; simp [this.1]
  have hminus : (c == '-') = false := by
    have := isSignChar_eq_false_of_isDigit c hc
    simp [isSignChar] at this; simp [this.2]
  have hp := parseDecimalDigits_toDigits n
  rw [h] at hp ⊢
  simp only [parseExponent, hplus, hminus, Bool.false_eq_true, ↓reduceIte, hp,
    Option.map_some, Int.ofNat_eq_natCast]
  exact Option.filter_some_pos ((fitsInt64_iff _).mpr (by omega))

theorem parseExponent_plus_toDigits (n : ℕ) (hn : n < 2 ^ 63) :
    parseExponent ('+' :: Nat.toDigits 10 n) = some (n : ℤ) := by
  simp only [parseExponent, BEq.rfl, ↓reduceIte, parseDecimalDigits_toDigits, Option.map_some,
    Int.ofNat_eq_natCast]
  exact Option.filter_some_pos ((fitsInt64_iff _).mpr (by omega))

theorem parseExponent_minus_toDigits (n : ℕ) (hn : n ≤ 2 ^ 63) :
    parseExponent ('-' :: Nat.toDigits 10 n) = some (-(n : ℤ)) := by
  simp only [parseExponent, BEq.rfl, ↓reduceIte, parseDecimalDigits_toDigits, Option.map_some,
    show ('-' == '+') = false from by decide, Bool.false_eq_true]
  exact Option.filter_some_pos ((fitsInt64_iff _).mpr (by omega))

/-- The characters of `toString e` for an integer `e`: `'-'` possibly first, then digits. -/
theorem toList_toString_int (e : ℤ) :
    (ToString.toString e).toList = (if e < 0 then ['-'] else []) ++ Nat.toDigits 10 e.natAbs := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · rename_i h
    rw [ite_eq_right (by omega), Nat.toList_repr, List.nil_append]
    congr 1; omega
  · rename_i h
    rw [ite_eq_left (by omega), String.toList_append, Nat.toList_repr]
    congr 2; omega

/-- The exponent suffix: an exponent indicator, then a tail that parses back to `e` and contains
no exponent indicator. -/
theorem exponentChars_spec (fmt : SciFormat) (b : UInt64) (e : ℤ) (he : e.natAbs < 2 ^ 63) :
    ∃ eCh tl, SciNumber.exponentChars fmt b e = eCh :: tl ∧ isExpChar eCh = true ∧
      (∀ c ∈ tl, isExpChar c = false) ∧ parseExponent tl = some e := by
  unfold SciNumber.exponentChars
  refine ⟨_, _, rfl, isExpChar_ite _, ?_, ?_⟩
  · intro c hc
    rw [toList_toString_int] at hc
    simp only [List.mem_append, List.mem_ite_nil_right] at hc
    rcases hc with ⟨-, hc⟩ | ⟨-, hc⟩ | hc
    · rw [List.mem_singleton] at hc; subst hc; decide
    · rw [List.mem_singleton] at hc; subst hc; decide
    · exact isExpChar_eq_false_of_isDigit c (isDigit_of_mem_toDigits10 hc)
  · rw [toList_toString_int]
    by_cases he0 : e < 0
    · rw [ite_eq_left he0, show (0 < e && (fmt.forceExponentPlusSign || 15 ≤ b)) = false by
        simp; omega]
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.singleton_append]
      rw [parseExponent_minus_toDigits _ (by omega), Int.natCast_natAbs, abs_of_neg he0, neg_neg]
    · rw [ite_eq_right he0, List.nil_append]
      split
      · rw [List.singleton_append, parseExponent_plus_toDigits _ (by omega), Int.natCast_natAbs,
          abs_of_nonneg (by omega)]
      · rw [List.nil_append, parseExponent_toDigits _ (by omega), Int.natCast_natAbs,
          abs_of_nonneg (by omega)]

/-- In bases `15` and up the exponent suffix carries a sign right after the indicator. -/
theorem exponentChars_ge15 (fmt : SciFormat) (b : UInt64) (hb : 15 ≤ b) (e : ℤ) (he0 : e ≠ 0)
    (he : e.natAbs < 2 ^ 63) :
    ∃ s, isSignChar s = true ∧
      SciNumber.exponentChars fmt b e
        = (if fmt.eLowercase then 'e' else 'E') :: s :: Nat.toDigits 10 e.natAbs ∧
      parseExponent (s :: Nat.toDigits 10 e.natAbs) = some e := by
  unfold SciNumber.exponentChars
  rw [toList_toString_int]
  by_cases hneg : e < 0
  · refine ⟨'-', by decide, ?_, ?_⟩
    · rw [ite_eq_left hneg, show (0 < e && (fmt.forceExponentPlusSign || 15 ≤ b)) = false by
        simp; omega]
      rfl
    · rw [parseExponent_minus_toDigits _ (by omega), Int.natCast_natAbs, abs_of_neg hneg, neg_neg]
  · refine ⟨'+', by decide, ?_, ?_⟩
    · rw [ite_eq_right hneg, show (0 < e && (fmt.forceExponentPlusSign || 15 ≤ b)) = true by
        simp [hb]; omega]
      rfl
    · rw [parseExponent_plus_toDigits _ (by omega), Int.natCast_natAbs, abs_of_nonneg (by omega)]

theorem isSignChar_eq_false_of_mem_toDigits10 {n : ℕ} {c : Char} (hc : c ∈ Nat.toDigits 10 n) :
    isSignChar c = false :=
  isSignChar_eq_false_of_isDigit c (isDigit_of_mem_toDigits10 hc)

/-! ### `splitExponent` -/

theorem splitExponent_no_exp (b : UInt64) (neg : Bool) (rest : List Char)
    (h1 : b.toNat < 15 → ∀ c ∈ rest, isExpChar c = false)
    (h2 : 15 ≤ b.toNat → ∀ c ∈ rest, isSignChar c = false) :
    splitExponent b (signChars neg ++ rest) = some (signChars neg ++ rest, 0) := by
  unfold splitExponent
  by_cases hb : b < 15
  · rw [ite_eq_left hb]
    have hb' : b.toNat < 15 := UInt64.lt_iff_toNat_lt.mp hb
    rw [splitLast_eq_none]
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · cases neg <;> simp [signChars] at hc; subst hc; decide
    · exact h1 hb' c hc
  · rw [ite_eq_right hb]
    have hb' : 15 ≤ b.toNat := by
      have := UInt64.lt_iff_toNat_lt.not.mp hb
      change ¬ b.toNat < (15 : ℕ) at this
      omega
    cases neg
    · simp only [signChars, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      rw [splitLast_eq_none _ _ (h2 hb')]
    · simp only [signChars, ↓reduceIte, List.singleton_append]
      rw [show '-' :: rest = [] ++ '-' :: rest from rfl,
        splitLast_append _ _ _ _ (by decide) (h2 hb')]

theorem splitExponent_append (b : UInt64) (neg : Bool) (body : List Char) (hne : body ≠ [])
    (fmt : SciFormat) (e : ℤ) (he : e.natAbs < 2 ^ 63) (he0 : 15 ≤ b.toNat → e ≠ 0) :
    splitExponent b (signChars neg ++ body ++ SciNumber.exponentChars fmt b e)
      = some (signChars neg ++ body, e) := by
  have hmant : signChars neg ++ body ≠ [] := by simp [hne]
  obtain ⟨c0, m, hm⟩ := List.exists_cons_of_ne_nil hmant
  unfold splitExponent
  by_cases hb : b < 15
  · rw [ite_eq_left hb]
    obtain ⟨eCh, tl, heq, hE, htl, hparse⟩ := exponentChars_spec fmt b e he
    rw [heq, splitLast_append _ _ _ _ hE htl, hm]
    simp only [hparse, Option.map_some]
  · rw [ite_eq_right hb]
    have hb' : 15 ≤ b.toNat := by
      have := UInt64.lt_iff_toNat_lt.not.mp hb
      change ¬ b.toNat < (15 : ℕ) at this
      omega
    obtain ⟨s, hs, heq, hparse⟩ := exponentChars_ge15 fmt b (UInt64.le_iff_toNat_le.mpr hb') e
      (he0 hb') he
    rw [heq, show signChars neg ++ body ++ (if fmt.eLowercase then 'e' else 'E') :: s ::
        Nat.toDigits 10 e.natAbs
      = ((signChars neg ++ body) ++ [if fmt.eLowercase then 'e' else 'E']) ++ s ::
        Nat.toDigits 10 e.natAbs from by simp,
      splitLast_append _ _ _ _ hs fun c hc => isSignChar_eq_false_of_mem_toDigits10 hc, hm]
    rw [List.cons_append]
    simp only [hparse, Option.map_some]
    rw [← List.cons_append, List.getLast?_concat, List.dropLast_concat]
    simp only [isExpChar_ite, ↓reduceIte]

/-! ### `splitPoint` -/

theorem splitPoint_no_point (cs : List Char) (e : ℤ) (h : ∀ c ∈ cs, (c == '.') = false) :
    splitPoint cs e = some (cs, e) := by
  unfold splitPoint
  rw [splitFirst_eq_none _ _ h]

theorem splitPoint_append (pre post : List Char) (e : ℤ)
    (hpre : ∀ c ∈ pre, (c == '.') = false)
    (hpost : ∀ c, post.head? = some c → isSignChar c = false)
    (hfit : fitsInt64 (e - post.length) = true) :
    splitPoint (pre ++ '.' :: post) e = some (pre ++ post, e - post.length) := by
  unfold splitPoint
  rw [splitFirst_append _ _ _ _ hpre (by decide)]
  have hany : post.head?.any isSignChar = false := by
    cases post with
    | nil => rfl
    | cons c rest => exact hpost c rfl
  simp only [hany, Bool.false_eq_true, ↓reduceIte, hfit]

/-! ### The mantissa -/

/-- The digit value of a character (`0` for non-digits). -/
def digitVal (c : Char) : ℕ := ((charToDigit c).getD 0).toNat

theorem digitVal_digitToChar (d : UInt64) (hd : d.toNat < 36) (u : Bool) :
    digitVal (digitToChar d u) = d.toNat := by
  rw [digitVal, charToDigit_digitToChar' d hd u, Option.getD_some]

theorem digitVal_zero : digitVal '0' = 0 := by decide

theorem parseMagnitude_eq (b : UInt64) (hb : 2 ≤ b.toNat) (cs : List Char) (hne : cs ≠ [])
    (h : ∀ c ∈ cs, ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) :
    ∃ n, parseMagnitude b cs = some n ∧
      n.toNat = Nat.ofDigits b.toNat (cs.map digitVal).reverse := by
  have h' : ∀ c ∈ cs, ∃ d, charToDigit c = some d ∧ d < b := fun c hc => by
    obtain ⟨d, hd, hlt⟩ := h c hc
    exact ⟨d, hd, UInt64.lt_iff_toNat_lt.mpr hlt⟩
  refine ⟨AzNat.ofLimbDigits b
    (⟨cs.map fun c => (charToDigit c).getD 0⟩ : Array UInt64).reverse, ?_, ?_⟩
  · unfold parseMagnitude AzNat.buildFromChars
    rw [ite_eq_right (by simpa using hne), AzNat.parseDigitsInto_eq_charToDigit b cs h']
  · rw [AzNat.toNat_ofLimbDigits b hb]
    · simp only [Array.toList_reverse, List.map_reverse, List.map_map]
      rfl
    · intro x hx
      simp only [Array.toList_reverse, List.map_reverse, List.mem_reverse, List.map_map,
        List.mem_map, Function.comp] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, hlt⟩ := h c hc
      rw [hd, Option.getD_some]
      exact hlt

theorem parseSignedDigits_eq (b : UInt64) (hb : 2 ≤ b.toNat) (neg : Bool) (cs : List Char)
    (hne : cs ≠ []) (h : ∀ c ∈ cs, ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) :
    ∃ n, parseSignedDigits b (signChars neg ++ cs) = some (!neg, n) ∧
      n.toNat = Nat.ofDigits b.toNat (cs.map digitVal).reverse := by
  obtain ⟨n, hn, hval⟩ := parseMagnitude_eq b hb cs hne h
  refine ⟨n, ?_, hval⟩
  cases neg
  · obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨d, hd, -⟩ := h c List.mem_cons_self
    have hs := isSignChar_eq_false_of_charToDigit c d hd
    simp only [isSignChar, Bool.or_eq_false_iff] at hs
    simp only [signChars, Bool.false_eq_true, ↓reduceIte, List.nil_append, parseSignedDigits,
      hs.1, hs.2, hn, Option.map_some, Bool.not_false]
  · simp only [signChars, ↓reduceIte, List.singleton_append, parseSignedDigits, BEq.rfl, hn,
      Option.map_some, Bool.not_true]

/-! ### `ofSciParts` -/

theorem toRat_ofSciParts (b : UInt64) (hb : 0 < b.toNat) (nonneg : Bool) (n : AzNat) (e : ℤ) :
    toRat (ofSciParts b nonneg n e)
      = (if nonneg then 1 else -1) * (n.toNat : ℚ) * (b.toNat : ℚ) ^ e := by
  unfold ofSciParts
  split
  · rename_i h0
    subst h0
    simp [AzNat.toNat_zero, toRat_zero]
  · have hbq : (b.toNat : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    cases e with
    | ofNat k =>
      simp only [toRat_ofSignAzNats, AzNat.toNat_mul, AzNat.toNat_pow, UInt64.toNat_toAzNat,
        show (1 : AzNat).toNat = 1 from rfl, Nat.cast_one, div_one, Int.ofNat_eq_natCast,
        zpow_natCast]
      push_cast
      ring
    | negSucc k =>
      simp only [toRat_ofSignAzNats, AzNat.toNat_pow, UInt64.toNat_toAzNat, zpow_negSucc]
      push_cast
      ring

/-! ### The whole parser on a rendered shape -/

/-- `fromSci` on a string of the shape `toChars` produces: a sign, digit characters with at most
one point (`post` empty when there is no point), and an exponent suffix that is either absent
(`e = 0`) or `exponentChars`.  The result is `± digits · b^(e − |post|)`. -/
theorem fromSci_shape (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36) (neg : Bool)
    (pre post : List Char) (point : Bool) (hpoint : point = false → post = [])
    (hpre : ∀ c ∈ pre, ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat)
    (hpost : ∀ c ∈ post, ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat)
    (hne : pre ≠ []) (fmt : SciFormat) (e : ℤ) (suffix : List Char)
    (hsuffix : (suffix = [] ∧ e = 0) ∨
      (suffix = SciNumber.exponentChars fmt b e ∧ e.natAbs < 2 ^ 63 ∧
        (15 ≤ b.toNat → e ≠ 0)))
    (hfit : (e - post.length).natAbs < 2 ^ 63) :
    fromSci (String.ofList
        (signChars neg ++ pre ++ (if point then ['.'] else []) ++ post ++ suffix)) b
      = some (ofRat ((if neg then -1 else 1)
          * ((Nat.ofDigits b.toNat ((pre ++ post).map digitVal).reverse : ℕ) : ℚ)
          * (b.toNat : ℚ) ^ (e - post.length))) := by
  have h2 : ¬ b < 2 := fun h => by
    have := UInt64.lt_iff_toNat_lt.mp h
    change b.toNat < (2 : ℕ) at this
    omega
  have h36 : ¬ 36 < b := fun h => by
    have := UInt64.lt_iff_toNat_lt.mp h
    change (36 : ℕ) < b.toNat at this
    omega
  have hrange : (b < 2 || 36 < b) = false := by simp [h2, h36]
  set body := pre ++ (if point then ['.'] else []) ++ post with hbody
  have hbody_ne : body ≠ [] := by simp [hbody, hne]
  have hdig_pre : ∀ c ∈ pre, (c == '.') = false := fun c hc => by
    obtain ⟨d, hd, -⟩ := hpre c hc
    exact beq_point_eq_false_of_charToDigit c d hd
  have hmem_body : ∀ c ∈ body,
      c = '.' ∨ ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat := by
    intro c hc
    simp only [hbody, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact Or.inr (hpre c hc)
    · cases point
      · simp at hc
      · exact Or.inl (by simpa using hc)
    · exact Or.inr (hpost c hc)
  have hsplitE : splitExponent b (signChars neg ++ body ++ suffix)
      = some (signChars neg ++ body, e) := by
    rcases hsuffix with ⟨rfl, rfl⟩ | ⟨rfl, he, he0⟩
    · rw [List.append_nil]
      refine splitExponent_no_exp b neg body (fun hb15 c hc => ?_) (fun _ c hc => ?_)
      · rcases hmem_body c hc with rfl | ⟨d, hd, hlt⟩
        · decide
        · exact isExpChar_eq_false_of_charToDigit c d hd (by omega)
      · rcases hmem_body c hc with rfl | ⟨d, hd, -⟩
        · decide
        · exact isSignChar_eq_false_of_charToDigit c d hd
    · exact splitExponent_append b neg body hbody_ne fmt e he he0
  have hsign : ∀ c ∈ signChars neg, (c == '.') = false := by
    cases neg <;> simp [signChars]
  have hdig_pre' : ∀ c ∈ signChars neg ++ pre, (c == '.') = false := fun c hc => by
    rcases List.mem_append.mp hc with h | h
    · exact hsign c h
    · exact hdig_pre c h
  have hsplitP : splitPoint (signChars neg ++ body) e
      = some (signChars neg ++ (pre ++ post), e - post.length) := by
    cases point
    · have hpost_nil := hpoint rfl
      subst hpost_nil
      simp only [hbody, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      rw [splitPoint_no_point _ e hdig_pre']
      simp
    · rw [show signChars neg ++ body = (signChars neg ++ pre) ++ '.' :: post by simp [hbody]]
      rw [splitPoint_append _ post e hdig_pre' (fun c hc => ?_) (fitsInt64_of_natAbs_lt _ hfit),
        List.append_assoc]
      obtain ⟨d, hd, -⟩ := hpost c (List.mem_of_mem_head? hc)
      exact isSignChar_eq_false_of_charToDigit c d hd
  obtain ⟨n, hparse, hval⟩ := parseSignedDigits_eq b hb neg (pre ++ post) (by simp [hne])
    (fun c hc => by
      rcases List.mem_append.mp hc with h | h
      · exact hpre c h
      · exact hpost c h)
  unfold fromSci
  rw [hrange, String.toList_ofList]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show signChars neg ++ pre ++ (if point then ['.'] else []) ++ post ++ suffix
      = signChars neg ++ body ++ suffix by simp [hbody]]
  rw [hsplitE]
  simp only [Bind.bind, Option.bind, hsplitP, hparse, Pure.pure, Option.some.injEq]
  rw [← ofRat_toRat (ofSciParts _ _ _ _), toRat_ofSciParts b (by omega), hval]
  cases neg <;> simp

/-! ### Trailing zeros -/

theorem dropTrailingZeros_spec (cs : List Char) :
    ∃ k, cs = SciNumber.dropTrailingZeros cs ++ List.replicate k '0' := by
  set k := (cs.reverse.takeWhile (· == '0')).length with hk
  refine ⟨k, ?_⟩
  unfold SciNumber.dropTrailingZeros
  have h := List.takeWhile_append_dropWhile (p := (· == '0')) (l := cs.reverse)
  have hrep : cs.reverse.takeWhile (· == '0') = List.replicate k '0' := by
    rw [List.eq_replicate_iff]
    exact ⟨hk.symm, fun c hc => by simpa using List.mem_takeWhile_imp hc⟩
  conv_lhs => rw [← List.reverse_reverse cs, ← h]
  rw [List.reverse_append, hrep, List.reverse_replicate]

theorem dropTrailingZerosWithin_spec (j : ℕ) (cs : List Char) :
    ∃ k, cs = SciNumber.dropTrailingZerosWithin j cs ++ List.replicate k '0' ∧
      cs.length - j ≤ (SciNumber.dropTrailingZerosWithin j cs).length := by
  simp only [SciNumber.dropTrailingZerosWithin]
  obtain ⟨k, hk⟩ := dropTrailingZeros_spec (cs.drop (cs.length - j))
  refine ⟨k, ?_, ?_⟩
  · conv_lhs => rw [← List.take_append_drop (cs.length - j) cs]
    rw [List.append_assoc, ← hk]
  · rw [List.length_append, List.length_take]
    omega

theorem ne_nil_of_eq_append_replicate (cs cs' : List Char) (k : ℕ) (c : Char)
    (h : cs = cs' ++ List.replicate k '0') (hc : cs.head? = some c) (hc0 : c ≠ '0') :
    cs' ≠ [] := by
  rintro rfl
  rw [List.nil_append] at h
  subst h
  cases k with
  | zero => simp at hc
  | succ k =>
    simp only [List.replicate_succ, List.head?_cons, Option.some.injEq] at hc
    exact hc0 hc.symm

/-! ### Values -/

theorem mantissa_eq_ofDigits (x : SciNumber) :
    x.mantissa = Nat.ofDigits x.base.toNat (x.digits.toList.map UInt64.toNat).reverse := by
  unfold SciNumber.mantissa
  rw [← Array.foldl_toList]
  have : x.digits.toList.foldl (fun acc d => acc * x.base.toNat + d.toNat) 0
      = (x.digits.toList.map UInt64.toNat).foldl (fun acc d => acc * x.base.toNat + d) 0 := by
    rw [List.foldl_map]
  rw [this, foldl_horner_eq_ofDigits]

/-- Moving `k` trailing zero digits into the exponent. -/
theorem sciValue_eq (b : ℕ) (hb : 0 < b) (neg : Bool) (L : List ℕ) (k : ℕ) (scale e' : ℤ)
    (he' : e' = k - scale) :
    (if neg then -1 else 1) * ((Nat.ofDigits b (L ++ List.replicate k 0).reverse : ℕ) : ℚ)
        * (b : ℚ) ^ (-scale)
      = (if neg then -1 else 1) * ((Nat.ofDigits b L.reverse : ℕ) : ℚ) * (b : ℚ) ^ e' := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [List.reverse_append, List.reverse_replicate, Nat.ofDigits_append,
    Nat.ofDigits_replicate_zero, List.length_replicate, he', sub_eq_add_neg, zpow_add₀ hbq,
    zpow_natCast]
  push_cast
  ring

/-! ### The branches of `toChars` -/

theorem charToDigit_zero_below (b : UInt64) (hb : 2 ≤ b.toNat) :
    ∃ d, charToDigit '0' = some d ∧ d.toNat < b.toNat :=
  ⟨0, by decide, by change 0 < b.toNat; omega⟩

/-- Zero: `"0"`, optionally with a point and trailing zeros. -/
theorem fromSci_zero_shape (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36) (neg : Bool)
    (scale : ℤ) (hs : scale.natAbs < 2 ^ 63) (itz : Bool) :
    fromSci (String.ofList (signChars neg ++ '0' ::
      (if itz && 0 < scale then '.' :: List.replicate scale.toNat '0' else []))) b
      = some (ofRat 0) := by
  have h0 := charToDigit_zero_below b hb
  split
  · have := fromSci_shape b hb hb' neg ['0'] (List.replicate scale.toNat '0') true (by simp)
      (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact h0)
      (fun c hc => by rw [List.mem_replicate] at hc; rw [hc.2]; exact h0)
      (by simp) {} 0 [] (Or.inl ⟨rfl, rfl⟩) (by rw [List.length_replicate]; omega)
    simp only [↓reduceIte, List.append_nil, List.append_assoc, List.cons_append, List.nil_append,
      List.map_cons, List.map_replicate, digitVal_zero] at this
    rw [this]
    congr 2
    rw [← List.replicate_succ, List.reverse_replicate, Nat.ofDigits_replicate_zero]
    simp
  · have := fromSci_shape b hb hb' neg ['0'] [] false (fun _ => rfl)
      (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact h0)
      (fun c hc => by simp at hc) (by simp) {} 0 [] (Or.inl ⟨rfl, rfl⟩) (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.map_cons, List.map_nil,
      digitVal_zero] at this
    rw [this]
    congr 2
    simp [Nat.ofDigits_singleton]

/-- The value spelled by `cs'` with exponent `E`. -/
def sciVal (b : UInt64) (neg : Bool) (cs' : List Char) (E : ℤ) : ℚ :=
  (if neg then -1 else 1) * ((Nat.ofDigits b.toNat (cs'.map digitVal).reverse : ℕ) : ℚ)
    * (b.toNat : ℚ) ^ E

/-- Exponent form with a single digit: `d` then the exponent suffix. -/
theorem fromSci_exp_single_shape (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36)
    (neg : Bool) (d : Char) (hd : ∃ k, charToDigit d = some k ∧ k.toNat < b.toNat)
    (fmt : SciFormat) (e : ℤ) (he : e.natAbs < 2 ^ 63) (he0 : 15 ≤ b.toNat → e ≠ 0) :
    fromSci (String.ofList (signChars neg ++ [d] ++ SciNumber.exponentChars fmt b e)) b
      = some (ofRat (sciVal b neg [d] e)) := by
  have := fromSci_shape b hb hb' neg [d] [] false (fun _ => rfl)
    (fun c hc => by rw [List.mem_singleton] at hc; rw [hc]; exact hd) (fun c hc => by simp at hc)
    (by simp) fmt e (SciNumber.exponentChars fmt b e) (Or.inr ⟨rfl, he, he0⟩)
    (by simpa using he)
  simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.length_nil, Nat.cast_zero,
    sub_zero] at this
  simpa [sciVal] using this

/-- Exponent form with several digits: `d.ddd` then the exponent suffix. -/
theorem fromSci_exp_point_shape (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36)
    (neg : Bool) (d : Char) (rest : List Char)
    (hcs : ∀ c ∈ d :: rest, ∃ k, charToDigit c = some k ∧ k.toNat < b.toNat)
    (fmt : SciFormat) (e : ℤ) (he : e.natAbs < 2 ^ 63) (he0 : 15 ≤ b.toNat → e ≠ 0)
    (hfit : (e - rest.length).natAbs < 2 ^ 63) :
    fromSci (String.ofList (signChars neg ++ d :: '.' :: rest ++ SciNumber.exponentChars fmt b e))
        b
      = some (ofRat (sciVal b neg (d :: rest) (e - rest.length))) := by
  have := fromSci_shape b hb hb' neg [d] rest true (by simp)
    (fun c hc => by rw [List.mem_singleton] at hc; rw [hc]; exact hcs d List.mem_cons_self)
    (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) (by simp) fmt e
    (SciNumber.exponentChars fmt b e) (Or.inr ⟨rfl, he, he0⟩) hfit
  simp only [↓reduceIte, List.cons_append, List.nil_append] at this
  simpa [sciVal] using this

/-- Plain form with nothing after the point: the digits alone. -/
theorem fromSci_plain_shape (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36) (neg : Bool)
    (cs' : List Char) (hne : cs' ≠ [])
    (hcs : ∀ c ∈ cs', ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) :
    fromSci (String.ofList (signChars neg ++ cs')) b = some (ofRat (sciVal b neg cs' 0)) := by
  have := fromSci_shape b hb hb' neg cs' [] false (fun _ => rfl) hcs (fun c hc => by simp at hc)
    hne {} 0 [] (Or.inl ⟨rfl, rfl⟩) (by simp)
  simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.length_nil, Nat.cast_zero,
    sub_zero] at this
  simpa [sciVal] using this

/-- Plain form below one: `0.000ddd`. -/
theorem fromSci_small_shape (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36) (neg : Bool)
    (z : ℕ) (cs' : List Char)
    (hcs : ∀ c ∈ cs', ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat)
    (hfit : ((z + cs'.length : ℕ) : ℤ).natAbs < 2 ^ 63) :
    fromSci (String.ofList (signChars neg ++ '0' :: '.' :: (List.replicate z '0' ++ cs'))) b
      = some (ofRat (sciVal b neg cs' (-((z + cs'.length : ℕ) : ℤ)))) := by
  have h0 := charToDigit_zero_below b hb
  have := fromSci_shape b hb hb' neg ['0'] (List.replicate z '0' ++ cs') true (by simp)
    (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact h0)
    (fun c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · rw [List.mem_replicate] at hc; rw [hc.2]; exact h0
      · exact hcs c hc)
    (by simp) {} 0 [] (Or.inl ⟨rfl, rfl⟩)
    (by simp only [List.length_append, List.length_replicate]; omega)
  simp only [↓reduceIte, List.append_nil, List.append_assoc, List.cons_append, List.nil_append,
    List.length_append, List.length_replicate, zero_sub, List.map_cons, List.map_append,
    List.map_replicate, digitVal_zero] at this
  rw [this]
  congr 2
  simp only [sciVal]
  rw [show (0 :: (List.replicate z 0 ++ cs'.map digitVal)).reverse
      = (cs'.map digitVal).reverse ++ List.replicate (z + 1) 0 by
      simp [List.replicate_succ']]
  rw [Nat.ofDigits_append_replicate_zero]

/-- Plain form with digits on both sides of the point. -/
theorem fromSci_split_shape (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36) (neg : Bool)
    (cs' : List Char) (before : ℕ) (hbefore : 0 < before) (hlt : before < cs'.length)
    (hcs : ∀ c ∈ cs', ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat)
    (hfit : ((cs'.length - before : ℕ) : ℤ).natAbs < 2 ^ 63) :
    fromSci (String.ofList (signChars neg ++ (cs'.take before ++ '.' :: cs'.drop before))) b
      = some (ofRat (sciVal b neg cs' (-((cs'.length - before : ℕ) : ℤ)))) := by
  have := fromSci_shape b hb hb' neg (cs'.take before) (cs'.drop before) true (by simp)
    (fun c hc => hcs c (List.mem_of_mem_take hc)) (fun c hc => hcs c (List.mem_of_mem_drop hc))
    (by rw [Ne, List.take_eq_nil_iff]; push Not; exact ⟨by omega, by rintro rfl; simp at hlt⟩)
    {} 0 [] (Or.inl ⟨rfl, rfl⟩) (by rw [List.length_drop]; simpa using hfit)
  simp only [↓reduceIte, List.append_nil, List.append_assoc, List.singleton_append,
    List.take_append_drop, List.length_drop, zero_sub] at this
  rw [this]
  rfl

theorem digitToChar_ne_zero (d : UInt64) (hd : d.toNat < 36) (h : d ≠ 0) (u : Bool) :
    digitToChar d u ≠ '0' := by
  intro hc
  have := charToDigit_digitToChar' d hd u
  rw [hc, show charToDigit '0' = some 0 from by decide] at this
  exact h (Option.some.inj this).symm

/-! ### The round trip -/

/-- Parsing the rendering of a well-formed `SciNumber` (base in `[2, 36]`, digits below the
base, nonzero leading digit; see `toSciNumber_wellFormed`) in any format with a negative
exponent threshold recovers its value.  The scale and the exponent must fit in a signed 64-bit
integer, as the parser requires. -/
theorem fromSci_toString (x : SciNumber) (fmt : SciFormat) (hb : 2 ≤ x.base.toNat)
    (hb' : x.base.toNat ≤ 36) (hthr : fmt.negExpThreshold < 0)
    (hd : ∀ d ∈ x.digits, d.toNat < x.base.toNat)
    (hlead : ∀ h : 0 < x.digits.size, x.digits[0]'h ≠ 0)
    (hs : x.scale.natAbs < 2 ^ 63) (he : x.exponent.natAbs < 2 ^ 63) :
    fromSci (x.toString fmt) x.base = some (ofRat x.value) := by
  obtain ⟨neg, b, digits, scale⟩ := x
  simp only [SciNumber.exponent] at hb hb' hd hlead hs he ⊢
  have hb0 : 0 < b.toNat := by omega
  set u := !fmt.lowercase with hu
  have hcs_map : (digits.map fun d => digitToChar d u).toList
      = digits.toList.map fun d => digitToChar d u := Array.toList_map
  set cs := digits.toList.map fun d => digitToChar d u with hcs
  have hcs_dig : ∀ c ∈ cs, ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat := by
    intro c hc
    rw [hcs, List.mem_map] at hc
    obtain ⟨d, hd', rfl⟩ := hc
    have hdb := hd d (Array.mem_toList_iff.mp hd')
    exact ⟨d, charToDigit_digitToChar' d (by omega) u, hdb⟩
  have hcs_val : cs.map digitVal = digits.toList.map UInt64.toNat := by
    rw [hcs, List.map_map]
    refine List.map_congr_left fun d hd' => ?_
    exact digitVal_digitToChar d (by have := hd d (Array.mem_toList_iff.mp hd'); omega) u
  have hcs_len : cs.length = digits.size := by rw [hcs, List.length_map, Array.length_toList]
  have hval : SciNumber.value ⟨neg, b, digits, scale⟩ = sciVal b neg cs (-scale) := by
    simp only [SciNumber.value, sciVal, mantissa_eq_ofDigits, hcs_val]
  have key : ∀ (cs' : List Char) (k : ℕ) (E : ℤ), cs = cs' ++ List.replicate k '0' →
      E = k - scale → sciVal b neg cs' E = SciNumber.value ⟨neg, b, digits, scale⟩ := by
    intro cs' k E hcs' hE
    rw [hval, hcs', sciVal, sciVal, List.map_append, List.map_replicate, digitVal_zero,
      sciValue_eq b.toNat hb0 neg _ k scale E hE]
  unfold SciNumber.toString SciNumber.toChars
  dsimp only [SciNumber.exponent]
  rw [hcs_map]
  by_cases h0 : digits.isEmpty
  · rw [ite_eq_left h0]
    have hdig0 : digits = #[] := Array.isEmpty_iff.mp h0
    have hcs0 : cs = [] := by rw [hcs, hdig0]; rfl
    have B := fromSci_zero_shape b hb hb' neg scale hs fmt.includeTrailingZeros
    simp only [signChars] at B
    rw [B, hval, hcs0]
    simp [sciVal]
  · have hsz : 0 < digits.size := by
      rcases Nat.eq_zero_or_pos digits.size with h | h
      · exact absurd (Array.isEmpty_iff.mpr (Array.eq_empty_of_size_eq_zero h)) h0
      · exact h
    rw [ite_eq_right h0]
    have hhead : ∃ c, cs.head? = some c ∧ c ≠ '0' := by
      obtain ⟨d0, ds, hds⟩ := List.exists_cons_of_ne_nil (show digits.toList ≠ [] by
        intro h
        have := congrArg List.length h
        simp only [Array.length_toList, List.length_nil] at this
        omega)
      refine ⟨digitToChar d0 u, by rw [hcs, hds]; rfl, ?_⟩
      have hd0 : digits[0]'hsz = d0 := by
        rw [← Array.getElem_toList (by simpa using hsz)]
        simp [hds]
      refine digitToChar_ne_zero d0
        (by have := hd d0 (Array.mem_toList_iff.mp (hds ▸ List.mem_cons_self)); omega) ?_ u
      rw [← hd0]
      exact hlead hsz
    obtain ⟨c0, hc0, hc0ne⟩ := hhead
    have hcs_ne : cs ≠ [] := by
      intro h
      rw [h] at hc0
      simp at hc0
    have htrim : ∀ (cs' : List Char) (k : ℕ), cs = cs' ++ List.replicate k '0' →
        cs' ≠ [] ∧ (∀ c ∈ cs', ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) ∧
          cs.length = cs'.length + k := by
      intro cs' k hk
      refine ⟨ne_nil_of_eq_append_replicate cs cs' k c0 hk hc0 hc0ne,
        fun c hc => hcs_dig c (hk ▸ List.mem_append_left _ hc), ?_⟩
      rw [hk, List.length_append, List.length_replicate]
    split
    · -- exponent form
      rename_i hcond
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hcond
      generalize hcs' : (if fmt.includeTrailingZeros then cs else SciNumber.dropTrailingZeros cs)
        = cs'
      obtain ⟨k, hk⟩ : ∃ k, cs = cs' ++ List.replicate k '0' := by
        rw [← hcs']
        split
        · exact ⟨0, by simp⟩
        · exact dropTrailingZeros_spec cs
      obtain ⟨hne', hdig', hlen'⟩ := htrim cs' k hk
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hne'
      simp only [List.length_cons] at hlen'
      cases rest with
      | nil =>
        simp only [List.length_nil] at hlen'
        have B := fromSci_exp_single_shape b hb hb' neg d (hdig' d List.mem_cons_self) fmt _ he
          (fun _ => by omega)
        simp only [signChars] at B
        rw [B, key [d] k (↑digits.size - 1 - scale) hk (by omega)]
      | cons c rest =>
        simp only [List.length_cons] at hlen'
        have B := fromSci_exp_point_shape b hb hb' neg d (c :: rest) hdig' fmt _ he
          (fun _ => by omega) (by simp only [List.length_cons]; omega)
        simp only [signChars] at B
        rw [B, key (d :: c :: rest) k (↑digits.size - 1 - scale - ↑(c :: rest).length) hk
          (by simp only [List.length_cons]; omega)]
    · rename_i hcond
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, not_lt] at hcond
      split
      · -- integer
        rename_i hscale
        have B := fromSci_plain_shape b hb hb' neg cs hcs_ne hcs_dig
        simp only [signChars] at B
        rw [B, key cs 0 0 (by simp) (by omega)]
      · rename_i hscale
        generalize hcs' : (if fmt.includeTrailingZeros then cs
          else SciNumber.dropTrailingZerosWithin scale.toNat cs) = cs'
        obtain ⟨k, hk, hkle⟩ :
            ∃ k, cs = cs' ++ List.replicate k '0' ∧ k ≤ scale.toNat := by
          rw [← hcs']
          split
          · exact ⟨0, by simp, by omega⟩
          · obtain ⟨k, hk, hle⟩ := dropTrailingZerosWithin_spec scale.toNat cs
            refine ⟨k, hk, ?_⟩
            have := congrArg List.length hk
            rw [List.length_append, List.length_replicate] at this
            omega
        obtain ⟨hne', hdig', hlen'⟩ := htrim cs' k hk
        have hpos : 0 < cs'.length := List.length_pos_of_ne_nil hne'
        split
        · -- below one
          have B := fromSci_small_shape b hb hb' neg (-(↑digits.size - 1 - scale) - 1).toNat cs'
            hdig' (by omega)
          simp only [signChars] at B
          rw [B, key cs' k
            (-(((-(↑digits.size - 1 - scale) - 1).toNat + cs'.length : ℕ) : ℤ)) hk (by omega)]
        · by_cases hlt : (↑digits.size - 1 - scale).toNat + 1 < cs'.length
          · -- point inside the digits
            rw [ite_eq_left hlt]
            have B := fromSci_split_shape b hb hb' neg cs' ((↑digits.size - 1 - scale).toNat + 1)
              (by omega) hlt hdig' (by omega)
            simp only [signChars] at B
            rw [B, key cs' k
              (-((cs'.length - ((↑digits.size - 1 - scale).toNat + 1) : ℕ) : ℤ)) hk
              (by omega)]
          · rw [ite_eq_right hlt]
            have B := fromSci_plain_shape b hb hb' neg cs' hne' hdig'
            simp only [signChars] at B
            rw [B, key cs' k 0 hk (by omega)]

/-! ### Through `toSci` -/

lemma valid_negExpThreshold {o : SciOptions} (hv : o.valid = true) :
    o.format.negExpThreshold < 0 := by
  unfold SciOptions.valid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact hv.1.2

lemma valid_of_toSciNumber {q : AzRat} {o : SciOptions} {x : SciNumber}
    (hx : q.toSciNumber o = some x) : o.valid = true := by
  by_contra h
  have h' : o.valid = false := by simpa using h
  simp [toSciNumber, h'] at hx

/-- `fromSci` undoes `toSci` up to the rounding `toSci` performed: the parsed value is the value
of the intermediate `SciNumber` (which the value theorems of `Equiv/ToSci.lean` identify as the
rounding of `toRat q` to the requested target).  Scale and exponent must fit in a signed 64-bit
integer. -/
theorem fromSci_toSci (q : AzRat) (o : SciOptions) (x : SciNumber) (hx : q.toSciNumber o = some x)
    (hs : x.scale.natAbs < 2 ^ 63) (he : x.exponent.natAbs < 2 ^ 63) :
    (q.toSci o).bind (fun s => fromSci s o.base) = some (ofRat x.value) := by
  have hv := valid_of_toSciNumber hx
  obtain ⟨hb, hb'⟩ := valid_base hv
  obtain ⟨hbase, hd, hlead⟩ := toSciNumber_wellFormed q o x hx
  unfold toSci
  rw [hx, Option.map_some, Option.bind_some]
  rw [← hbase] at hb hb' hd ⊢
  exact fromSci_toString x o.format hb hb' (valid_negExpThreshold hv) hd hlead hs he

/-- When `toSciExact` holds, `fromSci` recovers `q` itself. -/
theorem fromSci_toSci_of_exact (q : AzRat) (o : SciOptions) (x : SciNumber)
    (hx : q.toSciNumber o = some x) (hs : x.scale.natAbs < 2 ^ 63)
    (he : x.exponent.natAbs < 2 ^ 63) (hex : q.toSciExact o = true) :
    (q.toSci o).bind (fun s => fromSci s o.base) = some q := by
  rw [fromSci_toSci q o x hx hs he]
  obtain ⟨x', hx', hval⟩ := (toSciExact_iff q o).mp hex
  rw [hx] at hx'
  cases hx'
  have : x.value = toRat q := by exact_mod_cast hval
  rw [this, ofRat_toRat]

end Azurite.AzRat
