/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.OfString
import Azurite.AzFloat.Equiv.ToString
import Azurite.AzRat.Equiv.FromSci

/-!
# Correctness of decimal input

* `toVal_ofDecimalStringRound`: the float read from a parsable decimal is the rounding of the
  decimal's exact value, with the comparison tag.
* `ofDecimalString_toDecimalString`: reading `toDecimalString x` back at the precision of `x`
  gives `x` (under the run-time-checked round-trip predicate and the parser's exponent bounds).
  The writer's `.0` convention (`ensurePoint`) is undone by `fromSci` itself:
  `fromSci_ensurePoint_toString` redoes the branch analysis of `AzRat.fromSci_toString` for the
  three shapes without a point, where `.0` is appended or inserted before the exponent.
-/

namespace Azurite

open AzRat
open AzNat (charToDigit digitToChar)

namespace AzFloat

/-! ### `ensurePoint` -/

theorem ensurePoint_of_mem (cs : List Char) (h : '.' ∈ cs) : ensurePoint cs = cs := by
  unfold ensurePoint
  rw [ite_eq_left (by simpa using h)]

theorem ensurePoint_no_e (cs : List Char) (h1 : '.' ∉ cs) (h2 : ∀ c ∈ cs, (c == 'e') = false) :
    ensurePoint cs = cs ++ ['.', '0'] := by
  unfold ensurePoint
  rw [ite_eq_right (by simpa using h1), splitFirst_eq_none _ _ h2]

theorem ensurePoint_e (L M : List Char) (h1 : '.' ∉ L ++ 'e' :: M)
    (hL : ∀ c ∈ L, (c == 'e') = false) :
    ensurePoint (L ++ 'e' :: M) = L ++ '.' :: '0' :: 'e' :: M := by
  unfold ensurePoint
  rw [ite_eq_right (by simpa using h1), splitFirst_append _ L 'e' M hL rfl]

/-- Appending a zero digit and lowering the exponent by one keeps the value. -/
theorem sciVal_append_zero (b : UInt64) (hb : 0 < b.toNat) (neg : Bool) (cs : List Char)
    (E : ℤ) : sciVal b neg (cs ++ ['0']) (E - 1) = sciVal b neg cs E := by
  have hbq : (b.toNat : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold sciVal
  rw [List.map_append, List.map_singleton, digitVal_zero, List.reverse_append,
    List.reverse_singleton, List.singleton_append, Nat.ofDigits_cons, zpow_sub_one₀ hbq]
  push_cast
  field_simp
  ring

/-- A decimal digit character (base at most 14) is neither `'e'` nor `'.'`. -/
theorem digit_char_facts (b : UInt64) (hb' : b.toNat ≤ 14) (c : Char)
    (hc : ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) : (c == 'e') = false ∧ c ≠ '.' := by
  obtain ⟨d, hd, hdb⟩ := hc
  have h1 := isExpChar_eq_false_of_charToDigit c d hd (by omega)
  have h2 := beq_point_eq_false_of_charToDigit c d hd
  refine ⟨?_, by simpa using h2⟩
  simp only [isExpChar, Bool.or_eq_false_iff] at h1
  exact h1.1

/-- The exponent suffix with a lowercase `e`: `'e'` then sign and digits, no point. -/
theorem exponentChars_lower (fmt : SciFormat) (hlow : fmt.eLowercase = true) (b : UInt64)
    (e : ℤ) : ∃ tail, SciNumber.exponentChars fmt b e = 'e' :: tail ∧ '.' ∉ tail := by
  unfold SciNumber.exponentChars
  rw [hlow]
  refine ⟨_, rfl, ?_⟩
  intro h
  rw [List.mem_append] at h
  rcases h with h | h
  · split at h <;> simp at h
  · rw [toList_toString_int] at h
    rw [List.mem_append] at h
    rcases h with h | h
    · split at h <;> simp at h
    · have := isDigit_of_mem_toDigits10 h
      simp at this

/-- Parsing the `.0`-decorated rendering of a well-formed `SciNumber` in a base at most 14 with a
lowercase `e` recovers its value (the counterpart of `AzRat.fromSci_toString`). -/
theorem fromSci_ensurePoint_toString (x : SciNumber) (fmt : SciFormat) (hb : 2 ≤ x.base.toNat)
    (hb' : x.base.toNat ≤ 14) (hlow : fmt.eLowercase = true)
    (hd : ∀ d ∈ x.digits, d.toNat < x.base.toNat)
    (hlead : ∀ h : 0 < x.digits.size, x.digits[0]'h ≠ 0)
    (hs : x.scale.natAbs < 2 ^ 62) (he : x.exponent.natAbs < 2 ^ 62) :
    fromSci (String.ofList (ensurePoint (x.toString fmt).toList)) x.base
      = some (ofRat x.value) := by
  obtain ⟨neg, b, digits, scale⟩ := x
  simp only [SciNumber.exponent] at hb hb' hd hlead hs he ⊢
  have hb0 : 0 < b.toNat := by omega
  have hb36 : b.toNat ≤ 36 := by omega
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
  -- sign characters are neither `'e'` nor `'.'`
  have hsign_e : ∀ c ∈ signChars neg, (c == 'e') = false := by
    intro c hc; unfold signChars at hc; split at hc <;> simp at hc; subst hc; decide
  have hsign_p : '.' ∉ signChars neg := by
    intro hc; unfold signChars at hc; split at hc <;> simp at hc
  have hdig_e : ∀ (L : List Char), (∀ c ∈ L, ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) →
      ∀ c ∈ L, (c == 'e') = false := fun L hL c hc => (digit_char_facts b hb' c (hL c hc)).1
  have hdig_p : ∀ (L : List Char), (∀ c ∈ L, ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) →
      '.' ∉ L := fun L hL hc => (digit_char_facts b hb' '.' (hL '.' hc)).2 rfl
  have hno_e_sign_digits : ∀ (L : List Char),
      (∀ c ∈ L, ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) →
      ∀ c ∈ signChars neg ++ L, (c == 'e') = false := by
    intro L hL c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hsign_e c hc
    · exact hdig_e L hL c hc
  have hno_p_sign_digits : ∀ (L : List Char),
      (∀ c ∈ L, ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) →
      '.' ∉ signChars neg ++ L := by
    intro L hL hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hsign_p hc
    · exact hdig_p L hL hc
  -- the two no-point shapes: `sign digits` and `sign d e…`
  have plain_case : ∀ (cs' : List Char), cs' ≠ [] →
      (∀ c ∈ cs', ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat) →
      fromSci (String.ofList (ensurePoint (signChars neg ++ cs'))) b
        = some (ofRat (sciVal b neg cs' 0)) := by
    intro cs' hne hdig
    rw [ensurePoint_no_e _ (hno_p_sign_digits cs' hdig) (hno_e_sign_digits cs' hdig)]
    have hdig0 : ∀ c ∈ cs' ++ ['0'], ∃ d, charToDigit c = some d ∧ d.toNat < b.toNat := by
      intro c hc
      rw [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact hdig c hc
      · exact charToDigit_zero_below b hb
    have hpos : 0 < cs'.length := List.length_pos_of_ne_nil hne
    have B := fromSci_split_shape b hb hb36 neg (cs' ++ ['0']) cs'.length hpos
      (by simp) hdig0 (by simp)
    rw [List.take_left, List.drop_left] at B
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel_left,
      Nat.cast_one] at B
    rw [List.append_assoc, B, show (-1 : ℤ) = 0 - 1 by ring, sciVal_append_zero b hb0]
  simp only [SciNumber.toString, SciNumber.toChars, SciNumber.exponent, String.toList_ofList]
  rw [hcs_map]
  by_cases h0 : digits.isEmpty
  · rw [ite_eq_left h0]
    have hdig0 : digits = #[] := Array.isEmpty_iff.mp h0
    have hcs0 : cs = [] := by rw [hcs, hdig0]; rfl
    have hv0 : SciNumber.value ⟨neg, b, digits, scale⟩ = 0 := by
      rw [hval, hcs0]; simp [sciVal]
    rw [hv0]
    by_cases hitz : (fmt.includeTrailingZeros && decide (0 < scale)) = true
    · -- `0.000…` has a point
      rw [ite_eq_left hitz, ensurePoint_of_mem _ (by simp)]
      have B := fromSci_zero_shape b hb hb36 neg scale (by omega) fmt.includeTrailingZeros
      simp only [signChars] at B
      rw [ite_eq_left hitz] at B
      exact B
    · -- `0` alone: `0.0`
      rw [ite_eq_right hitz]
      have B := plain_case ['0'] (by simp) (fun c hc => by
        rw [List.mem_singleton] at hc; subst hc; exact charToDigit_zero_below b hb)
      simp only [signChars] at B
      rw [B, show sciVal b neg ['0'] 0 = 0 by cases neg <;> simp [sciVal, digitVal_zero]]
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
      obtain ⟨tail, htail, htail_p⟩ := exponentChars_lower fmt hlow b (↑digits.size - 1 - scale)
      cases rest with
      | nil =>
        simp only [List.length_nil] at hlen'
        -- `sign d e…` becomes `sign d.0e…`
        have hd_dig : ∃ k, charToDigit d = some k ∧ k.toNat < b.toNat := hdig' d List.mem_cons_self
        rw [htail]
        show fromSci (String.ofList (ensurePoint ((signChars neg ++ [d]) ++ 'e' :: tail))) b = _
        rw [ensurePoint_e _ _ (by
            intro h
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with (h | h) | h | h
            · exact hsign_p h
            · exact (digit_char_facts b hb' d hd_dig).2 h.symm
            · exact absurd h (by decide)
            · exact htail_p h)
          (hno_e_sign_digits [d] (fun c hc => by
            rw [List.mem_singleton] at hc; subst hc; exact hd_dig))]
        have hdig0 : ∀ c ∈ d :: ['0'], ∃ k, charToDigit c = some k ∧ k.toNat < b.toNat := by
          intro c hc
          rw [List.mem_cons, List.mem_singleton] at hc
          rcases hc with rfl | rfl
          · exact hd_dig
          · exact charToDigit_zero_below b hb
        have B := fromSci_exp_point_shape b hb hb36 neg d ['0'] hdig0 fmt (↑digits.size - 1 - scale)
          (by omega) (fun h => absurd h (by omega)) (by simp only [List.length_singleton]; omega)
        rw [htail] at B
        simp only [List.append_assoc, List.cons_append, List.nil_append] at B ⊢
        rw [B, List.length_singleton, Nat.cast_one, show [d, '0'] = [d] ++ ['0'] from rfl,
          sciVal_append_zero b hb0, key [d] k (↑digits.size - 1 - scale) hk (by omega)]
      | cons c rest =>
        simp only [List.length_cons] at hlen'
        rw [ensurePoint_of_mem _ (by simp)]
        have B := fromSci_exp_point_shape b hb hb36 neg d (c :: rest) hdig' fmt
          (↑digits.size - 1 - scale) (by omega) (fun h => absurd h (by omega))
          (by simp only [List.length_cons]; omega)
        simp only [signChars] at B
        rw [B, key (d :: c :: rest) k (↑digits.size - 1 - scale - ↑(c :: rest).length) hk
          (by simp only [List.length_cons]; omega)]
    · rename_i hcond
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hcond
      split
      · -- integer: `sign digits` becomes `sign digits.0`
        rename_i hscale
        have B := plain_case cs hcs_ne hcs_dig
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
        · -- below one: has a point
          rw [ensurePoint_of_mem _ (by simp)]
          have B := fromSci_small_shape b hb hb36 neg (-(↑digits.size - 1 - scale) - 1).toNat cs'
            hdig' (by omega)
          simp only [signChars] at B
          rw [B, key cs' k
            (-(((-(↑digits.size - 1 - scale) - 1).toNat + cs'.length : ℕ) : ℤ)) hk (by omega)]
        · by_cases hlt : (↑digits.size - 1 - scale).toNat + 1 < cs'.length
          · -- point inside the digits
            rw [ite_eq_left hlt, ensurePoint_of_mem _ (by simp)]
            have B := fromSci_split_shape b hb hb36 neg cs' ((↑digits.size - 1 - scale).toNat + 1)
              (by omega) hlt hdig' (by omega)
            simp only [signChars] at B
            rw [B, key cs' k
              (-((cs'.length - ((↑digits.size - 1 - scale).toNat + 1) : ℕ) : ℤ)) hk
              (by omega)]
          · -- no point: `sign digits` becomes `sign digits.0`
            rw [ite_eq_right hlt]
            have B := plain_case cs' hne' hdig'
            simp only [signChars] at B
            rw [B, key cs' k 0 hk (by omega)]

/-! ### The reader -/

/-- The rendering always has a point. -/
theorem mem_ensurePoint (cs : List Char) : '.' ∈ ensurePoint cs := by
  unfold ensurePoint
  split
  · rename_i h; simpa using h
  · split
    · simp
    · simp

/-- The three special spellings have no point, so a rendering is never one of them. -/
theorem ensurePoint_ne_special (cs : List Char) :
    String.ofList (ensurePoint cs) ≠ "NaN" ∧ String.ofList (ensurePoint cs) ≠ "Infinity" ∧
      String.ofList (ensurePoint cs) ≠ "-Infinity" := by
  have hmem := mem_ensurePoint cs
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have h' := congrArg String.toList h <;>
    rw [String.toList_ofList] at h' <;> rw [h'] at hmem <;> revert hmem <;> decide

theorem ofDecimalStringRound_of_fromSci (s : String) (q : AzRat) (hq : fromSci s = some q)
    (hne : s ≠ "NaN" ∧ s ≠ "Infinity" ∧ s ≠ "-Infinity") (p : ℕ) (mode : RoundingMode) :
    ofDecimalStringRound s p mode = some (ofAzRatRound q p mode) := by
  unfold ofDecimalStringRound
  rw [ite_eq_right hne.1, ite_eq_right hne.2.1, ite_eq_right hne.2.2, hq, Option.map_some]

/-- The float read from a parsable decimal is the rounding of its exact value, and the tag
compares that rounding with the exact value. -/
theorem toVal_ofDecimalStringRound (s : String) (q : AzRat) (hq : fromSci s = some q)
    (hne : s ≠ "NaN" ∧ s ≠ "Infinity" ∧ s ≠ "-Infinity") (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ∃ r, ofDecimalStringRound s p mode = some r ∧
      r.1.toVal = some (RoundingTarget.round (floatSet p) mode (toRat q : ℝ)).val ∧
      ∃ v : ℝ, r.1.toVal = some (v : EReal) ∧ r.2 = compare v (toRat q : ℝ) := by
  refine ⟨ofAzRatRound q p mode, ofDecimalStringRound_of_fromSci s q hq hne p mode, ?_,
    snd_ofAzRatRound q p (Nat.pos_of_ne_zero (NeZero.ne p)) mode⟩
  rw [toVal_ofAzRatRound, val_round_floatSet]

@[simp] theorem ofDecimalStringRound_nan (p : ℕ) (mode : RoundingMode) :
    ofDecimalStringRound "NaN" p mode = some (nan, .eq) := by
  unfold ofDecimalStringRound
  rw [ite_eq_left rfl]

@[simp] theorem ofDecimalStringRound_infinity (p : ℕ) (mode : RoundingMode) :
    ofDecimalStringRound "Infinity" p mode = some (infinity true, .eq) := by
  unfold ofDecimalStringRound
  rw [ite_eq_right (by decide), ite_eq_left rfl]

@[simp] theorem ofDecimalStringRound_neg_infinity (p : ℕ) (mode : RoundingMode) :
    ofDecimalStringRound "-Infinity" p mode = some (infinity false, .eq) := by
  unfold ofDecimalStringRound
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

/-- A finite float's precision is positive. -/
theorem pos_of_precision?_eq_some (x : AzFloat) (P : ℕ) (hP : x.precision? = some P) : 0 < P := by
  cases x with
  | finite s e p m hv => simp only [precision?, Option.some.injEq] at hP; subst hP; exact hv.pos
  | _ => simp [precision?] at hP

/-- Reading the shortest decimal rendering back at the precision of the float gives the float,
under the round-trip predicate the writer checks at run time and the parser's exponent bounds. -/
theorem ofDecimalString_toDecimalString (x : AzFloat) (q : AzRat) (hq : x.toAzRat? = some q)
    (P : ℕ) (hP : x.precision? = some P)
    (hrt : decimalRoundTrips x q P (shortestDecimalPrecision x) = true)
    (hbounds : ∀ sn, q.toSciNumber (decimalOptions (shortestDecimalPrecision x)) = some sn →
      sn.scale.natAbs < 2 ^ 62 ∧ sn.exponent.natAbs < 2 ^ 62) :
    ofDecimalString (toDecimalString x) P = some x := by
  obtain ⟨sn, hsn, hstr, hback⟩ := toDecimalString_spec x q hq P hP
  obtain ⟨hs, he⟩ := hbounds sn hsn
  obtain ⟨hbase, hd, hlead⟩ := toSciNumber_wellFormed q _ sn hsn
  have hbase10 : (decimalOptions (shortestDecimalPrecision x)).base = 10 := rfl
  rw [hbase10] at hbase hd
  have hb : 2 ≤ sn.base.toNat := by rw [hbase]; decide
  have hb' : sn.base.toNat ≤ 14 := by rw [hbase]; decide
  have hd' : ∀ d ∈ sn.digits, d.toNat < sn.base.toNat := by rw [hbase]; exact hd
  have hparse := fromSci_ensurePoint_toString sn {} hb hb' rfl hd' hlead hs he
  rw [hbase] at hparse
  have : NeZero P := ⟨(pos_of_precision?_eq_some x P hP).ne'⟩
  unfold ofDecimalString
  rw [hstr, ofDecimalStringRound_of_fromSci _ _ hparse (ensurePoint_ne_special _), Option.map_some,
    Option.some.injEq, ofAzRatRound_eq_ofEReal, toRat_ofRat, ← SciNumber.toRat_toAzRat sn hb hd',
    ← ofAzRatRound_eq_ofEReal]
  exact hback hrt

end AzFloat

end Azurite
