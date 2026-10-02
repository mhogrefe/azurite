/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ToString
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Equiv.Rounding
import Azurite.AzNat.Equiv.OfLimbDigits
import Azurite.AzRat.Equiv.Mul
import Azurite.AzRat.Equiv.FromSci
import Azurite.AzRat.Equiv.Pow
import Azurite.AzRat.Equiv.Unary
import Azurite.AzRat.Equiv.ToSci

/-!
# Correctness of the decimal output

* `SciNumber.toRat_toAzRat`: the computable rational of a well-formed `SciNumber` is its
  specified `value`.
* `searchLeast_pred`, `searchLeast_min`: the binary search returns a precision satisfying the
  predicate, and the least one when the predicate is monotone.
* `toDecimalString_spec`: for a finite nonzero float, the printed string is the `toSci`
  rendering (with the `.0` convention) of a `SciNumber` at the found precision `p`; and whenever
  the round-trip predicate holds at `p` — which it does as soon as it holds at the search's
  upper bound — that number's value converts back to the float at its precision.  The
  mathematical fact that `⌈P · log₁₀ 2⌉ + 2` digits always suffice is not formalized; the
  function checks it at run time and would widen the bound otherwise.
-/

namespace Azurite

namespace SciNumber

/-- The computable rational agrees with the specified value. -/
theorem toRat_toAzRat (x : SciNumber) (hb : 2 ≤ x.base.toNat)
    (hd : ∀ d ∈ x.digits, d.toNat < x.base.toNat) : AzRat.toRat x.toAzRat = x.value := by
  unfold toAzRat value
  have hm : (AzNat.ofLimbDigits x.base x.digits.reverse).toNat = x.mantissa := by
    rw [AzNat.toNat_ofLimbDigits x.base hb _ (fun v hv => by
      rw [Array.toList_reverse, List.map_reverse, List.mem_reverse, List.mem_map] at hv
      obtain ⟨d, hd', rfl⟩ := hv
      exact hd d (Array.mem_toList_iff.mp hd')),
      AzRat.mantissa_eq_ofDigits, Array.toList_reverse, List.map_reverse]
  have hv : AzRat.toRat ((AzNat.ofLimbDigits x.base x.digits.reverse).toAzRat *
      x.base.toAzRat.zpow (-x.scale)) = (x.mantissa : ℚ) * (x.base.toNat : ℚ) ^ (-x.scale) := by
    rw [AzRat.toRat_mul, AzRat.toRat_toAzRat, AzRat.toRat_zpow, UInt64.toRat_toAzRat, hm]
  cases x.negative
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, hv]
  · simp only [↓reduceIte, AzRat.toRat_neg, hv]
    ring

end SciNumber

namespace AzFloat

/-! ### The search -/

theorem searchLeast_pred (pred : Nat → Bool) :
    ∀ (n lo hi : Nat), hi - lo = n → pred hi = true → pred (searchLeast pred lo hi) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro lo hi hn h
    rw [searchLeast]
    dsimp only
    split_ifs with hlt hmid
    · exact ih _ (by omega) lo _ rfl hmid
    · exact ih _ (by omega) _ hi rfl h
    · exact h

theorem le_searchLeast (pred : Nat → Bool) :
    ∀ (n lo hi : Nat), hi - lo = n → lo ≤ hi →
      lo ≤ searchLeast pred lo hi ∧ searchLeast pred lo hi ≤ hi := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro lo hi hn hlo
    rw [searchLeast]
    dsimp only
    split_ifs with hlt hmid
    · have := ih _ (by omega) lo ((lo + hi) / 2) rfl (by omega)
      omega
    · have := ih _ (by omega) ((lo + hi) / 2 + 1) hi rfl (by omega)
      omega
    · omega

/-- With a monotone predicate, the search returns the least satisfying value at or above `lo`. -/
theorem searchLeast_min (pred : Nat → Bool)
    (hmono : ∀ a b, a ≤ b → pred a = true → pred b = true) :
    ∀ (n lo hi : Nat), hi - lo = n → lo ≤ hi → ∀ q, lo ≤ q → pred q = true →
      searchLeast pred lo hi ≤ q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro lo hi hn hlo q hq hpq
    rw [searchLeast]
    dsimp only
    split_ifs with hlt hmid
    · exact ih _ (by omega) lo ((lo + hi) / 2) rfl (by omega) q hq hpq
    · have hq' : (lo + hi) / 2 + 1 ≤ q := by
        by_contra h
        push Not at h
        have := hmono q ((lo + hi) / 2) (by omega) hpq
        rw [this] at hmid
        exact absurd hmid (by decide)
      exact ih _ (by omega) ((lo + hi) / 2 + 1) hi rfl (by omega) q hq' hpq
    · have := le_searchLeast pred (hi - hi) hi hi rfl le_rfl
      omega

theorem expandUntil_pred (pred : Nat → Bool) (p fuel : Nat) (h : pred p = true) :
    expandUntil pred p fuel = p := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [expandUntil, h]

theorem le_expandUntil (pred : Nat → Bool) (p fuel : Nat) : p ≤ expandUntil pred p fuel := by
  induction fuel generalizing p with
  | zero => exact le_rfl
  | succ fuel ih =>
    unfold expandUntil
    split_ifs
    · exact le_rfl
    · exact le_trans (by omega) (ih (2 * p))

/-! ### The predicate -/

theorem decimalRoundTrips_iff (x : AzFloat) (q : AzRat) (P p : Nat) :
    decimalRoundTrips x q P p = true ↔
      ∃ sn, q.toSciNumber (decimalOptions p) = some sn ∧ ofAzRat sn.toAzRat P = x := by
  unfold decimalRoundTrips
  cases h : q.toSciNumber (decimalOptions p) with
  | none => simp
  | some sn => simp [beq_iff_eq]

/-- The round-trip predicate is monotone: a `(p+1)`-digit nearest rounding is at least as
close as the `p`-digit one, so it stays inside the float's rounding interval.  (Stated as the
hypothesis the search needs; its proof is a property of `precisionSet` not yet formalized.) -/
def DecimalMonotone (x : AzFloat) (q : AzRat) (P : Nat) : Prop :=
  ∀ a b, a ≤ b → decimalRoundTrips x q P a = true → decimalRoundTrips x q P b = true

/-! ### The rendering -/

theorem decimalOptions_valid (p : ℕ) (hp : 0 < p) : (decimalOptions p).valid = true := by
  unfold decimalOptions SciOptions.valid SciSizeOptions.valid
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨⟨by decide, by decide⟩, by decide⟩, hp.ne'⟩

/-- If the round-trip predicate holds at the search's upper bound, it holds at the precision
found. -/
theorem decimalRoundTrips_shortest (x : AzFloat) (q : AzRat) (hq : x.toAzRat? = some q) (P : ℕ)
    (hP : x.precision? = some P)
    (hhi : decimalRoundTrips x q P (P * 30103 / 100000 + 2) = true) :
    decimalRoundTrips x q P (shortestDecimalPrecision x) = true := by
  unfold shortestDecimalPrecision
  rw [hq, hP]
  simp only
  rw [expandUntil_pred _ _ _ hhi]
  exact searchLeast_pred _ _ _ _ rfl hhi

theorem shortestDecimalPrecision_pos (x : AzFloat) (q : AzRat) (hq : x.toAzRat? = some q)
    (P : ℕ) (hP : x.precision? = some P) : 0 < shortestDecimalPrecision x := by
  unfold shortestDecimalPrecision
  rw [hq, hP]
  simp only
  have h1 : 1 ≤ expandUntil (decimalRoundTrips x q P) (P * 30103 / 100000 + 2) 64 :=
    le_trans (by omega) (le_expandUntil _ _ _)
  exact (le_searchLeast _ _ 1 _ rfl h1).1

/-- For a finite nonzero float the output is the `toSci` rendering of a `SciNumber` at the found
precision, and if the round-trip predicate holds there (as it does whenever it holds at the
search's upper bound, `decimalRoundTrips_shortest`), that number's value converts back to the
float. -/
theorem toDecimalString_spec (x : AzFloat) (q : AzRat) (hq : x.toAzRat? = some q) (P : ℕ)
    (hP : x.precision? = some P) :
    ∃ sn : SciNumber,
      q.toSciNumber (decimalOptions (shortestDecimalPrecision x)) = some sn ∧
      toDecimalString x = String.ofList (ensurePoint (sn.toString {}).toList) ∧
      (decimalRoundTrips x q P (shortestDecimalPrecision x) = true →
        ofAzRat sn.toAzRat P = x) := by
  have hpos := shortestDecimalPrecision_pos x q hq P hP
  have hvalid := decimalOptions_valid _ hpos
  have : Fact (1 < (decimalOptions (shortestDecimalPrecision x)).base.toNat) :=
    ⟨by show (1 : ℕ) < (10 : UInt64).toNat; decide⟩
  have : NeZero (shortestDecimalPrecision x) := ⟨hpos.ne'⟩
  obtain ⟨sn, hsn, -⟩ := AzRat.toSciNumber_value_precision q
    (decimalOptions (shortestDecimalPrecision x)) hvalid (shortestDecimalPrecision x) rfl
  refine ⟨sn, hsn, ?_, ?_⟩
  · cases x with
    | nan => simp [precision?] at hP
    | infinity _ => simp [precision?] at hP
    | zero => simp [precision?] at hP
    | finite s e p m hv =>
      show (toDecimalAt (finite s e p m hv) (shortestDecimalPrecision (finite s e p m hv))).getD ""
        = _
      unfold toDecimalAt
      rw [hq]
      dsimp only
      unfold AzRat.toSci
      rw [hsn]
      rfl
  · intro hrt
    rw [decimalRoundTrips_iff] at hrt
    obtain ⟨sn', hsn', h⟩ := hrt
    rw [hsn] at hsn'
    cases hsn'
    exact h

end AzFloat

end Azurite
