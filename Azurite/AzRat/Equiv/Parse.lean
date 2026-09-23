/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Parse
import Azurite.AzRat.Equiv.Construct
import Azurite.AzInt.Equiv.Parse
import Azurite.AzNat.Equiv.ToStringBase

/-!
# Round-trip: `AzRat → String → AzRat`

`parse_toString : parse (toString q) = some q`. The proof is compositional:

* `AzInt.parse_toString` / `AzNat.parse_toString` round-trip the two components;
* the rendered numerator contains no `'/'` (its characters are a possible leading
  `'-'` plus decimal digits, by `AzNat.toString_char_digit`), so `splitAtSlash`
  recovers exactly the numerator/denominator split (`splitAtSlash_no_slash`,
  `splitAtSlash_append`);
* `ofSignAzNats_self` collapses the reconstruction back to `q`, since `q`'s fields
  are already reduced and zero-canonical.
-/

namespace Azurite.AzRat

/-- `splitAtSlash` on a slash-free list returns the whole list with no remainder. -/
theorem splitAtSlash_no_slash (l : List Char) (h : ∀ c ∈ l, c ≠ '/') :
    splitAtSlash l = (l, none) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [splitAtSlash, ite_eq_right (h c (List.mem_cons_self ..)),
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- `splitAtSlash` splits at the first `'/'`: a slash-free prefix is returned whole,
with everything after the slash as the remainder. -/
theorem splitAtSlash_append (l₁ l₂ : List Char) (h : ∀ c ∈ l₁, c ≠ '/') :
    splitAtSlash (l₁ ++ '/' :: l₂) = (l₁, some l₂) := by
  induction l₁ with
  | nil => simp [splitAtSlash]
  | cons c cs ih =>
    rw [List.cons_append, splitAtSlash, ite_eq_right (h c (List.mem_cons_self ..)),
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- No character of `AzInt.toString` is a `'/'`: the characters are a possible
leading `'-'` plus decimal digits. -/
theorem _root_.Azurite.AzInt.toString_ne_slash (z : AzInt) :
    ∀ c ∈ (AzInt.toString z).toList, c ≠ '/' := by
  intro c hc
  have hdigit : ∀ x ∈ (AzNat.toString z.abs).toList, x ≠ '/' := by
    intro x hx heq
    have := AzNat.toString_char_digit z.abs x hx
    rw [heq] at this
    revert this; decide
  unfold AzInt.toString at hc
  by_cases hs : z.sign
  · rw [ite_eq_left hs] at hc
    exact hdigit c hc
  · rw [ite_eq_right hs, String.toList_append] at hc
    rcases List.mem_append.mp hc with hdash | hrest
    · have : c = '-' := List.mem_singleton.mp hdash
      subst this; decide
    · exact hdigit c hrest

/-- Round-trip: parsing the string rendered by `AzRat.toString` recovers the
original `AzRat`. -/
theorem parse_toString (q : AzRat) : parse (toString q) = some q := by
  unfold parse toString toChars
  rw [String.toList_ofList]
  by_cases hden : q.den = 1
  · -- Integer form: no slash anywhere, so `splitAtSlash` returns everything.
    rw [ite_eq_left hden,
        splitAtSlash_no_slash _ (AzInt.toString_ne_slash q.numInt)]
    simp only [String.ofList_toList, AzInt.parse_toString, Option.map_some]
    -- `toAzRat` of the signed numerator is exactly `q`, since `q.den = 1`.
    exact congrArg some (AzRat.ext rfl rfl hden.symm)
  · -- Fraction form: split at the rendered slash, round-trip both components.
    rw [ite_eq_right hden,
        splitAtSlash_append _ _ (AzInt.toString_ne_slash q.numInt)]
    simp only [String.ofList_toList, AzInt.parse_toString, AzNat.parse_toString]
    exact congrArg some (ofSignAzNats_self q)

end Azurite.AzRat
