/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ParsableElement` instance for `AzPolynomial R`, using the `XyzVar 1`
  display (single-variable `x`).  Allows `AzPolynomial` values to be used as
  entries inside `AzVector` / `AzMatrix` string representations.

  Bridges the thin `AzPolynomial ↔ AzMvPolynomial 1` facade from
  `AzPolynomial.ParseToString`, and derives the no-comma / no-semicolon
  properties through `AzMvPolynomial.char_notin_toCharsWith` at `XyzVar 1`.
-/
import Azurite.AzPolynomial.ParseToString
import Azurite.AzMvPolynomial.ParsableElement

namespace Azurite

open _root_.Azurite.AzPolynomial

/-! ### Variable-layer lemmas for `XyzVar n` -/

namespace XyzVar

theorem toChars_no_comma {n : ℕ} (v : XyzVar n) :
    ',' ∉ XyzVar.toChars v := by
  intro hc
  simp only [toChars, List.mem_singleton] at hc
  have hge := v.is_valid.1
  simp only [show ('a' : Char).toNat = 97 from by decide] at hge
  rw [← hc] at hge; exact absurd hge (by decide)

theorem toChars_no_semicolon {n : ℕ} (v : XyzVar n) :
    ';' ∉ XyzVar.toChars v := by
  intro hc
  simp only [toChars, List.mem_singleton] at hc
  have hge := v.is_valid.1
  simp only [show ('a' : Char).toNat = 97 from by decide] at hge
  rw [← hc] at hge; exact absurd hge (by decide)

end XyzVar

/-! ### `ParsableElement (AzPolynomial R)` instance -/

section Instance

variable {R : Type _} [CommSemiring R] [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R]

/-- List-of-Char serialization for `AzPolynomial`. The user-facing `toChars`
    returns a `String`; this unwraps to a `List Char` for `ParsableElement`. -/
private def AzPolynomial.toCharList (p : AzPolynomial R) : List Char :=
  (AzPolynomial.toChars p).toList

/-- List-of-Char deserialization for `AzPolynomial`. -/
private def AzPolynomial.parseCharList (cs : List Char) : Option (AzPolynomial R) :=
  parseAzPolynomial (String.ofList cs)

theorem AzPolynomial.parseCharList_toCharList (p : AzPolynomial R) :
    AzPolynomial.parseCharList (AzPolynomial.toCharList p) = some p := by
  unfold AzPolynomial.parseCharList AzPolynomial.toCharList
  rw [String.ofList_toList]
  exact parseAzPolynomial_toChars p

theorem AzPolynomial.no_char_toCharList (p : AzPolynomial R) (c : Char)
    (hcoeff : ∀ r : R, c ∉ ParsableCoeff.toChars r)
    (hvar : ∀ v : XyzVar 1, c ∉ ParsableVar.toChars v)
    (hdig : ∀ k : ℕ, c ∉ natToChars k)
    (hnot_plus : c ≠ '+') (hnot_star : c ≠ '*')
    (hnot_caret : c ≠ '^') (hnot_minus : c ≠ '-') :
    c ∉ AzPolynomial.toCharList p := by
  unfold AzPolynomial.toCharList AzPolynomial.toChars
  unfold AzMvPolynomial.toStrWith
  rw [String.toList_ofList]
  exact AzMvPolynomial.char_notin_toCharsWith (XyzVar 1) c
    hcoeff hvar hdig hnot_plus hnot_star hnot_caret hnot_minus _

instance : ParsableElement (AzPolynomial R) where
  toChars := AzPolynomial.toCharList
  parseChars := AzPolynomial.parseCharList
  parse_toChars := AzPolynomial.parseCharList_toCharList
  toChars_no_comma p :=
    AzPolynomial.no_char_toCharList p ','
      ParsableCoeff.toChars_no_comma
      XyzVar.toChars_no_comma
      (not_mem_natToChars_of_not_digit ',' (by decide))
      (by decide) (by decide) (by decide) (by decide)
  toChars_no_semicolon p :=
    AzPolynomial.no_char_toCharList p ';'
      ParsableCoeff.toChars_no_semicolon
      XyzVar.toChars_no_semicolon
      (not_mem_natToChars_of_not_digit ';' (by decide))
      (by decide) (by decide) (by decide) (by decide)

end Instance

end Azurite
