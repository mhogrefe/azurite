/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Content
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Add
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzInt.Equiv.RingEquiv
import Mathlib.RingTheory.Polynomial.Content

/-!
# Correctness of `AzPolynomial.content`

`content_toPoly`: the computable content agrees with Mathlib's
`Polynomial.content` of the represented integer polynomial,

  `((toPoly p).map toIntRingHom).content = (p.content.toNat : ℤ)`.

The proof characterizes both sides as the gcd of the coefficient list: the
`AzNat.gcd` fold descends to a `Nat.gcd` fold over the coefficient magnitudes
(`toNat_content`, via `toNat_gcd`); the fold divides every coefficient and
anything dividing every coefficient divides the fold (`foldl_gcd_dvd_mem` /
`dvd_foldl_gcd`), and Mathlib's content satisfies the same universal property
(`content_dvd_coeff`, `Finset.dvd_gcd`), so the two agree by antisymmetry;
nonnegativity of the `ℤ`-content (it is normalized) removes the `natAbs`.
-/

namespace Azurite.AzPolynomial

open Polynomial

/-- The magnitude of an `AzInt` represents `natAbs` of the represented
integer. -/
theorem _root_.Azurite.AzInt.toNat_abs (z : AzInt) : z.toInt.natAbs = z.abs.toNat := by
  rw [AzInt.toInt]
  split <;> simp

/-- A `Nat.gcd` fold divides its initial value. -/
theorem foldl_gcd_dvd_init (l : List ℕ) (init : ℕ) : l.foldl Nat.gcd init ∣ init := by
  induction l generalizing init with
  | nil => exact dvd_refl _
  | cons a l ih => exact dvd_trans (ih (Nat.gcd init a)) (Nat.gcd_dvd_left _ _)

/-- A `Nat.gcd` fold divides every list element. -/
theorem foldl_gcd_dvd_mem (l : List ℕ) (init : ℕ) {a : ℕ} (ha : a ∈ l) :
    l.foldl Nat.gcd init ∣ a := by
  induction l generalizing init with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact dvd_trans (foldl_gcd_dvd_init l (Nat.gcd init a)) (Nat.gcd_dvd_right _ _)
    · exact ih _ ha'

/-- Anything dividing the initial value and every element divides the fold. -/
theorem dvd_foldl_gcd (l : List ℕ) (init : ℕ) {c : ℕ} (hi : c ∣ init)
    (h : ∀ a ∈ l, c ∣ a) : c ∣ l.foldl Nat.gcd init := by
  induction l generalizing init with
  | nil => exact hi
  | cons a l ih =>
    exact ih _ (Nat.dvd_gcd hi (h a List.mem_cons_self))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The computable content descends to a `Nat.gcd` fold over the coefficient
magnitudes. -/
theorem toNat_content (p : AzPolynomial AzInt) :
    p.content.toNat = (p.coeffs.toList.map (fun z => z.abs.toNat)).foldl Nat.gcd 0 := by
  rw [content, ← Array.foldl_toList]
  have aux : ∀ (l : List AzInt) (acc : AzNat),
      (l.foldl (fun acc a => AzNat.gcd acc a.abs) acc).toNat
        = (l.map (fun z => z.abs.toNat)).foldl Nat.gcd acc.toNat := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons a l ih =>
      intro acc
      rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, Azurite.AzNat.toNat_gcd]
  rw [aux]
  rfl

/-- **Correctness of the content.** The computable content is Mathlib's
`Polynomial.content` of the represented polynomial in `ℤ[X]`. -/
theorem content_toPoly (p : AzPolynomial AzInt) :
    ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).content = (p.content.toNat : ℤ) := by
  classical
  set Q : Polynomial ℤ := (AzPolynomial.toPoly p).map AzInt.toIntRingHom with hQ
  have hQcoeff : ∀ n, Q.coeff n = (p.coeff n).toInt := by
    intro n
    rw [hQ, Polynomial.coeff_map, coeff_toPoly]
    rfl
  set g : ℕ := (p.coeffs.toList.map (fun z => z.abs.toNat)).foldl Nat.gcd 0 with hg
  -- `Q.content` and `g` divide each other in `ℕ`
  have h1 : Q.content.natAbs ∣ g := by
    apply dvd_foldl_gcd _ _ (dvd_zero _)
    intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hcoeff : p.coeff i = p.coeffs.toList[i] := by
      rw [AzPolynomial.coeff]
      rw [Array.getElem?_eq_getElem (by simpa using hi)]
      simp
    rw [← Azurite.AzInt.toNat_abs, ← hcoeff, ← hQcoeff]
    exact Int.natAbs_dvd_natAbs.mpr (Q.content_dvd_coeff i)
  have h2 : g ∣ Q.content.natAbs := by
    rw [← Int.natAbs_natCast g]
    apply Int.natAbs_dvd_natAbs.mpr
    rw [Polynomial.content]
    apply Finset.dvd_gcd
    intro i hi
    rcases lt_or_ge i p.coeffs.size with hlt | hge
    · have hcoeff : p.coeff i = p.coeffs.toList[i] := by
        rw [AzPolynomial.coeff]
        rw [Array.getElem?_eq_getElem hlt]
        simp
      have hmem : p.coeffs.toList[i].abs.toNat
          ∈ p.coeffs.toList.map (fun z => z.abs.toNat) :=
        List.mem_map.mpr ⟨_, List.getElem_mem (by simpa using hlt), rfl⟩
      have hdvd : g ∣ (Q.coeff i).natAbs := by
        rw [hQcoeff, hcoeff, Azurite.AzInt.toNat_abs]
        exact foldl_gcd_dvd_mem _ _ hmem
      exact dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) (Int.natAbs_dvd.mpr dvd_rfl)
    · exfalso
      have hzero : p.coeff i = 0 := by
        rw [AzPolynomial.coeff, Array.getElem?_eq_none (by omega)]
        rfl
      have : Q.coeff i = 0 := by rw [hQcoeff, hzero]; rfl
      exact (Polynomial.mem_support_iff.mp hi) this
  have hnat : Q.content.natAbs = g := Nat.dvd_antisymm h1 h2
  -- the `ℤ`-content is normalized, hence nonnegative
  have hnn : Q.content = (Q.content.natAbs : ℤ) := by
    have hnorm := Q.normalize_content
    rw [← Int.abs_eq_normalize] at hnorm
    have h0 : 0 ≤ Q.content := hnorm ▸ abs_nonneg _
    omega
  rw [hnn, hnat, toNat_content]

end Azurite.AzPolynomial
