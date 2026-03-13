import Azurite.DensePoly.Basic
import Mathlib.Algebra.Polynomial.Basic

open Polynomial

variable {R : Type _} [Semiring R]

/-- Evaluates a list of coefficients into a mathlib `Polynomial R` -/
noncomputable def List.toPoly : List R → Polynomial R
| [] => 0
| a :: as => C a + X * as.toPoly

/-- Converts a `DensePoly` into a mathlib `Polynomial R` -/
noncomputable def DensePoly.toPoly (p : Azurite.DensePoly R) : Polynomial R :=
  p.coeffs.toPoly

/-- Converts a mathlib `Polynomial R` into a list of coefficients from 0 to natDegree -/
noncomputable def Polynomial.toDenseList [DecidableEq R] (p : Polynomial R) : List R :=
  if p = 0 then [] else (List.range (p.natDegree + 1)).map p.coeff

lemma length_toDenseList [DecidableEq R] (p : Polynomial R) (hp : p ≠ 0) :
  p.toDenseList.length = p.natDegree + 1 := by
  dsimp [Polynomial.toDenseList]
  split
  · contradiction
  · simp

-- We need a proof that `Polynomial.toDenseList` does not end in zero when `p ≠ 0`.
@[simp] lemma last_toDenseList_ne_zero [DecidableEq R] (p : Polynomial R) (hp : p ≠ 0) :
    (p.toDenseList.getLast (by
      intro h
      have h1 : p.toDenseList.length = 0 := List.length_eq_zero_iff.mpr h
      have h2 : p.toDenseList.length = p.natDegree + 1 := length_toDenseList p hp
      omega
    )) = p.leadingCoeff := by
  dsimp [Polynomial.toDenseList]
  split
  · contradiction
  · -- we are in the `else` branch where we map `List.range (p.natDegree + 1)`
    -- length is `natDegree + 1`, so the last element is `natDegree`
    rw [List.getLast_map]
    have : (List.range (p.natDegree + 1)).getLast (by simp) = p.natDegree := by
      rw [List.getLast_range]
      omega
    rw [this]
    rfl

/-- Converts a mathlib `Polynomial R` to `DensePoly R` -/
noncomputable def DensePoly.ofPoly [DecidableEq R] (p : Polynomial R) : Azurite.DensePoly R :=
  if hp : p = 0 then 0 else
  ⟨p.toDenseList, by
    intro h
    have h_last := last_toDenseList_ne_zero p hp
    have h_coeff := Polynomial.leadingCoeff_ne_zero.mpr hp
    have h_opt : p.toDenseList.getLast? = some (p.toDenseList.getLast (by
      intro len_zero
      have h1 : p.toDenseList.length = 0 := List.length_eq_zero_iff.mpr len_zero
      have h2 : p.toDenseList.length = p.natDegree + 1 := length_toDenseList p hp
      omega
    )) := List.getLast?_eq_some_getLast _
    rw [h_last] at h_opt
    rw [h] at h_opt
    injection h_opt with h_eq
    exact h_coeff h_eq.symm
  ⟩


def List.getCoeff (l : List R) (i : ℕ) : R := (l[i]?).getD 0

@[simp] lemma getCoeff_nil (i : ℕ) : ([] : List R).getCoeff i = 0 := rfl
@[simp] lemma getCoeff_cons_zero (a : R) (as : List R) : (a :: as).getCoeff 0 = a := rfl
@[simp] lemma getCoeff_cons_succ (a : R) (as : List R) (i : ℕ) : (a :: as).getCoeff (i + 1) = as.getCoeff i := rfl

lemma coeff_toPoly (l : List R) (i : ℕ) :
  (List.toPoly l).coeff i = l.getCoeff i := by
  induction l generalizing i with
  | nil => simp [List.toPoly, List.getCoeff]
  | cons a as ih =>
    cases i
    · simp [List.toPoly, List.getCoeff]
    · simp [List.toPoly, ih, List.getCoeff]

lemma getCoeff_map_range_coeff [DecidableEq R] (p : Polynomial R) (i : ℕ) :
  ((List.range (p.natDegree + 1)).map p.coeff).getCoeff i = if i ≤ p.natDegree then p.coeff i else 0 := by
  dsimp [List.getCoeff]
  rw [List.getElem?_map]
  by_cases h : i < p.natDegree + 1
  · have h1 : (List.range (p.natDegree + 1))[i]? = some i := List.getElem?_range h
    rw [h1]
    simp
    have h2 : i ≤ p.natDegree := by omega
    simp [h2]
  · have hlen : (List.range (p.natDegree + 1)).length ≤ i := by simp; omega
    have h2 : (List.range (p.natDegree + 1))[i]? = none := List.getElem?_eq_none hlen
    rw [h2]
    simp
    have h3 : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h3]
    have h4 : ¬(i ≤ p.natDegree) := by omega
    simp [h4]

lemma toPoly_ofPoly [DecidableEq R] (p : Polynomial R) : DensePoly.toPoly (DensePoly.ofPoly p) = p := by
  dsimp [DensePoly.ofPoly]
  split
  · next hp => simp [hp, DensePoly.toPoly, List.toPoly]
  · next hp =>
      dsimp [Polynomial.toDenseList, DensePoly.toPoly]
      ext i
      simp [hp]
      rw [coeff_toPoly, getCoeff_map_range_coeff]
      split
      · rfl
      · apply Eq.symm
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega

lemma natDegree_toPoly (l : List R) (h_nonempty : l ≠ []) (h_last : l.getLast? ≠ some 0) :
  (List.toPoly l).natDegree = l.length - 1 := by
  have h_len_pos : 0 < l.length := List.length_pos_iff_ne_nil.mpr h_nonempty
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    have hm2 : l.length ≤ m := by omega
    have h1 : (List.toPoly l).coeff m = l.getCoeff m := coeff_toPoly l m
    rw [h1]
    dsimp [List.getCoeff]
    have h2 : l[m]? = none := List.getElem?_eq_none hm2
    rw [h2]
    rfl
  · apply le_natDegree_of_ne_zero
    have h1 : (List.toPoly l).coeff (l.length - 1) = l.getCoeff (l.length - 1) := coeff_toPoly l (l.length - 1)
    rw [h1]
    have h2 : l[l.length - 1]? = l.getLast? := by
      apply Eq.symm
      apply List.getLast?_eq_getElem?
    dsimp [List.getCoeff]
    rw [h2]
    have h3 : l.getLast?.isSome := List.getLast?_isSome.mpr h_nonempty
    have h4 : ∃ c, l.getLast? = some c := Option.isSome_iff_exists.mp h3
    rcases h4 with ⟨c, hc_some⟩
    rw [hc_some]
    simp
    intro hc
    rw [hc] at hc_some
    rw [hc_some] at h_last
    exact h_last rfl

lemma map_getCoeff_range (l : List R) :
  (List.range l.length).map l.getCoeff = l := by
  apply List.ext_get
  · simp
  · intro i h1 h2
    simp
    dsimp [List.getCoeff]
    have h3 : l[i]? = some l[i] := List.getElem?_eq_getElem h2
    rw [h3]
    rfl

lemma ofPoly_toPoly [DecidableEq R] (p : Azurite.DensePoly R) : DensePoly.ofPoly (DensePoly.toPoly p) = p := by
  apply Azurite.DensePoly.ext
  dsimp [DensePoly.ofPoly, DensePoly.toPoly]
  by_cases h : p.coeffs = []
  · have h_p_zero : p = 0 := by apply Azurite.DensePoly.ext; exact h
    rw [h_p_zero]
    rfl
  · have h_poly_ne_zero : List.toPoly p.coeffs ≠ 0 := by
      intro hc
      have h4 : (List.toPoly p.coeffs).coeff (p.coeffs.length - 1) = 0 := by rw [hc]; simp
      rw [coeff_toPoly] at h4
      -- Contradiction with p.last_ne_zero
      have h1 : p.coeffs[p.coeffs.length - 1]? = p.coeffs.getLast? := by
        apply Eq.symm
        apply List.getLast?_eq_getElem?
      dsimp [List.getCoeff] at h4
      rw [h1] at h4
      have h2 : p.coeffs.getLast?.isSome := List.getLast?_isSome.mpr h
      have h3 : ∃ c, p.coeffs.getLast? = some c := Option.isSome_iff_exists.mp h2
      rcases h3 with ⟨c, hc_some⟩
      rw [hc_some] at h4
      simp at h4
      have hlast : p.coeffs.getLast? ≠ some 0 := p.last_ne_zero
      rw [hc_some] at hlast
      rw [h4] at hlast
      exact hlast rfl
    simp [h_poly_ne_zero, Polynomial.toDenseList]
    have h1 : (List.toPoly p.coeffs).natDegree = p.coeffs.length - 1 := by
      apply natDegree_toPoly
      · exact h
      · exact p.last_ne_zero
    rw [h1]
    have h2 : p.coeffs.length - 1 + 1 = p.coeffs.length := by
      have hlen : p.coeffs.length > 0 := List.length_pos_iff_ne_nil.mpr h
      omega
    rw [h2]
    have h3 : Polynomial.coeff (List.toPoly p.coeffs) = p.coeffs.getCoeff := by
      funext i
      exact coeff_toPoly p.coeffs i
    rw [h3]
    exact map_getCoeff_range p.coeffs
