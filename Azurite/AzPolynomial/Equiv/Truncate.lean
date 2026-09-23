import Azurite.AzPolynomial.Truncate
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Truncate

/-!
# Equivalence: `AzPolynomial.truncate` ↔ BPR's `truncate`

Shows that Azurite's computable `truncate` on `AzPolynomial R` agrees
with BPR's Notation 1.16 `Tru_i(·)` — as formalized in
`Azurite/BasuPollackRoy/Chapter1/Section1_3.lean` — under the
`toPoly` bridge to Mathlib's `Polynomial R`.
-/

namespace Azurite.AzPolynomial

open Polynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Coefficient description of `truncate i p`: keep `p.coeff j` for
`j ≤ i`, and zero out higher indices. -/
lemma coeff_truncate (i : ℕ) (p : AzPolynomial R) (j : ℕ) :
    (truncate i p).coeff j = if j ≤ i then p.coeff j else 0 := by
  unfold truncate
  rw [coeff_normalize]
  simp only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add]
  by_cases h : j < min (i + 1) p.coeffs.size
  · -- In range: the extracted entry is the original `p.coeffs[j]?`.
    have hji : j ≤ i := by
      have h1 : j < i + 1 := Nat.lt_of_lt_of_le h (Nat.min_le_left _ _)
      omega
    rw [ite_eq_left h, ite_eq_left hji]
    rfl
  · -- Out of range for the extract: the `getElem?` returns `none`.
    rw [ite_eq_right h]
    show (none : Option R).getD 0 = if j ≤ i then p.coeff j else 0
    by_cases hji : j ≤ i
    · rw [ite_eq_left hji]
      -- `j ≤ i` but `¬(j < min (i+1) p.coeffs.size)`, so `j ≥ p.coeffs.size`,
      -- which forces `p.coeff j = 0`.
      have hsize : p.coeffs.size ≤ j := by
        push Not at h
        have : min (i + 1) p.coeffs.size ≤ j := h
        omega
      show (0 : R) = p.coeff j
      dsimp [coeff]
      rw [Array.getElem?_eq_none hsize]
      rfl
    · rw [ite_eq_right hji]
      rfl

/-- `truncate` on `AzPolynomial R` agrees with BPR's `Tru_i(·)` on
`Polynomial R` under the `toPoly` bridge. -/
@[simp] theorem toPoly_truncate (i : ℕ) (p : AzPolynomial R) :
    AzPolynomial.toPoly (truncate i p) =
      Azurite.BPR.truncate i (AzPolynomial.toPoly p) := by
  ext j
  rw [coeff_toPoly_eq, coeff_truncate, Azurite.BPR.coeff_truncate,
    coeff_toPoly_eq]

/-- Reverse direction: applying `ofPoly` to BPR's truncation of the
lifted polynomial recovers Azurite's truncation. -/
@[simp] theorem ofPoly_truncate (i : ℕ) (p : Polynomial R) :
    AzPolynomial.ofPoly (Azurite.BPR.truncate i p) =
      truncate i (AzPolynomial.ofPoly p) := by
  rw [← toPoly_inj, toPoly_ofPoly, toPoly_truncate, toPoly_ofPoly]

end Azurite.AzPolynomial
