import Azurite.AzPolynomial.Karatsuba
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.AzPolynomial.Equiv.Mul

/-!
# Correctness Proof for Karatsuba Multiplication

Establishes `toPoly_mulKaratsuba`:
  `AzPolynomial.toPoly (mulKaratsuba p q) = AzPolynomial.toPoly p * AzPolynomial.toPoly q`

Proof strategy: show each raw coefficient-array operation maps to its
polynomial counterpart, then use the Karatsuba algebraic identity
`(p0 + X^m p1)(q0 + X^m q1) = z0 + X^m z1 + X^{2m} z2` via `ring`.

We use `CommRing R` rather than `Ring R` because the Karatsuba identity
proof relies on commutativity of `Polynomial R`.
-/

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-! ## Raw operation lemmas -/

omit [DecidableEq R] in
/-- `rawAdd` on arrays corresponds to polynomial addition. -/
lemma toPoly_rawAdd (a b : Array R) :
    (rawAdd a b).toList.toPoly = a.toList.toPoly + b.toList.toPoly := by
  ext n; rw [Polynomial.coeff_add]
  simp only [coeff_list_toPoly, rawAdd, Array.toList_ofFn]
  rw [List.getCoeff_ofFn_aux]
  simp only [List.getCoeff, Array.getElem?_toList]
  split
  · rfl
  · simp [Array.getElem?_eq_none (show a.size ≤ n by omega),
          Array.getElem?_eq_none (show b.size ≤ n by omega)]

omit [DecidableEq R] in
/-- `rawSub` on arrays corresponds to polynomial subtraction. -/
lemma toPoly_rawSub (a b : Array R) :
    (rawSub a b).toList.toPoly = a.toList.toPoly - b.toList.toPoly := by
  ext n; rw [Polynomial.coeff_sub]
  simp only [coeff_list_toPoly, rawSub, Array.toList_ofFn]
  rw [List.getCoeff_ofFn_aux]
  simp only [List.getCoeff, Array.getElem?_toList]
  split
  · rfl
  · simp [Array.getElem?_eq_none (show a.size ≤ n by omega),
          Array.getElem?_eq_none (show b.size ≤ n by omega)]

/-! ## Shift lemma via list prepend -/

omit [DecidableEq R] in
/-- Prepending `m` zeros to a list multiplies the polynomial by `X^m`. -/
lemma list_replicate_toPoly (l : List R) (m : Nat) :
    (List.replicate m (0 : R) ++ l).toPoly = Polynomial.X ^ m * l.toPoly := by
  induction m with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, List.toPoly, ih,
               map_zero, zero_add, pow_succ]
    ring

omit [DecidableEq R] in
/-- `rawShift` (prepending `m` zeros) corresponds to multiplication by `X^m`. -/
lemma toPoly_rawShift (a : Array R) (m : Nat) :
    (rawShift a m).toList.toPoly = Polynomial.X ^ m * a.toList.toPoly := by
  simp only [rawShift, Array.toList_append, Array.toList_replicate]
  exact list_replicate_toPoly a.toList m

/-! ## Split lemma -/

omit [DecidableEq R] in
/-- Appending two lists corresponds to a polynomial sum with a power-of-X shift. -/
lemma list_append_toPoly (l1 l2 : List R) :
    (l1 ++ l2).toPoly = l1.toPoly + Polynomial.X ^ l1.length * l2.toPoly := by
  induction l1 with
  | nil => simp [List.toPoly]
  | cons a t ih =>
    simp only [List.cons_append, List.toPoly, List.length_cons, ih, pow_succ]
    ring

omit [DecidableEq R] in
/-- Splitting an array at index `m` corresponds to the polynomial decomposition
    `p = p_low + X^m · p_high`. -/
lemma toPoly_take_drop (a : Array R) (m : Nat) :
    a.toList.toPoly = (a.take m).toList.toPoly +
      Polynomial.X ^ m * (a.drop m).toList.toPoly := by
  have h1 : (a.take m).toList = a.toList.take m := by
    simp [Array.take, Array.toList_extract]
  have h2 : (a.drop m).toList = a.toList.drop m := by
    simp [Array.drop, Array.toList_extract]
  rw [h1, h2]
  conv_lhs => rw [show a.toList = a.toList.take m ++ a.toList.drop m from
    (List.take_append_drop m a.toList).symm]
  rw [list_append_toPoly]
  by_cases h : m ≤ a.toList.length
  · congr 2
    rw [List.length_take, Nat.min_eq_left h]
  · push Not at h
    have : a.toList.drop m = [] := List.drop_eq_nil_of_le (by omega)
    simp [this, List.toPoly]

/-! ## Basecase correctness -/

omit [DecidableEq R] in
/-- `mulBasecaseCoeffs` produces the correct product polynomial. -/
lemma toPoly_mulBasecaseCoeffs (a b : Array R) :
    (mulBasecaseCoeffs a b).toList.toPoly = a.toList.toPoly * b.toList.toPoly := by
  ext n; rw [Polynomial.coeff_mul, coeff_list_toPoly]
  simp only [mulBasecaseCoeffs]; split
  · next h =>
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ha | hb
    · simp [Array.eq_empty_of_size_eq_zero ha, List.toPoly]
    · simp [Array.eq_empty_of_size_eq_zero hb, List.toPoly]
  · simp only [Array.toList_ofFn]; rw [List.getCoeff_ofFn_aux]; split
    · next h_lt =>
      have hfold := fin_foldl_eq_finset_range_sum (n + 1)
        (fun j => (a[j]?).getD (0 : R) * (b[n - j]?).getD (0 : R))
      rw [hfold]
      have hanti := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => a.toList.toPoly.coeff i * b.toList.toPoly.coeff j) n
      rw [hanti]
      congr 1; ext i
      simp [coeff_list_toPoly, List.getCoeff, Array.getElem?_toList]
    · next h_ge =>
      have hanti := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => a.toList.toPoly.coeff i * b.toList.toPoly.coeff j) n
      rw [hanti]; symm
      apply Finset.sum_eq_zero
      intro i hi; rw [Finset.mem_range] at hi
      simp only [coeff_list_toPoly, List.getCoeff, Array.getElem?_toList]
      by_cases h1 : i < a.size
      · simp [Array.getElem?_eq_none (show b.size ≤ n - i by omega)]
      · push Not at h1; simp [Array.getElem?_eq_none h1]

/-! ## Main inductive proof -/

omit [DecidableEq R] in
/-- `rawKaratsuba.go` produces the correct product polynomial. -/
lemma toPoly_rawKaratsuba_go (fuel : Nat) (a b : Array R)
    (hfuel : max a.size b.size ≤ fuel) :
    (rawKaratsuba.go fuel a b hfuel).toList.toPoly =
      a.toList.toPoly * b.toList.toPoly := by
  induction fuel using Nat.strongRecOn generalizing a b with
  | _ fuel ih =>
    unfold rawKaratsuba.go
    split
    · next h =>
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ha | hb
      · simp [Array.eq_empty_of_size_eq_zero ha, List.toPoly]
      · simp [Array.eq_empty_of_size_eq_zero hb, List.toPoly]
    · split
      · exact toPoly_mulBasecaseCoeffs a b
      · next h_ne hlt =>
        have hfuel_pos : 0 < fuel := by unfold karatsubaThreshold at hlt; omega
        have hm_lt : fuel / 2 < fuel := Nat.div_lt_self hfuel_pos (by omega : 1 < 2)
        have hfm_lt : fuel - fuel / 2 < fuel := by
          apply Nat.sub_lt hfuel_pos
          exact Nat.div_pos (by unfold karatsubaThreshold at hlt; omega) (by omega : 0 < 2)
        simp only [toPoly_rawShift, toPoly_rawSub, toPoly_rawAdd]
        conv_lhs =>
          rw [ih (fuel / 2) hm_lt (a.take (fuel / 2)) (b.take (fuel / 2)) _]
          rw [ih (fuel - fuel / 2) hfm_lt (a.drop (fuel / 2)) (b.drop (fuel / 2)) _]
          rw [ih (fuel - fuel / 2) hfm_lt
            (rawAdd (a.take (fuel / 2)) (a.drop (fuel / 2)))
            (rawAdd (b.take (fuel / 2)) (b.drop (fuel / 2))) _]
        rw [toPoly_rawAdd, toPoly_rawAdd]
        rw [toPoly_take_drop a (fuel / 2), toPoly_take_drop b (fuel / 2)]
        ring

omit [DecidableEq R] in
/-- `rawKaratsuba` produces the correct product polynomial. -/
lemma toPoly_rawKaratsuba (a b : Array R) :
    (rawKaratsuba a b).toList.toPoly = a.toList.toPoly * b.toList.toPoly :=
  toPoly_rawKaratsuba_go _ a b (Nat.le_refl _)

/-! ## Final correctness theorem -/

@[simp] lemma toPoly_mulKaratsuba (p q : AzPolynomial R) :
    AzPolynomial.toPoly (mulKaratsuba p q) = AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  simp only [mulKaratsuba, toPoly_normalize]
  exact toPoly_rawKaratsuba p.coeffs q.coeffs

end Azurite.AzPolynomial
