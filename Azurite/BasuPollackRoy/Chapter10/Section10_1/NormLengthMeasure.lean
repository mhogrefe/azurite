/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Notation_2_18
import Azurite.BasuPollackRoy.Chapter3.Section3_1.EuclideanBall
import Mathlib.Algebra.Polynomial.Roots

/-!
# BPR §10.1: norm, length, and measure of a complex polynomial

For `P = aₚXᵖ + ⋯ + a₀ ∈ C[X]` with `aₚ ≠ 0` and `C = R[i]` over a real
closed `R`:

* the **norm** `∥P∥ = √(|aₚ|² + ⋯ + |a₀|²)` (`polyNorm`, with its square
  `polyNormSq = ∑ᵢ |aᵢ|²` — the quantity that is rational in the real and
  imaginary parts of the coefficients);
* the **length** `Len(P) = |aₚ| + ⋯ + |a₀|` (`polyLength`);
* the **measure** `Mea(P) = |aₚ| · ∏ᵢ max(1, |zᵢ|)` (`polyMeasure`), where
  `z₁, …, zₚ` are the roots of `P` in `C` counted with multiplicity, so that
  `P = aₚ ∏ᵢ (X − zᵢ)` (BPR display (10.1); the multiset `P.roots` is full
  because `C` is algebraically closed).

All three take values in `R`. The modulus `|z| ∈ R` of `z ∈ C` is defined
here as `Ri.abs z = √(normSqR z)` in the ambient order of the section context
(`Ri.modulus` of Notation 2.18 carries an internally-derived order instead,
which does not mix well with an explicit `[LinearOrder R]`); `Ri.abs_sq`
recovers `|z|² = normSqR z`.

Computable counterparts for `AzPolynomial` (the square of the norm, the
length, and the measure relative to a given root list) are in
`Azurite.AzPolynomial.NormLengthMeasure`.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The modulus `|z| ∈ R` of `z ∈ C = R[i]`, as `√(normSqR z)` in the
ambient order. -/
noncomputable def Ri.abs (z : Ri R) : R := sqrt (Ri.normSqR z)

/-- Uniqueness of the nonnegative square root. -/
theorem sqrt_eq_of_sq {a y : R} (hy : 0 ≤ y) (h : y ^ 2 = a) : sqrt a = y := by
  have ha : 0 ≤ a := h ▸ sq_nonneg y
  have h1 := sq_sqrt ha
  have h2 := sqrt_nonneg a
  have hle : sqrt a ≤ y := by nlinarith
  have hge : y ≤ sqrt a := by nlinarith
  linarith

/-- `√a ≤ y` whenever `y` is nonnegative with `a ≤ y²`. -/
theorem sqrt_le_of_le_sq {a y : R} (hy : 0 ≤ y) (h : a ≤ y ^ 2) : sqrt a ≤ y := by
  by_cases ha : 0 ≤ a
  · have h1 := sq_sqrt ha
    have h2 := sqrt_nonneg a
    nlinarith
  · rw [sqrt, dite_eq_right ha]
    exact hy

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The representation `z = a + b·i` computes `normSqR z = a² + b²`. -/
theorem Ri.normSqR_of_repr {z : Ri R} {a b : R}
    (hab : z = algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R) :
    Ri.normSqR z = a ^ 2 + b ^ 2 := by
  have h2 : algebraMap R (Ri R) (Ri.normSqR z) = algebraMap R (Ri R) (a ^ 2 + b ^ 2) := by
    rw [Ri.normSqR_spec z, hab, Ri.normSq_repr]
  exact FaithfulSMul.algebraMap_injective R (Ri R) h2

/-- `normSqR` is nonnegative in the ambient order: it is a sum of two
squares of the representation of `z`. -/
theorem Ri.normSqR_nonneg' (z : Ri R) : 0 ≤ Ri.normSqR z := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists z
  rw [Ri.normSqR_of_repr hab]
  positivity

theorem Ri.abs_nonneg' (z : Ri R) : 0 ≤ Ri.abs z := sqrt_nonneg _

/-- `|z|² = normSqR z`: the square of the modulus is rational in the real
and imaginary parts. -/
theorem Ri.abs_sq (z : Ri R) : Ri.abs z ^ 2 = Ri.normSqR z :=
  sq_sqrt (Ri.normSqR_nonneg' z)

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem Ri.normSqR_zero : Ri.normSqR (0 : Ri R) = 0 := by
  have h := Ri.normSqR_of_repr (z := (0 : Ri R)) (a := 0) (b := 0) (by simp)
  rw [h]; ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem Ri.normSqR_one : Ri.normSqR (1 : Ri R) = 1 := by
  have h := Ri.normSqR_of_repr (z := (1 : Ri R)) (a := 1) (b := 0) (by simp)
  rw [h]; ring

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `normSqR` is multiplicative (via `normSq z = z·z̄` and injectivity of the
coefficient embedding). -/
theorem Ri.normSqR_mul (z w : Ri R) :
    Ri.normSqR (z * w) = Ri.normSqR z * Ri.normSqR w := by
  have h2 : algebraMap R (Ri R) (Ri.normSqR (z * w))
      = algebraMap R (Ri R) (Ri.normSqR z * Ri.normSqR w) := by
    rw [Ri.normSqR_spec, map_mul, Ri.normSqR_spec, Ri.normSqR_spec]
    show z * w * (Ri.conj R) (z * w) = z * (Ri.conj R) z * (w * (Ri.conj R) w)
    rw [map_mul]
    ring
  exact FaithfulSMul.algebraMap_injective R (Ri R) h2

theorem Ri.abs_zero : Ri.abs (0 : Ri R) = 0 :=
  sqrt_eq_of_sq le_rfl (by rw [Ri.normSqR_zero]; ring)

theorem Ri.abs_one : Ri.abs (1 : Ri R) = 1 :=
  sqrt_eq_of_sq zero_le_one (by rw [Ri.normSqR_one]; ring)

/-- The modulus is multiplicative. -/
theorem Ri.abs_mul (z w : Ri R) : Ri.abs (z * w) = Ri.abs z * Ri.abs w :=
  sqrt_eq_of_sq (mul_nonneg (Ri.abs_nonneg' z) (Ri.abs_nonneg' w)) (by
    rw [mul_pow, Ri.abs_sq, Ri.abs_sq, Ri.normSqR_mul])

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem Ri.normSqR_conj (z : Ri R) : Ri.normSqR (Ri.conj R z) = Ri.normSqR z := by
  apply FaithfulSMul.algebraMap_injective R (Ri R)
  rw [Ri.normSqR_spec, Ri.normSqR_spec]
  show Ri.conj R z * (Ri.conj R) (Ri.conj R z) = z * Ri.conj R z
  rw [Ri.conj_conj]
  ring

/-- Conjugation preserves the modulus. -/
theorem Ri.abs_conj (z : Ri R) : Ri.abs (Ri.conj R z) = Ri.abs z := by
  rw [Ri.abs, Ri.normSqR_conj]
  rfl

/-- The modulus of an inverse is the inverse of the modulus. -/
theorem Ri.abs_inv (z : Ri R) : Ri.abs z⁻¹ = (Ri.abs z)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [inv_zero, Ri.abs_zero, inv_zero]
  · have h1 : Ri.abs z * Ri.abs z⁻¹ = 1 := by
      rw [← Ri.abs_mul, mul_inv_cancel₀ hz, Ri.abs_one]
    have h2 : Ri.abs z ≠ 0 := by
      intro h
      rw [h, zero_mul] at h1
      exact zero_ne_one h1
    field_simp at h1 ⊢
    linarith [h1]

theorem Ri.abs_neg (z : Ri R) : Ri.abs (-z) = Ri.abs z := by
  have h : (-z) = (-1) * z := by ring
  have hm1 : Ri.abs (-1 : Ri R) = 1 := by
    apply sqrt_eq_of_sq zero_le_one
    have h1 := Ri.normSqR_of_repr (z := (-1 : Ri R)) (a := -1) (b := 0) (by simp)
    rw [h1]; ring
  rw [h, Ri.abs_mul, hm1, one_mul]

/-- **Triangle inequality** for the modulus over a real closed field: reduce
to the representations and the two-dimensional Cauchy–Schwarz inequality
`(ac + bd)² ≤ (a² + b²)(c² + d²)`. -/
theorem Ri.abs_add (z w : Ri R) : Ri.abs (z + w) ≤ Ri.abs z + Ri.abs w := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists z
  obtain ⟨c, d, hcd⟩ := Ri.repr_exists w
  have hzw : Ri.normSqR (z + w) = (a + c) ^ 2 + (b + d) ^ 2 := by
    apply Ri.normSqR_of_repr
    rw [hab, hcd, map_add, map_add]
    ring
  set s := Ri.abs z with hs
  set t := Ri.abs w with ht
  have hs0 : 0 ≤ s := Ri.abs_nonneg' z
  have ht0 : 0 ≤ t := Ri.abs_nonneg' w
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by rw [hs, Ri.abs_sq, Ri.normSqR_of_repr hab]
  have ht2 : t ^ 2 = c ^ 2 + d ^ 2 := by rw [ht, Ri.abs_sq, Ri.normSqR_of_repr hcd]
  -- two-dimensional Cauchy–Schwarz: ac + bd ≤ st
  have hcs : a * c + b * d ≤ s * t := by
    rcases le_or_gt (a * c + b * d) 0 with h | h
    · exact le_trans h (mul_nonneg hs0 ht0)
    · have hsq : (a * c + b * d) ^ 2 ≤ (s * t) ^ 2 := by
        have h1 : (s * t) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
          rw [mul_pow, hs2, ht2]
        nlinarith [sq_nonneg (a * d - b * c)]
      nlinarith [mul_nonneg hs0 ht0]
  rw [show Ri.abs (z + w) = sqrt (Ri.normSqR (z + w)) from rfl, hzw]
  apply sqrt_le_of_le_sq (by linarith)
  nlinarith [hcs]

/-- **The square of the norm**: `∥P∥² = ∑ᵢ |aᵢ|²`. -/
noncomputable def polyNormSq (P : Polynomial (Ri R)) : R :=
  ∑ i ∈ Finset.range (P.natDegree + 1), Ri.normSqR (P.coeff i)

/-- **The norm** `∥P∥ = √(∑ᵢ |aᵢ|²)`. -/
noncomputable def polyNorm (P : Polynomial (Ri R)) : R := sqrt (polyNormSq P)

/-- **The length** `Len(P) = ∑ᵢ |aᵢ|`. -/
noncomputable def polyLength (P : Polynomial (Ri R)) : R :=
  ∑ i ∈ Finset.range (P.natDegree + 1), Ri.abs (P.coeff i)

/-- **The measure** `Mea(P) = |aₚ| · ∏ᵢ max(1, |zᵢ|)`, over the roots of `P`
in `C` counted with multiplicity (display (10.1)). -/
noncomputable def polyMeasure (P : Polynomial (Ri R)) : R :=
  Ri.abs P.leadingCoeff * (P.roots.map (fun z => max 1 (Ri.abs z))).prod

theorem polyNormSq_nonneg (P : Polynomial (Ri R)) : 0 ≤ polyNormSq P :=
  Finset.sum_nonneg (fun _ _ => Ri.normSqR_nonneg' _)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `polyNormSq` as a sum over any range past the degree (the extra
coefficients vanish). -/
theorem polyNormSq_eq_sum (Q : Polynomial (Ri R)) {n : ℕ} (h : Q.natDegree < n) :
    polyNormSq Q = ∑ j ∈ Finset.range n, Ri.normSqR (Q.coeff j) := by
  have hsplit := Finset.sum_Ico_consecutive (fun j => Ri.normSqR (Q.coeff j))
    (Nat.zero_le (Q.natDegree + 1)) (by omega : Q.natDegree + 1 ≤ n)
  rw [polyNormSq]
  conv_rhs => rw [Finset.range_eq_Ico, ← hsplit]
  rw [Finset.range_eq_Ico, Finset.sum_eq_zero (s := Finset.Ico (Q.natDegree + 1) n), add_zero]
  intro i hi
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
    have := Finset.mem_Ico.mp hi
    omega), Ri.normSqR_zero]

/-- The norm squares to `polyNormSq`. -/
theorem polyNorm_sq (P : Polynomial (Ri R)) : polyNorm P ^ 2 = polyNormSq P :=
  sq_sqrt (polyNormSq_nonneg P)

theorem polyNorm_nonneg (P : Polynomial (Ri R)) : 0 ≤ polyNorm P := sqrt_nonneg _

theorem polyLength_nonneg (P : Polynomial (Ri R)) : 0 ≤ polyLength P :=
  Finset.sum_nonneg (fun _ _ => Ri.abs_nonneg' _)

theorem polyMeasure_nonneg (P : Polynomial (Ri R)) : 0 ≤ polyMeasure P := by
  apply mul_nonneg (Ri.abs_nonneg' _)
  apply Multiset.prod_nonneg
  intro a ha
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp ha
  exact le_trans zero_le_one (le_max_left _ _)

/-- Monotonicity of the square root. -/
theorem sqrt_le_sqrt {a b : R} (hab : a ≤ b) (hb : 0 ≤ b) : sqrt a ≤ sqrt b :=
  sqrt_le_of_le_sq (sqrt_nonneg b) (by rw [sq_sqrt hb]; exact hab)

/-- The modulus of a real element of `C` is its absolute value. -/
theorem Ri.abs_algebraMap (a : R) : Ri.abs (algebraMap R (Ri R) a) = |a| := by
  apply sqrt_eq_of_sq (abs_nonneg a)
  rw [sq_abs, Ri.normSqR_of_repr (a := a) (b := 0) (by simp)]
  ring

/-- The modulus of an integer in `C` is (the cast of) its absolute value. -/
theorem Ri.abs_intCast (m : ℤ) : Ri.abs ((m : Ri R)) = ((|m| : ℤ) : R) := by
  rw [show ((m : Ri R)) = algebraMap R (Ri R) ((m : R)) from (map_intCast _ m).symm,
    Ri.abs_algebraMap, ← Int.cast_abs]

/-- Every coefficient modulus is bounded by the norm. -/
theorem abs_coeff_le_polyNorm (P : Polynomial (Ri R)) (i : ℕ) :
    Ri.abs (P.coeff i) ≤ polyNorm P := by
  rcases le_or_gt i P.natDegree with hi | hi
  · rw [Ri.abs, polyNorm]
    apply sqrt_le_sqrt _ (polyNormSq_nonneg P)
    rw [polyNormSq]
    exact Finset.single_le_sum (f := fun j => Ri.normSqR (P.coeff j))
      (fun _ _ => Ri.normSqR_nonneg' _) (Finset.mem_range_succ_iff.mpr hi)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, Ri.abs_zero]
    exact polyNorm_nonneg P

/-- The leading coefficient modulus is bounded by the norm. -/
theorem abs_leadingCoeff_le_polyNorm (P : Polynomial (Ri R)) :
    Ri.abs P.leadingCoeff ≤ polyNorm P :=
  abs_coeff_le_polyNorm P P.natDegree

/-- Every coefficient modulus is bounded by the length. -/
theorem abs_coeff_le_polyLength (P : Polynomial (Ri R)) (i : ℕ) :
    Ri.abs (P.coeff i) ≤ polyLength P := by
  rcases le_or_gt i P.natDegree with hi | hi
  · rw [polyLength]
    exact Finset.single_le_sum (f := fun j => Ri.abs (P.coeff j))
      (fun _ _ => Ri.abs_nonneg' _) (Finset.mem_range_succ_iff.mpr hi)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, Ri.abs_zero]
    exact polyLength_nonneg P

/-- `√a < B` whenever `B` is positive with `a < B²`. -/
theorem sqrt_lt_of_lt_sq {a B : R} (hB : 0 < B) (h : a < B ^ 2) : sqrt a < B := by
  by_cases ha : 0 ≤ a
  · have h1 := sq_sqrt ha
    have h2 := sqrt_nonneg a
    nlinarith
  · rw [sqrt, dite_eq_right ha]
    exact hB

end Azurite.BPR
