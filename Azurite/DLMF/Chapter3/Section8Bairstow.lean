/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section8
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.ComputeDegree

/-!
# DLMF §3.8(iv): Bairstow's method

For `p(z) = aₙzⁿ + ⋯ + a₀` and an approximate quadratic factor `z² − sz − t`:

* 3.8.10 (`bairSeq`, `bairQ`, `bairR`): `q_{n+1} = r_{n+1} = 0`, `q_n = r_n = a_n`,
  `q_j = a_j + s q_{j+1} + t q_{j+2}`, `r_j = q_j + s r_{j+1} + t r_{j+2}` (`bairSeq_rec`).
* The quotient (`dlmf_3_8_10_quotient`, `dlmf_3_8_10_quotient_poly`):
  `p(z) = (z² − sz − t)(q_n z^{n−2} + ⋯ + q₂) + q₁(z − s) + q₀`; so the remainder on dividing
  by `z² − sz − t` is `q₁ z + (q₀ − s q₁)`, and `z² − sz − t` is a factor iff
  `F(s, t) = (q₁, q₀ − s q₁) = 0` (`bairF_eq_zero_iff`). "On the last iteration
  `q_n z^{n−2} + ⋯ + q₂` is the quotient": at an exact factor it is the quotient.
* 3.8.11 (`bairStep`, `bairEll`, `bairDet`): `Δs = (r₃q₀ − r₂q₁)/(r₂² − ℓr₃)`,
  `Δt = (ℓq₁ − r₂q₀)/(r₂² − ℓr₃)`, `ℓ = sr₂ + tr₃`.
* Bairstow's method is Newton's method for `F` (`bairStep_newton`): `∂q_j/∂s = r_{j+1}`,
  `∂q_j/∂t = r_{j+2}` (`hasFDerivAt_bairQ`), the Jacobian of `F` is
  `[[r₂, r₃], [tr₃, r₂ − sr₃]]` with determinant `r₂² − ℓr₃` (`hasFDerivAt_bairF`), and
  3.8.11 solves `J Δ = −F`.
* At an exact factor `z² − sz − t = (z − z₁)(z − z₂)`, `r₂² − ℓr₃ = Q(z₁) Q(z₂)` with `Q` the
  quotient (`bairDet_eq_quotient`, `bairDet_eq_quotient_complex`).
* "The method converges locally and quadratically" (`dlmf_3_8_iv_bairstow`): when
  `Q(z₁) Q(z₂) ≠ 0`, i.e. when the quadratic factor and the quotient share no zero. For
  `z₁ ≠ z₂` this says that neither `z₁` nor `z₂` is a multiple zero of `p`; for `z₁ = z₂` it says
  `(z − z₁)³ ∤ p`. DLMF's exception "when the wanted quadratic factor is a multiple factor of
  `q(z)`" (read with `p` for `q`) is the case `Q(z₁) = Q(z₂) = 0` of this condition. The proof is
  the general Newton estimate in a normed space (`newton_sq_bound`, `iter_of_sq_bound`).
* Example `p = z⁴ − 2z² + 1 = (z − 1)²(z + 1)²`, `s₀ = 7/4`, `t₀ = −1/2`
  (`dlmf_3_8_iv_bairstow_example`): `(s, t) = (2, −1)` is an exact factor with `Q(1)² = 16 ≠ 0`,
  so the method converges locally and quadratically there although the zeros `1, 1` of the
  quadratic factor coincide. Table 3.8.3 (`dlmf_table_3_8_3`), certified exactly in `ℚ`: all
  entries are correctly rounded, and the errors satisfy `‖e_{k+1}‖ ≤ ‖e_k‖²` for `k ≤ 4`. That
  the iteration from `(7/4, −1/2)` converges is not formalized (it needs explicit constants).
-/

open Polynomial Finset Filter Topology Set Metric

namespace Azurite.DLMF

/-! ### 3.8.10 -/

section Rec

variable {R : Type*} [CommRing R]

/-- The downward recursion `c_j = b_j + s c_{j+1} + t c_{j+2}` run `k` steps from `c_n = b_n`,
`c_{n+1} = 0`: the pair `(c_{n−k}, c_{n−k+1})`. -/
def bairAux (b : ℕ → R) (n : ℕ) (s t : R) : ℕ → R × R
  | 0 => (b n, 0)
  | k + 1 => (b (n - (k + 1)) + s * (bairAux b n s t k).1 + t * (bairAux b n s t k).2,
      (bairAux b n s t k).1)

/-- The sequence of 3.8.10: `c_j = 0` for `j > n`, `c_n = b_n`,
`c_j = b_j + s c_{j+1} + t c_{j+2}` for `j ≤ n − 1`. -/
def bairSeq (b : ℕ → R) (n : ℕ) (s t : R) (j : ℕ) : R :=
  if n < j then 0 else (bairAux b n s t (n - j)).1

theorem bairSeq_of_lt (b : ℕ → R) {n : ℕ} (s t : R) {j : ℕ} (h : n < j) :
    bairSeq b n s t j = 0 := by
  simp [bairSeq, h]

theorem bairSeq_self (b : ℕ → R) (n : ℕ) (s t : R) : bairSeq b n s t n = b n := by
  simp [bairSeq, bairAux]

/-- **DLMF 3.8.10**: the recursion, for every `j ≤ n`. -/
theorem bairSeq_rec (b : ℕ → R) {n : ℕ} (s t : R) {j : ℕ} (hj : j ≤ n) :
    bairSeq b n s t j = b j + s * bairSeq b n s t (j + 1) + t * bairSeq b n s t (j + 2) := by
  rcases hj.lt_or_eq with hj | rfl
  · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
    have h1 : bairSeq b n s t (j + 1) = (bairAux b n s t k).1 := by
      simp [bairSeq, show ¬ n < j + 1 by omega, show n - (j + 1) = k by omega]
    have h2 : bairSeq b n s t (j + 2) = (bairAux b n s t k).2 := by
      rcases k with _ | k
      · simp [bairSeq_of_lt b s t (show n < j + 2 by omega), bairAux]
      · simp [bairSeq, show ¬ n < j + 2 by omega, show n - (j + 2) = k by omega, bairAux]
    rw [show bairSeq b n s t j = (bairAux b n s t (k + 1)).1 by
      simp [bairSeq, show ¬ n < j by omega, hk], bairAux, show n - (k + 1) = j by omega, h1, h2]
  · rw [bairSeq_self, bairSeq_of_lt b s t (by omega), bairSeq_of_lt b s t (by omega)]
    ring

/-- The recursion for every `j`, when `b` vanishes above `n`. -/
theorem bairSeq_rec_all {b : ℕ → R} {n : ℕ} (hb : ∀ j, n < j → b j = 0) (s t : R) (j : ℕ) :
    bairSeq b n s t j = b j + s * bairSeq b n s t (j + 1) + t * bairSeq b n s t (j + 2) := by
  rcases le_or_gt j n with hj | hj
  · exact bairSeq_rec b s t hj
  · rw [bairSeq_of_lt b s t hj, bairSeq_of_lt b s t (by omega), bairSeq_of_lt b s t (by omega),
      hb j hj]
    ring

theorem bairSeq_map {S : Type*} [CommRing S] (φ : R →+* S) (b : ℕ → R) (n : ℕ) (s t : R)
    (j : ℕ) : φ (bairSeq b n s t j) = bairSeq (fun i => φ (b i)) n (φ s) (φ t) j := by
  have h : ∀ k, ((φ (bairAux b n s t k).1, φ (bairAux b n s t k).2) : S × S) =
      bairAux (fun i => φ (b i)) n (φ s) (φ t) k := by
    intro k
    induction k with
    | zero => simp [bairAux]
    | succ k ih =>
      rw [bairAux, bairAux, ← ih]
      simp
  unfold bairSeq
  split_ifs
  · simp
  · rw [← h]

/-- Downward induction over the indices of 3.8.10. -/
theorem bair_down {P : ℕ → Prop} (n : ℕ) (hbig : ∀ j, n < j → P j)
    (hstep : ∀ j ≤ n, P (j + 1) → P (j + 2) → P j) (j : ℕ) : P j := by
  have : ∀ d j, n < j + d → P j := by
    intro d
    induction d with
    | zero => exact fun j hj => hbig j (by omega)
    | succ d ih =>
      intro j hj
      rcases lt_or_ge n j with h | h
      · exact hbig j h
      · exact hstep j h (ih _ (by omega)) (ih _ (by omega))
  exact this (n + 1) j (by omega)

/-- `q_j` of 3.8.10. -/
def bairQ (a : ℕ → R) (n : ℕ) (s t : R) : ℕ → R := bairSeq a n s t

/-- `r_j` of 3.8.10. -/
def bairR (a : ℕ → R) (n : ℕ) (s t : R) : ℕ → R := bairSeq (bairQ a n s t) n s t

theorem bairR_rec (a : ℕ → R) (n : ℕ) (s t : R) (j : ℕ) :
    bairR a n s t j = bairQ a n s t j + s * bairR a n s t (j + 1) + t * bairR a n s t (j + 2) :=
  bairSeq_rec_all (fun _ hj => bairSeq_of_lt a s t hj) s t j

/-- The telescoping identity behind the quotient. -/
theorem bair_telescope {S : Type*} [CommRing S] (c : ℕ → S) (s t z : S) (N : ℕ) :
    ∑ j ∈ range N, (c j - s * c (j + 1) - t * c (j + 2)) * z ^ j =
      (z ^ 2 - s * z - t) * ∑ i ∈ range N, c (i + 2) * z ^ i + c 1 * (z - s) + c 0 -
        c N * z ^ N - c (N + 1) * z ^ (N + 1) + s * c (N + 1) * z ^ N := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    ring

/-- The general form of the quotient identity. -/
theorem bair_quotient_gen {S : Type*} [CommRing S] (c e : ℕ → S) (n : ℕ) (s t z : S)
    (hrec : ∀ j ≤ n, e j = c j - s * c (j + 1) - t * c (j + 2)) (hc : ∀ j, n < j → c j = 0) :
    ∑ j ∈ range (n + 1), e j * z ^ j =
      (z ^ 2 - s * z - t) * ∑ i ∈ range (n - 1), c (i + 2) * z ^ i + c 1 * (z - s) + c 0 := by
  have h1 : ∑ j ∈ range (n + 1), e j * z ^ j =
      ∑ j ∈ range (n + 1), (c j - s * c (j + 1) - t * c (j + 2)) * z ^ j :=
    sum_congr rfl fun j hj => by rw [hrec j (by simp at hj; omega)]
  have h2 : ∑ i ∈ range (n + 1), c (i + 2) * z ^ i = ∑ i ∈ range (n - 1), c (i + 2) * z ^ i :=
    (sum_subset (range_subset_range.mpr (by omega)) fun i hi hi' => by
      simp at hi hi'; rw [hc _ (by omega), zero_mul]).symm
  rw [h1, bair_telescope, h2, hc (n + 1) (by omega), hc (n + 2) (by omega)]
  ring

/-- **DLMF §3.8(iv)**: `p(z) = (z² − sz − t)(q_n z^{n−2} + ⋯ + q₂) + q₁(z − s) + q₀`. -/
theorem dlmf_3_8_10_quotient (a : ℕ → R) (n : ℕ) (s t z : R) :
    ∑ j ∈ range (n + 1), a j * z ^ j =
      (z ^ 2 - s * z - t) * ∑ i ∈ range (n - 1), bairQ a n s t (i + 2) * z ^ i +
        bairQ a n s t 1 * (z - s) + bairQ a n s t 0 :=
  bair_quotient_gen _ _ n s t z (fun j hj => by
    simp only [bairQ]; rw [bairSeq_rec a s t hj]; ring) fun j hj => bairSeq_of_lt a s t hj

/-- The quotient identity for a polynomial. -/
theorem dlmf_3_8_10_quotient_poly (p : R[X]) (s t : R) :
    p = (X ^ 2 - C s * X - C t) *
        ∑ i ∈ range (p.natDegree - 1), C (bairQ p.coeff p.natDegree s t (i + 2)) * X ^ i +
      C (bairQ p.coeff p.natDegree s t 1) * (X - C s) + C (bairQ p.coeff p.natDegree s t 0) := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow p]
  exact bair_quotient_gen (fun j => C (bairQ p.coeff p.natDegree s t j)) (fun j => C (p.coeff j))
    _ (C s) (C t) X (fun j hj => by
      simp only [bairQ]; rw [bairSeq_rec _ s t hj]; simp only [map_add, map_mul]; ring)
    fun j hj => by simp [bairQ, bairSeq_of_lt _ s t hj]

/-- The residual `F(s, t) = (q₁, q₀ − s q₁)`: the coefficients of the remainder
`q₁ z + (q₀ − s q₁)` on dividing `p` by `z² − sz − t`. -/
def bairF (a : ℕ → R) (n : ℕ) (w : R × R) : R × R :=
  (bairQ a n w.1 w.2 1, bairQ a n w.1 w.2 0 - w.1 * bairQ a n w.1 w.2 1)

/-- `ℓ = s r₂ + t r₃` (3.8.11). -/
def bairEll (a : ℕ → R) (n : ℕ) (w : R × R) : R :=
  w.1 * bairR a n w.1 w.2 2 + w.2 * bairR a n w.1 w.2 3

/-- `r₂² − ℓ r₃`, the denominator of 3.8.11 and the Jacobian determinant of `F`. -/
def bairDet (a : ℕ → R) (n : ℕ) (w : R × R) : R :=
  bairR a n w.1 w.2 2 ^ 2 - bairEll a n w * bairR a n w.1 w.2 3

/-- **DLMF 3.8.11**: one step of Bairstow's method, `(s, t) ↦ (s + Δs, t + Δt)`. -/
def bairStep {K : Type*} [Field K] (a : ℕ → K) (n : ℕ) (w : K × K) : K × K :=
  (w.1 + (bairR a n w.1 w.2 3 * bairQ a n w.1 w.2 0 - bairR a n w.1 w.2 2 * bairQ a n w.1 w.2 1) /
      bairDet a n w,
    w.2 + (bairEll a n w * bairQ a n w.1 w.2 1 - bairR a n w.1 w.2 2 * bairQ a n w.1 w.2 0) /
      bairDet a n w)

end Rec

/-! ### Exact factors -/

/-- `z² − sz − t` is a factor of `p` iff `F(s, t) = 0`; then `q_n z^{n−2} + ⋯ + q₂` is the
quotient. -/
theorem bairF_eq_zero_iff {K : Type*} [Field K] (p : K[X]) (s t : K) :
    (X ^ 2 - C s * X - C t) ∣ p ↔ bairF p.coeff p.natDegree (s, t) = 0 := by
  set W := ∑ i ∈ range (p.natDegree - 1), C (bairQ p.coeff p.natDegree s t (i + 2)) * X ^ i
  set q₁ := bairQ p.coeff p.natDegree s t 1
  set q₀ := bairQ p.coeff p.natDegree s t 0
  have hp := dlmf_3_8_10_quotient_poly p s t
  have hρ : p - (X ^ 2 - C s * X - C t) * W = C q₁ * X + C (q₀ - s * q₁) := by
    rw [hp]; simp only [map_sub, map_mul]; ring
  have hD : (X ^ 2 - C s * X - C t).natDegree = 2 := by compute_degree!
  have hF : bairF p.coeff p.natDegree (s, t) = 0 ↔ q₁ = 0 ∧ q₀ - s * q₁ = 0 := by
    simp [bairF, q₁, q₀, Prod.ext_iff]
  rw [hF]
  constructor
  · intro hdvd
    have h1 : (X ^ 2 - C s * X - C t) ∣ C q₁ * X + C (q₀ - s * q₁) :=
      hρ ▸ dvd_sub hdvd (dvd_mul_right _ _)
    have h0 := eq_zero_of_dvd_of_natDegree_lt h1 (by
      rw [hD]; exact (natDegree_linear_le).trans_lt (by norm_num))
    have c1 := congrArg (coeff · 1) h0
    have c0 := congrArg (coeff · 0) h0
    simp at c1 c0
    exact ⟨c1, c0⟩
  · rintro ⟨h1, h0⟩
    refine ⟨W, ?_⟩
    rw [← sub_eq_zero, hρ, h0, h1]
    simp

/-- At an exact factor `z² − sz − t = (z − z₁)(z − z₂)` the denominator of 3.8.11 is
`r₂² − ℓr₃ = Q(z₁) Q(z₂)`, `Q(z) = q_n z^{n−2} + ⋯ + q₂` the quotient. -/
theorem bairDet_eq_quotient {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) {s t z₁ z₂ : R}
    (hs : z₁ + z₂ = s) (ht : z₁ * z₂ = -t) :
    bairDet a n (s, t) = (∑ i ∈ range (n - 1), bairQ a n s t (i + 2) * z₁ ^ i) *
      ∑ i ∈ range (n - 1), bairQ a n s t (i + 2) * z₂ ^ i := by
  -- `Q` has the Bairstow sequence `r_{j+2}`
  have hQ : ∀ z, z ^ 2 - s * z - t = 0 →
      ∑ i ∈ range (n - 1), bairQ a n s t (i + 2) * z ^ i =
        bairR a n s t 3 * (z - s) + bairR a n s t 2 := by
    intro z hz
    have hc : ∀ j, n < j → bairR a n s t (j + 2) = 0 := fun j hj =>
      bairSeq_of_lt _ s t (by omega)
    have h := bair_quotient_gen (fun j => bairR a n s t (j + 2))
      (fun j => bairQ a n s t (j + 2)) n s t z (fun j _ => by
        rw [bairR_rec a n s t (j + 2)]; ring) hc
    have hsum : ∑ j ∈ range (n + 1), bairQ a n s t (j + 2) * z ^ j =
        ∑ i ∈ range (n - 1), bairQ a n s t (i + 2) * z ^ i :=
      (sum_subset (range_subset_range.mpr (by omega)) fun i hi hi' => by
        simp at hi hi'; rw [bairQ, bairSeq_of_lt _ s t (by omega), zero_mul]).symm
    rw [← hsum, h, hz, zero_mul, zero_add]
  have h₁ : z₁ ^ 2 - s * z₁ - t = 0 := by rw [← hs]; linear_combination -ht
  have h₂ : z₂ ^ 2 - s * z₂ - t = 0 := by rw [← hs]; linear_combination -ht
  rw [hQ z₁ h₁, hQ z₂ h₂, bairDet, bairEll]
  rw [← hs, show t = -(z₁ * z₂) by rw [ht]; ring]
  ring

/-- `bairDet_eq_quotient` for real data, with the (possibly complex) zeros `z₁, z₂` of the
quadratic factor. -/
theorem bairDet_eq_quotient_complex (a : ℕ → ℝ) (n : ℕ) {s t : ℝ} {z₁ z₂ : ℂ}
    (hs : z₁ + z₂ = s) (ht : z₁ * z₂ = -t) :
    ((bairDet a n (s, t) : ℝ) : ℂ) =
      (∑ i ∈ range (n - 1), ((bairQ a n s t (i + 2) : ℝ) : ℂ) * z₁ ^ i) *
        ∑ i ∈ range (n - 1), ((bairQ a n s t (i + 2) : ℝ) : ℂ) * z₂ ^ i := by
  have e : ∀ j, ((bairQ a n s t j : ℝ) : ℂ) = bairQ (fun i => (a i : ℂ)) n s t j := fun j =>
    bairSeq_map Complex.ofRealHom a n s t j
  have eR : ∀ j, ((bairR a n s t j : ℝ) : ℂ) = bairR (fun i => (a i : ℂ)) n s t j := fun j => by
    have := bairSeq_map Complex.ofRealHom (bairQ a n s t) n s t j
    simp only [Complex.ofRealHom_eq_coe] at this
    rw [bairR, this, bairR]
    congr 1
    funext i
    exact e i
  simp only [e]
  rw [← bairDet_eq_quotient _ n hs ht]
  simp only [bairDet, bairEll]
  push_cast
  simp only [eR]

/-! ### Bairstow's method is Newton's method -/

section Newton

open ContinuousLinearMap

/-- `q_j` as a function of `w = (s, t)`. -/
def qf (a : ℕ → ℝ) (n j : ℕ) (w : ℝ × ℝ) : ℝ := bairQ a n w.1 w.2 j

/-- `r_j` as a function of `w = (s, t)`. -/
def rf (a : ℕ → ℝ) (n j : ℕ) (w : ℝ × ℝ) : ℝ := bairR a n w.1 w.2 j

theorem contDiff_bairSeq {b : ℕ → ℝ × ℝ → ℝ} (hb : ∀ j, ContDiff ℝ 2 (b j)) (n j : ℕ) :
    ContDiff ℝ 2 fun w : ℝ × ℝ => bairSeq (fun i => b i w) n w.1 w.2 j := by
  refine bair_down (P := fun j => ContDiff ℝ 2 fun w : ℝ × ℝ =>
    bairSeq (fun i => b i w) n w.1 w.2 j) n (fun j hj => ?_) (fun j hj h1 h2 => ?_) j
  · simp only [bairSeq_of_lt _ _ _ hj]; exact contDiff_const
  · have : (fun w : ℝ × ℝ => bairSeq (fun i => b i w) n w.1 w.2 j) = fun w =>
        b j w + w.1 * bairSeq (fun i => b i w) n w.1 w.2 (j + 1) +
          w.2 * bairSeq (fun i => b i w) n w.1 w.2 (j + 2) :=
      funext fun w => bairSeq_rec _ _ _ hj
    rw [this]
    exact ((hb j).add (contDiff_fst.mul h1)).add (contDiff_snd.mul h2)

theorem contDiff_qf (a : ℕ → ℝ) (n j : ℕ) : ContDiff ℝ 2 (qf a n j) :=
  contDiff_bairSeq (b := fun i _ => a i) (fun _ => contDiff_const) n j

theorem contDiff_rf (a : ℕ → ℝ) (n j : ℕ) : ContDiff ℝ 2 (rf a n j) :=
  contDiff_bairSeq (b := fun i w => qf a n i w) (fun i => contDiff_qf a n i) n j

/-- `∂q_j/∂s = r_{j+1}`, `∂q_j/∂t = r_{j+2}`. -/
theorem hasFDerivAt_bairQ (a : ℕ → ℝ) (n j : ℕ) (w : ℝ × ℝ) :
    HasFDerivAt (qf a n j) (rf a n (j + 1) w • fst ℝ ℝ ℝ + rf a n (j + 2) w • snd ℝ ℝ ℝ) w := by
  refine bair_down (P := fun j => HasFDerivAt (qf a n j)
    (rf a n (j + 1) w • fst ℝ ℝ ℝ + rf a n (j + 2) w • snd ℝ ℝ ℝ) w) n
    (fun j hj => ?_) (fun j hj h1 h2 => ?_) j
  · have h0 : qf a n j = fun _ => 0 := funext fun _ => bairSeq_of_lt _ _ _ hj
    have r1 : rf a n (j + 1) w = 0 := bairSeq_of_lt _ _ _ (by omega)
    have r2 : rf a n (j + 2) w = 0 := bairSeq_of_lt _ _ _ (by omega)
    rw [h0, r1, r2, zero_smul, zero_smul, add_zero]
    exact hasFDerivAt_const _ _
  · have e : qf a n j = fun w : ℝ × ℝ =>
        a j + w.1 * qf a n (j + 1) w + w.2 * qf a n (j + 2) w :=
      funext fun w => bairSeq_rec _ _ _ hj
    rw [e]
    refine (((hasFDerivAt_const (a j) w).add (hasFDerivAt_fst.mul h1)).add
      (hasFDerivAt_snd.mul h2)).congr_fderiv ?_
    have e1 := bairR_rec a n w.1 w.2 (j + 1)
    have e2 := bairR_rec a n w.1 w.2 (j + 2)
    ext <;> simp [rf, qf]
    · linear_combination -e1
    · linear_combination -e2

/-- The Jacobian `[[r₂, r₃], [t r₃, r₂ − s r₃]]` of `F`. -/
noncomputable def bairJ (a : ℕ → ℝ) (n : ℕ) (w : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (rf a n 2 w • fst ℝ ℝ ℝ + rf a n 3 w • snd ℝ ℝ ℝ).prod
    ((w.2 * rf a n 3 w) • fst ℝ ℝ ℝ + (rf a n 2 w - w.1 * rf a n 3 w) • snd ℝ ℝ ℝ)

theorem bairJ_apply (a : ℕ → ℝ) (n : ℕ) (w v : ℝ × ℝ) :
    bairJ a n w v = (rf a n 2 w * v.1 + rf a n 3 w * v.2,
      w.2 * rf a n 3 w * v.1 + (rf a n 2 w - w.1 * rf a n 3 w) * v.2) := by
  simp [bairJ]

/-- The Jacobian of `F(s, t) = (q₁, q₀ − s q₁)`. -/
theorem hasFDerivAt_bairF (a : ℕ → ℝ) (n : ℕ) (w : ℝ × ℝ) :
    HasFDerivAt (bairF a n) (bairJ a n w) w := by
  have h1 := hasFDerivAt_bairQ a n 1 w
  have h0 := hasFDerivAt_bairQ a n 0 w
  have e : bairF a n = fun w => (qf a n 1 w, qf a n 0 w - w.1 * qf a n 1 w) := rfl
  rw [e]
  refine (h1.prodMk (h0.sub (hasFDerivAt_fst.mul h1))).congr_fderiv ?_
  have e1 := bairR_rec a n w.1 w.2 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [bairJ, rf, qf]
  linear_combination v.1 * e1

/-- **DLMF 3.8.11 is Newton's rule for `F`**: the step `Δ` solves `J(s, t) Δ = −F(s, t)`. -/
theorem bairStep_newton (a : ℕ → ℝ) (n : ℕ) {w : ℝ × ℝ} (hdet : bairDet a n w ≠ 0) :
    bairJ a n w (bairStep a n w - w) = -bairF a n w := by
  have hd : bairDet a n w = rf a n 2 w ^ 2 - bairEll a n w * rf a n 3 w := rfl
  have hl : bairEll a n w = w.1 * rf a n 2 w + w.2 * rf a n 3 w := rfl
  rw [bairJ_apply]
  simp only [bairStep, bairF, Prod.fst_sub, Prod.snd_sub, Prod.neg_mk, add_sub_cancel_left]
  simp only [rf] at hd hl ⊢
  generalize bairDet a n w = d at hdet hd ⊢
  generalize bairEll a n w = l at hd hl ⊢
  refine Prod.ext ?_ ?_ <;> dsimp only <;> field_simp <;> subst hd <;> subst hl <;> ring

end Newton

/-! ### Newton's method in a normed space -/

section NewtonNormed

variable {E : Type*} [NormedAddCommGroup E]

/-- Newton's estimate: if `F(ζ) = 0`, `F′ = J` is `L`-Lipschitz on a ball, `‖v‖ ≤ M ‖J(w) v‖`
there, and the step `N` solves `J(w)(N(w) − w) = −F(w)`, then `‖N(w) − ζ‖ ≤ ML ‖w − ζ‖²`. -/
theorem newton_sq_bound [NormedSpace ℝ E] {F N : E → E} {J : E → E →L[ℝ] E} {ζ : E}
    {δ L M : ℝ} (hL : 0 ≤ L) (hM0 : 0 ≤ M) (hF : ∀ w ∈ ball ζ δ, HasFDerivAt F (J w) w)
    (hJ : ∀ w ∈ ball ζ δ, ∀ x ∈ ball ζ δ, ‖J x - J w‖ ≤ L * ‖x - w‖)
    (hM : ∀ w ∈ ball ζ δ, ∀ v, ‖v‖ ≤ M * ‖J w v‖)
    (hN : ∀ w ∈ ball ζ δ, J w (N w - w) = -F w) (h0 : F ζ = 0) :
    ∀ w ∈ ball ζ δ, ‖N w - ζ‖ ≤ M * L * ‖w - ζ‖ ^ 2 := by
  intro w hw
  have hζ : ζ ∈ ball ζ δ := mem_ball_self (lt_of_le_of_lt dist_nonneg hw)
  set S := ball ζ δ ∩ closedBall w ‖ζ - w‖
  have hS : Convex ℝ S := (convex_ball _ _).inter (convex_closedBall _ _)
  have hg : ∀ x ∈ S, HasFDerivWithinAt (fun x => F x - J w x) (J x - J w) S x := fun x hx =>
    ((hF x hx.1).sub (J w).hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ x ∈ S, ‖J x - J w‖ ≤ L * ‖ζ - w‖ := fun x hx => by
    refine (hJ w hw x hx.1).trans ?_
    have := hx.2
    rw [mem_closedBall, dist_eq_norm] at this
    gcongr
  have key := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbd
    ⟨hw, mem_closedBall_self (norm_nonneg _)⟩ ⟨hζ, by rw [mem_closedBall, dist_eq_norm]⟩
  have e : J w (N w - ζ) = (F ζ - J w ζ) - (F w - J w w) := by
    rw [show N w - ζ = (N w - w) + (w - ζ) by abel, map_add, hN w hw, h0, map_sub]
    abel
  calc ‖N w - ζ‖ ≤ M * ‖J w (N w - ζ)‖ := hM w hw _
    _ = M * ‖(F ζ - J w ζ) - (F w - J w w)‖ := by rw [e]
    _ ≤ M * (L * ‖ζ - w‖ * ‖ζ - w‖) := by gcongr
    _ = M * L * ‖w - ζ‖ ^ 2 := by rw [norm_sub_rev]; ring

/-- A quadratic error bound on a ball gives local convergence and 3.8.3 with `p = 2`. -/
theorem iter_of_sq_bound {T : E → E} {ζ : E} {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (h : ∀ z ∈ ball ζ δ, ‖T z - ζ‖ ≤ K * ‖z - ζ‖ ^ 2) :
    ConvergesLocally T ζ ∧ ∃ δ' > 0, ∀ z₀ ∈ ball ζ δ',
      (∀ n, ‖T^[n + 1] z₀ - ζ‖ ≤ K * ‖T^[n] z₀ - ζ‖ ^ 2) ∧
      ((∀ n, T^[n] z₀ ≠ ζ) → IsQuadraticConv (fun n => T^[n] z₀) ζ) := by
  set δ' := min δ (1 / (2 * K + 1))
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have hc : ∀ z ∈ ball ζ δ', ‖T z - ζ‖ ≤ 1 / 2 * ‖z - ζ‖ := fun z hz => by
    have hz' : ‖z - ζ‖ < δ' := by rwa [mem_ball, dist_eq_norm] at hz
    have h1 : ‖z - ζ‖ * (2 * K + 1) ≤ 1 := by
      have := hz'.le.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at this
    have h2 := h z (ball_subset_ball (min_le_left _ _) hz)
    have hn := norm_nonneg (z - ζ)
    nlinarith
  have hmem : ∀ z ∈ ball ζ δ', T z ∈ ball ζ δ' := fun z hz => by
    have := hc z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    linarith [norm_nonneg (z - ζ)]
  have hit : ∀ z₀ ∈ ball ζ δ', ∀ n, T^[n] z₀ ∈ ball ζ δ' := fun z₀ hz n => by
    induction n with
    | zero => exact hz
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmem _ ih
  refine ⟨(convergesLocally_of_contract hδ' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hc).1,
    δ', hδ', fun z₀ hz => ?_⟩
  have hq : ∀ n, ‖T^[n + 1] z₀ - ζ‖ ≤ K * ‖T^[n] z₀ - ζ‖ ^ 2 := fun n => by
    rw [Function.iterate_succ_apply']
    exact h _ (ball_subset_ball (min_le_left _ _) (hit z₀ hz n))
  refine ⟨hq, fun hne => ⟨K + 1, Eventually.of_forall fun n => ?_⟩⟩
  have hpos : 0 < ‖T^[n] z₀ - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne n))
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ‖T^[n + 1] z₀ - ζ‖ ≤ K * ‖T^[n] z₀ - ζ‖ ^ 2 := hq n
    _ < (K + 1) * ‖T^[n] z₀ - ζ‖ ^ 2 := by gcongr; linarith

/-- Cramer's rule bound for a `2 × 2` system. -/
theorem norm_le_of_two_by_two {a b c d B D : ℝ} (hD : 0 < D) (hdet : D ≤ |a * d - b * c|)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) (hd : |d| ≤ B) (v : ℝ × ℝ) :
    ‖v‖ ≤ 2 * B / D * ‖((a * v.1 + b * v.2, c * v.1 + d * v.2) : ℝ × ℝ)‖ := by
  set y : ℝ × ℝ := (a * v.1 + b * v.2, c * v.1 + d * v.2)
  have hy1 : |y.1| ≤ ‖y‖ := by simpa using norm_fst_le y
  have hy2 : |y.2| ≤ ‖y‖ := by simpa using norm_snd_le y
  have hB : 0 ≤ B := (abs_nonneg a).trans ha
  have hdet0 : 0 < |a * d - b * c| := hD.trans_le hdet
  have one : ∀ u : ℝ, |u| * |a * d - b * c| ≤ 2 * B * ‖y‖ → |u| ≤ 2 * B / D * ‖y‖ := by
    intro u hu
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    nlinarith [abs_nonneg u]
  rw [norm_prod_le_iff]
  refine ⟨?_, ?_⟩ <;> rw [Real.norm_eq_abs] <;> refine one _ ?_ <;> rw [← abs_mul]
  · rw [show v.1 * (a * d - b * c) = d * y.1 - b * y.2 by simp only [y]; ring]
    calc |d * y.1 - b * y.2| ≤ |d| * |y.1| + |b| * |y.2| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ B * ‖y‖ + B * ‖y‖ := by gcongr
      _ = 2 * B * ‖y‖ := by ring
  · rw [show v.2 * (a * d - b * c) = a * y.2 - c * y.1 by simp only [y]; ring]
    calc |a * y.2 - c * y.1| ≤ |a| * |y.2| + |c| * |y.1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ B * ‖y‖ + B * ‖y‖ := by gcongr
      _ = 2 * B * ‖y‖ := by ring

end NewtonNormed

/-! ### Local quadratic convergence -/

/-- **DLMF §3.8(iv)**: "The method converges locally and quadratically" — at an exact quadratic
factor `z² − s*z − t*` of `p` (`F(s*, t*) = 0`, `bairF_eq_zero_iff`) with `r₂² − ℓr₃ ≠ 0`, i.e.
`Q(z₁) Q(z₂) ≠ 0` (`bairDet_eq_quotient_complex`). The errors satisfy
`‖e_{k+1}‖ ≤ K ‖e_k‖²`, and 3.8.3 holds with `p = 2` whenever no iterate is exact. -/
theorem dlmf_3_8_iv_bairstow (a : ℕ → ℝ) (n : ℕ) {w₀ : ℝ × ℝ} (hF : bairF a n w₀ = 0)
    (hdet : bairDet a n w₀ ≠ 0) :
    ConvergesLocally (bairStep a n) w₀ ∧ ∃ δ > 0, ∃ K ≥ 0, ∀ v₀ ∈ ball w₀ δ,
      (∀ k, ‖(bairStep a n)^[k + 1] v₀ - w₀‖ ≤ K * ‖(bairStep a n)^[k] v₀ - w₀‖ ^ 2) ∧
      ((∀ k, (bairStep a n)^[k] v₀ ≠ w₀) →
        IsQuadraticConv (fun k => (bairStep a n)^[k] v₀) w₀) := by
  have hFd := hasFDerivAt_bairF a n
  have hC : ContDiff ℝ 2 (bairF a n) :=
    show ContDiff ℝ 2 (fun w => (qf a n 1 w, qf a n 0 w - w.1 * qf a n 1 w)) from
      (contDiff_qf a n 1).prodMk ((contDiff_qf a n 0).sub (contDiff_fst.mul (contDiff_qf a n 1)))
  have hfd : fderiv ℝ (bairF a n) = bairJ a n := funext fun w => (hFd w).fderiv
  have hJ1 : ContDiffAt ℝ 1 (bairJ a n) w₀ := by
    rw [← hfd]; exact hC.contDiffAt.fderiv_right (m := 1) (by norm_num)
  obtain ⟨L, t, ht, hL⟩ := hJ1.exists_lipschitzOnWith
  have hr2 : Continuous (rf a n 2) := (contDiff_rf a n 2).continuous
  have hr3 : Continuous (rf a n 3) := (contDiff_rf a n 3).continuous
  have hdc : Continuous (bairDet a n) :=
    show Continuous fun w : ℝ × ℝ => rf a n 2 w ^ 2 -
        (w.1 * rf a n 2 w + w.2 * rf a n 3 w) * rf a n 3 w from
      (hr2.pow 2).sub (((continuous_fst.mul hr2).add (continuous_snd.mul hr3)).mul hr3)
  set D := |bairDet a n w₀| / 2
  have hD : 0 < D := by positivity
  set B := |rf a n 2 w₀| + |rf a n 3 w₀| + |w₀.1| + |w₀.2| + 1
  have n1 := abs_nonneg (rf a n 2 w₀)
  have n2 := abs_nonneg (rf a n 3 w₀)
  have n3 := abs_nonneg w₀.1
  have n4 := abs_nonneg w₀.2
  have hB1 : 1 ≤ B := by simp only [B]; linarith
  have e1 : ∀ᶠ w in 𝓝 w₀, D < |bairDet a n w| :=
    ((continuous_abs.comp hdc).tendsto w₀).eventually_const_lt
      (by simp only [D, Function.comp]; linarith [abs_pos.mpr hdet])
  have ev : ∀ {f : ℝ × ℝ → ℝ}, Continuous f → |f w₀| < B → ∀ᶠ w in 𝓝 w₀, |f w| < B :=
    fun hf hlt => ((continuous_abs.comp hf).tendsto w₀).eventually_lt_const hlt
  have e2 := ev hr2 (by simp only [B]; linarith)
  have e3 := ev hr3 (by simp only [B]; linarith)
  have e4 := ev continuous_fst (by simp only [B]; linarith)
  have e5 := ev continuous_snd (by simp only [B]; linarith)
  have ht' : ∀ᶠ w in 𝓝 w₀, w ∈ t := ht
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (ht'.and (e1.and (e2.and (e3.and (e4.and e5)))))
  set B' := B + B * B
  have hBB : B ≤ B' := by simp only [B']; nlinarith
  have hM : ∀ w ∈ ball w₀ δ, ∀ v, ‖v‖ ≤ 2 * B' / D * ‖bairJ a n w v‖ := by
    intro w hw v
    obtain ⟨-, -, h2, h3, h4, h5⟩ := hball hw
    rw [bairJ_apply]
    refine norm_le_of_two_by_two hD ?_ (h2.le.trans hBB) (h3.le.trans hBB) ?_ ?_ v
    · have := (hball hw).2.1
      convert this.le using 2
      simp only [bairDet, bairEll, rf]
      ring
    · rw [abs_mul]; simp only [B']; nlinarith [abs_nonneg w.2, abs_nonneg (rf a n 3 w)]
    · refine (abs_sub _ _).trans ?_
      rw [abs_mul]; simp only [B']; nlinarith [abs_nonneg w.1, abs_nonneg (rf a n 3 w)]
  have hbound := newton_sq_bound (N := bairStep a n) (M := 2 * B' / D) L.coe_nonneg
    (by positivity) (fun w _ => hFd w)
    (fun w hw x hx => by
      have := hL.dist_le_mul x (hball hx).1 w (hball hw).1
      rwa [dist_eq_norm, dist_eq_norm] at this)
    hM (fun w hw => bairStep_newton a n (fun h0 => by
      have := (hball hw).2.1; rw [h0, abs_zero] at this; linarith)) hF
  obtain ⟨hloc, δ', hδ', hit⟩ := iter_of_sq_bound hδ (by positivity) hbound
  exact ⟨hloc, δ', hδ', _, by positivity, hit⟩

/-! ### Example: `z⁴ − 2z² + 1` -/

section Example

variable {R : Type*} [CommRing R]

/-- The coefficients of `z⁴ − 2z² + 1`. -/
def bairExA : ℕ → R
  | 0 => 1
  | 2 => -2
  | 4 => 1
  | _ => 0

theorem bairExA_map {S : Type*} [CommRing S] (φ : R →+* S) (j : ℕ) :
    φ (bairExA j) = bairExA j := by
  rcases j with _ | _ | _ | _ | _ | j <;> simp [bairExA, map_ofNat]

theorem bairExA_eval (z : R) :
    ∑ j ∈ range 5, bairExA j * z ^ j = z ^ 4 - 2 * z ^ 2 + 1 := by
  simp [sum_range_succ, bairExA]; ring

end Example

theorem bairQ_map {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L) (a : ℕ → K) (n : ℕ)
    (s t : K) (j : ℕ) : φ (bairQ a n s t j) = bairQ (fun i => φ (a i)) n (φ s) (φ t) j :=
  bairSeq_map φ a n s t j

theorem bairR_map {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L) (a : ℕ → K) (n : ℕ)
    (s t : K) (j : ℕ) : φ (bairR a n s t j) = bairR (fun i => φ (a i)) n (φ s) (φ t) j := by
  rw [bairR, bairSeq_map, bairR]
  congr 1
  funext i
  exact bairQ_map φ a n s t i

theorem bairStep_map {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a : ℕ → K) (n : ℕ)
    (w : K × K) : ((φ (bairStep a n w).1, φ (bairStep a n w).2) : L × L) =
      bairStep (fun i => φ (a i)) n (φ w.1, φ w.2) := by
  simp only [bairStep, bairDet, bairEll, map_add, map_div₀, map_sub, map_mul, map_pow,
    bairQ_map, bairR_map]

/-- Bairstow's method for `z⁴ − 2z² + 1` in `ℚ`. -/
def bairExStepQ (w : ℚ × ℚ) : ℚ × ℚ := bairStep bairExA 4 w

theorem bairEx_iterate_cast (k : ℕ) (w : ℚ × ℚ) :
    (((bairExStepQ^[k] w).1 : ℝ), ((bairExStepQ^[k] w).2 : ℝ)) =
      (bairStep bairExA 4)^[k] ((w.1 : ℝ), (w.2 : ℝ)) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, bairExStepQ]
    congr 1
    have := bairStep_map (Rat.castHom ℝ) bairExA 4 w
    simp only [bairExA_map, Rat.coe_castHom] at this
    exact this

theorem bairEx_checks :
    bairF (bairExA (R := ℚ)) 4 (2, -1) = 0 ∧ bairDet (bairExA (R := ℚ)) 4 (2, -1) = 16 := by
  decide +kernel

/-- **Example** (DLMF §3.8(iv)): `z⁴ − 2z² + 1 = (z² − 2z + 1)(z² + 2z + 1)`, so `(s, t) = (2, −1)`
is an exact quadratic factor `(z − 1)²`; the denominator of 3.8.11 there is
`Q(1)² = 4² = 16 ≠ 0`, and Bairstow's method converges locally and quadratically to `(2, −1)`
"even if the two zeros of the wanted quadratic factor are real and the same". -/
theorem dlmf_3_8_iv_bairstow_example :
    (∀ z : ℝ, z ^ 4 - 2 * z ^ 2 + 1 = (z ^ 2 - 2 * z - (-1)) * (z ^ 2 + 2 * z + 1)) ∧
      bairF (bairExA (R := ℝ)) 4 (2, -1) = 0 ∧ bairDet (bairExA (R := ℝ)) 4 (2, -1) = 16 ∧
      bairDet (bairExA (R := ℝ)) 4 (2, -1) =
        (∑ i ∈ range 3, bairQ (bairExA (R := ℝ)) 4 2 (-1) (i + 2) * 1 ^ i) ^ 2 ∧
      ConvergesLocally (bairStep (bairExA (R := ℝ)) 4) (2, -1) ∧
      ∃ δ > 0, ∃ K ≥ 0, ∀ v₀ ∈ ball ((2, -1) : ℝ × ℝ) δ,
        (∀ k, ‖(bairStep bairExA 4)^[k + 1] v₀ - (2, -1)‖ ≤
          K * ‖(bairStep bairExA 4)^[k] v₀ - (2, -1)‖ ^ 2) ∧
        ((∀ k, (bairStep bairExA 4)^[k] v₀ ≠ (2, -1)) →
          IsQuadraticConv (fun k => (bairStep (bairExA (R := ℝ)) 4)^[k] v₀) (2, -1)) := by
  obtain ⟨hF, hD⟩ := bairEx_checks
  have eF : bairF (bairExA (R := ℝ)) 4 (2, -1) = 0 := by
    have h1 := congrArg (fun p : ℚ × ℚ => ((p.1 : ℝ), (p.2 : ℝ))) hF
    simp only [bairF, Prod.mk_zero_zero, Prod.fst_zero, Prod.snd_zero, Rat.cast_zero] at h1
    simp only [bairF, Prod.mk_eq_zero] at h1 ⊢
    have q1 := bairQ_map (Rat.castHom ℝ) (bairExA (R := ℚ)) 4 2 (-1) 1
    have q0 := bairQ_map (Rat.castHom ℝ) (bairExA (R := ℚ)) 4 2 (-1) 0
    simp only [bairExA_map, Rat.coe_castHom, map_ofNat, map_neg, map_one] at q1 q0
    push_cast at h1
    rw [← q1, ← q0]
    exact h1
  have eD : bairDet (bairExA (R := ℝ)) 4 (2, -1) = 16 := by
    have h1 := congrArg (fun x : ℚ => (x : ℝ)) hD
    simp only [bairDet, bairEll] at h1 ⊢
    have r2 := bairR_map (Rat.castHom ℝ) (bairExA (R := ℚ)) 4 2 (-1) 2
    have r3 := bairR_map (Rat.castHom ℝ) (bairExA (R := ℚ)) 4 2 (-1) 3
    simp only [bairExA_map, Rat.coe_castHom, map_ofNat, map_neg, map_one] at r2 r3
    push_cast at h1
    rw [← r2, ← r3]
    exact h1
  have hQ := bairDet_eq_quotient (bairExA (R := ℝ)) 4 (s := 2) (t := -1) (z₁ := 1) (z₂ := 1)
    (by norm_num) (by norm_num)
  obtain ⟨hloc, δ, hδ, K, hK, hit⟩ := dlmf_3_8_iv_bairstow (bairExA (R := ℝ)) 4 eF
    (by rw [eD]; norm_num)
  refine ⟨fun z => by ring, eF, eD, by rw [hQ]; ring, hloc, δ, hδ, K, hK, hit⟩

/-! ### Table 3.8.3 -/

/-- Table 3.8.3 as printed (13 decimals). -/
def tab383 : ℕ → ℚ × ℚ
  | 0 => (175 / 100, -50 / 100)
  | 1 => (21352729454109 / 10 ^ 13, -12123575284943 / 10 ^ 13)
  | 2 => (20178610488956 / 10 ^ 13, -10252861401539 / 10 ^ 13)
  | 3 => (20003606329466 / 10 ^ 13, -10004763067522 / 10 ^ 13)
  | 4 => (20000001474803 / 10 ^ 13, -10000001858298 / 10 ^ 13)
  | _ => (2, -1)

/-- The sup-norm error `max(|s − 2|, |t + 1|)`. -/
def errQ (w : ℚ × ℚ) : ℚ := max |w.1 - 2| |w.2 + 1|

theorem tab383_check :
    (∀ k ≤ 5, |(bairExStepQ^[k] (7 / 4, -1 / 2)).1 - (tab383 k).1| < 5 / 10 ^ 14 ∧
      |(bairExStepQ^[k] (7 / 4, -1 / 2)).2 - (tab383 k).2| < 5 / 10 ^ 14) ∧
    ∀ k ≤ 4, errQ (bairExStepQ^[k + 1] (7 / 4, -1 / 2)) ≤
      errQ (bairExStepQ^[k] (7 / 4, -1 / 2)) ^ 2 := by
  decide +kernel

/-- **Table 3.8.3**: Bairstow's method for `z⁴ − 2z² + 1` from `s₀ = 7/4`, `t₀ = −1/2`. All
printed `sₙ`, `tₙ` are correctly rounded to 13 decimals, and the errors decrease quadratically:
`‖(sₙ₊₁, tₙ₊₁) − (2, −1)‖ ≤ ‖(sₙ, tₙ) − (2, −1)‖²` for `n ≤ 4` (sup norm). -/
theorem dlmf_table_3_8_3 :
    (∀ k ≤ 5, |((bairStep bairExA 4)^[k] ((7 / 4 : ℝ), (-1 / 2 : ℝ))).1 - (tab383 k).1| <
        5 / 10 ^ 14 ∧
      |((bairStep bairExA 4)^[k] ((7 / 4 : ℝ), (-1 / 2 : ℝ))).2 - (tab383 k).2| <
        5 / 10 ^ 14) ∧
    ∀ k ≤ 4, ‖(bairStep bairExA 4)^[k + 1] ((7 / 4 : ℝ), (-1 / 2 : ℝ)) - (2, -1)‖ ≤
      ‖(bairStep bairExA 4)^[k] ((7 / 4 : ℝ), (-1 / 2 : ℝ)) - (2, -1)‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := tab383_check
  have e : ∀ k, (bairStep bairExA 4)^[k] ((7 / 4 : ℝ), (-1 / 2 : ℝ)) =
      (((bairExStepQ^[k] (7 / 4, -1 / 2)).1 : ℝ), ((bairExStepQ^[k] (7 / 4, -1 / 2)).2 : ℝ)) :=
    fun k => by rw [bairEx_iterate_cast]; norm_num
  have c : ∀ x y : ℚ, (|(x : ℝ) - y| : ℝ) = ((|x - y| : ℚ) : ℝ) := fun x y => by push_cast; rfl
  have b : ((5 / 10 ^ 14 : ℚ) : ℝ) = 5 / 10 ^ 14 := by norm_num
  have en : ∀ w : ℚ × ℚ, ‖(((w.1 : ℝ), (w.2 : ℝ)) : ℝ × ℝ) - (2, -1)‖ = ((errQ w : ℚ) : ℝ) :=
    fun w => by
      simp only [errQ, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
      push_cast
      ring_nf
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [e, ← b, c, c]
    exact ⟨by exact_mod_cast (h1 k hk).1, by exact_mod_cast (h1 k hk).2⟩
  · rw [e, e, en, en]
    exact_mod_cast h2 k hk

end Azurite.DLMF
