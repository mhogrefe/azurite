import Azurite.BasuPollackRoy.Chapter4.Section4_7.MomentMap
import Azurite.BasuPollackRoy.Chapter4.Section4_7.Theorem_4_104
import Mathlib.Algebra.BigOperators.Field

/-!
# BPR §4.7, Proposition 4.106: algebraic properties of the moment map

The moment map `momentMap : ℙ_k(C) → R^N` sends a line to the orthogonal projector onto it; it is
already proven injective and continuous. Here we record its remaining purely *algebraic* properties
(no topology):

* **Trace identity** (`sum_projReV_diag`): the diagonal real entries of the projector sum to `1`
  (the projector has rank one and trace one).
* **Bounded entries** (`abs_projReV_le_one`, `abs_projImV_le_one`): every entry lies in `[-1, 1]`,
  by a two-dimensional Cauchy–Schwarz estimate.
* **Line recovery** (`reL_chartInv_eq`, `imL_chartInv_eq`): on each affine chart `𝒰ᵢ`, the chart
  coordinates `chartInv i x` are recovered explicitly from the projector entries of `momentMap x`
  by the formula `entry / diagonal`. This is the algebraic core of the statement that `momentMap`
  is an embedding: it exhibits a continuous local inverse.

Everything stays inside `Ri.reL` / `Ri.imL`, the product/inverse formulas `reL_mul` / `imL_mul`,
`Ri.reL_inv` / `Ri.imL_inv`, `Ri.ext_reL_imL`, real arithmetic, and `hermNormSq`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-! ### Trace identity -/

set_option linter.unusedSectionVars false in
/-- **Trace identity.** The diagonal real entries of the projector sum to `1`: the rank-one
Hermitian projector onto a line has trace one. -/
theorem sum_projReV_diag {v : Fin (k + 1) → Ri R} (hv : v ≠ 0) :
    (∑ i, projReV v i i) = 1 := by
  have hH : hermNormSq v ≠ 0 := ne_of_gt (hermNormSq_pos hv)
  have hsum : (∑ i, projReV v i i)
      = (∑ i, (Ri.reL (v i) * Ri.reL (v i) + Ri.imL (v i) * Ri.imL (v i))) / hermNormSq v := by
    rw [Finset.sum_div]
    rfl
  rw [hsum]
  have : (∑ i, (Ri.reL (v i) * Ri.reL (v i) + Ri.imL (v i) * Ri.imL (v i))) = hermNormSq v := by
    rw [hermNormSq]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this, div_self hH]

/-! ### Bounded entries -/

set_option linter.unusedSectionVars false in
/-- The `j`-th summand `(Re vⱼ)² + (Im vⱼ)²` is at most the full Hermitian norm `‖v‖²`. -/
private theorem summand_le_hermNormSq (v : Fin (k + 1) → Ri R) (j : Fin (k + 1)) :
    Ri.reL (v j) ^ 2 + Ri.imL (v j) ^ 2 ≤ hermNormSq v := by
  rw [hermNormSq]
  refine Finset.single_le_sum (f := fun i => Ri.reL (v i) ^ 2 + Ri.imL (v i) ^ 2)
    (fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ j)

set_option linter.unusedSectionVars false in
/-- **Bounded real entries.** Every real entry of the projector lies in `[-1, 1]`. -/
theorem abs_projReV_le_one {v : Fin (k + 1) → Ri R} (hv : v ≠ 0) (j l : Fin (k + 1)) :
    |projReV v j l| ≤ 1 := by
  have hHpos : (0 : R) < hermNormSq v := hermNormSq_pos hv
  set aⱼ := Ri.reL (v j); set bⱼ := Ri.imL (v j)
  set aₗ := Ri.reL (v l); set bₗ := Ri.imL (v l)
  set H := hermNormSq v with hHdef
  -- single-summand bounds
  have hj : aⱼ ^ 2 + bⱼ ^ 2 ≤ H := summand_le_hermNormSq v j
  have hl : aₗ ^ 2 + bₗ ^ 2 ≤ H := summand_le_hermNormSq v l
  have hjn : 0 ≤ aⱼ ^ 2 + bⱼ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hln : 0 ≤ aₗ ^ 2 + bₗ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  -- `|numerator| ≤ H`
  have hnum : |aⱼ * aₗ + bⱼ * bₗ| ≤ H := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (aⱼ * bₗ - bⱼ * aₗ), sq_nonneg (aⱼ + aₗ), sq_nonneg (bⱼ + bₗ),
        mul_nonneg hjn hln, hHpos]
    · nlinarith [sq_nonneg (aⱼ * bₗ - bⱼ * aₗ), sq_nonneg (aⱼ - aₗ), sq_nonneg (bⱼ - bₗ),
        mul_nonneg hjn hln, hHpos]
  rw [projReV, abs_div, abs_of_pos hHpos, div_le_one hHpos]
  exact hnum

set_option linter.unusedSectionVars false in
/-- **Bounded imaginary entries.** Every imaginary entry of the projector lies in `[-1, 1]`. -/
theorem abs_projImV_le_one {v : Fin (k + 1) → Ri R} (hv : v ≠ 0) (j l : Fin (k + 1)) :
    |projImV v j l| ≤ 1 := by
  have hHpos : (0 : R) < hermNormSq v := hermNormSq_pos hv
  set aⱼ := Ri.reL (v j); set bⱼ := Ri.imL (v j)
  set aₗ := Ri.reL (v l); set bₗ := Ri.imL (v l)
  set H := hermNormSq v with hHdef
  have hj : aⱼ ^ 2 + bⱼ ^ 2 ≤ H := summand_le_hermNormSq v j
  have hl : aₗ ^ 2 + bₗ ^ 2 ≤ H := summand_le_hermNormSq v l
  have hjn : 0 ≤ aⱼ ^ 2 + bⱼ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hln : 0 ≤ aₗ ^ 2 + bₗ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnum : |bⱼ * aₗ - aⱼ * bₗ| ≤ H := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (aⱼ * aₗ + bⱼ * bₗ), sq_nonneg (bⱼ + aₗ), sq_nonneg (aⱼ - bₗ),
        mul_nonneg hjn hln, hHpos]
    · nlinarith [sq_nonneg (aⱼ * aₗ + bⱼ * bₗ), sq_nonneg (bⱼ - aₗ), sq_nonneg (aⱼ + bₗ),
        mul_nonneg hjn hln, hHpos]
  rw [projImV, abs_div, abs_of_pos hHpos, div_le_one hHpos]
  exact hnum

/-! ### Line recovery on each chart -/

set_option linter.unusedSectionVars false in
/-- The diagonal real entry `projReV v i i = (Re vᵢ)² + (Im vᵢ)² / ‖v‖²` is nonzero when `vᵢ ≠ 0`. -/
private theorem projReV_diag_ne_zero {v : Fin (k + 1) → Ri R} (hv : v ≠ 0) {i : Fin (k + 1)}
    (hi : v i ≠ 0) : projReV v i i ≠ 0 := by
  have hHpos : (0 : R) < hermNormSq v := hermNormSq_pos hv
  have hN : (0 : R) < Ri.reL (v i) ^ 2 + Ri.imL (v i) ^ 2 := normSqC_pos hi
  rw [projReV]
  apply div_ne_zero
  · rw [← sq, ← sq]
    exact ne_of_gt hN
  · exact ne_of_gt hHpos

set_option linter.unusedSectionVars false in
/-- **Line recovery (real part).** On the chart `𝒰ᵢ` the real part of the recovered chart
coordinate `chartInv i x j` is the explicit ratio `projReV (succAbove j) i / projReV i i` of
projector entries of `momentMap x`. -/
theorem reL_chartInv_eq {i : Fin (k + 1)} {x : complexProjectiveSpace R k} (hi : x.rep i ≠ 0)
    (j : Fin k) :
    Ri.reL (chartInv i x j)
      = projReV x.rep (i.succAbove j) i / projReV x.rep i i := by
  have hHpos : (0 : R) < hermNormSq x.rep := hermNormSq_pos x.rep_nonzero
  have hHne : hermNormSq x.rep ≠ 0 := ne_of_gt hHpos
  set a := Ri.reL (x.rep (i.succAbove j)) with ha
  set b := Ri.imL (x.rep (i.succAbove j)) with hb
  set c := Ri.reL (x.rep i) with hc
  set d := Ri.imL (x.rep i) with hd
  have hN : (0 : R) < c * c + d * d := by
    have h := normSqC_pos hi
    nlinarith [h, sq_nonneg c, sq_nonneg d]
  have hNne : c * c + d * d ≠ 0 := ne_of_gt hN
  -- LHS
  rw [chartInv, div_eq_mul_inv, reL_mul, Ri.reL_inv _ hi, Ri.imL_inv _ hi]
  -- RHS
  rw [projReV, projReV]
  -- both sides now in terms of a,b,c,d,H
  rw [div_div_div_cancel_right₀ hHne]
  field_simp
  ring

set_option linter.unusedSectionVars false in
/-- **Line recovery (imaginary part).** On the chart `𝒰ᵢ` the imaginary part of the recovered chart
coordinate `chartInv i x j` is the explicit ratio `projImV (succAbove j) i / projReV i i` of
projector entries of `momentMap x`. -/
theorem imL_chartInv_eq {i : Fin (k + 1)} {x : complexProjectiveSpace R k} (hi : x.rep i ≠ 0)
    (j : Fin k) :
    Ri.imL (chartInv i x j)
      = projImV x.rep (i.succAbove j) i / projReV x.rep i i := by
  have hHpos : (0 : R) < hermNormSq x.rep := hermNormSq_pos x.rep_nonzero
  have hHne : hermNormSq x.rep ≠ 0 := ne_of_gt hHpos
  set a := Ri.reL (x.rep (i.succAbove j)) with ha
  set b := Ri.imL (x.rep (i.succAbove j)) with hb
  set c := Ri.reL (x.rep i) with hc
  set d := Ri.imL (x.rep i) with hd
  have hN : (0 : R) < c * c + d * d := by
    have h := normSqC_pos hi
    nlinarith [h, sq_nonneg c, sq_nonneg d]
  have hNne : c * c + d * d ≠ 0 := ne_of_gt hN
  rw [chartInv, div_eq_mul_inv, imL_mul, Ri.reL_inv _ hi, Ri.imL_inv _ hi]
  rw [projImV, projReV]
  rw [div_div_div_cancel_right₀ hHne]
  field_simp
  ring

/- NOTE. The convenience corollary `chartInv_eq_recover`, packaging the two recovery identities
into the single explicit complex form
`chartInv i x j = AdjoinRoot.of (X²+1) (projReV … / projReV i i)
  + AdjoinRoot.of (X²+1) (projImV … / projReV i i) · i`,
was deliberately omitted: writing the literal `AdjoinRoot.of (X^2+1)` constructor for `Ri R` in the
statement triggers the known `Ri R = AdjoinRoot (X^2+1)` `whnf` blow-up (timeout even at 1,000,000
heartbeats). The essential algebraic content — the per-component recovery formulas
`reL_chartInv_eq` / `imL_chartInv_eq` — is the explicit local inverse and is provided above. -/

end Azurite.BPR.Chapter4
