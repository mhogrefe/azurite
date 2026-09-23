import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # BPR Section 1.3 — Truncation `Tru_i(Q)`

BPR's **Notation 1.16**: for `Q = b_q X^q + ⋯ + b_0 ∈ D[X]` and
`0 ≤ i ≤ q`, the *truncation of `Q` at `i`* is

  Tru_i(Q) = b_i X^i + ⋯ + b_0,

obtained from `Q` by dropping all monomial terms of degree `> i`.
We extend the definition to arbitrary `i : ℕ` by the same formula;
when `i ≥ natDegree Q` the result coincides with `Q`.
-/

namespace Azurite.BPR

open Polynomial

/-- BPR's **truncation** `Tru_i(Q)` (Notation 1.16): for
`Q = b_q X^q + ⋯ + b_0 ∈ R[X]`, the polynomial obtained by
dropping every monomial term of degree `> i`. Concretely,
`Tru_i(Q) = b_i X^i + ⋯ + b_0`. Stated over an arbitrary semiring
`R`; BPR's original statement takes `R = D` a domain. -/
noncomputable def truncate {R : Type*} [Semiring R] (i : ℕ)
    (Q : Polynomial R) : Polynomial R :=
  ∑ j ∈ Finset.range (i + 1), Polynomial.monomial j (Q.coeff j)

/-- Coefficient characterization of `truncate`: the `j`-th coefficient
of `Tru_i(Q)` is `Q.coeff j` when `j ≤ i`, and `0` otherwise. -/
@[simp] theorem coeff_truncate {R : Type*} [Semiring R] (i : ℕ)
    (Q : Polynomial R) (j : ℕ) :
    (truncate i Q).coeff j = if j ≤ i then Q.coeff j else 0 := by
  rw [truncate, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
    Nat.lt_succ_iff]

/-- The `natDegree` of a truncation is at most `i`. -/
theorem natDegree_truncate_le {R : Type*} [Semiring R] (i : ℕ)
    (Q : Polynomial R) : (truncate i Q).natDegree ≤ i := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_truncate, ite_eq_right (Nat.not_le.mpr hj)]

end Azurite.BPR
