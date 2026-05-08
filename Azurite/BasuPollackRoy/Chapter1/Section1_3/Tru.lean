import Azurite.BasuPollackRoy.Chapter1.Section1_3.Truncate
import Mathlib.Algebra.MvPolynomial.Basic

/-! # BPR Section 1.3 — Set of truncations `Tru(Q)`

BPR's **set of truncations** of a non-zero polynomial
`Q ∈ D[Y_1, …, Y_k][X]` is the finite subset of `D[Y_1, …, Y_k][X]`
defined recursively by

  Tru(Q) = {Q}                             if lcof(Q) ∈ D or deg_X(Q) = 0,
            {Q} ∪ Tru(Tru_{deg_X(Q)−1}(Q)) otherwise.

We extend to `Q = 0` by setting `Tru(0) = ∅`.

The recursion terminates because `natDegree (truncate (natDegree Q − 1) Q)`
is strictly less than `natDegree Q` whenever `natDegree Q > 0`.
-/

namespace Azurite.BPR

open Classical MvPolynomial Polynomial

variable {k : ℕ} {D : Type*} [CommRing D] [IsDomain D]

/-- BPR's **set of truncations** `Tru(Q)` for
`Q ∈ D[Y_1, …, Y_k][X]`. Returns the empty set when `Q = 0`;
`{Q}` when `lcof(Q) ∈ D` or `deg_X(Q) = 0`; and
`{Q} ∪ Tru(Tru_{deg_X(Q)-1}(Q))` otherwise. -/
noncomputable def Tru :
    Polynomial (MvPolynomial (Fin k) D) →
    Set (Polynomial (MvPolynomial (Fin k) D))
  | Q =>
    if Q = 0 then ∅
    else if (∃ d : D, Q.leadingCoeff = MvPolynomial.C d) ∨ Q.natDegree = 0 then
      {Q}
    else
      {Q} ∪ Tru (truncate (Q.natDegree - 1) Q)
termination_by Q => Q.natDegree
decreasing_by
  show (truncate (Q.natDegree - 1) Q).natDegree < Q.natDegree
  have hQpos : 0 < Q.natDegree := by
    rename_i _ hb
    push Not at hb
    exact Nat.pos_of_ne_zero hb.2
  have h := natDegree_truncate_le (Q.natDegree - 1) Q
  omega

end Azurite.BPR
