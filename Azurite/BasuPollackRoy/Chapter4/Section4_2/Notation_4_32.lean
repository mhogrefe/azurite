import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_22

/-!
# BPR Notation 4.32: the subresultant sequence `sRes(P, Q)`

For two polynomials `P` of degree `p` and `Q` of degree `q < p`, BPR write
`sRes(P, Q)` for the sequence of signed subresultant coefficients
`sRes_j(P, Q)` for `j = p, …, 0`.

We formalize it as a `List D` ordered **high index first**, so the head is
`sRes_p(P, Q)` and the last entry is `sRes_0(P, Q)` — matching the convention of
`PmV` (Notation 4.31). The list has length `p + 1`, and its `k`-th entry is
`sRes_{p-k}(P, Q)`.

The definition is total in `P, Q` (the degree hypotheses are only needed for the
results about the sequence); `sRes` itself defaults to `0` outside its meaningful
range.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- **BPR Notation 4.32.** The subresultant sequence
`sRes(P, Q) = sRes_p(P, Q), …, sRes_0(P, Q)`, as a `List D` ordered with the
highest index `p = P.natDegree` first. -/
noncomputable def sResSeq (P Q : D[X]) : List D :=
  (List.range (P.natDegree + 1)).map (fun j => sRes P Q (P.natDegree - j))

@[simp] theorem sResSeq_length (P Q : D[X]) :
    (sResSeq P Q).length = P.natDegree + 1 := by
  simp [sResSeq]

/-- The `k`-th entry of `sRes(P, Q)` (from the head) is `sRes_{p-k}(P, Q)`. -/
theorem sResSeq_getElem (P Q : D[X]) (k : ℕ) (hk : k < P.natDegree + 1) :
    (sResSeq P Q)[k]'(by simpa using hk) = sRes P Q (P.natDegree - k) := by
  simp only [sResSeq, List.getElem_map, List.getElem_range]

/-- The head of `sRes(P, Q)` is `sRes_p(P, Q)`. -/
theorem sResSeq_head? (P Q : D[X]) :
    (sResSeq P Q).head? = some (sRes P Q P.natDegree) := by
  simp [sResSeq, List.range_succ_eq_map, List.head?_cons]

end Azurite.BPR.Chapter4
