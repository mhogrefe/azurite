import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_28

/-!
# BPR Remark 4.29: `sDisc_i(P) ∈ D` for `P ∈ D[X]`

For a polynomial `P` over a domain `D` and any `i ≤ deg P`, the
subdiscriminant `sDisc_i(P)` lies in `D` (rather than just the
algebraic closure `C`).

In the Lean setup with `K` a field (the field of fractions of a
domain), this becomes: `sDisc (C := C) P i` lies in the image of
`algebraMap K C`.

## Proof

For `i = P.natDegree`, the formula gives `sDisc P p = 1` directly
(the unique sub-multiset of size `0` is the empty multiset; the
sign factor is `1`; the leading-coefficient factor is `a_p^0 = 1`).

For `0 ≤ i < P.natDegree` (i.e., `k := p - i ≥ 1`), Proposition 4.28
gives `a_p · sDisc P i = sRes P P' i`, so

  `sDisc P i = (algebraMap K C) (sRes P P' i / a_p)`,

with division well-defined in the field `K` since `a_p ≠ 0` (from
`0 < P.natDegree`).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- The `K`-valued subdiscriminant, defined via Proposition 4.28's
    identity `sDisc P i = sRes P P' i / a_p` for `i < P.natDegree`,
    extended by `1` at `i = P.natDegree` (matching the trivial
    convention `sDisc P p = 1`). -/
noncomputable def sDiscK (P : K[X]) (i : ℕ) : K :=
  if i < P.natDegree then sRes P P.derivative i / P.leadingCoeff
  else 1

/-- **BPR Remark 4.29.** For `P : K[X]` of positive degree and
    `i ≤ P.natDegree`, the subdiscriminant `sDisc P i` lies in the
    image of `algebraMap K C`. Explicit witness via `sDiscK`. -/
theorem Remark_4_29 (P : K[X]) (hP : 0 < P.natDegree) (i : ℕ)
    (hi : i ≤ P.natDegree) :
    (algebraMap K C) (sDiscK P i) = sDisc P i := by
  have hP_ne : P ≠ 0 := fun h => by rw [h] at hP; simp at hP
  have h_a_ne : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hP_ne
  have h_aroots : (P.aroots C).card = P.natDegree :=
    IsAlgClosed.card_aroots_eq_natDegree_of_isUnit_leadingCoeff
      h_a_ne.isUnit
  unfold sDiscK
  by_cases h_i : i < P.natDegree
  · rw [if_pos h_i, map_div₀]
    have h_prop28 := proposition_4_28 (C := C) P hP (P.natDegree - i)
      (by omega) (by omega)
    rw [show P.natDegree - (P.natDegree - i) = i from by omega] at h_prop28
    have h_alg_a_ne : (algebraMap K C) P.leadingCoeff ≠ 0 :=
      (map_ne_zero (algebraMap K C)).mpr h_a_ne
    field_simp
    linear_combination -h_prop28
  · rw [if_neg h_i]
    push Not at h_i
    have h_i_eq : i = P.natDegree := by omega
    subst h_i_eq
    unfold sDisc
    rw [h_aroots, Nat.sub_self]
    simp [Multiset.powersetCard_zero_left]

end Azurite.BPR.Chapter4
