import Azurite.BasuPollackRoy.Chapter4.Section4_2.Theorem_4_33
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Remark_4_29
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Proposition_2_57

/-!
# BPR Theorem 4.34: subdiscriminants count the real roots

For `P` over a real closed field `R` (positive degree),
`PmV(sDisc_p(P), …, sDisc_0(P))` equals the number of distinct roots of `P` in
`R`.

The proof composes:

* Proposition 4.28 / Remark 4.29: `sRes_j(P, P') = a_p · sDisc_j(P)`, so the
  signed subresultant sequence of `(P, P')` is the subdiscriminant sequence scaled
  by the (nonzero) leading coefficient `a_p`. Since `PmV` is invariant under
  scaling every entry by a nonzero constant (`PmV_smul`), the two have equal `PmV`.
* Theorem 4.32: `PmV(sRes(P, P')) = Ind(P'/P)` (using `deg P' < deg P`).
* `Ind(P'/P) = #{distinct real roots}` (Corollary of Proposition 2.57 with `Q = 1`).
-/

namespace Azurite.BPR.Chapter4

-- The Chapter 2 import chain shadows `Polynomial`; use the root namespace so the
-- `R[X]` notation keeps working.
open _root_.Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The subdiscriminant sequence `sDisc_p(P), …, sDisc_0(P)` (high index first),
using the `K`-valued subdiscriminant `sDiscK` of Remark 4.29. -/
noncomputable def sDiscSeq (P : R[X]) : List R :=
  (List.range (P.natDegree + 1)).map (fun j => sDiscK P (P.natDegree - j))

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **Proposition 4.28, base-field form.** `sRes_i(P, P') = a_p · sDisc_i(P)` for
`i ≤ p`: for `i < p` this is the definition of `sDiscK`; at `i = p` both sides are
`a_p` (as `sRes_p(P, P') = a_p` and `sDiscK P p = 1`). -/
theorem sRes_eq_leadingCoeff_mul_sDiscK (P : R[X])
    (hdeg : P.derivative.natDegree < P.natDegree) {i : ℕ} (hi : i ≤ P.natDegree) :
    sRes P P.derivative i = P.leadingCoeff * sDiscK P i := by
  have ha : P.leadingCoeff ≠ 0 := by
    rw [Ne, Polynomial.leadingCoeff_eq_zero]
    rintro rfl; simp at hdeg
  rw [sDiscK]
  by_cases h : i < P.natDegree
  · rw [ite_eq_left h, ← mul_div_assoc, mul_div_cancel_left₀ _ ha]
  · rw [ite_eq_right h, mul_one]
    obtain rfl : i = P.natDegree := by omega
    rw [sRes, ite_eq_right (by omega), ite_eq_left hdeg, ite_eq_left rfl]

/-- **Core of Theorem 4.34.** `PmV(sRes(P, P')) = #{distinct roots}` over a real
closed field: `PmV(sRes(P,P')) = Ind(P'/P)` (Theorem 4.32) `= #roots`
(corollary of Proposition 2.57 with `Q = 1`). -/
theorem PmV_sResSeq_derivative_eq_card (P : R[X]) (hP : 0 < P.natDegree) :
    PmV (sResSeq P P.derivative) = (P.roots.toFinset.card : ℤ) := by
  classical
  have hPne : P ≠ 0 := fun h => by rw [h] at hP; simp at hP
  have hdeg : P.derivative.natDegree < P.natDegree :=
    Polynomial.natDegree_derivative_lt (by omega)
  have hP' : P.derivative ≠ 0 := fun h => by
    have := Polynomial.derivative_eq_zero.mp h; omega
  rw [theorem_4_32 P P.derivative hP' hdeg,
    cauchyIndex_eq_cauchyIndexOn_negInf_posInf,
    ← cauchyIndexOn_derivative_self_eq_card_roots_in_openInterval hasIVP_of_isRealClosed P hPne]
  norm_cast
  apply congrArg Finset.card
  apply Finset.filter_true_of_mem
  intro x _
  exact Set.mem_univ x

omit [IsRealClosed R] in
/-- `PmV(sDisc(P)) = PmV(sRes(P, P'))`: the subdiscriminant sequence scaled by the
nonzero leading coefficient is `sRes(P, P')`, and `PmV` is scale-invariant. -/
theorem PmV_sDiscSeq_eq_PmV_sResSeq (P : R[X]) (hP : 0 < P.natDegree) :
    PmV (sDiscSeq P) = PmV (sResSeq P P.derivative) := by
  have ha : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h] at hP; simp at hP)
  have hdeg : P.derivative.natDegree < P.natDegree :=
    Polynomial.natDegree_derivative_lt (by omega)
  have h_map : sResSeq P P.derivative = (sDiscSeq P).map (fun x => P.leadingCoeff * x) := by
    unfold sResSeq sDiscSeq
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp only [Function.comp_apply]
    exact sRes_eq_leadingCoeff_mul_sDiscK P hdeg (by omega)
  rw [h_map, PmV_smul ha]

/-- **BPR Theorem 4.34.** Over a real closed field, for `P` of positive degree,
`PmV(sDisc_p(P), …, sDisc_0(P))` is the number of distinct roots of `P`. -/
theorem theorem_4_34 (P : R[X]) (hP : 0 < P.natDegree) :
    PmV (sDiscSeq P) = (P.roots.toFinset.card : ℤ) := by
  rw [PmV_sDiscSeq_eq_PmV_sResSeq P hP, PmV_sResSeq_derivative_eq_card P hP]

/-- **BPR Theorem 4.34, `D[X]` version.** Over an ordered integral domain `D` with
a strictly monotone ring embedding `f : D →+* R` into a real closed field, for `P`
of positive degree and any `D`-valued subdiscriminant sequence `sd` — characterized
by `sRes(P, P') = sd.map (a_p · ·)` (the defining relation
`a_p · sDisc_j(P) = sRes_j(P, P')`, as in Proposition 4.28) — the `PmV` of `sd`
(computed in `D`) is the number of roots of `P` in `R`:
`PmV(sd) = #{roots of (map f P) in R}`. -/
theorem theorem_4_34_domain {D R : Type*}
    [CommRing D] [LinearOrder D] [IsStrictOrderedRing D]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {f : D →+* R} (hf : StrictMono f) (P : D[X]) (hP : 0 < P.natDegree) (sd : List D)
    (hsd : sResSeq P P.derivative = sd.map (fun x => P.leadingCoeff * x)) :
    PmV sd = ((P.map f).roots.toFinset.card : ℤ) := by
  have hfP : 0 < (P.map f).natDegree := by
    rwa [Polynomial.natDegree_map_eq_of_injective hf.injective]
  have ha : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h] at hP; simp at hP)
  have hfa : f P.leadingCoeff ≠ 0 := by
    rw [Ne, map_eq_zero_iff f hf.injective]; exact ha
  -- mapped relation over `R`: the subresultant sequence of `(map f P, (map f P)')`
  -- is `sd.map f` scaled by `f a_p`
  have hmapR : sResSeq (P.map f) (P.map f).derivative
      = (sd.map f).map (fun y => f P.leadingCoeff * y) := by
    rw [Polynomial.derivative_map, ← map_sResSeq hf.injective, hsd, List.map_map, List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply, map_mul]
  rw [← PmV_map hf sd, ← PmV_smul hfa (sd.map f), ← hmapR,
    PmV_sResSeq_derivative_eq_card (P.map f) hfP]

end Azurite.BPR.Chapter4
