import Azurite.AzPolynomial.CauchyIndex
import Azurite.AzPolynomial.Equiv.SignedSubresultant
import Azurite.AzPolynomial.Equiv.PRem
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Theorem_4_32
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Lemma_4_36
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Remark_2_55

/-!
# Correctness of `cauchyIndex` (BPR Algorithm 9.4)

`cauchyIndex Q P` (the signed-subresultant Cauchy index, Algorithm 9.4)
computes the Cauchy index `Ind(Q/P)` over a real closed coefficient field, for
every `Q` and every `P` of degree `≥ 1`. The correctness is BPR's cited "follows
from Theorem 4.32": `PmV(sRes(P, Q)) = Ind(Q/P)`.

* `cauchyIndex_eq_BPR_of_lt` — the case `deg Q < deg P` (no
  pseudo-remainder normalization), for *any* `Q` (zero, constant, or higher
  degree). This is where `PmV(sResSeq) = Ind` is applied via `theorem_4_32`; the
  `deg Q = 0` corner is handled by a direct signed-subresultant bridge
  (`snd_toList_deg0_sRes`), and `Q = 0` by `Ind(0/P) = 0`.
* `cauchyIndex_eq_BPR` — arbitrary `Q`, `deg P ≥ 1`. The
  `deg Q ≥ deg P` branch replaces `Q` by `pRem Q P`; the Cauchy index is
  preserved (`cauchyIndex_toPoly_pRem`) and the computation reduces to the
  `< deg P` case on `(pRem Q P, P)`.

Supporting reusable results:

* `Azurite.BPR.cauchyIndexOn_C_mul_left` — positive-scaling invariance of the
  Cauchy index in the numerator: `Ind((c·Q)/P) = Ind(Q/P)` for `0 < c`.
* `cauchyIndex_toPoly_pRem` — the signed pseudo-remainder preserves the Cauchy
  index: `Ind((pRem Q P)/P) = Ind(Q/P)`.

The statements are over a real closed field `R` (where `theorem_4_32` lives),
mirroring how `cauchyIndexOnSRem_eq_BPR` states the correctness of the
signed-remainder Cauchy index generically rather than at a fixed coefficient type.
-/

open Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Root multiplicity is unchanged by a nonzero constant factor. -/
theorem rootMultiplicity_C_mul (c : R) (hc : c ≠ 0) (Q : R[X]) (x : R) :
    (C c * Q).rootMultiplicity x = Q.rootMultiplicity x := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · simp
  · rw [rootMultiplicity_mul (mul_ne_zero (by simpa using hc) hQ0)]
    have : (C c).rootMultiplicity x = 0 := by rw [rootMultiplicity_eq_zero]; simp [IsRoot, hc]
    omega

/-- Multiplying by a positive constant does not change the one-sided sign. -/
theorem hasSignRight_C_mul (c : R) (hc : 0 < c) (F : R[X]) (x : R) (s : SignType) :
    HasSignRight (C c * F) x s ↔ HasSignRight F x s := by
  have hev : ∀ y, SignType.sign ((C c * F).eval y) = SignType.sign (F.eval y) := fun y => by
    rw [eval_mul, eval_C, sign_mul, sign_pos hc, one_mul]
  unfold HasSignRight
  constructor <;> rintro ⟨bb, h1, h2⟩ <;> exact ⟨bb, h1, fun y hy => by
    first | exact (hev y).symm.trans (h2 y hy) | exact (hev y).trans (h2 y hy)⟩

/-- The `−∞→+∞` jump predicate is invariant under a positive scaling of the numerator. -/
theorem jumpNegPos_C_mul (c : R) (hc : 0 < c) (Q P : R[X]) (x : R) :
    JumpsFromNegInfToPosInf (C c * Q) P x ↔ JumpsFromNegInfToPosInf Q P x := by
  unfold JumpsFromNegInfToPosInf
  rw [rootMultiplicity_C_mul c hc.ne' Q x, show (C c * Q) * P = C c * (Q * P) by ring,
    hasSignRight_C_mul c hc]

/-- The `+∞→−∞` jump predicate is invariant under a positive scaling of the numerator. -/
theorem jumpPosNeg_C_mul (c : R) (hc : 0 < c) (Q P : R[X]) (x : R) :
    JumpsFromPosInfToNegInf (C c * Q) P x ↔ JumpsFromPosInfToNegInf Q P x := by
  unfold JumpsFromPosInfToNegInf
  rw [rootMultiplicity_C_mul c hc.ne' Q x, show (C c * Q) * P = C c * (Q * P) by ring,
    hasSignRight_C_mul c hc]

/-- **Positive-scaling invariance of the Cauchy index** (numerator). For `0 < c`,
`Ind((c·Q)/P; a, b) = Ind(Q/P; a, b)`. -/
theorem cauchyIndexOn_C_mul_left (c : R) (hc : 0 < c) (Q P : R[X]) (a b : ExtendedPoint R) :
    cauchyIndexOn (C c * Q) P a b = cauchyIndexOn Q P a b := by
  classical
  unfold cauchyIndexOn
  have e1 := Finset.filter_congr (s := P.roots.toFinset)
    (p := fun x => x ∈ a.openInterval b ∧ JumpsFromNegInfToPosInf (C c * Q) P x)
    (q := fun x => x ∈ a.openInterval b ∧ JumpsFromNegInfToPosInf Q P x)
    (fun x _ => by rw [jumpNegPos_C_mul c hc])
  have e2 := Finset.filter_congr (s := P.roots.toFinset)
    (p := fun x => x ∈ a.openInterval b ∧ JumpsFromPosInfToNegInf (C c * Q) P x)
    (q := fun x => x ∈ a.openInterval b ∧ JumpsFromPosInfToNegInf Q P x)
    (fun x _ => by rw [jumpPosNeg_C_mul c hc])
  simp only [e1, e2]

end Azurite.BPR

namespace Azurite.AzPolynomial

open Azurite.BPR.Chapter4 (PmV sResSeq sRes theorem_4_32 ε sRes_q_eq sRes_eq_zero_of_gap)

section Deg0

-- The `deg Q = 0` corner of the signed subresultant is a pure computation: it
-- needs no field structure (or order), only a nontrivial commutative ring with
-- exact division. Stated at that generality so the ordered-domain transport
-- (`Equiv.CauchyIndexSubresMap`) can reuse it, e.g. over `AzInt`.
variable {R : Type _} [CommRing R] [Nontrivial R] [DecidableEq R] [Azurite.ExactDiv R]

omit [DecidableEq R] in
/-- Exact division by `1` is the identity. -/
theorem exactDiv_one' (x : R) :
    Azurite.ExactDiv.exactDiv x 1 = x := by
  have := Azurite.ExactDiv.exactDiv_mul_self x 1 (one_dvd x) one_ne_zero; rwa [mul_one] at this

/-- **`signedSubresultant` for a constant `Q` (`deg Q = 0`).** The explicit
coefficient array is `[ε_p·lcof(Q)^p, 0, …, 0, lcof(P)]`. Proved by a single
unfolding of `ssAux` (which terminates in one step for `deg Q = 0`). -/
theorem snd_toList_deg0 (P Q : AzPolynomial R) (hQ : Q ≠ 0) (hq0 : Q.natDegree = 0)
    (hp : 1 ≤ P.natDegree) :
    (signedSubresultant P Q).2.toList
      = Azurite.ExactDiv.exactDiv (epsilonSign P.natDegree * Q.leadingCoeff ^ P.natDegree)
          ((1 : R) ^ (P.natDegree - 1)) :: List.replicate (P.natDegree - 1) 0 ++ [P.leadingCoeff] := by
  have hcond : ¬ (Q = 0 ∨ P.natDegree ≤ Q.natDegree) := not_or.mpr ⟨hQ, by omega⟩
  rw [signedSubresultant, ite_eq_right hcond]
  simp only [List.map_reverse, List.map_cons]
  rcases Nat.lt_or_ge 1 P.natDegree with hp2 | hp1
  · have hss : ssAux (P.natDegree + 1) P.natDegree P Q 1 1
        = (Q, (0 : R)) :: (List.replicate (P.natDegree - 2) ((0 : AzPolynomial R), (0 : R))
            ++ [(divByRingElt Q.leadingCoeff
                  (Azurite.ExactDiv.exactDiv (epsilonSign P.natDegree * Q.leadingCoeff ^ P.natDegree)
                    ((1 : R) ^ (P.natDegree - 1)) • Q),
                 Azurite.ExactDiv.exactDiv (epsilonSign P.natDegree * Q.leadingCoeff ^ P.natDegree)
                   ((1 : R) ^ (P.natDegree - 1)))]) := by
      conv_lhs => rw [ssAux]
      rw [ite_eq_right hQ]; simp only [hq0, Nat.sub_zero]
      rw [ite_eq_right (by omega : ¬ (0 = P.natDegree - 1)), ite_true]
    rw [hss]
    simp only [List.map_cons, List.map_append, List.map_replicate, List.reverse_cons,
      List.reverse_append, List.reverse_replicate, List.map_nil, List.reverse_nil, List.nil_append]
    rw [show P.natDegree - 1 = (P.natDegree - 2) + 1 from by omega, List.replicate_succ']
    simp
  · have hp1' : P.natDegree = 1 := by omega
    have hss : ssAux (P.natDegree + 1) P.natDegree P Q 1 1 = [(Q, Q.leadingCoeff)] := by
      conv_lhs => rw [ssAux]; rw [ite_eq_right hQ]; simp only [hq0, hp1']; norm_num
    rw [hss, hp1']
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append]
    have he1 : (epsilonSign 1 : R) = 1 := by rw [epsilonSign_eq]; norm_num
    have : Azurite.ExactDiv.exactDiv (epsilonSign 1 * Q.leadingCoeff ^ 1) ((1 : R) ^ (1 - 1))
        = Q.leadingCoeff := by
      rw [he1, one_mul, pow_one, one_pow, exactDiv_one']
    rw [this]; simp

end Deg0

variable {R : Type _} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]
    [Azurite.ExactDiv R]

/-- **Signed-subresultant `.2` bridge for a constant `Q` (`deg Q = 0`).** Matches
the computed coefficients to the abstract signed subresultant coefficients `sRes`,
the missing `deg Q = 0` case of `signedSubresultant_toPoly_domain`. -/
theorem snd_toList_deg0_sRes (P Q : AzPolynomial R) (hQ : Q ≠ 0)
    (hq0 : Q.natDegree = 0) (hp : 1 ≤ P.natDegree) :
    (signedSubresultant P Q).2.toList
      = (List.range (P.natDegree + 1)).map (sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) := by
  have hQm : AzPolynomial.toPoly Q ≠ 0 := fun h => hQ (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hpd : (AzPolynomial.toPoly P).natDegree = P.natDegree := AzPolynomial.natDegree_toPoly P
  have hqd0 : (AzPolynomial.toPoly Q).natDegree = 0 := by rw [AzPolynomial.natDegree_toPoly, hq0]
  have hqpm : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
    rw [hpd, hqd0]; omega
  have hs0 : sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) 0
      = Azurite.ExactDiv.exactDiv (epsilonSign P.natDegree * Q.leadingCoeff ^ P.natDegree)
          ((1 : R) ^ (P.natDegree - 1)) := by
    have h := sRes_q_eq (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hQm hqpm
    rw [hqd0] at h
    rw [h, one_pow, exactDiv_one', hpd, Nat.sub_zero, epsilonSign_eq, leadingCoeff_toPoly]
    simp only [ε]; push_cast; ring
  have hsp : sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) P.natDegree = P.leadingCoeff := by
    rw [← hpd, sRes, ite_eq_right (by omega), ite_eq_left hqpm, ite_eq_left rfl, leadingCoeff_toPoly]
  rw [snd_toList_deg0 P Q hQ hq0 hp]
  apply List.ext_getElem
  · simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil,
      List.length_map, List.length_range]; omega
  · intro m hm1 _
    simp only [List.length_append, List.length_cons, List.length_replicate, List.length_nil] at hm1
    simp only [List.getElem_map, List.getElem_range]
    rcases Nat.lt_or_ge m P.natDegree with hmlt | hmge
    · rw [List.getElem_append_left (by simp only [List.length_cons, List.length_replicate]; omega)]
      match m with
      | 0 => simpa using hs0.symm
      | (i + 1) =>
        rw [List.getElem_cons_succ, List.getElem_replicate,
          sRes_eq_zero_of_gap _ _ (by rw [hqd0]; omega) (by rw [hpd]; omega)]
    · have hmp : m = P.natDegree := by omega
      subst hmp
      rw [List.getElem_append_right (by simp only [List.length_cons, List.length_replicate]; omega)]
      simp only [List.getElem_singleton]
      exact hsp.symm

variable [IsRealClosed R]

omit [Azurite.ExactDiv R] in
/-- **The signed pseudo-remainder preserves the Cauchy index.**
`Ind((pRem Q P)/P) = Ind(Q/P)` over a real closed field, for `P ≠ 0`. Since
`pRem Q P = C(lcof(P)^d)·Q − A·P` with `d` even (so `lcof(P)^d > 0`), the two
numerators are congruent modulo `P` up to a positive scalar, and both the `% P`
invariance (`remark_2_55_b`) and positive-scaling invariance
(`cauchyIndexOn_C_mul_left`) leave the Cauchy index fixed. -/
theorem cauchyIndex_toPoly_pRem (Q P : AzPolynomial R) (hP : P ≠ 0) :
    Azurite.BPR.cauchyIndex (AzPolynomial.toPoly (pRem Q P)) (AzPolynomial.toPoly P)
      = Azurite.BPR.cauchyIndex (AzPolynomial.toPoly Q) (AzPolynomial.toPoly P) := by
  have hPm : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
  obtain ⟨A, hA⟩ := toPoly_pRem_div_eq Q P hPm
  set c := P.leadingCoeff ^ Azurite.BPR.pRemExp (AzPolynomial.toPoly Q) (AzPolynomial.toPoly P)
    with hc
  have hlc : P.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly]; exact Polynomial.leadingCoeff_ne_zero.mpr hPm
  have hcpos : 0 < c := Even.pow_pos (Azurite.BPR.pRemExp_even _ _) hlc
  have hIVP : Azurite.BPR.HasIntermediateValueProperty R := Azurite.BPR.hasIVP_of_isRealClosed
  have hdeg : (AzPolynomial.toPoly (pRem Q P)).degree < (AzPolynomial.toPoly P).degree :=
    degree_toPoly_pRem_lt Q P hPm
  have hmod : (Polynomial.C c * AzPolynomial.toPoly Q) % AzPolynomial.toPoly P
      = AzPolynomial.toPoly (pRem Q P) := by
    rw [hA, mod_eq_of_dvd_sub (show AzPolynomial.toPoly P ∣
          ((A * AzPolynomial.toPoly P + AzPolynomial.toPoly (pRem Q P))
            - AzPolynomial.toPoly (pRem Q P)) from by
        rw [add_sub_cancel_right]; exact dvd_mul_left _ _),
      (Polynomial.mod_eq_self_iff hPm).mpr hdeg]
  rw [Azurite.BPR.cauchyIndex_eq_cauchyIndexOn_negInf_posInf,
      Azurite.BPR.cauchyIndex_eq_cauchyIndexOn_negInf_posInf,
      ← Azurite.BPR.cauchyIndexOn_C_mul_left c hcpos (AzPolynomial.toPoly Q),
      ← Azurite.BPR.remark_2_55_b hIVP (Polynomial.C c * AzPolynomial.toPoly Q)
          (AzPolynomial.toPoly P) .negInf .posInf hPm,
      hmod]

/-- **Correctness of `cauchyIndex`, `deg Q < deg P`.** For any `Q` (zero,
constant, or higher degree) with `deg Q < deg P` over a real closed coefficient
field, `cauchyIndex Q P = Ind(Q/P)`. No pseudo-remainder normalization
happens, and `PmV(sResSeq) = Ind` (Theorem 4.32). -/
theorem cauchyIndex_eq_BPR_of_lt (Q P : AzPolynomial R)
    (hlt : Q.natDegree < P.natDegree) :
    cauchyIndex Q P
      = Azurite.BPR.cauchyIndex (AzPolynomial.toPoly Q) (AzPolynomial.toPoly P) := by
  have hP : P ≠ 0 := by
    rintro rfl; rw [show (0 : AzPolynomial R).natDegree = 0 from rfl] at hlt; omega
  have hexpand : cauchyIndex Q P = PmV (signedSubresultant P Q).2.toList.reverse := by
    show PmV (signedSubresultant P
      (if P.natDegree ≤ Q.natDegree then pRem Q P else Q)).2.toList.reverse = _
    rw [ite_eq_right (by omega)]
  rcases eq_or_ne Q 0 with rfl | hQ
  · rw [hexpand, signedSubresultant, ite_eq_left (Or.inl rfl), toPoly_zero,
      Azurite.BPR.cauchyIndex_eq_cauchyIndexOn_negInf_posInf, Azurite.BPR.cauchyIndexOn_zero_left]
    simp [Azurite.BPR.Chapter4.PmV_nil]
  · have hQm : AzPolynomial.toPoly Q ≠ 0 := fun h => hQ (toPoly_inj.mp (h.trans toPoly_zero.symm))
    have hpd : (AzPolynomial.toPoly P).natDegree = P.natDegree := AzPolynomial.natDegree_toPoly P
    have hqd : (AzPolynomial.toPoly Q).natDegree = Q.natDegree := AzPolynomial.natDegree_toPoly Q
    have hqpm : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
      rw [hpd, hqd]; exact hlt
    have h2 : (signedSubresultant P Q).2.toList
        = (List.range (P.natDegree + 1)).map (sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) := by
      rcases Nat.eq_zero_or_pos Q.natDegree with hq0 | hq1
      · exact snd_toList_deg0_sRes P Q hQ hq0 (by omega)
      · exact (signedSubresultant_toPoly_domain P Q hP hQ hlt hq1).2
    have hlist : (signedSubresultant P Q).2.toList.reverse
        = sResSeq (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
      rw [h2, sResSeq]
      apply List.ext_getElem
      · simp only [List.length_reverse, List.length_map, List.length_range, hpd]
      · intro k hk1 hk2
        simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map,
          List.length_range]
        congr 1
        omega
    rw [hexpand, hlist]
    exact theorem_4_32 (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hQm hqpm

/-- **Correctness of `cauchyIndex` (BPR Algorithm 9.4), general form.** For
*any* `Q` and `P` over a real closed coefficient field,
`cauchyIndex Q P = Ind(Q/P)` — no degree hypothesis. When `deg P = 0` both
sides are `0` (`P` has no poles, and the pseudo-remainder step collapses the
subresultant list to empty). When `deg P ≥ 1`, the `deg Q ≥ deg P` branch replaces
`Q` by `pRem Q P` (Cauchy index preserved), reducing to the `deg < deg P` case. -/
theorem cauchyIndex_eq_BPR (Q P : AzPolynomial R) :
    cauchyIndex Q P
      = Azurite.BPR.cauchyIndex (AzPolynomial.toPoly Q) (AzPolynomial.toPoly P) := by
  rcases Nat.eq_zero_or_pos P.natDegree with hP0 | hP1
  · -- `deg P = 0`: `P` is constant (or zero), so both sides are `0`.
    have hLHS : cauchyIndex Q P = 0 := by
      show PmV (signedSubresultant P
        (if P.natDegree ≤ Q.natDegree then pRem Q P else Q)).2.toList.reverse = 0
      rw [signedSubresultant, ite_eq_left (Or.inr (by rw [hP0]; exact Nat.zero_le _))]
      simp [Azurite.BPR.Chapter4.PmV_nil]
    have hroots : (AzPolynomial.toPoly P).roots = 0 := by
      obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp
        (show (AzPolynomial.toPoly P).natDegree = 0 by rw [AzPolynomial.natDegree_toPoly]; exact hP0)
      rw [← ha, Polynomial.roots_C]
    rw [hLHS, Azurite.BPR.cauchyIndex_eq_cauchyIndexOn_negInf_posInf]
    unfold Azurite.BPR.cauchyIndexOn
    simp [hroots]
  rcases Nat.lt_or_ge Q.natDegree P.natDegree with hlt | hge
  · exact cauchyIndex_eq_BPR_of_lt Q P hlt
  · have hP : P ≠ 0 := by
      rintro rfl; rw [show (0 : AzPolynomial R).natDegree = 0 from rfl] at hP1; omega
    have hPm : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
    have hprlt : (pRem Q P).natDegree < P.natDegree := by
      rcases eq_or_ne (pRem Q P) 0 with h0 | hne
      · rw [h0, show (0 : AzPolynomial R).natDegree = 0 from rfl]; omega
      · have hprm : AzPolynomial.toPoly (pRem Q P) ≠ 0 :=
          fun h => hne (toPoly_inj.mp (h.trans toPoly_zero.symm))
        have := Polynomial.natDegree_lt_natDegree hprm (degree_toPoly_pRem_lt Q P hPm)
        rwa [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly] at this
    have hstep : cauchyIndex Q P = cauchyIndex (pRem Q P) P := by
      show PmV (signedSubresultant P
          (if P.natDegree ≤ Q.natDegree then pRem Q P else Q)).2.toList.reverse
        = PmV (signedSubresultant P
          (if P.natDegree ≤ (pRem Q P).natDegree then pRem (pRem Q P) P
            else pRem Q P)).2.toList.reverse
      rw [ite_eq_left hge, ite_eq_right (by omega)]
    rw [hstep, cauchyIndex_eq_BPR_of_lt (pRem Q P) P hprlt,
      cauchyIndex_toPoly_pRem Q P hP]

/-- **`ofPoly` form.** For abstract polynomials `q, p : R[X]`, the
signed-subresultant Cauchy index of their `ofPoly` images equals `Ind(q/p)`. -/
theorem cauchyIndex_ofPoly_eq_BPR (q p : R[X]) :
    cauchyIndex (AzPolynomial.ofPoly q) (AzPolynomial.ofPoly p)
      = Azurite.BPR.cauchyIndex q p := by
  rw [cauchyIndex_eq_BPR, toPoly_ofPoly, toPoly_ofPoly]

end Azurite.AzPolynomial
