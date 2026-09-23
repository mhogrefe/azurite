import Azurite.AzPolynomial.Equiv.Gcd
import Azurite.AzPolynomial.Equiv.SignedSubresultant
import Azurite.BasuPollackRoy.Chapter10.Section10_1.Proposition_10_14

/-!
# Boundary cofactors of `extendedSignedSubresultant` (BPR Algorithm 8.22)

`ssAuxExt_spec_domain` identifies the cofactor outputs of Algorithm 8.22 with the abstract
`sResU`/`sResV` determinants at every *non-defective* index (`s_ℓ ≠ 0`).  That guard excludes
the **boundary** tuple — the index `j₀ - 1` just below the gcd degree
`j₀ = deg(gcd P Q)`, where `sResP_{j₀-1} = 0` and `s_{j₀-1} = 0` but the emitted cofactors
`sResU_{j₀-1}, sResV_{j₀-1}` are the genuinely interesting ones: `sResV_{j₀-1}` is the
gcd-free part of `P` with respect to `Q` (Proposition 10.14, consumed by Algorithm 10.1).

This file exports that boundary identification positionally.  The key observations:

* the recursion of `ssAuxExt` terminates in the `Sj = 0` branch exactly when its carried
  index `j` satisfies `sResP_{j-1} = 0` with `sResP_j` non-defective, which by the chain
  criterion `sResP_pred_eq_zero_iff` (Theorem 8.34's gcd branch) forces `j = j₀` — so the
  head `(0, 0, Uj, Vj)` of the terminal zero-fill carries exactly `sResU_{j₀-1}, sResV_{j₀-1}`;
* the loop invariant pins each emitted tuple to its position (the output list of the call at
  index `j` has length `j`, descending), so the boundary tuple sits at ascending index `j₀ - 1`
  of the public output arrays.

The development runs over an integral domain `D` (so it applies to the `AzInt` run of the
algorithm): the boundary index `j₀` is characterized by the domain-transferable package
`sResP_{j₀-1} = 0` plus `sResP_{j₀}` nonzero non-defective, which pins `j₀` down as the
fraction-field gcd degree (`fractionGcd_natDegree_eq`, via `sResP_map` along the injective
`algebraMap D (FractionRing D)`).  Over a field the package is derivable from
`deg(gcd P Q) = j₀` (Theorem 8.34's gcd branch), giving the field corollaries.

Main results:

* `ssAuxExt_boundary` — the strengthened loop induction (domain): length of the output plus
  the positional identification of the boundary tuple at descending position `j - j₀`;
* `ssAuxExt_boundary_first` — the same for the top-level call (`i = p + 1`), peeling the
  first step exactly as `ssAuxExt_bezout_first_domain` does;
* `extendedSignedSubresultant_boundary_cofactors_domain` — array-level (domain): at output
  index `j₀ - 1`, the `sResU`/`sResV` output arrays of `extendedSignedSubresultant` are
  (after `toPoly`) the abstract `sResU (j₀-1)` and `sResV (j₀-1)`;
* `extendedSignedSubresultant_boundary_domain` /
  `extendedSignedSubresultant_boundary_sResU_domain` — the two components separately;
* `extendedSignedSubresultant_boundary_cofactors`, `extendedSignedSubresultant_boundary`,
  `extendedSignedSubresultant_boundary_sResU` — the field versions, with the boundary
  package replaced by the gcd-degree hypothesis `deg(gcd P Q) = j₀`.

`gcd` is the house instance `Azurite.BPR.gcdMonoidPolynomial` throughout (written with an
explicit `@` so that no ambient instance can shadow it).
-/

namespace Azurite.AzPolynomial

open Polynomial

/-! ### Fraction-field transfer of the boundary index

Over an integral domain `D` the gcd of `P, Q ∈ D[X]` is not available, so the boundary index
`j₀` is characterized instead by the domain-transferable package

* `sResP P Q (j₀ - 1) = 0`, and
* `sResP P Q j₀` nonzero and non-defective (`natDegree = j₀`),

which pins `j₀` down as the fraction-field gcd degree: all three facts transfer along the
injective `algebraMap D (FractionRing D)` via `sResP_map`, where the field-level chain
criterion `sResP_pred_eq_zero_iff` applies. -/

open Azurite.BPR.Chapter8 in
/-- The domain-transferable boundary package identifies `j₀` as the **fraction-field gcd
    degree**: mapping along `algebraMap D (FractionRing D)` (injective) preserves all three
    facts, and `sResP_pred_eq_zero_iff` reads the gcd degree off them. -/
private theorem fractionGcd_natDegree_eq {D : Type _} [CommRing D] [IsDomain D]
    (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀) (hj₀q : j₀ ≤ Q.natDegree)
    (h0 : sResP P Q (j₀ - 1) = 0) (hnd : (sResP P Q j₀).natDegree = j₀)
    (hne : sResP P Q j₀ ≠ 0) :
    (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
        (P.map (algebraMap D (FractionRing D)))
        (Q.map (algebraMap D (FractionRing D)))).natDegree = j₀ := by
  have hf : Function.Injective (algebraMap D (FractionRing D)) :=
    IsFractionRing.injective D (FractionRing D)
  have hPK : P.map (algebraMap D (FractionRing D)) ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hP
  have hQK : Q.map (algebraMap D (FractionRing D)) ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hQ
  have hqdeg : (Q.map (algebraMap D (FractionRing D))).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf Q
  have hpqK : (Q.map (algebraMap D (FractionRing D))).natDegree
      < (P.map (algebraMap D (FractionRing D))).natDegree := by
    rw [hqdeg, Polynomial.natDegree_map_eq_of_injective hf P]; exact hpq
  have hsResK : Azurite.BPR.Chapter4.sRes (P.map (algebraMap D (FractionRing D)))
      (Q.map (algebraMap D (FractionRing D))) j₀ ≠ 0 := by
    refine (isNonDefective_iff_sRes_ne_zero _ _ hpqK (by rw [hqdeg]; exact hj₀q)).mp ?_
    rw [IsNonDefective, sResP_map hf,
      Polynomial.degree_eq_natDegree ((Polynomial.map_ne_zero_iff hf).mpr hne),
      Polynomial.natDegree_map_eq_of_injective hf, hnd]
  have hzeroK : sResP (P.map (algebraMap D (FractionRing D)))
      (Q.map (algebraMap D (FractionRing D))) (j₀ - 1) = 0 := by
    rw [sResP_map hf, h0, Polynomial.map_zero]
  exact (sResP_pred_eq_zero_iff _ _ hPK hQK hpqK hj₀1 (by rw [hqdeg]; exact hj₀q) hsResK).mp
    hzeroK

open Azurite.BPR.Chapter8 in
/-- **Uniqueness of the boundary index** over a domain: if the boundary package holds at `j₀`
    and the loop's terminal facts hold at `j` (`sResP_{j-1} = 0`, `sResP_j` non-defective),
    then `j = j₀`.  Both indices read off the same fraction-field gcd degree. -/
private theorem boundary_index_unique {D : Type _} [CommRing D] [IsDomain D]
    (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀) (hj₀q : j₀ ≤ Q.natDegree)
    (h0 : sResP P Q (j₀ - 1) = 0) (hnd : (sResP P Q j₀).natDegree = j₀)
    (hne : sResP P Q j₀ ≠ 0) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ Q.natDegree)
    (hzero : sResP P Q (j - 1) = 0) (hjnd : (sResP P Q j).natDegree = j) :
    j = j₀ := by
  have hjne : sResP P Q j ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hjnd; omega
  have h1 := fractionGcd_natDegree_eq P Q hP hQ hpq hj1 hjq hzero hjnd hjne
  have h2 := fractionGcd_natDegree_eq P Q hP hQ hpq hj₀1 hj₀q h0 hnd hne
  exact h1.symm.trans h2

open Azurite.BPR.Chapter8 in
/-- **Lower bound from the boundary index** over a domain: every nonzero signed subresultant
    has degree at least `j₀`.  Transfer of `natDegree_gcd_le_natDegree_sResP` through the
    fraction field, with the gcd degree read off the boundary package. -/
private theorem boundary_le_natDegree_sResP {D : Type _} [CommRing D] [IsDomain D]
    (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀) (hj₀q : j₀ ≤ Q.natDegree)
    (h0 : sResP P Q (j₀ - 1) = 0) (hnd : (sResP P Q j₀).natDegree = j₀)
    (hne : sResP P Q j₀ ≠ 0) {m : ℕ} (hm : sResP P Q m ≠ 0) :
    j₀ ≤ (sResP P Q m).natDegree := by
  have hf : Function.Injective (algebraMap D (FractionRing D)) :=
    IsFractionRing.injective D (FractionRing D)
  have hPK : P.map (algebraMap D (FractionRing D)) ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hP
  have hQK : Q.map (algebraMap D (FractionRing D)) ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hQ
  have hpqK : (Q.map (algebraMap D (FractionRing D))).natDegree
      < (P.map (algebraMap D (FractionRing D))).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hf Q,
      Polynomial.natDegree_map_eq_of_injective hf P]
    exact hpq
  have hle := natDegree_gcd_le_natDegree_sResP (P.map (algebraMap D (FractionRing D)))
    (Q.map (algebraMap D (FractionRing D))) hPK hQK hpqK (m := m)
    (by rw [sResP_map hf]; exact (Polynomial.map_ne_zero_iff hf).mpr hm)
  rw [fractionGcd_natDegree_eq P Q hP hQ hpq hj₀1 hj₀q h0 hnd hne, sResP_map hf,
    Polynomial.natDegree_map_eq_of_injective hf] at hle
  exact hle

open Azurite.BPR.Chapter8 in
/-- **Boundary-cofactor loop induction for Algorithm 8.22** (`j ≤ q`, over an integral
    domain).  Under the same invariant package as `ssAuxExt_spec_domain`, the output list of
    `ssAuxExt` at carried index `j` has length `j`, and the tuple at (descending) position
    `j - j₀` — ascending index `j₀ - 1`, where `j₀ ≥ 1` carries the domain-transferable
    boundary package (`sResP_{j₀-1} = 0`, `sResP_{j₀}` nonzero non-defective; over a field
    this says `j₀ = deg(gcd P Q)`) — carries the boundary cofactors:
    `toPoly` of its `U`/`V` components is `sResU P Q (j₀ - 1)` / `sResV P Q (j₀ - 1)`.

    The interesting case is the terminal `Sj = 0` branch: there `sResP_{j-1} = 0` with `sResP_j`
    non-defective, which forces `j = j₀` (`boundary_index_unique`, the fraction-field transfer
    of the chain criterion `sResP_pred_eq_zero_iff`), and the head `(0, 0, Uj, Vj)` of the
    zero-fill is the boundary tuple (its identifications are the carried invariants
    `hUj`/`hVj`).  All other branches have `sResP_{j-1} ≠ 0`, so `j₀ ≤ deg(sResP_{j-1})`
    (`boundary_le_natDegree_sResP`: the fraction-field gcd divides every nonzero subresultant)
    and the boundary position lands strictly inside the recursive call. -/
theorem ssAuxExt_boundary {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (hq1 : 1 ≤ Q.natDegree) {j₀ : ℕ} (hj₀1 : 1 ≤ j₀) (hj₀q : j₀ ≤ Q.natDegree)
    (h0 : sResP P Q (j₀ - 1) = 0) (hnd : (sResP P Q j₀).natDegree = j₀)
    (hne0 : sResP P Q j₀ ≠ 0) :
    ∀ (fuel i j : ℕ) (Si Sj : AzPolynomial D) (sj ti : D) (Ui Vi Uj Vj : AzPolynomial D),
      j ≤ fuel → 1 ≤ j → j < i → j ≤ Q.natDegree → (i ≤ Q.natDegree + 1 ∨ i = P.natDegree) →
      AzPolynomial.toPoly Si = sResP P Q (i - 1) → AzPolynomial.toPoly Sj = sResP P Q (j - 1) →
      (sResP P Q (i - 1)).natDegree = j → (sResP P Q j).natDegree = j →
      sj = Azurite.BPR.Chapter4.sRes P Q j → ti = (sResP P Q (i - 1)).leadingCoeff →
      AzPolynomial.toPoly Uj = sResU P Q (j - 1) → AzPolynomial.toPoly Vj = sResV P Q (j - 1) →
      ((i ≤ Q.natDegree + 1 ∧ AzPolynomial.toPoly Ui = sResU P Q (i - 1)
          ∧ AzPolynomial.toPoly Vi = sResV P Q (i - 1))
        ∨ (i = P.natDegree ∧ AzPolynomial.toPoly Ui = 0 ∧ AzPolynomial.toPoly Vi = 1)) →
      (ssAuxExt fuel j Si Sj sj ti Ui Vi Uj Vj).length = j
      ∧ ∃ t, (ssAuxExt fuel j Si Sj sj ti Ui Vi Uj Vj)[j - j₀]? = some t
          ∧ AzPolynomial.toPoly t.2.2.1 = sResU P Q (j₀ - 1)
          ∧ AzPolynomial.toPoly t.2.2.2 = sResV P Q (j₀ - 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i j Si Sj sj ti Ui Vi Uj Vj hfuel hj1 _ _ _ _ _ _ _ _ _ _ _ _
    exact (by omega : False).elim
  | succ f ih =>
    intro i j Si Sj sj ti Ui Vi Uj Vj hfuel hj1 hji hjq hicase hSi hSj hdeg hjnd hsj hti hUj hVj hUVi
    have hip : i ≤ P.natDegree + 1 := by rcases hicase with h | h <;> omega
    have hne : sResP P Q (i - 1) ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
    have htine : ti ≠ 0 := by rw [hti]; exact Polynomial.leadingCoeff_ne_zero.mpr hne
    have hsResP_j_ne : sResP P Q j ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hjnd; omega
    have hsjne : sj ≠ 0 := by
      rw [hsj]; exact (isNonDefective_iff_sRes_ne_zero P Q hpq hjq).mp
        (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsResP_j_ne, hjnd])
    rw [ssAuxExt]
    by_cases hSj0 : Sj = 0
    · -- terminal branch: `sResP_{j-1} = 0` forces `j = j₀`; the head carries the boundary cofactors
      have hzero : sResP P Q (j - 1) = 0 := by rw [← hSj, hSj0, toPoly_zero]
      have hj₀j : j₀ = j :=
        (boundary_index_unique P Q hP hQ hpq hj₀1 hj₀q h0 hnd hne0 hj1 hjq hzero hjnd).symm
      rw [ite_eq_left hSj0, ite_eq_right (show ¬j = 0 by omega)]
      refine ⟨by rw [List.length_cons, List.length_replicate]; omega, (0, 0, Uj, Vj), ?_, ?_, ?_⟩
      · rw [show j - j₀ = 0 from by omega, List.getElem?_cons_zero]
      · rw [show j₀ - 1 = j - 1 from by omega]; exact hUj
      · rw [show j₀ - 1 = j - 1 from by omega]; exact hVj
    · rw [ite_eq_right hSj0]
      have hkdeg : (sResP P Q (j - 1)).natDegree = Sj.natDegree := by
        rw [← hSj, AzPolynomial.natDegree_toPoly]
      have hsResPne : sResP P Q (j - 1) ≠ 0 := by
        rw [← hSj]; intro h; exact hSj0 (toPoly_inj.mp (h.trans toPoly_zero.symm))
      have htj : Sj.leadingCoeff = (sResP P Q (j - 1)).leadingCoeff := by
        rw [← hSj, leadingCoeff_toPoly]
      have htjne : Sj.leadingCoeff ≠ 0 := by
        rw [htj]; exact Polynomial.leadingCoeff_ne_zero.mpr hsResPne
      -- the boundary index `j₀` sits at or below `deg(sResP_{j-1}) = deg Sj`
      have hj₀k : j₀ ≤ Sj.natDegree := by
        have h := boundary_le_natDegree_sResP P Q hP hQ hpq hj₀1 hj₀q h0 hnd hne0 hsResPne
        rw [hkdeg] at h
        exact h
      -- the `i = p` boundary facts (used by the `_ip` cofactor bridges)
      have hbdry : i = P.natDegree → AzPolynomial.toPoly Si = Q ∧ j = Q.natDegree := by
        intro hip2
        have hQeq : sResP P Q (i - 1) = Q := by
          rw [show i - 1 = P.natDegree - 1 from by omega]; exact sResP_pm1_eq_Q_domain P Q hQ hpq
        exact ⟨hSi.trans hQeq, by rw [← hdeg, hQeq]⟩
      dsimp only
      split_ifs with hkj hk0 hk0'
      · -- non-defective, `k = 0` ⟹ `j = 1`: impossible, `1 ≤ j₀ ≤ deg Sj = 0`
        exact absurd hj₀k (by omega)
      · -- non-defective, `k ≥ 1`: the boundary sits inside the recursive call
        have hk1 : 1 ≤ Sj.natDegree := by omega
        have hlc : Sj.leadingCoeff = Azurite.BPR.Chapter4.sRes P Q (j - 1) := by
          rw [htj]
          exact leadingCoeff_sResP_eq_sRes P Q hpq (by omega)
            (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsResPne, hkdeg.trans hkj])
        have hdC : Polynomial.C (Sj.leadingCoeff ^ 2) = (cofactorMat P Q j Sj.natDegree).det := by
          rw [det_cofactorMat_domain P Q hP hpq hk1 (by omega) (by omega) hQ hsResPne hkdeg
            (by rw [hkj, ← hlc]; exact htjne)]
          congr 1
          rw [hkj, ← hlc, ← htj]; ring
        have hSkm1 : AzPolynomial.toPoly (divByRingElt (sj * ti)
            (-((Sj.leadingCoeff ^ 2 • Si).remExact Sj))) = sResP P Q (Sj.natDegree - 1) := by
          by_cases hiq2 : i ≤ Q.natDegree + 1
          · have hcC : Polynomial.C (sj * ti) = (cofactorMat P Q i j).det := by
              rw [hsj, hti]
              exact (det_cofactorMat_domain P Q hP hpq hj1 hji hiq2 hQ hne hdeg
                (by rw [← hsj]; exact hsjne)).symm
            exact toPoly_Skm1_eq_sResP_domain P Q hQ hpq Si Sj (sj * ti) (Sj.leadingCoeff ^ 2)
              hSi hSj hcC hdC (by omega) (by omega) (by omega) (mul_ne_zero hsjne htine) hsResPne
              hkdeg hk1
          · obtain ⟨hSiQ, hjeq⟩ := hbdry (hicase.resolve_left hiq2)
            have hQeq : sResP P Q (i - 1) = Q := hSi.symm.trans hSiQ
            have hsk : Azurite.BPR.Chapter4.sRes P Q Sj.natDegree = Sj.leadingCoeff := by
              rw [hkj]; exact hlc.symm
            exact toPoly_Skm1_eq_sResP_domain_ip P Q hP hQ hpq Si Sj (sj * ti) (Sj.leadingCoeff ^ 2)
              hSiQ (by rw [hSj, hjeq]) hk1 (by omega) (by rw [← hjeq]; exact hsResPne)
              (by rw [← hjeq]; exact hkdeg) (by rw [hsk]; exact htjne)
              (by rw [← hjeq, ← hsj]; exact hsjne) (by rw [hsk, ← hjeq, ← htj]; ring)
              (by rw [hsj, hti, ← hjeq, show (sResP P Q (i - 1)).leadingCoeff = Q.leadingCoeff
                  from by rw [hQeq]])
        have hUkm1 : AzPolynomial.toPoly (divByRingElt (sj * ti)
            ((exactDivQuoRem (Sj.leadingCoeff ^ 2 • Si) Sj).1 * Uj - Sj.leadingCoeff ^ 2 • Ui))
            = sResU P Q (Sj.natDegree - 1) := by
          rcases hUVi with ⟨hiq1, hUi, _⟩ | ⟨hip2, hUi0, _⟩
          · have hcC : Polynomial.C (sj * ti) = (cofactorMat P Q i j).det := by
              rw [hsj, hti]
              exact (det_cofactorMat_domain P Q hP hpq hj1 hji hiq1 hQ hne hdeg
                (by rw [← hsj]; exact hsjne)).symm
            exact toPoly_Ukm1_eq_sResU_domain P Q hQ hpq Si Sj Ui Uj (sj * ti)
              (Sj.leadingCoeff ^ 2) hSi hSj hUi hUj hcC hdC (by omega) (by omega) (by omega)
              (mul_ne_zero hsjne htine) hsResPne hkdeg hk1
          · obtain ⟨hSiQ, hjeq⟩ := hbdry hip2
            have hsk : Azurite.BPR.Chapter4.sRes P Q Sj.natDegree = Sj.leadingCoeff := by
              rw [hkj]; exact hlc.symm
            exact toPoly_Ukm1_eq_sResU_domain_ip P Q hP hQ hpq hq1 Si Sj Ui Uj (sj * ti)
              (Sj.leadingCoeff ^ 2) hSiQ (by rw [hSj, hjeq]) hk1 (by omega)
              (by rw [← hjeq]; exact hsResPne) (by rw [← hjeq]; exact hkdeg)
              (by rw [hsk]; exact htjne) (by rw [← hjeq, ← hsj]; exact hsjne)
              (by rw [hsk, ← hjeq, ← htj]; ring)
              (by rw [hsj, hti, ← hjeq, show (sResP P Q (i - 1)).leadingCoeff = Q.leadingCoeff
                  from by rw [hSi.symm.trans hSiQ]]) hUi0 (by rw [hUj, hjeq])
        have hVkm1 : AzPolynomial.toPoly (divByRingElt (sj * ti)
            ((exactDivQuoRem (Sj.leadingCoeff ^ 2 • Si) Sj).1 * Vj - Sj.leadingCoeff ^ 2 • Vi))
            = sResV P Q (Sj.natDegree - 1) := by
          rcases hUVi with ⟨hiq1, _, hVi⟩ | ⟨hip2, _, hVi1⟩
          · have hcC : Polynomial.C (sj * ti) = (cofactorMat P Q i j).det := by
              rw [hsj, hti]
              exact (det_cofactorMat_domain P Q hP hpq hj1 hji hiq1 hQ hne hdeg
                (by rw [← hsj]; exact hsjne)).symm
            exact toPoly_Vkm1_eq_sResV_domain P Q hQ hpq Si Sj Vi Vj (sj * ti)
              (Sj.leadingCoeff ^ 2) hSi hSj hVi hVj hcC hdC (by omega) (by omega) (by omega)
              (mul_ne_zero hsjne htine) hsResPne hkdeg hk1
          · obtain ⟨hSiQ, hjeq⟩ := hbdry hip2
            have hsk : Azurite.BPR.Chapter4.sRes P Q Sj.natDegree = Sj.leadingCoeff := by
              rw [hkj]; exact hlc.symm
            exact toPoly_Vkm1_eq_sResV_domain_ip P Q hP hQ hpq hq1 Si Sj Vi Vj (sj * ti)
              (Sj.leadingCoeff ^ 2) hSiQ (by rw [hSj, hjeq]) hk1 (by omega)
              (by rw [← hjeq]; exact hsResPne) (by rw [← hjeq]; exact hkdeg)
              (by rw [hsk]; exact htjne) (by rw [← hjeq, ← hsj]; exact hsjne)
              (by rw [hsk, ← hjeq, ← htj]; ring)
              (by rw [hsj, hti, ← hjeq, show (sResP P Q (i - 1)).leadingCoeff = Q.leadingCoeff
                  from by rw [hSi.symm.trans hSiQ]]) hVi1 (by rw [hVj, hjeq])
        obtain ⟨ihlen, t, ihget, ihU, ihV⟩ := ih j Sj.natDegree Sj _ Sj.leadingCoeff
          Sj.leadingCoeff Uj Vj _ _
          (by omega) hk1 (by omega) (by omega) (Or.inl (by omega)) hSj hSkm1 hkdeg
          (by rw [hkj]; exact hkdeg.trans hkj) (by rw [hkj]; exact hlc) htj hUkm1 hVkm1
          (Or.inl ⟨by omega, hUj, hVj⟩)
        refine ⟨?_, t, ?_, ihU, ihV⟩
        · simp only [List.length_cons, ihlen]; omega
        · obtain ⟨m, hm⟩ : ∃ m, j - j₀ = m + 1 := ⟨j - j₀ - 1, by omega⟩
          rw [hm, List.getElem?_cons_succ, show m = Sj.natDegree - j₀ from by omega]
          exact ihget
      · -- defective, `k = 0` (terminal): impossible, `1 ≤ j₀ ≤ deg Sj = 0`
        exact absurd hj₀k (by omega)
      · -- defective, `k ≥ 1`: the boundary sits inside the recursive call, past the gap
        set sk := Azurite.ExactDiv.exactDiv
          (epsilonSign (j - Sj.natDegree) * Sj.leadingCoeff ^ (j - Sj.natDegree))
          (sj ^ (j - Sj.natDegree - 1)) with hsk_def
        have hk_lt : Sj.natDegree < j - 1 := by
          have hk_le : Sj.natDegree ≤ j - 1 := by
            rw [← hkdeg]
            exact Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
          omega
        obtain ⟨-, hsksRes, hndk⟩ := def_step_domain P Q hP hQ hpq hjq hj1 Sj hSj hsResPne hkdeg
          hjnd hsj hk_lt
        rw [← hsk_def] at hsksRes
        have hsResP_k_ne : sResP P Q Sj.natDegree ≠ 0 := by
          intro h; rw [h, Polynomial.natDegree_zero] at hndk; omega
        have hsRes_ne : Azurite.BPR.Chapter4.sRes P Q Sj.natDegree ≠ 0 :=
          (isNonDefective_iff_sRes_ne_zero P Q hpq (by omega)).mp
            (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsResP_k_ne, hndk])
        have hdC : Polynomial.C (Sj.leadingCoeff * sk) = (cofactorMat P Q j Sj.natDegree).det := by
          rw [det_cofactorMat_domain P Q hP hpq (by omega) (by omega) (by omega) hQ hsResPne hkdeg
            hsRes_ne]
          congr 1
          rw [hsksRes, htj]; ring
        have hSkm1 : AzPolynomial.toPoly (divByRingElt (sj * ti)
            (-(((Sj.leadingCoeff * sk) • Si).remExact Sj))) = sResP P Q (Sj.natDegree - 1) := by
          by_cases hiq2 : i ≤ Q.natDegree + 1
          · have hcC : Polynomial.C (sj * ti) = (cofactorMat P Q i j).det := by
              rw [hsj, hti]
              exact (det_cofactorMat_domain P Q hP hpq hj1 hji hiq2 hQ hne hdeg
                (by rw [← hsj]; exact hsjne)).symm
            exact toPoly_Skm1_eq_sResP_domain P Q hQ hpq Si Sj (sj * ti) (Sj.leadingCoeff * sk)
              hSi hSj hcC hdC (by omega) (by omega) (by omega) (mul_ne_zero hsjne htine) hsResPne
              hkdeg (by omega)
          · obtain ⟨hSiQ, hjeq⟩ := hbdry (hicase.resolve_left hiq2)
            have hQeq : sResP P Q (i - 1) = Q := hSi.symm.trans hSiQ
            exact toPoly_Skm1_eq_sResP_domain_ip P Q hP hQ hpq Si Sj (sj * ti) (Sj.leadingCoeff * sk)
              hSiQ (by rw [hSj, hjeq]) (by omega) (by omega) (by rw [← hjeq]; exact hsResPne)
              (by rw [← hjeq]; exact hkdeg) hsRes_ne (by rw [← hjeq, ← hsj]; exact hsjne)
              (by rw [hsksRes, show (sResP P Q (Q.natDegree - 1)).leadingCoeff = Sj.leadingCoeff
                  from by rw [← hjeq, ← htj]]; ring)
              (by rw [hsj, hti, ← hjeq, show (sResP P Q (i - 1)).leadingCoeff = Q.leadingCoeff
                  from by rw [hQeq]])
        have hUkm1 : AzPolynomial.toPoly (divByRingElt (sj * ti)
            ((exactDivQuoRem ((Sj.leadingCoeff * sk) • Si) Sj).1 * Uj - (Sj.leadingCoeff * sk) • Ui))
            = sResU P Q (Sj.natDegree - 1) := by
          rcases hUVi with ⟨hiq1, hUi, _⟩ | ⟨hip2, hUi0, _⟩
          · have hcC : Polynomial.C (sj * ti) = (cofactorMat P Q i j).det := by
              rw [hsj, hti]
              exact (det_cofactorMat_domain P Q hP hpq hj1 hji hiq1 hQ hne hdeg
                (by rw [← hsj]; exact hsjne)).symm
            exact toPoly_Ukm1_eq_sResU_domain P Q hQ hpq Si Sj Ui Uj (sj * ti)
              (Sj.leadingCoeff * sk) hSi hSj hUi hUj hcC hdC (by omega) (by omega) (by omega)
              (mul_ne_zero hsjne htine) hsResPne hkdeg (by omega)
          · obtain ⟨hSiQ, hjeq⟩ := hbdry hip2
            exact toPoly_Ukm1_eq_sResU_domain_ip P Q hP hQ hpq hq1 Si Sj Ui Uj (sj * ti)
              (Sj.leadingCoeff * sk) hSiQ (by rw [hSj, hjeq]) (by omega) (by omega)
              (by rw [← hjeq]; exact hsResPne) (by rw [← hjeq]; exact hkdeg) hsRes_ne
              (by rw [← hjeq, ← hsj]; exact hsjne)
              (by rw [hsksRes, show (sResP P Q (Q.natDegree - 1)).leadingCoeff = Sj.leadingCoeff
                  from by rw [← hjeq, ← htj]]; ring)
              (by rw [hsj, hti, ← hjeq, show (sResP P Q (i - 1)).leadingCoeff = Q.leadingCoeff
                  from by rw [hSi.symm.trans hSiQ]]) hUi0 (by rw [hUj, hjeq])
        have hVkm1 : AzPolynomial.toPoly (divByRingElt (sj * ti)
            ((exactDivQuoRem ((Sj.leadingCoeff * sk) • Si) Sj).1 * Vj - (Sj.leadingCoeff * sk) • Vi))
            = sResV P Q (Sj.natDegree - 1) := by
          rcases hUVi with ⟨hiq1, _, hVi⟩ | ⟨hip2, _, hVi1⟩
          · have hcC : Polynomial.C (sj * ti) = (cofactorMat P Q i j).det := by
              rw [hsj, hti]
              exact (det_cofactorMat_domain P Q hP hpq hj1 hji hiq1 hQ hne hdeg
                (by rw [← hsj]; exact hsjne)).symm
            exact toPoly_Vkm1_eq_sResV_domain P Q hQ hpq Si Sj Vi Vj (sj * ti)
              (Sj.leadingCoeff * sk) hSi hSj hVi hVj hcC hdC (by omega) (by omega) (by omega)
              (mul_ne_zero hsjne htine) hsResPne hkdeg (by omega)
          · obtain ⟨hSiQ, hjeq⟩ := hbdry hip2
            exact toPoly_Vkm1_eq_sResV_domain_ip P Q hP hQ hpq hq1 Si Sj Vi Vj (sj * ti)
              (Sj.leadingCoeff * sk) hSiQ (by rw [hSj, hjeq]) (by omega) (by omega)
              (by rw [← hjeq]; exact hsResPne) (by rw [← hjeq]; exact hkdeg) hsRes_ne
              (by rw [← hjeq, ← hsj]; exact hsjne)
              (by rw [hsksRes, show (sResP P Q (Q.natDegree - 1)).leadingCoeff = Sj.leadingCoeff
                  from by rw [← hjeq, ← htj]]; ring)
              (by rw [hsj, hti, ← hjeq, show (sResP P Q (i - 1)).leadingCoeff = Q.leadingCoeff
                  from by rw [hSi.symm.trans hSiQ]]) hVi1 (by rw [hVj, hjeq])
        obtain ⟨ihlen, t, ihget, ihU, ihV⟩ := ih j Sj.natDegree Sj _ sk Sj.leadingCoeff Uj Vj _ _
          (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) hSj hSkm1 hkdeg
          hndk hsksRes htj hUkm1 hVkm1 (Or.inl ⟨by omega, hUj, hVj⟩)
        refine ⟨?_, t, ?_, ihU, ihV⟩
        · simp only [List.length_cons, List.length_append, List.length_replicate, ihlen]; omega
        · obtain ⟨m, hm⟩ : ∃ m, j - j₀ = m + 1 := ⟨j - j₀ - 1, by omega⟩
          rw [hm, List.getElem?_cons_succ,
            List.getElem?_append_right (by rw [List.length_replicate]; omega),
            List.length_replicate,
            show m - (j - Sj.natDegree - 2) = (Sj.natDegree - j₀) + 1 from by omega,
            List.getElem?_cons_succ]
          exact ihget

open Azurite.BPR.Chapter8 in
/-- **Boundary cofactors of the top-level call** (`i = p + 1`, over an integral domain).  The
    output of the main-loop call made by `extendedSignedSubresultant` has length `p`, and its
    tuple at (descending) position `p - j₀` — ascending index `j₀ - 1`, where `j₀ ≥ 1` carries
    the domain-transferable boundary package — carries the boundary cofactors
    `sResU_{j₀-1}`/`sResV_{j₀-1}`.  Peels the `j = p` step with the `_first` bridges, then
    applies `ssAuxExt_boundary` to the tail at `(i, j) = (p, q)`, exactly as
    `ssAuxExt_bezout_first_domain` does. -/
theorem ssAuxExt_boundary_first {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {j₀ : ℕ} (hj₀1 : 1 ≤ j₀)
    (hj₀q : j₀ ≤ Q.natDegree)
    (h0 : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) = 0)
    (hnd : (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀).natDegree = j₀)
    (hne0 : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀ ≠ 0) :
    (ssAuxExt (P.natDegree + 1) P.natDegree P Q 1 1 1 0 0 1).length = P.natDegree
    ∧ ∃ t, (ssAuxExt (P.natDegree + 1) P.natDegree P Q 1 1 1 0 0 1)[P.natDegree - j₀]? = some t
        ∧ AzPolynomial.toPoly t.2.2.1
            = sResU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1)
        ∧ AzPolynomial.toPoly t.2.2.2
            = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) := by
  have hpd : (AzPolynomial.toPoly P).natDegree = P.natDegree := AzPolynomial.natDegree_toPoly P
  have hqd : (AzPolynomial.toPoly Q).natDegree = Q.natDegree := AzPolynomial.natDegree_toPoly Q
  have hPm : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hQm : AzPolynomial.toPoly Q ≠ 0 := fun h => hQ (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hpqm : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
    rw [hpd, hqd]; exact hpq
  have hq1m : 1 ≤ (AzPolynomial.toPoly Q).natDegree := by rw [hqd]; exact hq1
  have hlcq : (AzPolynomial.toPoly Q).leadingCoeff = Q.leadingCoeff := leadingCoeff_toPoly Q
  have hsRq : Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        (AzPolynomial.toPoly Q).natDegree
      = (epsilonSign (P.natDegree - Q.natDegree) : D)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
    rw [sRes_natDegree _ _ hpqm hQm, epsilonSign_eq, zsmul_eq_mul, Azurite.BPR.Chapter4.ε, hpd, hqd,
      hlcq]
    push_cast; ring
  have hsRqne : Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        (AzPolynomial.toPoly Q).natDegree ≠ 0 := by
    rw [hsRq]
    exact mul_ne_zero (by rw [epsilonSign_eq]; exact pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by rw [← hlcq]; exact Polynomial.leadingCoeff_ne_zero.mpr hQm))
  have hndq : IsNonDefective (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
      (AzPolynomial.toPoly Q).natDegree :=
    (isNonDefective_iff_sRes_ne_zero _ _ hpqm (le_refl _)).mpr hsRqne
  have hSResq_nd : (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
      (AzPolynomial.toPoly Q).natDegree).natDegree = (AzPolynomial.toPoly Q).natDegree :=
    natDegree_eq_of_degree_eq_some hndq
  have hPm1 : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (P.natDegree - 1)
      = AzPolynomial.toPoly Q := by
    rw [show P.natDegree - 1 = (AzPolynomial.toPoly P).natDegree - 1 from by rw [hpd]]
    exact sResP_pm1_eq_Q_domain _ _ hQm hpqm
  rw [ssAuxExt, ite_eq_right hQ]
  dsimp only
  split_ifs with hkj hk0 hk0'
  · exact absurd hk0 (by omega)
  · -- non-defective `k = q ≥ 1` (so `q = p - 1`)
    have hSkm1 : AzPolynomial.toPoly (divByRingElt (1 * 1)
        (-((Q.leadingCoeff ^ 2 • P).remExact Q)))
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (Q.natDegree - 1) := by
      rw [show Q.natDegree - 1 = (AzPolynomial.toPoly Q).natDegree - 1 from by rw [hqd]]
      refine toPoly_Skm1_eq_sResP_domain_first (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm
        hpqm hq1m P Q (1 * 1) (Q.leadingCoeff ^ 2) rfl rfl hsRqne ?_ (one_mul 1)
      rw [hsRq, hlcq, show P.natDegree - Q.natDegree = 1 from by omega,
        show (epsilonSign 1 : D) = 1 from by rw [epsilonSign_eq]; norm_num]; ring
    have hUkm1 : AzPolynomial.toPoly (divByRingElt (1 * 1)
        ((exactDivQuoRem (Q.leadingCoeff ^ 2 • P) Q).1 * 0 - Q.leadingCoeff ^ 2 • 1))
        = sResU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (Q.natDegree - 1) := by
      rw [show Q.natDegree - 1 = (AzPolynomial.toPoly Q).natDegree - 1 from by rw [hqd]]
      refine toPoly_Ukm1_eq_sResU_domain_first (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm
        hpqm hq1m P Q 1 0 (1 * 1) (Q.leadingCoeff ^ 2) rfl rfl hsRqne ?_ (one_mul 1) toPoly_one
        toPoly_zero
      rw [hsRq, hlcq, show P.natDegree - Q.natDegree = 1 from by omega,
        show (epsilonSign 1 : D) = 1 from by rw [epsilonSign_eq]; norm_num]; ring
    have hVkm1 : AzPolynomial.toPoly (divByRingElt (1 * 1)
        ((exactDivQuoRem (Q.leadingCoeff ^ 2 • P) Q).1 * 1 - Q.leadingCoeff ^ 2 • 0))
        = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (Q.natDegree - 1) := by
      rw [show Q.natDegree - 1 = (AzPolynomial.toPoly Q).natDegree - 1 from by rw [hqd]]
      refine toPoly_Vkm1_eq_sResV_domain_first (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm
        hpqm hq1m P Q 0 1 (1 * 1) (Q.leadingCoeff ^ 2) rfl rfl hsRqne ?_ (one_mul 1) toPoly_zero
        toPoly_one
      rw [hsRq, hlcq, show P.natDegree - Q.natDegree = 1 from by omega,
        show (epsilonSign 1 : D) = 1 from by rw [epsilonSign_eq]; norm_num]; ring
    have hsRq' : Q.leadingCoeff = Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P)
        (AzPolynomial.toPoly Q) Q.natDegree := by
      rw [← hqd, hsRq, show P.natDegree - Q.natDegree = 1 from by omega,
        show (epsilonSign 1 : D) = 1 from by rw [epsilonSign_eq]; norm_num, pow_one, one_mul]
    obtain ⟨ihlen, t, ihget, ihU, ihV⟩ := ssAuxExt_boundary (AzPolynomial.toPoly P)
      (AzPolynomial.toPoly Q) hPm hQm hpqm hq1m hj₀1 (by rw [hqd]; exact hj₀q) h0 hnd hne0
      P.natDegree P.natDegree Q.natDegree
      Q _ Q.leadingCoeff Q.leadingCoeff 0 1 _ _
      (by omega) hq1 (by omega) hqd.ge (Or.inr hpd.symm) (by rw [hPm1])
      hSkm1 (by rw [hPm1, hqd]) (by rw [← hqd]; exact hSResq_nd) hsRq'
      (by rw [hPm1, hlcq]) hUkm1 hVkm1
      (Or.inr ⟨hpd.symm, toPoly_zero, toPoly_one⟩)
    refine ⟨?_, t, ?_, ihU, ihV⟩
    · simp only [List.length_cons, ihlen]; omega
    · obtain ⟨m, hm⟩ : ∃ m, P.natDegree - j₀ = m + 1 := ⟨P.natDegree - j₀ - 1, by omega⟩
      rw [hm, List.getElem?_cons_succ, show m = Q.natDegree - j₀ from by omega]
      exact ihget
  · exact absurd hk0' (by omega)
  · -- defective `k = q ≥ 1` with the gap `q < p - 1`
    set sk := Azurite.ExactDiv.exactDiv
      (epsilonSign (P.natDegree - Q.natDegree) * Q.leadingCoeff ^ (P.natDegree - Q.natDegree))
      ((1 : D) ^ (P.natDegree - Q.natDegree - 1)) with hsk_def
    have hsk : sk = epsilonSign (P.natDegree - Q.natDegree)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
      rw [hsk_def, one_pow]
      have := Azurite.ExactDiv.exactDiv_mul_self (epsilonSign (P.natDegree - Q.natDegree)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) 1 (one_dvd _) one_ne_zero
      rwa [mul_one] at this
    have hskRes : sk = Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        Q.natDegree := by rw [hsk, ← hsRq, hqd]
    have hdfirst : Q.leadingCoeff * sk = Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P)
        (AzPolynomial.toPoly Q) (AzPolynomial.toPoly Q).natDegree
          * (AzPolynomial.toPoly Q).leadingCoeff := by
      rw [hlcq, hqd, hskRes]; ring
    have hSkm1 : AzPolynomial.toPoly (divByRingElt (1 * 1)
        (-(((Q.leadingCoeff * sk) • P).remExact Q)))
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (Q.natDegree - 1) := by
      rw [show Q.natDegree - 1 = (AzPolynomial.toPoly Q).natDegree - 1 from by rw [hqd]]
      exact toPoly_Skm1_eq_sResP_domain_first (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm
        hpqm hq1m P Q (1 * 1) (Q.leadingCoeff * sk) rfl rfl hsRqne hdfirst (one_mul 1)
    have hUkm1 : AzPolynomial.toPoly (divByRingElt (1 * 1)
        ((exactDivQuoRem ((Q.leadingCoeff * sk) • P) Q).1 * 0 - (Q.leadingCoeff * sk) • 1))
        = sResU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (Q.natDegree - 1) := by
      rw [show Q.natDegree - 1 = (AzPolynomial.toPoly Q).natDegree - 1 from by rw [hqd]]
      exact toPoly_Ukm1_eq_sResU_domain_first (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm
        hpqm hq1m P Q 1 0 (1 * 1) (Q.leadingCoeff * sk) rfl rfl hsRqne hdfirst
        (one_mul 1) toPoly_one toPoly_zero
    have hVkm1 : AzPolynomial.toPoly (divByRingElt (1 * 1)
        ((exactDivQuoRem ((Q.leadingCoeff * sk) • P) Q).1 * 1 - (Q.leadingCoeff * sk) • 0))
        = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (Q.natDegree - 1) := by
      rw [show Q.natDegree - 1 = (AzPolynomial.toPoly Q).natDegree - 1 from by rw [hqd]]
      exact toPoly_Vkm1_eq_sResV_domain_first (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm
        hpqm hq1m P Q 0 1 (1 * 1) (Q.leadingCoeff * sk) rfl rfl hsRqne hdfirst
        (one_mul 1) toPoly_zero toPoly_one
    obtain ⟨ihlen, t, ihget, ihU, ihV⟩ := ssAuxExt_boundary (AzPolynomial.toPoly P)
      (AzPolynomial.toPoly Q) hPm hQm hpqm hq1m hj₀1 (by rw [hqd]; exact hj₀q) h0 hnd hne0
      P.natDegree P.natDegree Q.natDegree
      Q _ sk Q.leadingCoeff 0 1 _ _
      (by omega) hq1 (by omega) hqd.ge (Or.inr hpd.symm) (by rw [hPm1])
      hSkm1 (by rw [hPm1, hqd]) (by rw [← hqd]; exact hSResq_nd) hskRes
      (by rw [hPm1, hlcq]) hUkm1 hVkm1
      (Or.inr ⟨hpd.symm, toPoly_zero, toPoly_one⟩)
    refine ⟨?_, t, ?_, ihU, ihV⟩
    · simp only [List.length_cons, List.length_append, List.length_replicate, ihlen]; omega
    · obtain ⟨m, hm⟩ : ∃ m, P.natDegree - j₀ = m + 1 := ⟨P.natDegree - j₀ - 1, by omega⟩
      rw [hm, List.getElem?_cons_succ,
        List.getElem?_append_right (by rw [List.length_replicate]; omega),
        List.length_replicate,
        show m - (P.natDegree - Q.natDegree - 2) = (Q.natDegree - j₀) + 1 from by omega,
        List.getElem?_cons_succ]
      exact ihget

open Azurite.BPR.Chapter8 in
/-- **BPR Algorithm 8.22, boundary-cofactor correctness (both components, over an integral
    domain).**  For `P, Q` with `1 ≤ deg Q < deg P` and a boundary index `j₀ ≥ 1` carrying the
    domain-transferable package (`sResP_{j₀-1} = 0`, `sResP_{j₀}` nonzero non-defective — over
    the fraction field this says `j₀` is the gcd degree), the `sResU`/`sResV` output arrays of
    `extendedSignedSubresultant` at index `j₀ - 1` — where `s_{j₀-1} = 0`, so the non-defective
    guard of `extendedSignedSubresultant_cofactor_domain` says nothing — are (after `toPoly`)
    exactly the abstract cofactor determinants `sResU_{j₀-1}` and `sResV_{j₀-1}` of
    Notation 8.41. -/
theorem extendedSignedSubresultant_boundary_cofactors_domain {D : Type _} [CommRing D]
    [DecidableEq D] [Azurite.ExactDiv D] [IsDomain D]
    (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀) (hj₀q : j₀ ≤ Q.natDegree)
    (h0 : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) = 0)
    (hnd : (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀).natDegree = j₀)
    (hne : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀ ≠ 0) :
    AzPolynomial.toPoly ((extendedSignedSubresultant P Q).2.2.1[j₀ - 1]!)
      = sResU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1)
    ∧ AzPolynomial.toPoly ((extendedSignedSubresultant P Q).2.2.2[j₀ - 1]!)
      = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) := by
  obtain ⟨hlen, t, hget, hU, hV⟩ :=
    ssAuxExt_boundary_first P Q hP hQ hpq hq1 hj₀1 hj₀q h0 hnd hne
  have hcond : ¬ (Q = 0 ∨ P.natDegree ≤ Q.natDegree) := not_or.mpr ⟨hQ, by omega⟩
  set lst := (P, P.leadingCoeff, (1 : AzPolynomial D), (0 : AzPolynomial D))
    :: ssAuxExt (P.natDegree + 1) P.natDegree P Q 1 1 1 0 0 1 with hlst
  have hlstlen : lst.length = P.natDegree + 1 := by
    rw [hlst, List.length_cons, hlen]
  have hj₀lt : j₀ - 1 < lst.length := by rw [hlstlen]; omega
  have hgetlst : lst.reverse[j₀ - 1]? = some t := by
    rw [List.getElem?_reverse hj₀lt,
      show lst.length - 1 - (j₀ - 1) = (P.natDegree - j₀) + 1 from by rw [hlstlen]; omega,
      hlst, List.getElem?_cons_succ]
    exact hget
  have hframe : ∀ f : AzPolynomial D × D × AzPolynomial D × AzPolynomial D → AzPolynomial D,
      ((lst.reverse.map f).toArray)[j₀ - 1]! = f t := by
    intro f
    have hlen' : j₀ - 1 < (lst.reverse.map f).length := by
      rw [List.length_map, List.length_reverse, hlstlen]; omega
    have hsz : j₀ - 1 < (lst.reverse.map f).toArray.size := by
      rw [List.size_toArray]; exact hlen'
    rw [getElem!_pos (lst.reverse.map f).toArray (j₀ - 1) hsz, List.getElem_toArray]
    have hopt : (lst.reverse.map f)[j₀ - 1]? = some (f t) := by
      rw [List.getElem?_map, hgetlst]; rfl
    exact Option.some_inj.mp ((List.getElem?_eq_getElem hlen').symm.trans hopt)
  constructor
  · have harr : (extendedSignedSubresultant P Q).2.2.1
        = (lst.reverse.map (·.2.2.1)).toArray := by
      rw [hlst]; unfold extendedSignedSubresultant; rw [ite_eq_right hcond]
    rw [harr, hframe (·.2.2.1)]
    exact hU
  · have harr : (extendedSignedSubresultant P Q).2.2.2
        = (lst.reverse.map (·.2.2.2)).toArray := by
      rw [hlst]; unfold extendedSignedSubresultant; rw [ite_eq_right hcond]
    rw [harr, hframe (·.2.2.2)]
    exact hV

open Azurite.BPR.Chapter8 in
/-- **BPR Algorithm 8.22, boundary `sResV` correctness over an integral domain** (e.g. the
    `AzInt` run of the algorithm).  The boundary index `j₀` is characterized by the
    domain-transferable package; over the fraction field it is the gcd degree. -/
theorem extendedSignedSubresultant_boundary_domain {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D]
    (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀) (hj₀q : j₀ ≤ Q.natDegree)
    (h0 : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) = 0)
    (hnd : (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀).natDegree = j₀)
    (hne : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀ ≠ 0) :
    AzPolynomial.toPoly ((extendedSignedSubresultant P Q).2.2.2[j₀ - 1]!)
      = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) :=
  (extendedSignedSubresultant_boundary_cofactors_domain P Q hP hQ hpq hq1 hj₀1 hj₀q
    h0 hnd hne).2

open Azurite.BPR.Chapter8 in
/-- **BPR Algorithm 8.22, boundary `sResU` correctness over an integral domain.**  The
    `U`-component companion of `extendedSignedSubresultant_boundary_domain`. -/
theorem extendedSignedSubresultant_boundary_sResU_domain {D : Type _} [CommRing D]
    [DecidableEq D] [Azurite.ExactDiv D] [IsDomain D]
    (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀) (hj₀q : j₀ ≤ Q.natDegree)
    (h0 : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) = 0)
    (hnd : (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀).natDegree = j₀)
    (hne : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀ ≠ 0) :
    AzPolynomial.toPoly ((extendedSignedSubresultant P Q).2.2.1[j₀ - 1]!)
      = sResU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) :=
  (extendedSignedSubresultant_boundary_cofactors_domain P Q hP hQ hpq hq1 hj₀1 hj₀q
    h0 hnd hne).1

open Azurite.BPR.Chapter8 in
/-- **BPR Algorithm 8.22, boundary-cofactor correctness (both components, field version).**
    For `P, Q` with `1 ≤ deg Q < deg P` and gcd degree `j₀ ≥ 1`, the `sResU`/`sResV` output
    arrays of `extendedSignedSubresultant` at index `j₀ - 1` are (after `toPoly`) exactly the
    abstract cofactor determinants of Notation 8.41.  Corollary of the domain version: over a
    field the gcd hypothesis supplies the boundary package via Theorem 8.34's gcd branch. -/
theorem extendedSignedSubresultant_boundary_cofactors {K : Type _} [Field K] [DecidableEq K]
    (P Q : AzPolynomial K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀)
    (hj₀ : (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
      (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)).natDegree = j₀) :
    AzPolynomial.toPoly ((extendedSignedSubresultant P Q).2.2.1[j₀ - 1]!)
      = sResU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1)
    ∧ AzPolynomial.toPoly ((extendedSignedSubresultant P Q).2.2.2[j₀ - 1]!)
      = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) := by
  have hPm : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hQm : AzPolynomial.toPoly Q ≠ 0 := fun h => hQ (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hpqm : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
    rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]; exact hpq
  have hj₀q : j₀ ≤ Q.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd
      (@gcd_dvd_right _ _ Azurite.BPR.gcdMonoidPolynomial
        (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) hQm
    rw [hj₀, AzPolynomial.natDegree_toPoly] at h
    exact h
  have h0 : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) = 0 :=
    sResP_eq_zero_of_lt_gcd _ _ hPm hQm hpqm
      (by rw [AzPolynomial.natDegree_toPoly]; omega) (by omega)
  have hne : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀ ≠ 0 :=
    hj₀ ▸ sResP_natDegree_gcd_ne_zero _ _ hPm hQm hpqm
  have hnd : (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀).natDegree = j₀ := by
    have h1 : (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀).natDegree ≤ j₀ :=
      Polynomial.natDegree_le_iff_degree_le.mpr
        (sResP_degree_le _ _ hpqm (by rw [AzPolynomial.natDegree_toPoly]; exact hj₀q))
    have h2 := natDegree_gcd_le_natDegree_sResP _ _ hPm hQm hpqm hne
    rw [hj₀] at h2
    omega
  exact extendedSignedSubresultant_boundary_cofactors_domain P Q hP hQ hpq hq1 hj₀1 hj₀q
    h0 hnd hne

open Azurite.BPR.Chapter8 in
/-- **BPR Algorithm 8.22, boundary `sResV` correctness.**  At output index `j₀ - 1` (just below
    the gcd degree `j₀ ≥ 1`), the `sResV` output array of `extendedSignedSubresultant` is (after
    `toPoly`) the abstract `sResV_{j₀-1}` — the gcd-free part of `P` with respect to `Q` up to a
    multiplicative constant (Proposition 10.14). -/
theorem extendedSignedSubresultant_boundary {K : Type _} [Field K] [DecidableEq K]
    (P Q : AzPolynomial K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀)
    (hj₀ : (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
      (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)).natDegree = j₀) :
    AzPolynomial.toPoly ((extendedSignedSubresultant P Q).2.2.2[j₀ - 1]!)
      = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) :=
  (extendedSignedSubresultant_boundary_cofactors P Q hP hQ hpq hq1 hj₀1 hj₀).2

open Azurite.BPR.Chapter8 in
/-- **BPR Algorithm 8.22, boundary `sResU` correctness.**  The `U`-component companion of
    `extendedSignedSubresultant_boundary`. -/
theorem extendedSignedSubresultant_boundary_sResU {K : Type _} [Field K] [DecidableEq K]
    (P Q : AzPolynomial K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀)
    (hj₀ : (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
      (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)).natDegree = j₀) :
    AzPolynomial.toPoly ((extendedSignedSubresultant P Q).2.2.1[j₀ - 1]!)
      = sResU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) :=
  (extendedSignedSubresultant_boundary_cofactors P Q hP hQ hpq hq1 hj₀1 hj₀).1

/-! ### Consumer: gcd-free-part correctness of `gcdGcdFreePartRaw` -/

open Azurite.BPR.Chapter8 in
/-- **The raw Algorithm 10.1 pair's second output is `sResV_{j₀−1}` exactly**
(field, `deg P > deg Q ≥ 1`, gcd degree `j₀ ≥ 1`): completing the raw
route's correctness — the first output was already identified with
`sResP_{j₀}` via the Algorithm 8.21 bridge; this identifies the second with
the boundary cofactor of Algorithm 8.22. -/
theorem gcdGcdFreePartRaw_snd {K : Type _} [Field K] [DecidableEq K]
    (P Q : AzPolynomial K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀)
    (hj₀ : (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
      (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)).natDegree = j₀) :
    AzPolynomial.toPoly (gcdGcdFreePartRaw P Q).2
      = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) := by
  have hQ0 : Q ≠ 0 := hQ
  have hP' : AzPolynomial.toPoly P ≠ 0 := toPoly_ne_zero hP
  have hQ' : AzPolynomial.toPoly Q ≠ 0 := toPoly_ne_zero hQ
  have hpq' : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
    rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]
    exact hpq
  have hjq : j₀ ≤ Q.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd
      (@gcd_dvd_right _ _ Azurite.BPR.gcdMonoidPolynomial
        (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) hQ'
    rw [hj₀, AzPolynomial.natDegree_toPoly] at h
    exact h
  -- positional identification of the `sResP` output array
  obtain ⟨hmaps, -⟩ := signedSubresultant_toPoly P Q hP hQ hpq hq1
  have hlen : (signedSubresultant P Q).1.size = P.natDegree + 1 := by
    have h := congrArg List.length hmaps
    simpa using h
  have hentry : ∀ ℓ, ℓ < P.natDegree + 1 →
      AzPolynomial.toPoly ((signedSubresultant P Q).1[ℓ]!)
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ := by
    intro ℓ hℓ
    have h := congrArg (fun l => l[ℓ]?) hmaps
    simp only [List.getElem?_map, List.getElem?_range, hℓ] at h
    have hℓs : ℓ < (signedSubresultant P Q).1.toList.length := by
      simpa [hlen] using hℓ
    rw [List.getElem?_eq_getElem hℓs] at h
    simp only [Option.map_some] at h
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega : ℓ < (signedSubresultant P Q).1.size)]
    simpa [Array.getElem_toList] using h
  -- the scan lands exactly on the gcd degree
  have hfst : (extendedSignedSubresultant P Q).1 = (signedSubresultant P Q).1 :=
    extendedSignedSubresultant_fst P Q
  have hfind : firstNonzero (extendedSignedSubresultant P Q).1 = some j₀ := by
    rw [hfst]
    refine firstNonzero_eq_some _ j₀ (by omega) ?_ ?_
    · intro i hi
      apply toPoly_inj.mp
      rw [hentry i (by omega), toPoly_zero]
      exact sResP_eq_zero_of_lt_gcd _ _ hP' hQ' hpq'
        (by rw [AzPolynomial.natDegree_toPoly]; omega) (by omega)
    · intro h
      have h2 := hentry j₀ (by omega)
      rw [h, toPoly_zero] at h2
      exact sResP_natDegree_gcd_ne_zero _ _ hP' hQ' hpq' (hj₀ ▸ h2.symm)
  -- reduce the wrapper and apply the boundary identification
  rw [gcdGcdFreePartRaw, ite_eq_right hQ0, ite_eq_right (by omega)]
  show AzPolynomial.toPoly (gcdGcdFreePartCore P Q).2 = _
  rw [gcdGcdFreePartCore]
  split
  rename_i sP s sU sV heq
  have hsP : sP = (extendedSignedSubresultant P Q).1 := by rw [heq]
  have hsV : sV = (extendedSignedSubresultant P Q).2.2.2 := by rw [heq]
  rw [show firstNonzero sP = some j₀ from by rw [hsP]; exact hfind, hsV]
  match j₀, hj₀1, hj₀ with
  | jj + 1, _, hj₀ =>
    exact extendedSignedSubresultant_boundary P Q hP hQ hpq hq1 (by omega) hj₀

open Azurite.BPR.Chapter8 in
/-- **Full gcd-free-part correctness of the raw Algorithm 10.1 pair** over a
field: the second output times the gcd is associated to `P` — it *is* the
gcd-free part of `P` with respect to `Q` up to a multiplicative constant
(BPR Proposition 10.14 via `sResV_gcdFree_associated`). -/
theorem gcdGcdFreePartRaw_snd_gcdFree {K : Type _} [Field K] [DecidableEq K]
    (P Q : AzPolynomial K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀)
    (hj₀ : (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
      (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)).natDegree = j₀) :
    Associated
      (AzPolynomial.toPoly (gcdGcdFreePartRaw P Q).2
        * @GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
            (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
      (AzPolynomial.toPoly P) := by
  rw [gcdGcdFreePartRaw_snd P Q hP hQ hpq hq1 hj₀1 hj₀]
  exact Azurite.BPR.sResV_gcdFree_associated (toPoly_ne_zero hP) (toPoly_ne_zero hQ)
    (by rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]; exact hpq)
    hj₀1 hj₀

end Azurite.AzPolynomial
