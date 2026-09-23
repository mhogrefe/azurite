import Azurite.AzPolynomial.Gcd
import Azurite.AzPolynomial.Equiv.SignedSubresultant
import Azurite.AzPolynomial.Equiv.SMul
import Azurite.AzPolynomial.Equiv.Sub

/-!
# Correctness of the subresultant gcd: equivalence with `Polynomial.gcd`

Main results (field coefficients `K`, `[Field K] [DecidableEq K]`):

* `toPoly_subresGcd_associated` — the core `subresGcd P Q` (the last nonzero
  signed subresultant) is associated to `gcd (toPoly P) (toPoly Q)`, via the
  Algorithm 8.21 bridge (`signedSubresultant_toPoly`) and the gcd branch of
  Theorem 8.34 (`associated_sResP_gcd`);
* `toPoly_monicize` — `monicize` computes `normalize` (monic-uniqueness:
  both sides are monic and associated to the input);
* **`toPoly_gcdMonic`** — `toPoly (gcdMonic P Q) = gcd (toPoly P) (toPoly Q)`
  (the Mathlib `NormalizedGCDMonoid` gcd of `K[X]`), unconditionally in
  `P, Q`. Each branch of the wrapper (zeros, constants, the `p = q`
  pre-step, proportionality, swapped degrees) is matched against the
  corresponding gcd identity; the pre-step is covered by the invariance
  `gcd A (C c·B − C d·A) = gcd A B` for `c ≠ 0`.

The `ℤ` case (`gcdNormalizedInt` against the normalized `ℤ[X]` gcd) is in
`Azurite.AzPolynomial.Equiv.GcdInt`.
-/

namespace Azurite.AzPolynomial

open Polynomial

/- Chapter 1 (imported through the Chapter 8 subresultant theory) installs the
`EuclideanDomain`-derived `GCDMonoid K[X]` instance
`Azurite.BPR.gcdMonoidPolynomial`, which would win over Mathlib's
`NormalizedGCDMonoid`-derived gcd. This file's statements are about
**Mathlib's** gcd, so we locally prefer it; the Chapter 8 gcd facts are
transported across the (associated) instances once, in
`toPoly_subresGcd_associated`. -/
attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

/-! ### `List.findIdx?` characterization and `firstNonzero` -/

private theorem List.findIdx?_eq_some_of {α : Type _} (p : α → Bool) :
    ∀ (l : List α) (j : ℕ) (hj : j < l.length),
      (∀ i (hi : i < j), p (l[i]'(by omega)) = false) → p (l[j]'hj) = true →
      l.findIdx? p = some j := by
  intro l
  induction l with
  | nil => intro j hj _ _; simp at hj
  | cons x xs ih =>
    intro j hj h1 h2
    match j with
    | 0 =>
      rw [List.findIdx?_cons, ite_eq_left (by simpa using h2)]
    | j + 1 =>
      rw [List.findIdx?_cons, ite_eq_right (by simpa using h1 0 (by omega)),
        ih j (by simpa using hj) (fun i hi => h1 (i + 1) (by omega)) (by simpa using h2)]
      rfl

/-- `firstNonzero` finds the index characterized by "zero below, nonzero
there". -/
theorem firstNonzero_eq_some {R : Type _} [CommRing R] [DecidableEq R]
    [Azurite.ExactDiv R] (arr : Array (AzPolynomial R)) (j : ℕ)
    (hj : j < arr.size) (h1 : ∀ i, i < j → arr[i]! = 0) (h2 : arr[j]! ≠ 0) :
    firstNonzero arr = some j := by
  rw [firstNonzero]
  refine List.findIdx?_eq_some_of _ arr.toList j (by simpa using hj) ?_ ?_
  · intro i hi
    have his : i < arr.size := by omega
    have := h1 i hi
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem his] at this
    simpa [Array.getElem_toList] using this
  · have := h2
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hj] at this
    simpa [Array.getElem_toList] using this

variable {K : Type _} [Field K] [DecidableEq K]

/-! ### The core: `subresGcd` is associated to the gcd -/

open Azurite.BPR.Chapter8 in
/-- **Core correctness.** For `P, Q ≠ 0` with `deg P > deg Q ≥ 1`,
`subresGcd P Q` is associated to `gcd (toPoly P) (toPoly Q)`, and it is
nonzero. -/
theorem toPoly_subresGcd_associated (P Q : AzPolynomial K) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    Associated (AzPolynomial.toPoly (subresGcd P Q))
        (GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
      ∧ subresGcd P Q ≠ 0 := by
  have hP' : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hQ' : AzPolynomial.toPoly Q ≠ 0 := fun h => hQ (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hpq' : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
    rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]; exact hpq
  have hq1' : 1 ≤ (AzPolynomial.toPoly Q).natDegree := by
    rw [AzPolynomial.natDegree_toPoly]; exact hq1
  -- the Algorithm 8.21 bridge, in list form
  have hlist := (signedSubresultant_toPoly P Q hP hQ hpq hq1).1
  set sP := (signedSubresultant P Q).1 with hsP
  have hlen : sP.size = P.natDegree + 1 := by
    have := congrArg List.length hlist
    simpa using this
  -- index-wise identification
  have hidx : ∀ j (hj : j < P.natDegree + 1),
      AzPolynomial.toPoly (sP[j]!)
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j := by
    intro j hj
    have hjs : j < sP.size := by omega
    have h1 : (sP.toList.map AzPolynomial.toPoly)[j]'(by simpa using hjs)
        = ((List.range (P.natDegree + 1)).map
            (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)))[j]'(by simpa using hj) := by
      congr 1
    rw [List.getElem_map, List.getElem_map, List.getElem_range] at h1
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjs]
    simpa [Array.getElem_toList] using h1
  -- the gcd degree (of the Chapter 8 / `EuclideanDomain`-instance gcd,
  -- which drives the abstract subresultant lemmas)
  set j₀ := (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
    (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)).natDegree with hj₀
  have hj₀q : j₀ ≤ (AzPolynomial.toPoly Q).natDegree :=
    Polynomial.natDegree_le_of_dvd
      (@gcd_dvd_right _ _ Azurite.BPR.gcdMonoidPolynomial _ _) hQ'
  have hj₀lt : j₀ < P.natDegree + 1 := by
    have h1 := hj₀q
    rw [AzPolynomial.natDegree_toPoly] at h1
    have h2 := hpq
    omega
  -- zeros below the gcd degree, nonzero at it
  have hzero : ∀ i, i < j₀ → sP[i]! = 0 := by
    intro i hi
    apply toPoly_inj.mp
    rw [hidx i (by omega), toPoly_zero]
    exact sResP_eq_zero_of_lt_gcd _ _ hP' hQ' hpq' (by omega) hi
  have hne : sP[j₀]! ≠ 0 := by
    intro h
    have h2 := hidx j₀ hj₀lt
    rw [h, toPoly_zero] at h2
    exact sResP_natDegree_gcd_ne_zero _ _ hP' hQ' hpq' h2.symm
  -- assemble
  have hfind : firstNonzero sP = some j₀ :=
    firstNonzero_eq_some sP j₀ (by omega) hzero hne
  have hout : subresGcd P Q = sP[j₀]! := by
    rw [subresGcd]
    rw [← hsP, hfind]
  rw [hout]
  refine ⟨?_, hne⟩
  rw [hidx j₀ hj₀lt]
  -- Chapter 8 identifies `sResP j₀` with the `EuclideanDomain`-instance gcd;
  -- the two instances' gcds divide each other, hence are associated
  have hbridge : Associated
      (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
        (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
      (GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) :=
    associated_of_dvd_dvd
      (dvd_gcd (@gcd_dvd_left _ _ Azurite.BPR.gcdMonoidPolynomial _ _)
        (@gcd_dvd_right _ _ Azurite.BPR.gcdMonoidPolynomial _ _))
      (@dvd_gcd _ _ Azurite.BPR.gcdMonoidPolynomial _ _ _
        (gcd_dvd_left _ _) (gcd_dvd_right _ _))
  exact (associated_sResP_gcd _ _ hP' hQ' hpq' rfl).trans hbridge

/-! ### Monic normalization -/

/-- `monicize` computes Mathlib's `normalize` (the monic associate). -/
theorem toPoly_monicize (q : AzPolynomial K) (hq : q ≠ 0) :
    AzPolynomial.toPoly (monicize q) = _root_.normalize (AzPolynomial.toPoly q) := by
  have hq' : AzPolynomial.toPoly q ≠ 0 := fun h => hq (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hlc : q.leadingCoeff = (AzPolynomial.toPoly q).leadingCoeff :=
    (leadingCoeff_toPoly q).symm
  have hlc0 : (AzPolynomial.toPoly q).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hq'
  have h1 : AzPolynomial.toPoly (monicize q)
      = Polynomial.C (AzPolynomial.toPoly q).leadingCoeff⁻¹ * AzPolynomial.toPoly q := by
    rw [monicize, toPoly_divByRingElt, hlc]
  have hmonic : (AzPolynomial.toPoly (monicize q)).Monic := by
    rw [h1, Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hlc0]
  have hCu : IsUnit (Polynomial.C (AzPolynomial.toPoly q).leadingCoeff⁻¹ : K[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc0))
  have hassoc : Associated (AzPolynomial.toPoly (monicize q)) (AzPolynomial.toPoly q) := by
    rw [h1]
    exact Associated.symm ⟨hCu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩
  exact Polynomial.eq_of_monic_of_associated hmonic (Polynomial.monic_normalize hq')
    (hassoc.trans (associated_normalize _))

/-! ### gcd identities in `K[X]` for the wrapper branches -/

theorem gcd_isUnit_left {A B : K[X]} (hA : IsUnit A) : GCDMonoid.gcd A B = 1 := by
  rw [← normalize_gcd A B]
  exact normalize_eq_one.mpr (isUnit_of_dvd_unit (gcd_dvd_left A B) hA)

theorem gcd_isUnit_right {A B : K[X]} (hB : IsUnit B) : GCDMonoid.gcd A B = 1 := by
  rw [gcd_comm]
  exact gcd_isUnit_left hB

theorem gcd_eq_normalize_left {A B : K[X]} (h : A ∣ B) :
    GCDMonoid.gcd A B = _root_.normalize A := by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd A B) (normalize_idem A)
  · exact (gcd_dvd_left A B).trans (associated_normalize A).dvd
  · exact dvd_gcd (normalize_associated A).dvd ((normalize_associated A).dvd.trans h)

/-- The `p = q` pre-step preserves the gcd: `gcd A (C c·B − C d·A) = gcd A B`
for `c ≠ 0`. -/
theorem gcd_pre_step (A B : K[X]) {c d : K} (hc : c ≠ 0) :
    GCDMonoid.gcd A (Polynomial.C c * B - Polynomial.C d * A) = GCDMonoid.gcd A B := by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  · refine dvd_gcd (gcd_dvd_left _ _) ?_
    have h2 : GCDMonoid.gcd A (Polynomial.C c * B - Polynomial.C d * A)
        ∣ Polynomial.C c * B := by
      have h3 := dvd_add (gcd_dvd_right A (Polynomial.C c * B - Polynomial.C d * A))
        (Dvd.dvd.mul_left (gcd_dvd_left A (Polynomial.C c * B - Polynomial.C d * A))
          (Polynomial.C d))
      simpa [sub_add_cancel] using h3
    have h4 : B = Polynomial.C c⁻¹ * (Polynomial.C c * B) := by
      rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1, one_mul]
    conv_rhs => rw [h4]
    exact Dvd.dvd.mul_left h2 _
  · refine dvd_gcd (gcd_dvd_left _ _) ?_
    exact dvd_sub (Dvd.dvd.mul_left (gcd_dvd_right _ _) _)
      (Dvd.dvd.mul_left (gcd_dvd_left _ _) _)

/-! ### The main field-case equivalence -/

theorem toPoly_ne_zero {R : Type _} [Semiring R] [DecidableEq R] {T : AzPolynomial R}
    (hT : T ≠ 0) : AzPolynomial.toPoly T ≠ 0 :=
  fun h => hT (toPoly_inj.mp (h.trans toPoly_zero.symm))

theorem isUnit_toPoly_of_natDegree_eq_zero {T : AzPolynomial K} (hT : T ≠ 0)
    (hd : T.natDegree = 0) : IsUnit (AzPolynomial.toPoly T) := by
  have hT' := toPoly_ne_zero hT
  have hd' : (AzPolynomial.toPoly T).natDegree = 0 := by
    rw [AzPolynomial.natDegree_toPoly]; exact hd
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hd'
  rw [hC]
  refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h => hT' ?_))
  rw [hC, h, Polynomial.C_0]

/-- `toPoly` of the pre-step polynomial. -/
theorem toPoly_pre_step {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]
    (P Q : AzPolynomial R) :
    AzPolynomial.toPoly (P.leadingCoeff • Q - Q.leadingCoeff • P)
      = Polynomial.C P.leadingCoeff * AzPolynomial.toPoly Q
        - Polynomial.C Q.leadingCoeff * AzPolynomial.toPoly P := by
  rw [toPoly_sub, toPoly_smul, toPoly_smul, Polynomial.smul_eq_C_mul,
    Polynomial.smul_eq_C_mul]

/-- The pre-step polynomial has degree strictly below `deg P` when
`deg P = deg Q ≥ 1` (the leading terms cancel). -/
theorem pre_step_natDegree_lt {R : Type _} [CommRing R] [DecidableEq R]
    [Azurite.ExactDiv R] [IsDomain R] {P Q : AzPolynomial R} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hdeq : P.natDegree = Q.natDegree)
    (hne : P.leadingCoeff • Q - Q.leadingCoeff • P ≠ 0) :
    (P.leadingCoeff • Q - Q.leadingCoeff • P).natDegree < P.natDegree := by
  have hP' := toPoly_ne_zero hP
  have hQ' := toPoly_ne_zero hQ
  set T := P.leadingCoeff • Q - Q.leadingCoeff • P with hT
  have hT' : AzPolynomial.toPoly T ≠ 0 := toPoly_ne_zero hne
  -- degree bound ≤ deg P
  have hle : (AzPolynomial.toPoly T).natDegree ≤ P.natDegree := by
    rw [hT, toPoly_pre_step]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [AzPolynomial.natDegree_toPoly]; omega
    · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [AzPolynomial.natDegree_toPoly]
  -- the coefficient at `deg P` vanishes
  have hcoeff : (AzPolynomial.toPoly T).coeff P.natDegree = 0 := by
    rw [hT, toPoly_pre_step, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul]
    have h1 : (AzPolynomial.toPoly Q).coeff P.natDegree
        = (AzPolynomial.toPoly Q).leadingCoeff := by
      rw [Polynomial.leadingCoeff, AzPolynomial.natDegree_toPoly, hdeq]
    have h2 : (AzPolynomial.toPoly P).coeff P.natDegree
        = (AzPolynomial.toPoly P).leadingCoeff := by
      rw [Polynomial.leadingCoeff, AzPolynomial.natDegree_toPoly]
    rw [h1, h2, leadingCoeff_toPoly, leadingCoeff_toPoly]
    ring
  have hnd : (AzPolynomial.toPoly T).natDegree ≠ P.natDegree := by
    intro h
    have := Polynomial.leadingCoeff_ne_zero.mpr hT'
    rw [Polynomial.leadingCoeff, h] at this
    exact this hcoeff
  have := AzPolynomial.natDegree_toPoly T
  omega

set_option maxHeartbeats 800000 in
/-- **Equivalence with `Polynomial.gcd` (field case).**
`toPoly (gcdMonic P Q) = gcd (toPoly P) (toPoly Q)`, the Mathlib
`NormalizedGCDMonoid` gcd of `K[X]`, for all `P, Q`. -/
theorem toPoly_gcdMonic (P Q : AzPolynomial K) :
    AzPolynomial.toPoly (gcdMonic P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
  rw [gcdMonic]
  by_cases h00 : P = 0 ∧ Q = 0
  · rw [ite_eq_left h00]
    obtain ⟨rfl, rfl⟩ := h00
    rw [toPoly_zero, gcd_zero_right, normalize_zero]
  rw [ite_eq_right h00]
  by_cases hP0 : P = 0
  · have hQ0 : Q ≠ 0 := fun h => h00 ⟨hP0, h⟩
    rw [ite_eq_left hP0, hP0, toPoly_zero, toPoly_monicize Q hQ0, gcd_zero_left]
  rw [ite_eq_right hP0]
  by_cases hQ0 : Q = 0
  · rw [ite_eq_left hQ0, hQ0, toPoly_zero, toPoly_monicize P hP0, gcd_zero_right]
  rw [ite_eq_right hQ0]
  have hP' := toPoly_ne_zero hP0
  have hQ' := toPoly_ne_zero hQ0
  by_cases hd0 : P.natDegree = 0 ∨ Q.natDegree = 0
  · rw [ite_eq_left hd0, toPoly_one]
    rcases hd0 with h | h
    · exact (gcd_isUnit_left (isUnit_toPoly_of_natDegree_eq_zero hP0 h)).symm
    · exact (gcd_isUnit_right (isUnit_toPoly_of_natDegree_eq_zero hQ0 h)).symm
  rw [ite_eq_right hd0]
  push Not at hd0
  obtain ⟨hPd0, hQd0⟩ := hd0
  have hlcP : P.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP'
  have hlcQ : Q.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ'
  by_cases hdeq : P.natDegree = Q.natDegree
  · rw [ite_eq_left hdeq]
    have hstep : GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly (preStep P Q))
        = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
      rw [preStep, toPoly_pre_step]
      exact gcd_pre_step _ _ hlcP
    by_cases hT0 : preStep P Q = 0
    · rw [ite_eq_left hT0]
      -- proportional: `C lcP · tpQ = C lcQ · tpP`, so `tpP ∣ tpQ`
      have hprop : Polynomial.C P.leadingCoeff * AzPolynomial.toPoly Q
          = Polynomial.C Q.leadingCoeff * AzPolynomial.toPoly P := by
        have h := congrArg AzPolynomial.toPoly hT0
        rw [preStep, toPoly_pre_step, toPoly_zero, sub_eq_zero] at h
        exact h
      have hdvd : AzPolynomial.toPoly P ∣ AzPolynomial.toPoly Q := by
        refine ⟨Polynomial.C P.leadingCoeff⁻¹ * Polynomial.C Q.leadingCoeff, ?_⟩
        have h2 := congrArg (fun z => Polynomial.C P.leadingCoeff⁻¹ * z) hprop
        simp only [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlcP,
          Polynomial.C_1, one_mul] at h2
        rw [h2, Polynomial.C_mul]
        ring
      rw [toPoly_monicize P hP0, gcd_eq_normalize_left hdvd]
    rw [ite_eq_right hT0]
    by_cases hTd : (preStep P Q).natDegree = 0
    · rw [ite_eq_left hTd, toPoly_one, ← hstep]
      exact (gcd_isUnit_right (isUnit_toPoly_of_natDegree_eq_zero hT0 hTd)).symm
    · rw [ite_eq_right hTd]
      have hlt : (preStep P Q).natDegree < P.natDegree := by
        rw [preStep]
        exact pre_step_natDegree_lt hP0 hQ0 hdeq (by rw [← preStep]; exact hT0)
      obtain ⟨hassoc, hne⟩ := toPoly_subresGcd_associated P (preStep P Q) hP0 hT0 hlt
        (by omega)
      rw [toPoly_monicize _ hne, ← hstep, ← normalize_gcd,
        normalize_eq_normalize_iff_associated.mpr hassoc]
  rw [ite_eq_right hdeq]
  by_cases hdlt : P.natDegree < Q.natDegree
  · rw [ite_eq_left hdlt]
    obtain ⟨hassoc, hne⟩ := toPoly_subresGcd_associated Q P hQ0 hP0 hdlt (by omega)
    rw [toPoly_monicize _ hne, ← normalize_gcd,
      normalize_eq_normalize_iff_associated.mpr hassoc, gcd_comm]
  · rw [ite_eq_right hdlt]
    obtain ⟨hassoc, hne⟩ := toPoly_subresGcd_associated P Q hP0 hQ0 (by omega) (by omega)
    rw [toPoly_monicize _ hne, ← normalize_gcd,
      normalize_eq_normalize_iff_associated.mpr hassoc]

/-! ### The `GcdImpl` interface over a field -/

/-- **`gcd` (typeclass) computes the `K[X]` gcd.** -/
theorem toPoly_gcd_field (P Q : AzPolynomial K) :
    AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) :=
  toPoly_gcdMonic P Q

/-- **The canonical pair over a field.** The first component is the gcd, and
the second is the exact quotient: `gcd(A, B) · (toPoly snd) = toPoly P`,
unconditionally. -/
theorem gcdGcdFreePart_field_spec (P Q : AzPolynomial K) :
    (gcdGcdFreePart P Q).1 = gcd P Q
    ∧ GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        * AzPolynomial.toPoly (gcdGcdFreePart P Q).2
      = AzPolynomial.toPoly P := by
  set g := gcdMonic P Q with hg
  have hpair : gcdGcdFreePart P Q
      = (g, if g = 0 then 0 else (exactDivQuoRem P g).1) := rfl
  have hgcd : AzPolynomial.toPoly g
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) :=
    toPoly_gcdMonic P Q
  refine ⟨by rw [hpair]; rfl, ?_⟩
  rw [hpair]
  by_cases hg0 : g = 0
  · have hgcd0 : GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) = 0 := by
      rw [← hgcd, hg0, toPoly_zero]
    have hP0 : AzPolynomial.toPoly P = 0 := ((gcd_eq_zero_iff _ _).mp hgcd0).1
    rw [ite_eq_left hg0]
    show GCDMonoid.gcd _ _ * AzPolynomial.toPoly (0 : AzPolynomial K) = _
    rw [hgcd0, zero_mul, hP0]
  · rw [ite_eq_right hg0]
    have hGdvd : AzPolynomial.toPoly g ∣ AzPolynomial.toPoly P := by
      rw [hgcd]
      exact gcd_dvd_left _ _
    obtain ⟨H, hH⟩ := hGdvd
    have hg' : AzPolynomial.toPoly g ≠ 0 := toPoly_ne_zero hg0
    have hquo : AzPolynomial.toPoly ((exactDivQuoRem P g).1) = H := by
      refine toPoly_exactDivQuoRem_fst_of_euclidean P g H 0 hg' ?_ ?_
      · rw [add_zero, hH]
        ring
      · rw [Polynomial.degree_zero]
        exact bot_lt_iff_ne_bot.mpr (fun h => hg' (Polynomial.degree_eq_bot.mp h))
    show GCDMonoid.gcd _ _ * AzPolynomial.toPoly ((exactDivQuoRem P g).1) = _
    rw [hquo, ← hgcd]
    exact hH.symm

/-! ### `ofPoly` directions -/

/-- **`ofPoly` version of the field equivalence**: pulling two `K[X]`
polynomials back and taking the computable gcd represents Mathlib's gcd. -/
theorem ofPoly_gcd_field (p q : K[X]) :
    gcd (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q)
      = AzPolynomial.ofPoly (GCDMonoid.gcd p q) := by
  apply toPoly_inj.mp
  rw [toPoly_gcd_field, toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

/-- **`ofPoly` version of the canonical pair**: the gcd together with the
exact (Euclidean) quotient `p / gcd p q`. -/
theorem ofPoly_gcdGcdFreePart_field (p q : K[X]) :
    gcdGcdFreePart (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q)
      = (AzPolynomial.ofPoly (GCDMonoid.gcd p q),
         AzPolynomial.ofPoly (p / GCDMonoid.gcd p q)) := by
  obtain ⟨h1, h2⟩ := gcdGcdFreePart_field_spec (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q)
  rw [toPoly_ofPoly, toPoly_ofPoly] at h2
  refine Prod.ext ?_ ?_
  · rw [h1]
    exact ofPoly_gcd_field p q
  · apply toPoly_inj.mp
    rw [toPoly_ofPoly]
    by_cases hg : GCDMonoid.gcd p q = 0
    · have h6 : gcdMonic (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q) = 0 := by
        apply toPoly_inj.mp
        rw [toPoly_gcdMonic, toPoly_ofPoly, toPoly_ofPoly, hg, toPoly_zero]
      have h4 : (gcdGcdFreePart (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q)).2
          = 0 := by
        show (if gcdMonic (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q) = 0
          then (0 : AzPolynomial K)
          else (exactDivQuoRem (AzPolynomial.ofPoly p)
            (gcdMonic (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q))).1) = 0
        rw [ite_eq_left h6]
      rw [h4, toPoly_zero, hg, EuclideanDomain.div_zero]
    · -- cancel the gcd: `snd = p / gcd`
      apply mul_left_cancel₀ hg
      rw [h2, EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left p q)]

end Azurite.AzPolynomial
