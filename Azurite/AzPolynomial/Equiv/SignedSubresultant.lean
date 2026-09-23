/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.SignedSubresultant
import Azurite.AzPolynomial.Equiv.SMul
import Azurite.AzPolynomial.Equiv.ExactDiv
import Azurite.AzPolynomial.Equiv.QuoRem
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Theorem_8_34
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_46
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_38
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Lemma_8_43
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Theorem_8_51

/-!
# Correctness foundations for `signedSubresultant` (BPR Algorithm 8.21)

This file proves the `toPoly` bridges for the three primitives the algorithm is built from
(`epsilonSign`, `divByRingElt`, `remExact`).  Each translates one computational operation into the
abstract `Polynomial`-level operation it realizes:

* `epsilonSign_eq`     — `epsilonSign n = (-1)^{n(n-1)/2}` (the reversal sign `ε_n`);
* `toPoly_divByRingElt` — over a field, dividing every coefficient by `c` is `C(c⁻¹) • (-)`;
* `toPoly_remExact_add` — `remExact A B` is a genuine Euclidean remainder: `A = quo·B + remExact`.

These are the per-step ingredients of the full correctness theorem (`signedSubresultant` agrees with
`Azurite.BPR.Chapter8.sResP` after `toPoly`), whose remaining content is the Theorem 8.34 induction
over the subresultant-degree recursion.
-/

namespace Azurite.AzPolynomial

open Polynomial

/-- **`epsilonSign` is the reversal sign `ε_n = (-1)^{n(n-1)/2}`.**  The `if`-on-parity definition
    agrees with the integer power that appears in Notation 8.33. -/
theorem epsilonSign_eq {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R] (n : ℕ) :
    (epsilonSign n : R) = (-1) ^ (n * (n - 1) / 2) := by
  unfold epsilonSign
  rcases Nat.even_or_odd (n * (n - 1) / 2) with he | ho
  · rw [ite_eq_left (Nat.even_iff.mp he), he.neg_one_pow]
  · rw [ite_eq_right (by rw [Nat.odd_iff.mp ho]; decide), ho.neg_one_pow]

/-- Over a field, `divByRingElt c` is scalar multiplication by `c⁻¹`. -/
theorem divByRingElt_eq_smul {K : Type _} [Field K] [DecidableEq K] (c : K) (p : AzPolynomial K) :
    divByRingElt c p = c⁻¹ • p := by
  have hfun : (fun x : K => Azurite.ExactDiv.exactDiv x c) = (fun x : K => c⁻¹ • x) := by
    funext x
    show x / c = c⁻¹ • x
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  show normalize (p.coeffs.map (fun x => Azurite.ExactDiv.exactDiv x c)) = c⁻¹ • p
  rw [hfun]
  rfl

/-- **`divByRingElt` bridge (field):** coefficient-wise division by `c` is `C(c⁻¹) · (-)`. -/
theorem toPoly_divByRingElt {K : Type _} [Field K] [DecidableEq K] (c : K) (p : AzPolynomial K) :
    AzPolynomial.toPoly (divByRingElt c p) = Polynomial.C c⁻¹ * AzPolynomial.toPoly p := by
  rw [divByRingElt_eq_smul, toPoly_smul, Polynomial.smul_eq_C_mul]

/-- **`remExact` is a Euclidean remainder:** `A = quo · B + remExact A B` at the `Polynomial`
    level, where `quo = (exactDivQuoRem A B).1`.  (Immediate from `toPoly_exactDivQuoRem_eq`, since
    `remExact A B = (exactDivQuoRem A B).2`.) -/
theorem toPoly_remExact_add {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]
    (A B : AzPolynomial R) :
    AzPolynomial.toPoly A
      = AzPolynomial.toPoly (exactDivQuoRem A B).1 * AzPolynomial.toPoly B
        + AzPolynomial.toPoly (remExact A B) :=
  toPoly_exactDivQuoRem_eq A B

/-- Over a field, `remExact` is the Euclidean remainder `rem` — `exactDivQuoRem` and `quoRem` are
    the same fold, since the field `ExactDiv` instance is `(· / ·)`. -/
theorem remExact_eq_rem {K : Type _} [Field K] [DecidableEq K] (A B : AzPolynomial K) :
    remExact A B = rem A B := rfl

/-- **`remExact` bridge (field):** `toPoly (remExact A B) = toPoly A % toPoly B`. -/
theorem toPoly_remExact {K : Type _} [Field K] [DecidableEq K] (A B : AzPolynomial K)
    (hB : AzPolynomial.toPoly B ≠ 0) :
    AzPolynomial.toPoly (remExact A B) = AzPolynomial.toPoly A % AzPolynomial.toPoly B := by
  rw [remExact_eq_rem]; exact toPoly_rem A B hB

/-- **`divByRingElt` bridge (domain).**  Over an integral domain, if `c · r = toPoly p` for some
    target polynomial `r` (so `c` divides every coefficient of `p`, the exactness witness), then
    `divByRingElt c p` realizes the exact quotient: `toPoly (divByRingElt c p) = r`.  This is the
    fraction-free replacement for `toPoly_divByRingElt` — no field inverse, the divisibility is
    supplied externally (here, by the Structure-Theorem recurrence). -/
theorem toPoly_divByRingElt_of_smul {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (c : D) (hc : c ≠ 0) (p : AzPolynomial D) (r : Polynomial D)
    (hr : Polynomial.C c * r = AzPolynomial.toPoly p) :
    AzPolynomial.toPoly (divByRingElt c p) = r := by
  have hdvd : ∀ i, c ∣ p.coeff i := by
    intro i
    rw [← coeff_toPoly_eq, ← hr, Polynomial.coeff_C_mul]
    exact dvd_mul_right c (r.coeff i)
  have hkey : Polynomial.C c * AzPolynomial.toPoly (divByRingElt c p) = AzPolynomial.toPoly p := by
    ext i
    rw [Polynomial.coeff_C_mul, coeff_toPoly_eq, coeff_toPoly_eq]
    show c * (divByRingElt c p).coeff i = p.coeff i
    unfold divByRingElt
    rw [coeff_normalize, Array.getElem?_map]
    show c * (Option.map (fun x => Azurite.ExactDiv.exactDiv x c) p.coeffs[i]?).getD 0
      = (p.coeffs[i]?).getD 0
    cases h : p.coeffs[i]? with
    | none => simp
    | some v =>
      simp only [Option.map_some, Option.getD_some]
      have hdvdv : c ∣ v := by
        have := hdvd i; rwa [show p.coeff i = v by rw [coeff, h]; rfl] at this
      rw [mul_comm]
      exact Azurite.ExactDiv.exactDiv_mul_self v c hdvdv hc
  rw [← hr] at hkey
  exact mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hc) hkey

/-- **Round-trip for `divByRingElt`** (exact case).  If `c` divides every coefficient of `p`, then
    `C(c) · toPoly (divByRingElt c p) = toPoly p`. -/
theorem C_mul_toPoly_divByRingElt {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (c : D) (hc : c ≠ 0) (p : AzPolynomial D) (hdvd : ∀ i, c ∣ p.coeff i) :
    Polynomial.C c * AzPolynomial.toPoly (divByRingElt c p) = AzPolynomial.toPoly p := by
  ext i
  rw [Polynomial.coeff_C_mul, coeff_toPoly_eq, coeff_toPoly_eq]
  show c * (divByRingElt c p).coeff i = p.coeff i
  unfold divByRingElt
  rw [coeff_normalize, Array.getElem?_map]
  show c * (Option.map (fun x => Azurite.ExactDiv.exactDiv x c) p.coeffs[i]?).getD 0
    = (p.coeffs[i]?).getD 0
  cases h : p.coeffs[i]? with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some]
    have hdvdv : c ∣ v := by
      have := hdvd i; rwa [show p.coeff i = v by rw [coeff, h]; rfl] at this
    rw [mul_comm]
    exact Azurite.ExactDiv.exactDiv_mul_self v c hdvdv hc

/-- **Fraction-free remainder identification via descent.**  When the dividend `A` is scaled so that
    `lcof(B)^M ∣` every coefficient (`M` = number of synthetic-division steps), the synthetic
    remainder is exact (degree `< deg B`, by `degree_exactDivQuoRem_snd_lt_of_pow_dvd`).  If moreover
    over the fraction field that integral Euclidean division agrees with a target `R`
    (`map A = QK·map B + map R`), then by uniqueness of Euclidean division over `Frac D` and
    injectivity of `Polynomial.map`, `toPoly (remExact A B) = R` over `D`.  This is the boundary
    counterpart of the cofactor-recurrence route (`sResP_cofactor_recurrence`), used where `i-1 > q`. -/
theorem toPoly_remExact_descent {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (A B : AzPolynomial D) (R : Polynomial D) (QK : Polynomial (FractionRing D))
    (hB : AzPolynomial.toPoly B ≠ 0) (hsize : B.coeffs.size ≤ A.coeffs.size)
    (hpow : ∀ idx, B.leadingCoeff ^ (A.coeffs.size - B.coeffs.size + 1) ∣ A.coeff idx)
    (hdeg : R.degree < (AzPolynomial.toPoly B).degree)
    (hKdiv : (AzPolynomial.toPoly A).map (algebraMap D (FractionRing D))
        = QK * (AzPolynomial.toPoly B).map (algebraMap D (FractionRing D))
          + R.map (algebraMap D (FractionRing D))) :
    AzPolynomial.toPoly (remExact A B) = R := by
  set f := algebraMap D (FractionRing D) with hf_def
  have hf : Function.Injective f := IsFractionRing.injective D (FractionRing D)
  have hdegD : (AzPolynomial.toPoly (remExact A B)).degree < (AzPolynomial.toPoly B).degree :=
    degree_exactDivQuoRem_snd_lt_of_pow_dvd A B hB hsize hpow
  have hmapA : (AzPolynomial.toPoly A).map f
      = (AzPolynomial.toPoly (exactDivQuoRem A B).1).map f * (AzPolynomial.toPoly B).map f
        + (AzPolynomial.toPoly (remExact A B)).map f := by
    rw [toPoly_remExact_add A B, Polynomial.map_add, Polynomial.map_mul]
  have hdivdvd : (AzPolynomial.toPoly B).map f
      ∣ ((AzPolynomial.toPoly (remExact A B)).map f - R.map f) :=
    ⟨QK - (AzPolynomial.toPoly (exactDivQuoRem A B).1).map f, by
      have hcombine := hmapA.symm.trans hKdiv; linear_combination hcombine⟩
  have hzero : (AzPolynomial.toPoly (remExact A B)).map f - R.map f = 0 := by
    by_contra hne
    have h1 := Polynomial.degree_le_of_dvd hdivdvd hne
    have h2 : ((AzPolynomial.toPoly (remExact A B)).map f - R.map f).degree
        < (AzPolynomial.toPoly B).degree := by
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · rw [Polynomial.degree_map_eq_of_injective hf]; exact hdegD
      · rw [Polynomial.degree_map_eq_of_injective hf]; exact hdeg
    rw [Polynomial.degree_map_eq_of_injective hf] at h1
    exact absurd h1 (not_le.mpr h2)
  exact Polynomial.map_injective f hf (by rw [← sub_eq_zero]; exact hzero)

/-- **Domain step bridge.**  Given the integral Euclidean division `C d · toPoly Si = QD·toPoly Sj + R`
    (the cleared-denominator recurrence `transC_spec`, descended to `D`) with `deg R < deg (toPoly Sj)`,
    and the exactness witness `C c · S = −R` (`c = s_j·t_{i-1}`, `S = sResP_{k-1}`), the algorithm's
    `Skm1 = divByRingElt c (−remExact (d•Si) Sj)` realizes `S` over the domain — fraction-free, no
    inverse.  Composes the two M5 linchpins. -/
theorem toPoly_Skm1_eq_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (Si Sj : AzPolynomial D) (c d : D) (QD R S : Polynomial D)
    (hc : c ≠ 0) (hSj_ne : AzPolynomial.toPoly Sj ≠ 0)
    (hdiv : Polynomial.C d * AzPolynomial.toPoly Si = QD * AzPolynomial.toPoly Sj + R)
    (hdeg : R.degree < (AzPolynomial.toPoly Sj).degree) (hcR : Polynomial.C c * S = -R) :
    AzPolynomial.toPoly (divByRingElt c (-(remExact (d • Si) Sj))) = S := by
  have hlin : AzPolynomial.toPoly (remExact (d • Si) Sj) = R := by
    show AzPolynomial.toPoly (exactDivQuoRem (d • Si) Sj).2 = R
    apply toPoly_exactDivQuoRem_snd_of_euclidean (d • Si) Sj QD R hSj_ne _ hdeg
    rw [toPoly_smul, Polynomial.smul_eq_C_mul]
    exact hdiv
  apply toPoly_divByRingElt_of_smul c hc (-(remExact (d • Si) Sj)) S
  rw [toPoly_neg, hlin]
  exact hcR

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Combined domain step bridge.**  Assembling `sResP_cofactor_recurrence` (the Bézout recurrence)
    and `toPoly_Skm1_eq_domain` (the linchpins): with `C c = det(B_{i,j})`, `C d = det(B_{j,k})`
    (the caller discharges these via `det_cofactorMat_domain` from the coefficient invariants), the
    recursion's `Skm1 = divByRingElt c (−remExact (d•Si) Sj)` realizes `sResP_{k-1}` over `D`. -/
theorem toPoly_Skm1_eq_sResP_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (Si Sj : AzPolynomial D) (c d : D) {i j k : ℕ}
    (hSi : AzPolynomial.toPoly Si = sResP P Q (i - 1))
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hcC : Polynomial.C c = (cofactorMat P Q i j).det)
    (hdC : Polynomial.C d = (cofactorMat P Q j k).det)
    (hi1 : i - 1 ≤ Q.natDegree) (hj1 : j - 1 ≤ Q.natDegree) (hk1 : k - 1 ≤ Q.natDegree)
    (hc_ne : c ≠ 0) (hSj_ne : sResP P Q (j - 1) ≠ 0)
    (hdegj : (sResP P Q (j - 1)).natDegree = k) (hk1' : 1 ≤ k) :
    AzPolynomial.toPoly (divByRingElt c (-(remExact (d • Si) Sj))) = sResP P Q (k - 1) := by
  apply toPoly_Skm1_eq_domain Si Sj c d
    (sResU P Q (i - 1) * sResV P Q (k - 1) - sResV P Q (i - 1) * sResU P Q (k - 1))
    (-(Polynomial.C c * sResP P Q (k - 1))) (sResP P Q (k - 1)) hc_ne
    (by rw [hSj]; exact hSj_ne)
  · -- hdiv : `C d * toPoly Si = QD * toPoly Sj + R`
    rw [hSi, hSj, hdC, hcC]
    have hrec := sResP_cofactor_recurrence P Q hQ hpq hi1 hj1 hk1
    rw [hrec]; ring
  · -- hdeg : `R.degree < (toPoly Sj).degree`
    rw [hSj, Polynomial.degree_neg]
    have h3 : (sResP P Q (j - 1)).degree = (k : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hSj_ne, hdegj]
    rw [h3]
    have hCmul : (Polynomial.C c * sResP P Q (k - 1)).degree ≤ (sResP P Q (k - 1)).degree := by
      calc (Polynomial.C c * sResP P Q (k - 1)).degree
          ≤ (Polynomial.C c).degree + (sResP P Q (k - 1)).degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + (sResP P Q (k - 1)).degree := add_le_add (Polynomial.degree_C_le (a := c)) le_rfl
        _ = (sResP P Q (k - 1)).degree := zero_add _
    refine lt_of_le_of_lt hCmul ?_
    refine lt_of_le_of_lt (sResP_degree_le P Q hpq (by omega)) ?_
    exact_mod_cast (by omega : k - 1 < k)
  · -- hcR : `C c * S = -R`
    rw [neg_neg]

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Defective `Spk` domain bridge** (`j ≤ q`).  The algorithm's gap-bottom output
    `Spk = divByRingElt t_{j-1} (s_k • Sj)` (with the closed-form `s_k`) realizes `sResP_k` over the
    domain.  Uses the descended scalar identity (`sRes_block_identity_domain`, giving `s_k = sRes_k`
    by exact division) and the cleared proportionality (`sResP_clear_domain`). -/
theorem toPoly_Spk_eq_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    {j k : ℕ} (hjq : j ≤ Q.natDegree) (hj1 : 1 ≤ j) (hjnd : (sResP P Q j).natDegree = j)
    (Sj : AzPolynomial D) {sj : D} (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) (_hjk : 1 ≤ j - k)
    (hsj : sj = Azurite.BPR.Chapter4.sRes P Q j) (hsjne : sj ≠ 0) :
    AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1))) • Sj))
      = sResP P Q k := by
  have htj : Sj.leadingCoeff = (sResP P Q (j - 1)).leadingCoeff := by rw [← leadingCoeff_toPoly, hSj]
  have htjne : Sj.leadingCoeff ≠ 0 := by rw [htj]; exact Polynomial.leadingCoeff_ne_zero.mpr hk0
  have hA := sRes_block_identity_domain P Q hP hQ hpq hjq hj1 hjnd hk0 hkdeg
  have heps : (epsilonSign (j - k) : D) = (-1 : D) ^ ((j - k - 1) * (j - k) / 2) := by
    rw [epsilonSign_eq, Nat.mul_comm (j - k) (j - k - 1)]
  have hsjpow : sj ^ (j - k - 1) ≠ 0 := pow_ne_zero _ hsjne
  have heq : epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k)
      = Azurite.BPR.Chapter4.sRes P Q k * sj ^ (j - k - 1) := by
    rw [heps, htj, ← hA, hsj]
  have hsk : Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
      (sj ^ (j - k - 1)) = Azurite.BPR.Chapter4.sRes P Q k := by
    have hdvd : sj ^ (j - k - 1) ∣ epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k) := by
      rw [heq]; exact dvd_mul_left _ _
    apply mul_right_cancel₀ hsjpow
    rw [Azurite.ExactDiv.exactDiv_mul_self _ _ hdvd hsjpow]; exact heq
  apply toPoly_divByRingElt_of_smul Sj.leadingCoeff htjne _ (sResP P Q k)
  rw [toPoly_smul, Polynomial.smul_eq_C_mul, hSj, hsk, htj]
  exact sResP_clear_domain P Q hP hQ hpq hjq hj1 hk0 hkdeg

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Defective gap-bottom `sResU` bridge** (`j ≤ q`, `k < j-1`).  The cofactor analogue of
    `toPoly_Spk_eq_domain`: the algorithm's `Upk = divByRingElt t_{j-1} (s_k • Uj)` realizes
    `sResU_k`, via `sRes_block_identity_domain` (`s_k = sRes_k`) and the cofactor clearing
    `sResUV_clear_domain`. -/
theorem toPoly_Upk_eq_sResU_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    {j k : ℕ} (hjq : j ≤ Q.natDegree) (hj1 : 1 ≤ j) (hjnd : (sResP P Q j).natDegree = j)
    (Sj Uj : AzPolynomial D) {sj : D} (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hUj : AzPolynomial.toPoly Uj = sResU P Q (j - 1)) (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hkj : k < j - 1)
    (hsj : sj = Azurite.BPR.Chapter4.sRes P Q j) (hsjne : sj ≠ 0) :
    AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1))) • Uj))
      = sResU P Q k := by
  have htj : Sj.leadingCoeff = (sResP P Q (j - 1)).leadingCoeff := by rw [← leadingCoeff_toPoly, hSj]
  have htjne : Sj.leadingCoeff ≠ 0 := by rw [htj]; exact Polynomial.leadingCoeff_ne_zero.mpr hk0
  have hA := sRes_block_identity_domain P Q hP hQ hpq hjq hj1 hjnd hk0 hkdeg
  have heps : (epsilonSign (j - k) : D) = (-1 : D) ^ ((j - k - 1) * (j - k) / 2) := by
    rw [epsilonSign_eq, Nat.mul_comm (j - k) (j - k - 1)]
  have hsjpow : sj ^ (j - k - 1) ≠ 0 := pow_ne_zero _ hsjne
  have heq : epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k)
      = Azurite.BPR.Chapter4.sRes P Q k * sj ^ (j - k - 1) := by
    rw [heps, htj, ← hA, hsj]
  have hsk : Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
      (sj ^ (j - k - 1)) = Azurite.BPR.Chapter4.sRes P Q k := by
    have hdvd : sj ^ (j - k - 1) ∣ epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k) := by
      rw [heq]; exact dvd_mul_left _ _
    apply mul_right_cancel₀ hsjpow
    rw [Azurite.ExactDiv.exactDiv_mul_self _ _ hdvd hsjpow]; exact heq
  apply toPoly_divByRingElt_of_smul Sj.leadingCoeff htjne _ (sResU P Q k)
  rw [toPoly_smul, Polynomial.smul_eq_C_mul, hUj, hsk, htj]
  exact (sResUV_clear_domain P Q hP hQ hpq hjq hj1 hk0 hkdeg hkj).1

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Defective gap-bottom `sResV` bridge** (`j ≤ q`, `k < j-1`).  The `Q`-cofactor analogue of
    `toPoly_Upk_eq_sResU_domain`, via the second component of `sResUV_clear_domain`. -/
theorem toPoly_Vpk_eq_sResV_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    {j k : ℕ} (hjq : j ≤ Q.natDegree) (hj1 : 1 ≤ j) (hjnd : (sResP P Q j).natDegree = j)
    (Sj Vj : AzPolynomial D) {sj : D} (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hVj : AzPolynomial.toPoly Vj = sResV P Q (j - 1)) (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hkj : k < j - 1)
    (hsj : sj = Azurite.BPR.Chapter4.sRes P Q j) (hsjne : sj ≠ 0) :
    AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1))) • Vj))
      = sResV P Q k := by
  have htj : Sj.leadingCoeff = (sResP P Q (j - 1)).leadingCoeff := by rw [← leadingCoeff_toPoly, hSj]
  have htjne : Sj.leadingCoeff ≠ 0 := by rw [htj]; exact Polynomial.leadingCoeff_ne_zero.mpr hk0
  have hA := sRes_block_identity_domain P Q hP hQ hpq hjq hj1 hjnd hk0 hkdeg
  have heps : (epsilonSign (j - k) : D) = (-1 : D) ^ ((j - k - 1) * (j - k) / 2) := by
    rw [epsilonSign_eq, Nat.mul_comm (j - k) (j - k - 1)]
  have hsjpow : sj ^ (j - k - 1) ≠ 0 := pow_ne_zero _ hsjne
  have heq : epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k)
      = Azurite.BPR.Chapter4.sRes P Q k * sj ^ (j - k - 1) := by
    rw [heps, htj, ← hA, hsj]
  have hsk : Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
      (sj ^ (j - k - 1)) = Azurite.BPR.Chapter4.sRes P Q k := by
    have hdvd : sj ^ (j - k - 1) ∣ epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k) := by
      rw [heq]; exact dvd_mul_left _ _
    apply mul_right_cancel₀ hsjpow
    rw [Azurite.ExactDiv.exactDiv_mul_self _ _ hdvd hsjpow]; exact heq
  apply toPoly_divByRingElt_of_smul Sj.leadingCoeff htjne _ (sResV P Q k)
  rw [toPoly_smul, Polynomial.smul_eq_C_mul, hVj, hsk, htj]
  exact (sResUV_clear_domain P Q hP hQ hpq hjq hj1 hk0 hkdeg hkj).2

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Domain defective step bundle** (`j ≤ q`): `Spk = sResP_k`, `sk = sRes_k`, and
    `deg sResP_k = k`.  The domain analogue of `def_step`, via `toPoly_Spk_eq_domain` (gap-bottom
    polynomial), `sRes_block_identity_domain` (`sk = sRes_k`), and `sResP_clear_domain` (degree). -/
theorem def_step_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D] [IsDomain D]
    (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) {j k : ℕ}
    (hjq : j ≤ Q.natDegree) (hj1 : 1 ≤ j) (Sj : AzPolynomial D) {sj : D}
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1)) (hsResPne : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hjnd : (sResP P Q j).natDegree = j)
    (hsj : sj = Azurite.BPR.Chapter4.sRes P Q j) (hkj : k < j - 1) :
    AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1))) • Sj)) = sResP P Q k
      ∧ Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1)) = Azurite.BPR.Chapter4.sRes P Q k
      ∧ (sResP P Q k).natDegree = k := by
  have hsResPj_ne : sResP P Q j ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hjnd; omega
  have hsjne : sj ≠ 0 := by
    rw [hsj]; exact (isNonDefective_iff_sRes_ne_zero P Q hpq hjq).mp
      (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsResPj_ne, hjnd])
  have htj : Sj.leadingCoeff = (sResP P Q (j - 1)).leadingCoeff := by rw [← leadingCoeff_toPoly, hSj]
  have htjne : Sj.leadingCoeff ≠ 0 := by rw [htj]; exact Polynomial.leadingCoeff_ne_zero.mpr hsResPne
  -- `sk = sRes_k`
  have hA := sRes_block_identity_domain P Q hP hQ hpq hjq hj1 hjnd hsResPne hkdeg
  have heps : (epsilonSign (j - k) : D) = (-1 : D) ^ ((j - k - 1) * (j - k) / 2) := by
    rw [epsilonSign_eq, Nat.mul_comm (j - k) (j - k - 1)]
  have hsjpow : sj ^ (j - k - 1) ≠ 0 := pow_ne_zero _ hsjne
  have heq : epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k)
      = Azurite.BPR.Chapter4.sRes P Q k * sj ^ (j - k - 1) := by rw [heps, htj, ← hA, hsj]
  have hsksRes : Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
      (sj ^ (j - k - 1)) = Azurite.BPR.Chapter4.sRes P Q k := by
    have hdvd : sj ^ (j - k - 1) ∣ epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k) := by
      rw [heq]; exact dvd_mul_left _ _
    apply mul_right_cancel₀ hsjpow
    rw [Azurite.ExactDiv.exactDiv_mul_self _ _ hdvd hsjpow]; exact heq
  have hSpk := toPoly_Spk_eq_domain P Q hP hQ hpq hjq hj1 hjnd Sj hSj hsResPne hkdeg (by omega)
    hsj hsjne
  -- `deg sResP_k = k` from the cleared proportionality
  have hskne : Azurite.BPR.Chapter4.sRes P Q k ≠ 0 := by
    have hlhs : epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k) ≠ 0 :=
      mul_ne_zero (by unfold epsilonSign; split <;> norm_num) (pow_ne_zero _ htjne)
    rw [heq] at hlhs
    exact left_ne_zero_of_mul hlhs
  have hndk : (sResP P Q k).natDegree = k := by
    have hcl := sResP_clear_domain P Q hP hQ hpq hjq hj1 hsResPne hkdeg
    have hcc := congrArg Polynomial.natDegree hcl
    rwa [Polynomial.natDegree_C_mul (Polynomial.leadingCoeff_ne_zero.mpr hsResPne),
      Polynomial.natDegree_C_mul hskne, hkdeg] at hcc
  exact ⟨hSpk, hsksRes, hndk⟩

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Defective `Spk` bridge, `j = p` case (first call).**  Over the domain, via Notation 8.33
    (`sResP_q = ε·b_q^{p-q-1}·Q`, `sResP_eq_of_natDegree`, `CommRing`) and the `s_j = 1` convention —
    no descent, no field inverse. -/
theorem toPoly_Spk_eq_of_eq_p_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hgap : Q.natDegree + 1 < P.natDegree) (hQ : Q ≠ 0) {j k : ℕ}
    (hjp : j = P.natDegree) (hk : k = Q.natDegree) (Sj : AzPolynomial D) {sj : D}
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1)) (hsj : sj = 1) (_hjk : 1 ≤ j - k) :
    AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1))) • Sj)) = sResP P Q k := by
  have hpq : Q.natDegree < P.natDegree := by omega
  have hQeq : AzPolynomial.toPoly Sj = Q := by rw [hSj, hjp, sResP_eq_self_Q P Q hgap]
  have hlc : Sj.leadingCoeff = Q.leadingCoeff := by rw [← leadingCoeff_toPoly, hQeq]
  have htj : Sj.leadingCoeff ≠ 0 := by rw [hlc]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hsk : Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
      (sj ^ (j - k - 1)) = epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k) := by
    rw [hsj, one_pow]
    have := Azurite.ExactDiv.exactDiv_mul_self
      (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k)) 1 (one_dvd _) one_ne_zero
    rwa [mul_one] at this
  apply toPoly_divByRingElt_of_smul Sj.leadingCoeff htj _ (sResP P Q k)
  rw [toPoly_smul, Polynomial.smul_eq_C_mul, hsk, hQeq, hlc, hk, hjp,
    sResP_eq_of_natDegree P Q hpq hQ, ← Int.cast_smul_eq_zsmul D, Polynomial.smul_eq_C_mul,
    ← mul_assoc, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul]
  have htjpow : Q.leadingCoeff * Q.leadingCoeff ^ (P.natDegree - Q.natDegree - 1)
      = Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
    rw [← pow_succ']; congr 1; omega
  congr 2
  rw [epsilonSign_eq, Azurite.BPR.Chapter4.ε]
  push_cast
  rw [mul_right_comm, htjpow]
  ring

/-! ### Abstract step lemma (M2 core)

The recurrence of `theorem_8_34_monolithic` is stated as `C(s_j)·C(t_{i-1})·sResP_{k-1} = -(…)`.
Solved for `sResP_{k-1}`, it has exactly the shape `-divByRingElt(s_j·t_{i-1})(remExact …)` produces
once bridged.  This is the polynomial output of a single recursion step (both branches). -/

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Theorem 8.34 recurrence, solved for `sResP_{k-1}`.**  Over a field, with the denominator
    coefficients nonzero, `sResP_{k-1}` is `-(s_j t_{i-1})⁻¹` times the signed remainder of
    `s_k·t_{j-1}·sResP_{i-1}` by `sResP_{j-1}`. -/
theorem sResP_km1_eq {K : Type _} [Field K] [DecidableEq K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ} (hj1 : 1 ≤ j) (hji : j < i)
    (hip : i ≤ P.natDegree + 1) (hne : sResP P Q (i - 1) ≠ 0)
    (hdeg : (sResP P Q (i - 1)).natDegree = j) {k : ℕ} (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hsj : sBPR P Q j ≠ 0) (hti : tBPR P Q (i - 1) ≠ 0) :
    sResP P Q (k - 1)
      = -(Polynomial.C (sBPR P Q j * tBPR P Q (i - 1))⁻¹
          * ((Polynomial.C (sBPR P Q k) * Polynomial.C (tBPR P Q (j - 1)) * sResP P Q (i - 1))
              % sResP P Q (j - 1))) := by
  obtain ⟨hrec, _⟩ := (theorem_8_34_monolithic P Q hP hQ hpq hq1 hj1 hji hip hne hdeg).2 k hk0 hkdeg
  rw [ite_eq_right (show ¬ k = 0 by omega)] at hrec
  have hsjti : sBPR P Q j * tBPR P Q (i - 1) ≠ 0 := mul_ne_zero hsj hti
  have hrec' : Polynomial.C (sBPR P Q j * tBPR P Q (i - 1)) * sResP P Q (k - 1)
      = -((Polynomial.C (sBPR P Q k) * Polynomial.C (tBPR P Q (j - 1)) * sResP P Q (i - 1))
          % sResP P Q (j - 1)) := by
    rw [Polynomial.C_mul]; exact hrec
  have hCinv : Polynomial.C (sBPR P Q j * tBPR P Q (i - 1))
      * Polynomial.C (sBPR P Q j * tBPR P Q (i - 1))⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hsjti, map_one]
  apply mul_left_cancel₀ (b := sResP P Q (k - 1)) (Polynomial.C_ne_zero.mpr hsjti)
  rw [hrec', mul_neg, ← mul_assoc, hCinv, one_mul]

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Boundary step bridge** (`i - 1 > q`, where the cofactor recurrence does not apply).  Using the
    pseudo-division degree bound (`toPoly_remExact_descent`) and the field recurrence `sResP_km1_eq`
    (valid for `i ≤ deg P + 1`), the recursion's `Skm1 = divByRingElt c (−remExact (d•Si) Sj)`
    realizes `sResP_{k-1}` over `D`.  The caller supplies the dividend-scaling divisibility `hpow`
    and the scalar-image facts tying the carried `D`-scalars `c`, `d` to the field `sBPR`/`tBPR` of
    the mapped polynomials. -/
theorem toPoly_Skm1_eq_sResP_domain_boundary {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    (Si Sj : AzPolynomial D) (c d : D) {i j k : ℕ}
    (hSi : AzPolynomial.toPoly Si = sResP P Q (i - 1))
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hj1 : 1 ≤ j) (hji : j < i) (hip : i ≤ P.natDegree + 1)
    (hdeg : (sResP P Q (i - 1)).natDegree = j) (hne : sResP P Q (i - 1) ≠ 0)
    (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hkq : k ≤ Q.natDegree) (hc_ne : c ≠ 0)
    (hsize : Sj.coeffs.size ≤ (d • Si).coeffs.size)
    (hpow : ∀ idx, Sj.leadingCoeff ^ ((d • Si).coeffs.size - Sj.coeffs.size + 1) ∣ (d • Si).coeff idx)
    (hfd : algebraMap D (FractionRing D) d
        = sBPR (P.map (algebraMap D (FractionRing D))) (Q.map (algebraMap D (FractionRing D))) k
          * tBPR (P.map (algebraMap D (FractionRing D))) (Q.map (algebraMap D (FractionRing D))) (j - 1))
    (hfc : algebraMap D (FractionRing D) c
        = sBPR (P.map (algebraMap D (FractionRing D))) (Q.map (algebraMap D (FractionRing D))) j
          * tBPR (P.map (algebraMap D (FractionRing D))) (Q.map (algebraMap D (FractionRing D))) (i - 1))
    (hsjne : sBPR (P.map (algebraMap D (FractionRing D)))
      (Q.map (algebraMap D (FractionRing D))) j ≠ 0)
    (htine : tBPR (P.map (algebraMap D (FractionRing D)))
      (Q.map (algebraMap D (FractionRing D))) (i - 1) ≠ 0) :
    AzPolynomial.toPoly (divByRingElt c (-(remExact (d • Si) Sj))) = sResP P Q (k - 1) := by
  set f := algebraMap D (FractionRing D) with hf_def
  have hf : Function.Injective f := IsFractionRing.injective D (FractionRing D)
  set PK := P.map f with hPK
  set QK := Q.map f with hQK
  have hPKne : PK ≠ 0 := by rw [hPK, Ne, Polynomial.map_eq_zero_iff hf]; exact hP
  have hQKne : QK ≠ 0 := by rw [hQK, Ne, Polynomial.map_eq_zero_iff hf]; exact hQ
  have hpqK : QK.natDegree < PK.natDegree := by
    rw [hPK, hQK, Polynomial.natDegree_map_eq_of_injective hf,
      Polynomial.natDegree_map_eq_of_injective hf]; exact hpq
  have hq1K : 1 ≤ QK.natDegree := by
    rw [hQK, Polynomial.natDegree_map_eq_of_injective hf]; exact hq1
  have hsResK : ∀ m, sResP PK QK m = (sResP P Q m).map f := fun m => by
    rw [hPK, hQK, sResP_map hf]
  have hneK : sResP PK QK (i - 1) ≠ 0 := by
    rw [hsResK, Ne, Polynomial.map_eq_zero_iff hf]; exact hne
  have hk0K : sResP PK QK (j - 1) ≠ 0 := by
    rw [hsResK, Ne, Polynomial.map_eq_zero_iff hf]; exact hk0
  have hdegK : (sResP PK QK (i - 1)).natDegree = j := by
    rw [hsResK, Polynomial.natDegree_map_eq_of_injective hf]; exact hdeg
  have hkdegK : (sResP PK QK (j - 1)).natDegree = k := by
    rw [hsResK, Polynomial.natDegree_map_eq_of_injective hf]; exact hkdeg
  have hipK : i ≤ PK.natDegree + 1 := by
    rw [hPK, Polynomial.natDegree_map_eq_of_injective hf]; exact hip
  have hrec := sResP_km1_eq PK QK hPKne hQKne hpqK hq1K hj1 hji hipK hneK hdegK hk0K hkdegK hk1
    hsjne htine
  set R : Polynomial D := -(Polynomial.C c * sResP P Q (k - 1)) with hR_def
  have hRdeg : R.degree < (AzPolynomial.toPoly Sj).degree := by
    rw [hSj, hR_def, Polynomial.degree_neg]
    have h3 : (sResP P Q (j - 1)).degree = (k : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hk0, hkdeg]
    rw [h3]
    have hCmul : (Polynomial.C c * sResP P Q (k - 1)).degree ≤ (sResP P Q (k - 1)).degree := by
      calc (Polynomial.C c * sResP P Q (k - 1)).degree
          ≤ (Polynomial.C c).degree + (sResP P Q (k - 1)).degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + (sResP P Q (k - 1)).degree := add_le_add (Polynomial.degree_C_le (a := c)) le_rfl
        _ = (sResP P Q (k - 1)).degree := zero_add _
    refine lt_of_le_of_lt hCmul ?_
    refine lt_of_le_of_lt (sResP_degree_le P Q hpq (by omega)) ?_
    exact_mod_cast (by omega : k - 1 < k)
  have hAKeq : (AzPolynomial.toPoly (d • Si)).map f
      = Polynomial.C (sBPR PK QK k) * Polynomial.C (tBPR PK QK (j - 1)) * sResP PK QK (i - 1) := by
    rw [toPoly_smul, Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C, hfd, hSi,
      ← hsResK, Polynomial.C_mul]
  have hBKeq : (AzPolynomial.toPoly Sj).map f = sResP PK QK (j - 1) := by
    rw [hSj, ← hsResK]
  have hRKeq : R.map f = -(Polynomial.C (f c) * sResP PK QK (k - 1)) := by
    rw [hR_def, Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_C, ← hsResK]
  have hsjti : sBPR PK QK j * tBPR PK QK (i - 1) ≠ 0 := mul_ne_zero hsjne htine
  have hmod : (AzPolynomial.toPoly (d • Si)).map f % (AzPolynomial.toPoly Sj).map f = R.map f := by
    rw [hAKeq, hBKeq, hRKeq, hfc, hrec]
    have huc : Polynomial.C (sBPR PK QK j * tBPR PK QK (i - 1))
        * Polynomial.C (sBPR PK QK j * tBPR PK QK (i - 1))⁻¹ = 1 := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ hsjti, map_one]
    rw [show ∀ u v w : (FractionRing D)[X], -(u * -(v * w)) = u * v * w from
      fun u v w => by ring, huc, one_mul]
  have hrem : AzPolynomial.toPoly (remExact (d • Si) Sj) = R := by
    apply toPoly_remExact_descent (d • Si) Sj R
      ((AzPolynomial.toPoly (d • Si)).map f / (AzPolynomial.toPoly Sj).map f)
      (by rw [hSj]; exact hk0) hsize hpow hRdeg
    have hdam := EuclideanDomain.div_add_mod ((AzPolynomial.toPoly (d • Si)).map f)
      ((AzPolynomial.toPoly Sj).map f)
    rw [hmod] at hdam
    linear_combination -hdam
  apply toPoly_divByRingElt_of_smul c hc_ne (-(remExact (d • Si) Sj)) (sResP P Q (k - 1))
  rw [toPoly_neg, hrem, hR_def, neg_neg]

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Boundary step bridge at `i = p`** (`Si = sResP_{p-1} = Q`, where the matrix cofactor det
    `det(B_{p,q})` is unavailable).  Uses the integral `boundary_recurrence` (Cramer elimination,
    quotient `-sResU_{k-1}`, remainder `sResU_{q-1}·sResP_{k-1}` of degree `< k`) directly through the
    fraction-free linchpin `toPoly_exactDivQuoRem_snd_of_euclidean` — no pseudo-division scaling, which
    is insufficient when `sResP_{q-1}` is itself defective — and `sResU_sub_one_eq` to clear `c`. -/
theorem toPoly_Skm1_eq_sResP_domain_ip {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (Si Sj : AzPolynomial D) (c d : D) {k : ℕ}
    (hSi : AzPolynomial.toPoly Si = Q)
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (Q.natDegree - 1))
    (hk1 : 1 ≤ k) (hkq : k < Q.natDegree) (hne : sResP P Q (Q.natDegree - 1) ≠ 0)
    (hdeg : (sResP P Q (Q.natDegree - 1)).natDegree = k)
    (hsResk : Azurite.BPR.Chapter4.sRes P Q k ≠ 0)
    (hsResq : Azurite.BPR.Chapter4.sRes P Q Q.natDegree ≠ 0)
    (hd : d = Azurite.BPR.Chapter4.sRes P Q k * (sResP P Q (Q.natDegree - 1)).leadingCoeff)
    (hc : c = Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff) :
    AzPolynomial.toPoly (divByRingElt c (-(remExact (d • Si) Sj))) = sResP P Q (k - 1) := by
  have hq1 : 1 ≤ Q.natDegree := by omega
  have hrec := boundary_recurrence P Q hP hQ hpq rfl hk1 hkq hne hdeg hsResk
  have hSjne : AzPolynomial.toPoly Sj ≠ 0 := by rw [hSj]; exact hne
  have hc_ne : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero hsResq (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  have hU0 : (sResU P Q (Q.natDegree - 1)).natDegree = 0 := by
    have := sResU_natDegree_le P Q hpq (show Q.natDegree - 1 ≤ Q.natDegree from by omega); omega
  have hrem : AzPolynomial.toPoly (remExact (d • Si) Sj)
      = sResU P Q (Q.natDegree - 1) * sResP P Q (k - 1) := by
    show AzPolynomial.toPoly (exactDivQuoRem (d • Si) Sj).2 = _
    apply toPoly_exactDivQuoRem_snd_of_euclidean (d • Si) Sj
      (- sResU P Q (k - 1)) (sResU P Q (Q.natDegree - 1) * sResP P Q (k - 1)) hSjne
    · rw [toPoly_smul, Polynomial.smul_eq_C_mul, hSi, hd, hSj, ← hrec]
    · rw [hSj, Polynomial.degree_eq_natDegree hne, hdeg]
      refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      have hUd : (sResU P Q (Q.natDegree - 1)).degree ≤ 0 := by
        refine le_trans Polynomial.degree_le_natDegree ?_; rw [hU0]; rfl
      have hPd : (sResP P Q (k - 1)).degree ≤ ((k - 1 : ℕ) : WithBot ℕ) :=
        sResP_degree_le P Q hpq (by omega)
      calc (sResU P Q (Q.natDegree - 1)).degree + (sResP P Q (k - 1)).degree
          ≤ 0 + ((k - 1 : ℕ) : WithBot ℕ) := add_le_add hUd hPd
        _ < (k : ℕ) := by rw [zero_add]; exact_mod_cast (show k - 1 < k from by omega)
  apply toPoly_divByRingElt_of_smul c hc_ne (-(remExact (d • Si) Sj)) (sResP P Q (k - 1))
  rw [toPoly_neg, hrem, sResU_sub_one_eq P Q hP hQ hpq hq1 hsResq, hc]; ring

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **First-call step bridge** (`i = p+1`, `Si = sResP_p = P`, `Sj = sResP_{p-1} = Q`, denom `= 1`).
    The first division `divByRingElt 1 (−remExact (d•P) Q)` (with `d = s_q·lcof Q`) realizes
    `sResP_{q-1}` over `D`.  Like the `i=p` bridge: the integral division `C(d)·P = sResV_{q-1}·Q −
    sResP_{q-1}` comes straight from the Bézout `sResP_{q-1} = sResU_{q-1}·P + sResV_{q-1}·Q` together
    with `sResU_sub_one_eq` (`sResU_{q-1} = -C(s_q·lcof Q)`), fed to the fraction-free linchpin — no
    pseudo-division scaling needed. -/
theorem toPoly_Skm1_eq_sResP_domain_first {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) (Si Sj : AzPolynomial D) (c d : D)
    (hSi : AzPolynomial.toPoly Si = P) (hSj : AzPolynomial.toPoly Sj = Q)
    (hsResq : Azurite.BPR.Chapter4.sRes P Q Q.natDegree ≠ 0)
    (hd : d = Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff) (hc : c = 1) :
    AzPolynomial.toPoly (divByRingElt c (-(remExact (d • Si) Sj))) = sResP P Q (Q.natDegree - 1) := by
  have hbez : sResP P Q (Q.natDegree - 1)
      = sResU P Q (Q.natDegree - 1) * P + sResV P Q (Q.natDegree - 1) * Q :=
    sResP_eq_cofactor P Q hQ hpq (by omega)
  have hSjne : AzPolynomial.toPoly Sj ≠ 0 := by rw [hSj]; exact hQ
  have hc_ne : c ≠ 0 := by rw [hc]; exact one_ne_zero
  have hrem : AzPolynomial.toPoly (remExact (d • Si) Sj) = - sResP P Q (Q.natDegree - 1) := by
    show AzPolynomial.toPoly (exactDivQuoRem (d • Si) Sj).2 = _
    apply toPoly_exactDivQuoRem_snd_of_euclidean (d • Si) Sj
      (sResV P Q (Q.natDegree - 1)) (- sResP P Q (Q.natDegree - 1)) hSjne
    · rw [toPoly_smul, Polynomial.smul_eq_C_mul, hSi, hd, hSj,
        show Polynomial.C (Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff)
          = - sResU P Q (Q.natDegree - 1) from by
            rw [sResU_sub_one_eq P Q hP hQ hpq hq1 hsResq, neg_neg]]
      linear_combination hbez
    · rw [hSj, Polynomial.degree_neg, Polynomial.degree_eq_natDegree hQ]
      refine lt_of_le_of_lt (sResP_degree_le P Q hpq (by omega)) ?_
      exact_mod_cast (show Q.natDegree - 1 < Q.natDegree from by omega)
  apply toPoly_divByRingElt_of_smul c hc_ne (-(remExact (d • Si) Sj)) (sResP P Q (Q.natDegree - 1))
  rw [toPoly_neg, hrem, hc, map_one, one_mul, neg_neg]

/-- **Defective coefficient match.**  The algorithm's `s_k / t_{j-1}` (with the closed-form
    `s_k = ε_{d}·t_{j-1}^{d}/s_j^{d-1}`, `d = j-k`) equals the constant of Proposition 8.46,
    `(-1)^{(d-1)d/2}·(t_{j-1}/s_j)^{d-1}`. -/
theorem defective_const_eq {K : Type _} [Field K] [DecidableEq K] {tj sj : K}
    (htj : tj ≠ 0) (hsj : sj ≠ 0) {d : ℕ} (hd : 1 ≤ d) :
    (epsilonSign d * tj ^ d / sj ^ (d - 1)) / tj
      = (-1 : K) ^ ((d - 1) * d / 2) * (tj / sj) ^ (d - 1) := by
  rw [epsilonSign_eq, show d * (d - 1) / 2 = (d - 1) * d / 2 from by rw [Nat.mul_comm],
    div_pow, show tj ^ d = tj ^ (d - 1) * tj from by rw [← pow_succ, Nat.sub_add_cancel hd]]
  field_simp

open Azurite.BPR.Chapter8 in
/-- **Step bridge for `sResP_{k-1}`.**  The algorithm's `divByRingElt (s_j t_{i-1})
    (-(remExact (d • Si) Sj))` with `d = s_k t_{j-1}` maps (via `toPoly`) to `sResP_{k-1}`.  Used by
    both branches of `ssAux`. -/
theorem toPoly_Skm1_eq {K : Type _} [Field K] [DecidableEq K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j k : ℕ} (hj1 : 1 ≤ j) (hji : j < i)
    (hip : i ≤ P.natDegree + 1) (Si Sj : AzPolynomial K) {sj ti d : K}
    (hSi : AzPolynomial.toPoly Si = sResP P Q (i - 1))
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hdeg : (sResP P Q (i - 1)).natDegree = j) (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hsj : sj = sBPR P Q j) (hti : ti = tBPR P Q (i - 1)) (hd : d = sBPR P Q k * tBPR P Q (j - 1))
    (hsjne : sBPR P Q j ≠ 0) (htine : tBPR P Q (i - 1) ≠ 0) :
    AzPolynomial.toPoly (divByRingElt (sj * ti) (-(remExact (d • Si) Sj))) = sResP P Q (k - 1) := by
  have hne : sResP P Q (i - 1) ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
  have hSjne : AzPolynomial.toPoly Sj ≠ 0 := by rw [hSj]; exact hk0
  rw [toPoly_divByRingElt, toPoly_neg, toPoly_remExact _ _ hSjne, toPoly_smul, hSi, hSj, hsj, hti,
    hd, Polynomial.smul_eq_C_mul, Polynomial.C_mul, mul_neg,
    sResP_km1_eq P Q hP hQ hpq hq1 hj1 hji hip hne hdeg hk0 hkdeg hk1 hsjne htine]

/-- **`Spk` reduction (uniform).**  The algorithm's `divByRingElt t_{j-1} (s_k • Sj)` (with the
    closed-form `s_k`) maps to `C(c)·toPoly Sj`, where `c = (-1)^{(j-k-1)(j-k)/2}(t_{j-1}/s_j)^{j-k-1}`
    is the constant of Proposition 8.46 / Notation 8.33. -/
theorem toPoly_Spk_reduce {K : Type _} [Field K] [DecidableEq K] (Sj : AzPolynomial K) {sj : K}
    {j k : ℕ} (htj : Sj.leadingCoeff ≠ 0) (hsj : sj ≠ 0) (hjk : 1 ≤ j - k) :
    AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1))) • Sj))
      = Polynomial.C ((-1 : K) ^ ((j - k - 1) * (j - k) / 2)
          * (Sj.leadingCoeff / sj) ^ (j - k - 1)) * AzPolynomial.toPoly Sj := by
  rw [toPoly_divByRingElt, toPoly_smul, Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul]
  congr 2
  rw [mul_comm, ← div_eq_mul_inv]
  exact defective_const_eq htj hsj hjk

open Azurite.BPR.Chapter8 in
/-- **`Spk` bridge, `j ≤ q` case** (Proposition 8.46): the defective `sResP_k` output is correct. -/
theorem toPoly_Spk_eq_of_le_q {K : Type _} [Field K] [DecidableEq K] (P Q : K[X]) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {j k : ℕ}
    (hjq : j ≤ Q.natDegree) (hj1 : 1 ≤ j) (hjnd : (sResP P Q j).natDegree = j) (Sj : AzPolynomial K)
    {sj : K} (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1)) (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hjk : 1 ≤ j - k)
    (hsj : sj = Azurite.BPR.Chapter4.sRes P Q j) (hsjne : sj ≠ 0) :
    AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1))) • Sj))
      = sResP P Q k := by
  have htj : Sj.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly, hSj]; exact Polynomial.leadingCoeff_ne_zero.mpr hk0
  rw [toPoly_Spk_reduce Sj htj hsjne hjk, proposition_8_46 P Q hP hQ hpq hq1 hjq hj1 hjnd hk0 hkdeg,
    hSj, hsj, show Sj.leadingCoeff = (sResP P Q (j - 1)).leadingCoeff from by
      rw [← leadingCoeff_toPoly, hSj]]

open Azurite.BPR.Chapter8 in
/-- **`Spk` bridge, `j = p` case** (Notation 8.33 closed form `sResP_q = ε_{p-q} b_q^{p-q-1} Q`),
    the special first call where `s_j = 1`. -/
theorem toPoly_Spk_eq_of_eq_p {K : Type _} [Field K] [DecidableEq K] (P Q : K[X])
    (hpq : Q.natDegree < P.natDegree) (hQ : Q ≠ 0) {j k : ℕ} (hjp : j = P.natDegree)
    (hk : k = Q.natDegree) (Sj : AzPolynomial K) {sj : K}
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1)) (hsj : sj = 1) (hjk : 1 ≤ j - k) :
    AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1))) • Sj))
      = sResP P Q k := by
  have hQeq : AzPolynomial.toPoly Sj = Q := by rw [hSj, hjp, sResP_pm1_eq_Q P Q hQ hpq]
  have hlc : Sj.leadingCoeff = Q.leadingCoeff := by rw [← leadingCoeff_toPoly, hQeq]
  have htj : Sj.leadingCoeff ≠ 0 := by rw [hlc]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ
  rw [toPoly_Spk_reduce Sj htj (by rw [hsj]; exact one_ne_zero) hjk, hsj, div_one, hlc, hQeq, hk, hjp,
    sResP_eq_of_natDegree P Q hpq hQ, ← Int.cast_smul_eq_zsmul K, smul_eq_C_mul, ← mul_assoc,
    ← Polynomial.C_mul]
  congr 2
  rw [Azurite.BPR.Chapter4.ε]
  push_cast
  rw [Nat.mul_comm (P.natDegree - Q.natDegree - 1) (P.natDegree - Q.natDegree)]

open Azurite.BPR.Chapter8 in
/-- For a non-defective `sResP_m` with `m < p`, the coefficient `s_m = sBPR_m` is its leading
    coefficient (uses `coeff_sResP`, so no `m ≤ q` bound). -/
theorem sBPR_eq_leadingCoeff {K : Type _} [Field K] [DecidableEq K] (P Q : K[X])
    (hpq : Q.natDegree < P.natDegree) {m : ℕ} (hmp : m < P.natDegree)
    (hnd : (sResP P Q m).natDegree = m) :
    sBPR P Q m = (sResP P Q m).leadingCoeff := by
  rw [sBPR, ite_eq_right (by omega), ← coeff_sResP P Q hpq (by omega), Polynomial.leadingCoeff, hnd]

open Azurite.BPR.Chapter8 in
/-- **Defective step facts.**  For a defective transition (`k = deg sResP_{j-1} < j-1`), the
    algorithm's `Spk` maps to `sResP_k`, its scalar `s_k` is `sRes_k`, and `sResP_k` is
    non-defective.  Bundled because cases 3 & 4 of the assembly both need all three. -/
theorem def_step {K : Type _} [Field K] [DecidableEq K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {j k : ℕ} (hj1 : 1 ≤ j)
    (hjcase : j ≤ Q.natDegree ∨ j = P.natDegree) (Sj : AzPolynomial K) {sj : K}
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1)) (hsResPne : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hjnd : (sResP P Q j).natDegree = j)
    (hsj : sj = sBPR P Q j) (hkj : k < j - 1) :
    AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1))) • Sj)) = sResP P Q k
      ∧ Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
          (sj ^ (j - k - 1)) = Azurite.BPR.Chapter4.sRes P Q k
      ∧ (sResP P Q k).natDegree = k := by
  set sk := Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k))
    (sj ^ (j - k - 1)) with hsk_def
  have htj : Sj.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly, hSj]; exact Polynomial.leadingCoeff_ne_zero.mpr hsResPne
  have hsjne : sj ≠ 0 := by
    rw [hsj]
    rcases hjcase with hjq | hjp
    · exact sBPR_ne_of_nondef P Q hpq hjq
        (by intro h; rw [h, Polynomial.natDegree_zero] at hjnd; omega) hjnd
    · rw [hjp, sBPR, ite_eq_left rfl]; exact one_ne_zero
  have hjk1 : 1 ≤ j - k := by omega
  have hSpk : AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff (sk • Sj)) = sResP P Q k := by
    rcases hjcase with hjq | hjp
    · exact toPoly_Spk_eq_of_le_q P Q hP hQ hpq hq1 hjq hj1 hjnd Sj hSj hsResPne hkdeg hjk1
        (by rw [hsj, sBPR, ite_eq_right (by omega)]) hsjne
    · have hkq : k = Q.natDegree := by
        have h := hkdeg; rw [hjp, sResP_pm1_eq_Q P Q hQ hpq] at h; omega
      exact toPoly_Spk_eq_of_eq_p P Q hpq hQ hjp hkq Sj hSj
        (by rw [hsj, hjp, sBPR, ite_eq_left rfl]) hjk1
  have hSpk_form : AzPolynomial.toPoly (divByRingElt Sj.leadingCoeff (sk • Sj))
      = Polynomial.C (sk * Sj.leadingCoeff⁻¹) * AzPolynomial.toPoly Sj := by
    rw [toPoly_divByRingElt, toPoly_smul, Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul,
      mul_comm Sj.leadingCoeff⁻¹ sk]
  have hskne : sk ≠ 0 := by
    rw [hsk_def]
    show (epsilonSign (j - k) * Sj.leadingCoeff ^ (j - k)) / sj ^ (j - k - 1) ≠ 0
    exact div_ne_zero (mul_ne_zero (by unfold epsilonSign; split <;> norm_num) (pow_ne_zero _ htj))
      (pow_ne_zero _ hsjne)
  have hndk : (sResP P Q k).natDegree = k := by
    rw [← hSpk, hSpk_form, Polynomial.natDegree_C_mul (mul_ne_zero hskne (inv_ne_zero htj)),
      AzPolynomial.natDegree_toPoly, ← AzPolynomial.natDegree_toPoly, hSj, hkdeg]
  have hsksRes : sk = Azurite.BPR.Chapter4.sRes P Q k := by
    rw [show Azurite.BPR.Chapter4.sRes P Q k = sBPR P Q k from by rw [sBPR, ite_eq_right (by omega)],
      sBPR_eq_leadingCoeff P Q hpq (by omega) hndk, ← hSpk, hSpk_form, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C, leadingCoeff_toPoly, mul_assoc, inv_mul_cancel₀ htj, mul_one]
  exact ⟨hSpk, hsksRes, hndk⟩

open Azurite.BPR.Chapter8 in
/-- The spec target: the descending list of `(sResP_ℓ, sRes_ℓ)` for `ℓ = j-1, …, 0`, defined by
    the cons recursion that mirrors `ssAux`. -/
noncomputable def targetList {K : Type _} [CommRing K] (P Q : K[X]) : ℕ → List (K[X] × K)
  | 0 => []
  | j + 1 => (sResP P Q j, Azurite.BPR.Chapter4.sRes P Q j) :: targetList P Q j

open Azurite.BPR.Chapter8 in
/-- `targetList` cons step (definitional). -/
theorem targetList_succ {K : Type _} [CommRing K] (P Q : K[X]) (j : ℕ) :
    targetList P Q (j + 1)
      = (sResP P Q j, Azurite.BPR.Chapter4.sRes P Q j) :: targetList P Q j := rfl

open Azurite.BPR.Chapter8 in
/-- `sRes_ℓ = 0` whenever `sResP_ℓ = 0` (for `ℓ ≤ p`). -/
theorem sRes_eq_zero_of_sResP {K : Type _} [CommRing K] [DecidableEq K] (P Q : K[X])
    (hpq : Q.natDegree < P.natDegree) {ℓ : ℕ} (hℓ : ℓ ≤ P.natDegree) (h : sResP P Q ℓ = 0) :
    Azurite.BPR.Chapter4.sRes P Q ℓ = 0 := by
  rw [← coeff_sResP P Q hpq hℓ, h, Polynomial.coeff_zero]

open Azurite.BPR.Chapter8 in
/-- When `sResP_ℓ = 0` for all `ℓ < j` (the gcd-termination branch of Theorem 8.34), the target
    list collapses to all-zero pairs. -/
theorem targetList_eq_replicate {K : Type _} [CommRing K] [DecidableEq K] (P Q : K[X])
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hjp : j ≤ P.natDegree + 1)
    (h : ∀ ℓ, ℓ < j → sResP P Q ℓ = 0) :
    targetList P Q j = List.replicate j (0, 0) := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [targetList_succ, h n (by omega), sRes_eq_zero_of_sResP P Q hpq (by omega) (h n (by omega)),
      ih (by omega) (fun ℓ hℓ => h ℓ (by omega)), List.replicate_succ]

open Azurite.BPR.Chapter8 in
/-- `targetList` defective-block split: when `sResP_ℓ = 0` on the gap `k < ℓ < m`, the target list
    is the gap zeros, then `(sResP_k, sRes_k)`, then `targetList k`. -/
theorem targetList_gap {K : Type _} [CommRing K] [DecidableEq K] (P Q : K[X])
    (hpq : Q.natDegree < P.natDegree) {k : ℕ} :
    ∀ {m : ℕ}, k < m → m ≤ P.natDegree + 1 → (∀ ℓ, k < ℓ → ℓ < m → sResP P Q ℓ = 0) →
      targetList P Q m
        = List.replicate (m - 1 - k) (0, 0)
          ++ (sResP P Q k, Azurite.BPR.Chapter4.sRes P Q k) :: targetList P Q k := by
  intro m
  induction m with
  | zero => intro hkm; omega
  | succ n ih =>
    intro hkm hmp hgap
    rw [targetList_succ]
    rcases Nat.lt_or_ge k n with hkn | hkn
    · have h0 : sResP P Q n = 0 := hgap n hkn (by omega)
      rw [h0, sRes_eq_zero_of_sResP P Q hpq (by omega) h0,
        ih hkn (by omega) (fun ℓ hℓ1 hℓ2 => hgap ℓ hℓ1 (by omega)),
        show n + 1 - 1 - k = (n - 1 - k) + 1 from by omega, List.replicate_succ, List.cons_append]
    · have hkn' : k = n := by omega
      subst hkn'
      rw [show k + 1 - 1 - k = 0 from by omega, List.replicate_zero, List.nil_append]

open Azurite.BPR.Chapter8 in
/-- `targetList` reversed is the ascending `(sResP_ℓ, sRes_ℓ)` over `[0, n)`. -/
theorem targetList_reverse {K : Type _} [CommRing K] (P Q : K[X]) (n : ℕ) :
    (targetList P Q n).reverse
      = (List.range n).map (fun ℓ => (sResP P Q ℓ, Azurite.BPR.Chapter4.sRes P Q ℓ)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [targetList_succ, List.reverse_cons, ih, List.range_succ, List.map_append, List.map_cons,
      List.map_nil]

open Azurite.BPR.Chapter8 in
/-- **Assembly (M3).**  Under the loop invariant, the `ssAux` output (mapped through `toPoly`)
    equals the abstract spec `targetList`. -/
theorem ssAux_spec {K : Type _} [Field K] [DecidableEq K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    ∀ (fuel i j : ℕ) (Si Sj : AzPolynomial K) (sj ti : K),
      j ≤ fuel → 1 ≤ j → j < i → i ≤ P.natDegree + 1 → (j ≤ Q.natDegree ∨ j = P.natDegree) →
      AzPolynomial.toPoly Si = sResP P Q (i - 1) → AzPolynomial.toPoly Sj = sResP P Q (j - 1) →
      (sResP P Q (i - 1)).natDegree = j → (sResP P Q j).natDegree = j →
      sj = sBPR P Q j → ti = tBPR P Q (i - 1) →
      (ssAux fuel j Si Sj sj ti).map (Prod.map AzPolynomial.toPoly id) = targetList P Q j := by
  intro fuel
  induction fuel with
  | zero => intro i j Si Sj sj ti hfuel hj1 _ _ _ _ _ _ _ _ _; exfalso; omega
  | succ f ih =>
    intro i j Si Sj sj ti hfuel hj1 hji hip hjcase hSi hSj hdeg hjnd hsj hti
    have hne : sResP P Q (i - 1) ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
    have htine : tBPR P Q (i - 1) ≠ 0 := by
      rw [tBPR]; split
      · exact one_ne_zero
      · exact Polynomial.leadingCoeff_ne_zero.mpr hne
    rw [ssAux]
    by_cases hSj0 : Sj = 0
    · -- gcd termination: `sResP_{j-1} = 0`
      rw [ite_eq_left hSj0]
      have hzero : sResP P Q (j - 1) = 0 := by rw [← hSj, hSj0, toPoly_zero]
      obtain ⟨_, hzeros⟩ := (theorem_8_34_monolithic P Q hP hQ hpq hq1 hj1 hji hip hne hdeg).1 hzero
      rw [targetList_eq_replicate P Q hpq (by omega) hzeros, List.map_replicate]
      simp [Prod.map, toPoly_zero]
    · rw [ite_eq_right hSj0]
      have hkdeg : (sResP P Q (j - 1)).natDegree = Sj.natDegree := by
        rw [← hSj, AzPolynomial.natDegree_toPoly]
      have hsResPne : sResP P Q (j - 1) ≠ 0 := by
        rw [← hSj]; intro h; exact hSj0 (toPoly_inj.mp (h.trans toPoly_zero.symm))
      have htj : Sj.leadingCoeff = (sResP P Q (j - 1)).leadingCoeff := by
        rw [← hSj, leadingCoeff_toPoly]
      have hsResP_j_ne : sResP P Q j ≠ 0 := by
        intro h; rw [h, Polynomial.natDegree_zero] at hjnd; omega
      have hsjne : sBPR P Q j ≠ 0 := by
        rcases hjcase with hjq | hjp
        · exact sBPR_ne_of_nondef P Q hpq hjq hsResP_j_ne hjnd
        · rw [hjp, sBPR, ite_eq_left rfl]; exact one_ne_zero
      dsimp only
      split_ifs with hkj hk0 hk0'
      · -- non-defective, `k = 0` ⟹ `j = 1`
        have hlc : Sj.leadingCoeff = Azurite.BPR.Chapter4.sRes P Q (j - 1) := by
          rw [htj, ← sBPR_eq_leadingCoeff P Q hpq (by omega) (hkdeg.trans hkj), sBPR, ite_eq_right (by omega)]
        simp only [List.map_cons, List.map_nil, Prod.map_apply, id_eq]
        rw [hSj, hlc, show j = (j - 1) + 1 from by omega, targetList_succ, show j - 1 = 0 from by omega]
        rfl
      · -- non-defective, `k ≥ 1`
        have hk1 : 1 ≤ j - 1 := by omega
        have hjm1q : j - 1 ≤ Q.natDegree := by
          rcases hjcase with h | h
          · omega
          · have hq : (sResP P Q (j - 1)).natDegree = Q.natDegree := by
              rw [h, sResP_pm1_eq_Q P Q hQ hpq]
            rw [hkdeg, hkj] at hq; omega
        have hsbpr : sBPR P Q (j - 1) = Sj.leadingCoeff := by
          rw [sBPR_eq_leadingCoeff P Q hpq (by omega) (hkdeg.trans hkj), htj]
        have htbpr : tBPR P Q (j - 1) = Sj.leadingCoeff := by rw [tBPR, ite_eq_right (by omega), htj]
        have hlc : Sj.leadingCoeff = Azurite.BPR.Chapter4.sRes P Q (j - 1) := by
          rw [← hsbpr, sBPR, ite_eq_right (by omega)]
        have htail := ih j (j - 1) Sj
          (divByRingElt (sj * ti) (-((Sj.leadingCoeff ^ 2 • Si).remExact Sj)))
          Sj.leadingCoeff Sj.leadingCoeff (by omega) hk1 (by omega) (by omega) (Or.inl hjm1q) hSj
          (toPoly_Skm1_eq P Q hP hQ hpq hq1 hj1 hji hip Si Sj hSi hSj hdeg hsResPne
            (hkdeg.trans hkj) hk1 hsj hti (by rw [hsbpr, htbpr]; ring) hsjne htine)
          (hkdeg.trans hkj) (hkdeg.trans hkj) hsbpr.symm htbpr.symm
        have htgt := targetList_succ P Q (j - 1)
        rw [show j - 1 + 1 = j from by omega] at htgt
        rw [hkj, htgt]
        simp only [List.map_cons, Prod.map_apply, id_eq]
        rw [htail, hSj, hlc]
      · -- defective, `k = 0` (terminal)
        have hk_lt : Sj.natDegree < j - 1 := by omega
        obtain ⟨hSpk, hsksRes, _⟩ :=
          def_step P Q hP hQ hpq hq1 hj1 hjcase Sj hSj hsResPne hkdeg hjnd hsj hk_lt
        have hgap : ∀ ℓ, Sj.natDegree < ℓ → ℓ < j - 1 → sResP P Q ℓ = 0 :=
          (((theorem_8_34_monolithic P Q hP hQ hpq hq1 hj1 hji hip hne hdeg).2 Sj.natDegree hsResPne
            hkdeg).2 hk_lt).1
        have hsRjm1 : Azurite.BPR.Chapter4.sRes P Q (j - 1) = 0 := by
          rw [← coeff_sResP P Q hpq (by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hkdeg]; omega)]
        have htgt := targetList_succ P Q (j - 1)
        rw [show j - 1 + 1 = j from by omega, targetList_gap P Q hpq hk_lt (by omega) hgap] at htgt
        rw [htgt]
        simp only [List.map_cons, List.map_append, List.map_replicate, List.map_nil, Prod.map_apply,
          id_eq, toPoly_zero]
        rw [show j - Sj.natDegree - 2 = j - 1 - 1 - Sj.natDegree from by omega, hSj, hSpk, hsksRes,
          hsRjm1, hk0']
        rfl
      · -- defective, `k ≥ 1`
        set sk := Azurite.ExactDiv.exactDiv
          (epsilonSign (j - Sj.natDegree) * Sj.leadingCoeff ^ (j - Sj.natDegree))
          (sj ^ (j - Sj.natDegree - 1)) with hsk_def
        have hk_le : Sj.natDegree ≤ j - 1 := by
          rcases hjcase with h | h
          · rw [← hkdeg]
            exact Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
          · have hq : (sResP P Q (j - 1)).natDegree = Q.natDegree := by
              rw [h, sResP_pm1_eq_Q P Q hQ hpq]
            rw [hkdeg] at hq; omega
        have hk_lt : Sj.natDegree < j - 1 := by omega
        have hkq : Sj.natDegree ≤ Q.natDegree := by
          rcases hjcase with h | h
          · omega
          · have hq : (sResP P Q (j - 1)).natDegree = Q.natDegree := by
              rw [h, sResP_pm1_eq_Q P Q hQ hpq]
            rw [hkdeg] at hq; omega
        obtain ⟨hSpk, hsksRes, hndk⟩ :=
          def_step P Q hP hQ hpq hq1 hj1 hjcase Sj hSj hsResPne hkdeg hjnd hsj hk_lt
        rw [← hsk_def] at hSpk hsksRes
        have hgap : ∀ ℓ, Sj.natDegree < ℓ → ℓ < j - 1 → sResP P Q ℓ = 0 :=
          (((theorem_8_34_monolithic P Q hP hQ hpq hq1 hj1 hji hip hne hdeg).2 Sj.natDegree hsResPne
            hkdeg).2 hk_lt).1
        have hsRjm1 : Azurite.BPR.Chapter4.sRes P Q (j - 1) = 0 := by
          rw [← coeff_sResP P Q hpq (by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hkdeg]; omega)]
        have htbpr : tBPR P Q (j - 1) = Sj.leadingCoeff := by rw [tBPR, ite_eq_right (by omega), htj]
        have hsbprk : Azurite.BPR.Chapter4.sRes P Q Sj.natDegree = sBPR P Q Sj.natDegree := by
          rw [sBPR, ite_eq_right (by omega)]
        have htail := ih j Sj.natDegree Sj
          (divByRingElt (sj * ti) (-((Sj.leadingCoeff * sk) • Si).remExact Sj)) sk Sj.leadingCoeff
          (by omega) (by omega) (by omega) (by omega) (Or.inl hkq) hSj
          (toPoly_Skm1_eq P Q hP hQ hpq hq1 hj1 hji hip Si Sj hSi hSj hdeg hsResPne hkdeg (by omega)
            hsj hti (by rw [htbpr, hsksRes, hsbprk]; ring) hsjne htine)
          hkdeg hndk (hsksRes.trans hsbprk) htbpr.symm
        have htgt := targetList_succ P Q (j - 1)
        rw [show j - 1 + 1 = j from by omega, targetList_gap P Q hpq hk_lt (by omega) hgap] at htgt
        rw [htgt]
        simp only [List.map_cons, List.map_append, List.map_replicate, Prod.map_apply,
          id_eq, toPoly_zero]
        rw [show j - Sj.natDegree - 2 = j - 1 - 1 - Sj.natDegree from by omega, hSj, hSpk, htail,
          hsksRes, hsRjm1]

open Azurite.BPR.Chapter8 in
/-- **Field-level correctness of `signedSubresultant`.**  For `P, Q ∈ AzPolynomial K` with
    `1 ≤ deg Q < deg P`, the output arrays are (after `toPoly`) exactly the signed subresultant
    polynomials `sResP_ℓ` and coefficients `sRes_ℓ` for `ℓ = 0, …, p`. -/
theorem signedSubresultant_toPoly {K : Type _} [Field K] [DecidableEq K] (P Q : AzPolynomial K)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    (signedSubresultant P Q).1.toList.map AzPolynomial.toPoly
        = (List.range (P.natDegree + 1)).map (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
      ∧ (signedSubresultant P Q).2.toList
        = (List.range (P.natDegree + 1)).map
            (Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) := by
  have hpdm : (AzPolynomial.toPoly P).natDegree = P.natDegree := AzPolynomial.natDegree_toPoly P
  have hqdm : (AzPolynomial.toPoly Q).natDegree = Q.natDegree := AzPolynomial.natDegree_toPoly Q
  have hPm : AzPolynomial.toPoly P ≠ 0 := by
    intro h; exact hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hQm : AzPolynomial.toPoly Q ≠ 0 := by
    intro h; exact hQ (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hpqm : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
    rw [hpdm, hqdm]; exact hpq
  have hq1m : 1 ≤ (AzPolynomial.toPoly Q).natDegree := by rw [hqdm]; exact hq1
  have hlst : ((P, P.leadingCoeff) :: ssAux (P.natDegree + 1) P.natDegree P Q 1 1).map
      (Prod.map AzPolynomial.toPoly id)
      = targetList (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (P.natDegree + 1) := by
    rw [List.map_cons, targetList_succ]
    congr 1
    · rw [Prod.map_apply, id_eq, ← hpdm, sResP_eq_self _ _ hpqm,
        show P.leadingCoeff = Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
            (AzPolynomial.toPoly P).natDegree from by
          rw [← leadingCoeff_toPoly, sRes_top_eq_leadingCoeff _ _ hpqm]]
    · exact ssAux_spec (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm hpqm hq1m
        (P.natDegree + 1) (P.natDegree + 1) P.natDegree P Q 1 1 (by omega) (by omega) (by omega)
        (by rw [hpdm]) (Or.inr (by rw [hpdm]))
        (by rw [Nat.add_sub_cancel, ← hpdm]; exact (sResP_eq_self _ _ hpqm).symm)
        (by rw [← hpdm]; exact (sResP_pm1_eq_Q _ _ hQm hpqm).symm)
        (by rw [Nat.add_sub_cancel, ← hpdm, sResP_eq_self _ _ hpqm])
        (by rw [← hpdm, sResP_eq_self _ _ hpqm]) (by rw [sBPR, ite_eq_left (by rw [hpdm])])
        (by rw [Nat.add_sub_cancel, tBPR, ite_eq_left (by rw [hpdm])])
  have hcond : ¬ (Q = 0 ∨ P.natDegree ≤ Q.natDegree) := not_or.mpr ⟨hQ, by omega⟩
  have key : (((P, P.leadingCoeff) :: ssAux (P.natDegree + 1) P.natDegree P Q 1 1).reverse).map
      (Prod.map AzPolynomial.toPoly id)
      = (List.range (P.natDegree + 1)).map
          (fun ℓ => (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ,
            Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ)) := by
    rw [List.map_reverse, hlst, targetList_reverse]
  constructor
  · rw [signedSubresultant, ite_eq_right hcond]
    simp only [List.map_map]
    rw [show (AzPolynomial.toPoly ∘ Prod.fst :
        AzPolynomial K × K → Polynomial K) = Prod.fst ∘ Prod.map AzPolynomial.toPoly id from rfl,
      ← List.map_map, key, List.map_map]
    rfl
  · rw [signedSubresultant, ite_eq_right hcond]
    dsimp only
    rw [show (Prod.snd : AzPolynomial K × K → K) = Prod.snd ∘ Prod.map AzPolynomial.toPoly id
        from rfl, ← List.map_map, key, List.map_map]
    rfl

open Azurite.BPR.Chapter8 in
/-- **Domain-level `ssAux` correctness for `j ≤ q`.**  The mirror of `ssAux_spec` over an integral
    domain: the invariant is stated with `Chapter4.sRes`/`leadingCoeff` in place of the Field-only
    `sBPR`/`tBPR`, and the per-step bridges are the fraction-free domain versions.  Restricted to
    `i ≤ q+1` (so `j ≤ q`), where every cofactor determinant applies; the first call `j=p` is handled
    separately at the top level. -/
theorem ssAux_spec_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D] [IsDomain D]
    (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    ∀ (fuel i j : ℕ) (Si Sj : AzPolynomial D) (sj ti : D),
      j ≤ fuel → 1 ≤ j → j < i → j ≤ Q.natDegree → (i ≤ Q.natDegree + 1 ∨ i = P.natDegree) →
      AzPolynomial.toPoly Si = sResP P Q (i - 1) → AzPolynomial.toPoly Sj = sResP P Q (j - 1) →
      (sResP P Q (i - 1)).natDegree = j → (sResP P Q j).natDegree = j →
      sj = Azurite.BPR.Chapter4.sRes P Q j → ti = (sResP P Q (i - 1)).leadingCoeff →
      (ssAux fuel j Si Sj sj ti).map (Prod.map AzPolynomial.toPoly id) = targetList P Q j := by
  intro fuel
  induction fuel with
  | zero => intro i j Si Sj sj ti hfuel hj1 _ _ _ _ _ _ _ _ _; exfalso; omega
  | succ f ih =>
    intro i j Si Sj sj ti hfuel hj1 hji hjq hicase hSi hSj hdeg hjnd hsj hti
    have hip : i ≤ P.natDegree + 1 := by rcases hicase with h | h <;> omega
    have hne : sResP P Q (i - 1) ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
    have htine : ti ≠ 0 := by rw [hti]; exact Polynomial.leadingCoeff_ne_zero.mpr hne
    rw [ssAux]
    by_cases hSj0 : Sj = 0
    · rw [ite_eq_left hSj0]
      have hzero : sResP P Q (j - 1) = 0 := by rw [← hSj, hSj0, toPoly_zero]
      have hzeros := theorem_8_34_gcd_zeros_domain P Q hP hQ hpq hq1 hj1 hji hip hne hdeg hzero
      rw [targetList_eq_replicate P Q hpq (by omega) hzeros, List.map_replicate]
      simp [Prod.map, toPoly_zero]
    · rw [ite_eq_right hSj0]
      have hkdeg : (sResP P Q (j - 1)).natDegree = Sj.natDegree := by
        rw [← hSj, AzPolynomial.natDegree_toPoly]
      have hsResPne : sResP P Q (j - 1) ≠ 0 := by
        rw [← hSj]; intro h; exact hSj0 (toPoly_inj.mp (h.trans toPoly_zero.symm))
      have htj : Sj.leadingCoeff = (sResP P Q (j - 1)).leadingCoeff := by
        rw [← hSj, leadingCoeff_toPoly]
      have htjne : Sj.leadingCoeff ≠ 0 := by
        rw [htj]; exact Polynomial.leadingCoeff_ne_zero.mpr hsResPne
      have hsResP_j_ne : sResP P Q j ≠ 0 := by
        intro h; rw [h, Polynomial.natDegree_zero] at hjnd; omega
      have hsjne : sj ≠ 0 := by
        rw [hsj]; exact (isNonDefective_iff_sRes_ne_zero P Q hpq hjq).mp
          (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsResP_j_ne, hjnd])
      dsimp only
      split_ifs with hkj hk0 hk0'
      · -- non-defective, `k = 0` ⟹ `j = 1`
        have hlc : Sj.leadingCoeff = Azurite.BPR.Chapter4.sRes P Q (j - 1) := by
          rw [htj]
          exact leadingCoeff_sResP_eq_sRes P Q hpq (by omega)
            (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsResPne, hkdeg.trans hkj])
        simp only [List.map_cons, List.map_nil, Prod.map_apply, id_eq]
        rw [hSj, hlc, show j = (j - 1) + 1 from by omega, targetList_succ, show j - 1 = 0 from by omega]
        rfl
      · -- non-defective, `k ≥ 1`
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
            (-((Sj.leadingCoeff ^ 2 • Si).remExact Sj))) = sResP P Q (j - 1 - 1) := by
          rw [show j - 1 - 1 = Sj.natDegree - 1 from by omega]
          by_cases hiq2 : i ≤ Q.natDegree + 1
          · have hcC : Polynomial.C (sj * ti) = (cofactorMat P Q i j).det := by
              rw [hsj, hti]
              exact (det_cofactorMat_domain P Q hP hpq hj1 hji hiq2 hQ hne hdeg
                (by rw [← hsj]; exact hsjne)).symm
            exact toPoly_Skm1_eq_sResP_domain P Q hQ hpq Si Sj (sj * ti) (Sj.leadingCoeff ^ 2)
              hSi hSj hcC hdC (by omega) (by omega) (by omega) (mul_ne_zero hsjne htine) hsResPne
              hkdeg hk1
          · have hip2 : i = P.natDegree := hicase.resolve_left hiq2
            have hQeq : sResP P Q (i - 1) = Q := by
              rw [show i - 1 = P.natDegree - 1 from by omega, sResP_eq_self_Q P Q (by omega)]
            have hjeq : j = Q.natDegree := by rw [← hdeg, hQeq]
            have hsk : Azurite.BPR.Chapter4.sRes P Q Sj.natDegree = Sj.leadingCoeff := by
              rw [htj, hkj]
              exact (leadingCoeff_sResP_eq_sRes P Q hpq (by omega)
                (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsResPne,
                  hkdeg.trans hkj])).symm
            exact toPoly_Skm1_eq_sResP_domain_ip P Q hP hQ hpq Si Sj (sj * ti) (Sj.leadingCoeff ^ 2)
              (hSi.trans hQeq) (by rw [hSj, hjeq]) hk1 (by omega) (by rw [← hjeq]; exact hsResPne)
              (by rw [← hjeq]; exact hkdeg) (by rw [hsk]; exact htjne)
              (by rw [← hjeq, ← hsj]; exact hsjne)
              (by rw [hsk, ← hjeq, ← htj]; ring)
              (by rw [hsj, hti, ← hjeq, show (sResP P Q (i - 1)).leadingCoeff = Q.leadingCoeff
                  from by rw [hQeq]])
        have htail := ih j (j - 1) Sj
          (divByRingElt (sj * ti) (-((Sj.leadingCoeff ^ 2 • Si).remExact Sj)))
          Sj.leadingCoeff Sj.leadingCoeff (by omega) (by omega) (by omega) (by omega)
          (Or.inl (by omega)) hSj hSkm1
          (hkdeg.trans hkj) (hkdeg.trans hkj) hlc htj
        have htgt := targetList_succ P Q (j - 1)
        rw [show j - 1 + 1 = j from by omega] at htgt
        rw [hkj, htgt]
        simp only [List.map_cons, Prod.map_apply, id_eq]
        rw [htail, hSj, hlc]
      · -- defective, `k = 0` (terminal)
        have hk_le : Sj.natDegree ≤ j - 1 := by
          rw [← hkdeg]
          exact Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
        have hk_lt : Sj.natDegree < j - 1 := by omega
        obtain ⟨hSpk, hsksRes, _⟩ :=
          def_step_domain P Q hP hQ hpq hjq hj1 Sj hSj hsResPne hkdeg hjnd hsj hk_lt
        have hgap : ∀ ℓ, Sj.natDegree < ℓ → ℓ < j - 1 → sResP P Q ℓ = 0 :=
          theorem_8_34_gap_zeros_domain P Q hP hQ hpq hq1 hj1 hji hip hne hdeg hsResPne hkdeg hk_lt
        have hsRjm1 : Azurite.BPR.Chapter4.sRes P Q (j - 1) = 0 := by
          rw [← coeff_sResP P Q hpq (by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hkdeg]; omega)]
        have htgt := targetList_succ P Q (j - 1)
        rw [show j - 1 + 1 = j from by omega, targetList_gap P Q hpq hk_lt (by omega) hgap] at htgt
        rw [htgt]
        simp only [List.map_cons, List.map_append, List.map_replicate, List.map_nil, Prod.map_apply,
          id_eq, toPoly_zero]
        rw [show j - Sj.natDegree - 2 = j - 1 - 1 - Sj.natDegree from by omega, hSj, hSpk, hsksRes,
          hsRjm1, hk0']
        rfl
      · -- defective, `k ≥ 1`
        set sk := Azurite.ExactDiv.exactDiv
          (epsilonSign (j - Sj.natDegree) * Sj.leadingCoeff ^ (j - Sj.natDegree))
          (sj ^ (j - Sj.natDegree - 1)) with hsk_def
        have hk_le : Sj.natDegree ≤ j - 1 := by
          rw [← hkdeg]
          exact Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
        have hk_lt : Sj.natDegree < j - 1 := by omega
        obtain ⟨hSpk, hsksRes, hndk⟩ :=
          def_step_domain P Q hP hQ hpq hjq hj1 Sj hSj hsResPne hkdeg hjnd hsj hk_lt
        rw [← hsk_def] at hSpk hsksRes
        have hgap : ∀ ℓ, Sj.natDegree < ℓ → ℓ < j - 1 → sResP P Q ℓ = 0 :=
          theorem_8_34_gap_zeros_domain P Q hP hQ hpq hq1 hj1 hji hip hne hdeg hsResPne hkdeg hk_lt
        have hsRjm1 : Azurite.BPR.Chapter4.sRes P Q (j - 1) = 0 := by
          rw [← coeff_sResP P Q hpq (by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hkdeg]; omega)]
        have hsResP_k_ne : sResP P Q Sj.natDegree ≠ 0 := by
          intro h; rw [h, Polynomial.natDegree_zero] at hndk; omega
        have hsRes_ne : Azurite.BPR.Chapter4.sRes P Q Sj.natDegree ≠ 0 :=
          (isNonDefective_iff_sRes_ne_zero P Q hpq (by omega)).mp
            (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsResP_k_ne, hndk])
        have hSkm1 : AzPolynomial.toPoly (divByRingElt (sj * ti)
            (-(((Sj.leadingCoeff * sk) • Si).remExact Sj))) = sResP P Q (Sj.natDegree - 1) := by
          by_cases hiq2 : i ≤ Q.natDegree + 1
          · have hcC : Polynomial.C (sj * ti) = (cofactorMat P Q i j).det := by
              rw [hsj, hti]
              exact (det_cofactorMat_domain P Q hP hpq hj1 hji hiq2 hQ hne hdeg
                (by rw [← hsj]; exact hsjne)).symm
            have hdC : Polynomial.C (Sj.leadingCoeff * sk) = (cofactorMat P Q j Sj.natDegree).det := by
              rw [det_cofactorMat_domain P Q hP hpq (by omega) (by omega) (by omega) hQ hsResPne hkdeg
                hsRes_ne]
              congr 1
              rw [hsksRes, htj]; ring
            exact toPoly_Skm1_eq_sResP_domain P Q hQ hpq Si Sj (sj * ti) (Sj.leadingCoeff * sk) hSi
              hSj hcC hdC (by omega) (by omega) (by omega) (mul_ne_zero hsjne htine) hsResPne hkdeg
              (by omega)
          · have hip2 : i = P.natDegree := hicase.resolve_left hiq2
            have hQeq : sResP P Q (i - 1) = Q := by
              rw [show i - 1 = P.natDegree - 1 from by omega, sResP_eq_self_Q P Q (by omega)]
            have hjeq : j = Q.natDegree := by rw [← hdeg, hQeq]
            exact toPoly_Skm1_eq_sResP_domain_ip P Q hP hQ hpq Si Sj (sj * ti) (Sj.leadingCoeff * sk)
              (hSi.trans hQeq) (by rw [hSj, hjeq]) (by omega) (by omega)
              (by rw [← hjeq]; exact hsResPne) (by rw [← hjeq]; exact hkdeg) hsRes_ne
              (by rw [← hjeq, ← hsj]; exact hsjne)
              (by rw [hsksRes, show (sResP P Q (Q.natDegree - 1)).leadingCoeff = Sj.leadingCoeff
                  from by rw [← hjeq, ← htj]]; ring)
              (by rw [hsj, hti, ← hjeq, show (sResP P Q (i - 1)).leadingCoeff = Q.leadingCoeff
                  from by rw [hQeq]])
        have htail := ih j Sj.natDegree Sj
          (divByRingElt (sj * ti) (-(((Sj.leadingCoeff * sk) • Si).remExact Sj))) sk Sj.leadingCoeff
          (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) hSj hSkm1
          hkdeg hndk hsksRes htj
        have htgt := targetList_succ P Q (j - 1)
        rw [show j - 1 + 1 = j from by omega, targetList_gap P Q hpq hk_lt (by omega) hgap] at htgt
        rw [htgt]
        simp only [List.map_cons, List.map_append, List.map_replicate, Prod.map_apply, id_eq,
          toPoly_zero]
        rw [show j - Sj.natDegree - 2 = j - 1 - 1 - Sj.natDegree from by omega, hSj, hSpk, htail,
          hsksRes, hsRjm1]

open Azurite.BPR.Chapter8 in
/-- `sResP_{p-1}(P,Q) = Q` over a domain, for all `q < p` (including the non-defective top
    `q = p-1`).  CommRing analogue of the field `sResP_pm1_eq_Q`. -/
theorem sResP_pm1_eq_Q_domain {D : Type _} [CommRing D] [IsDomain D] (P Q : D[X]) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) : sResP P Q (P.natDegree - 1) = Q := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpq) with h | h
  · have hpq1 : P.natDegree - 1 = Q.natDegree := by omega
    rw [hpq1, sResP_eq_of_natDegree P Q hpq hQ, show P.natDegree - Q.natDegree = 1 from by omega]
    simp [Azurite.BPR.Chapter4.ε]
  · exact sResP_eq_self_Q P Q h

open Azurite.BPR.Chapter8 in
/-- **First call (`j = p`) of `ssAux` over a domain.**  Handled separately from `ssAux_spec_domain`
    (which requires `j ≤ q`): the `j = p` step emits the head `(Q, …)` (and, in the gap case, the
    closed-form `(Spk, s_q)`), computes the first remainder `Skm1 = sResP_{q-1}` via the fraction-free
    first-call bridge, and the recursion (now at `i = p, j = q`) is closed by `ssAux_spec_domain`. -/
theorem ssAux_first_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    (ssAux (P.natDegree + 1) P.natDegree P Q 1 1).map (Prod.map AzPolynomial.toPoly id)
      = targetList (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) P.natDegree := by
  have hpd : (AzPolynomial.toPoly P).natDegree = P.natDegree := AzPolynomial.natDegree_toPoly P
  have hqd : (AzPolynomial.toPoly Q).natDegree = Q.natDegree := AzPolynomial.natDegree_toPoly Q
  have hPm : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hQm : AzPolynomial.toPoly Q ≠ 0 := fun h => hQ (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hpqm : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
    rw [hpd, hqd]; exact hpq
  have hq1m : 1 ≤ (AzPolynomial.toPoly Q).natDegree := by rw [hqd]; exact hq1
  have hlcq : (AzPolynomial.toPoly Q).leadingCoeff = Q.leadingCoeff := leadingCoeff_toPoly Q
  -- `s_q` closed form, nonzero, and non-defectiveness of index `q`.
  have hsRq : Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        (AzPolynomial.toPoly Q).natDegree
      = (epsilonSign (P.natDegree - Q.natDegree) : D) * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
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
  rw [ssAux, ite_eq_right hQ]
  dsimp only
  split_ifs with hkj hk0 hk0'
  · exact absurd hk0 (by omega)
  · -- non-defective `k = q ≥ 1`, so `q = p - 1`
    have hSkm1 : AzPolynomial.toPoly (divByRingElt (1 * 1)
        (-(remExact (Q.leadingCoeff ^ 2 • P) Q)))
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (Q.natDegree - 1) := by
      rw [show Q.natDegree - 1 = (AzPolynomial.toPoly Q).natDegree - 1 from by rw [hqd]]
      refine toPoly_Skm1_eq_sResP_domain_first (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm
        hpqm hq1m P Q (1 * 1) (Q.leadingCoeff ^ 2) rfl rfl hsRqne ?_ (one_mul 1)
      rw [hsRq, hlcq, show P.natDegree - Q.natDegree = 1 from by omega,
        show (epsilonSign 1 : D) = 1 from by rw [epsilonSign_eq]; norm_num]; ring
    have hsRpm1 : Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        (P.natDegree - 1) = Q.leadingCoeff := by
      have hnd' : IsNonDefective (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (P.natDegree - 1) := by
        rw [show P.natDegree - 1 = (AzPolynomial.toPoly Q).natDegree from by rw [hqd]; omega]
        exact hndq
      rw [← leadingCoeff_sResP_eq_sRes _ _ hpqm (by rw [hqd]; omega) hnd', hPm1, hlcq]
    have htail := ssAux_spec_domain (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm hpqm hq1m
      P.natDegree P.natDegree Q.natDegree Q
      (divByRingElt (1 * 1) (-(remExact (Q.leadingCoeff ^ 2 • P) Q))) Q.leadingCoeff Q.leadingCoeff
      (by omega) hq1 (by omega) hqd.ge (Or.inr hpd.symm)
      hPm1.symm hSkm1 (by rw [hPm1, hqd]) (by rw [← hqd]; exact hSResq_nd)
      (by rw [hkj]; exact hsRpm1.symm)
      (by rw [hPm1, hlcq])
    have htgt := targetList_succ (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (P.natDegree - 1)
    rw [show P.natDegree - 1 + 1 = P.natDegree from by omega] at htgt
    rw [List.map_cons, htail, htgt]
    congr 1
    · rw [Prod.map_apply, id_eq, hPm1, hsRpm1]
    · rw [show P.natDegree - 1 = Q.natDegree from by omega]
  · exact absurd hk0' (by omega)
  · -- defective `k = q ≥ 1`, with the gap `q < p - 1`
    have hgap_lt : Q.natDegree < P.natDegree - 1 := by omega
    have hsk : Azurite.ExactDiv.exactDiv (epsilonSign (P.natDegree - Q.natDegree)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) ((1 : D) ^ (P.natDegree - Q.natDegree - 1))
        = epsilonSign (P.natDegree - Q.natDegree) * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
      rw [one_pow]
      have := Azurite.ExactDiv.exactDiv_mul_self (epsilonSign (P.natDegree - Q.natDegree)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) 1 (one_dvd _) one_ne_zero
      rwa [mul_one] at this
    have hskRes : Azurite.ExactDiv.exactDiv (epsilonSign (P.natDegree - Q.natDegree)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) ((1 : D) ^ (P.natDegree - Q.natDegree - 1))
        = Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
          (AzPolynomial.toPoly Q).natDegree := by rw [hsk, hsRq]
    -- `Spk` realizes `sResP_q`
    have hSpk : AzPolynomial.toPoly (divByRingElt Q.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (P.natDegree - Q.natDegree)
          * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) ((1 : D) ^ (P.natDegree - Q.natDegree - 1)))
          • Q))
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (AzPolynomial.toPoly Q).natDegree := by
      have hthis := toPoly_Spk_eq_of_eq_p_domain (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        (by rw [hpd, hqd]; omega) hQm (j := P.natDegree) (k := Q.natDegree) hpd.symm hqd.symm Q
        hPm1.symm rfl (by omega)
      rw [hqd]; exact hthis
    have hSkm1 : AzPolynomial.toPoly (divByRingElt (1 * 1)
        (-(remExact ((Q.leadingCoeff
          * Azurite.ExactDiv.exactDiv (epsilonSign (P.natDegree - Q.natDegree)
            * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) ((1 : D) ^ (P.natDegree - Q.natDegree - 1)))
          • P) Q)))
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (Q.natDegree - 1) := by
      rw [show Q.natDegree - 1 = (AzPolynomial.toPoly Q).natDegree - 1 from by rw [hqd]]
      refine toPoly_Skm1_eq_sResP_domain_first (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm
        hpqm hq1m P Q (1 * 1) _ rfl rfl hsRqne ?_ (one_mul 1)
      rw [hsk, hsRq, hlcq]; ring
    have htail := ssAux_spec_domain (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm hpqm hq1m
      P.natDegree P.natDegree Q.natDegree Q
      (divByRingElt (1 * 1) (-(remExact ((Q.leadingCoeff
        * Azurite.ExactDiv.exactDiv (epsilonSign (P.natDegree - Q.natDegree)
          * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) ((1 : D) ^ (P.natDegree - Q.natDegree - 1)))
        • P) Q)))
      (Azurite.ExactDiv.exactDiv (epsilonSign (P.natDegree - Q.natDegree)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) ((1 : D) ^ (P.natDegree - Q.natDegree - 1)))
      Q.leadingCoeff
      (by omega) hq1 (by omega) hqd.ge (Or.inr hpd.symm)
      hPm1.symm hSkm1 (by rw [hPm1, hqd]) (by rw [← hqd]; exact hSResq_nd)
      (hqd ▸ hskRes) (by rw [hPm1, hlcq])
    have hsRpm1_zero : Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        (P.natDegree - 1) = 0 := by
      rw [← coeff_sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hpqm (by rw [hpd]; omega),
        hPm1, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hqd]; omega)]
    have hSpkQ : AzPolynomial.toPoly (divByRingElt Q.leadingCoeff
        ((Azurite.ExactDiv.exactDiv (epsilonSign (P.natDegree - Q.natDegree)
          * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) ((1 : D) ^ (P.natDegree - Q.natDegree - 1)))
          • Q)) = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) Q.natDegree := by
      rw [hSpk, hqd]
    have hskResQ : Azurite.ExactDiv.exactDiv (epsilonSign (P.natDegree - Q.natDegree)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) ((1 : D) ^ (P.natDegree - Q.natDegree - 1))
        = Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) Q.natDegree := by
      rw [hskRes, hqd]
    have htgt := targetList_succ (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (P.natDegree - 1)
    rw [show P.natDegree - 1 + 1 = P.natDegree from by omega,
      targetList_gap (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hpqm
        (k := Q.natDegree) (m := P.natDegree - 1) (by omega) (by rw [hpd]; omega)
        (fun ℓ hℓ1 hℓ2 => sResP_eq_zero _ _ (by rw [hqd]; omega) (by rw [hpd]; omega)
          (by rw [hpd]; omega))] at htgt
    rw [htgt]
    simp only [List.map_cons, List.map_append, List.map_replicate, Prod.map_apply, id_eq,
      toPoly_zero]
    rw [htail, hSpkQ, hPm1, hsRpm1_zero, hskResQ,
      show P.natDegree - Q.natDegree - 2 = P.natDegree - 1 - 1 - Q.natDegree from by omega]

open Azurite.BPR.Chapter8 in
/-- **Domain-level correctness of `signedSubresultant`.**  For `P, Q ∈ AzPolynomial D` over an
    integral domain with `1 ≤ deg Q < deg P`, the output arrays are (after `toPoly`) exactly the
    signed subresultant polynomials `sResP_ℓ` and coefficients `sRes_ℓ` for `ℓ = 0, …, p`.  The
    fraction-free mirror of `signedSubresultant_toPoly`. -/
theorem signedSubresultant_toPoly_domain {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    (signedSubresultant P Q).1.toList.map AzPolynomial.toPoly
        = (List.range (P.natDegree + 1)).map (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
      ∧ (signedSubresultant P Q).2.toList
        = (List.range (P.natDegree + 1)).map
            (Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) := by
  have hpdm : (AzPolynomial.toPoly P).natDegree = P.natDegree := AzPolynomial.natDegree_toPoly P
  have hPm : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hQm : AzPolynomial.toPoly Q ≠ 0 := fun h => hQ (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hpqm : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
    rw [hpdm, AzPolynomial.natDegree_toPoly Q]; exact hpq
  have hlst : ((P, P.leadingCoeff) :: ssAux (P.natDegree + 1) P.natDegree P Q 1 1).map
      (Prod.map AzPolynomial.toPoly id)
      = targetList (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (P.natDegree + 1) := by
    rw [List.map_cons, targetList_succ]
    congr 1
    · rw [Prod.map_apply, id_eq, ← hpdm, sResP_eq_self _ _ hpqm,
        show P.leadingCoeff = Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P)
            (AzPolynomial.toPoly Q) (AzPolynomial.toPoly P).natDegree from by
          rw [← leadingCoeff_toPoly, Azurite.BPR.Chapter4.sRes, ite_eq_right (by omega), ite_eq_left hpqm,
            ite_eq_left rfl]]
    · exact ssAux_first_domain P Q hP hQ hpq hq1
  have hcond : ¬ (Q = 0 ∨ P.natDegree ≤ Q.natDegree) := not_or.mpr ⟨hQ, by omega⟩
  have key : (((P, P.leadingCoeff) :: ssAux (P.natDegree + 1) P.natDegree P Q 1 1).reverse).map
      (Prod.map AzPolynomial.toPoly id)
      = (List.range (P.natDegree + 1)).map
          (fun ℓ => (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ,
            Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ)) := by
    rw [List.map_reverse, hlst, targetList_reverse]
  refine ⟨?_, ?_⟩
  · rw [signedSubresultant, ite_eq_right hcond]
    simp only [List.map_map]
    rw [show (AzPolynomial.toPoly ∘ Prod.fst :
        AzPolynomial D × D → Polynomial D) = Prod.fst ∘ Prod.map AzPolynomial.toPoly id from rfl,
      ← List.map_map, key, List.map_map]
    rfl
  · rw [signedSubresultant, ite_eq_right hcond]
    dsimp only
    rw [show (Prod.snd : AzPolynomial D × D → D) = Prod.snd ∘ Prod.map AzPolynomial.toPoly id
        from rfl, ← List.map_map, key, List.map_map]
    rfl

open Azurite.BPR.Chapter8 in
/-- **Per-index reader for `signedSubresultant` (Algorithm 8.21).**  At every output index
    `ℓ = 0, …, p`, the `ℓ`-th signed subresultant *polynomial* is `sResP_ℓ` and the `ℓ`-th
    coefficient is `s_ℓ`.  (The per-element form of `signedSubresultant_toPoly_domain`'s list
    equalities; for the full list the index `ℓ` coincides with the array position, which is why the
    natural statement is position-indexed rather than tuple-intrinsic.) -/
theorem signedSubresultant_toPoly_get {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (hq1 : 1 ≤ Q.natDegree) {ℓ : ℕ} (hℓ : ℓ ≤ P.natDegree) :
    ((signedSubresultant P Q).1.toList[ℓ]?).map AzPolynomial.toPoly
        = some (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ)
      ∧ (signedSubresultant P Q).2.toList[ℓ]?
        = some (Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ) := by
  obtain ⟨h1, h2⟩ := signedSubresultant_toPoly_domain P Q hP hQ hpq hq1
  refine ⟨?_, ?_⟩
  · rw [← List.getElem?_map, h1, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  · rw [h2, List.getElem?_map, List.getElem?_range (by omega)]; rfl

/-- **Unified cofactor step** (Algorithm 8.22).  For any "track" `X ∈ {sResP, sResU, sResV}`, the
    algorithm computes the next value as `divByRingElt denom (Cp * Xj - d • Xi)` with the *shared*
    quotient `Cp` and scalars `d, denom`.  Given the recurrence in cleared-denominator form
    `C(denom)·X_{k-1} = (toPoly Cp)·(toPoly Xj) − C(d)·(toPoly Xi)`, this realizes `X_{k-1}`.  Each
    track instantiates `hrec` from its cofactor recurrence (`sResP`/`sResU`/`sResV_cofactor_recurrence`)
    together with `toPoly Cp = β`, `toPoly Xi`, `toPoly Xj`. -/
theorem toPoly_cofactor_step {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (Cp Xi Xj : AzPolynomial D) (d denom : D) (Xkm1 : Polynomial D) (hdenom : denom ≠ 0)
    (hrec : Polynomial.C denom * Xkm1
        = AzPolynomial.toPoly Cp * AzPolynomial.toPoly Xj
          - Polynomial.C d * AzPolynomial.toPoly Xi) :
    AzPolynomial.toPoly (divByRingElt denom (Cp * Xj - d • Xi)) = Xkm1 := by
  apply toPoly_divByRingElt_of_smul denom hdenom (Cp * Xj - d • Xi) Xkm1
  rw [toPoly_sub, toPoly_mul, toPoly_smul, Polynomial.smul_eq_C_mul]
  exact hrec

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **The shared quotient `C` of Algorithm 8.22 realizes the `(i,k)` cofactor minor `β`.**  The
    algorithm forms `C = Quo(d·sResP_{i-1}, sResP_{j-1})` once and reuses it across the `sResP`,
    `sResU`, `sResV` tracks.  Over the domain (same hypotheses as `toPoly_Skm1_eq_sResP_domain`),
    `toPoly C = sResU_{i-1}·sResV_{k-1} − sResV_{i-1}·sResU_{k-1} = det(cofactorMat i k)`, via the
    quotient linchpin and the `sResP` cofactor recurrence (the same Euclidean division). -/
theorem toPoly_quotient_eq_cofactor_domain {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : D[X]) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (Si Sj : AzPolynomial D) (c d : D) {i j k : ℕ}
    (hSi : AzPolynomial.toPoly Si = sResP P Q (i - 1))
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hcC : Polynomial.C c = (cofactorMat P Q i j).det)
    (hdC : Polynomial.C d = (cofactorMat P Q j k).det)
    (hi1 : i - 1 ≤ Q.natDegree) (hj1 : j - 1 ≤ Q.natDegree) (hk1 : k - 1 ≤ Q.natDegree)
    (hSj_ne : sResP P Q (j - 1) ≠ 0)
    (hdegj : (sResP P Q (j - 1)).natDegree = k) (hk1' : 1 ≤ k) :
    AzPolynomial.toPoly (exactDivQuoRem (d • Si) Sj).1
      = sResU P Q (i - 1) * sResV P Q (k - 1) - sResV P Q (i - 1) * sResU P Q (k - 1) := by
  apply toPoly_exactDivQuoRem_fst_of_euclidean (d • Si) Sj
    (sResU P Q (i - 1) * sResV P Q (k - 1) - sResV P Q (i - 1) * sResU P Q (k - 1))
    (-(Polynomial.C c * sResP P Q (k - 1)))
  · rw [hSj]; exact hSj_ne
  · -- `hdiv : toPoly (d • Si) = β · toPoly Sj + R`
    rw [toPoly_smul, Polynomial.smul_eq_C_mul, hSi, hSj, hdC, hcC,
      sResP_cofactor_recurrence P Q hQ hpq hi1 hj1 hk1]
    ring
  · -- `hdeg : R.degree < (toPoly Sj).degree`
    rw [hSj, Polynomial.degree_neg]
    have h3 : (sResP P Q (j - 1)).degree = (k : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hSj_ne, hdegj]
    rw [h3]
    have hCmul : (Polynomial.C c * sResP P Q (k - 1)).degree ≤ (sResP P Q (k - 1)).degree := by
      calc (Polynomial.C c * sResP P Q (k - 1)).degree
          ≤ (Polynomial.C c).degree + (sResP P Q (k - 1)).degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + (sResP P Q (k - 1)).degree := add_le_add (Polynomial.degree_C_le (a := c)) le_rfl
        _ = (sResP P Q (k - 1)).degree := zero_add _
    refine lt_of_le_of_lt hCmul ?_
    refine lt_of_le_of_lt (sResP_degree_le P Q hpq (by omega)) ?_
    exact_mod_cast (by omega : k - 1 < k)

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **`sResU` step bridge** (interior, `i - 1 ≤ q`).  The algorithm's `Ukm1 = divByRingElt denom
    (C·Uj − d•Ui)` realizes `sResU_{k-1}`: `toPoly C = β` (`toPoly_quotient_eq_cofactor_domain`),
    `C(denom) = det(cofactorMat i j)`, `C(d) = det(cofactorMat j k)`, and the cleared recurrence is
    exactly `sResU_cofactor_recurrence` rearranged. -/
theorem toPoly_Ukm1_eq_sResU_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (Si Sj Ui Uj : AzPolynomial D) (c d : D) {i j k : ℕ}
    (hSi : AzPolynomial.toPoly Si = sResP P Q (i - 1))
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hUi : AzPolynomial.toPoly Ui = sResU P Q (i - 1))
    (hUj : AzPolynomial.toPoly Uj = sResU P Q (j - 1))
    (hcC : Polynomial.C c = (cofactorMat P Q i j).det)
    (hdC : Polynomial.C d = (cofactorMat P Q j k).det)
    (hi1 : i - 1 ≤ Q.natDegree) (hj1 : j - 1 ≤ Q.natDegree) (hk1 : k - 1 ≤ Q.natDegree)
    (hc_ne : c ≠ 0) (hSj_ne : sResP P Q (j - 1) ≠ 0)
    (hdegj : (sResP P Q (j - 1)).natDegree = k) (hk1' : 1 ≤ k) :
    AzPolynomial.toPoly (divByRingElt c ((exactDivQuoRem (d • Si) Sj).1 * Uj - d • Ui))
      = sResU P Q (k - 1) := by
  apply toPoly_cofactor_step (exactDivQuoRem (d • Si) Sj).1 Ui Uj d c (sResU P Q (k - 1)) hc_ne
  rw [toPoly_quotient_eq_cofactor_domain P Q hQ hpq Si Sj c d hSi hSj hcC hdC hi1 hj1 hk1 hSj_ne
      hdegj hk1', hUi, hUj, hcC, hdC]
  linear_combination sResU_cofactor_recurrence P Q i j k

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **`sResV` step bridge** (interior, `i - 1 ≤ q`).  The `Q`-cofactor analogue of
    `toPoly_Ukm1_eq_sResU_domain`, via `sResV_cofactor_recurrence`. -/
theorem toPoly_Vkm1_eq_sResV_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (Si Sj Vi Vj : AzPolynomial D) (c d : D) {i j k : ℕ}
    (hSi : AzPolynomial.toPoly Si = sResP P Q (i - 1))
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hVi : AzPolynomial.toPoly Vi = sResV P Q (i - 1))
    (hVj : AzPolynomial.toPoly Vj = sResV P Q (j - 1))
    (hcC : Polynomial.C c = (cofactorMat P Q i j).det)
    (hdC : Polynomial.C d = (cofactorMat P Q j k).det)
    (hi1 : i - 1 ≤ Q.natDegree) (hj1 : j - 1 ≤ Q.natDegree) (hk1 : k - 1 ≤ Q.natDegree)
    (hc_ne : c ≠ 0) (hSj_ne : sResP P Q (j - 1) ≠ 0)
    (hdegj : (sResP P Q (j - 1)).natDegree = k) (hk1' : 1 ≤ k) :
    AzPolynomial.toPoly (divByRingElt c ((exactDivQuoRem (d • Si) Sj).1 * Vj - d • Vi))
      = sResV P Q (k - 1) := by
  apply toPoly_cofactor_step (exactDivQuoRem (d • Si) Sj).1 Vi Vj d c (sResV P Q (k - 1)) hc_ne
  rw [toPoly_quotient_eq_cofactor_domain P Q hQ hpq Si Sj c d hSi hSj hcC hdC hi1 hj1 hk1 hSj_ne
      hdegj hk1', hVi, hVj, hcC, hdC]
  linear_combination sResV_cofactor_recurrence P Q i j k

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **Boundary quotient bridge** (`i = p`, `i-1 > q`, cofactor minor unavailable).  At `i = p` the
    carried `Si` realizes `Q = sResP_{p-1}`, and the shared quotient `C = Quo(d·Q, sResP_{q-1})` (with
    `d = s_k·lcof(sResP_{q-1})`) equals `−sResU_{k-1}` (the `i=p` value of the cofactor minor `β`,
    since `sResU_{p-1}=0, sResV_{p-1}=1`).  Via the quotient linchpin and `boundary_recurrence`. -/
theorem toPoly_quotient_eq_cofactor_domain_ip {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (Si Sj : AzPolynomial D) (d : D) {k : ℕ}
    (hSi : AzPolynomial.toPoly Si = Q)
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (Q.natDegree - 1))
    (hk1 : 1 ≤ k) (hkq : k < Q.natDegree) (hne : sResP P Q (Q.natDegree - 1) ≠ 0)
    (hdeg : (sResP P Q (Q.natDegree - 1)).natDegree = k)
    (hsResk : Azurite.BPR.Chapter4.sRes P Q k ≠ 0)
    (hd : d = Azurite.BPR.Chapter4.sRes P Q k * (sResP P Q (Q.natDegree - 1)).leadingCoeff) :
    AzPolynomial.toPoly (exactDivQuoRem (d • Si) Sj).1 = - sResU P Q (k - 1) := by
  apply toPoly_exactDivQuoRem_fst_of_euclidean (d • Si) Sj
    (- sResU P Q (k - 1)) (sResU P Q (Q.natDegree - 1) * sResP P Q (k - 1))
  · rw [hSj]; exact hne
  · rw [toPoly_smul, Polynomial.smul_eq_C_mul, hSi, hd, hSj]
    exact boundary_recurrence P Q hP hQ hpq rfl hk1 hkq hne hdeg hsResk
  · rw [hSj, Polynomial.degree_eq_natDegree hne, hdeg]
    refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
    have hU0 : (sResU P Q (Q.natDegree - 1)).natDegree = 0 := by
      have := sResU_natDegree_le P Q hpq (show Q.natDegree - 1 ≤ Q.natDegree from by omega); omega
    have hUd : (sResU P Q (Q.natDegree - 1)).degree ≤ 0 := by
      refine le_trans Polynomial.degree_le_natDegree ?_; rw [hU0]; rfl
    have hPd : (sResP P Q (k - 1)).degree ≤ ((k - 1 : ℕ) : WithBot ℕ) :=
      sResP_degree_le P Q hpq (by omega)
    calc (sResU P Q (Q.natDegree - 1)).degree + (sResP P Q (k - 1)).degree
        ≤ 0 + ((k - 1 : ℕ) : WithBot ℕ) := add_le_add hUd hPd
      _ < (k : ℕ) := by rw [zero_add]; exact_mod_cast (show k - 1 < k from by omega)

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **First-call quotient bridge** (`i = p+1`, `Si = P = sResP_p`, `Sj = Q = sResP_{p-1}`).  The first
    shared quotient `C = Quo(d·P, Q)` (with `d = s_q·lcof Q`) equals `sResV_{q-1}` (the `i=p+1` value
    of `β`, since `sResU_p=1, sResV_p=0`).  Via the quotient linchpin and the Bézout
    `sResP_{q-1} = sResU_{q-1}·P + sResV_{q-1}·Q` with `sResU_sub_one_eq`. -/
theorem toPoly_quotient_eq_cofactor_domain_first {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) (Si Sj : AzPolynomial D) (d : D)
    (hSi : AzPolynomial.toPoly Si = P) (hSj : AzPolynomial.toPoly Sj = Q)
    (hsResq : Azurite.BPR.Chapter4.sRes P Q Q.natDegree ≠ 0)
    (hd : d = Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff) :
    AzPolynomial.toPoly (exactDivQuoRem (d • Si) Sj).1 = sResV P Q (Q.natDegree - 1) := by
  have hbez : sResP P Q (Q.natDegree - 1)
      = sResU P Q (Q.natDegree - 1) * P + sResV P Q (Q.natDegree - 1) * Q :=
    sResP_eq_cofactor P Q hQ hpq (by omega)
  apply toPoly_exactDivQuoRem_fst_of_euclidean (d • Si) Sj
    (sResV P Q (Q.natDegree - 1)) (- sResP P Q (Q.natDegree - 1))
  · rw [hSj]; exact hQ
  · rw [toPoly_smul, Polynomial.smul_eq_C_mul, hSi, hd, hSj,
      show Polynomial.C (Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff)
        = - sResU P Q (Q.natDegree - 1) from by
          rw [sResU_sub_one_eq P Q hP hQ hpq hq1 hsResq, neg_neg]]
    linear_combination hbez
  · rw [hSj, Polynomial.degree_neg, Polynomial.degree_eq_natDegree hQ]
    refine lt_of_le_of_lt (sResP_degree_le P Q hpq (by omega)) ?_
    exact_mod_cast (show Q.natDegree - 1 < Q.natDegree from by omega)

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **`sResU` step bridge, `i = p` boundary.**  With `toPoly Ui = 0` (`sResU_{p-1}` convention),
    `toPoly Uj = sResU_{q-1}`, the boundary quotient `toPoly C = −sResU_{k-1}`, and
    `C(c) = −sResU_{q-1}` (`sResU_sub_one_eq`), the step realizes `sResU_{k-1}`. -/
theorem toPoly_Ukm1_eq_sResU_domain_ip {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (hq1 : 1 ≤ Q.natDegree) (Si Sj Ui Uj : AzPolynomial D) (c d : D) {k : ℕ}
    (hSi : AzPolynomial.toPoly Si = Q)
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (Q.natDegree - 1))
    (hk1 : 1 ≤ k) (hkq : k < Q.natDegree) (hne : sResP P Q (Q.natDegree - 1) ≠ 0)
    (hdeg : (sResP P Q (Q.natDegree - 1)).natDegree = k)
    (hsResk : Azurite.BPR.Chapter4.sRes P Q k ≠ 0)
    (hsResq : Azurite.BPR.Chapter4.sRes P Q Q.natDegree ≠ 0)
    (hd : d = Azurite.BPR.Chapter4.sRes P Q k * (sResP P Q (Q.natDegree - 1)).leadingCoeff)
    (hc : c = Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff)
    (hUi : AzPolynomial.toPoly Ui = 0) (hUj : AzPolynomial.toPoly Uj = sResU P Q (Q.natDegree - 1)) :
    AzPolynomial.toPoly (divByRingElt c ((exactDivQuoRem (d • Si) Sj).1 * Uj - d • Ui))
      = sResU P Q (k - 1) := by
  have hc_ne : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero hsResq (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  have hcval : Polynomial.C c = - sResU P Q (Q.natDegree - 1) := by
    rw [hc, sResU_sub_one_eq P Q hP hQ hpq hq1 hsResq, neg_neg]
  apply toPoly_cofactor_step (exactDivQuoRem (d • Si) Sj).1 Ui Uj d c (sResU P Q (k - 1)) hc_ne
  rw [toPoly_quotient_eq_cofactor_domain_ip P Q hP hQ hpq Si Sj d hSi hSj hk1 hkq hne hdeg hsResk hd,
    hUj, hUi, hcval]
  ring

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **`sResV` step bridge, `i = p` boundary.**  With `toPoly Vi = 1` (`sResV_{p-1}` convention),
    `toPoly Vj = sResV_{q-1}`, the boundary quotient `toPoly C = −sResU_{k-1}`, and
    `C(d) = det(cofactorMat q k)`, the step realizes `sResV_{k-1}`. -/
theorem toPoly_Vkm1_eq_sResV_domain_ip {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (hq1 : 1 ≤ Q.natDegree) (Si Sj Vi Vj : AzPolynomial D) (c d : D) {k : ℕ}
    (hSi : AzPolynomial.toPoly Si = Q)
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (Q.natDegree - 1))
    (hk1 : 1 ≤ k) (hkq : k < Q.natDegree) (hne : sResP P Q (Q.natDegree - 1) ≠ 0)
    (hdeg : (sResP P Q (Q.natDegree - 1)).natDegree = k)
    (hsResk : Azurite.BPR.Chapter4.sRes P Q k ≠ 0)
    (hsResq : Azurite.BPR.Chapter4.sRes P Q Q.natDegree ≠ 0)
    (hd : d = Azurite.BPR.Chapter4.sRes P Q k * (sResP P Q (Q.natDegree - 1)).leadingCoeff)
    (hc : c = Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff)
    (hVi : AzPolynomial.toPoly Vi = 1) (hVj : AzPolynomial.toPoly Vj = sResV P Q (Q.natDegree - 1)) :
    AzPolynomial.toPoly (divByRingElt c ((exactDivQuoRem (d • Si) Sj).1 * Vj - d • Vi))
      = sResV P Q (k - 1) := by
  have hc_ne : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero hsResq (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  have hcval : Polynomial.C c = - sResU P Q (Q.natDegree - 1) := by
    rw [hc, sResU_sub_one_eq P Q hP hQ hpq hq1 hsResq, neg_neg]
  have hdval : Polynomial.C d
      = sResU P Q (Q.natDegree - 1) * sResV P Q (k - 1) - sResV P Q (Q.natDegree - 1) * sResU P Q (k - 1) := by
    rw [hd, ← det_cofactorMat_domain P Q hP hpq hk1 hkq (by omega) hQ hne hdeg hsResk,
      cofactorMat, Matrix.det_fin_two_of]
  apply toPoly_cofactor_step (exactDivQuoRem (d • Si) Sj).1 Vi Vj d c (sResV P Q (k - 1)) hc_ne
  rw [toPoly_quotient_eq_cofactor_domain_ip P Q hP hQ hpq Si Sj d hSi hSj hk1 hkq hne hdeg hsResk hd,
    hVj, hVi, hcval, hdval]
  ring

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **`sResU` step bridge, first call (`i = p+1`).**  With `toPoly Ui = 1` (`sResU_p`),
    `toPoly Uj = 0` (`sResU_{p-1}`), `c = 1`, the first quotient `toPoly C = sResV_{q-1}`, and
    `C(d) = −sResU_{q-1}` (`sResU_sub_one_eq`), the step realizes `sResU_{q-1}`. -/
theorem toPoly_Ukm1_eq_sResU_domain_first {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) (Si Sj Ui Uj : AzPolynomial D) (c d : D)
    (hSi : AzPolynomial.toPoly Si = P) (hSj : AzPolynomial.toPoly Sj = Q)
    (hsResq : Azurite.BPR.Chapter4.sRes P Q Q.natDegree ≠ 0)
    (hd : d = Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff) (hc : c = 1)
    (hUi : AzPolynomial.toPoly Ui = 1) (hUj : AzPolynomial.toPoly Uj = 0) :
    AzPolynomial.toPoly (divByRingElt c ((exactDivQuoRem (d • Si) Sj).1 * Uj - d • Ui))
      = sResU P Q (Q.natDegree - 1) := by
  have hc_ne : c ≠ 0 := by rw [hc]; exact one_ne_zero
  apply toPoly_cofactor_step (exactDivQuoRem (d • Si) Sj).1 Ui Uj d c
    (sResU P Q (Q.natDegree - 1)) hc_ne
  rw [toPoly_quotient_eq_cofactor_domain_first P Q hP hQ hpq hq1 Si Sj d hSi hSj hsResq hd,
    hUj, hUi, hc, map_one,
    show Polynomial.C d = - sResU P Q (Q.natDegree - 1) from by
      rw [hd, sResU_sub_one_eq P Q hP hQ hpq hq1 hsResq, neg_neg]]
  ring

open Azurite.BPR.Chapter8 in
open Polynomial in
/-- **`sResV` step bridge, first call (`i = p+1`).**  With `toPoly Vi = 0` (`sResV_p`),
    `toPoly Vj = 1` (`sResV_{p-1}`), `c = 1`, and `toPoly C = sResV_{q-1}`, realizes `sResV_{q-1}`. -/
theorem toPoly_Vkm1_eq_sResV_domain_first {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) (Si Sj Vi Vj : AzPolynomial D) (c d : D)
    (hSi : AzPolynomial.toPoly Si = P) (hSj : AzPolynomial.toPoly Sj = Q)
    (hsResq : Azurite.BPR.Chapter4.sRes P Q Q.natDegree ≠ 0)
    (hd : d = Azurite.BPR.Chapter4.sRes P Q Q.natDegree * Q.leadingCoeff) (hc : c = 1)
    (hVi : AzPolynomial.toPoly Vi = 0) (hVj : AzPolynomial.toPoly Vj = 1) :
    AzPolynomial.toPoly (divByRingElt c ((exactDivQuoRem (d • Si) Sj).1 * Vj - d • Vi))
      = sResV P Q (Q.natDegree - 1) := by
  have hc_ne : c ≠ 0 := by rw [hc]; exact one_ne_zero
  apply toPoly_cofactor_step (exactDivQuoRem (d • Si) Sj).1 Vi Vj d c
    (sResV P Q (Q.natDegree - 1)) hc_ne
  rw [toPoly_quotient_eq_cofactor_domain_first P Q hP hQ hpq hq1 Si Sj d hSi hSj hsResq hd,
    hVj, hVi, hc, map_one]
  ring

/-! ### Algorithm 8.22 reuses Algorithm 8.21 on the `(sResP, sRes)` components -/

/-- `ssAuxExt` (Algorithm 8.22) projects onto `ssAux` (Algorithm 8.21) on the `sResP`/`sRes`
    components: the cofactor state never affects them, since `sResP`/`sRes` are computed by the
    identical recurrence. -/
theorem ssAuxExt_proj {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]
    (fuel j : ℕ) (Si Sj : AzPolynomial R) (sj ti : R) (Ui Vi Uj Vj : AzPolynomial R) :
    (ssAuxExt fuel j Si Sj sj ti Ui Vi Uj Vj).map (fun t => (t.1, t.2.1))
      = ssAux fuel j Si Sj sj ti := by
  induction fuel generalizing j Si Sj sj ti Ui Vi Uj Vj with
  | zero => simp [ssAuxExt, ssAux]
  | succ f ih =>
    rw [ssAuxExt, ssAux]
    by_cases hSj : Sj = 0
    · by_cases hj : j = 0
      · simp [hSj, hj]
      · simp only [ite_eq_left hSj, ite_eq_right hj, List.map_cons, List.map_replicate]
        conv_rhs => rw [show j = (j - 1) + 1 from by omega, List.replicate_succ]
    · rw [ite_eq_right hSj, ite_eq_right hSj]
      dsimp only
      split_ifs with hkj hk0 hk0' <;>
        simp only [List.map_cons, List.map_append, List.map_replicate, ih] <;> rfl

/-- The `sResP` (first) component of `extendedSignedSubresultant` equals that of
    `signedSubresultant`. -/
theorem extendedSignedSubresultant_fst {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]
    (P Q : AzPolynomial R) :
    (extendedSignedSubresultant P Q).1 = (signedSubresultant P Q).1 := by
  unfold extendedSignedSubresultant signedSubresultant
  split_ifs with h
  · rfl
  · simp only [List.map_reverse, List.map_cons]
    rw [show (fun t : AzPolynomial R × R × AzPolynomial R × AzPolynomial R => t.1)
          = Prod.fst ∘ (fun t => (t.1, t.2.1)) from rfl, ← List.map_map, ssAuxExt_proj]

/-- The `sRes` (second) component of `extendedSignedSubresultant` equals that of
    `signedSubresultant`. -/
theorem extendedSignedSubresultant_snd_fst {R : Type _} [CommRing R] [DecidableEq R]
    [Azurite.ExactDiv R] (P Q : AzPolynomial R) :
    (extendedSignedSubresultant P Q).2.1 = (signedSubresultant P Q).2 := by
  unfold extendedSignedSubresultant signedSubresultant
  split_ifs with h
  · rfl
  · simp only [List.map_reverse, List.map_cons]
    rw [show (fun t : AzPolynomial R × R × AzPolynomial R × AzPolynomial R => t.2.1)
          = Prod.snd ∘ (fun t => (t.1, t.2.1)) from rfl, ← List.map_map, ssAuxExt_proj]

open Azurite.BPR.Chapter8 in
/-- **Domain-level Bézout correctness of Algorithm 8.22's main loop** (`j ≤ q`).  Every 4-tuple
    `(sResP_ℓ, s_ℓ, sResU_ℓ, sResV_ℓ)` emitted by `ssAuxExt` satisfies the Bézout relation
    `sResU_ℓ·P + sResV_ℓ·Q = sResP_ℓ` (BPR's correctness remark for Algorithm 8.22).  Mirror of
    `ssAux_spec_domain`, with the `i`-side cofactors carried as a disjunction (abstract for
    `i ≤ q+1`, the convention values `0, 1` at the boundary `i = p`); the `j`-side cofactors are
    always abstract (`j ≤ q`).  The step uses the interior bridges (`toPoly_Ukm1_eq_sResU_domain`)
    in the abstract case and the `_ip` bridges at the boundary. -/
theorem ssAuxExt_spec_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (hq1 : 1 ≤ Q.natDegree) :
    ∀ (fuel i j : ℕ) (Si Sj : AzPolynomial D) (sj ti : D) (Ui Vi Uj Vj : AzPolynomial D),
      j ≤ fuel → 1 ≤ j → j < i → j ≤ Q.natDegree → (i ≤ Q.natDegree + 1 ∨ i = P.natDegree) →
      AzPolynomial.toPoly Si = sResP P Q (i - 1) → AzPolynomial.toPoly Sj = sResP P Q (j - 1) →
      (sResP P Q (i - 1)).natDegree = j → (sResP P Q j).natDegree = j →
      sj = Azurite.BPR.Chapter4.sRes P Q j → ti = (sResP P Q (i - 1)).leadingCoeff →
      AzPolynomial.toPoly Uj = sResU P Q (j - 1) → AzPolynomial.toPoly Vj = sResV P Q (j - 1) →
      ((i ≤ Q.natDegree + 1 ∧ AzPolynomial.toPoly Ui = sResU P Q (i - 1)
          ∧ AzPolynomial.toPoly Vi = sResV P Q (i - 1))
        ∨ (i = P.natDegree ∧ AzPolynomial.toPoly Ui = 0 ∧ AzPolynomial.toPoly Vi = 1)) →
      ∀ t ∈ ssAuxExt fuel j Si Sj sj ti Ui Vi Uj Vj,
        (AzPolynomial.toPoly t.2.2.1 * P + AzPolynomial.toPoly t.2.2.2 * Q
          = AzPolynomial.toPoly t.1)
        ∧ (t.2.1 ≠ 0 → AzPolynomial.toPoly t.2.2.1 = sResU P Q t.1.natDegree
            ∧ AzPolynomial.toPoly t.2.2.2 = sResV P Q t.1.natDegree) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i j Si Sj sj ti Ui Vi Uj Vj hfuel hj1 _ _ _ _ _ _ _ _ _ _ _ _
    exact (by omega : False).elim
  | succ f ih =>
    intro i j Si Sj sj ti Ui Vi Uj Vj hfuel hj1 hji hjq hicase hSi hSj hdeg hjnd hsj hti hUj hVj hUVi
    have hjm1q : j - 1 ≤ Q.natDegree := by omega
    have hhead : AzPolynomial.toPoly Uj * P + AzPolynomial.toPoly Vj * Q = AzPolynomial.toPoly Sj := by
      rw [hUj, hVj, hSj]; exact (sResP_eq_cofactor P Q hQ hpq hjm1q).symm
    have hip : i ≤ P.natDegree + 1 := by rcases hicase with h | h <;> omega
    have hne : sResP P Q (i - 1) ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
    have htine : ti ≠ 0 := by rw [hti]; exact Polynomial.leadingCoeff_ne_zero.mpr hne
    rw [ssAuxExt]
    by_cases hSj0 : Sj = 0
    · rw [ite_eq_left hSj0, ite_eq_right (show ¬j = 0 by omega)]
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · refine ⟨?_, fun h => absurd rfl h⟩
        rw [hhead, hSj0]
      · rw [List.eq_of_mem_replicate ht']
        exact ⟨by simp [toPoly_zero], fun h => absurd rfl h⟩
    · rw [ite_eq_right hSj0]
      have hkdeg : (sResP P Q (j - 1)).natDegree = Sj.natDegree := by
        rw [← hSj, AzPolynomial.natDegree_toPoly]
      have hsResPne : sResP P Q (j - 1) ≠ 0 := by
        rw [← hSj]; intro h; exact hSj0 (toPoly_inj.mp (h.trans toPoly_zero.symm))
      have htj : Sj.leadingCoeff = (sResP P Q (j - 1)).leadingCoeff := by
        rw [← hSj, leadingCoeff_toPoly]
      have htjne : Sj.leadingCoeff ≠ 0 := by
        rw [htj]; exact Polynomial.leadingCoeff_ne_zero.mpr hsResPne
      have hsResP_j_ne : sResP P Q j ≠ 0 := by
        intro h; rw [h, Polynomial.natDegree_zero] at hjnd; omega
      have hsjne : sj ≠ 0 := by
        rw [hsj]; exact (isNonDefective_iff_sRes_ne_zero P Q hpq hjq).mp
          (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsResP_j_ne, hjnd])
      -- The `i = p` boundary facts (used by the `_ip` cofactor bridges).
      have hbdry : i = P.natDegree → AzPolynomial.toPoly Si = Q ∧ j = Q.natDegree := by
        intro hip2
        have hQeq : sResP P Q (i - 1) = Q := by
          rw [show i - 1 = P.natDegree - 1 from by omega]; exact sResP_pm1_eq_Q_domain P Q hQ hpq
        exact ⟨hSi.trans hQeq, by rw [← hdeg, hQeq]⟩
      dsimp only
      split_ifs with hkj hk0 hk0'
      · -- non-defective, `k = 0` ⟹ `j = 1`: output `[(Sj, tj, Uj, Vj)]`
        intro t ht
        rw [List.mem_singleton] at ht; subst ht
        exact ⟨hhead, fun _ => ⟨by rw [hkj]; exact hUj, by rw [hkj]; exact hVj⟩⟩
      · -- non-defective, `k ≥ 1`
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
        intro t ht
        rcases List.mem_cons.mp ht with rfl | htmem
        · exact ⟨hhead, fun _ => ⟨by rw [hkj]; exact hUj, by rw [hkj]; exact hVj⟩⟩
        · exact ih j Sj.natDegree Sj _ Sj.leadingCoeff Sj.leadingCoeff Uj Vj _ _
            (by omega) hk1 (by omega) (by omega) (Or.inl (by omega)) hSj hSkm1 hkdeg
            (by rw [hkj]; exact hkdeg.trans hkj) (by rw [hkj]; exact hlc) htj hUkm1 hVkm1
            (Or.inl ⟨by omega, hUj, hVj⟩) t htmem
      · -- defective, `k = 0` (terminal): output `(Sj,0,Uj,Vj) :: (gaps ++ [(Spk,sk,Upk,Vpk)])`
        have hk_lt : Sj.natDegree < j - 1 := by
          have hk_le : Sj.natDegree ≤ j - 1 := by
            rw [← hkdeg]
            exact Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
          omega
        obtain ⟨hSpk, _, hndk⟩ := def_step_domain P Q hP hQ hpq hjq hj1 Sj hSj hsResPne hkdeg hjnd hsj
          hk_lt
        have hUpk := toPoly_Upk_eq_sResU_domain P Q hP hQ hpq hjq hj1 hjnd Sj Uj hSj hUj hsResPne
          hkdeg hk_lt hsj hsjne
        have hVpk := toPoly_Vpk_eq_sResV_domain P Q hP hQ hpq hjq hj1 hjnd Sj Vj hSj hVj hsResPne
          hkdeg hk_lt hsj hsjne
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht2
        · exact ⟨hhead, fun h => absurd rfl h⟩
        · rcases List.mem_append.mp ht2 with hg | hb
          · rw [List.eq_of_mem_replicate hg]; exact ⟨by simp [toPoly_zero], fun h => absurd rfl h⟩
          · obtain rfl := List.mem_singleton.mp hb
            refine ⟨?_, fun _ => ?_⟩
            · dsimp only; rw [hUpk, hVpk, hSpk]
              exact (sResP_eq_cofactor P Q hQ hpq (by omega)).symm
            · dsimp only
              rw [show (_ : AzPolynomial D).natDegree = Sj.natDegree from
                (AzPolynomial.natDegree_toPoly _).symm.trans
                  ((congrArg Polynomial.natDegree hSpk).trans hndk)]
              exact ⟨hUpk, hVpk⟩
      · -- defective, `k ≥ 1`: output `(Sj,0,Uj,Vj) :: (gaps ++ ((Spk,sk,Upk,Vpk) :: recursion))`
        set sk := Azurite.ExactDiv.exactDiv
          (epsilonSign (j - Sj.natDegree) * Sj.leadingCoeff ^ (j - Sj.natDegree))
          (sj ^ (j - Sj.natDegree - 1)) with hsk_def
        have hk_lt : Sj.natDegree < j - 1 := by
          have hk_le : Sj.natDegree ≤ j - 1 := by
            rw [← hkdeg]
            exact Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
          omega
        obtain ⟨hSpk, hsksRes, hndk⟩ := def_step_domain P Q hP hQ hpq hjq hj1 Sj hSj hsResPne hkdeg
          hjnd hsj hk_lt
        rw [← hsk_def] at hSpk hsksRes
        have hUpk := toPoly_Upk_eq_sResU_domain P Q hP hQ hpq hjq hj1 hjnd Sj Uj hSj hUj hsResPne
          hkdeg hk_lt hsj hsjne
        have hVpk := toPoly_Vpk_eq_sResV_domain P Q hP hQ hpq hjq hj1 hjnd Sj Vj hSj hVj hsResPne
          hkdeg hk_lt hsj hsjne
        rw [← hsk_def] at hUpk hVpk
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
        have hUpk := toPoly_Upk_eq_sResU_domain P Q hP hQ hpq hjq hj1 hjnd Sj Uj hSj hUj hsResPne
          hkdeg hk_lt hsj hsjne
        have hVpk := toPoly_Vpk_eq_sResV_domain P Q hP hQ hpq hjq hj1 hjnd Sj Vj hSj hVj hsResPne
          hkdeg hk_lt hsj hsjne
        rw [← hsk_def] at hUpk hVpk
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht2
        · exact ⟨hhead, fun h => absurd rfl h⟩
        · rcases List.mem_append.mp ht2 with hg | ht3
          · rw [List.eq_of_mem_replicate hg]; exact ⟨by simp [toPoly_zero], fun h => absurd rfl h⟩
          · rcases List.mem_cons.mp ht3 with rfl | htmem
            · refine ⟨?_, fun _ => ?_⟩
              · dsimp only; rw [hUpk, hVpk, hSpk]
                exact (sResP_eq_cofactor P Q hQ hpq (by omega)).symm
              · dsimp only
                rw [show (_ : AzPolynomial D).natDegree = Sj.natDegree from
                  (AzPolynomial.natDegree_toPoly _).symm.trans
                    ((congrArg Polynomial.natDegree hSpk).trans hndk)]
                exact ⟨hUpk, hVpk⟩
            · exact ih j Sj.natDegree Sj _ sk Sj.leadingCoeff Uj Vj _ _
                (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) hSj hSkm1 hkdeg
                hndk hsksRes htj hUkm1 hVkm1 (Or.inl ⟨by omega, hUj, hVj⟩) t htmem

open Azurite.BPR.Chapter8 in
/-- **Cofactor equivalence on non-defective indices** (`j ≤ q`).  At every non-defective index
    (a tuple `t` whose signed-subresultant coefficient `t.2.1 = s_ℓ` is nonzero), the cofactors
    `ssAuxExt` computes are exactly the `Notation_8_41` cofactor determinants:
    `toPoly t.2.2.1 = sResU P Q (deg t.1)` and `toPoly t.2.2.2 = sResV P Q (deg t.1)`.
    The `.2` projection of `ssAuxExt_spec_domain`. -/
theorem ssAuxExt_cofactor_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (hq1 : 1 ≤ Q.natDegree) (fuel i j : ℕ) (Si Sj : AzPolynomial D) (sj ti : D)
    (Ui Vi Uj Vj : AzPolynomial D) (hfuel : j ≤ fuel) (hj1 : 1 ≤ j) (hji : j < i)
    (hjq : j ≤ Q.natDegree) (hicase : i ≤ Q.natDegree + 1 ∨ i = P.natDegree)
    (hSi : AzPolynomial.toPoly Si = sResP P Q (i - 1))
    (hSj : AzPolynomial.toPoly Sj = sResP P Q (j - 1))
    (hdeg : (sResP P Q (i - 1)).natDegree = j) (hjnd : (sResP P Q j).natDegree = j)
    (hsj : sj = Azurite.BPR.Chapter4.sRes P Q j) (hti : ti = (sResP P Q (i - 1)).leadingCoeff)
    (hUj : AzPolynomial.toPoly Uj = sResU P Q (j - 1))
    (hVj : AzPolynomial.toPoly Vj = sResV P Q (j - 1))
    (hUVi : (i ≤ Q.natDegree + 1 ∧ AzPolynomial.toPoly Ui = sResU P Q (i - 1)
          ∧ AzPolynomial.toPoly Vi = sResV P Q (i - 1))
        ∨ (i = P.natDegree ∧ AzPolynomial.toPoly Ui = 0 ∧ AzPolynomial.toPoly Vi = 1)) :
    ∀ t ∈ ssAuxExt fuel j Si Sj sj ti Ui Vi Uj Vj,
      t.2.1 ≠ 0 → AzPolynomial.toPoly t.2.2.1 = sResU P Q t.1.natDegree
        ∧ AzPolynomial.toPoly t.2.2.2 = sResV P Q t.1.natDegree :=
  fun t ht => (ssAuxExt_spec_domain P Q hP hQ hpq hq1 fuel i j Si Sj sj ti Ui Vi Uj Vj hfuel hj1 hji
    hjq hicase hSi hSj hdeg hjnd hsj hti hUj hVj hUVi t ht).2

open Azurite.BPR.Chapter8 in
/-- **First-call Bézout + cofactor equivalence** (`i = p+1`): every tuple emitted by the top-level
    `ssAuxExt` call satisfies the Bézout relation, and — at every non-defective index `< q` — its
    cofactors are the `Notation_8_41` determinants `sResU`/`sResV`.  Peels the `j = p` step (via the
    `_first` bridges), then applies `ssAuxExt_spec_domain` to the tail at `(i, j) = (p, q)`; the
    boundary tuples (index `≥ q`) are excluded by the `t.1.natDegree < q` guard. -/
theorem ssAuxExt_bezout_first_domain {D : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
    [IsDomain D] (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    ∀ t ∈ ssAuxExt (P.natDegree + 1) P.natDegree P Q 1 1 1 0 0 1,
      (AzPolynomial.toPoly t.2.2.1 * AzPolynomial.toPoly P
          + AzPolynomial.toPoly t.2.2.2 * AzPolynomial.toPoly Q
        = AzPolynomial.toPoly t.1)
      ∧ (t.2.1 ≠ 0 → t.1.natDegree < Q.natDegree →
          AzPolynomial.toPoly t.2.2.1 = sResU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
              t.1.natDegree
          ∧ AzPolynomial.toPoly t.2.2.2 = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
              t.1.natDegree) := by
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
      = (epsilonSign (P.natDegree - Q.natDegree) : D) * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
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
  have hheadQ : AzPolynomial.toPoly (0 : AzPolynomial D) * AzPolynomial.toPoly P
      + AzPolynomial.toPoly (1 : AzPolynomial D) * AzPolynomial.toPoly Q = AzPolynomial.toPoly Q := by
    rw [toPoly_zero, toPoly_one]; ring
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
    intro t ht
    rcases List.mem_cons.mp ht with rfl | htmem
    · exact ⟨hheadQ, fun _ hlt => absurd hlt (lt_irrefl _)⟩
    · have hsd := ssAuxExt_spec_domain (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm hpqm
        hq1m P.natDegree P.natDegree Q.natDegree Q _ Q.leadingCoeff Q.leadingCoeff 0 1 _ _
        (by omega) hq1 (by omega) hqd.ge (Or.inr hpd.symm) (by rw [hPm1])
        hSkm1 (by rw [hPm1, hqd]) (by rw [← hqd]; exact hSResq_nd) hsRq'
        (by rw [hPm1, hlcq]) hUkm1 hVkm1
        (Or.inr ⟨hpd.symm, toPoly_zero, toPoly_one⟩) t (by rw [hkj] at htmem ⊢; exact htmem)
      exact ⟨hsd.1, fun hs _ => hsd.2 hs⟩
  · exact absurd hk0' (by omega)
  · -- defective `k = q ≥ 1` with the gap `q < p - 1`
    have hlcQne : Q.leadingCoeff ≠ 0 := by
      rw [← hlcq]; exact Polynomial.leadingCoeff_ne_zero.mpr hQm
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
    have hlcdvd : Q.leadingCoeff ∣ sk := by
      rw [hsk]
      exact (dvd_pow_self Q.leadingCoeff (by omega : P.natDegree - Q.natDegree ≠ 0)).mul_left _
    have hdvd : ∀ (W : AzPolynomial D) (i : ℕ), Q.leadingCoeff ∣ (sk • W).coeff i := by
      intro W i; rw [coeff_smul]; exact hlcdvd.mul_right _
    have hdfirst : Q.leadingCoeff * sk = Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P)
        (AzPolynomial.toPoly Q) (AzPolynomial.toPoly Q).natDegree * (AzPolynomial.toPoly Q).leadingCoeff := by
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
    have hSpk : AzPolynomial.toPoly (divByRingElt Q.leadingCoeff (sk • Q))
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) Q.natDegree := by
      rw [hsk_def]
      exact toPoly_Spk_eq_of_eq_p_domain (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        (by rw [hpd, hqd]; omega) hQm (j := P.natDegree) (k := Q.natDegree) hpd.symm hqd.symm Q
        hPm1.symm rfl (by omega)
    have hSpkdeg : (divByRingElt Q.leadingCoeff (sk • Q)).natDegree = Q.natDegree :=
      (AzPolynomial.natDegree_toPoly _).symm.trans
        ((congrArg Polynomial.natDegree hSpk).trans (hqd ▸ hSResq_nd))
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht2
    · exact ⟨hheadQ, fun hs _ => absurd rfl hs⟩
    · rcases List.mem_append.mp ht2 with hg | ht3
      · rw [List.eq_of_mem_replicate hg]
        exact ⟨by simp [toPoly_zero], fun hs _ => absurd rfl hs⟩
      · rcases List.mem_cons.mp ht3 with rfl | htmem
        · -- gap-bottom `(Spk, sk, Upk, Vpk)`: Bézout from `Q = 0·P + 1·Q` via the round-trip;
          -- the cofactor match is vacuous since its index is `q`, not `< q`.
          refine ⟨?_, fun _ hlt => absurd (hSpkdeg ▸ hlt) (lt_irrefl _)⟩
          dsimp only
          apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hlcQne)
          rw [mul_add, ← mul_assoc, ← mul_assoc,
            C_mul_toPoly_divByRingElt Q.leadingCoeff hlcQne _ (hdvd 0),
            C_mul_toPoly_divByRingElt Q.leadingCoeff hlcQne _ (hdvd 1),
            C_mul_toPoly_divByRingElt Q.leadingCoeff hlcQne _ (hdvd Q)]
          simp only [toPoly_smul, toPoly_zero, toPoly_one, Polynomial.smul_eq_C_mul]
          ring
        · have hsd := ssAuxExt_spec_domain (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) hPm hQm hpqm
            hq1m P.natDegree P.natDegree Q.natDegree Q _ sk Q.leadingCoeff 0 1 _ _
            (by omega) hq1 (by omega) hqd.ge (Or.inr hpd.symm) (by rw [hPm1])
            hSkm1 (by rw [hPm1, hqd]) (by rw [← hqd]; exact hSResq_nd) hskRes
            (by rw [hPm1, hlcq]) hUkm1 hVkm1
            (Or.inr ⟨hpd.symm, toPoly_zero, toPoly_one⟩) t htmem
          exact ⟨hsd.1, fun hs _ => hsd.2 hs⟩

/-- **The four output arrays of `extendedSignedSubresultant` recover the internal tuple list.**
    Zipping the `sResP`, `s`, `sResU`, `sResV` output arrays (as lists) reconstructs the descending
    tuple list `((P, lcof P, 1, 0) :: ssAuxExt …).reverse` — so a statement about the public output
    can be reduced to one about that list (and hence to the recursion). -/
theorem extendedSignedSubresultant_tuples_eq {R : Type _} [CommRing R] [DecidableEq R]
    [Azurite.ExactDiv R] (P Q : AzPolynomial R) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) :
    (extendedSignedSubresultant P Q).1.toList.zip
        ((extendedSignedSubresultant P Q).2.1.toList.zip
          ((extendedSignedSubresultant P Q).2.2.1.toList.zip
            (extendedSignedSubresultant P Q).2.2.2.toList))
      = ((P, P.leadingCoeff, (1 : AzPolynomial R), (0 : AzPolynomial R))
          :: ssAuxExt (P.natDegree + 1) P.natDegree P Q 1 1 1 0 0 1).reverse := by
  have hcond : ¬ (Q = 0 ∨ P.natDegree ≤ Q.natDegree) := not_or.mpr ⟨hQ, by omega⟩
  unfold extendedSignedSubresultant
  rw [ite_eq_right hcond]
  simp only [List.zip_map']
  exact List.map_id _

open Azurite.BPR.Chapter8 in
/-- **BPR Algorithm 8.22 correctness (Bézout relation).**  Reading each output index `ℓ` of
    `extendedSignedSubresultant P Q` as a tuple `t = (sResP_ℓ, s_ℓ, sResU_ℓ, sResV_ℓ)` (zipping the
    four output arrays), the cofactors satisfy `sResU_ℓ · P + sResV_ℓ · Q = sResP_ℓ`. -/
theorem extendedSignedSubresultant_toPoly_domain {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    ∀ t ∈ (extendedSignedSubresultant P Q).1.toList.zip
        ((extendedSignedSubresultant P Q).2.1.toList.zip
          ((extendedSignedSubresultant P Q).2.2.1.toList.zip
            (extendedSignedSubresultant P Q).2.2.2.toList)),
      AzPolynomial.toPoly t.2.2.1 * AzPolynomial.toPoly P
          + AzPolynomial.toPoly t.2.2.2 * AzPolynomial.toPoly Q
        = AzPolynomial.toPoly t.1 := by
  intro t ht
  have hmem := List.mem_reverse.mp (extendedSignedSubresultant_tuples_eq P Q hQ hpq ▸ ht)
  rcases List.mem_cons.mp hmem with rfl | htmem
  · rw [toPoly_one, toPoly_zero]; ring
  · exact (ssAuxExt_bezout_first_domain P Q hP hQ hpq hq1 t htmem).1

open Azurite.BPR.Chapter8 in
/-- **BPR Algorithm 8.22, cofactor equivalence to `sResU`/`sResV`.**  At every non-defective output
    index `ℓ < q` (a tuple whose signed-subresultant coefficient `t.2.1 = s_ℓ` is nonzero and whose
    degree `t.1.natDegree = ℓ` is below `q`), the cofactors `extendedSignedSubresultant P Q` computes
    are exactly the `Notation_8_41` cofactor determinants:
    `toPoly (sResU output) = sResU P Q ℓ` and `toPoly (sResV output) = sResV P Q ℓ`.

    The boundary indices `q` (the entry, where the matrix `sResU_q` is `0` by convention) and `p` (the
    input `P`) are excluded by the `t.1.natDegree < q` guard; the faithful all-index statement there
    is the Bézout relation `extendedSignedSubresultant_toPoly_domain`. -/
theorem extendedSignedSubresultant_cofactor_domain {D : Type _} [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    ∀ t ∈ (extendedSignedSubresultant P Q).1.toList.zip
        ((extendedSignedSubresultant P Q).2.1.toList.zip
          ((extendedSignedSubresultant P Q).2.2.1.toList.zip
            (extendedSignedSubresultant P Q).2.2.2.toList)),
      t.2.1 ≠ 0 → t.1.natDegree < Q.natDegree →
        AzPolynomial.toPoly t.2.2.1 = sResU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
            t.1.natDegree
        ∧ AzPolynomial.toPoly t.2.2.2 = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
            t.1.natDegree := by
  intro t ht
  have hmem := List.mem_reverse.mp (extendedSignedSubresultant_tuples_eq P Q hQ hpq ▸ ht)
  rcases List.mem_cons.mp hmem with rfl | htmem
  · -- the prepended head is `P` at index `p > q`, excluded by the guard
    intro _ hlt
    change P.natDegree < Q.natDegree at hlt
    exact absurd hlt (by omega)
  · exact (ssAuxExt_bezout_first_domain P Q hP hQ hpq hq1 t htmem).2

end Azurite.AzPolynomial
