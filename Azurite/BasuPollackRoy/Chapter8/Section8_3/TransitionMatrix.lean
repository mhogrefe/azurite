/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_44

/-!
# BPR signed subresultant transition matrix `T_j` and equations (8.13), (8.14)

In the Structure Theorem 8.34 recurrence setting — `sResP_{i-1}(P,Q)` nonzero of degree `j`,
`sResP_{j-1}(P,Q)` nonzero of degree `k` (`1 ≤ k`) — the recurrence
`s_j t_{i-1} sResP_{k-1} = -Rem(s_k t_{j-1} sResP_{i-1}, sResP_{j-1})` rearranges, writing
`C_{k-1}` for the quotient `Quo(s_k t_{j-1} sResP_{i-1}, sResP_{j-1})`, into

  `s_j t_{i-1} sResP_{k-1} = -s_k t_{j-1} sResP_{i-1} + C_{k-1} sResP_{j-1}`.

Dividing by `s_j t_{i-1} ≠ 0` gives the *signed subresultant transition*:

  `sResP_{k-1} = -(s_k t_{j-1})/(s_j t_{i-1}) · sResP_{i-1} + C_{k-1}/(s_j t_{i-1}) · sResP_{j-1}`
                                                                                        (8.13)

and, with the **transition matrix**

  `T_j = [ 0                            1                       ;
           -(s_k t_{j-1})/(s_j t_{i-1})  C_{k-1}/(s_j t_{i-1}) ] ∈ K[X]^{2×2}`,

  `[sResP_{j-1}, sResP_{k-1}]ᵀ = T_j · [sResP_{i-1}, sResP_{j-1}]ᵀ`.                    (8.14)
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

variable {K : Type*} [Field K]

/-- BPR's quotient `C_{k-1}` of the signed subresultant transition: the Euclidean quotient of
    `s_k t_{j-1} · sResP_{i-1}(P,Q)` by `sResP_{j-1}(P,Q)`. -/
noncomputable def transC (P Q : K[X]) (i j k : ℕ) : K[X] :=
  (C (sBPR P Q k * tBPR P Q (j - 1)) * sResP P Q (i - 1)) / sResP P Q (j - 1)

/-- The **signed subresultant transition matrix** `T_j`. -/
noncomputable def transMat (P Q : K[X]) (i j k : ℕ) : Matrix (Fin 2) (Fin 2) K[X] :=
  !![0, 1;
     C (-(sBPR P Q k * tBPR P Q (j - 1)) / (sBPR P Q j * tBPR P Q (i - 1))),
     C ((sBPR P Q j * tBPR P Q (i - 1))⁻¹) * transC P Q i j k]

/-- The cleared-denominator form of the Structure Theorem recurrence:
    `s_j t_{i-1} sResP_{k-1} = -s_k t_{j-1} sResP_{i-1} + C_{k-1} sResP_{j-1}`. -/
theorem transC_spec (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1) {k : ℕ}
    (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    C (sBPR P Q j * tBPR P Q (i - 1)) * sResP P Q (k - 1)
      = -(C (sBPR P Q k * tBPR P Q (j - 1)) * sResP P Q (i - 1))
        + transC P Q i j k * sResP P Q (j - 1) := by
  obtain ⟨hmono, _⟩ :=
    (theorem_8_34_monolithic P Q hP hQ hpq hq1 hj1 hji (by omega) hne hdeg).2 k hk0 hkdeg
  rw [ite_eq_right (show ¬ k = 0 by omega)] at hmono
  simp only [← Polynomial.C_mul] at hmono
  rw [hmono, EuclideanDomain.mod_eq_sub_mul_div]
  simp only [transC]
  ring

/-- **BPR equation (8.13).**  In the recurrence setting, the signed subresultant transition. -/
theorem sResP_transition (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1) {k : ℕ}
    (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    sResP P Q (k - 1)
      = C (-(sBPR P Q k * tBPR P Q (j - 1)) / (sBPR P Q j * tBPR P Q (i - 1)))
          * sResP P Q (i - 1)
        + C ((sBPR P Q j * tBPR P Q (i - 1))⁻¹) * transC P Q i j k * sResP P Q (j - 1) := by
  have hc_ne := sBPR_mul_tBPR_ne_zero P Q hP hQ hpq hq1 hj1 hji hiq hne hdeg
  have hspec := transC_spec P Q hP hQ hpq hq1 hj1 hji hiq hk0 hkdeg hk1 hne hdeg
  set c := sBPR P Q j * tBPR P Q (i - 1) with hcdef
  set d := sBPR P Q k * tBPR P Q (j - 1) with hddef
  have hCc : (C c : K[X]) ≠ 0 := Polynomial.C_ne_zero.mpr hc_ne
  have hsc : c * (-d / c) = -d := by field_simp
  have hCA : C c * C (-d / c) = -(C d) := by rw [← Polynomial.C_mul, hsc, Polynomial.C_neg]
  have hCcc : C c * C c⁻¹ = 1 := by rw [← Polynomial.C_mul, mul_inv_cancel₀ hc_ne, Polynomial.C_1]
  apply mul_left_cancel₀ hCc
  rw [hspec, mul_add]
  linear_combination -(sResP P Q (i - 1) * hCA)
    - (transC P Q i j k * sResP P Q (j - 1)) * hCcc

/-- **BPR equation (8.14).**  `[sResP_{j-1}, sResP_{k-1}]ᵀ = T_j · [sResP_{i-1}, sResP_{j-1}]ᵀ`. -/
theorem transMat_mulVec (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hiq : i ≤ Q.natDegree + 1) {k : ℕ}
    (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    (transMat P Q i j k).mulVec ![sResP P Q (i - 1), sResP P Q (j - 1)]
      = ![sResP P Q (j - 1), sResP P Q (k - 1)] := by
  funext r
  fin_cases r
  · simp [transMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp only [transMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact (sResP_transition P Q hP hQ hpq hq1 hj1 hji hiq hk0 hkdeg hk1 hne hdeg).symm

end Azurite.BPR.Chapter8
