/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_3.PdetSpecialCases

/-!
# BPR §8.3.2.1: the polynomial determinant over a ring

Equation (8.11) defines the `(m,n)`-polynomial determinant of a sequence
`𝒫 = P_1, …, P_m` of polynomials with coefficients in a commutative ring `D`,
and `pdet_{m,n}(𝒫) ∈ D[X]`. The construction is the same as over a field — the
minors `m_i` are determinants over `D` and the sum is in `D[X]` — so it is a
straightforward re-parameterization. Over a field it agrees with the
`𝓕`-valued `pdet` (`coe_pdet_eq_pdetRing`).
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {m n : ℕ}

section Ring

variable {D : Type*} [CommRing D]

/-- The `m × m` minor matrix of `𝒫` (with `D[X]` coefficients): the `(r,c)` entry
    is the coefficient of `X^{pdetColIdx n i c}` in `P_r`. -/
noncomputable def pdetMinorMatRing (n : ℕ) (P : Fin m → D[X]) (i : ℕ) :
    Matrix (Fin m) (Fin m) D :=
  fun r c => (P r).coeff (pdetColIdx n i c)

/-- The minor `m_i` of `Mat(𝒫)` over `D`. -/
noncomputable def pdetMinorRing (n : ℕ) (P : Fin m → D[X]) (i : ℕ) : D :=
  (pdetMinorMatRing n P i).det

/-- **BPR equation (8.11) over a commutative ring `D`.** The `(m,n)`-polynomial
    determinant of `𝒫 = P_1, …, P_m` with coefficients in `D`:
    `pdet_{m,n}(𝒫) = Σ_{i ≤ n-m} m_i X^i ∈ D[X]`, where `m_i` is the `m × m` minor
    of `Mat(𝒫)` on columns `1, …, m-1, n-i`. -/
noncomputable def pdetRing (n : ℕ) (P : Fin m → D[X]) : D[X] :=
  ∑ i : Fin (n - m + 1), pdetMinorRing n P (i : ℕ) • X ^ (i : ℕ)

/-- **The polynomial determinant commutes with any ring homomorphism.** Mapping
    the coefficients of each `P_i` through `φ : D →+* E` and then taking the
    determinant equals taking the determinant and then mapping the result. -/
theorem pdetRing_map {E : Type*} [CommRing E] (φ : D →+* E) (n : ℕ) (P : Fin m → D[X]) :
    pdetRing n (fun r => (P r).map φ) = (pdetRing n P).map φ := by
  rw [pdetRing, pdetRing, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hminor : pdetMinorRing n (fun r => (P r).map φ) (i : ℕ) = φ (pdetMinorRing n P (i : ℕ)) := by
    rw [pdetMinorRing, pdetMinorRing, RingHom.map_det]
    congr 1
    ext r c
    simp only [pdetMinorMatRing, RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coeff_map]
  rw [hminor, smul_eq_C_mul, smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]

end Ring

/-- The polynomial determinant of integer polynomials, mapped into `ℚ[X]`, is the
    polynomial determinant of the corresponding rational polynomials. -/
theorem pdetRing_intCast_rat (n : ℕ) (P : Fin m → ℤ[X]) :
    pdetRing n (fun r => (P r).map (Int.castRingHom ℚ))
      = (pdetRing n P).map (Int.castRingHom ℚ) :=
  pdetRing_map (Int.castRingHom ℚ) n P

section FieldCompat

variable {K : Type*} [Field K]

/-- Over a field, the ring-level polynomial determinant `pdetRing` agrees with the
    `𝓕`-valued `pdet` (under the coercion `𝓕_{n-m+1} ↪ K[X]`). -/
theorem coe_pdet_eq_pdetRing (P : Fin m → degreeLT K n) :
    ((pdet P : degreeLT K (n - m + 1)) : K[X]) = pdetRing n (fun r => (P r : K[X])) := by
  rw [pdet_coe, pdetRing]
  exact Finset.sum_congr rfl (fun i _ => rfl)

end FieldCompat

end Azurite.BPR.Chapter8
