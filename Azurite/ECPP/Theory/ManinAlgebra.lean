/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic

/-!
# Manin's proof of the Hasse bound: the polynomial algebra of the Basic Identity

After A. W. Knapp, *Elliptic Curves*, §X.3, Lemma 10.8 (the proof that Chahal–Osserman cite
and omit).  There `X_n = P/Q` and `X_{n−1} = A/B`, `X_{n+1} = C/D` are in lowest terms in
`𝔽_p(x)`, and (10.19), (10.20) say

  `X_{n−1} X_{n+1} = N₁/M`,  `½ (X_{n−1} + X_{n+1}) = N₂/M`

with `N₁ = (Px − aQ)² − 4bQ(Qx + P)`, `N₂ = PQx² + P²x + axQ² + 2bQ² + aPQ`,
`M = (Qx − P)²` (`formN1`, `formN2`, `formM`).  This file has the three facts about
polynomials that turn these into `d_{n−1} + d_{n+1} = 2 d_n + 2` for the heights
`d = max (deg num, deg den)`; no elliptic curve appears in it.

* `isUnit_of_dvd_forms`: `N₁`, `N₂`, `M` have no common factor (for coprime `P`, `Q` and
  `4a³ + 27b² ≠ 0`): modulo a prime factor of `Qx − P` they are `Q² g` and `2Q² f` with
  `f = x³ + ax + b`, `g = (x² − a)² − 8bx`, and `(3x² + 4a) g − (3x³ − 5ax − 27b) f
  = 4a³ + 27b²`.
* `exists_unit_of_relations`: hence `BD = M`, `AC = N₁`, `AD + BC = 2N₂` up to one common
  unit.  (Knapp's (10.21)–(10.22); his text takes `gcd(N₁, M) = 1` for granted, which need
  not hold — the argument here uses the three forms together.)
* `height_add_height`: `max(deg A, deg B) + max(deg C, deg D)
  = max(deg AC, deg BD, deg(AD + BC))`, and `max_natDegree_forms`: the maximum of the degrees
  of the three forms is `2 max(deg P, deg Q) + 2`.  (In place of Knapp's cases (a)–(d).)
-/

namespace Azurite.ECPP.Manin

open Polynomial

variable {k : Type*} [Field k]

/-- `N₁ = (Px − aQ)² − 4bQ(Qx + P)`, the numerator of `X_{n−1} X_{n+1}`. -/
noncomputable def formN1 (a b : k) (P Q : k[X]) : k[X] :=
  (P * X - C a * Q) ^ 2 - 4 * C b * Q * (Q * X + P)

/-- `N₂ = PQx² + P²x + axQ² + 2bQ² + aPQ`, the numerator of `½ (X_{n−1} + X_{n+1})`. -/
noncomputable def formN2 (a b : k) (P Q : k[X]) : k[X] :=
  P * Q * X ^ 2 + P ^ 2 * X + C a * X * Q ^ 2 + 2 * C b * Q ^ 2 + C a * P * Q

/-- `M = (Qx − P)²`, the common denominator. -/
noncomputable def formM (P Q : k[X]) : k[X] := (Q * X - P) ^ 2

theorem isUnit_two (h2 : (2 : k) ≠ 0) : IsUnit (2 : k[X]) := by
  have : (2 : k[X]) = C 2 := (map_ofNat C 2).symm
  rw [this]
  exact isUnit_C.mpr (IsUnit.mk0 _ h2)

/-- **The three forms have no common factor.** -/
theorem isUnit_of_dvd_forms (a b : k) (h2 : (2 : k) ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    {P Q : k[X]} (hPQ : IsCoprime P Q) (hM : Q * X - P ≠ 0) {T : k[X]}
    (h1 : T ∣ formN1 a b P Q) (hN2 : T ∣ formN2 a b P Q) (hTM : T ∣ formM P Q) : IsUnit T := by
  by_contra hT
  have hT0 : T ≠ 0 := by
    rintro rfl
    exact pow_ne_zero 2 hM (zero_dvd_iff.mp hTM)
  obtain ⟨F, hF, hFT⟩ := WfDvdMonoid.exists_irreducible_factor hT hT0
  have hFp : Prime F := hF.prime
  have hFM : F ∣ Q * X - P := hFp.dvd_of_dvd_pow (hFT.trans hTM)
  have hFQ : ¬ F ∣ Q := by
    intro hQ
    have hP : F ∣ P := by
      have : P = Q * X - (Q * X - P) := by ring
      rw [this]
      exact dvd_sub (hQ.mul_right X) hFM
    exact hF.not_isUnit (hPQ.isUnit_of_dvd' hP hQ)
  -- the forms modulo `Qx − P`
  have e1 : formN1 a b P Q = Q ^ 2 * ((X ^ 2 - C a) ^ 2 - 8 * C b * X)
      + (Q * X - P) * (-X * (P * X + Q * X ^ 2) + 2 * C a * Q * X + 4 * C b * Q) := by
    unfold formN1
    ring
  have e2 : formN2 a b P Q = 2 * (Q ^ 2 * (X ^ 3 + C a * X + C b))
      + (Q * X - P) * (-X * (P + 2 * Q * X) - C a * Q) := by
    unfold formN2
    ring
  have hg : F ∣ (X ^ 2 - C a) ^ 2 - 8 * C b * X := by
    have h : F ∣ Q ^ 2 * ((X ^ 2 - C a) ^ 2 - 8 * C b * X) := by
      have := hFT.trans h1
      rw [e1] at this
      exact (dvd_add_left (hFM.mul_right _)).mp this
    rcases hFp.dvd_or_dvd h with h' | h'
    · exact absurd (hFp.dvd_of_dvd_pow h') hFQ
    · exact h'
  have hf : F ∣ X ^ 3 + C a * X + C b := by
    have h : F ∣ 2 * (Q ^ 2 * (X ^ 3 + C a * X + C b)) := by
      have := hFT.trans hN2
      rw [e2] at this
      exact (dvd_add_left (hFM.mul_right _)).mp this
    rcases hFp.dvd_or_dvd h with h' | h'
    · exact absurd (isUnit_of_dvd_unit h' (isUnit_two h2)) hF.not_isUnit
    · rcases hFp.dvd_or_dvd h' with h'' | h''
      · exact absurd (hFp.dvd_of_dvd_pow h'') hFQ
      · exact h''
  have hid : (3 * X ^ 2 + 4 * C a) * ((X ^ 2 - C a) ^ 2 - 8 * C b * X)
      - (3 * X ^ 3 - 5 * C a * X - 27 * C b) * (X ^ 3 + C a * X + C b)
      = C (4 * a ^ 3 + 27 * b ^ 2) := by
    simp only [C_add, C_mul, C_pow, C_ofNat]
    ring
  have hc : F ∣ C (4 * a ^ 3 + 27 * b ^ 2) := by
    rw [← hid]
    exact dvd_sub (hg.mul_left _) (hf.mul_left _)
  exact hF.not_isUnit (isUnit_of_dvd_unit hc (isUnit_C.mpr (IsUnit.mk0 _ hΔ)))

/-- **`BD = M`, `AC = N₁`, `AD + BC = 2N₂` up to a common unit**: from the two relations
between fractions in lowest terms, when `N₁`, `N₂`, `M` have no common factor. -/
theorem exists_unit_of_relations (h2 : (2 : k) ≠ 0) {A B C D N1 N2 M : k[X]}
    (hAB : IsCoprime A B) (hCD : IsCoprime C D) (hB : B ≠ 0) (hD : D ≠ 0)
    (h1 : A * C * M = B * D * N1) (hs : (A * D + B * C) * M = 2 * (B * D) * N2)
    (hgcd : ∀ T : k[X], T ∣ N1 → T ∣ N2 → T ∣ M → IsUnit T) :
    ∃ T : k[X], IsUnit T ∧ M = B * D * T ∧ N1 = A * C * T ∧ 2 * N2 = (A * D + B * C) * T := by
  -- `B ∣ M`
  have hBCM : B ∣ C * M := by
    have h : B ∣ A * (C * M) := ⟨D * N1, by rw [← mul_assoc, h1]; ring⟩
    exact hAB.symm.dvd_of_dvd_mul_left h
  have hBDM : B ∣ D * M := by
    have h : B ∣ A * (D * M) := by
      have e : A * (D * M) = (A * D + B * C) * M - B * (C * M) := by ring
      rw [e, hs]
      exact dvd_sub ⟨2 * D * N2, by ring⟩ (dvd_mul_right B _)
    exact hAB.symm.dvd_of_dvd_mul_left h
  have hBM : B ∣ M := by
    obtain ⟨u, v, huv⟩ := hCD
    have e : M = u * (C * M) + v * (D * M) := by
      calc M = (u * C + v * D) * M := by rw [huv, one_mul]
        _ = u * (C * M) + v * (D * M) := by ring
    rw [e]
    exact dvd_add (hBCM.mul_left u) (hBDM.mul_left v)
  obtain ⟨M', rfl⟩ := hBM
  have h1' : A * C * M' = D * N1 := by
    apply mul_left_cancel₀ hB
    rw [show B * (A * C * M') = A * C * (B * M') by ring, h1]
    ring
  have hs' : (A * D + B * C) * M' = 2 * D * N2 := by
    apply mul_left_cancel₀ hB
    rw [show B * ((A * D + B * C) * M') = (A * D + B * C) * (B * M') by ring, hs]
    ring
  -- `D ∣ M'`
  have hDAM : D ∣ A * M' := by
    have h : D ∣ C * (A * M') := ⟨N1, by rw [← h1']; ring⟩
    exact hCD.symm.dvd_of_dvd_mul_left h
  have hDBM : D ∣ B * M' := by
    have h : D ∣ C * (B * M') := by
      have e : C * (B * M') = (A * D + B * C) * M' - D * (A * M') := by ring
      rw [e, hs']
      exact dvd_sub ⟨2 * N2, by ring⟩ (dvd_mul_right D _)
    exact hCD.symm.dvd_of_dvd_mul_left h
  have hDM : D ∣ M' := by
    obtain ⟨u, v, huv⟩ := hAB
    have e : M' = u * (A * M') + v * (B * M') := by
      calc M' = (u * A + v * B) * M' := by rw [huv, one_mul]
        _ = u * (A * M') + v * (B * M') := by ring
    rw [e]
    exact dvd_add (hDAM.mul_left u) (hDBM.mul_left v)
  obtain ⟨T, rfl⟩ := hDM
  have e1 : N1 = A * C * T := by
    apply mul_left_cancel₀ hD
    rw [← h1']
    ring
  have e2 : 2 * N2 = (A * D + B * C) * T := by
    apply mul_left_cancel₀ hD
    rw [show D * (2 * N2) = 2 * D * N2 by ring, ← hs']
    ring
  have hT2 : T ∣ N2 := by
    have h : T ∣ 2 * N2 := ⟨A * D + B * C, by rw [e2]; ring⟩
    exact ((isUnit_two h2).dvd_mul_left).mp h
  exact ⟨T, hgcd T ⟨A * C, by rw [e1]; ring⟩ hT2 ⟨B * D, by ring⟩, by ring, e1, e2⟩

/-- **The heights add up to the largest of three degrees.** -/
theorem height_add_height {A B C D : k[X]} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hD : D ≠ 0) :
    max A.natDegree B.natDegree + max C.natDegree D.natDegree
      = max (max (A * C).natDegree (B * D).natDegree) (A * D + B * C).natDegree := by
  rw [natDegree_mul hA hC, natDegree_mul hB hD]
  have hle : (A * D + B * C).natDegree
      ≤ max (A.natDegree + D.natDegree) (B.natDegree + C.natDegree) := by
    refine (natDegree_add_le _ _).trans ?_
    rw [natDegree_mul hA hD, natDegree_mul hB hC]
  have hlt1 : B.natDegree + C.natDegree < A.natDegree + D.natDegree →
      (A * D + B * C).natDegree = A.natDegree + D.natDegree := by
    intro h
    rw [natDegree_add_eq_left_of_natDegree_lt (by rwa [natDegree_mul hB hC,
      natDegree_mul hA hD]), natDegree_mul hA hD]
  have hlt2 : A.natDegree + D.natDegree < B.natDegree + C.natDegree →
      (A * D + B * C).natDegree = B.natDegree + C.natDegree := by
    intro h
    rw [natDegree_add_eq_right_of_natDegree_lt (by rwa [natDegree_mul hB hC,
      natDegree_mul hA hD]), natDegree_mul hB hC]
  rcases lt_trichotomy (A.natDegree + D.natDegree) (B.natDegree + C.natDegree) with h | h | h
  · have := hlt2 h
    omega
  · omega
  · have := hlt1 h
    omega

/-- **The largest degree of the three forms is `2 max(deg P, deg Q) + 2`.** -/
theorem max_natDegree_forms (a b : k) {P Q : k[X]} (hQ : Q ≠ 0) :
    max (max (formN1 a b P Q).natDegree (formM P Q).natDegree) (formN2 a b P Q).natDegree
      = 2 * max P.natDegree Q.natDegree + 2 := by
  obtain ⟨e, he⟩ : ∃ e, e = max P.natDegree Q.natDegree := ⟨_, rfl⟩
  rw [← he]
  have hPe : P.natDegree ≤ e := he ▸ le_max_left _ _
  have hQe : Q.natDegree ≤ e := he ▸ le_max_right _ _
  have u1 : (formN1 a b P Q).natDegree ≤ 2 * e + 2 := by
    unfold formN1
    compute_degree
    omega
  have u2 : (formN2 a b P Q).natDegree ≤ 2 * e + 2 := by
    unfold formN2
    compute_degree
    omega
  have u3 : (formM P Q).natDegree ≤ 2 * e + 2 := by
    unfold formM
    compute_degree
    omega
  have hX : (X : k[X]) ≠ 0 := X_ne_zero
  by_cases hcase : P ≠ 0 ∧ Q.natDegree ≤ P.natDegree
  · -- the term `P² x²` of `N₁` dominates
    obtain ⟨hP0, hle⟩ := hcase
    have hep : e = P.natDegree := by rw [he]; exact max_eq_left hle
    have hsplit : formN1 a b P Q = P ^ 2 * X ^ 2
        + (-2 * C a * P * Q * X + C a ^ 2 * Q ^ 2 - 4 * C b * Q * (Q * X + P)) := by
      unfold formN1
      ring
    have hmain : (P ^ 2 * X ^ 2).natDegree = 2 * e + 2 := by
      rw [natDegree_mul (pow_ne_zero 2 hP0) (pow_ne_zero 2 hX), natDegree_pow, natDegree_pow,
        natDegree_X, hep]
    have hrest : (-2 * C a * P * Q * X + C a ^ 2 * Q ^ 2 - 4 * C b * Q * (Q * X + P)).natDegree
        ≤ 2 * e + 1 := by
      compute_degree
      omega
    have h1 : (formN1 a b P Q).natDegree = 2 * e + 2 := by
      rw [hsplit, natDegree_add_eq_left_of_natDegree_lt (by omega), hmain]
    omega
  · -- `Qx` dominates `P` in `M`
    have hlt : P.natDegree < (Q * X).natDegree := by
      rw [natDegree_mul hQ hX, natDegree_X]
      by_cases hP0 : P = 0
      · rw [hP0, natDegree_zero]
        omega
      · have : ¬ Q.natDegree ≤ P.natDegree := fun h => hcase ⟨hP0, h⟩
        omega
    have heq : e = Q.natDegree := by
      rw [he]
      refine max_eq_right ?_
      rw [natDegree_mul hQ hX, natDegree_X] at hlt
      by_cases hP0 : P = 0
      · rw [hP0, natDegree_zero]
        omega
      · have : ¬ Q.natDegree ≤ P.natDegree := fun h => hcase ⟨hP0, h⟩
        omega
    have h3 : (formM P Q).natDegree = 2 * e + 2 := by
      unfold formM
      rw [natDegree_pow, natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_mul hQ hX,
        natDegree_X, heq]
      ring
    omega

end Azurite.ECPP.Manin
