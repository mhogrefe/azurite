/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.BasicCellStratumA
import Azurite.BasuPollackRoy.Chapter2.Section2_1.SignAtPoint

/-! # Stratum B of the Theorem 2.76 kernel: foundational sign-at-∞ loci

Stratum B is the `P_y ≡ 0` part of the basic-cell projection:
`{y | P_y ≡ 0 ∧ ∃ x, ⋀_{q ∈ 𝒬} q_y(x) > 0}`. Via BPR Lemma 2.75, the nonemptiness
of the all-positive realization of the family `𝒬_y` is decided by: the sign of each
`q_y` at `−∞`, the sign at `+∞`, and a `matrixLocus`-style Tarski-query condition
for `(∏ 𝒬_y)'`.

This file builds the foundational **sign-at-±∞ loci**: that
`{y | signAtPosInfty(P_y) = +}` and `{y | signAtNegInfty(P_y) = +}` are semialgebraic
over `D`. The leading coefficient of `P_y` is `aeval y (P.coeff n)` on the locus where
`deg P_y = n` (a `degLocus`), so each sign-at-∞ condition is a finite union over the
degree `n` of `degLocus n ∩ {sign of the n-th coefficient}` — a `pos_locus` (with a
degree-parity twist at `−∞`).
-/

open _root_.Polynomial

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {D : Type*} [CommRing D] [Algebra D R]

/-- The locus `{y | deg P_y = d}` is semialgebraic over `D`: it is the realization of
the quantifier-free `degFormula`. -/
theorem degLocus_isSemialgebraicSetOver (P : Polynomial (MvPolynomial (Fin k) D))
    (d : WithBot ℕ) :
    IsSemialgebraicSetOver D
      {y : Fin k → R | (P.map (MvPolynomial.aeval y).toRingHom).degree = d} := by
  rw [← realization_degFormula (C := R),
    ← Formula.realization_mapAtom_toOrderedFieldAtom (degFormula P d)]
  exact qfRealizable_isSemialgebraicSetOver
    (by rw [Formula.mapAtom_isQF]; exact degFormula_isQF P d)

/-- `{y | 0 < (P_y).leadingCoeff}` is semialgebraic over `D`: partition by the actual
degree `n` (a `degLocus`), on which the leading coefficient is `aeval y (P.coeff n)`. -/
theorem leadingCoeffSign_pos_locus (P : Polynomial (MvPolynomial (Fin k) D)) :
    IsSemialgebraicSetOver D
      {y : Fin k → R | 0 < (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff} := by
  classical
  have hset : {y : Fin k → R | 0 < (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff} =
      ⋃ n ∈ Finset.range (P.natDegree + 1),
        {y : Fin k → R | (P.map (MvPolynomial.aeval y).toRingHom).degree = (n : ℕ) ∧
          0 < MvPolynomial.aeval y (P.coeff n)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · intro hpos
      have hne : P.map (MvPolynomial.aeval y).toRingHom ≠ 0 := by
        rintro h; rw [h] at hpos; simp at hpos
      set m := (P.map (MvPolynomial.aeval y).toRingHom).natDegree with hm
      have hc : (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff
          = MvPolynomial.aeval y (P.coeff m) := by
        rw [Polynomial.leadingCoeff, ← hm, Polynomial.coeff_map]; rfl
      refine ⟨m, ?_, Polynomial.degree_eq_natDegree hne, ?_⟩
      · have := Polynomial.natDegree_map_le (f := (MvPolynomial.aeval y).toRingHom) (p := P)
        omega
      · rwa [hc] at hpos
    · rintro ⟨n, _, hdeg, hcpos⟩
      have hnd : (P.map (MvPolynomial.aeval y).toRingHom).natDegree = n := by
        rw [Polynomial.natDegree, hdeg]; rfl
      have hc : (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff
          = MvPolynomial.aeval y (P.coeff n) := by
        rw [Polynomial.leadingCoeff, hnd, Polynomial.coeff_map]; rfl
      rwa [hc]
  rw [hset]
  apply IsSemialgebraicSetOver.finsetBiUnion
  intro n _
  exact (degLocus_isSemialgebraicSetOver P (n : ℕ)).inter (IsSemialgebraicSetOver.gtZero (P.coeff n))

/-- `{y | signAtPosInfty(P_y) = +}` is semialgebraic over `D` (the sign at `+∞` is the
sign of the leading coefficient). -/
theorem signAtPosInfty_pos_locus (P : Polynomial (MvPolynomial (Fin k) D)) :
    IsSemialgebraicSetOver D
      {y : Fin k → R | signAtPosInfty (P.map (MvPolynomial.aeval y).toRingHom) = SignType.pos} := by
  have hset : {y : Fin k → R |
        signAtPosInfty (P.map (MvPolynomial.aeval y).toRingHom) = SignType.pos} =
      {y : Fin k → R | 0 < (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff} := by
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, signAtPosInfty_eq_sign_leadingCoeff]
    exact sign_eq_one_iff
  rw [hset]; exact leadingCoeffSign_pos_locus P

/-- `{y | signAtNegInfty(P_y) = +}` is semialgebraic over `D` (the sign at `−∞` is
`(-1)^{deg} · sign(leadingCoeff)`; on `deg P_y = n` the condition is the sign of
`(-1)^n · (n-th coefficient)`). -/
theorem signAtNegInfty_pos_locus (P : Polynomial (MvPolynomial (Fin k) D)) :
    IsSemialgebraicSetOver D
      {y : Fin k → R | signAtNegInfty (P.map (MvPolynomial.aeval y).toRingHom) = SignType.pos} := by
  classical
  have key : ∀ (z : R) (m : ℕ),
      ((-1 : SignType) ^ m * SignType.sign z = SignType.pos) ↔ (0 < (-1 : R) ^ m * z) := by
    intro z m
    rw [← sign_eq_one_iff, sign_mul, sign_pow, sign_neg neg_one_lt_zero]; rfl
  have hset : {y : Fin k → R |
        signAtNegInfty (P.map (MvPolynomial.aeval y).toRingHom) = SignType.pos} =
      ⋃ n ∈ Finset.range (P.natDegree + 1),
        {y : Fin k → R | (P.map (MvPolynomial.aeval y).toRingHom).degree = (n : ℕ) ∧
          0 < MvPolynomial.aeval y ((-1) ^ n * P.coeff n)} := by
    ext y
    have haeval : ∀ (j : ℕ), MvPolynomial.aeval y ((-1) ^ j * P.coeff j)
        = (-1 : R) ^ j * MvPolynomial.aeval y (P.coeff j) := fun j => by
      rw [map_mul, map_pow, map_neg, map_one]
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
      signAtNegInfty_eq_sign_leadingCoeff]
    constructor
    · intro hsign
      have hne : P.map (MvPolynomial.aeval y).toRingHom ≠ 0 := by
        rintro h; rw [h] at hsign; simp at hsign
      set m := (P.map (MvPolynomial.aeval y).toRingHom).natDegree with hm
      have hlc : (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff
          = MvPolynomial.aeval y (P.coeff m) := by
        rw [Polynomial.leadingCoeff, ← hm, Polynomial.coeff_map]; rfl
      refine ⟨m, ?_, Polynomial.degree_eq_natDegree hne, ?_⟩
      · have := Polynomial.natDegree_map_le (f := (MvPolynomial.aeval y).toRingHom) (p := P)
        omega
      · rw [haeval, ← key, ← hlc]; exact hsign
    · rintro ⟨n, _, hdeg, hcpos⟩
      have hnd : (P.map (MvPolynomial.aeval y).toRingHom).natDegree = n := by
        rw [Polynomial.natDegree, hdeg]; rfl
      have hlc : (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff
          = MvPolynomial.aeval y (P.coeff n) := by
        rw [Polynomial.leadingCoeff, hnd, Polynomial.coeff_map]; rfl
      rw [hnd, hlc, haeval] at *
      exact (key _ n).mpr hcpos
  rw [hset]
  apply IsSemialgebraicSetOver.finsetBiUnion
  intro n _
  exact (degLocus_isSemialgebraicSetOver P (n : ℕ)).inter
    (IsSemialgebraicSetOver.gtZero ((-1) ^ n * P.coeff n))

end Azurite.BPR
