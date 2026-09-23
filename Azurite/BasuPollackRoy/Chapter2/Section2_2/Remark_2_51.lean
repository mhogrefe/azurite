/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_50

/-!
# BPR Remark 2.51

Given Sturm's theorem (Theorem 2.50), a nonzero polynomial `P` over a
real closed field `R` has a real root iff

`Var(SRemS(P, P'); −∞, +∞) > 0`.

This gives a (terminating, computable in principle) decision procedure
for "does `P` have a real root" via the signed remainder sequence.
-/

open scoped Polynomial
open Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

open Classical in
/-- **BPR Remark 2.51.** A nonzero polynomial `P` over a real closed
    field `R` has a real root iff `Var(SRemS(P, P'); −∞, +∞) > 0`.

    Immediate from BPR Theorem 2.50: the right side counts the distinct
    real roots of `P`, so positivity is equivalent to existence. -/
theorem remark_2_51
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P : R[X]) (hP : P ≠ 0) :
    (∃ x : R, P.IsRoot x) ↔
      0 < ((varAt (SRemSList P P.derivative
          (P.derivative.natDegree + 2))
          (.negInf : ExtendedPoint R) : ℤ) -
        (varAt (SRemSList P P.derivative
          (P.derivative.natDegree + 2))
          (.posInf : ExtendedPoint R) : ℤ)) := by
  -- Hypotheses for Theorem 2.50 at the `(-∞, +∞)` interval.
  have h_aP : ExtendedPoint.evalPoly P (.negInf : ExtendedPoint R) ≠ 0 := by
    show (-1 : R) ^ P.natDegree * P.leadingCoeff ≠ 0
    apply mul_ne_zero
    · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    · exact mt Polynomial.leadingCoeff_eq_zero.mp hP
  have h_bP : ExtendedPoint.evalPoly P (.posInf : ExtendedPoint R) ≠ 0 := by
    show P.leadingCoeff ≠ 0
    exact mt Polynomial.leadingCoeff_eq_zero.mp hP
  have hab : ExtendedPoint.Lt (.negInf : ExtendedPoint R) .posInf := by trivial
  rw [theorem_2_50 hIVP P hP .negInf .posInf hab h_aP h_bP]
  -- `openInterval .negInf .posInf = Set.univ`, so the filter is the identity.
  have h_filter_univ : P.roots.toFinset.filter
        (· ∈ ExtendedPoint.openInterval (R := R) .negInf .posInf) =
      P.roots.toFinset :=
    Finset.filter_eq_self.mpr (fun x _ => Set.mem_univ x)
  rw [h_filter_univ]
  constructor
  · rintro ⟨x, hx⟩
    have h_in : x ∈ P.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hx
    exact_mod_cast Finset.card_pos.mpr ⟨x, h_in⟩
  · intro h
    have h_pos : 0 < P.roots.toFinset.card := by exact_mod_cast h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp h_pos
    refine ⟨x, ?_⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP] at hx
    exact hx

end Azurite.BPR
