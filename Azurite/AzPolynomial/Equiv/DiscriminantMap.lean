/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Discriminant
import Azurite.AzPolynomial.Equiv.NewtonMatrix
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Map

/-!
# `discriminantMonic` commutes with ring homomorphisms (CommRing-level)

For any ring homomorphism `f : R →+* S` between CommRings (both equipped
with `HasDet`), and any monic `P : AzPolynomial R`,

  `f (P.discriminantMonic) = (P.map f).discriminantMonic`.

This is the pure CommRing-level functoriality: the discriminant is a
polynomial expression in the coefficients, so transports along ring
homomorphisms. Composed with the Field-level theorem
`discriminantMonic_toPoly`, it gives correctness over any integral
domain via the fraction field.
-/

namespace Azurite.AzPolynomial

open Polynomial _root_.AzPolynomial

variable {R S : Type _} [CommRing R] [CommRing S] [DecidableEq R] [DecidableEq S]

/-! ### Auxiliary: degree and coefficients commute with `.map f` -/

omit [DecidableEq R] in
/-- The `natDegree` of a monic polynomial is preserved by any ring
    homomorphism (since the leading coefficient is `1`, which maps to a
    nonzero element in any `Nontrivial` codomain). -/
theorem Monic.natDegree_map [Nontrivial S] (f : R →+* S) (P : AzPolynomial R)
    (hMonic : P.Monic) :
    (P.map f).natDegree = P.natDegree := by
  have h1 : (toPoly (P.map f)).natDegree = (P.map f).natDegree :=
    natDegree_toPoly _
  have h2 : (toPoly P).natDegree = P.natDegree := natDegree_toPoly _
  have hQM : (toPoly P).Monic := (Monic_toPoly P).mpr hMonic
  have h3 : ((toPoly P).map f).natDegree = (toPoly P).natDegree :=
    hQM.natDegree_map f
  rw [← h1, toPoly_map, h3, h2]

omit [DecidableEq R] in
/-- The `i`-th coefficient commutes with the ring-hom map. -/
theorem coeff_map (f : R →+* S) (P : AzPolynomial R) (i : ℕ) :
    (P.map f).coeff i = f (P.coeff i) := by
  have h1 : (P.map f).coeff i = (toPoly (P.map f)).coeff i :=
    (coeff_toPoly_eq _ i).symm
  have h2 : P.coeff i = (toPoly P).coeff i := (coeff_toPoly_eq _ i).symm
  rw [h1, toPoly_map, Polynomial.coeff_map, h2]

/-! ### `newtonSumMonic` commutes with `.map f` -/

omit [DecidableEq R] in
/-- The iterative Newton-sum recurrence commutes with any ring
    homomorphism (when applied to a monic polynomial). -/
theorem newtonSumMonic_map [Nontrivial S] (f : R →+* S) (P : AzPolynomial R)
    (hMonic : P.Monic) (k : ℕ) :
    (P.map f).newtonSumMonic k = f (P.newtonSumMonic k) := by
  have h_deg : (P.map f).natDegree = P.natDegree := Monic.natDegree_map f P hMonic
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      simp only [newtonSumMonic]
      rw [h_deg, map_natCast]
    | n + 1 =>
      simp only [newtonSumMonic]
      rw [h_deg]
      rw [map_sub, map_sum]
      congr 1
      · -- Leading term: commutes with f via map_natCast, coeff_map, map_mul, if-split.
        split_ifs with h_le
        · rw [map_mul, map_natCast, coeff_map]
        · exact (map_zero f).symm
      · -- Sum: each summand commutes.
        apply Finset.sum_congr rfl
        intro l h_l
        rw [Finset.mem_range] at h_l
        rw [map_mul]
        rw [coeff_map]
        congr 1
        exact ih (n - l) (by omega)

/-! ### `newtMatMonic` commutes with `.map f` -/

omit [DecidableEq R] in
/-- The Newton matrix's entries commute with the ring-hom map. -/
theorem newtMatMonic_map [Nontrivial S] (f : R →+* S) (P : AzPolynomial R)
    (hMonic : P.Monic) (k : ℕ) (i j : Fin k) :
    ((P.map f).newtMatMonic k).toFn i j =
      f ((P.newtMatMonic k).toFn i j) := by
  rw [newtMatMonic_toFn, newtMatMonic_toFn]
  exact newtonSumMonic_map f P hMonic (i.val + j.val)

/-! ### `discriminantMonic` commutes with `.map f` -/

variable [AzMatrix.HasDet R] [AzMatrix.HasDet S] [Nontrivial S]

/-- **CommRing-level naturality of the discriminant.** For any ring
    homomorphism `f : R →+* S` (both `CommRing`s with `HasDet`, codomain
    `Nontrivial`) and any monic `P : AzPolynomial R`,

      `f (P.discriminantMonic) = (P.map f).discriminantMonic`.

    The proof tracks `f` through `det_eq_Matrix_det`, `RingHom.map_det`,
    `newtMatMonic_toFn`, and the entry-wise `newtonSumMonic_map`. -/
theorem discriminantMonic_map (f : R →+* S) (P : AzPolynomial R)
    (hMonic : P.Monic) :
    f (P.discriminantMonic) = (P.map f).discriminantMonic := by
  have h_deg : (P.map f).natDegree = P.natDegree :=
    Monic.natDegree_map f P hMonic
  unfold discriminantMonic
  rw [h_deg]
  rw [AzMatrix.det_eq_Matrix_det, AzMatrix.det_eq_Matrix_det]
  show f ((Matrix.of (P.newtMatMonic P.natDegree).toFn).det)
    = (Matrix.of ((P.map f).newtMatMonic P.natDegree).toFn).det
  rw [RingHom.map_det f]
  congr 1
  funext i j
  show f ((Matrix.of (P.newtMatMonic P.natDegree).toFn) i j) =
    (Matrix.of ((P.map f).newtMatMonic P.natDegree).toFn) i j
  rw [Matrix.of_apply, Matrix.of_apply]
  exact (newtMatMonic_map f P hMonic P.natDegree i j).symm

end Azurite.AzPolynomial
