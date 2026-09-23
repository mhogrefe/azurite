/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Corollary_2_23

/-!
# BPR Corollary 2.24: Monotonicity from derivative sign

**Corollary 2.24 (BPR).** Let `R` be an ordered field with the intermediate
value property, `P ∈ R[X]`, `a < b`.

* If `P' > 0` on `(a, b)`, then `P` is strictly increasing on `[a, b]`.
* If `P' < 0` on `(a, b)`, then `P` is strictly decreasing on `[a, b]`.

Both follow from the polynomial mean value theorem (Corollary 2.23).
-/

namespace Azurite.BPR.Corollary2_24

open Polynomial Azurite.BPR Azurite.BPR.Theorem2_11 Azurite.BPR.Corollary2_23

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Corollary 2.24 (increasing case).** If `P' > 0` on `(a, b)`, then
    `P` is strictly increasing on `[a, b]`. -/
theorem corollary_2_24_increasing (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) {a b : R} (_hab : a < b)
    (hP' : ∀ x ∈ Set.Ioo a b, 0 < (derivative P).eval x) :
    StrictMonoOn (fun x => P.eval x) (Set.Icc a b) := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hMVT⟩ := corollary_2_23 hIVP P hxy
  have hc_ab : c ∈ Set.Ioo a b :=
    ⟨lt_of_le_of_lt hx.1 hc.1, lt_of_lt_of_le hc.2 hy.2⟩
  linarith [mul_pos (sub_pos.mpr hxy) (hP' c hc_ab)]

/-- **BPR Corollary 2.24 (decreasing case).** If `P' < 0` on `(a, b)`, then
    `P` is strictly decreasing on `[a, b]`. -/
theorem corollary_2_24_decreasing (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) {a b : R} (_hab : a < b)
    (hP' : ∀ x ∈ Set.Ioo a b, (derivative P).eval x < 0) :
    StrictAntiOn (fun x => P.eval x) (Set.Icc a b) := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hMVT⟩ := corollary_2_23 hIVP P hxy
  have hc_ab : c ∈ Set.Ioo a b :=
    ⟨lt_of_le_of_lt hx.1 hc.1, lt_of_lt_of_le hc.2 hy.2⟩
  linarith [mul_neg_of_pos_of_neg (sub_pos.mpr hxy) (hP' c hc_ab)]

/-- **Corollary 2.24 (increasing), real closed form.** -/
theorem corollary_2_24_increasing_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) {a b : R} :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    a < b →
    (∀ x ∈ Set.Ioo a b, 0 < (derivative P).eval x) →
    StrictMonoOn (fun x => P.eval x) (Set.Icc a b) := by
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  have : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact corollary_2_24_increasing theorem_2_11_b_c P

/-- **Corollary 2.24 (decreasing), real closed form.** -/
theorem corollary_2_24_decreasing_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) {a b : R} :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    a < b →
    (∀ x ∈ Set.Ioo a b, (derivative P).eval x < 0) →
    StrictAntiOn (fun x => P.eval x) (Set.Icc a b) := by
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  have : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact corollary_2_24_decreasing theorem_2_11_b_c P

end Azurite.BPR.Corollary2_24
