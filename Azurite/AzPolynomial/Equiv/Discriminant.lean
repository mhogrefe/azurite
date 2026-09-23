/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Discriminant
import Azurite.AzPolynomial.Equiv.NewtonMatrix
import Azurite.AzPolynomial.Equiv.NewtonSum
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_9

/-!
# Correctness of `discriminantMonic`

For a monic polynomial `P : AzPolynomial K` over a field `K`, the
computable `P.discriminantMonic : K` lifts via `algebraMap K C` to the
mathematical discriminant `Azurite.BPR.Chapter4.disc (toPoly P) : C`
over any algebraically closed extension `C`.

Proof:
  * `discriminantMonic P = det (newtMatMonic P p)` (by definition).
  * Lifting through `algebraMap K C` gives the Newton matrix
    `newtMat (toPoly P) p` over `C` (each entry: `newtonSumMonic_toPoly`).
  * BPR Proposition 4.9 at `k = p` together with
    `sDisc_zero_eq_disc` identify this with `disc (toPoly P)`.
-/

namespace Azurite.AzPolynomial

open Azurite.BPR.Chapter4 Polynomial _root_.AzPolynomial

variable {K : Type _} [Field K] [DecidableEq K]
variable {C : Type _} [Field C] [Algebra K C] [IsAlgClosed C]

/-- **Correctness of `discriminantMonic`.** For a monic polynomial `P`,
    the algebra map sends the computable `P.discriminantMonic : K` to the
    BPR discriminant `disc (toPoly P) : C` in any algebraically closed
    extension `C/K`. -/
theorem discriminantMonic_toPoly (P : AzPolynomial K) (hMonic : P.Monic) :
    algebraMap K C P.discriminantMonic =
      (Azurite.BPR.Chapter4.disc (toPoly P) : C) := by
  classical
  set Q : K[X] := toPoly P with hQ_def
  set p : ℕ := P.natDegree with hp_def
  have hQ_natDeg : Q.natDegree = p := natDegree_toPoly P
  have hQ_monic : Q.Monic := (Monic_toPoly P).mpr hMonic
  have hcard : (Q.aroots C).card = p := by
    rw [← hQ_natDeg]; exact IsAlgClosed.card_aroots_eq_natDegree
  -- Apply Prop 4.9 with k = p.
  have hp_le : p ≤ (Q.aroots C).card := by rw [hcard]
  have h_prop49 := proposition_4_9 (C := C) Q p hp_le
  rw [hcard, Nat.sub_self] at h_prop49
  rw [sDisc_zero_eq_disc Q hQ_monic] at h_prop49
  -- h_prop49 : disc Q = a_p^{2p-2} · (newtMat Q p).det. For monic Q the
  -- leading factor is `1`.
  rw [show (algebraMap K C) Q.leadingCoeff = 1 from by
        rw [hQ_monic.leadingCoeff]; simp, one_pow, one_mul] at h_prop49
  rw [h_prop49]
  -- Goal: algebraMap K C P.discriminantMonic = (newtMat Q p).det
  unfold discriminantMonic
  rw [AzMatrix.det_eq_Matrix_det]
  show (algebraMap K C) ((Matrix.of (P.newtMatMonic p).toFn).det) = (newtMat Q p).det
  rw [RingHom.map_det (algebraMap K C)]
  -- Now both sides are determinants over C; show the matrices coincide.
  congr 1
  ext i j
  show (algebraMap K C) ((Matrix.of (P.newtMatMonic p).toFn) i j) =
    newtMat (C := C) Q p i j
  rw [Matrix.of_apply]
  rw [newtMatMonic_toFn]
  show algebraMap K C (P.newtonSumMonic (i.val + j.val)) = _
  rw [newtonSumMonic_toPoly P hMonic (i.val + j.val)]
  rfl

end Azurite.AzPolynomial
