/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_7

/-!
# Definition 1.10: Extended Signed Remainder Sequence

The U- and V-cofactors of the extended signed remainder sequence
satisfy a Bezout-style identity (Lemma 1.11) and underpin Proposition
1.9.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

open Classical in
/-- BPR Definition 1.10: The U-cofactor of the extended signed remainder sequence.
    - `SRemU P Q 0 = 1`
    - `SRemU P Q 1 = 0`
    - `SRemU P Q (n+2) = −SRemU(n) + A · SRemU(n+1)` when `SRemS(n+1) ≠ 0`
    - `SRemU P Q (n+2) = 0` when `SRemS(n+1) = 0`

    where `A = Quo(SRemS(n), SRemS(n+1))` is the quotient from the Euclidean
    division step that produces `SRemS(n+2)`. -/
noncomputable def SRemU (P Q : K[X]) : ℕ → K[X]
  | 0 => 1
  | 1 => 0
  | n + 2 =>
    if SRemS P Q (n + 1) = 0 then 0
    else -(SRemU P Q n) + (SRemS P Q n / SRemS P Q (n + 1)) * SRemU P Q (n + 1)

open Classical in
/-- BPR Definition 1.10: The V-cofactor of the extended signed remainder sequence.
    - `SRemV P Q 0 = 0`
    - `SRemV P Q 1 = 1`
    - `SRemV P Q (n+2) = −SRemV(n) + A · SRemV(n+1)` when `SRemS(n+1) ≠ 0`
    - `SRemV P Q (n+2) = 0` when `SRemS(n+1) = 0`

    where `A = Quo(SRemS(n), SRemS(n+1))` is the quotient from the Euclidean
    division step that produces `SRemS(n+2)`. -/
noncomputable def SRemV (P Q : K[X]) : ℕ → K[X]
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if SRemS P Q (n + 1) = 0 then 0
    else -(SRemV P Q n) + (SRemS P Q n / SRemS P Q (n + 1)) * SRemV P Q (n + 1)

open Classical in
/-- Unfolding lemma for SRemU at index n+2 when SRemS(n+1) ≠ 0. -/
lemma SRemU_ss (P Q : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0) :
    SRemU P Q (n + 2) =
      -(SRemU P Q n) + (SRemS P Q n / SRemS P Q (n + 1)) * SRemU P Q (n + 1) := by
  simp [SRemU, hne]

open Classical in
/-- Unfolding lemma for SRemV at index n+2 when SRemS(n+1) ≠ 0. -/
lemma SRemV_ss (P Q : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0) :
    SRemV P Q (n + 2) =
      -(SRemV P Q n) + (SRemS P Q n / SRemS P Q (n + 1)) * SRemV P Q (n + 1) := by
  simp [SRemV, hne]

end Azurite.BPR
