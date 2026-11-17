/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Construct
import Azurite.AzNat.TangentNumbers
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.Sub

/-!
## Bernoulli numbers

`bernoulli n` is the Bernoulli number `B_n` as an exact rational, with the convention
`B_1 = −1/2` (Mathlib's `bernoulli`; DLMF §24.2(i)): `1, −1/2, 1/6, 0, −1/30, 0, 1/42, …`.
`bernoulliEvens m` is the table `#[B_2, B_4, …, B_{2m}]` (`B_{2j}` at index `j − 1`), which is
what an asymptotic series such as Stirling's needs.

The even ones come from the tangent numbers (`AzNat.tangentNumbers`, Algorithm 4.3 of Brent
and Zimmermann, *Modern Computer Arithmetic*, §4.7.2) by their (4.62),

  `B_{2j} = (−1)^(j−1) · 2j · T_j / (4^(2j) − 2^(2j))`,

and one reduction to lowest terms each (`bernoulliOfTangent`).  The tangent numbers are
positive integers computed without cancellation; the usual recurrence for the `B_n` themselves
needs `O(n²)` rational additions.  The cost is that of the table of tangent numbers,
`O(m³ log m)` bit operations for `B_2, …, B_{2m}` — also when a single `B_n` is asked for, so
callers that need several should take the table.

The proofs are in `Azurite/AzRat/Equiv/Bernoulli.lean`.
-/

namespace Azurite.AzRat

/-- `B_{2j}` from the tangent number `T = T_j` (`j ≥ 1`):
`(−1)^(j−1) · 2j · T / (4^(2j) − 2^(2j))`, reduced. -/
def bernoulliOfTangent (j : Nat) (T : AzNat) : AzRat :=
  ofSignAzNats (decide (j % 2 = 1)) (T.mulNat (2 * j))
    (((1 : AzNat) <<< (4 * j)) - ((1 : AzNat) <<< (2 * j)))

/-- The Bernoulli number `B_n` (`B_1 = −1/2`). -/
def bernoulli (n : Nat) : AzRat :=
  if n = 0 then 1
  else if n = 1 then ofSignAzNats false (AzNat.ofNat 1) (AzNat.ofNat 2)
  else if n % 2 = 1 then 0
  else bernoulliOfTangent (n / 2) ((AzNat.tangentNumbers (n / 2)).getD (n / 2 - 1) 0)

/-- The table `#[B_2, B_4, …, B_{2m}]`. -/
def bernoulliEvens (m : Nat) : Array AzRat :=
  let T := AzNat.tangentNumbers m
  Array.ofFn (n := m) fun i => bernoulliOfTangent (i.val + 1) (T.getD i.val 0)

end Azurite.AzRat
