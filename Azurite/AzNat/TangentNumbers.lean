/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.MulNat
import Azurite.AzNat.Add
import Azurite.AzNat.Factorial

/-!
## Tangent numbers

The tangent numbers `T_1, T_2, … = 1, 2, 16, 272, 7936, …` are the coefficients of
`tan x = ∑_{j≥1} T_j x^(2j−1)/(2j−1)!`.  `tangentNumbers m` is the array `#[T_1, …, T_m]`
(`T_j` at index `j − 1`), by Algorithm 4.3 (TangentNumbers) of Brent and Zimmermann, *Modern
Computer Arithmetic*, §4.7.2:

```
T_j ← (j − 1)!                                   for j = 1, …, m
for k from 2 to m do
  for j from k to m do
    T_j ← (j − k) T_{j−1} + (j − k + 2) T_j
```

Only additions and multiplications of non-negative integers by small numbers: `m²/2` steps on
integers of up to about `2m lg m` bits, `O(m³ log m)` bit operations for the whole table.  The
tangent numbers are the stable route to the Bernoulli numbers (`AzRat/Bernoulli.lean`):
`B_{2j} = (−1)^(j−1) 2j T_j / (4^(2j) − 2^(2j))`.

The theory (the recurrence behind the algorithm, the relation to the Bernoulli numbers) is in
`Azurite/BrentZimmermann/Chapter4/TangentNumbers.lean` and `TangentAlgorithm.lean`; the proof
that this array is the model of the latter is in `Azurite/AzNat/Equiv/TangentNumbers.lean`.
-/

namespace Azurite.AzNat

/-- The inner loop of pass `k` after `s` steps (`j = k, …, k + s − 1`):
`T_j ← (j − k) T_{j−1} + (j − k + 2) T_j` with `T_j` at index `j − 1`. -/
def tangentPassArr (k : Nat) (T : Array AzNat) : Nat → Array AzNat
  | 0 => T
  | s + 1 =>
    let T' := tangentPassArr k T s
    T'.setIfInBounds (k + s - 1)
      ((T'.getD (k + s - 2) 0).mulNat s + (T'.getD (k + s - 1) 0).mulNat (s + 2))

/-- The outer loop after `r` passes (`k = 2, …, r + 1`) on an array of length `m`. -/
def tangentOuterArr (m : Nat) (T : Array AzNat) : Nat → Array AzNat
  | 0 => T
  | r + 1 => tangentPassArr (r + 2) (tangentOuterArr m T r) (m + 1 - (r + 2))

/-- The tangent numbers `#[T_1, …, T_m]`. -/
def tangentNumbers (m : Nat) : Array AzNat :=
  tangentOuterArr m (Array.ofFn (n := m) fun i => factorial i.val) (m - 1)

end Azurite.AzNat
